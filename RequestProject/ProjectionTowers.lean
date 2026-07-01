import RequestProject.Foundations

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

/-!
# Projection towers and the rounding lemma `lem:lowd`

This file begins the formalization of Section *Projection towers* of the paper
*"Polynomial Hilbert–Schmidt stability of the lamplighter group"*.

We work in the same setting as the rest of the project: the Hilbert space is
`Matrix ι ι ℂ` for a finite index type `ι`, "projections" are Hermitian
idempotent matrices, and distances are measured in the normalized
Hilbert–Schmidt norm `normHS` from `RequestProject.Foundations`.

## Contents

* **Definitions.** `IsProj` (a projection = Hermitian idempotent), `ProjLE`
  (the sub-projection / Löwner order `P' ≤ P`), the support of a tower, and the
  three notions
  - `IsProjTower` / `IsClosedProjTower` (Definition `def:proj-tower`),
  - `IsApproxClosedProjTower` (Definition `def:approx-proj-tower`),
  - `TowerClose` (closeness of two (approximate) towers).

* **The SVD / polar-decomposition claim** `claim_svd` (Claim `claim:svd`):
  from a contraction `R` with `RR* ≤ P`, `R*R ≤ Q` and `rank P = rank Q` one
  extracts a partial isometry `V` with `V*V = Q`, `VV* = P` and
  `‖R − V‖_HS ≤ ‖R*R − Q‖_HS`.  This is the matrix polar decomposition; it is
  **not** currently available in Mathlib (there is no `PartialIsometry` / polar
  decomposition for operators), so we state and prove it here.

* **The dimension/trace claim** `claim_p_bound` (Claim `claim:p-bound`).

* **The semi-triangle inequality** `semitriangle` (Lemma `lem:semitriang`).
-/

namespace LamplighterStability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Projections and the sub-projection order -/

/-- A **projection** on `Matrix ι ι ℂ`: a Hermitian idempotent matrix. -/
def IsProj (P : Matrix ι ι ℂ) : Prop := P.IsHermitian ∧ IsIdempotentElem P

/-- The **sub-projection (Löwner) order** `P' ≤ P` for projections: `P − P'` is
positive semidefinite.  For projections this is equivalent to `P * P' = P'`. -/
def ProjLE (P' P : Matrix ι ι ℂ) : Prop := (P - P').PosSemidef

/-! ## Projection towers (`def:proj-tower`) -/

/-- A family `P : ℕ → Matrix ι ι ℂ` is a family of **pairwise orthogonal
projections** on the index range `[0, j)`. -/
def PairwiseOrthProj (j : ℕ) (P : ℕ → Matrix ι ι ℂ) : Prop :=
  (∀ i < j, IsProj (P i)) ∧ (∀ i < j, ∀ k < j, i ≠ k → P i * P k = 0)

/-- The **support** of a height-`j` tower: `P_τ = ∑_{i<j} P i`. -/
noncomputable def towerSupport (j : ℕ) (P : ℕ → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ i ∈ Finset.range j, P i

/-- `(P, R)` is a **projection tower of height `j`** (Definition `def:proj-tower`):
the `P i` (`i < j`) are pairwise orthogonal projections, `R` is unitary, and
`R* P_i R = P_{i+1}` for all `0 ≤ i < j-1`. -/
def IsProjTower (j : ℕ) (P : ℕ → Matrix ι ι ℂ) (R : Matrix ι ι ℂ) : Prop :=
  PairwiseOrthProj j P ∧
  R ∈ unitary (Matrix ι ι ℂ) ∧
  (∀ i, i + 1 < j → Rᴴ * P i * R = P (i + 1))

/-- A **closed** projection tower additionally satisfies `R* P_{j-1} R = P_0`. -/
def IsClosedProjTower (j : ℕ) (P : ℕ → Matrix ι ι ℂ) (R : Matrix ι ι ℂ) : Prop :=
  IsProjTower j P R ∧ (0 < j → Rᴴ * P (j - 1) * R = P 0)

/-! ## Approximate towers (`def:approx-proj-tower`) -/

/-- `(P, R)` is an **approximate `(δ₁, δ₂)`-closed projection tower of height `j`**
(Definition `def:approx-proj-tower`): the `P i` are pairwise orthogonal
projections, `R` is unitary, and
`∑_{i<j-1} ‖R* P_i R − P_{i+1}‖² ≤ δ₁`, `‖R* P_{j-1} R − P_0‖² ≤ δ₂`. -/
def IsApproxClosedProjTower (j : ℕ) (P : ℕ → Matrix ι ι ℂ) (R : Matrix ι ι ℂ)
    (δ₁ δ₂ : ℝ) : Prop :=
  PairwiseOrthProj j P ∧
  R ∈ unitary (Matrix ι ι ℂ) ∧
  (∑ i ∈ Finset.range (j - 1), normHS (Rᴴ * P i * R - P (i + 1)) ^ 2 ≤ δ₁) ∧
  (normHS (Rᴴ * P (j - 1) * R - P 0) ^ 2 ≤ δ₂)

/-- Two height-`j` (approximate) towers `(P, R)` and `(P', R')` are
**`(ε₁, ε₂)`-close** if `∑_{i<j} ‖P_i − P'_i‖² ≤ ε₁` and
`‖P_τ R P_τ − P_{τ'} R' P_{τ'}‖² ≤ ε₂`. -/
def TowerClose (j : ℕ) (P P' : ℕ → Matrix ι ι ℂ) (R R' : Matrix ι ι ℂ)
    (ε₁ ε₂ : ℝ) : Prop :=
  (∑ i ∈ Finset.range j, normHS (P i - P' i) ^ 2 ≤ ε₁) ∧
  (normHS (towerSupport j P * R * towerSupport j P
      - towerSupport j P' * R' * towerSupport j P') ^ 2 ≤ ε₂)

/-! ## The semi-triangle inequality (`lem:semitriang`) -/

omit [DecidableEq ι] in
/-
**Lemma `lem:semitriang` (semi-triangle inequality).**  For any finite family
`A : ℕ → Matrix ι ι ℂ`,
`‖∑_{i<k} A_i‖²_HS ≤ k · ∑_{i<k} ‖A_i‖²_HS`.
-/
lemma semitriangle (k : ℕ) (A : ℕ → Matrix ι ι ℂ) :
    normHS (∑ i ∈ Finset.range k, A i) ^ 2
      ≤ (k : ℝ) * ∑ i ∈ Finset.range k, normHS (A i) ^ 2 := by
  refine' le_trans ( pow_le_pow_left₀ ( normHS_nonneg _ ) ( show normHS ( ∑ i ∈ Finset.range k, A i ) ≤ ∑ i ∈ Finset.range k, normHS ( A i ) from _ ) _ ) _;
  · exact Nat.recOn k ( by simp +decide ) fun n ihn => by simpa [ Finset.sum_range_succ ] using le_trans ( normHS_add_le _ _ ) ( add_le_add ihn le_rfl ) ;
  · have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.range k ) => pow_two_nonneg ( normHS ( A i ) - ( ∑ j ∈ Finset.range k, normHS ( A j ) ) / k );
    by_cases hk : k = 0 <;> simp_all +decide [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ];
    norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at *; nlinarith [ mul_div_cancel₀ ( ∑ j ∈ Finset.range k, normHS ( A j ) ) ( Nat.cast_ne_zero.mpr hk ) ] ;

/-! ## Projection helpers -/

/-
The normalized trace of a projection equals its rank divided by the dimension.
-/
lemma ntrace_eq_rank_div {P : Matrix ι ι ℂ} (hP : IsProj P) :
    ntrace P = (P.rank : ℝ) / (Fintype.card ι : ℝ) := by
  have h_trace_eq_rank : (P.trace).re = P.rank := by
    have hP_idempotent : IsIdempotentElem P := by
      exact hP.2
    have hP_linear_map : IsIdempotentElem (Matrix.toLin' P) := by
      exact DFunLike.ext _ _ fun x => by simpa [ Matrix.mulVec ] using congr_arg ( fun m => m.mulVec x ) hP_idempotent;
    have hP_range : Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) = P.rank := by
      convert rfl;
    have hP_trace : LinearMap.trace ℂ (ι → ℂ) (Matrix.toLin' P) = (Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) : ℂ) := by
      convert LinearMap.IsProj.trace ( _ );
      · grind +suggestions;
      · infer_instance;
      · infer_instance;
      · infer_instance;
      · infer_instance;
    simp_all +decide [ Matrix.trace ];
  unfold ntrace; ring_nf at *; aesop;

/-
If `P' ≤ P` are projections, then `P - P'` is again a projection.
-/
set_option maxHeartbeats 1000000 in
lemma isProj_sub_of_projLE {P P' : Matrix ι ι ℂ}
    (hP : IsProj P) (hP' : IsProj P') (hle : ProjLE P' P) :
    IsProj (P - P') := by
  refine' ⟨ hP.1.sub hP'.1, _ ⟩;
  simp_all +decide [ IsIdempotentElem ];
  have h_range : ∀ x : ι → ℂ, P.mulVec x = 0 → P'.mulVec x = 0 := by
    intro x hx
    have h_inner : star x ⬝ᵥ (P - P') *ᵥ x = 0 := by
      have h_inner : star x ⬝ᵥ (P - P') *ᵥ x = -star x ⬝ᵥ P' *ᵥ x := by
        simp_all +decide [ Matrix.sub_mulVec ];
      have h_inner_nonneg : 0 ≤ (star x ⬝ᵥ P' *ᵥ x).re := by
        have h_inner_nonneg : ∀ x : ι → ℂ, 0 ≤ (star x ⬝ᵥ P' *ᵥ x).re := by
          intro x
          have h_inner_nonneg : 0 ≤ (star x ⬝ᵥ P' *ᵥ x).re := by
            have h_inner_nonneg : 0 ≤ (star (P' *ᵥ x) ⬝ᵥ P' *ᵥ x).re := by
              simp +decide [ dotProduct ];
              exact Finset.sum_nonneg fun _ _ => add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ )
            have h_inner_nonneg : star (P' *ᵥ x) ⬝ᵥ P' *ᵥ x = star x ⬝ᵥ P' *ᵥ (P' *ᵥ x) := by
              have h_inner_nonneg : ∀ (A : Matrix ι ι ℂ) (x y : ι → ℂ), star (A *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ Aᴴ *ᵥ y := by
                simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_comm, mul_left_comm ];
                exact fun A x y => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
              convert h_inner_nonneg P' x ( P' *ᵥ x ) using 1;
              rw [ hP'.1.eq ];
            simp_all +decide [ IsProj, IsIdempotentElem ];
          exact h_inner_nonneg;
        exact h_inner_nonneg x;
      have h_inner_nonneg : (star x ⬝ᵥ (P - P') *ᵥ x).re ≥ 0 := by
        have := hle.2;
        specialize this ( Finsupp.equivFunOnFinite.symm x ) ; simp_all +decide [ Matrix.mulVec, dotProduct, Finsupp.sum_fintype ] ;
        simp_all +decide [ Complex.le_def, Complex.ext_iff, Finset.mul_sum _ _ _, mul_assoc, mul_sub, sub_mul ];
        convert this.1 using 1;
        simp +decide only [Finset.sum_add_distrib, Finset.sum_sub_distrib];
      simp_all +decide [ Complex.ext_iff ];
      have h_inner_zero : (star x ⬝ᵥ P' *ᵥ x).im = 0 := by
        have h_herm : (star x ⬝ᵥ P' *ᵥ x) = star (star x ⬝ᵥ P' *ᵥ x) := by
          simp +decide [ dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
          rw [ Finset.sum_comm ];
          exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [ ← hP'.1.apply ] ; simp +decide [ mul_left_comm ] ;
        norm_num [ Complex.ext_iff ] at h_herm ; linarith;
      exact ⟨ by linarith, h_inner_zero ⟩;
    have h_inner_P' : star x ⬝ᵥ P' *ᵥ x = 0 := by
      simp_all +decide [ Matrix.sub_mulVec ];
    have h_inner_P'_zero : ∀ (A : Matrix ι ι ℂ), A.IsHermitian → A.PosSemidef → ∀ (x : ι → ℂ), star x ⬝ᵥ A.mulVec x = 0 → A.mulVec x = 0 := by
      intros A hA hA_pos x hx_zero
      apply Matrix.PosSemidef.dotProduct_mulVec_zero_iff hA_pos x |>.1 hx_zero;
    apply h_inner_P'_zero P' hP'.1 (by
    convert Matrix.posSemidef_conjTranspose_mul_self ( P' ) using 1 ; simp +decide [ hP'.1.eq, hP'.2.eq ]) x h_inner_P';
  have h_range : ∀ x : ι → ℂ, P'.mulVec x = P'.mulVec (P.mulVec x) := by
    intro x; specialize h_range ( x - P.mulVec x ) ; simp_all +decide [ Matrix.mulVec_sub ] ;
    simp_all +decide [ sub_eq_zero ];
    exact h_range ( by rw [ hP.2.eq ] );
  have h_range : P' * P = P' := by
    exact Matrix.toLin'.injective ( LinearMap.ext fun x => by simpa using h_range x |> Eq.symm );
  simp +decide [ sub_mul, mul_sub, h_range, hP.2.eq, hP'.2.eq ];
  rw [ ← Matrix.conjTranspose_inj, Matrix.conjTranspose_mul, hP.1.eq, hP'.1.eq, h_range ]

/-
For projections `P' ≤ P`, the squared HS distance equals the trace gap:
`‖P' − P‖²_HS = tr P − tr P'`.
-/
lemma normHS_projLE_sq {P P' : Matrix ι ι ℂ}
    (hP : IsProj P) (hP' : IsProj P') (hle : ProjLE P' P) :
    normHS (P' - P) ^ 2 = ntrace P - ntrace P' := by
  rw [ ← ntrace_sub, ← normHS_sq_proj ];
  · rw [ ← normHS_neg, neg_sub ];
  · exact hP.1.sub hP'.1;
  · exact isProj_sub_of_projLE hP hP' hle |>.2

/-
**Subprojection of prescribed rank.**  Inside any projection `P` there is a
subprojection `P' ≤ P` of any rank `r ≤ rank P`.
-/
set_option maxHeartbeats 4000000 in
lemma exists_subproj_of_rank {P : Matrix ι ι ℂ} (hP : IsProj P) {r : ℕ}
    (hr : r ≤ P.rank) :
    ∃ P' : Matrix ι ι ℂ, IsProj P' ∧ ProjLE P' P ∧ P'.rank = r := by
  obtain ⟨U, d, hd⟩ : ∃ U : Matrix ι ι ℂ, ∃ d : ι → ℝ, U ∈ unitary (Matrix ι ι ℂ) ∧ P = U * Matrix.diagonal (fun i => d i : ι → ℂ) * star U ∧ ∀ i, d i = 0 ∨ d i = 1 := by
    obtain ⟨U, d, hd⟩ : ∃ U : Matrix ι ι ℂ, ∃ d : ι → ℝ, U ∈ unitary (Matrix ι ι ℂ) ∧ P = U * Matrix.diagonal (fun i => d i : ι → ℂ) * star U ∧ ∀ i, d i = 0 ∨ d i = 1 := by
      have h_spectral : ∃ U : Matrix ι ι ℂ, ∃ d : ι → ℝ, U ∈ unitary (Matrix ι ι ℂ) ∧ P = U * Matrix.diagonal (fun i => d i : ι → ℂ) * star U := by
        obtain ⟨U, d, hU, hd⟩ : ∃ U : Matrix ι ι ℂ, ∃ d : ι → ℝ, U ∈ unitary (Matrix ι ι ℂ) ∧ P = U * Matrix.diagonal (fun i => d i : ι → ℂ) * star U := by
          have h_spectral : P.IsHermitian := hP.left
          have := h_spectral.spectral_theorem;
          refine' ⟨ h_spectral.eigenvectorUnitary, fun i => h_spectral.eigenvalues i, _, _ ⟩;
          · grind;
          · convert this using 1;
        use U, d
      obtain ⟨ U, d, hU, rfl ⟩ := h_spectral; use U, d; simp_all +decide [ IsProj ] ;
      intro i; have := hP.2; simp_all +decide [ IsIdempotentElem, mul_assoc ] ;
      replace hP := congr_arg ( fun m => star U * m * U ) hP.2 ; simp_all +decide [ ← mul_assoc, Unitary.mem_iff ] ;
      simp_all +decide [ mul_assoc, mul_eq_one_comm.mp hU.1 ];
      norm_cast at hP; specialize hP i; by_cases hi : d i = 0 <;> simp_all +decide ;
    use U, d;
  -- Since $r \leq \text{rank}(P)$, we can choose a subset $T \subseteq \{i \mid d_i = 1\}$ with $|T| = r$.
  obtain ⟨T, hT⟩ : ∃ T : Finset ι, T ⊆ Finset.filter (fun i => d i = 1) Finset.univ ∧ T.card = r := by
    have h_rank : P.rank = Finset.card (Finset.filter (fun i => d i = 1) Finset.univ) := by
      have h_rank : P.rank = (Matrix.diagonal (fun i => d i : ι → ℂ)).rank := by
        have h_rank : Matrix.rank (U * Matrix.diagonal (fun i => d i : ι → ℂ) * star U) = Matrix.rank (Matrix.diagonal (fun i => d i : ι → ℂ)) := by
          have h_unitary : U ∈ unitary (Matrix ι ι ℂ) := hd.left
          have h_unitary : Matrix.rank (U * Matrix.diagonal (fun i => d i : ι → ℂ)) = Matrix.rank (Matrix.diagonal (fun i => d i : ι → ℂ)) := by
            refine' le_antisymm _ _;
            · exact Matrix.rank_mul_le_right _ _;
            · have := Matrix.rank_mul_le ( star U ) ( U * Matrix.diagonal ( fun i => ( d i : ℂ ) ) ) ; simp_all +decide [ Matrix.mul_assoc ] ;
              simp_all +decide [ ← mul_assoc ];
          have h_unitary : Matrix.rank ((U * Matrix.diagonal (fun i => d i : ι → ℂ)) * star U) ≤ Matrix.rank (U * Matrix.diagonal (fun i => d i : ι → ℂ)) := by
            exact Matrix.rank_mul_le_left _ _;
          have h_unitary : Matrix.rank (U * Matrix.diagonal (fun i => d i : ι → ℂ)) ≤ Matrix.rank ((U * Matrix.diagonal (fun i => d i : ι → ℂ)) * star U) := by
            have h_unitary : Matrix.rank (U * Matrix.diagonal (fun i => d i : ι → ℂ)) ≤ Matrix.rank ((U * Matrix.diagonal (fun i => d i : ι → ℂ)) * star U * U) := by
              simp_all +decide [ Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff ];
            exact h_unitary.trans ( Matrix.rank_mul_le_left _ _ );
          linarith;
        aesop;
      rw [ h_rank, Matrix.rank_diagonal ];
      rw [ Fintype.card_subtype ] ; congr ; ext i ; cases hd.2.2 i <;> simp +decide [ * ] ;
    exact Finset.exists_subset_card_eq ( by linarith );
  refine' ⟨ U * Matrix.diagonal ( fun i => if i ∈ T then 1 else 0 ) * star U, _, _, _ ⟩ <;> simp_all +decide [ IsProj, ProjLE ];
  · constructor <;> simp_all +decide [ IsIdempotentElem, Matrix.IsHermitian ];
    · simp +decide [ ← Matrix.mul_assoc, ← Matrix.ext_iff ];
      simp +decide [ Matrix.mul_apply, Matrix.diagonal ];
    · simp_all +decide [ ← mul_assoc ];
      simp_all +decide [ Matrix.mul_assoc ];
  · -- Since $U$ is unitary, we have $U * Uᴴ = I$, and thus $U * (diagonal (fun i => d i) - diagonal (fun i => if i ∈ T then 1 else 0)) * Uᴴ$ is positive semidefinite.
    have h_pos_semidef : (Matrix.diagonal (fun i => d i : ι → ℂ) - Matrix.diagonal (fun i => if i ∈ T then 1 else 0 : ι → ℂ)).PosSemidef := by
      simp +decide [ Matrix.PosSemidef, Matrix.IsHermitian ];
      simp +decide [ Matrix.diagonal, Finsupp.sum_fintype ];
      intro x; rw [ Finset.sum_congr rfl fun i hi => Finset.sum_eq_single i ( fun j hj => by aesop ) ( by aesop ) ] ; simp +decide ;
      refine' Finset.sum_nonneg fun i _ => _ ; cases hd.2.2 i <;> simp +decide [ * ] ; ring_nf ;
      · split_ifs <;> simp_all +decide [ Finset.subset_iff ];
      · split_ifs <;> simp +decide [ *, mul_comm ];
        simp +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
    convert h_pos_semidef.conjTranspose_mul_mul_same ( star U ) using 1 ; simp +decide [ Matrix.mul_assoc ];
    simp +decide [ ← Matrix.mul_sub, ← Matrix.sub_mul ];
    simp +decide [ Matrix.star_eq_conjTranspose ];
  · have h_rank : Matrix.rank (U * Matrix.diagonal (fun i => if i ∈ T then 1 else 0) * star U) = Matrix.rank (Matrix.diagonal (fun i => if i ∈ T then 1 else 0) : Matrix ι ι ℂ) := by
      have h_rank : Matrix.rank (U * Matrix.diagonal (fun i => if i ∈ T then 1 else 0) * star U) ≤ Matrix.rank (Matrix.diagonal (fun i => if i ∈ T then 1 else 0) : Matrix ι ι ℂ) := by
        exact le_trans ( Matrix.rank_mul_le_left _ _ ) ( Matrix.rank_mul_le_right _ _ );
      refine' le_antisymm h_rank _;
      have h_rank : Matrix.rank (star U * (U * Matrix.diagonal (fun i => if i ∈ T then 1 else 0) * star U) * U) ≤ Matrix.rank (U * Matrix.diagonal (fun i => if i ∈ T then 1 else 0) * star U) := by
        exact Matrix.rank_mul_le_left _ _ |> le_trans <| Matrix.rank_mul_le_right _ _;
      simp_all +decide [ ← mul_assoc, Matrix.mem_unitaryGroup_iff ];
      simp_all +decide [ mul_assoc, mul_eq_one_comm.mp hd.1 ];
    rw [ h_rank, Matrix.rank_diagonal ] ; aesop

/-! ## The SVD / polar-decomposition claim (`claim:svd`) -/

/-
For a projection `Q`, `1 - Q` is positive semidefinite.
-/
lemma posSemidef_one_sub_isProj {Q : Matrix ι ι ℂ} (hQ : IsProj Q) :
    ((1 : Matrix ι ι ℂ) - Q).PosSemidef := by
  unfold IsProj at hQ;
  convert Matrix.posSemidef_conjTranspose_mul_self ( 1 - Q ) using 1;
  simp_all +decide [ IsIdempotentElem, Matrix.IsHermitian, Matrix.mul_sub ]

/-
If `A ≤ Q` with `A` positive semidefinite and `Q` a projection, then `Q`
fixes the range of `A`: `Q * A = A` and `A * Q = A`.
-/
lemma proj_mul_eq_of_psd_le {Q A : Matrix ι ι ℂ}
    (hQ : IsProj Q) (hA : A.PosSemidef) (hle : (Q - A).PosSemidef) :
    Q * A = A ∧ A * Q = A := by
  have h_range : ∀ x : ι → ℂ, Q.mulVec x = 0 → A.mulVec x = 0 := by
    intro x hx
    have h_inner : star x ⬝ᵥ A *ᵥ x = 0 := by
      have h_inner : star x ⬝ᵥ (Q - A) *ᵥ x = - star x ⬝ᵥ A *ᵥ x := by
        simp +decide [ Matrix.sub_mulVec, hx ];
      have h_inner_nonneg : 0 ≤ star x ⬝ᵥ A *ᵥ x ∧ 0 ≤ -star x ⬝ᵥ A *ᵥ x := by
        grind +suggestions;
      simp_all +decide [ Complex.ext_iff, le_iff_lt_or_eq ];
      grind +splitIndPred;
    exact hA.dotProduct_mulVec_zero_iff x |>.1 h_inner;
  have h_range : A * Q = A := by
    refine' Matrix.toLin'.injective ( LinearMap.ext fun x => _ );
    specialize h_range ( x - Q.mulVec x ) ; simp_all +decide [ Matrix.mulVec_sub, sub_eq_zero ] ;
    simp_all +decide [ hQ.2.eq ];
  have := hQ.1; have := hA.1; simp_all +decide [ Matrix.IsHermitian ] ;
  apply_fun Matrix.conjTranspose at h_range; simp_all +decide [ Matrix.conjTranspose_mul ] ;

/-
If `n ≤ Q ≤ 1` (with `Q` a projection), then `n ≤ 1`.
-/
lemma posSemidef_one_sub_of_le_isProj {Q n : Matrix ι ι ℂ}
    (hQ : IsProj Q) (hle : (Q - n).PosSemidef) :
    ((1 : Matrix ι ι ℂ) - n).PosSemidef := by
  have := posSemidef_one_sub_isProj hQ;
  convert hle.add this using 1 ; abel_nf

/-
`Q` fixes the range of `√n` as well: `Q * √n = √n` and `√n * Q = √n`.
-/
lemma proj_mul_sqrt_eq_of_psd_le {Q n : Matrix ι ι ℂ}
    (hQ : IsProj Q) (hn : n.PosSemidef) (hle : (Q - n).PosSemidef) :
    Q * CFC.sqrt n = CFC.sqrt n ∧ CFC.sqrt n * Q = CFC.sqrt n := by
  have h_norm_zero : normHS ((1 - Q) * CFC.sqrt n) = 0 := by
    have h_norm_sq_zero : (normHS ((1 - Q) * CFC.sqrt n)) ^ 2 = ntrace ((1 - Q) * n) := by
      have h_normHS_sq : (normHS ((1 - Q) * CFC.sqrt n)) ^ 2 = ntrace (CFC.sqrt n * (1 - Q) * CFC.sqrt n) := by
        convert normHS_sq_eq_ntrace _ using 2 ; simp +decide [ Matrix.mul_assoc ];
        have h_sqrt_herm : (CFC.sqrt n).IsHermitian := by
          grind +suggestions;
        simp_all +decide [ IsProj, Matrix.IsHermitian ];
        simp_all +decide [ IsIdempotentElem, sub_mul, mul_sub ];
        simp_all +decide [ ← Matrix.mul_assoc ];
      rw [ h_normHS_sq, mul_assoc ];
      rw [ ← ntrace_mul_comm ];
      rw [ mul_assoc, CFC.sqrt_mul_sqrt_self n ];
    have h_trace_zero : ntrace ((1 - Q) * n) = 0 := by
      have h_trace_zero : Q * n = n := by
        exact proj_mul_eq_of_psd_le hQ hn hle |>.1;
      simp +decide [ sub_mul, h_trace_zero ];
    nlinarith;
  by_cases h : Nonempty ι <;> simp_all +decide [ normHS_eq_zero_iff ];
  · have h_sqrt_herm : (CFC.sqrt n).IsHermitian := by
      convert CFC.sqrt_nonneg n |>.posSemidef.1 using 1;
    simp_all +decide [ Matrix.IsHermitian ];
    have := congr_arg Matrix.conjTranspose h_norm_zero; norm_num [ h_sqrt_herm ] at this;
    simp_all +decide [ mul_sub, sub_mul, hQ.1.eq ];
    exact ⟨ eq_of_sub_eq_zero h_norm_zero ▸ rfl, eq_of_sub_eq_zero this ▸ rfl ⟩;
  · exact ⟨ Subsingleton.elim _ _, Subsingleton.elim _ _ ⟩

/-
The CFC combination `n² − 3n + 2√n` is positive semidefinite when `0 ≤ n ≤ 1`
(the scalar function `z² − 3z + 2√z = w(w−1)²(w+2) ≥ 0` for `w = √z ∈ [0,1]`).
-/
lemma posSemidef_sq_sub_smul_add_sqrt {n : Matrix ι ι ℂ}
    (hn : n.PosSemidef) (hle : ((1 : Matrix ι ι ℂ) - n).PosSemidef) :
    (n ^ 2 - (3 : ℝ) • n + (2 : ℝ) • CFC.sqrt n).PosSemidef := by
  -- By definition of $CFC.sqrt$, we know that $CFC.sqrt n = cfc Real.sqrt n$.
  have h_sqrt : CFC.sqrt n = cfc Real.sqrt n := by
    convert CFC.sqrt_eq_real_sqrt n _ using 1
    generalize_proofs at *; (
    rw [ cfcₙ_eq_cfc ]);
    convert hn using 1;
    ext; simp [LE.le]
  generalize_proofs at *; (
  -- By definition of $cfc$, we know that $cfc (fun z => z^2 - 3*z + 2*Real.sqrt z) n = n^2 - 3*n + 2*cfc Real.sqrt n$.
  have h_cfc : cfc (fun z : ℝ => z^2 - 3*z + 2*Real.sqrt z) n = n^2 - 3•n + 2•CFC.sqrt n := by
    have h_cfc : cfc (fun z : ℝ => z^2 - 3*z + 2*Real.sqrt z) n = cfc (fun z : ℝ => z^2) n - 3 • cfc (fun z : ℝ => z) n + 2 • cfc (fun z : ℝ => Real.sqrt z) n := by
      have h_cfc : ∀ (f g : ℝ → ℝ), ContinuousOn f (spectrum ℝ n) → ContinuousOn g (spectrum ℝ n) → cfc (fun z => f z + g z) n = cfc f n + cfc g n := by
        intros f g hf hg; exact (by
        convert cfc_add ( a := n ) ( f := f ) ( g := g ) ( by
          exact hf ) ( by
          exact hg ) using 1);
      generalize_proofs at *; (
      have h_cfc : ∀ (f : ℝ → ℝ), ContinuousOn f (spectrum ℝ n) → ∀ (c : ℝ), cfc (fun z => c * f z) n = c • cfc f n := by
        intro f hf c; exact (by
        convert cfc_const_mul c f n using 1);
      generalize_proofs at *; (
      simp +decide only [sub_eq_add_neg];
      rename_i h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀;
      rw [ h₁₀, h₁₀ ];
      · rw [ show ( fun z : ℝ => - ( 3 * z ) ) = fun z : ℝ => -3 * z by ext; ring, h_cfc ] <;> norm_num [ h_cfc ];
        · rw [ h_cfc _ ( Real.continuous_sqrt.continuousOn ) 2 ] ; norm_num [ Algebra.smul_def ];
          congr! 2;
        · exact continuousOn_id;
      · exact continuousOn_pow 2;
      · exact ContinuousOn.neg ( continuousOn_const.mul continuousOn_id );
      · fun_prop (disch := norm_num);
      · exact ContinuousOn.mul continuousOn_const ( Real.continuous_sqrt.continuousOn )));
    have h_cfc_id : cfc (fun z : ℝ => z) n = n := by
      exact cfc_id ℝ n
    generalize_proofs at *; (
    have h_cfc_sq : cfc (fun z : ℝ => z^2) n = n^2 := by
      have h_cfc_sq : cfc (fun z : ℝ => z^2) n = cfc (fun z : ℝ => z) n * cfc (fun z : ℝ => z) n := by
        convert cfc_mul ( fun z : ℝ => z ) ( fun z : ℝ => z ) n using 1 ; ring!;
      generalize_proofs at *; (
      rw [ h_cfc_sq, h_cfc_id, pow_two ])
    generalize_proofs at *; (simp_all +decide [ pow_two ]))
  generalize_proofs at *; (
  have h_spectrum : ∀ x ∈ spectrum ℝ n, 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    have h_nonneg : 0 ≤ x := by
      grind +suggestions
    have h_le_one : x ≤ 1 := by
      have h_le_one : x ∈ spectrum ℝ (1 - (1 - n)) := by
        simpa using hx
      generalize_proofs at *; (
      have h_le_one : ∀ x ∈ spectrum ℝ (1 - (1 - n)), x ≤ 1 := by
        intro x hx
        have h_le_one : 1 - x ∈ spectrum ℝ (1 - n) := by
          simp_all +decide [ spectrum.mem_iff ];
          exact fun h => hx <| by simpa [ sub_eq_neg_add ] using h.neg;
        grind +suggestions
      generalize_proofs at *; (
      exact h_le_one x ‹_›))
    exact ⟨h_nonneg, h_le_one⟩
  generalize_proofs at *; (
  convert cfc_nonneg ( show ∀ x ∈ spectrum ℝ n, 0 ≤ x ^ 2 - 3 * x + 2 * Real.sqrt x from fun x hx => ?_ ) using 1
  generalize_proofs at *; (
  ext; simp [PosSemidef, LE.le]);
  · convert h_cfc.symm using 1;
    norm_cast;
  · nlinarith [ h_spectrum x hx, sq_nonneg ( Real.sqrt x - 1 ), Real.sqrt_nonneg x, Real.sq_sqrt ( h_spectrum x hx |>.1 ) ])))

/-
**Spectral inequality.**  For a projection `Q` and a positive semidefinite
`n` with `n ≤ Q`, the positive square root satisfies
`‖√n − Q‖_HS ≤ ‖n − Q‖_HS`.

Since `n ≤ Q` forces `range n ⊆ range Q`, `n` and `Q` commute and can be
simultaneously diagonalized; on `range Q` the eigenvalues `z ∈ [0,1]` of `n` give
`(√z − 1)² ≤ (z − 1)²`, and off `range Q` both sides vanish.
-/
lemma sqrt_sub_proj_normHS_le {Q n : Matrix ι ι ℂ}
    (hQ : IsProj Q) (hn : n.PosSemidef) (hle : (Q - n).PosSemidef) :
    normHS (CFC.sqrt n - Q) ≤ normHS (n - Q) := by
  -- Let `T = CFC.sqrt n`. Facts:
  set T := CFC.sqrt n with hT_def
  have hT_herm : T.IsHermitian := by
    convert CFC.sqrt_nonneg n |>.posSemidef.1 using 1
  have hT_sq : T * T = n := by
    convert CFC.sqrt_mul_sqrt_self n using 1
  have hQn : Q * n = n ∧ n * Q = n := by
    apply proj_mul_eq_of_psd_le hQ hn hle
  have hQT : Q * T = T ∧ T * Q = T := by
    apply proj_mul_sqrt_eq_of_psd_le hQ hn hle
  have hQQ : Q * Q = Q := by
    exact hQ.2.eq
  have hQ_herm : Q.IsHermitian := by
    exact hQ.1
  have hn_herm : n.IsHermitian := by
    exact hn.1;
  -- By `normHS_sq_eq_ntrace` and Hermitianness (so `(X-Q)ᴴ = X - Q`):
  have h1 : normHS (T - Q) ^ 2 = ntrace n - 2 * ntrace T + ntrace Q := by
    rw [ normHS_sq_eq_ntrace ];
    simp +decide [ sub_mul, mul_sub, hT_sq, hQT, hQQ, hT_herm.eq, hQ_herm.eq, ntrace_sub ] ; ring
  have h2 : normHS (n - Q) ^ 2 = ntrace (n ^ 2) - 2 * ntrace n + ntrace Q := by
    convert normHS_sq_eq_ntrace ( n - Q ) using 1 ; simp +decide [ *, sq, Matrix.mul_sub, Matrix.sub_mul ] ; ring;
    simp +decide [ hn_herm.eq, hQ_herm.eq, hQn, hQQ, ntrace ] ; ring;
  -- By `posSemidef_sq_sub_smul_add_sqrt` this matrix is PSD, so `ntrace_nonneg_of_posSemidef` gives `0 ≤ ntrace (n^2 - 3•n + 2•T)`.
  have h3 : 0 ≤ ntrace (n ^ 2 - (3 : ℝ) • n + (2 : ℝ) • T) := by
    apply ntrace_nonneg_of_posSemidef;
    convert posSemidef_sq_sub_smul_add_sqrt hn ( posSemidef_one_sub_of_le_isProj hQ hle ) using 1;
  -- By `ntrace_add`/`ntrace_sub` additivity and `ntrace (c • A) = c * ntrace A` for real `c`:
  have h4 : ntrace (n ^ 2 - (3 : ℝ) • n + (2 : ℝ) • T) = ntrace (n ^ 2) - 3 * ntrace n + 2 * ntrace T := by
    unfold ntrace; simp +decide [ Matrix.trace_add, Matrix.trace_smul ] ; ring;
  nlinarith [ normHS_nonneg ( T - Q ), normHS_nonneg ( n - Q ) ]

omit [DecidableEq ι] in
/-
**Partial-isometry identity.**  If `Wᴴ * W` is idempotent (a projection),
then `W * Wᴴ * W = W`.
-/
lemma partialIsometry_mul_self {W : Matrix ι ι ℂ}
    (h : IsIdempotentElem (Wᴴ * W)) :
    W * Wᴴ * W = W := by
  have h_eq : (W * Wᴴ * W - W)ᴴ * (W * Wᴴ * W - W) = 0 := by
    simp_all +decide [ Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, IsIdempotentElem ];
  exact sub_eq_zero.mp ( Matrix.conjTranspose_mul_self_eq_zero.mp h_eq )

omit [DecidableEq ι] in
/-
If `Wᴴ * W` is a projection, so is `W * Wᴴ`.
-/
lemma isProj_mulConjTranspose_of_isProj {W : Matrix ι ι ℂ}
    (h : IsProj (Wᴴ * W)) :
    IsProj (W * Wᴴ) := by
  constructor;
  · simp +decide [ Matrix.IsHermitian, Matrix.conjTranspose_mul ];
  · have hW_right : W * Wᴴ * W * Wᴴ = W * Wᴴ := by
      convert congrArg ( fun x => x * Wᴴ ) ( partialIsometry_mul_self h.2 ) using 1;
    simp_all +decide [ IsIdempotentElem, Matrix.mul_assoc ]

/-
If `A Aᴴ ≤ P` (Löwner order) with `P` a projection, then `P` fixes the
range of `A`: `P * A = A`.
-/
lemma proj_mul_eq_self_of_psd_le {P A : Matrix ι ι ℂ}
    (hP : IsProj P) (hle : (P - A * Aᴴ).PosSemidef) :
    P * A = A := by
  obtain ⟨hP₁, hP₂⟩ := hP;
  -- Since `1-P` is a projection, `(1-P)ᴴ*(1-P) = (1-P)`. So this equals `ntrace (Aᴴ*(1-P)*A)`.
  have h_trace : ntrace (Aᴴ * (1 - P) * A) = 0 := by
    have h_trace : ntrace ((1 - P) * A * Aᴴ) = 0 := by
      have hP_mul_A_sq : P * (A * Aᴴ) = A * Aᴴ := by
        apply (proj_mul_eq_of_psd_le ⟨ hP₁, hP₂ ⟩ ( show ( A * Aᴴ ).PosSemidef from ?_ ) hle).left;
        grind +suggestions;
      simp_all +decide [ sub_mul, mul_assoc ];
    convert h_trace using 1;
    unfold ntrace; simp +decide [ Matrix.mul_assoc, Matrix.trace_mul_comm Aᴴ ] ;
  -- Since `ntrace (Aᴴ * (1 - P) * A) = 0`, we have `normHS ((1 - P) * A) = 0`.
  have h_norm_zero : normHS ((1 - P) * A) = 0 := by
    have h_norm_zero : normHS ((1 - P) * A) ^ 2 = ntrace (Aᴴ * (1 - P) * A) := by
      convert normHS_sq_eq_ntrace _ using 2;
      simp +decide [ Matrix.mul_assoc, Matrix.conjTranspose_mul, hP₁.eq ];
      simp +decide [ ← mul_assoc, sub_mul, mul_sub, hP₂.eq ];
    aesop;
  by_cases h : Nonempty ι <;> simp_all +decide [ IsIdempotentElem ];
  · have := normHS_eq_zero_iff.mp h_norm_zero; simp_all +decide [ sub_mul ] ;
    exact Eq.symm ( sub_eq_zero.mp this );
  · exact Subsingleton.elim _ _

/-
**Rank subtractivity for subprojections.**  If `P' ≤ P` are projections,
then `rank (P - P') = rank P - rank P'` (as real numbers).
-/
lemma rank_sub_of_projLE {P P' : Matrix ι ι ℂ}
    (hP : IsProj P) (hP' : IsProj P') (hle : ProjLE P' P) :
    ((P - P').rank : ℝ) = (P.rank : ℝ) - (P'.rank : ℝ) := by
  by_cases h : Fintype.card ι = 0;
  · simp_all +decide [ Fintype.card_eq_zero_iff ];
    rw [ Subsingleton.elim ( P - P' ) 0, Subsingleton.elim P 0, Subsingleton.elim P' 0 ] ; norm_num;
  · have h_rank_sub : (P - P').rank / (Fintype.card ι : ℝ) = P.rank / (Fintype.card ι : ℝ) - P'.rank / (Fintype.card ι : ℝ) := by
      rw [ ← ntrace_eq_rank_div hP, ← ntrace_eq_rank_div hP', ← ntrace_eq_rank_div ( isProj_sub_of_projLE hP hP' hle ), ntrace_sub ];
    rw [ ← sub_div, div_eq_div_iff ] at h_rank_sub <;> norm_cast at * ; aesop

/-
**Equal-rank projections are linked by a partial isometry.**  For two
projections `E, F` of the same rank there is a `W` with `Wᴴ * W = E` and
`W * Wᴴ = F`.
-/
set_option maxHeartbeats 4000000 in
lemma exists_partialIsometry_equal_rank {E F : Matrix ι ι ℂ}
    (hE : IsProj E) (hF : IsProj F) (hrank : E.rank = F.rank) :
    ∃ W : Matrix ι ι ℂ, Wᴴ * W = E ∧ W * Wᴴ = F := by
  -- By the spectral theorem, there exist unitary matrices $U$ and $V$ and diagonal matrices $D_E$ and $D_F$ such that $E = U D_E Uᴴ$ and $F = V D_F Vᴴ$.
  obtain ⟨U, D_E, hU⟩ : ∃ U : Matrix ι ι ℂ, U ∈ unitary (Matrix ι ι ℂ) ∧ ∃ D_E : ι → ℝ, (∀ i, D_E i = 0 ∨ D_E i = 1) ∧ E = U * Matrix.diagonal (fun i => D_E i : ι → ℂ) * star U := by
    have h_spectral : ∃ U : Matrix ι ι ℂ, U ∈ unitary (Matrix ι ι ℂ) ∧ ∃ D_E : ι → ℝ, (∀ i, D_E i = 0 ∨ D_E i = 1) ∧ E = U * Matrix.diagonal (fun i => D_E i : ι → ℂ) * star U := by
      have h_herm : E.IsHermitian := hE.left
      obtain ⟨U, D, hU, hD⟩ : ∃ U : Matrix ι ι ℂ, U ∈ unitary (Matrix ι ι ℂ) ∧ ∃ D : ι → ℝ, (∀ i, D i = 0 ∨ D i = 1) ∧ E = U * Matrix.diagonal (fun i => D i : ι → ℂ) * star U := by
        have h_eigenvalues : ∀ i, h_herm.eigenvalues i = 0 ∨ h_herm.eigenvalues i = 1 := by
          intro i
          have h_eigenvalue : h_herm.eigenvalues i * h_herm.eigenvalues i = h_herm.eigenvalues i := by
            have h_eigenvalue : E.mulVec (h_herm.eigenvectorBasis i) = h_herm.eigenvalues i • h_herm.eigenvectorBasis i := by
              convert h_herm.mulVec_eigenvectorBasis i using 1;
            have h_eigenvalue : E.mulVec (E.mulVec (h_herm.eigenvectorBasis i)) = E.mulVec (h_herm.eigenvectorBasis i) := by
              have := hE.2;
              simp_all +decide [ IsIdempotentElem ];
              simp +decide [ ← h_eigenvalue, this ];
            simp_all +decide [ Matrix.mulVec_smul ];
            simp_all +decide [ ← smul_assoc ];
            exact smul_left_injective _ ( by simpa using h_herm.eigenvectorBasis.orthonormal.ne_zero i ) h_eigenvalue;
          exact or_iff_not_imp_left.mpr fun h => mul_left_cancel₀ h <| by linear_combination' h_eigenvalue;
        refine' ⟨ h_herm.eigenvectorUnitary, _, fun i => h_herm.eigenvalues i, h_eigenvalues, _ ⟩;
        · grind;
        · convert h_herm.spectral_theorem using 1;
      exact ⟨ U, D, hU, hD ⟩;
    exact h_spectral;
  obtain ⟨V, D_F, hV⟩ : ∃ V : Matrix ι ι ℂ, V ∈ unitary (Matrix ι ι ℂ) ∧ ∃ D_F : ι → ℝ, (∀ i, D_F i = 0 ∨ D_F i = 1) ∧ F = V * Matrix.diagonal (fun i => D_F i : ι → ℂ) * star V := by
    have := Matrix.IsHermitian.spectral_theorem hF.1;
    refine' ⟨ _, _, _, _, this ⟩;
    · simp +decide [];
    · intro i
      have h_eigenvalue : (hF.1.eigenvalues i : ℂ) ^ 2 = (hF.1.eigenvalues i : ℂ) := by
        have h_eigenvalue : (hF.1.eigenvalues i : ℂ) ^ 2 = (hF.1.eigenvalues i : ℂ) := by
          have h_eigenvalue : (hF.1.eigenvalues i : ℂ) ^ 2 = (hF.1.eigenvalues i : ℂ) := by
            have h_eigenvalue : F.mulVec (hF.1.eigenvectorBasis i) = (hF.1.eigenvalues i : ℂ) • hF.1.eigenvectorBasis i := by
              convert hF.1.mulVec_eigenvectorBasis i using 1
            have h_eigenvalue : F.mulVec (F.mulVec (hF.1.eigenvectorBasis i)) = F.mulVec ((hF.1.eigenvalues i : ℂ) • hF.1.eigenvectorBasis i) := by
              rw [ ← h_eigenvalue ];
            have h_eigenvalue : F.mulVec (F.mulVec (hF.1.eigenvectorBasis i)) = F.mulVec (hF.1.eigenvectorBasis i) := by
              have := hF.2;
              simp +decide [ this.eq ];
            simp +decide [ sq, Matrix.mulVec_smul ] at *;
            simp +decide [ h_eigenvalue, ‹F *ᵥ _ = _› ] at *;
            simp +decide [ ← smul_assoc, ← Complex.ofReal_mul ] at *;
            exact smul_left_injective _ ( by simp +decide [ hF.1.eigenvectorBasis.orthonormal.ne_zero ] ) h_eigenvalue.symm
          exact h_eigenvalue;
        exact h_eigenvalue;
      norm_num [ Complex.ext_iff, sq ] at h_eigenvalue ⊢;
      exact or_iff_not_imp_left.mpr fun h => mul_left_cancel₀ h <| by linarith;
  obtain ⟨ D_E, hD_E, rfl ⟩ := hU
  obtain ⟨ D_F, hD_F, rfl ⟩ := hV
  have h_card : (Finset.filter (fun i => D_E i = 1) Finset.univ).card = (Finset.filter (fun i => D_F i = 1) Finset.univ).card := by
    have h_card : Matrix.rank (Matrix.diagonal (fun i => D_E i : ι → ℂ)) = Matrix.rank (Matrix.diagonal (fun i => D_F i : ι → ℂ)) := by
      have h_rank_eq : ∀ (U : Matrix ι ι ℂ), U ∈ unitary (Matrix ι ι ℂ) → ∀ (A : Matrix ι ι ℂ), Matrix.rank (U * A * star U) = Matrix.rank A := by
        intro U hU A
        have h_rank_eq : Matrix.rank (U * A * star U) ≤ Matrix.rank A := by
          exact le_trans ( Matrix.rank_mul_le_left _ _ ) ( Matrix.rank_mul_le_right _ _ );
        have h_rank_eq : Matrix.rank A ≤ Matrix.rank (U * A * star U) := by
          have h_rank_eq : Matrix.rank A ≤ Matrix.rank (star U * (U * A * star U) * U) := by
            simp +decide [ ← mul_assoc, hU.1 ];
            simp +decide [ mul_assoc, hU.1 ];
          exact h_rank_eq.trans ( Matrix.rank_mul_le_left _ _ |> le_trans <| Matrix.rank_mul_le_right _ _ );
        exact le_antisymm ‹_› ‹_›;
      grind;
    convert h_card using 1 <;> rw [ Matrix.rank_diagonal ];
    · rw [ Fintype.card_subtype ] ; congr ; ext i ; cases hD_E i <;> simp +decide [ * ] ;
    · rw [ Fintype.card_subtype ] ; congr ; ext i ; cases hD_F i <;> simp +decide [ * ] ;
  -- Build a permutation `g : Equiv.Perm ι` with `g` mapping `S` bijectively onto `S'`.
  obtain ⟨g, hg⟩ : ∃ g : Equiv.Perm ι, ∀ i, D_E i = 1 ↔ D_F (g i) = 1 := by
    obtain ⟨g, hg⟩ : ∃ g : {i : ι | D_E i = 1} ≃ {i : ι | D_F i = 1}, True := by
      exact ⟨ Fintype.equivOfCardEq ( by simpa [ Fintype.card_subtype ] using h_card ), trivial ⟩;
    obtain ⟨g', hg'⟩ : ∃ g' : {i : ι | D_E i ≠ 1} ≃ {i : ι | D_F i ≠ 1}, True := by
      have h_card_compl : (Finset.filter (fun i => D_E i ≠ 1) Finset.univ).card = (Finset.filter (fun i => D_F i ≠ 1) Finset.univ).card := by
        simp_all +decide [ Finset.filter_not, Finset.card_sdiff ];
      exact ⟨ Fintype.equivOfCardEq ( by simpa [ Fintype.card_subtype ] using h_card_compl ), trivial ⟩;
    refine' ⟨ Equiv.ofBijective ( fun i => if hi : D_E i = 1 then g ⟨ i, hi ⟩ else g' ⟨ i, hi ⟩ ) ⟨ _, _ ⟩, _ ⟩;
    all_goals simp +decide [ Function.Injective, Function.Surjective ];
    · intro i j hij; split_ifs at hij <;> simp_all +decide [] ;
      · have := g.injective ( Subtype.ext hij ) ; aesop;
      · grind +qlia;
      · grind;
      · have := g'.injective ( Subtype.ext hij ) ; aesop;
    · intro b;
      by_cases hb : D_F b = 1;
      · obtain ⟨ a, ha ⟩ := g.surjective ⟨ b, hb ⟩;
        grind;
      · obtain ⟨ a, ha ⟩ := g'.surjective ⟨ b, hb ⟩;
        grind;
    · grind;
  -- Let $M := Pg * Matrix.diagonal (fun i => if i ∈ S then 1 else 0)$.
  obtain ⟨M, hM⟩ : ∃ M : Matrix ι ι ℂ, Mᴴ * M = Matrix.diagonal (fun i => D_E i : ι → ℂ) ∧ M * Mᴴ = Matrix.diagonal (fun i => D_F i : ι → ℂ) := by
    refine' ⟨ Matrix.of fun i j => if D_E j = 1 then if g j = i then 1 else 0 else 0, _, _ ⟩ <;> ext i j <;> simp +decide [ Matrix.mul_apply, Matrix.diagonal ];
    · cases hD_E i <;> cases hD_E j <;> simp +decide [ * ];
      grind;
    · rw [ Finset.sum_eq_single ( g.symm i ) ] <;> simp +decide [ hg ];
      · cases hD_F i <;> aesop;
      · grind;
  refine' ⟨ V * M * star U, _, _ ⟩ <;> simp +decide [ ← hM.1, ← hM.2, Matrix.mul_assoc ];
  · have h_unitary : U * star U = 1 ∧ V * star V = 1 := by
      exact ⟨ by simpa using ‹U ∈ unitary ( Matrix ι ι ℂ ) ›.2, by simpa using ‹V ∈ unitary ( Matrix ι ι ℂ ) ›.2 ⟩;
    simp +decide [ ← Matrix.mul_assoc ];
    simp +decide [ Matrix.mul_assoc, show Vᴴ * V = 1 from by simpa [ mul_eq_one_comm ] using h_unitary.2 ];
    simp +decide [ Matrix.star_eq_conjTranspose ];
  · simp_all +decide [ ← Matrix.mul_assoc, Matrix.star_eq_conjTranspose ];
    simp_all +decide [ mul_assoc ];
    simp_all +decide [ ← mul_assoc, mul_eq_one_comm.mp ( show U * Uᴴ = 1 from by simpa using ‹U ∈ unitary ( Matrix ι ι ℂ ) ›.2 ) ]

/-
**Polar decomposition (existence of the partial isometry).**  For any matrix
`R`, writing `T = √(Rᴴ R)`, there is a matrix `W = R * Tp` (with `Tp` the
Moore–Penrose-type pseudoinverse of `T`) which is the partial isometry of the
polar decomposition: `W * T = R`, `s := Wᴴ * W` is the support projection of `T`
(`s = T * Tp`, `s * T = T`), and `rank s = rank R`.
-/
set_option maxHeartbeats 4000000 in
lemma exists_polar_partialIsometry (R : Matrix ι ι ℂ) :
    ∃ W Tp : Matrix ι ι ℂ,
      W = R * Tp ∧
      W * CFC.sqrt (Rᴴ * R) = R ∧
      IsProj (Wᴴ * W) ∧
      Wᴴ * W = CFC.sqrt (Rᴴ * R) * Tp ∧
      (Wᴴ * W) * CFC.sqrt (Rᴴ * R) = CFC.sqrt (Rᴴ * R) ∧
      (Wᴴ * W).rank = R.rank := by
  -- Let T = CFC.sqrt (Rᴴ * R). Then T is Hermitian and T * T = Rᴴ * R.
  set T : Matrix ι ι ℂ := CFC.sqrt (Rᴴ * R)
  have hT_herm : T.IsHermitian := by
    exact ( CFC.sqrt_nonneg ( Rᴴ * R ) ).posSemidef.1
  have hT_sq : T * T = Rᴴ * R := by
    apply CFC.sqrt_mul_sqrt_self;
    convert Matrix.posSemidef_conjTranspose_mul_self R using 1;
    ext; simp [PosSemidef];
    constructor <;> intro h;
    · obtain ⟨ h₁, h₂ ⟩ := h;
      aesop;
    · constructor <;> simp_all +decide [ Matrix.IsHermitian ];
  -- Let Tp be the pseudoinverse of T, defined by Tp = cfc (fun x => if x = 0 then 0 else x⁻¹) T.
  obtain ⟨Tp, hTp⟩ : ∃ Tp : Matrix ι ι ℂ, Tp.IsHermitian ∧ T * Tp = Tp * T ∧ T * Tp * T = T ∧ Tp * T * Tp = Tp := by
    -- Let $Tp$ be the Moore–Penrose-type pseudoinverse of $T$, defined as $Tp = T^{-1}$ on the range of $T$ and $0$ on the orthogonal complement. We can construct $Tp$ using the spectral decomposition of $T$.
    obtain ⟨U, D, hU, hD⟩ : ∃ U : Matrix ι ι ℂ, ∃ D : ι → ℝ, U * U.conjTranspose = 1 ∧ U.conjTranspose * U = 1 ∧ T = U * Matrix.diagonal (fun i => D i : ι → ℂ) * U.conjTranspose := by
      have := Matrix.IsHermitian.spectral_theorem hT_herm;
      refine' ⟨ hT_herm.eigenvectorUnitary, fun i => hT_herm.eigenvalues i, _, _, _ ⟩ <;> simp +decide [] at *;
      · convert hT_herm.eigenvectorUnitary.2.2 using 1;
      · simp +decide [ Matrix.IsHermitian.eigenvectorUnitary ];
      · convert this using 1;
    refine' ⟨ U * Matrix.diagonal ( fun i => if D i = 0 then 0 else ( D i : ℂ ) ⁻¹ ) * Uᴴ, _, _, _, _ ⟩ <;> simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
    · congr! 2 ; aesop;
    · simp +decide [ ← mul_assoc, hD.1 ];
      simp +decide [ mul_comm ];
    · simp_all +decide [ ← Matrix.mul_assoc ];
      exact congr_arg₂ _ ( congr_arg _ ( by ext i j; by_cases hi : i = j <;> aesop ) ) rfl;
    · simp_all +decide [ ← Matrix.mul_assoc ];
  refine' ⟨ R * Tp, Tp, rfl, _, _, _, _ ⟩;
  · have hRTpT : (R * Tp * T - R)ᴴ * (R * Tp * T - R) = 0 := by
      simp_all +decide [ mul_sub, sub_mul, ← Matrix.mul_assoc ];
      simp_all +decide [ mul_assoc, ← hT_sq ];
    exact sub_eq_zero.mp ( by simpa [ Matrix.mul_assoc ] using Matrix.conjTranspose_mul_self_eq_zero.mp hRTpT );
  · simp_all +decide [ Matrix.mul_assoc, Matrix.IsHermitian ];
    constructor <;> simp_all +decide [ ← Matrix.mul_assoc, IsIdempotentElem ];
    · simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
    · grind +qlia;
  · simp +decide [ ← mul_assoc, hTp.1.eq ];
    grind +qlia;
  · have h_rank_eq : (Tp * T).rank = T.rank ∧ T.rank = R.rank := by
      have h_rank_eq : (Tp * T).rank = T.rank := by
        refine' le_antisymm _ _;
        · exact Matrix.rank_mul_le_right _ _;
        · have := Matrix.rank_mul_le ( Tp * T ) T; simp_all +decide [ Matrix.mul_assoc ] ;
          grind;
      have h_rank_eq : T.rank = (T * T).rank := by
        refine' le_antisymm _ _;
        · have := Matrix.rank_mul_le ( T * T ) Tp; simp_all +decide [ Matrix.mul_assoc ] ;
          grind +splitIndPred;
        · exact Matrix.rank_mul_le_left _ _;
      grind +suggestions;
    simp_all +decide [ ← mul_assoc, Matrix.IsHermitian ];
    grind +splitImp

omit [DecidableEq ι] in
/-
**Cross-term vanishing from orthogonal ranges.**  If `W, W₁` are partial
isometries (`Wᴴ*W`, `W₁ᴴ*W₁` idempotent) whose final (range) projections
`W*Wᴴ`, `W₁*W₁ᴴ` are orthogonal, then `Wᴴ * W₁ = 0`.
-/
lemma conjTranspose_mul_eq_zero_of_range_orth {W W1 : Matrix ι ι ℂ}
    (hW : IsIdempotentElem (Wᴴ * W)) (hW1 : IsIdempotentElem (W1ᴴ * W1))
    (hrng : (W * Wᴴ) * (W1 * W1ᴴ) = 0) :
    Wᴴ * W1 = 0 := by
  have hW1_zero : W1 * W1ᴴ * W1 = W1 := by
    exact?
  have hW_zero : Wᴴ * W * Wᴴ = Wᴴ := by
    convert congr_arg Matrix.conjTranspose ( partialIsometry_mul_self hW ) using 1;
    simp +decide [ Matrix.mul_assoc, Matrix.conjTranspose_mul ];
  replace hrng := congr_arg ( fun m => Wᴴ * m * W1 ) hrng ; simp_all +decide [ Matrix.mul_assoc ];
  simp_all +decide [ ← Matrix.mul_assoc ]

omit [DecidableEq ι] in
/-
**Cross-term vanishing from orthogonal sources.**  If `W, W₁` are partial
isometries whose initial (source) projections `Wᴴ*W`, `W₁ᴴ*W₁` are orthogonal,
then `W * W₁ᴴ = 0`.
-/
lemma mul_conjTranspose_eq_zero_of_src_orth {W W1 : Matrix ι ι ℂ}
    (hW : IsIdempotentElem (Wᴴ * W)) (hW1 : IsIdempotentElem (W1ᴴ * W1))
    (hsrc : (Wᴴ * W) * (W1ᴴ * W1) = 0) :
    W * W1ᴴ = 0 := by
  have hW1H : W1ᴴ = (W1ᴴ * W1) * W1ᴴ := by
    have hW1H : W1 * W1ᴴ * W1 = W1 := by
      exact?;
    apply_fun Matrix.conjTranspose at hW1H; simp_all +decide [ Matrix.mul_assoc ] ;
  conv_lhs => rw [ hW1H, ← Matrix.mul_assoc ];
  have hW1H : W * (W1ᴴ * W1) = W * (Wᴴ * W) * (W1ᴴ * W1) := by
    simp +decide [ ← mul_assoc ];
    have := partialIsometry_mul_self hW; simp +decide [ mul_assoc, this ] ;
  simp +decide [ hW1H, Matrix.mul_assoc, hsrc ]

omit [DecidableEq ι] in
/-
**The polar norm identity.**  Under the structural facts of the polar
decomposition, `‖R - (W + W₁)‖_HS = ‖T - Q‖_HS` where `T` is Hermitian.
-/
lemma normHS_polar_eq {R T W W1 Q : Matrix ι ι ℂ}
    (hT : T.IsHermitian) (hQ : IsProj Q)
    (hWT : W * T = R)
    (hsT : (Wᴴ * W) * T = T)
    (hcross : Wᴴ * W1 = 0)
    (hVV : (W + W1)ᴴ * (W + W1) = Q)
    (hQT : Q * T = T) :
    normHS (R - (W + W1)) = normHS (T - Q) := by
  apply_fun Matrix.conjTranspose at hsT hQT;
  simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
  apply_fun Matrix.conjTranspose at hQT; simp_all +decide [ IsProj ] ;
  have h_norm_eq : normHS (R - (W + W1)) ^ 2 = ntrace (Rᴴ * R - Rᴴ * (W + W1) - (W + W1)ᴴ * R + Q) := by
    rw [ ← hVV ];
    convert normHS_sq_eq_ntrace ( R - ( W + W1 ) ) using 1 ; simp +decide [ sub_mul, mul_sub ] ; abel_nf;
  have h_norm_eq : normHS (T - Q) ^ 2 = ntrace (T * T - T - T + Q) := by
    rw [ normHS_sq_eq_ntrace ];
    simp_all +decide [ Matrix.IsHermitian, IsIdempotentElem ];
    simp +decide [ sub_mul, mul_sub, hQT, hQ.2 ];
    rw [ show T * Q = T by rw [ ← Matrix.conjTranspose_inj, Matrix.conjTranspose_mul, hT, hQ.1, hQT ] ] ; abel_nf;
  have h_norm_eq : Rᴴ * (W + W1) = T := by
    simp_all +decide [ Matrix.mul_add, Matrix.add_mul ];
    rw [ ← hWT ] at *; simp_all +decide [ Matrix.mul_assoc ] ;
  have h_norm_eq : (W + W1)ᴴ * R = T := by
    apply_fun Matrix.conjTranspose at h_norm_eq; simp_all +decide [] ;
  have h_norm_eq : Rᴴ * R = T * T := by
    simp_all +decide [ ← hWT, Matrix.mul_assoc ];
    simp_all +decide [ ← Matrix.mul_assoc ];
  rw [ ← sq_eq_sq₀ ( LamplighterStability.normHS_nonneg _ ) ( LamplighterStability.normHS_nonneg _ ), ‹normHS ( R - ( W + W1 ) ) ^ 2 = ntrace ( Rᴴ * R - Rᴴ * ( W + W1 ) - ( W + W1 ) ᴴ * R + Q ) ›, ‹normHS ( T - Q ) ^ 2 = ntrace ( T * T - T - T + Q ) › ] ; aesop

set_option maxHeartbeats 4000000 in
/-- **Polar decomposition with full partial isometry (core of `claim:svd`).**
Under the hypotheses of `claim_svd`, there is a partial isometry `V` with
`V* V = Q`, `V V* = P` and the exact identity
`‖R − V‖_HS = ‖√(R* R) − Q‖_HS`.

This is the matrix polar decomposition `R = V·√(R*R)` with `V` extended (using
`rank P = rank Q`) to a partial isometry of source `Q` and range `P`; no
`PartialIsometry` / polar-decomposition API exists in the current Mathlib. -/
lemma exists_partialIsometry_polar (R P Q : Matrix ι ι ℂ)
    (hP : IsProj P) (hQ : IsProj Q)
    (hrank : P.rank = Q.rank)
    (hRRP : (P - R * Rᴴ).PosSemidef)
    (hRRQ : (Q - Rᴴ * R).PosSemidef) :
    ∃ V : Matrix ι ι ℂ,
      Vᴴ * V = Q ∧ V * Vᴴ = P ∧
      normHS (R - V) = normHS (CFC.sqrt (Rᴴ * R) - Q) := by
  set T := CFC.sqrt (Rᴴ * R);
  obtain ⟨W, Tp, hW1, hW2, hW3, hW4, hW5, hW6⟩ := exists_polar_partialIsometry R;
  set s := Wᴴ * W;
  set r := W * Wᴴ;
  have hs : IsProj s := hW3;
  have hr : IsProj r := isProj_mulConjTranspose_of_isProj hs;
  have hrk : r.rank = R.rank := by
    grind +suggestions;
  have hsQ : ProjLE s Q := by
    have hQs : Q * s = s := by
      have hQs : Q * T = T := by
        apply proj_mul_sqrt_eq_of_psd_le hQ (Matrix.posSemidef_conjTranspose_mul_self R) hRRQ |>.1;
      grind;
    have hQs' : s * Q = s := by
      convert congr_arg Matrix.conjTranspose hQs using 1 ; simp +decide [ Matrix.conjTranspose_mul, hQ.1.eq ];
      · simp +zetaDelta at *;
      · exact hs.1.symm;
    have hQs'' : (Q - s) * (Q - s) = Q - s := by
      simp_all +decide [ sub_mul, mul_sub, IsProj ];
      simp_all +decide [ IsIdempotentElem ];
    have hQs''' : (Q - s).IsHermitian := by
      simp_all +decide [ Matrix.IsHermitian, IsProj ];
    have hQs'''' : (Q - s).PosSemidef := by
      have hQs'''' : (Q - s) = (Q - s)ᴴ * (Q - s) := by
        rw [ hQs'''.eq, hQs'' ]
      exact hQs'''' ▸ Matrix.posSemidef_conjTranspose_mul_self _;
    exact hQs'''';
  have hrP : ProjLE r P := by
    have hrP : P * r = r := by
      have hrP : P * W = W := by
        have hP_W : P * R = R := by
          apply proj_mul_eq_self_of_psd_le hP hRRP;
        rw [ hW1, ← Matrix.mul_assoc, hP_W ];
      grind +suggestions;
    have hrP : r * P = r := by
      convert congr_arg Matrix.conjTranspose hrP using 1 ; simp +decide [ Matrix.conjTranspose_mul ];
      · simp +zetaDelta at *;
        exact hP.1.symm ▸ rfl;
      · simp +zetaDelta at *;
    have hrP : (P - r) * (P - r) = P - r := by
      simp_all +decide [ sub_mul, mul_sub ];
      simp_all +decide [ IsProj, IsIdempotentElem ];
    have hrP : (P - r).IsHermitian := by
      simp_all +decide [ Matrix.IsHermitian, IsProj ];
    have hrP : (P - r).PosSemidef := by
      have h_idempotent : (P - r) * (P - r) = P - r := by
        assumption
      convert Matrix.posSemidef_conjTranspose_mul_self ( P - r ) using 1;
      convert h_idempotent.symm using 1;
      rw [ hrP.eq ];
    exact hrP;
  have hE : IsProj (Q - s) := isProj_sub_of_projLE hQ hs hsQ;
  have hF : IsProj (P - r) := isProj_sub_of_projLE hP hr hrP;
  have hEF : (Q - s).rank = (P - r).rank := by
    have := rank_sub_of_projLE hQ hs hsQ; have := rank_sub_of_projLE hP hr hrP; simp_all +decide ;
    exact_mod_cast ( by linarith : ( Q - CFC.sqrt ( Rᴴ * R ) * Tp |> Matrix.rank : ℝ ) = ( P - r |> Matrix.rank : ℝ ) );
  obtain ⟨W1, hL, hR⟩ := exists_partialIsometry_equal_rank hE hF hEF;
  have hcrossR : Wᴴ * W1 = 0 := by
    apply conjTranspose_mul_eq_zero_of_range_orth hs.2 (by
    exact hL.symm ▸ hE.2) (by
    simp +decide [ hR, mul_sub ];
    simp +zetaDelta at *;
    have hP_W : P * W = W := by
      convert proj_mul_eq_self_of_psd_le hP _ using 1;
      exact hrP;
    apply_fun ( fun x => x * Wᴴ ) at hP_W; simp +decide [ mul_assoc ] at hP_W;
    rw [ ← Matrix.conjTranspose_inj ] ; simp +decide [ hP.1.eq ];
    rw [ hP_W, hr.2, sub_self ]);
  have hcrossS : W * W1ᴴ = 0 := by
    apply mul_conjTranspose_eq_zero_of_src_orth hs.2 (by
    exact hL.symm ▸ hE.2) (by
    simp +decide [ hL ];
    simp +decide [ mul_sub ];
    have hQs : Q * s = s := by
      grind +suggestions;
    have hQs : s * Q = s := by
      convert congr_arg Matrix.conjTranspose hQs using 1;
      · simp +decide [ hQ.1.eq ];
        simp +decide [ s, Matrix.conjTranspose_mul ];
      · exact hs.1.symm;
    simp +zetaDelta at *;
    simp +decide [ hQs, hs.2.eq ]);
  have hV : (W + W1)ᴴ * (W + W1) = Q := by
    simp +decide [ add_mul, mul_add, hcrossR, hL ];
    simp +zetaDelta at *;
    rw [ show W1ᴴ * W = 0 by simpa [ Matrix.mul_assoc ] using congr_arg Matrix.conjTranspose hcrossR ] ; simp +decide [ add_sub_cancel ] ;
  have hV' : (W + W1) * (W + W1)ᴴ = P := by
    simp +decide [ add_mul, mul_add, hcrossS, hR ];
    simp +zetaDelta at *;
    rw [ show W1 * Wᴴ = 0 from by simpa [ Matrix.mul_assoc ] using congr_arg Matrix.conjTranspose hcrossS ] ; simp +decide [ add_sub_cancel ];
  have hnorm : normHS (R - (W + W1)) = normHS (T - Q) := by
    apply normHS_polar_eq;
    any_goals assumption;
    · exact ( CFC.sqrt_nonneg _ ).posSemidef.1;
    · grind +suggestions;
  exact ⟨W + W1, hV, hV', hnorm⟩

/-- **Claim `claim:svd` (polar decomposition / SVD).**  Let `R` be a matrix with
`R* R ≤ Q` and `R R* ≤ P` (Löwner order, expressed via positive semidefiniteness
of the differences), where `P, Q` are projections of the same rank.  Then there
is a partial isometry `V` with `V* V = Q`, `V V* = P` and
`‖R − V‖_HS ≤ ‖R* R − Q‖_HS`.

This is the matrix polar decomposition (no `PartialIsometry` API exists in the
current Mathlib), proved here from the spectral theorem / continuous functional
calculus: writing `R = V T` with `T = (R*R)^{1/2}` supported on `Q` and `V` the
induced partial isometry, one has
`‖R − V‖_HS = ‖T − Q‖_HS = ‖(R*R)^{1/2} − Q‖_HS ≤ ‖R*R − Q‖_HS`,
the last step using `1 − z ≤ 1 − z²` for `z ∈ [0,1]`. -/
lemma claim_svd (R P Q : Matrix ι ι ℂ)
    (hP : IsProj P) (hQ : IsProj Q)
    (hrank : P.rank = Q.rank)
    (hRRP : (P - R * Rᴴ).PosSemidef)
    (hRRQ : (Q - Rᴴ * R).PosSemidef) :
    ∃ V : Matrix ι ι ℂ,
      Vᴴ * V = Q ∧ V * Vᴴ = P ∧
      normHS (R - V) ≤ normHS (Rᴴ * R - Q) := by
  obtain ⟨V, hVQ, hVP, hVnorm⟩ :=
    exists_partialIsometry_polar R P Q hP hQ hrank hRRP hRRQ
  refine ⟨V, hVQ, hVP, ?_⟩
  rw [hVnorm]
  exact sqrt_sub_proj_normHS_le hQ (Matrix.posSemidef_conjTranspose_mul_self R) hRRQ

/-! ## The dimension/trace claim (`claim:p-bound`) -/

/-
**Total-variation / telescoping bound.**  For a real sequence `a` and indices
`i, i' < j`, the gap `|a i − a i'|` is bounded by the total variation
`∑_{k<j-1} |a (k+1) − a k|`.
-/
lemma abs_sub_le_sum_consecutive (a : ℕ → ℝ) {j i i' : ℕ}
    (hi : i < j) (hi' : i' < j) :
    |a i - a i'| ≤ ∑ k ∈ Finset.range (j - 1), |a (k + 1) - a k| := by
  by_cases h_cases : i ≤ i';
  · -- By the triangle inequality, we have $|a i - a i'| \leq \sum_{k=i}^{i'-1} |a (k + 1) - a k|$.
    have h_triangle : abs (a i - a i') ≤ ∑ k ∈ Finset.Ico i i', abs (a (k + 1) - a k) := by
      induction h_cases <;> simp_all +decide [ Finset.sum_Ico_succ_top ];
      rename_i k hk ih; specialize ih ( by linarith ) ; cases abs_cases ( a i - a ( k + 1 ) ) <;> cases abs_cases ( a ( k + 1 ) - a k ) <;> cases abs_cases ( a i - a k ) <;> linarith;
    exact h_triangle.trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_iff.mpr fun x hx => Finset.mem_range.mpr ( by linarith [ Finset.mem_Ico.mp hx, Nat.sub_add_cancel ( by linarith : 1 ≤ j ) ] ) ) fun _ _ _ => abs_nonneg _ );
  · have h_telescope : |a i - a i'| ≤ ∑ k ∈ Finset.Ico i' i, |a (k + 1) - a k| := by
      convert Finset.abs_sum_le_sum_abs _ _ using 2;
      · rw [ Finset.sum_Ico_eq_sub _ ( by linarith ) ];
        rw [ Finset.sum_range_sub, Finset.sum_range_sub ] ; ring;
      · infer_instance;
    exact h_telescope.trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_iff.mpr fun x hx => Finset.mem_range.mpr ( by linarith [ Finset.mem_Ico.mp hx, Nat.sub_add_cancel ( by linarith : 1 ≤ j ) ] ) ) fun _ _ _ => abs_nonneg _ )

/-
**Claim `claim:p-bound`.**  Given pairwise orthogonal projections
`P_0, …, P_{j-1}` with support `P`, there exist orthogonal projections
`P'_0, …, P'_{j-1}`, each of the same rank, with `P'_i ≤ P_i`, such that
`∑_i ‖P'_i − P_i‖² ≤ j · ∑_{i<j-1} |tr P_{i+1} − tr P_i|`, and
`∑_i |tr P_i − tr(P)/j| ≤ 2j · ∑_{i<j-1} |tr P_{i+1} − tr P_i|`.
-/
lemma claim_p_bound (j : ℕ) (P : ℕ → Matrix ι ι ℂ)
    (hP : PairwiseOrthProj j P) :
    ∃ P' : ℕ → Matrix ι ι ℂ,
      (∀ i < j, IsProj (P' i)) ∧
      (∀ i < j, ProjLE (P' i) (P i)) ∧
      (∀ i < j, ∀ k < j, (P' i).rank = (P' k).rank) ∧
      (∑ i ∈ Finset.range j, normHS (P' i - P i) ^ 2
        ≤ (j : ℝ) * ∑ i ∈ Finset.range (j - 1),
            |ntrace (P (i + 1)) - ntrace (P i)|) ∧
      (∑ i ∈ Finset.range j,
          |ntrace (P i) - ntrace (towerSupport j P) / j|
        ≤ 2 * (j : ℝ) * ∑ i ∈ Finset.range (j - 1),
            |ntrace (P (i + 1)) - ntrace (P i)|) := by
  by_cases hj : 0 < j;
  · obtain ⟨i₀, hi₀⟩ : ∃ i₀ < j, ∀ i < j, ntrace (P i₀) ≤ ntrace (P i) := by
      simpa using Finset.exists_min_image ( Finset.range j ) ( fun i => ntrace ( P i ) ) ⟨ _, Finset.mem_range.mpr hj ⟩;
    have hP'_def : ∀ i < j, ∃ Q : Matrix ι ι ℂ, IsProj Q ∧ ProjLE Q (P i) ∧ Q.rank = (P i₀).rank := by
      exact fun i hi => exists_subproj_of_rank ( hP.1 i hi ) ( by
        have := hi₀.2 i hi;
        rw [ ntrace_eq_rank_div ( hP.1 i₀ hi₀.1 ), ntrace_eq_rank_div ( hP.1 i hi ) ] at this;
        by_cases h : Fintype.card ι = 0 <;> simp_all +decide;
        · simp_all +decide [ Fintype.card_eq_zero_iff ];
          simp +decide [ Matrix.rank ];
          simp +decide [ Module.finrank ];
        · rw [ div_le_div_iff_of_pos_right ] at this <;> norm_cast at * ; positivity );
    choose! Q hQ₁ hQ₂ hQ₃ using hP'_def;
    refine' ⟨ Q, hQ₁, hQ₂, fun i hi k hk => by rw [ hQ₃ i hi, hQ₃ k hk ], _, _ ⟩;
    · have h_sum_sq : ∑ i ∈ Finset.range j, normHS (Q i - P i) ^ 2 = ∑ i ∈ Finset.range j, (ntrace (P i) - ntrace (P i₀)) := by
        apply Finset.sum_congr rfl;
        intro i hi;
        have := normHS_projLE_sq ( hP.1 i ( Finset.mem_range.mp hi ) ) ( hQ₁ i ( Finset.mem_range.mp hi ) ) ( hQ₂ i ( Finset.mem_range.mp hi ) );
        rw [ this, ntrace_eq_rank_div ( hQ₁ i ( Finset.mem_range.mp hi ) ), ntrace_eq_rank_div ( hP.1 i₀ hi₀.1 ), hQ₃ i ( Finset.mem_range.mp hi ) ];
      have h_sum_abs : ∀ i < j, |ntrace (P i) - ntrace (P i₀)| ≤ ∑ k ∈ Finset.range (j - 1), |ntrace (P (k + 1)) - ntrace (P k)| := by
        intro i hi;
        convert abs_sub_le_sum_consecutive ( fun k => ntrace ( P k ) ) hi hi₀.1 using 1;
      exact h_sum_sq.symm ▸ le_trans ( Finset.sum_le_sum fun i hi => show ntrace ( P i ) - ntrace ( P i₀ ) ≤ ∑ k ∈ Finset.range ( j - 1 ), |ntrace ( P ( k + 1 ) ) - ntrace ( P k )| from le_of_abs_le ( h_sum_abs i ( Finset.mem_range.mp hi ) ) ) ( by simp +decide );
    · -- By the properties of the trace and the definition of $Q$, we have:
      have h_trace_sum : ∑ i ∈ Finset.range j, ntrace (P i) = ntrace (towerSupport j P) := by
        unfold towerSupport ntrace;
        simp +decide [ Finset.mul_sum _ _ _ ];
      have h_trace_bound : ∑ i ∈ Finset.range j, |ntrace (P i) - ntrace (P i₀)| ≤ j * ∑ i ∈ Finset.range (j - 1), |ntrace (P (i + 1)) - ntrace (P i)| := by
        have h_trace_bound : ∀ i < j, |ntrace (P i) - ntrace (P i₀)| ≤ ∑ k ∈ Finset.range (j - 1), |ntrace (P (k + 1)) - ntrace (P k)| := by
          intro i hi;
          have := abs_sub_le_sum_consecutive ( fun k => ntrace ( P k ) ) hi hi₀.1;
          exact this;
        exact le_trans ( Finset.sum_le_sum fun i hi => h_trace_bound i ( Finset.mem_range.mp hi ) ) ( by simp +decide );
      have h_trace_bound : ∑ i ∈ Finset.range j, |ntrace (P i) - ntrace (towerSupport j P) / j| ≤ ∑ i ∈ Finset.range j, |ntrace (P i) - ntrace (P i₀)| + ∑ i ∈ Finset.range j, |ntrace (P i₀) - ntrace (towerSupport j P) / j| := by
        simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_le_sum fun i _ => abs_sub_le _ _ _;
      have h_trace_bound : ∑ i ∈ Finset.range j, |ntrace (P i₀) - ntrace (towerSupport j P) / j| ≤ j * ∑ i ∈ Finset.range (j - 1), |ntrace (P (i + 1)) - ntrace (P i)| := by
        have h_trace_bound : ntrace (P i₀) ≤ ntrace (towerSupport j P) / j := by
          rw [ le_div_iff₀' ( Nat.cast_pos.mpr hj ) ];
          exact h_trace_sum ▸ le_trans ( by simp +decide [ mul_comm ] ) ( Finset.sum_le_sum fun i hi => hi₀.2 i ( Finset.mem_range.mp hi ) );
        have h_trace_bound : ∑ i ∈ Finset.range j, (ntrace (P i) - ntrace (P i₀)) ≤ j * ∑ i ∈ Finset.range (j - 1), |ntrace (P (i + 1)) - ntrace (P i)| := by
          exact le_trans ( Finset.sum_le_sum fun _ _ => le_abs_self _ ) ‹_›;
        simp_all +decide [ abs_of_nonpos ];
        rw [ mul_div_cancel₀ ] <;> first | positivity | linarith;
      grind;
  · aesop

end LamplighterStability