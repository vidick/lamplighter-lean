import RequestProject.TowerRounding
import RequestProject.TowerToRep

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

/-!
# Lemma `lem:lowd` — Rounding approximate closed projection towers

This file proves the capstone of Block A of the roadmap, Lemma `lem:lowd`:
every approximate `(δ₁, δ₂)`-closed projection tower can be *rounded* to a true
closed projection tower that is `(ε₁, ε₂)`-close to it, with
`ε₁ = O(j·δ₁)` and `ε₂ = O(j²·δ₁ + δ₂)`.

The construction follows the paper:

* Step 1 (`claim_p_bound`): replace each `Pᵢ` by an equal-rank sub-projection
  `P'ᵢ ≤ Pᵢ` so that `∑ ‖P'ᵢ − Pᵢ‖² ≤ j·δ₁`.
* Step 2 (`claim_svd`): for each `i`, polar-decompose `P'ᵢ R P'_{cyc i}` into a
  partial isometry `Vᵢ` with source `P'_{cyc i}` and range `P'ᵢ`, and assemble
  `R' = ∑ᵢ Vᵢ + (I − P')`, a unitary realizing a true closed tower.

The structural facts (`R'` is unitary, forms a closed tower, acts as the
identity off `P'`) are proved here, as are the supporting partial-isometry
identities.  The quantitative closeness bound `ε₂` is the analytic core.
-/

namespace LamplighterStability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The cyclic successor -/

/-- The cyclic successor on `{0, …, j−1}`: `cyc j i = i+1` if `i+1 < j`, else `0`. -/
def cyc (j i : ℕ) : ℕ := if i + 1 < j then i + 1 else 0

lemma cyc_lt {j i : ℕ} (hj : 0 < j) : cyc j i < j := by
  unfold cyc; split <;> omega

lemma cyc_inj {j i k : ℕ} (hi : i < j) (hk : k < j) (h : cyc j i = cyc j k) :
    i = k := by
  unfold cyc at h; split_ifs at h <;> omega

/-! ## Partial-isometry identities -/

omit [DecidableEq ι] in
/-
If `Vᴴ V = Q` is a projection, then `V` fixes `Q` on the right: `V Q = V`.
-/
lemma pisom_mul_source {V Q : Matrix ι ι ℂ}
    (hQ : Vᴴ * V = Q) (hQi : IsIdempotentElem Q) : V * Q = V := by
  have h_key : (V - V * Q)ᴴ * (V - V * Q) = 0 := by
    simp_all +decide [ Matrix.mul_sub, Matrix.sub_mul, mul_assoc, IsIdempotentElem ];
    simp_all +decide [ ← Matrix.mul_assoc ];
  exact Eq.symm ( sub_eq_zero.mp ( Matrix.conjTranspose_mul_self_eq_zero.mp h_key ) )

omit [DecidableEq ι] in
/-
If `V Vᴴ = P` is a projection, then `P` fixes `V` on the left: `P V = V`.
-/
lemma pisom_range_mul {V P : Matrix ι ι ℂ}
    (hP : V * Vᴴ = P) (hPi : IsIdempotentElem P) : P * V = V := by
  convert congr_arg Matrix.conjTranspose ( pisom_mul_source ( show ( Vᴴ ) ᴴ * Vᴴ = P from ?_ ) ?_ ) using 1;
  · simp +decide [ ← hP, Matrix.mul_assoc ];
  · rw [ Matrix.conjTranspose_conjTranspose ];
  · aesop;
  · exact hPi

/-
For projections `P, M`, the matrix `P − P M P` is positive semidefinite.
-/
lemma psd_proj_sub_conj {P M : Matrix ι ι ℂ} (hP : IsProj P) (hM : IsProj M) :
    (P - P * M * P).PosSemidef := by
  have h_pos : (Pᴴ * (1 - M) * P).PosSemidef := by
    exact Matrix.PosSemidef.conjTranspose_mul_mul_same ( posSemidef_one_sub_isProj hM ) P;
  convert h_pos using 1 ; simp +decide [ mul_sub, sub_mul, hP.1.eq, hP.2.eq ]

/-! ## Orthogonality of a partial-isometry family -/

section Family

variable {j : ℕ} {P' V : ℕ → Matrix ι ι ℂ}

omit [DecidableEq ι] in
/-
Distinct partial isometries in the rounded family have orthogonal sources.
-/
lemma pisom_family_orthH
    (hPproj : ∀ i < j, IsProj (P' i))
    (hPorth : ∀ i < j, ∀ k < j, i ≠ k → P' i * P' k = 0)
    (hrng : ∀ i < j, (V i) * (V i)ᴴ = P' i)
    {i k : ℕ} (hi : i < j) (hk : k < j) (hik : i ≠ k) :
    (V i)ᴴ * (V k) = 0 := by
  -- From hrng i hi, we get P' i * V i = V i. Taking conjTranspose gives (V i)ᴴ * P' i = (V i)ᴴ.
  have h1 : (V i)ᴴ * P' i = (V i)ᴴ := by
    convert congr_arg Matrix.conjTranspose ( pisom_range_mul ( hrng i hi ) ( hPproj i hi |>.2 ) ) using 1 ; simp +decide [];
    rw [ ← hrng i hi, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose ];
  have := pisom_range_mul ( hrng k hk ) ( hPproj k hk |>.2 );
  simp_all +decide [];
  rw [ ← this, ← h1, Matrix.mul_assoc ];
  simp +decide [ ← mul_assoc, hPorth i hi k hk hik ]


end Family

/-
Reindexing a sum over `range j` along the cyclic successor `cyc j` is the
identity on the value of the sum.
-/
lemma sum_cyc_reindex {M : Type*} [AddCommMonoid M] (j : ℕ) (f : ℕ → M) :
    ∑ m ∈ Finset.range j, f (cyc j m) = ∑ k ∈ Finset.range j, f k := by
  rcases j with ( _ | j ) <;> simp_all +decide [ cyc ];
  rw [ Finset.sum_range_succ, Finset.sum_range_succ' ];
  exact congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun x hx => by rw [ if_pos ( Finset.mem_range.mp hx ) ] ) ( by simp +decide )

/-! ## The rounded unitary -/

/-- The rounded operator `R' = ∑_{i<j} Vᵢ + (I − P')`. -/
noncomputable def roundedR (j : ℕ) (P' V : ℕ → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (∑ i ∈ Finset.range j, V i) + (1 - towerSupport j P')

section Rounded

variable {j : ℕ} {P' V : ℕ → Matrix ι ι ℂ}

/-
`(R')ᴴ = ∑ (Vᵢ)ᴴ + (1 − P')`.
-/
lemma roundedR_conjTranspose
    (hPproj : ∀ i < j, IsProj (P' i))
    (hPorth : ∀ i < j, ∀ k < j, i ≠ k → P' i * P' k = 0) :
    (roundedR j P' V)ᴴ
      = (∑ i ∈ Finset.range j, (V i)ᴴ) + (1 - towerSupport j P') := by
  convert Matrix.conjTranspose_add _ _ using 2;
  · rw [ Matrix.conjTranspose_sum ];
  · simp +decide [];
    exact Eq.symm ( towerSupport_isHermitian ⟨ hPproj, hPorth ⟩ )

/-
`Vₖ` is supported on the right inside `P'_{cyc k} ≤ P'`, hence killed by `1 − P'`.
-/
lemma roundedR_V_comp
    (hPproj : ∀ i < j, IsProj (P' i))
    (hPorth : ∀ i < j, ∀ k < j, i ≠ k → P' i * P' k = 0)
    (hsrc : ∀ i < j, (V i)ᴴ * (V i) = P' (cyc j i))
    {k : ℕ} (hk : k < j) :
    V k * (1 - towerSupport j P') = 0 := by
  rw [ mul_sub, mul_one, show V k * towerSupport j P' = V k from ?_ ];
  · rw [ sub_self ];
  · have hV_k : V k = V k * P' (cyc j k) := by
      have := hPproj ( cyc j k ) ( by
        exact cyc_lt ( pos_of_gt hk ) );
      have := pisom_mul_source ( hsrc k hk ) this.2; aesop;
    rw [ hV_k, mul_assoc, proj_mul_towerSupport ];
    · exact ⟨ hPproj, hPorth ⟩;
    · exact cyc_lt ( pos_of_gt hk )

/-
`(1 − P')` kills `(Vₖ)ᴴ` on the right.
-/
lemma roundedR_comp_VH
    (hPproj : ∀ i < j, IsProj (P' i))
    (hPorth : ∀ i < j, ∀ k < j, i ≠ k → P' i * P' k = 0)
    (hsrc : ∀ i < j, (V i)ᴴ * (V i) = P' (cyc j i))
    {k : ℕ} (hk : k < j) :
    (1 - towerSupport j P') * (V k)ᴴ = 0 := by
  have hT_VkH : towerSupport j P' * (V k)ᴴ = (V k)ᴴ := by
    have hT_VkH : towerSupport j P' * (P' (cyc j k)) = P' (cyc j k) := by
      apply towerSupport_mul_proj; exact ⟨hPproj, hPorth⟩; exact cyc_lt (by linarith);
    have hT_VkH : (V k)ᴴ = P' (cyc j k) * (V k)ᴴ := by
      have hT_VkH : (V k) * (P' (cyc j k)) = V k := by
        convert pisom_mul_source ( hsrc k hk ) _ using 1;
        exact hPproj _ ( cyc_lt ( pos_of_gt hk ) ) |>.2;
      convert congr_arg ( fun x => xᴴ ) hT_VkH using 1;
      · rw [ hT_VkH ];
      · convert congr_arg ( fun x => xᴴ ) hT_VkH using 1;
        simp +decide [ ← hsrc k hk ];
    grind;
  simp +decide [ sub_mul, hT_VkH ]

/-
`Vₖ` is supported on the left inside `P'ₖ ≤ P'`, hence killed by `1 − P'`.
-/
lemma roundedR_VH_comp
    (hPproj : ∀ i < j, IsProj (P' i))
    (hPorth : ∀ i < j, ∀ k < j, i ≠ k → P' i * P' k = 0)
    (hrng : ∀ i < j, (V i) * (V i)ᴴ = P' i)
    {k : ℕ} (hk : k < j) :
    (V k)ᴴ * (1 - towerSupport j P') = 0 := by
  have hV_k_killed : (V k)ᴴ * P' k = (V k)ᴴ := by
    have hV_k_killed : P' k * V k = V k := by
      convert pisom_range_mul ( hrng k hk ) ( hPproj k hk |>.2 ) using 1;
    convert congr_arg Matrix.conjTranspose hV_k_killed using 1 ; simp +decide [];
    exact congr_arg _ ( hPproj k hk |>.1.eq.symm );
  simp_all +decide [ mul_sub, sub_eq_zero ];
  convert hV_k_killed.symm using 1;
  convert congr_arg ( fun x => ( V k ) ᴴ * x ) ( proj_mul_towerSupport ⟨ hPproj, hPorth ⟩ hk ) using 1;
  rw [ ← Matrix.mul_assoc, hV_k_killed ]

/-
`(1 − P')` kills `Vₖ` on the left.
-/
lemma roundedR_comp_V
    (hPproj : ∀ i < j, IsProj (P' i))
    (hPorth : ∀ i < j, ∀ k < j, i ≠ k → P' i * P' k = 0)
    (hrng : ∀ i < j, (V i) * (V i)ᴴ = P' i)
    {k : ℕ} (hk : k < j) :
    (1 - towerSupport j P') * V k = 0 := by
  have h_pisom : P' k * V k = V k := by
    convert pisom_range_mul ( hrng k hk ) ( hPproj k hk |>.2 ) using 1;
  have h_towerSupport_mul : towerSupport j P' * V k = V k := by
    have h_towerSupport_mul : towerSupport j P' * P' k = P' k := by
      apply towerSupport_mul_proj ⟨hPproj, hPorth⟩ hk;
    rw [ ← h_pisom, ← Matrix.mul_assoc, h_towerSupport_mul ];
  simp +decide [ sub_mul, h_towerSupport_mul ]

/-
`R'` acts as the identity on the complement of `P' = ∑ P'ᵢ`.
-/
lemma roundedR_comp
    (hPproj : ∀ i < j, IsProj (P' i))
    (hPorth : ∀ i < j, ∀ k < j, i ≠ k → P' i * P' k = 0)
    (hsrc : ∀ i < j, (V i)ᴴ * (V i) = P' (cyc j i)) :
    roundedR j P' V * (1 - towerSupport j P') = 1 - towerSupport j P' := by
  have h_roundedR_comp : (1 - towerSupport j P') * (1 - towerSupport j P') = 1 - towerSupport j P' := by
    simp +decide [ sub_mul, mul_sub, towerSupport_idem ⟨ hPproj, hPorth ⟩ ];
  simp +decide [ roundedR, h_roundedR_comp, Matrix.add_mul, Finset.sum_mul _ _ _ ];
  exact Finset.sum_eq_zero fun i hi => roundedR_V_comp hPproj hPorth hsrc ( Finset.mem_range.mp hi )

/-
The compression of `R'` to `P'` is exactly `∑ᵢ Vᵢ`.
-/
lemma roundedR_compress
    (hPproj : ∀ i < j, IsProj (P' i))
    (hPorth : ∀ i < j, ∀ k < j, i ≠ k → P' i * P' k = 0)
    (hsrc : ∀ i < j, (V i)ᴴ * (V i) = P' (cyc j i))
    (hrng : ∀ i < j, (V i) * (V i)ᴴ = P' i) :
    towerSupport j P' * roundedR j P' V * towerSupport j P'
      = ∑ i ∈ Finset.range j, V i := by
  have hT_roundedR : towerSupport j P' * roundedR j P' V = ∑ i ∈ Finset.range j, V i := by
    simp +decide [ roundedR, mul_add ];
    have h_compression : ∀ i < j, towerSupport j P' * V i = V i := by
      intro i hi;
      have := roundedR_comp_V hPproj hPorth hrng hi;
      simp_all +decide [ sub_mul ];
      exact Eq.symm ( sub_eq_zero.mp this );
    rw [ Matrix.mul_sum, Finset.sum_congr rfl fun i hi => h_compression i ( Finset.mem_range.mp hi ) ];
    simp +decide [ mul_sub, towerSupport_idem ( show PairwiseOrthProj j P' from ⟨ hPproj, hPorth ⟩ ) ];
  convert congr_arg ( fun x => x * towerSupport j P' ) hT_roundedR using 1;
  simp +decide [ Finset.sum_mul ];
  refine' Finset.sum_congr rfl fun i hi => _;
  have hT_Vi : V i * (1 - towerSupport j P') = 0 := by
    apply roundedR_V_comp hPproj hPorth hsrc (Finset.mem_range.mp hi);
  simp_all +decide [ mul_sub ];
  exact eq_of_sub_eq_zero hT_Vi

/-
The closed-tower conjugation identity: `R'ᴴ P'ₖ R' = P'_{cyc k}`.
-/
lemma roundedR_conj_proj
    (hPproj : ∀ i < j, IsProj (P' i))
    (hPorth : ∀ i < j, ∀ k < j, i ≠ k → P' i * P' k = 0)
    (hsrc : ∀ i < j, (V i)ᴴ * (V i) = P' (cyc j i))
    (hrng : ∀ i < j, (V i) * (V i)ᴴ = P' i)
    {k : ℕ} (hk : k < j) :
    (roundedR j P' V)ᴴ * P' k * roundedR j P' V = P' (cyc j k) := by
  convert congr_arg ( fun x => x * roundedR j P' V ) ( show ( roundedR j P' V )ᴴ * P' k = ( V k )ᴴ from ?_ ) using 1;
  · have h_sum : (V k)ᴴ * (∑ i ∈ Finset.range j, V i) = ∑ i ∈ Finset.range j, (V k)ᴴ * V i := by
      rw [ Finset.mul_sum _ _ _ ];
    rw [ roundedR, Matrix.mul_add, h_sum ];
    rw [ Finset.sum_eq_single k ] <;> simp_all +decide [];
    · exact roundedR_VH_comp hPproj hPorth hrng hk;
    · exact fun i hi hik => pisom_family_orthH hPproj hPorth hrng hk hi ( Ne.symm hik );
  · rw [ roundedR_conjTranspose hPproj hPorth ];
    simp +decide [ add_mul, Finset.sum_mul _ _ _ ];
    rw [ Finset.sum_eq_single k ];
    · have hVH_Pk : (V k)ᴴ * P' k = (V k)ᴴ := by
        have := hPproj k hk;
        convert congr_arg Matrix.conjTranspose ( pisom_range_mul ( hrng k hk ) this.2 ) using 1 ; simp +decide [ this.1.eq ];
      rw [ hVH_Pk, sub_mul, one_mul, towerSupport_mul_proj ⟨ hPproj, hPorth ⟩ hk, sub_self, add_zero ];
    · intro i hi hik
      have h_orth : (V i)ᴴ * (V k) = 0 := by
        apply pisom_family_orthH hPproj hPorth hrng (Finset.mem_range.mp hi) hk hik;
      rw [ ← hrng k hk, ← Matrix.mul_assoc, h_orth, Matrix.zero_mul ];
    · grind

/-
`R'` is unitary.
-/
lemma roundedR_unitary
    (hPproj : ∀ i < j, IsProj (P' i))
    (hPorth : ∀ i < j, ∀ k < j, i ≠ k → P' i * P' k = 0)
    (hsrc : ∀ i < j, (V i)ᴴ * (V i) = P' (cyc j i))
    (hrng : ∀ i < j, (V i) * (V i)ᴴ = P' i) :
    roundedR j P' V ∈ unitary (Matrix ι ι ℂ) := by
  -- By `unitary.mem_iff` it suffices to prove (roundedR)ᴴ * roundedR = 1 and roundedR * (roundedR)ᴴ = 1.
  apply Classical.byContradiction
  intro h_not_unitary;
  -- By `unitary.mem_iff` it suffices to prove (roundedR)ᴴ * roundedR = 1.
  have h_unitary_conj : (roundedR j P' V)ᴴ * roundedR j P' V = 1 := by
    -- Expanding the product using the definitions of `roundedR` and `roundedR_conjTranspose`.
    have h_expand : (roundedR j P' V)ᴴ * roundedR j P' V = (∑ m ∈ Finset.range j, (V m)ᴴ) * (∑ k ∈ Finset.range j, V k) + (1 - towerSupport j P') := by
      have h_expand : (roundedR j P' V)ᴴ * roundedR j P' V = (∑ m ∈ Finset.range j, (V m)ᴴ) * (∑ k ∈ Finset.range j, V k) + (∑ m ∈ Finset.range j, (V m)ᴴ) * (1 - towerSupport j P') + (1 - towerSupport j P') * (∑ k ∈ Finset.range j, V k) + (1 - towerSupport j P') * (1 - towerSupport j P') := by
        rw [ roundedR_conjTranspose, roundedR ];
        · simp +decide only [mul_add, add_mul] ; abel_nf;
        · exact hPproj;
        · exact hPorth;
      simp_all +decide [ Finset.sum_mul _ _ _, Finset.mul_sum ];
      simp_all +decide [ add_assoc ];
      rw [ Finset.sum_eq_zero, Finset.sum_eq_zero ] <;> simp_all +decide [ roundedR_VH_comp, roundedR_comp_V ];
      simp +decide [ sub_mul, mul_sub, towerSupport_idem ⟨ hPproj, hPorth ⟩ ];
    -- By `pisom_family_orthH`, the off-diagonal terms vanish, so this equals ∑_m (V m)ᴴ V m.
    have h_off_diag : (∑ m ∈ Finset.range j, (V m)ᴴ) * (∑ k ∈ Finset.range j, V k) = ∑ m ∈ Finset.range j, (V m)ᴴ * V m := by
      rw [ Finset.sum_mul, Finset.sum_congr rfl ];
      intro i hi; rw [ Finset.mul_sum _ _ _ ] ; rw [ Finset.sum_eq_single i ] <;> simp_all +decide ;
      exact fun k hk hki => pisom_family_orthH hPproj hPorth hrng hi hk ( Ne.symm hki );
    rw [ h_expand, h_off_diag, Finset.sum_congr rfl fun i hi => hsrc i ( Finset.mem_range.mp hi ) ];
    rw [ sum_cyc_reindex ];
    unfold towerSupport; simp +decide ;
  exact h_not_unitary ( by rw [ Unitary.mem_iff ] ; exact ⟨ h_unitary_conj, by rw [ mul_eq_one_comm ] at h_unitary_conj; exact h_unitary_conj ⟩ )

end Rounded

/-! ## The quantitative closeness bound `ε₂` (analytic core) -/

/-
`‖P·A‖ ≤ ‖A‖` for a projection `P`.
-/
lemma normHS_proj_mul_le {P A : Matrix ι ι ℂ} (hP : IsProj P) :
    normHS (P * A) ≤ normHS A := by
  have h_norm_sq : normHS (P * A) ^ 2 ≤ normHS A ^ 2 := by
    have h_norm_sq : normHS (P * A) ^ 2 = ntrace ((P * A)ᴴ * (P * A)) := by
      convert normHS_sq_eq_ntrace ( P * A ) using 1
    have h_norm_sq_A : normHS A ^ 2 = ntrace (Aᴴ * A) := by
      convert normHS_sq_eq_ntrace A using 1
    have h_diff : ntrace (Aᴴ * A) - ntrace ((P * A)ᴴ * (P * A)) = ntrace (Aᴴ * (1 - P) * A) := by
      simp +decide [ Matrix.mul_sub, Matrix.sub_mul, mul_assoc, hP.1.eq ];
      simp +decide [ ← mul_assoc, hP.2.eq, ntrace_sub ]
    have h_nonneg : 0 ≤ ntrace (Aᴴ * (1 - P) * A) := by
      have h_nonneg : (1 - P).PosSemidef := by
        convert posSemidef_one_sub_isProj hP using 1
      have h_nonneg : (Aᴴ * (1 - P) * A).PosSemidef := by
        convert h_nonneg.conjTranspose_mul_mul_same A using 1
      have h_nonneg : 0 ≤ ntrace (Aᴴ * (1 - P) * A) := by
        convert ntrace_nonneg_of_posSemidef h_nonneg using 1
      exact h_nonneg
    linarith [h_norm_sq, h_norm_sq_A, h_diff, h_nonneg];
  exact le_of_pow_le_pow_left₀ ( by norm_num ) ( normHS_nonneg _ ) h_norm_sq

/-
`‖A·P‖ ≤ ‖A‖` for a projection `P`.
-/
lemma normHS_mul_proj_le {P A : Matrix ι ι ℂ} (hP : IsProj P) :
    normHS (A * P) ≤ normHS A := by
  have h_norm : normHS (P * Aᴴ) ≤ normHS (Aᴴ) := by
    exact normHS_proj_mul_le hP;
  convert h_norm using 1;
  · convert normHS_conjTranspose ( A * P ) using 1;
    · rw [ normHS_conjTranspose ];
    · convert normHS_conjTranspose ( A * P ) using 1;
      rw [ Matrix.conjTranspose_mul, hP.1.eq ];
  · exact Eq.symm (normHS_conjTranspose A)

omit [DecidableEq ι] in
/-
Asymmetric `L²` split: separate the last summand from the rest.
-/
lemma normHS_sq_sum_split (j : ℕ) (hj : 0 < j) (a : ℕ → Matrix ι ι ℂ) :
    normHS (∑ m ∈ Finset.range j, a m) ^ 2
      ≤ 2 * (j - 1 : ℕ) * (∑ m ∈ Finset.range (j - 1), normHS (a m) ^ 2)
        + 2 * normHS (a (j - 1)) ^ 2 := by
  rcases j with ( _ | j ) <;> simp_all +decide [ Finset.sum_range_succ ];
  refine' le_trans ( pow_le_pow_left₀ ( by exact normHS_nonneg _ ) ( normHS_add_le _ _ ) 2 ) _;
  have := semitriangle j a;
  nlinarith [ sq_nonneg ( normHS ( ∑ i ∈ Finset.range j, a i ) - normHS ( a j ) ), normHS_nonneg ( ∑ i ∈ Finset.range j, a i ), normHS_nonneg ( a j ) ]

/-
Compressing `Rₘᴴ Pp Rₘ` by the projection `Q` only decreases the distance to `Q`:
`‖(Pp Rₘ Q)ᴴ (Pp Rₘ Q) − Q‖ ≤ ‖Rₘᴴ Pp Rₘ − Q‖`.
-/
lemma normHS_compress_diff_le {Pp Q Rm : Matrix ι ι ℂ}
    (hPp : IsProj Pp) (hQ : IsProj Q) :
    normHS ((Pp * Rm * Q)ᴴ * (Pp * Rm * Q) - Q) ≤ normHS (Rmᴴ * Pp * Rm - Q) := by
  -- Using the property that compressing by a projection only decreases the norm:
  have h_compression : normHS (Q * (Rmᴴ * Pp * Rm - Q) * Q) ≤ normHS (Rmᴴ * Pp * Rm - Q) := by
    refine' le_trans ( normHS_mul_proj_le hQ ) _;
    exact normHS_proj_mul_le hQ;
  convert h_compression using 2 ; simp +decide [ Matrix.mul_assoc, hPp.1.eq, hQ.1.eq ];
  simp +decide [ sub_mul, mul_sub, ← Matrix.mul_assoc, hPp.2.eq, hQ.2.eq ]

section Eps2

variable {j : ℕ} {P P' V : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}

/-
Per-floor `svd`-defect bound (`eq:lowd-2` content).
-/
lemma f_bound
    (hR : R ∈ unitary (Matrix ι ι ℂ))
    (hP'proj : ∀ i < j, IsProj (P' i))
    {m : ℕ} (hm : m < j) :
    normHS ((P' m * R * P' (cyc j m))ᴴ * (P' m * R * P' (cyc j m)) - P' (cyc j m)) ^ 2
      ≤ 3 * (normHS (Rᴴ * P m * R - P (cyc j m)) ^ 2
          + normHS (P m - P' m) ^ 2 + normHS (P (cyc j m) - P' (cyc j m)) ^ 2) := by
  -- Apply the normHS_compress_diff_le lemma to get the first part of the inequality.
  have h1 : normHS ((P' m * R * P' (cyc j m))ᴴ * (P' m * R * P' (cyc j m)) - P' (cyc j m)) ≤ normHS (Rᴴ * P' m * R - P' (cyc j m)) := by
    grind +suggestions;
  -- Let cm = cyc j m; since m < j, 0 < j and cm < j (cyc_lt).
  set cm := cyc j m
  have hcm : cm < j := by
    exact cyc_lt ( pos_of_gt hm );
  -- Let b = normHS (P m - P' m), y = normHS (Rᴴ * P m * R - P cm), and c = normHS (P cm - P' cm).
  set b := normHS (P m - P' m)
  set y := normHS (Rᴴ * P m * R - P cm)
  set c := normHS (P cm - P' cm);
  -- By the triangle inequality, we have:
  have h2 : normHS (Rᴴ * P' m * R - P' cm) ≤ b + y + c := by
    have h2 : normHS (Rᴴ * P' m * R - P' cm) ≤ normHS (Rᴴ * (P' m - P m) * R) + normHS (Rᴴ * P m * R - P cm) + normHS (P cm - P' cm) := by
      convert normHS_add_le ( Rᴴ * ( P' m - P m ) * R ) ( Rᴴ * P m * R - P cm + ( P cm - P' cm ) ) |> le_trans <| ?_ using 1;
      · simp +decide [ mul_sub, sub_mul, mul_assoc ];
      · linarith [ normHS_add_le ( Rᴴ * P m * R - P cm ) ( P cm - P' cm ) ];
    exact h2.trans ( add_le_add_three ( by simpa [ normHS_sub_comm ] using normHS_unitary_conj ( Unitary.star_mem hR ) ( P' m - P m ) |> le_of_eq ) le_rfl le_rfl );
  exact le_trans ( pow_le_pow_left₀ ( normHS_nonneg _ ) ( h1.trans h2 ) 2 ) ( by linarith [ sq_nonneg ( y - b ), sq_nonneg ( y - c ), sq_nonneg ( b - c ) ] )

/-
Per-floor `support-replacement` bound for the main difference.
-/
lemma g_bound
    (hR : R ∈ unitary (Matrix ι ι ℂ))
    (hPproj : ∀ i < j, IsProj (P i))
    (hPorth : ∀ i < j, ∀ k < j, i ≠ k → P i * P k = 0)
    (hP'proj : ∀ i < j, IsProj (P' i))
    {m : ℕ} (hm : m < j) :
    normHS (towerSupport j P * R * P (cyc j m) - P' m * R * P' (cyc j m)) ^ 2
      ≤ 12 * normHS (Rᴴ * P m * R - P (cyc j m)) ^ 2
          + 3 * normHS (P m - P' m) ^ 2 + 3 * normHS (P (cyc j m) - P' (cyc j m)) ^ 2 := by
  set T := towerSupport j P
  set cm := cyc j m
  set a := normHS (Rᴴ * P m * R - P cm)
  set b := normHS (P m - P' m)
  set c := normHS (P cm - P' cm);
  -- By the triangle inequality, we have:
  have h_triangle : normHS (T * R * P cm - P' m * R * P' cm) ≤ 2 * a + b + c := by
    have h_triangle : normHS (T * R * P cm - P' m * R * P' cm) ≤ normHS ((T - P' m) * R * P cm) + normHS (P' m * R * (P cm - P' cm)) := by
      convert normHS_add_le _ _ using 2 ; simp +decide [ sub_mul, mul_sub ];
    have h_bound1 : normHS ((T - P' m) * R * P cm) ≤ 2 * a + b := by
      have h_term1 : normHS ((T - P' m) * R * P cm) ≤ normHS ((T - P m) * R * P cm) + normHS ((P m - P' m) * R * P cm) := by
        convert normHS_add_le _ _ using 2 ; simp +decide [ sub_mul ];
      -- Now consider the term $\| (T - P m) * R * P cm \|_2$.
      have h_term1_inner : normHS ((T - P m) * R * P cm) ≤ 2 * a := by
        have h_term1_inner : normHS ((T - P m) * R * P cm) ≤ normHS (T * (R * P cm - P m * R)) + normHS (P m * (R * P cm - P m * R)) := by
          convert normHS_sub_le ( T * ( R * P cm - P m * R ) ) ( P m * ( R * P cm - P m * R ) ) using 1 ; simp +decide [ mul_sub, sub_mul, mul_assoc ];
          simp +decide [ ← mul_assoc ];
          rw [ show T * P m = P m from towerSupport_mul_proj ⟨ hPproj, hPorth ⟩ hm ] ; simp +decide [ mul_assoc, hPproj m hm |>.2.eq ] ;
        have h_term1_inner : normHS (T * (R * P cm - P m * R)) ≤ normHS (R * P cm - P m * R) := by
          apply normHS_proj_mul_le;
          exact ⟨ towerSupport_isHermitian ⟨ hPproj, hPorth ⟩, towerSupport_idem ⟨ hPproj, hPorth ⟩ ⟩;
        have h_term1_inner : normHS (P m * (R * P cm - P m * R)) ≤ normHS (R * P cm - P m * R) := by
          apply normHS_proj_mul_le; exact hPproj m hm;
        have h_term1_inner : normHS (R * P cm - P m * R) = normHS (Rᴴ * (R * P cm - P m * R)) := by
          rw [ ← normHS_unitary_left ( Unitary.star_mem hR ) ];
          rfl;
        have h_term1_inner : normHS (Rᴴ * (R * P cm - P m * R)) = normHS (P cm - Rᴴ * P m * R) := by
          simp +decide [ mul_sub, ← mul_assoc ];
          rw [ show Rᴴ * R = 1 from hR.1 ] ; simp +decide [ mul_assoc ] ;
        linarith [ normHS_sub_comm ( Rᴴ * P m * R ) ( P cm ) ];
      refine' le_trans h_term1 ( add_le_add h_term1_inner _ );
      have h_term1_inner : normHS ((P m - P' m) * R * P cm) ≤ normHS ((P m - P' m) * R) := by
        apply normHS_mul_proj_le;
        grind +locals;
      exact h_term1_inner.trans ( by rw [ normHS_unitary_right hR ] );
    have h_bound2 : normHS (P' m * R * (P cm - P' cm)) ≤ c := by
      have h_bound2 : normHS (P' m * R * (P cm - P' cm)) ≤ normHS (R * (P cm - P' cm)) := by
        have h_bound2 : normHS (P' m * (R * (P cm - P' cm))) ≤ normHS (R * (P cm - P' cm)) := by
          apply normHS_proj_mul_le; exact hP'proj m hm;
        simpa only [ Matrix.mul_assoc ] using h_bound2;
      exact h_bound2.trans ( by rw [ normHS_unitary_left hR ] );
    linarith;
  exact le_trans ( pow_le_pow_left₀ ( by exact normHS_nonneg _ ) h_triangle 2 ) ( by nlinarith only [ sq_nonneg ( 2 * a - b ), sq_nonneg ( 2 * a - c ), sq_nonneg ( b - c ) ] )

/-
Per-floor combined bound: the `m`-th column defect of the rounded tower.
-/
lemma b_bound
    (hR : R ∈ unitary (Matrix ι ι ℂ))
    (hPproj : ∀ i < j, IsProj (P i))
    (hPorth : ∀ i < j, ∀ k < j, i ≠ k → P i * P k = 0)
    (hP'proj : ∀ i < j, IsProj (P' i))
    (hsvd : ∀ i < j, normHS (P' i * R * P' (cyc j i) - V i)
        ≤ normHS ((P' i * R * P' (cyc j i))ᴴ * (P' i * R * P' (cyc j i)) - P' (cyc j i)))
    {m : ℕ} (hm : m < j) :
    normHS (towerSupport j P * R * P (cyc j m) - V m) ^ 2
      ≤ 30 * (normHS (Rᴴ * P m * R - P (cyc j m)) ^ 2
          + normHS (P m - P' m) ^ 2 + normHS (P (cyc j m) - P' (cyc j m)) ^ 2) := by
  -- By Lemma 25, apply the nlinarith trick to conclude the proof.
  have h_nlinarith : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
    exact fun x y hx hy => by linarith [ sq_nonneg ( x - y ) ] ;
  have := g_bound hR hPproj hPorth hP'proj hm;
  have := f_bound (P := P) hR hP'proj hm;
  have := normHS_add_le ( towerSupport j P * R * P ( cyc j m ) - P' m * R * P' ( cyc j m ) ) ( P' m * R * P' ( cyc j m ) - V m );
  rw [ show towerSupport j P * R * P ( cyc j m ) - V m = ( towerSupport j P * R * P ( cyc j m ) - P' m * R * P' ( cyc j m ) ) + ( P' m * R * P' ( cyc j m ) - V m ) by abel1 ];
  exact le_trans ( pow_le_pow_left₀ ( normHS_nonneg _ ) this 2 ) ( by nlinarith [ h_nlinarith ( normHS ( towerSupport j P * R * P ( cyc j m ) - P' m * R * P' ( cyc j m ) ) ) ( normHS ( P' m * R * P' ( cyc j m ) - V m ) ) ( normHS_nonneg _ ) ( normHS_nonneg _ ), hsvd m hm, normHS_nonneg ( P' m * R * P' ( cyc j m ) - V m ) ] )

/-
The main difference of the `ε₂` bound is a sum of per-column defects.
-/
lemma roundedR_main_diff_eq
    (hP'proj : ∀ i < j, IsProj (P' i))
    (hP'orth : ∀ i < j, ∀ k < j, i ≠ k → P' i * P' k = 0)
    (hsrc : ∀ i < j, (V i)ᴴ * (V i) = P' (cyc j i))
    (hrng : ∀ i < j, (V i) * (V i)ᴴ = P' i) :
    towerSupport j P * R * towerSupport j P
        - towerSupport j P' * roundedR j P' V * towerSupport j P'
      = ∑ m ∈ Finset.range j, (towerSupport j P * R * P (cyc j m) - V m) := by
  rw [ roundedR_compress ];
  · rw [ Finset.sum_sub_distrib, eq_comm ];
    simp +decide [ towerSupport, Finset.mul_sum _ _ _ ];
    convert sum_cyc_reindex j ( fun k => ( ∑ i ∈ Finset.range j, P i ) * R * P k ) using 1;
  · assumption;
  · exact hP'orth;
  · assumption;
  · assumption

/-
The `ε₂` bound (`eq:lowd-0c`): the rounded tower is `O(j²δ₁ + δ₂)`-close.
-/
lemma roundedR_close2
    (hR : R ∈ unitary (Matrix ι ι ℂ))
    {δ₁ δ₂ : ℝ} (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hPproj : ∀ i < j, IsProj (P i))
    (hPorth : ∀ i < j, ∀ k < j, i ≠ k → P i * P k = 0)
    (hP'proj : ∀ i < j, IsProj (P' i))
    (hP'orth : ∀ i < j, ∀ k < j, i ≠ k → P' i * P' k = 0)
    (hsrc : ∀ i < j, (V i)ᴴ * (V i) = P' (cyc j i))
    (hrng : ∀ i < j, (V i) * (V i)ᴴ = P' i)
    (hε₁ : ∑ i ∈ Finset.range j, normHS (P i - P' i) ^ 2 ≤ (j : ℝ) * δ₁)
    (hd1 : ∑ i ∈ Finset.range (j - 1), normHS (Rᴴ * P i * R - P (i + 1)) ^ 2 ≤ δ₁)
    (hd2 : normHS (Rᴴ * P (j - 1) * R - P 0) ^ 2 ≤ δ₂)
    (hsvd : ∀ i < j, normHS (P' i * R * P' (cyc j i) - V i)
        ≤ normHS ((P' i * R * P' (cyc j i))ᴴ * (P' i * R * P' (cyc j i)) - P' (cyc j i))) :
    normHS (towerSupport j P * R * towerSupport j P
        - towerSupport j P' * roundedR j P' V * towerSupport j P') ^ 2
      ≤ 300 * ((j : ℝ) ^ 2 * δ₁ + δ₂) := by
  by_cases hj : j = 0;
  · simp_all +decide [ towerSupport ];
  · have h_bound : normHS (∑ m ∈ Finset.range j, (towerSupport j P * R * P (cyc j m) - V m)) ^ 2 ≤ 2 * (j - 1 : ℝ) * 30 * (δ₁ + 2 * j * δ₁) + 2 * 30 * (δ₂ + 2 * j * δ₁) := by
      refine' le_trans ( normHS_sq_sum_split j ( Nat.pos_of_ne_zero hj ) _ ) _;
      refine' add_le_add _ _;
      · have h_bound : ∑ m ∈ Finset.range (j - 1), normHS (towerSupport j P * R * P (cyc j m) - V m) ^ 2 ≤ 30 * (∑ m ∈ Finset.range (j - 1), normHS (Rᴴ * P m * R - P (cyc j m)) ^ 2 + ∑ m ∈ Finset.range j, normHS (P m - P' m) ^ 2 + ∑ m ∈ Finset.range j, normHS (P (cyc j m) - P' (cyc j m)) ^ 2) := by
          refine' le_trans ( Finset.sum_le_sum fun m hm => b_bound hR hPproj hPorth hP'proj hsvd ( Finset.mem_range.mp ( Finset.mem_range.mpr ( Nat.lt_of_lt_of_le ( Finset.mem_range.mp hm ) ( Nat.pred_le _ ) ) ) ) ) _;
          simp +decide only [mul_add, Finset.mul_sum _ _ _];
          simp +decide only [Finset.sum_add_distrib];
          exact add_le_add_three le_rfl ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.pred_le _ ) ) fun _ _ _ => mul_nonneg ( by norm_num ) ( sq_nonneg _ ) ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.pred_le _ ) ) fun _ _ _ => mul_nonneg ( by norm_num ) ( sq_nonneg _ ) );
        have h_bound : ∑ m ∈ Finset.range (j - 1), normHS (Rᴴ * P m * R - P (cyc j m)) ^ 2 ≤ δ₁ := by
          convert hd1 using 1;
          exact Finset.sum_congr rfl fun i hi => by rw [ show cyc j i = i + 1 from if_pos ( by linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr hj ) ] ) ] ;
        have h_bound : ∑ m ∈ Finset.range j, normHS (P (cyc j m) - P' (cyc j m)) ^ 2 ≤ j * δ₁ := by
          convert hε₁ using 1;
          convert sum_cyc_reindex j ( fun k => normHS ( P k - P' k ) ^ 2 ) using 1;
        rw [ Nat.cast_pred ( Nat.pos_of_ne_zero hj ) ];
        nlinarith [ show ( j : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hj ) ];
      · refine' le_trans ( mul_le_mul_of_nonneg_left ( b_bound hR hPproj hPorth hP'proj hsvd ( Nat.sub_lt ( Nat.pos_of_ne_zero hj ) zero_lt_one ) ) zero_le_two ) _;
        rcases j with ( _ | _ | j ) <;> simp_all +decide [ cyc ];
        · linarith;
        · have := hε₁.trans' ( Finset.single_le_sum ( fun i _ => sq_nonneg ( normHS ( P i - P' i ) ) ) ( Finset.mem_range.mpr ( Nat.succ_pos _ ) ) );
          have := hε₁.trans' ( Finset.single_le_sum ( fun i _ => sq_nonneg ( normHS ( P i - P' i ) ) ) ( Finset.mem_range.mpr ( Nat.lt_succ_self _ ) ) ) ; norm_num at * ; nlinarith;
    convert h_bound.trans _ using 1;
    · rw [ roundedR_main_diff_eq hP'proj hP'orth hsrc hrng ];
    · nlinarith only [ show ( j : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hj ), hδ₁, hδ₂, mul_le_mul_of_nonneg_left ( show ( j : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hj ) ) hδ₁ ]

end Eps2

/-! ## Assembling the rounding lemma -/

/-
A projection is positive semidefinite.
-/
omit [DecidableEq ι] in
lemma IsProj.posSemidef {P : Matrix ι ι ℂ} (hP : IsProj P) : P.PosSemidef := by
  convert Matrix.posSemidef_conjTranspose_mul_self P using 1
  generalize_proofs at *;
  convert hP.2.eq.symm using 1;
  rw [ hP.1.eq ]

/-
Sub-projections of a pairwise-orthogonal family are pairwise orthogonal.
-/
lemma subproj_orth {j : ℕ} {P P' : ℕ → Matrix ι ι ℂ}
    (hPO : PairwiseOrthProj j P)
    (hP'proj : ∀ i < j, IsProj (P' i))
    (hle : ∀ i < j, ProjLE (P' i) (P i)) :
    ∀ i < j, ∀ k < j, i ≠ k → P' i * P' k = 0 := by
  intro i hi k hk hik;
  obtain ⟨hP_i, hP_k⟩ : IsProj (P i) ∧ IsProj (P k) := by
    exact ⟨ hPO.1 i hi, hPO.1 k hk ⟩;
  have hP'_i : P' i * P i = P' i := by
    apply (LamplighterStability.proj_mul_eq_of_psd_le hP_i (hP'proj i hi).posSemidef (hle i hi)).right
  have hP'_k : P k * P' k = P' k := by
    apply (proj_mul_eq_of_psd_le hP_k (hP'proj k hk).posSemidef (hle k hk)).left;
  convert congr_arg ( fun x => P' i * x * P' k ) ( hPO.2 i hi k hk hik ) using 1 <;> simp +decide [ mul_assoc, hP'_k ];
  simp +decide [ ← mul_assoc, hP'_i ]

/-
Trace-gap bound for an approximate tower: the total variation of the traces
is bounded by `δ₁`.
-/
lemma trace_gap_bound {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ} {δ₁ δ₂ : ℝ}
    (h : IsApproxClosedProjTower j P R δ₁ δ₂) :
    ∑ i ∈ Finset.range (j - 1), |ntrace (P (i + 1)) - ntrace (P i)| ≤ δ₁ := by
  refine' le_trans ( Finset.sum_le_sum fun i hi => _ ) h.2.2.1;
  have h_trace_eq : ntrace (P i) = ntrace (Rᴴ * P i * R) := by
    have h_trace_eq : ntrace (P i) = ntrace (R * Rᴴ * P i) := by
      have h_trace_eq : R * Rᴴ = 1 := by
        have := h.2.1;
        exact this.2;
      rw [ h_trace_eq, one_mul ];
    convert h_trace_eq using 1;
    unfold ntrace; simp +decide [ Matrix.mul_assoc, Matrix.trace_mul_comm R ] ;
  have := proj_diff_bound ( Rᴴ * P i * R ) ( P ( i + 1 ) ) ?_ ?_ ?_ ?_ <;> simp_all +decide;
  · rwa [ abs_sub_comm ];
  · have := h.1.1 i ( by omega ) ; simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ] ;
    exact congr_arg _ ( congr_arg₂ _ ( this.1 ) rfl );
  · have := h.1.1 i ( by linarith [ Nat.sub_add_cancel ( show 1 ≤ j from Nat.pos_of_ne_zero ( by aesop_cat ) ) ] ) ; simp_all +decide [ IsIdempotentElem ] ;
    have := this.2; simp_all +decide [ IsIdempotentElem, Matrix.mul_assoc ] ;
    have := h.2.1; simp_all +decide [ ← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff ] ;
    simp_all +decide [ Matrix.mul_assoc ];
    simp_all +decide [ ← Matrix.mul_assoc, show Rᴴ = star R from rfl ];
  · exact h.1.1 ( i + 1 ) ( by linarith [ Nat.sub_add_cancel ( show 1 ≤ j from Nat.pos_of_ne_zero ( by aesop_cat ) ) ] ) |>.1;
  · exact h.1.1 ( i + 1 ) ( by linarith [ Nat.sub_add_cancel ( show 1 ≤ j from Nat.pos_of_ne_zero ( by aesop_cat ) ) ] ) |>.2

/-
For each floor, the polar decomposition (`claim:svd`) yields a partial isometry.
-/
set_option maxHeartbeats 1000000 in
lemma exists_rounding_isometry_one {j : ℕ} {P' : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hR : R ∈ unitary (Matrix ι ι ℂ))
    (hP'proj : ∀ i < j, IsProj (P' i))
    (hrank : ∀ i < j, ∀ k < j, (P' i).rank = (P' k).rank)
    {i : ℕ} (hi : i < j) :
    ∃ W : Matrix ι ι ℂ,
      Wᴴ * W = P' (cyc j i) ∧ W * Wᴴ = P' i ∧
      normHS (P' i * R * P' (cyc j i) - W)
        ≤ normHS ((P' i * R * P' (cyc j i))ᴴ * (P' i * R * P' (cyc j i)) - P' (cyc j i)) := by
  apply LamplighterStability.claim_svd;
  · exact hP'proj i hi;
  · grind +suggestions;
  · exact hrank i hi _ ( by unfold cyc; split_ifs <;> linarith );
  · have hM : IsProj (R * P' (cyc j i) * Rᴴ) := by
      constructor;
      · have := hP'proj ( cyc j i ) ( by
          exact cyc_lt ( pos_of_gt hi ) );
        obtain ⟨ h₁, h₂ ⟩ := this;
        simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
      · have := hP'proj ( cyc j i ) ( by
          exact cyc_lt ( pos_of_gt hi ) );
        have := this.2;
        simp_all +decide [ IsIdempotentElem, mul_assoc ];
        have := hR.2;
        simp_all +decide [ ← mul_assoc, star_eq_conjTranspose ];
        simp_all +decide [ mul_assoc, mul_eq_one_comm.mp this ];
    convert LamplighterStability.psd_proj_sub_conj ( hP'proj i hi ) hM using 1 ; simp +decide [ Matrix.mul_assoc ];
    simp_all +decide [ ← Matrix.mul_assoc, IsProj ];
    simp_all +decide [ IsIdempotentElem, Matrix.IsHermitian, Matrix.mul_assoc ];
    grind +suggestions;
  · have hM_proj : IsProj (Rᴴ * P' i * R) := by
      have := hP'proj i hi;
      obtain ⟨ h₁, h₂ ⟩ := this;
      constructor;
      · simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
      · simp_all +decide [ IsIdempotentElem, Matrix.mul_assoc ];
        simp_all +decide [ ← Matrix.mul_assoc, Unitary.mem_iff ];
        simp_all +decide [ Matrix.mul_assoc, star ];
    convert psd_proj_sub_conj ( hP'proj ( cyc j i ) ( cyc_lt ( by linarith ) ) ) hM_proj using 1;
    simp +decide [ ← Matrix.mul_assoc, ( hP'proj i hi ).1.eq, ( hP'proj ( cyc j i ) ( cyc_lt ( by linarith ) ) ).1.eq ];
    simp +decide [ mul_assoc, ( hP'proj i hi ).2.eq ]

/-
Choosing the whole rounded partial-isometry family at once.
-/
lemma exists_rounding_isometries {j : ℕ} {P' : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hR : R ∈ unitary (Matrix ι ι ℂ))
    (hP'proj : ∀ i < j, IsProj (P' i))
    (hrank : ∀ i < j, ∀ k < j, (P' i).rank = (P' k).rank) :
    ∃ V : ℕ → Matrix ι ι ℂ,
      (∀ i < j, (V i)ᴴ * (V i) = P' (cyc j i)) ∧
      (∀ i < j, (V i) * (V i)ᴴ = P' i) ∧
      (∀ i < j, normHS (P' i * R * P' (cyc j i) - V i)
        ≤ normHS ((P' i * R * P' (cyc j i))ᴴ * (P' i * R * P' (cyc j i)) - P' (cyc j i))) := by
  have := @exists_rounding_isometry_one;
  choose! V hV₁ hV₂ hV₃ using @this ι _ _ j P' R hR hP'proj hrank;
  exact ⟨ fun _ => V, fun i hi => hV₁ hi, fun i hi => hV₂ hi, fun i hi => hV₃ hi ⟩

/-
**Lemma `lem:lowd` (Rounding approximate closed projection towers).**
Every approximate `(δ₁,δ₂)`-closed projection tower `(P₀,…,P_{j-1}; R)` admits a
*true* closed projection tower `(P'₀,…,P'_{j-1}; R')` that is `(ε₁,ε₂)`-close to it,
with `P'ᵢ ≤ Pᵢ`, `R'` acting as the identity on the complement of `P' = ∑ P'ᵢ`, and
`ε₁ = C·(j·δ₁)`, `ε₂ = C·(j²·δ₁ + δ₂)` for the universal constant `C = 300`.
-/
lemma lem_lowd :
    ∃ C : ℝ, 0 < C ∧
      ∀ {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ} {δ₁ δ₂ : ℝ},
        0 ≤ δ₁ → 0 ≤ δ₂ →
        IsApproxClosedProjTower j P R δ₁ δ₂ →
        ∃ (P' : ℕ → Matrix ι ι ℂ) (R' : Matrix ι ι ℂ),
          IsClosedProjTower j P' R' ∧
          (∀ i < j, ProjLE (P' i) (P i)) ∧
          (R' * (1 - towerSupport j P') = 1 - towerSupport j P') ∧
          TowerClose j P P' R R'
            (C * ((j : ℝ) * δ₁)) (C * ((j : ℝ) ^ 2 * δ₁ + δ₂)) := by
  refine' ⟨ 300, by norm_num, fun { j } { P } { R } { δ₁ δ₂ } hδ₁ hδ₂ h => _ ⟩;
  obtain ⟨P', hP'proj, hP'le, hP'rank, hP'sumle, hP'gap⟩ := claim_p_bound j P h.1
  obtain ⟨V, hsrc, hrng, hsvd⟩ := exists_rounding_isometries h.2.1 hP'proj hP'rank
  set R' := roundedR j P' V
  use P', R';
  refine' ⟨ _, hP'le, _, _ ⟩;
  · refine' ⟨ ⟨ ⟨ hP'proj, _ ⟩, roundedR_unitary hP'proj _ hsrc hrng, _ ⟩, _ ⟩;
    · exact subproj_orth h.1 hP'proj hP'le;
    · exact subproj_orth h.1 hP'proj hP'le;
    · intro i hi
      have := roundedR_conj_proj hP'proj (subproj_orth h.1 hP'proj hP'le) hsrc hrng (show i < j by linarith)
      simp_all +decide [ cyc ];
      exact this;
    · intro hj
      have := roundedR_conj_proj hP'proj (subproj_orth h.1 hP'proj hP'le) hsrc hrng (Nat.sub_lt hj zero_lt_one)
      simp_all +decide [ cyc ];
      grind +splitImp;
  · exact roundedR_comp hP'proj ( subproj_orth h.1 hP'proj hP'le ) hsrc;
  · refine' ⟨ _, _ ⟩;
    · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( trace_gap_bound h ) ( Nat.cast_nonneg j ) ) ( by norm_num ) );
      exact le_trans ( Finset.sum_le_sum fun _ _ => by rw [ normHS_sub_comm ] ) ( hP'sumle.trans ( le_mul_of_one_le_left ( mul_nonneg ( Nat.cast_nonneg _ ) ( Finset.sum_nonneg fun _ _ => abs_nonneg _ ) ) ( by norm_num ) ) );
    · refine' le_trans ( roundedR_close2 h.2.1 hδ₁ hδ₂ h.1.1 h.1.2 hP'proj ( subproj_orth h.1 hP'proj hP'le ) hsrc hrng _ _ _ hsvd ) _;
      · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( trace_gap_bound h ) ( Nat.cast_nonneg _ ) );
        simpa only [ normHS_sub_comm ] using hP'sumle;
      · exact h.2.2.1;
      · exact h.2.2.2;
      · norm_num

end LamplighterStability