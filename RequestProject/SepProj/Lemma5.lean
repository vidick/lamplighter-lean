import RequestProject.SepProj.Defs

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace SepProj

variable {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

/-
`A = Vᴴ F V` is positive semidefinite when `F` is a projection.
-/
omit [DecidableEq H] [DecidableEq K] in
lemma VFV_posSemidef (V : Matrix K H ℂ) {F : Matrix K K ℂ} (hF : IsProj F) :
    (Vᴴ * F * V).PosSemidef := by
  convert Matrix.posSemidef_conjTranspose_mul_self ( F * V ) using 1;
  simp +decide [ Matrix.mul_assoc, hF.1.eq ];
  simp +decide [ ← Matrix.mul_assoc, hF.2 ]

/-
`A = Vᴴ F V ≤ 1` (i.e. `1 - A` is PSD) when `V` is an isometry and `F` a projection.
-/
lemma VFV_le_one (V : Matrix K H ℂ) (hV : Vᴴ * V = 1) {F : Matrix K K ℂ} (hF : IsProj F) :
    (1 - Vᴴ * F * V).PosSemidef := by
  -- Show $1 - Vᴴ * F * V = Vᴴ * (1 - F) * V$.
  have h_identity : (1 - Vᴴ * F * V) = Vᴴ * (1 - F) * V := by
    simp +decide [ Matrix.mul_sub, Matrix.sub_mul, hV ];
  convert VFV_posSemidef V _ using 1;
  constructor <;> simp_all +decide [ IsProj, Matrix.mul_sub, sub_mul ]

/-
For a Hermitian `S` with `0 ≤ S ≤ 1`, `Tr(S²) ≤ Tr S` (equivalently `Tr(S − S²) ≥ 0`).
-/
lemma trace_sq_le_trace {S : Matrix H H ℂ} (hSpos : S.PosSemidef) (hSle : (1 - S).PosSemidef) :
    (S * S).trace.re ≤ S.trace.re := by
  -- By the properties of the trace and positive semidefinite matrices, we have that $S - S^2$ is positive semidefinite.
  have h_diff_posSemidef : (S - S * S).PosSemidef := by
    obtain ⟨T, hT⟩ : ∃ T : Matrix H H ℂ, T.IsHermitian ∧ T * T = S :=
      ⟨CFC.sqrt S, (CFC.sqrt_nonneg S).posSemidef.isHermitian,
        CFC.sqrt_mul_sqrt_self S (ha := hSpos.nonneg)⟩
    convert hSle.conjTranspose_mul_mul_same T using 1 ; simp_all +decide [ mul_assoc, Matrix.IsHermitian ];
    simp +decide [ ← hT.2, mul_sub, sub_mul, mul_assoc ];
  have := Matrix.PosSemidef.trace_nonneg h_diff_posSemidef;
  norm_num [ Complex.le_def ] at this ⊢ ; linarith

/-
If `S` is positive semidefinite and `S² ≤ 1` then `S ≤ 1`.
-/
lemma psd_le_one_of_sq_le_one {S : Matrix H H ℂ} (hSpos : S.PosSemidef)
    (hsq : (1 - S * S).PosSemidef) : (1 - S).PosSemidef := by
  revert hSpos hsq;
  intro hSpos hsq
  obtain ⟨U, D, hU, hD⟩ : ∃ U : Matrix H H ℂ, ∃ D : H → ℝ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ S = U * Matrix.diagonal (fun i => (D i : ℂ)) * Uᴴ ∧ ∀ i, 0 ≤ D i := by
    have := Matrix.IsHermitian.spectral_theorem hSpos.1;
    refine' ⟨ _, fun i => hSpos.1.eigenvalues i, _, _, this.trans _, _ ⟩;
    exact ↑ ( hSpos.1.eigenvectorUnitary );
    · simp +decide [ Matrix.IsHermitian.eigenvectorUnitary ];
    · simp +decide [ Matrix.IsHermitian.eigenvectorUnitary ];
    · ext i j ; simp +decide [ Matrix.mul_apply, Matrix.diagonal ];
    · exact fun i => hSpos.eigenvalues_nonneg i;
  -- Since $1 - S^2$ is positive semidefinite, we have $1 - D^2 \geq 0$, which implies $D^2 \leq 1$.
  have hD_sq_le_one : ∀ i, D i ^ 2 ≤ 1 := by
    have hD_sq_le_one : (Uᴴ * (1 - S * S) * U).PosSemidef := by
      convert hsq.conjTranspose_mul_mul_same U using 1;
    simp_all +decide [ mul_sub, sub_mul, ← mul_assoc ];
    simp_all +decide [ Matrix.mul_assoc, Matrix.PosSemidef ];
    intro i; specialize hD_sq_le_one; have := hD_sq_le_one.2 ( Finsupp.single i 1 ) ; simp_all +decide [ Finsupp.sum_single_index ] ;
    norm_cast at this; nlinarith [ abs_mul_abs_self ( D i ) ] ;
  -- Since $D^2 \leq 1$, we have $1 - D \geq 0$, which implies $1 - S \geq 0$.
  have h1_minus_S_ge_zero : (1 - Matrix.diagonal (fun i => (D i : ℂ))).PosSemidef := by
    constructor;
    · simp +decide [ Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_one ];
    · simp +decide [ Finsupp.sum, Matrix.one_apply, Matrix.diagonal_apply ];
      intro x; refine' Finset.sum_nonneg fun i hi => _; simp +decide [ mul_sub, sub_mul, mul_comm, mul_left_comm ] ;
      split_ifs <;> simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
      exact_mod_cast le_of_abs_le ( hD_sq_le_one i );
  have h1_minus_S_ge_zero : (U * (1 - Matrix.diagonal (fun i => (D i : ℂ))) * Uᴴ).PosSemidef := by
    convert h1_minus_S_ge_zero.conjTranspose_mul_mul_same Uᴴ using 1;
    simp +decide [ Matrix.conjTranspose_conjTranspose ];
  simp_all +decide [ mul_sub, sub_mul ]

/-
A projection `F` of rank `card H` admits an isometry onto its range: there is `W₀ : H → K`
with `W₀ᴴ W₀ = 1` and `W₀ W₀ᴴ = F`.
-/
lemma exists_isometry_onto_proj (F : Matrix K K ℂ) (hF : IsProj F)
    (hFrank : F.trace.re = (Fintype.card H : ℝ)) :
    ∃ W₀ : Matrix K H ℂ, W₀ᴴ * W₀ = 1 ∧ W₀ * W₀ᴴ = F := by
  obtain ⟨U, lam, hU, hlam⟩ : ∃ (U : Matrix K K ℂ) (lam : K → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ F = U * Matrix.diagonal (fun i => (lam i : ℂ)) * Uᴴ ∧ ∀ i, lam i = 0 ∨ lam i = 1 := by
    have := hermitian_decomp hF.1;
    obtain ⟨ U, lam, hU, hlam, rfl ⟩ := this; use U, lam; simp_all +decide [ mul_assoc, IsProj ] ;
    intro i; have := congr_arg ( fun m => Uᴴ * m * U ) hF.2; norm_num [ hU, hlam, Matrix.mul_assoc ] at this;
    replace this := congr_arg ( fun m => m i i ) this ; simp_all +decide [ ← Matrix.mul_assoc ] ;
    norm_cast at this; exact or_iff_not_imp_left.mpr fun h => mul_left_cancel₀ h <| by linarith;
  -- The set `T := {k // lam k = 1}` has cardinality `card H`.
  obtain ⟨T, hT⟩ : ∃ T : Finset K, T.card = Fintype.card H ∧ ∀ i, i ∈ T ↔ lam i = 1 := by
    have hT_card : ∑ i, lam i = Fintype.card H := by
      simp_all +decide [ mul_assoc, Matrix.trace_mul_comm U ];
    rw [ Finset.sum_congr rfl fun i _ => show lam i = if lam i = 1 then 1 else 0 by cases hlam.2.2 i <;> aesop ] at hT_card ; aesop;
  -- Define `W₀ : Matrix K H ℂ` by `W₀ k h := U k (e h)`.
  obtain ⟨e, he⟩ : ∃ e : H ≃ T, True := by
    exact ⟨ Fintype.equivOfCardEq ( by simp +decide [ hT.1 ] ), trivial ⟩
  use Matrix.of (fun k h => U k (e h));
  constructor <;> ext i j <;> simp_all +decide [ Matrix.mul_apply, Matrix.diagonal ];
  · replace hU := congr_fun ( congr_fun hU ( e i ) ) ( e j ) ; simp_all +decide [ Matrix.mul_apply, Matrix.one_apply ] ;
  · rw [ ← Finset.sum_subset ( show Finset.image ( fun x : H => ( e x : K ) ) Finset.univ ⊆ Finset.univ from Finset.subset_univ _ ) ];
    · rw [ Finset.sum_image ];
      · exact Finset.sum_congr rfl fun x _ => by rw [ show lam ( e x ) = 1 from hT.2 _ |>.1 ( e x |>.2 ) ] ; simp +decide ;
      · exact fun x _ y _ hxy => e.injective <| Subtype.ext hxy;
    · intro x hx hx'; specialize hT; have := hT.2 x; simp_all +decide [ Finset.mem_image ] ;
      exact Or.inl <| Or.inr <| Or.resolve_right ( hlam.2.2 x ) fun hx'' => hx' ( e.symm ⟨ x, by aesop ⟩ ) <| by aesop;

/-
A positive semidefinite matrix is unitarily diagonalizable with nonnegative real eigenvalues.
-/
lemma posSemidef_diagonalize (A : Matrix H H ℂ) (hA : A.PosSemidef) :
    ∃ (U : Matrix H H ℂ) (μ : H → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ (∀ i, 0 ≤ μ i) ∧
      A = U * Matrix.diagonal (fun i => (μ i : ℂ)) * Uᴴ := by
  obtain ⟨U, μ, hU, hμ⟩ : ∃ (U : Matrix H H ℂ) (μ : H → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ (∀ i, 0 ≤ μ i) ∧ A = U * Matrix.diagonal (fun i => (μ i : ℂ)) * Uᴴ := by
    have h_hermitian : A.IsHermitian := hA.1
    have h_eigenvalues_nonneg : ∀ i, 0 ≤ hA.1.eigenvalues i := by
      convert hA.eigenvalues_nonneg using 1
    have := Matrix.IsHermitian.spectral_theorem h_hermitian;
    refine' ⟨ h_hermitian.eigenvectorUnitary, fun i => h_hermitian.eigenvalues i, _, _, h_eigenvalues_nonneg, _ ⟩;
    · simp +decide [ Matrix.IsHermitian.eigenvectorUnitary ];
    · simp +decide [ Matrix.IsHermitian.eigenvectorUnitary ];
    · convert this using 1;
  use U, μ

/-
**Unitary completion of an isometry**.  A matrix `J` whose columns (indexed by a subtype
`{i // p i}` of `H`) are orthonormal (`Jᴴ * J = 1`) extends to a unitary `Y` on `H` whose `i`-th
column (for `p i`) coincides with the corresponding column of `J`.
-/
set_option maxHeartbeats 1000000 in
lemma exists_unitary_extend_cols {p : H → Prop} [DecidablePred p]
    (J : Matrix H {i : H // p i} ℂ) (hJ : Jᴴ * J = 1) :
    ∃ Y : Matrix H H ℂ, Yᴴ * Y = 1 ∧ Y * Yᴴ = 1 ∧
      ∀ (i : H) (hi : p i) (h : H), Y h i = J h ⟨i, hi⟩ := by
  -- Let `Pr := J * Jᴴ : Matrix H H ℂ`. Then `Pr` is a projection: `Prᴴ = J * Jᴴ = Pr`, and `Pr * Pr = J * (Jᴴ * J) * Jᴴ = J * Jᴴ = Pr` (using `hJ`).
  set Pr : Matrix H H ℂ := J * Jᴴ
  have hPr : Pr.IsHermitian ∧ Pr * Pr = Pr := by
    simp +zetaDelta at *;
    simp +decide [ ← Matrix.mul_assoc, Matrix.IsHermitian ];
    simp +decide [ Matrix.mul_assoc, hJ ];
  obtain ⟨W, hW⟩ : ∃ W : Matrix H {i : H // ¬p i} ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = 1 - Pr := by
    apply exists_isometry_onto_proj;
    · constructor;
      · simp_all +decide [ Matrix.IsHermitian];
      · simp_all +decide [ sub_mul, mul_sub ];
    · have hPr_trace : Pr.trace.re = Fintype.card {i // p i} := by
        rw [ ← Matrix.trace_mul_comm ] ; aesop;
      simp_all +decide [ Matrix.trace_sub ];
      rw [ Nat.cast_sub ( Fintype.card_subtype_le _ ) ];
  -- Show `Jᴴ * W = 0`: from `W * Wᴴ = 1 - Pr = 1 - J*Jᴴ` we get `(J*Jᴴ) * (W*Wᴴ) = J*Jᴴ - J*Jᴴ*J*Jᴴ = J*Jᴴ - J*Jᴴ = 0`; multiplying on the right by `W` and using `Wᴴ*W = 1` gives `J*Jᴴ*W = 0`; multiplying on the left by `Jᴴ` and using `Jᴴ*J = 1` gives `Jᴴ*W = 0`.
  have hJW : Jᴴ * W = 0 := by
    have hJW : J * Jᴴ * W = 0 := by
      have hJW : (J * Jᴴ) * (W * Wᴴ) = 0 := by
        simp_all +decide [ Matrix.mul_assoc ];
        simp +zetaDelta at *;
        simp +decide [ ← Matrix.mul_assoc];
        simp +decide [ mul_sub, hPr.2 ];
      simpa [ Matrix.mul_assoc, hW.1 ] using congr_arg ( fun x => x * W ) hJW;
    apply_fun ( fun x => Jᴴ * x ) at hJW; simp_all +decide [ Matrix.mul_assoc ] ;
    simp_all +decide [ ← Matrix.mul_assoc ];
  refine' ⟨ Matrix.of ( fun h i => if hi : p i then J h ⟨ i, hi ⟩ else W h ⟨ i, hi ⟩ ), _, _, _ ⟩;
  · ext i j;
    by_cases hi : p i <;> by_cases hj : p j <;> simp_all +decide [ Matrix.mul_apply ];
    · convert congr_fun ( congr_fun hJ ⟨ i, hi ⟩ ) ⟨ j, hj ⟩ using 1;
      simp +decide [ Matrix.one_apply ];
    · replace hJW := congr_fun ( congr_fun hJW ⟨ i, hi ⟩ ) ⟨ j, hj ⟩ ; simp_all +decide [ Matrix.mul_apply ] ;
      rw [ Matrix.one_apply ] ; aesop;
    · replace hJW := congr_fun ( congr_fun hJW ⟨ j, hj ⟩ ) ⟨ i, hi ⟩ ; simp_all +decide [ Matrix.mul_apply ] ;
      convert congr_arg Star.star hJW using 1 <;> simp +decide [ mul_comm, Matrix.one_apply ];
      lia;
    · convert congr_fun ( congr_fun hW.1 ⟨ i, hi ⟩ ) ⟨ j, hj ⟩ using 1;
      simp +decide [ Matrix.one_apply ];
  · ext h h';
    simp +decide [ Matrix.mul_apply, Matrix.one_apply ];
    convert congr_fun ( congr_fun ( show J * Jᴴ + W * Wᴴ = 1 from ?_ ) h ) h' using 1;
    · rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun x : { i // p i } => x.val ) Finset.univ ∪ Finset.image ( fun x : { i // ¬p i } => x.val ) Finset.univ ) ) ];
      · rw [ Finset.sum_union ];
        · rw [ Finset.sum_image, Finset.sum_image ] <;> simp +decide [ Matrix.mul_apply, Matrix.conjTranspose_apply ];
          grind;
        · simp +decide [ Finset.disjoint_left ];
      · aesop;
    · rw [ hW.2, add_sub_cancel ];
  · aesop

/-
**Square polar decomposition** (the singular-value / polar decomposition of a square complex
matrix).  Every square `C` factors as `C = Q * S` with `Q` unitary and `S` a positive semidefinite
square root of `Cᴴ C`.

Assembled from `posSemidef_diagonalize` and the unitary completion `exists_unitary_extend_cols`.
-/
lemma exists_unitary_polar (C : Matrix H H ℂ) :
    ∃ (Q S : Matrix H H ℂ), Qᴴ * Q = 1 ∧ Q * Qᴴ = 1 ∧
      S.IsHermitian ∧ S.PosSemidef ∧ S * S = Cᴴ * C ∧ C = Q * S := by
  -- By singular-value decomposition, there exists a positive semidefinite matrix `S` such that `S * S = Cᴴ * C`.
  obtain ⟨S, hS⟩ : ∃ S : Matrix H H ℂ, S.IsHermitian ∧ S.PosSemidef ∧ S * S = Cᴴ * C := by
    obtain ⟨U, μ, hU, hμ⟩ : ∃ (U : Matrix H H ℂ) (μ : H → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ (∀ i, 0 ≤ μ i) ∧ Cᴴ * C = U * Matrix.diagonal (fun i => (μ i : ℂ)) * Uᴴ := by
      convert posSemidef_diagonalize ( Cᴴ * C ) ( Matrix.posSemidef_conjTranspose_mul_self C ) using 1;
    refine' ⟨ U * Matrix.diagonal ( fun i => ( Real.sqrt ( μ i ) : ℂ ) ) * Uᴴ, _, _, _ ⟩;
    · simp +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
      congr ; ext i ; simp +decide ;
    · convert Matrix.PosSemidef.mul_mul_conjTranspose_same _ _ using 1;
      · infer_instance;
      · exact Matrix.PosSemidef.diagonal fun i => by simp +decide [ Real.sqrt_nonneg] ;
    · simp_all +decide [ ← mul_assoc ];
      simp_all +decide [ mul_assoc, mul_eq_one_comm.mp hU ];
      simp +decide [ ← Complex.ofReal_mul, Real.mul_self_sqrt ( hμ.1 _ ) ];
  obtain ⟨U, μ, hU, hμ⟩ : ∃ (U : Matrix H H ℂ) (μ : H → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ (∀ i, 0 ≤ μ i) ∧ S = U * Matrix.diagonal (fun i => (μ i : ℂ)) * Uᴴ := by
    exact posSemidef_diagonalize S hS.2.1;
  -- Let `M := C * U`. Then `Mᴴ * M = Uᴴ * Cᴴ * C * U = Uᴴ * A * U = diagonal (fun i => (μ i : ℂ))` (using `A`'s form and `Uᴴ*U = U*Uᴴ = 1`).
  set M : Matrix H H ℂ := C * U
  have hM : Mᴴ * M = Matrix.diagonal (fun i => (μ i : ℂ) ^ 2) := by
    simp +zetaDelta at *;
    simp_all +decide [ ← mul_assoc, sq ];
    simp +decide [ ← hS.2.2, mul_assoc, hU];
    rw [ ← Matrix.mul_assoc, hU, Matrix.one_mul ];
  -- Set `p i := μ i ≠ 0`. Define `J : Matrix H {i // μ i ≠ 0} ℂ` by `J h ⟨k, hk⟩ := (1 / μ k : ℂ) * M h k`.
  set p : H → Prop := fun i => μ i ≠ 0
  set J : Matrix H {i : H // p i} ℂ := fun h ⟨k, hk⟩ => (1 / μ k : ℂ) * M h k;
  -- By `exists_unitary_extend_cols J` get a unitary `Y` (`Yᴴ*Y=1`, `Y*Yᴴ=1`) with `Y h i = J h ⟨i, hi⟩` whenever `μ i ≠ 0`.
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix H H ℂ, Yᴴ * Y = 1 ∧ Y * Yᴴ = 1 ∧ ∀ (i : H) (hi : p i) (h : H), Y h i = J h ⟨i, hi⟩ := by
    apply exists_unitary_extend_cols;
    ext ⟨ i, hi ⟩ ⟨ j, hj ⟩ ; simp_all +decide [ Matrix.mul_apply ] ;
    replace hM := congr_fun ( congr_fun hM i ) j; simp_all +decide [ Matrix.mul_apply ] ;
    convert congr_arg ( fun x : ℂ => ( 1 / μ i : ℂ ) * ( 1 / μ j : ℂ ) * x ) hM using 1 <;> simp +decide [ J, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, mul_comm ];
    by_cases hij : i = j <;> simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm ];
    simp +decide [ ne_of_gt ( show 0 < μ j from lt_of_le_of_ne ( hμ.2.1 j ) ( Ne.symm hj ) ) ];
    simp +decide [ hij, Matrix.one_apply ];
  refine' ⟨ Y * Uᴴ, S, _, _, _, _, _ ⟩ <;> simp_all +decide [ Matrix.mul_assoc ];
  · simp +decide [ ← Matrix.mul_assoc, hY.1, hμ.1 ];
  · simp_all +decide [ ← Matrix.mul_assoc ];
  · -- By definition of $Y$, we know that $Y * diagonal (fun i => (μ i : ℂ)) = M$.
    have hY_diag : Y * Matrix.diagonal (fun i => (μ i : ℂ)) = M := by
      ext h i; by_cases hi : μ i = 0 <;> simp_all +decide [ Matrix.mul_apply, Matrix.diagonal ] ;
      · replace hM := congr_fun ( congr_fun hM i ) i; simp_all +decide [ Matrix.mul_apply, sq ] ;
        simp_all +decide [ Complex.ext_iff ];
        simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, add_nonneg, mul_self_nonneg ];
        constructor <;> nlinarith only [ hM.1 h ];
      · simp +zetaDelta at *;
        rw [ hY.2.2 i hi h, inv_mul_eq_div, div_mul_cancel₀ _ ( Complex.ofReal_ne_zero.mpr hi ) ];
    simp_all +decide [ ← Matrix.mul_assoc ];
    rw [ Matrix.mul_assoc, hμ.1, Matrix.mul_one ]

/-- **Polar decomposition data for Lemma 5**.
For an isometry `V : H → K` and a projection `F` on `K` of the same rank as `V V ᴴ`, there is an
isometry `W : H → K` onto `Ran F` (`Wᴴ W = 1`, `W Wᴴ = F`) with `Wᴴ V` equal to the positive
square root `S` of `A = Vᴴ F V` (so `S² = A`, `0 ≤ S ≤ 1`).

Assembled from `exists_isometry_onto_proj`, the square polar decomposition `exists_unitary_polar`,
and `psd_le_one_of_sq_le_one`. -/
lemma polar_exists (V : Matrix K H ℂ) (hV : Vᴴ * V = 1) (F : Matrix K K ℂ) (hF : IsProj F)
    (hFrank : F.trace.re = (Fintype.card H : ℝ)) :
    ∃ W : Matrix K H ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = F ∧ ∃ S : Matrix H H ℂ,
      S.IsHermitian ∧ S.PosSemidef ∧ (1 - S).PosSemidef ∧ S * S = Vᴴ * F * V ∧ Wᴴ * V = S := by
  obtain ⟨W₀, hW₀iso, hW₀F⟩ := exists_isometry_onto_proj (H := H) F hF hFrank
  obtain ⟨Q, S, hQiso, hQco, hSherm, hSpos, hSsq, hCQS⟩ := exists_unitary_polar (W₀ᴴ * V)
  have hCC : (W₀ᴴ * V)ᴴ * (W₀ᴴ * V) = Vᴴ * F * V := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc W₀ W₀ᴴ, hW₀F]
    rw [← Matrix.mul_assoc]
  have hSsq' : S * S = Vᴴ * F * V := by rw [hSsq, hCC]
  refine ⟨W₀ * Q, ?_, ?_, S, hSherm, hSpos, ?_, hSsq', ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc W₀ᴴ, hW₀iso,
      Matrix.one_mul, hQiso]
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQco,
      Matrix.one_mul, hW₀F]
  · exact psd_le_one_of_sq_le_one hSpos (by rw [hSsq']; exact VFV_le_one V hV hF)
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hCQS, ← Matrix.mul_assoc Qᴴ Q,
      hQiso, Matrix.one_mul]

/-
The HS-norm reduction step of Lemma 5: given the polar data `W, S`, the displacement norm is
controlled by the projection-difference norm via `Tr(S²) ≤ Tr S`.
-/
omit [DecidableEq K] in
lemma norm_reduction (d : ℕ) (V W : Matrix K H ℂ) (hV : Vᴴ * V = 1) (F : Matrix K K ℂ)
    (hF : IsProj F) (hFrank : F.trace.re = (Fintype.card H : ℝ))
    (hWiso : Wᴴ * W = 1) (hWF : W * Wᴴ = F)
    (S : Matrix H H ℂ) (hSherm : S.IsHermitian) (hSpos : S.PosSemidef) (hSle : (1 - S).PosSemidef)
    (hSsq : S * S = Vᴴ * F * V) (hWV : Wᴴ * V = S) :
    hsNormSq d (V - W) ≤ hsNormSq d (V * Vᴴ - F) := by
  -- Compute both normalized squared norms via hsNormSq X = (Xᴴ * X).trace.re / d.
  have h_norm_VW : hsNormSq d (V - W) = (2 * (Fintype.card H : ℝ) - 2 * S.trace.re) / d := by
    simp +decide [ hsNormSq, Matrix.mul_sub, Matrix.sub_mul, hV, hWiso, hWV ];
    rw [ show Vᴴ * W = Sᴴ from ?_ ];
    · rw [ hSherm.eq ] ; ring;
    · rw [ ← hWV, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose ]
  have h_norm_VF : hsNormSq d (V * Vᴴ - F) = (2 * (Fintype.card H : ℝ) - 2 * (S * S).trace.re) / d := by
    -- Now compute the trace of the squared difference.
    have h_trace_VF : (Matrix.trace ((V * Vᴴ - F) * (V * Vᴴ - F).conjTranspose)).re = 2 * (Fintype.card H : ℝ) - 2 * (S * S).trace.re := by
      simp +decide [ sub_mul, mul_sub, hSsq ];
      simp_all +decide [ Matrix.mul_assoc, Matrix.trace_mul_comm V, Matrix.trace_mul_comm F, hF.1.eq ];
      rw [ ← hFrank, ← hF.2 ] ; ring;
      simp +decide [ hF.2 ] ; ring;
    unfold hsNormSq; aesop;
  convert div_le_div_of_nonneg_right ( sub_le_sub_left ( mul_le_mul_of_nonneg_left ( trace_sq_le_trace hSpos hSle ) zero_le_two ) _ ) ( Nat.cast_nonneg d ) using 1 ; ring!;
  rotate_right;
  exacts [ 2 * Fintype.card H, by linear_combination h_norm_VW, by linear_combination h_norm_VF ]

/-- **Lemma 5** (matching two subspaces by close isometries).
Let `V : H → K` be an isometry (`Vᴴ V = 1`), `E = V Vᴴ` the projection onto its range, and `F`
a projection on `K` of the same rank as `E` (i.e. `rank F = dim H`).  Then there is an isometry
`W : H → K` with `W Wᴴ = F` and `‖V − W‖₂,d ≤ ‖E − F‖₂,d`. -/
theorem lemma5 (d : ℕ) (V : Matrix K H ℂ) (hV : Vᴴ * V = 1)
    (F : Matrix K K ℂ) (hF : IsProj F) (hFrank : F.trace.re = (Fintype.card H : ℝ)) :
    ∃ W : Matrix K H ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = F ∧
      hsNorm d (V - W) ≤ hsNorm d (V * Vᴴ - F) := by
  obtain ⟨W, hWiso, hWF, S, hSherm, hSpos, hSle, hSsq, hWV⟩ :=
    polar_exists V hV F hF hFrank
  refine ⟨W, hWiso, hWF, ?_⟩
  rw [hsNorm, hsNorm]
  exact Real.sqrt_le_sqrt
    (norm_reduction d V W hV F hF hFrank hWiso hWF S hSherm hSpos hSle hSsq hWV)

end SepProj