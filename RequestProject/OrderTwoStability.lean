import RequestProject.ProjectionTowers
import RequestProject.PVMToMeasure

/-!
# Order-two stability (DGLT, Proposition 1.4)

This file proves the *order-two stability* result quoted (DGLT, Prop. 1.4) in the
paper: a unitary `A` with `‖A² − 1‖_HS ≤ ε` is `ε`-close (in normalized
Hilbert–Schmidt norm) to a genuine order-two unitary `A'` (`A'² = 1`).

Although the paper merely *cites* this, it admits a fully elementary proof using
only Mathlib's **Hermitian** spectral theorem (Mathlib lacks the unitary/normal
spectral theorem).  The idea is to diagonalize the Hermitian *real part*
`B = (A + Aᴴ)/2` of `A` (rather than `A` itself):

* Spectrally decompose `B = U · diag(β) · Uᴴ` with real eigenvalues `β`.  Since
  `4·1 − (A+Aᴴ)² = (A−Aᴴ)ᴴ(A−Aᴴ) ≥ 0`, each eigenvalue satisfies `β² ≤ 1`.
* Round to `A' = U · diag(sign β) · Uᴴ`, a Hermitian involution (`A'² = 1`).
* Two trace identities (using only `AᴴA = AAᴴ = 1`, `A'ᴴ = A'`, `A'² = 1`) give
  `‖A − A'‖² = 2 − tr(A'(A+Aᴴ)) = (2/d) ∑ (1 − |βₖ|)` and
  `‖A² − 1‖² = 4 − tr((A+Aᴴ)²) = (4/d) ∑ (1 − βₖ²)`.
* The scalar inequality `1 − |β| ≤ 2(1 − β²)` for `|β| ≤ 1` finishes the bound.
-/

namespace LamplighterStability

open Matrix
open scoped BigOperators ComplexOrder

variable {d : ℕ}

/-
Elementary scalar inequality: for `β² ≤ 1`, `1 − |β| ≤ 2(1 − β²)`.
-/
lemma dglt_real_ineq {β : ℝ} (h : β ^ 2 ≤ 1) : 1 - |β| ≤ 2 * (1 - β ^ 2) := by
  cases abs_cases β <;> nlinarith [ sq_nonneg ( |β| - 1 ) ]

/-
Trace identity for the perturbation distance: if `A` is unitary and `A'` is a
Hermitian involution, then `‖A − A'‖² = 2 − tr(A'·(A + Aᴴ))`.
-/
lemma dglt_diff_identity [Nonempty (Fin d)]
    {A A' : Matrix (Fin d) (Fin d) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hA'H : A'.IsHermitian) (hA'2 : A' ^ 2 = 1) :
    normHS (A - A') ^ 2 = 2 - ntrace (A' * (A + Aᴴ)) := by
  -- Expand the expression for the Hilbert-Schmidt norm squared.
  have h_expand : normHS (A - A') ^ 2 = ntrace (Aᴴ * A) + ntrace (A' * A') - ntrace (Aᴴ * A') - ntrace (A' * A) := by
    rw [normHS_sq_eq_ntrace];
    simp +decide [ sub_mul, mul_sub, ntrace_sub ];
    rw [ hA'H.eq ] ; ring;
  simp_all +decide [ mul_add, ntrace_add, ntrace_mul_comm ];
  rw [ show ntrace ( A * Aᴴ ) = 1 from ?_, show ntrace ( A' * A' ) = 1 from ?_ ] ; ring!;
  · simp_all +decide [ sq, ntrace_one ];
  · have hA'_trace : A * Aᴴ = 1 := by
      exact hA.2;
    rw [ hA'_trace, ntrace_one ]

/-
Trace identity for the order-two defect: if `A` is unitary then
`‖A² − 1‖² = 4 − tr((A + Aᴴ)·(A + Aᴴ))`.
-/
lemma dglt_sq_identity [Nonempty (Fin d)]
    {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    normHS (A ^ 2 - 1) ^ 2 = 4 - ntrace ((A + Aᴴ) * (A + Aᴴ)) := by
  convert normHS_sq_eq_ntrace ( A^2 - 1 ) using 1;
  simp +decide [ Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, sq, ntrace ];
  have h_unitary : A * Aᴴ = 1 ∧ Aᴴ * A = 1 := by
    exact ⟨ hA.2, hA.1 ⟩;
  simp_all +decide [ mul_assoc, Matrix.trace ] ; ring;
  simp_all +decide [ ← mul_assoc ] ; ring;
  rw [ mul_inv_cancel₀ ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Fin.pos <| Classical.arbitrary _ ) ] ; ring

/-
Spectral construction of the rounded involution `A'` from the real part of a
unitary `A`, recording the eigenvalue data needed for the bound.
-/
lemma dglt_construct [Nonempty (Fin d)]
    (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ (A' : Matrix (Fin d) (Fin d) ℂ) (β : Fin d → ℝ),
      A' ∈ Matrix.unitaryGroup (Fin d) ℂ ∧ A'.IsHermitian ∧ A' ^ 2 = 1 ∧
      (∀ k, β k ^ 2 ≤ 1) ∧
      ntrace (A' * (A + Aᴴ)) = (2 / (d : ℝ)) * ∑ k, |β k| ∧
      ntrace ((A + Aᴴ) * (A + Aᴴ)) = (4 / (d : ℝ)) * ∑ k, β k ^ 2 := by
  obtain ⟨U, D, hU, hD⟩ : ∃ U : Matrix (Fin d) (Fin d) ℂ, ∃ D : Fin d → ℝ, U ∈ unitaryGroup (Fin d) ℂ ∧ (A + Aᴴ) = U * Matrix.diagonal (fun k => (D k : ℂ)) * Uᴴ := by
    have h_herm : (A + Aᴴ).IsHermitian := by
      simp +decide [ Matrix.IsHermitian, add_comm ];
    have := h_herm.spectral_theorem;
    refine' ⟨ _, _, _, this ⟩;
    simp +decide [];
  refine' ⟨ U * Matrix.diagonal ( fun k => if D k ≥ 0 then 1 else -1 : Fin d → ℂ ) * Uᴴ, fun k => D k / 2, _, _, _, _, _ ⟩;
  · simp_all +decide [ Matrix.mem_unitaryGroup_iff, Matrix.mul_assoc ];
    simp_all +decide [ ← Matrix.mul_assoc, star_eq_conjTranspose ];
    simp_all +decide [ Matrix.mul_assoc, mul_eq_one_comm.mp hU ];
  · simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
    congr ; ext ; aesop;
  · simp_all +decide [ sq, mul_assoc ];
    simp_all +decide [ ← mul_assoc, mem_unitaryGroup_iff ];
    simp_all +decide [ star_eq_conjTranspose ];
    simp_all +decide [ Matrix.mul_assoc, mul_eq_one_comm.mp hU ];
  · -- Since $A$ is unitary, we have $A * Aᴴ = 1$, and thus $(A - Aᴴ)ᴴ * (A - Aᴴ)$ is positive semidefinite.
    have h_pos_semidef : (A - Aᴴ)ᴴ * (A - Aᴴ) = 4 • 1 - (A + Aᴴ) * (A + Aᴴ) := by
      have h_pos_semidef : (A - Aᴴ)ᴴ * (A - Aᴴ) = -(A * A + Aᴴ * Aᴴ - 2 • 1) := by
        simp_all +decide [ sub_mul, mul_sub, Matrix.mul_assoc ];
        rw [ show A * Aᴴ = 1 by simpa using hA.2 ] ; abel_nf;
        rw [ show Aᴴ * A = 1 by simpa using hA.1 ] ; abel_nf;
        norm_num [ two_smul, add_comm, add_left_comm, add_assoc ];
      simp_all +decide [];
      rw [ ← hD ] ; norm_num [ two_mul, add_mul, mul_add, sub_mul, mul_sub ] ; abel_nf;
      rw [ show Aᴴ * A = 1 from by simpa [ mul_eq_one_comm ] using hA.2 ] ; rw [ show A * Aᴴ = 1 from by simpa [ mul_eq_one_comm ] using hA.1 ] ; abel_nf;
      ext i j ; norm_num ; ring;
    have h_pos_semidef : (Uᴴ * ((A - Aᴴ)ᴴ * (A - Aᴴ)) * U).PosSemidef := by
      grind +suggestions;
    have h_pos_semidef : (4 • 1 - Matrix.diagonal (fun k => (D k : ℂ) ^ 2)).PosSemidef := by
      convert h_pos_semidef using 1;
      simp_all +decide [ mul_assoc, Matrix.mul_sub, Matrix.sub_mul ];
      simp_all +decide [ ← mul_assoc ];
      simp_all +decide [ mul_assoc, mul_eq_one_comm.mp ( show U * Uᴴ = 1 from hU.2 ) ];
      simp_all +decide [ ← Matrix.mul_assoc ];
      rw [ show ( 4 : Matrix ( Fin d ) ( Fin d ) ℂ ) = 4 • 1 by norm_num, Matrix.mul_smul, Matrix.smul_mul ] ; norm_num [ hU.2 ];
      simp_all +decide [ sq, Matrix.mem_unitaryGroup_iff ];
      rw [ show Uᴴ * U = 1 from by simpa [ mul_eq_one_comm ] using hU ] ; norm_num;
    have := h_pos_semidef.2;
    intro k; specialize this ( Finsupp.single k 1 ) ; norm_num [ Finsupp.sum_single_index ] at this;
    erw [ show ( 4 : Matrix ( Fin d ) ( Fin d ) ℂ ) = 4 • 1 by norm_num, Matrix.smul_apply ] at this ; norm_num at this ; norm_cast at this ; nlinarith;
  · constructor <;> simp_all +decide [ ntrace, Matrix.mul_assoc ];
    · simp_all +decide [ ← mul_assoc ];
      -- Simplify the expression using the properties of the trace and the diagonal matrix.
      have h_trace : Matrix.trace ((U * Matrix.diagonal (fun k => if 0 ≤ D k then 1 else -1) * Uᴴ * U * Matrix.diagonal (fun k => (D k : ℂ)) * Uᴴ)) = Matrix.trace (Matrix.diagonal (fun k => if 0 ≤ D k then (D k : ℂ) else -(D k : ℂ))) := by
        simp_all +decide [ Matrix.mul_assoc, Matrix.trace_mul_comm U ];
        simp_all +decide [ ← Matrix.mul_assoc, Matrix.mem_unitaryGroup_iff ];
        simp_all +decide [ Matrix.mul_assoc ];
        simp_all +decide [ ← Matrix.mul_assoc, show Uᴴ * U = 1 from mul_eq_one_comm.mp hU ];
      simp_all +decide [ Matrix.trace_diagonal, abs_div ];
      rw [ Finset.mul_sum _ _ _ ] ; rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; split_ifs <;> norm_num [ abs_of_nonneg, abs_of_nonpos, ‹_› ] ; ring;
      rw [ abs_of_neg ( not_le.mp ‹_› ) ] ; ring;
    · simp_all +decide [ Matrix.mul_assoc, Matrix.trace_mul_comm U ];
      simp_all +decide [ ← mul_assoc, Matrix.trace ];
      simp_all +decide [ Matrix.mul_assoc, mul_eq_one_comm.mp ( show U * Uᴴ = 1 from hU.2 ) ];
      ring;
      norm_num [ ← Finset.sum_mul _ _ _ ] ; ring

/-- **DGLT, Proposition 1.4 (order-two stability).**  If a unitary `A` satisfies
`‖A² − 1‖_HS ≤ ε`, then there is a unitary `A'` with `A'² = 1` and
`‖A − A'‖_HS ≤ ε`. -/
theorem order_two_stability {ε : ℝ}
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h : normHS (A ^ 2 - 1) ≤ ε) :
    ∃ A' : Matrix (Fin d) (Fin d) ℂ, A' ∈ Matrix.unitaryGroup (Fin d) ℂ ∧
      A' ^ 2 = 1 ∧ normHS (A - A') ≤ ε := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨1, one_mem _, one_pow 2, ?_⟩
    have h0 : normHS (A - (1 : Matrix (Fin 0) (Fin 0) ℂ)) = 0 := by
      have he : A - (1 : Matrix (Fin 0) (Fin 0) ℂ) = 0 := Subsingleton.elim _ _
      rw [he]; simp [normHS]
    have hε : (0 : ℝ) ≤ ε := by
      refine le_trans ?_ h
      have he : A ^ 2 - (1 : Matrix (Fin 0) (Fin 0) ℂ) = 0 := Subsingleton.elim _ _
      rw [he]; simp [normHS]
    rw [h0]; exact hε
  · haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
    obtain ⟨A', β, hA'u, hA'H, hA'2, hβ, hid, hsq⟩ := dglt_construct A hA
    refine ⟨A', hA'u, hA'2, ?_⟩
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hcard : (∑ _k : Fin d, (1 : ℝ)) = (d : ℝ) := by simp
    have hsum : (∑ k : Fin d, (1 - |β k|)) ≤ 2 * ∑ k : Fin d, (1 - β k ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun k _ => dglt_real_ineq (hβ k))
    have key : normHS (A - A') ^ 2 ≤ normHS (A ^ 2 - 1) ^ 2 := by
      rw [dglt_diff_identity hA hA'H hA'2, dglt_sq_identity hA, hid, hsq]
      have hexp : (∑ k : Fin d, (1 - |β k|)) = (d : ℝ) - ∑ k : Fin d, |β k| := by
        rw [Finset.sum_sub_distrib, hcard]
      have hexp2 : (∑ k : Fin d, (1 - β k ^ 2)) = (d : ℝ) - ∑ k : Fin d, β k ^ 2 := by
        rw [Finset.sum_sub_distrib, hcard]
      rw [hexp, hexp2] at hsum
      have hd' : (d : ℝ) ≠ 0 := ne_of_gt hdpos
      have hkey : 4 * (∑ k, β k ^ 2) - 2 * (∑ k, |β k|) ≤ 2 * (d : ℝ) := by
        linarith [hsum]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, sub_le_sub_iff,
        add_div' _ _ _ hd', add_div' _ _ _ hd', div_le_div_iff_of_pos_right hdpos]
      linarith [hkey]
    have hnn1 := normHS_nonneg (A - A')
    have hnn2 := normHS_nonneg (A ^ 2 - 1)
    have : normHS (A - A') ≤ normHS (A ^ 2 - 1) := by nlinarith [key, hnn1, hnn2]
    linarith [this, h]

end LamplighterStability