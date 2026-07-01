import Mathlib
import RequestProject.Foundations
import RequestProject.AssemblyChao
import RequestProject.MeasureInstantiation

/-!
# Orbit input bridge (Section 5, steps 1–2)

This file packages the *orbit-side input* to the final assembly
(`assembly_final`).  Starting from a family `A : Win (m+1) → Matrix` of Hermitian
involutions with small pairwise commutators and *exact* `T`-equivariance
`star T · A_i · T = A_{i+1}` (which the lamplighter orbit `A_i = T^{-i} A₀ T^i`
satisfies), it:

* rounds `A` to nearby pairwise *commuting* Hermitian involutions `B` via the
  linear Chao bound (`exists_commuting_involutions`), with
  `‖B_i − A_i‖ ≤ 4·(2m+3)·ε`;
* feeds the commuting family into the measure bridge
  (`approxInvMeasure_EpatB`) and bounds the shift defect to conclude that the
  induced probability measure `pvmMeasure (m+1) (EpatB (m+1) B)` is
  `(m, η)`-approximately invariant with `η ≤ 4050·(m+1)^6·ε²`.

This is exactly the `ApproxInvMeasure` input consumed by `prop_decomp`.
-/

namespace LamplighterStability.OrbitInput

open scoped BigOperators
open Matrix
open LamplighterStability LamplighterStability.MeasureInstantiation
  LamplighterStability.Dynamics LamplighterStability.MeasureBridge

variable {d : ℕ}

/-
Round a `Win (m+1)`-indexed family of Hermitian involutions with small
pairwise commutators to nearby commuting Hermitian involutions, via the
`Fin (2m+3)`-indexed `exists_commuting_involutions` and the reindexing
`winEquiv (m+1) : Win (m+1) ≃ Fin (2m+3)`.
-/
lemma exists_commuting_involutions_win (m : ℕ)
    (A : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hAh : ∀ i, (A i).IsHermitian) (hA2 : ∀ i, A i * A i = 1)
    {ε : ℝ} (hcomm : ∀ i j, normHS ⁅A i, A j⁆ ≤ ε) :
    ∃ B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (B i).IsHermitian) ∧ (∀ i, B i * B i = 1) ∧
      (∀ i j, Commute (B i) (B j)) ∧
      (∀ i, normHS (B i - A i) ≤ 4 * ((2 * (m + 1) + 1 : ℕ) : ℝ) * ε) := by
  convert exists_commuting_involutions ( fun k => A ( ( winEquiv ( m + 1 ) ).symm k ) ) ( fun k => hAh _ ) ( fun k => hA2 _ ) ( fun i j => hcomm _ _ ) using 1;
  constructor <;> rintro ⟨ B, hB₁, hB₂, hB₃, hB₄ ⟩;
  · use fun i => B ((winEquiv (m + 1)).symm i);
    exact ⟨ fun i => hB₁ _, fun i => hB₂ _, fun i j => hB₃ _ _, fun i => hB₄ _ ⟩;
  · use fun i => B (winEquiv (m + 1) i);
    exact ⟨ fun i => hB₁ _, fun i => hB₂ _, fun i j => hB₃ _ _, fun i => by simpa using hB₄ ( winEquiv ( m + 1 ) i ) ⟩

/-
For commuting approximations `B` that are uniformly `K`-close to a
`T`-equivariant family `A` (`star T · A_i · T = A_{i+1}`), every consecutive
shift defect is bounded by `2K`.
-/
lemma shift_defect_le {m : ℕ} {T : Matrix (Fin d) (Fin d) ℂ}
    (hT : T ∈ unitary (Matrix (Fin d) (Fin d) ℂ))
    {A B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ} {K : ℝ}
    (hclose : ∀ i, normHS (B i - A i) ≤ K)
    (hequiv : ∀ i j : Win (m + 1), (j : ℤ) = (i : ℤ) + 1 →
        star T * A i * T = A j)
    (k : Fin (2 * m + 1)) :
    normHS (star T * Bmid m B k.castSucc * T - Bmid m B k.succ) ≤ 2 * K := by
  -- Let `i := Bmid`'s `castSucc` index as the `Win (m+1)` element `iw` with value `(k:ℤ) - m`, and `jw` the `succ` index with value `(k:ℤ) - m + 1`.
  set iw : Win (m + 1) := ⟨(k.castSucc : ℤ) - m, by
    grind +qlia⟩
  set jw : Win (m + 1) := ⟨(k.succ : ℤ) - m, by
    grind⟩
  generalize_proofs at *;
  -- By the triangle inequality `normHS_sub_le`/`normHS_add_le`,
  have h_triangle : normHS (star T * B iw * T - B jw) ≤ normHS (star T * (B iw - A iw) * T) + normHS (A jw - B jw) := by
    convert normHS_add_le _ _ using 2 ; simp +decide [ mul_sub, sub_mul ];
    grind;
  convert h_triangle.trans _ using 1;
  rw [ two_mul ];
  refine' add_le_add _ _;
  · convert hclose iw using 1;
    convert normHS_unitary_conj ( Unitary.star_mem hT ) ( B iw - A iw ) using 1;
    simp +decide [ Matrix.star_eq_conjTranspose ];
  · grind +suggestions

/-
**Orbit input bridge.**  From a `T`-equivariant family `A` of Hermitian
involutions with pairwise commutators `≤ ε`, produce nearby commuting
involutions `B` and conclude that the induced PVM probability measure is
`(m, η)`-approximately invariant with `η ≤ 2592·(m+1)^4·ε²`.
-/
theorem commuting_involutions_approxInvMeasure (m : ℕ)
    {T : Matrix (Fin d) (Fin d) ℂ} (hT : T ∈ unitary (Matrix (Fin d) (Fin d) ℂ))
    (A : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hAh : ∀ i, (A i).IsHermitian) (hA2 : ∀ i, A i * A i = 1)
    {ε : ℝ}
    (hcomm : ∀ i j, normHS ⁅A i, A j⁆ ≤ ε)
    (hequiv : ∀ i j : Win (m + 1), (j : ℤ) = (i : ℤ) + 1 →
        star T * A i * T = A j) :
    ∃ B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (B i).IsHermitian) ∧ (∀ i, B i * B i = 1) ∧
      (∀ i j, Commute (B i) (B j)) ∧
      (∀ i, normHS (B i - A i) ≤ 4 * ((2 * (m + 1) + 1 : ℕ) : ℝ) * ε) ∧
      ApproxInvMeasure m (2592 * ((m : ℝ) + 1) ^ 4 * ε ^ 2)
        (pvmMeasure (m + 1) (EpatB (m + 1) B)) := by
  obtain ⟨B, hBh, hB2, hBc, hBclose⟩ := exists_commuting_involutions_win m A hAh hA2 hcomm;
  refine' ⟨ B, hBh, hB2, hBc, hBclose, approxInvMeasure_EpatB m hT B hBh hB2 hBc _ ⟩;
  refine' le_trans ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun i _ => pow_le_pow_left₀ ( normHS_nonneg _ ) ( shift_defect_le hT hBclose hequiv i ) 2 ) ( by positivity ) ) _ ; norm_num ; ring_nf;
  nlinarith [ pow_nonneg ( Nat.cast_nonneg m : ( 0 : ℝ ) ≤ m ) 3, pow_nonneg ( Nat.cast_nonneg m : ( 0 : ℝ ) ≤ m ) 4 ]

end LamplighterStability.OrbitInput