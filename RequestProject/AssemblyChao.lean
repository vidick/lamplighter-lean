import Mathlib
import RequestProject.CommutingProjections
import RequestProject.ChaoLinear

set_option maxHeartbeats 2000000

/-!
# Linear-Chao rounding of an almost-commuting family of involutions

This file packages the pre-processing step of the final assembly
(`assembly_final`, Section 5) that replaces the orbit involutions
`A_i = T^{-i} A₀ T^i` by nearby *commuting* involutions, using the **improved
linear** Chao bound `chao_commuting_projections_linear` (`8·n·ε₀` under the
dimension-free threshold `ε₀ ≤ 1/(32 n)`).  This is what recovers the paper's
`ε = cκ⁷/M²` denominator downstream (versus the `M³` supported by the
unconditional quadratic bound).  See `IMPROVED_CHAO_PLAN.md`.
-/

namespace LamplighterStability

open scoped BigOperators
open Matrix

/-
**Linear-Chao rounding of an almost-commuting family of Hermitian
involutions.**

Given `n` Hermitian involutions `A i` (`(A i)ᴴ = A i`, `(A i)^2 = 1`) with
pairwise normalized Hilbert–Schmidt commutators `‖⁅A i, A j⁆‖_HS ≤ ε`, there is a
family of pairwise *commuting* Hermitian involutions `B i` with
`‖B i − A i‖_HS ≤ 4·n·ε`.

This is the involution form of `chao_commuting_projections_linear`: pass to the
spectral projections `P i = ½(1 + A i)` (whose pairwise commutators are
`¼·‖⁅A i, A j⁆‖_HS ≤ ε/4`), apply the linear Chao bound to
round them to commuting projections `Q i` with `‖Q i − P i‖_HS ≤ 8·n·(ε/4)`, and
pass back via `B i = 2 Q i − 1`, so `‖B i − A i‖_HS = 2·‖Q i − P i‖_HS ≤ 4·n·ε`.
-/
theorem exists_commuting_involutions {d n : ℕ} {ε : ℝ}
    (A : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hAh : ∀ i, (A i).IsHermitian) (hA2 : ∀ i, A i * A i = 1)
    (hcomm : ∀ i j, normHS (⁅A i, A j⁆) ≤ ε) :
    ∃ B : Fin n → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (B i).IsHermitian) ∧ (∀ i, B i * B i = 1) ∧
      (∀ i j, Commute (B i) (B j)) ∧
      (∀ i, normHS (B i - A i) ≤ 4 * (n : ℝ) * ε) := by
  by_contra h_contra;
  obtain ⟨Q, hQ⟩ : ∃ Q : Fin n → Matrix (Fin d) (Fin d) ℂ, (∀ i, IsProj (Q i)) ∧ (∀ i j, Commute (Q i) (Q j)) ∧ (∀ i, normHS (Q i - (1 / 2 : ℂ) • (1 + A i)) ≤ 8 * n * (ε / 4)) := by
    apply chao_commuting_projections_linear;
    · intro i; exact ⟨by
      simp_all +decide [ Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul ], by
        simp_all +decide [ IsIdempotentElem, mul_add, add_mul, mul_assoc ];
        ext; norm_num; ring;⟩;
    · intro i j; convert mul_le_mul_of_nonneg_right ( hcomm i j ) ( show ( 0 : ℝ ) ≤ 1 / 4 by norm_num ) using 1 ; norm_num [ normHS_smul ] ; ring;
      · norm_num [ normHS_smul, LieRing.of_associative_ring_bracket ] ; ring;
      · ring;
  refine' h_contra ⟨ fun i => ( 2 : ℂ ) • Q i - 1, _, _, _, _ ⟩;
  · simp_all +decide [ IsProj, Matrix.IsHermitian ];
  · intro i; have := hQ.1 i; simp_all +decide [ IsProj, mul_sub, sub_mul, two_smul ] ;
    simp_all +decide [ mul_add, add_mul, IsIdempotentElem ];
  · simp_all +decide [ Commute ];
    simp_all +decide [ SemiconjBy, sub_mul, mul_sub ];
    intro i j; ext x y; norm_num [ two_smul ] ; ring;
  · intro i
    have h_norm : normHS ((2 : ℂ) • (Q i - (1 / 2 : ℂ) • (1 + A i))) ≤ 4 * n * ε := by
      convert mul_le_mul_of_nonneg_left ( hQ.2.2 i ) zero_le_two using 1 <;> ring;
      convert normHS_smul ( 2 : ℂ ) ( Q i - ( 1 / 2 : ℂ ) • ( 1 + A i ) ) using 1 ; norm_num [ mul_comm ];
    convert h_norm using 2 ; ext ; norm_num ; ring

end LamplighterStability