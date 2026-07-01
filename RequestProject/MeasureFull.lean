import Mathlib
import RequestProject.OrbitConstruction
import RequestProject.OperatorDefect

/-!
# Combined measure input: approximate invariance + operator equivariance defect

`OrbitConstruction.measure_input` packages Section 5 steps 0–2 (orbit → commuting
involutions → approximately invariant induced measure).  For the back-half
assembly `tower_rep_final` we additionally need the **operator** (Hilbert–Schmidt)
form of the equivariance defect `hopdef` (the input to Lemma `lem:clb`), with the
*same* bound `η = 4050·(m+1)⁶·(5ε)²` that controls the measure defect.

`measure_input_full` adds that conjunct, derived from `operator_defect_le`
(using the improved linear-Chao bound `η = 2592·(m+1)⁴·(5ε)²`)
(`OperatorDefect.lean`) and `shift_defect_le` (`OrbitInput.lean`) applied to the
exactly `T`-equivariant orbit family (`orbit_equiv`).
-/

namespace LamplighterStability.OrbitConstruction

open scoped BigOperators
open Matrix
open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.OrbitInput LamplighterStability.MeasureInstantiation
  LamplighterStability.MeasureBridge

variable {d : ℕ}

theorem measure_input_full (m : ℕ) (T : unitaryGroup (Fin d) ℂ)
    {A₀ : Matrix (Fin d) (Fin d) ℂ}
    (hA₀u : A₀ ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (hA₀2 : A₀ * A₀ = 1)
    (A : unitaryGroup (Fin d) ℂ) {ε : ℝ}
    (hA₀d : normHS ((A : Matrix (Fin d) (Fin d) ℂ) - A₀) ≤ ε)
    (hcomm : ∀ i : ℕ, i ≤ 2 * (m + 1) →
      normHS (⁅(A : Matrix (Fin d) (Fin d) ℂ),
        (star (T : Matrix (Fin d) (Fin d) ℂ)) ^ i * (A : Matrix (Fin d) (Fin d) ℂ)
          * (T : Matrix (Fin d) (Fin d) ℂ) ^ i⁆) ≤ ε) :
    ∃ B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (B i).IsHermitian) ∧ (∀ i, B i * B i = 1) ∧
      (∀ i j, Commute (B i) (B j)) ∧
      (∀ i, normHS (B i - orbit T A₀ (i : ℤ))
        ≤ 4 * ((2 * (m + 1) + 1 : ℕ) : ℝ) * (5 * ε)) ∧
      ApproxInvMeasure m (2592 * ((m : ℝ) + 1) ^ 4 * (5 * ε) ^ 2)
        (pvmMeasure (m + 1) (EpatB (m + 1) B)) ∧
      (∑ x : Win m → Bool,
          normHS (star (T : Matrix (Fin d) (Fin d) ℂ)
              * Edef (m + 1) (EpatB (m + 1) B) (cyl m x)
              * (T : Matrix (Fin d) (Fin d) ℂ)
            - Edef (m + 1) (EpatB (m + 1) B)
                ((L : Equiv.Perm Cfg) '' cyl m x)) ^ 2
        ≤ 2592 * ((m : ℝ) + 1) ^ 4 * (5 * ε) ^ 2) := by
  -- Apply measure_input to obtain the existence of B.
  obtain ⟨B, hB⟩ := measure_input m T hA₀u hA₀2 A hA₀d hcomm;
  refine' ⟨ B, hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, hB.2.2.2.2, _ ⟩;
  convert (LamplighterStability.MeasureInstantiation.operator_defect_le m T.2 B hB.1 hB.2.1 hB.2.2.1) |> le_trans <| ?_ using 1;
  refine' le_trans ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun i _ => pow_le_pow_left₀ ( normHS_nonneg _ ) ( show normHS _ ≤ 2 * ( 4 * ↑ ( 2 * ( m + 1 ) + 1 ) * ( 5 * ε ) ) from _ ) 2 ) ( by positivity ) ) _;
  · convert LamplighterStability.OrbitInput.shift_defect_le T.2 hB.2.2.2.1 ( fun k => ?_ ) i using 1;
    intro j hj; convert LamplighterStability.OrbitConstruction.orbit_equiv k using 1;
    exact hj ▸ rfl;
  · norm_num [ Finset.card_univ ] ; ring_nf;
    gcongr <;> norm_num

end LamplighterStability.OrbitConstruction