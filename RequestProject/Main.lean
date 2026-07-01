import Mathlib
import RequestProject.MainAssembly

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Polynomial Hilbert–Schmidt stability of the lamplighter group

This file formalizes the **statement** of the main technical theorem
(Theorem 1.1) of the paper *"Polynomial Hilbert–Schmidt stability of the
lamplighter group"* by Alon Dogon and Thomas Vidick.

The theorem is stated in a self-contained way and concerns approximately
"order-two and commuting along an orbit" pairs of unitaries `A, T`, asserting
that they can be perturbed (in the normalized Hilbert–Schmidt distance) to
genuine such unitaries, with a perturbation controlled polynomially in the
tolerance `κ`.

The full proof is the content of the entire paper (it relies on new dynamical
methods — a polynomial continuous tower decomposition — together with
techniques from descriptive combinatorics).  The proof is assembled in
`RequestProject.MainAssembly` (see `core_main`); this file discharges the
theorem by `core_main`.

The normalized Hilbert–Schmidt norm `normHS` used in the statement is the shared
`LamplighterStability.normHS` from `RequestProject.Foundations`, namely
`‖A‖_HS = √((1/|ι|) ∑_{i,j} |A_{ij}|²)`; for `ι = Fin d` this is
`√((1/d) ∑_{i,j} |A_{ij}|²)`.
-/

namespace LamplighterStability

/-- **Theorem 1.1** (main technical theorem).

There exist universal constants `C, c > 0` such that the following holds.
Let `0 < κ ≤ 1/2`, set
`M = ⌈C · κ^(-20) · log(2/κ)⌉` and `ε = c · κ⁷ / M²`.
(The `M²` denominator is the paper's, recovered via the improved
*linear* form of the Chao nearby-commuting-projections lemma
`8·n·ε₀` under `ε₀ ≤ 1/(32 n)`; see `IMPROVED_CHAO_PLAN.md`.)
Then for every dimension `d` and every pair of unitaries `A, T ∈ U(d)` such that

* `‖A² - 1‖_HS ≤ ε`, and
* `‖[A, T^{-i} A T^{i}]‖_HS ≤ ε` for all `0 ≤ i ≤ 2M`,

there exist unitaries `Ã, T̃ ∈ U(d)` with `Ã² = 1` and such that `T̃^{-i} Ã T̃^{i}`
commutes with `Ã` for all `i ∈ ℤ`, and moreover

* `‖A - Ã‖_HS ≤ κ` and `‖T - T̃‖_HS ≤ κ`.

Here unitaries are elements of `Matrix.unitaryGroup (Fin d) ℂ`; integer powers
`T^i` are taken in this group, and `star T = T⁻¹` so that `(star T)^i = T^{-i}`.
The bracket `⁅·,·⁆` is the ring commutator `X Y - Y X`. -/
theorem lamplighter_HS_stability :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (κ : ℝ), 0 < κ → κ ≤ 1 / 2 →
        ∀ (M : ℕ) (ε : ℝ),
          M = ⌈C * κ ^ (-20 : ℤ) * Real.log (2 / κ)⌉₊ →
          ε = c * κ ^ 7 / (M : ℝ) ^ 2 →
          ∀ (d : ℕ) (A T : Matrix.unitaryGroup (Fin d) ℂ),
            normHS ((A : Matrix (Fin d) (Fin d) ℂ) ^ 2 - 1) ≤ ε →
            (∀ i : ℕ, i ≤ 2 * M →
              normHS (⁅(A : Matrix (Fin d) (Fin d) ℂ),
                (star (T : Matrix (Fin d) (Fin d) ℂ)) ^ i
                  * (A : Matrix (Fin d) (Fin d) ℂ)
                  * (T : Matrix (Fin d) (Fin d) ℂ) ^ i⁆) ≤ ε) →
            ∃ (A' T' : Matrix.unitaryGroup (Fin d) ℂ),
              (A' : Matrix (Fin d) (Fin d) ℂ) ^ 2 = 1 ∧
              (∀ i : ℤ, Commute (A' : Matrix.unitaryGroup (Fin d) ℂ)
                (T' ^ (-i) * A' * T' ^ i)) ∧
              normHS ((A : Matrix (Fin d) (Fin d) ℂ)
                  - (A' : Matrix (Fin d) (Fin d) ℂ)) ≤ κ ∧
              normHS ((T : Matrix (Fin d) (Fin d) ℂ)
                  - (T' : Matrix (Fin d) (Fin d) ℂ)) ≤ κ :=
  core_main

/- **Theorem 1.1, exponential-window form.** (Removed from this export.)

The exponential-window variant `lamplighter_HS_stability_exp` and its supporting
module `RequestProject.MainAssemblyExp` have been omitted from this cleaned-up
export, which focuses solely on the polynomial-window main theorem
`lamplighter_HS_stability`.

Identical to `lamplighter_HS_stability` except the window `M` is supplied as an
existential function `Mfun : ℝ → ℕ` of the tolerance `κ` (in particular it may be
exponential in `1/κ`), rather than the closed-form polynomial
`M = ⌈C·κ^(-20)·log(2/κ)⌉`.  This is the lamplighter group's Hilbert–Schmidt
stability with a computable (exponential) modulus; it is `core_main_exp`.

The polynomial-window form `lamplighter_HS_stability` is the sharper statement;
this exponential form avoids the polynomial marker lemma entirely. -/

end LamplighterStability
