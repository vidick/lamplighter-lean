import Mathlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def normHS (A : Matrix ι ι ℂ) : ℝ :=
  Real.sqrt ((1 / (Fintype.card ι : ℝ)) * ∑ i, ∑ j, ‖A i j‖ ^ 2)

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
  by sorry
