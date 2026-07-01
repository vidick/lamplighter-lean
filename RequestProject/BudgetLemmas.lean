import Mathlib

/-!
# Real-arithmetic budget lemmas for the final assembly

These two purely real-arithmetic lemmas package the parameter-budget checks used
in both the exponential-window (`MainAssemblyExp.lean`) and polynomial-window
(`MainAssembly.lean`) final assemblies.  They are placed in their own file so
that both assemblies can import them (since `MainAssemblyExp` imports
`MainAssembly`, the polynomial assembly cannot import them back from there).
-/

namespace LamplighterStability

/-
Real-arithmetic budget for the two Pythagorean closeness bounds.  With the
parameter choices `t ≈ C/κ²`, `υ = δ = cκ¹⁴`, `η = 101250c²κ¹⁴`, the back-half
bounds `Cback·t⁶·(υ+δ+η)` and `Cback·(1/t + t⁶(υ+δ+η))` are at most `κ²/4`.
-/
theorem budget_main {Cback C c κ : ℝ} {t : ℕ}
    (hκ0 : 0 < κ)
    (hCback : 0 < Cback) (hCbackC : Cback ≤ C / 8)
    (hc0 : 0 < c) (hc1000 : c ≤ 1 / 1000)
    (hcD : Cback * (C + 1) ^ 6 * (2 * c + 64800 * c ^ 2) ≤ 1 / 8)
    (htlb : C / κ ^ 2 ≤ (t : ℝ)) (htub : (t : ℝ) ≤ (C + 1) / κ ^ 2) :
    Cback * (t : ℝ) ^ 6 * (c * κ ^ 14 + c * κ ^ 14 + 64800 * c ^ 2 * κ ^ 14)
        ≤ κ ^ 2 / 4 ∧
    Cback * ((1 : ℝ) / (t : ℝ)
        + (t : ℝ) ^ 6 * (c * κ ^ 14 + c * κ ^ 14 + 64800 * c ^ 2 * κ ^ 14))
        ≤ κ ^ 2 / 4 := by
  constructor <;> ring_nf at *;
  · -- By simplifying, we can see that the inequality holds.
    have h_simp : (t : ℝ) ^ 6 ≤ (C + 1) ^ 6 / κ ^ 12 := by
      convert pow_le_pow_left₀ ( by positivity ) htub 6 using 1 ; ring;
    rw [ le_div_iff₀ ( by positivity ) ] at h_simp;
    nlinarith [ show 0 < Cback * c * κ ^ 12 by positivity, show 0 < Cback * c ^ 2 * κ ^ 12 by positivity, show 0 < Cback * c * κ ^ 14 by positivity, show 0 < Cback * c ^ 2 * κ ^ 14 by positivity, pow_pos hκ0 12, pow_pos hκ0 14 ];
  · refine' le_trans ( add_le_add_right _ _ ) _;
    exact Cback * ( C * κ⁻¹ ^ 2 ) ⁻¹;
    · gcongr;
      exact mul_pos ( by nlinarith [ inv_pos.2 hκ0 ] ) ( sq_pos_of_pos ( inv_pos.2 hκ0 ) );
    · refine' le_trans ( add_le_add_right _ _ ) _;
      exact κ ^ 2 * ( 1 / 8 );
      · field_simp;
        rw [ div_le_iff₀ ] <;> nlinarith [ show 0 < C by nlinarith [ inv_pos.2 hκ0 ] ];
      · have h_bound : Cback * t^6 * κ^14 ≤ Cback * ((C + 1) / κ^2)^6 * κ^14 := by
          gcongr;
          convert htub using 1 ; ring;
        field_simp at *;
        nlinarith [ show 0 ≤ Cback * c by positivity, show 0 ≤ Cback * c ^ 2 by positivity, show 0 ≤ Cback * c ^ 3 by positivity, show 0 ≤ Cback * c ^ 4 by positivity, show 0 ≤ Cback * c ^ 5 by positivity, show 0 ≤ Cback * c ^ 6 by positivity ]

/-
Real-arithmetic budget for the pre-processing closeness `‖A − B₀‖ ≤ κ/2`.
-/
theorem budget_close {c κ ε : ℝ} {m : ℕ}
    (hκ0 : 0 < κ) (hκ2 : κ ≤ 1 / 2) (hc0 : 0 < c) (hc1000 : c ≤ 1 / 1000)
    (hεeq : ε = c * κ ^ 7 / ((m : ℝ) + 1) ^ 2) :
    ε + 4 * ((2 * (m + 1) + 1 : ℕ) : ℝ) * (5 * ε) ≤ κ / 2 := by
  -- Substitute hεeq into the inequality.
  rw [hεeq];
  field_simp;
  norm_num [ pow_succ' ] at * ; nlinarith [ pow_le_pow_left₀ ( by positivity ) hκ2 6, mul_le_mul_of_nonneg_left hc1000 <| pow_nonneg hκ0.le 6, mul_le_mul_of_nonneg_left hc1000 <| pow_nonneg hκ0.le 5, mul_le_mul_of_nonneg_left hc1000 <| pow_nonneg hκ0.le 4, mul_le_mul_of_nonneg_left hc1000 <| pow_nonneg hκ0.le 3, mul_le_mul_of_nonneg_left hc1000 <| pow_nonneg hκ0.le 2 ] ;

end LamplighterStability