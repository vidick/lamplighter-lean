import RequestProject.Dynamics.PropDecompPolyExplicit

/-!
# Closed-form bound on the polynomial tower-decomposition window

This file bounds the explicit window `winBoundPoly C2 t υ δ` of
`prop_decomp_poly_explicit` by the closed-form modulus `C·κ⁻²⁰·log(2/κ)` of
Theorem 1.1, for the assembly parameter choices `t = ⌈C_t/κ²⌉`, `υ = δ = c·κ¹⁴`.

The numerics: with `L := log(2/κ)`,
`ℓ = ⌈coverLenPoly⌉ = O(κ⁻¹⁶ L)`, `K = 2ℓ+t = O(κ⁻¹⁶ L)`,
`markerDefPoly = O(κ⁻⁶ L²)`, `D = O(κ⁻¹⁶ L²)`, hence
`winBoundPoly = 2tD + 6D + 31t + 1 = O(κ⁻¹⁸ L²)`.  Since `κ² L ≤ 1`, this is
`≤ C κ⁻²⁰ L` with one large universal constant `C`.
-/

namespace LamplighterStability.Dynamics

open scoped BigOperators

/-! ## Elementary real/log helper lemmas -/

/-
For `0 < κ ≤ 1/2`, `log(2/κ) ≥ 1`.
-/
lemma one_le_log_two_div {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 1 / 2) :
    (1 : ℝ) ≤ Real.log (2 / κ) := by
  exact Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by linarith [ Real.exp_one_lt_d9.le, show ( 2 : ℝ ) / κ ≥ 4 by rw [ ge_iff_le, le_div_iff₀ hκ ] ; linarith ] )

/-
For `0 < κ ≤ 1/2`, `κ² · log(2/κ) ≤ 1`.  (Via `log x ≤ x - 1`.)
-/
lemma sq_mul_log_two_div_le_one {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 1 / 2) :
    κ ^ 2 * Real.log (2 / κ) ≤ 1 := by
  have := Real.log_le_sub_one_of_pos ( show 0 < 2 / κ by positivity );
  nlinarith [ mul_div_cancel₀ 2 hκ.ne', mul_le_mul_of_nonneg_left hκ2 hκ.le ]

/-
For `0 < κ ≤ 1/2` and `0 < c ≤ 1`, `log(2/(c κ¹⁴)) ≤ (14 - log c)·log(2/κ)`.
-/
lemma log_two_div_cmul {κ c : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 1 / 2) (hc0 : 0 < c)
    (hc1 : c ≤ 1) :
    Real.log (2 / (c * κ ^ 14)) ≤ (14 - Real.log c) * Real.log (2 / κ) := by
  -- We'll use the fact that $L = \log(2/\kappa)$ and $K = \log(\kappa)$ to simplify the expression.
  set L := Real.log (2 / κ)
  set K := Real.log κ
  have hL1 : 1 ≤ L := by
    exact one_le_log_two_div hκ hκ2
  have hLeq : L = Real.log 2 - K := by
    exact Real.log_div ( by positivity ) ( by positivity );
  -- Substitute $L$ and $K$ into the inequality.
  have h_sub : Real.log 2 - (Real.log c + 14 * K) ≤ (14 - Real.log c) * (Real.log 2 - K) := by
    nlinarith [ Real.log_pos one_lt_two, Real.log_le_sub_one_of_pos hc0, mul_le_mul_of_nonpos_left hL1 ( Real.log_nonpos hc0.le hc1 ) ];
  convert h_sub using 1 <;> norm_num [ Real.log_div, Real.log_mul, hκ.ne', hc0.ne' ] ; ring;
  exact Or.inl hLeq



/-
`logb₂((κ²)⁻¹) ≤ 3·log(2/κ)` for `0 < κ ≤ 1/2`.
-/
lemma logb_two_inv_sq_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 1 / 2) :
    Real.logb 2 ((κ ^ 2)⁻¹) ≤ 3 * Real.log (2 / κ) := by
  rw [ Real.logb, Real.log_inv, Real.log_pow ];
  rw [ Real.log_div ] <;> norm_num <;> try linarith;
  rw [ div_le_iff₀ ( Real.log_pos one_lt_two ) ];
  have := Real.log_two_gt_d9 ; norm_num at * ; nlinarith [ Real.log_le_sub_one_of_pos hκ, Real.log_le_sub_one_of_pos zero_lt_two, Real.log_pos one_lt_two, mul_le_mul_of_nonneg_left this.le <| Real.log_nonneg one_le_two ]

/-! ## Bounding the Nat-expression `winBoundPoly` by a polynomial in real bounds -/

/-
Pure arithmetic: given real upper bounds `Tb ≥ t`, `Lb ≥ ℓ`,
`Lg ≥ Nat.log₂(4(2t+1)²(2ℓ+3)²)` (all `≥ 1`/`≥ 0`), the window
`winBoundPoly`-expression is bounded by an explicit polynomial in `Tb, Lb, Lg`.
-/
lemma winBoundPoly_expr_le {t ℓ : ℕ} {Tb Lb Lg : ℝ}
    (ht1 : 1 ≤ t)
    (hTb : (t : ℝ) ≤ Tb) (hLb : (ℓ : ℝ) ≤ Lb)
    (hTb1 : 1 ≤ Tb) (hLb1 : 1 ≤ Lb)
    (hlog : (Nat.log 2 (4 * (2 * t + 1) ^ 2 * (2 * ℓ + 3) ^ 2) : ℝ) ≤ Lg)
    (hLg0 : 0 ≤ Lg) :
    ((2 * t * ((2 * ℓ + t) + markerDefPoly t ℓ (2 * ℓ + t))
        + 6 * ((2 * ℓ + t) + markerDefPoly t ℓ (2 * ℓ + t)) + 31 * t + 1 : ℕ) : ℝ)
      ≤ (2 * Tb + 6) * (5 * Lb + 4 * Tb + 36 * Tb ^ 3 * (Lg + 2) ^ 2) + 31 * Tb + 1 := by
  -- By definition of `markerDefPoly`, we know that
  have h_marker : markerDefPoly t ℓ (2 * ℓ + t) ≤ 3 * Lb + 3 * Tb + 36 * Tb ^ 3 * (Lg + 2) ^ 2 := by
    refine' le_trans _ ( add_le_add ( le_rfl ) _ );
    rotate_left;
    exact 4 * ( 2 * t + 1 ) ^ 2 * ( Lg + 2 ) ^ 2 * t;
    · -- By simplifying, we can see that this inequality holds.
      have h_simp : (2 * t + 1 : ℝ) ^ 2 * t ≤ 9 * Tb ^ 3 := by
        nlinarith [ sq_nonneg ( Tb - t ), mul_le_mul_of_nonneg_left hTb ( Nat.cast_nonneg t ) ];
      nlinarith only [ h_simp, show 0 ≤ ( Lg + 2 ) ^ 2 by positivity ];
    · refine' le_trans _ ( add_le_add ( le_rfl ) _ );
      rotate_left;
      exact 4 * ( 2 * t + 1 ) ^ 2 * ( Nat.log 2 ( 4 * ( 2 * t + 1 ) ^ 2 * ( 2 * ℓ + 3 ) ^ 2 ) + 2 ) ^ 2 * t;
      · gcongr;
      · unfold markerDefPoly;
        norm_num;
        constructor <;> linarith [ ( by norm_cast : ( 1 : ℝ ) ≤ t ) ];
  norm_num [ markerDefPoly ] at *;
  nlinarith [ show ( t : ℝ ) ≥ 1 by norm_cast, show ( t : ℝ ) ≤ Tb by assumption, show ( ℓ : ℝ ) ≤ Lb by assumption, show ( 0 : ℝ ) ≤ Tb ^ 3 * ( Lg + 2 ) ^ 2 by positivity ]

/-
The `Nat.log` term in `markerDefPoly` is bounded by `12 + 2 logb₂ Tb + 2 logb₂ Lb`.
-/
lemma natLog_prod_sq_le {t ℓ : ℕ} {Tb Lb : ℝ}
    (ht1 : 1 ≤ t) (hℓ1 : 1 ≤ ℓ)
    (hTb : (t : ℝ) ≤ Tb) (hLb : (ℓ : ℝ) ≤ Lb) :
    (Nat.log 2 (4 * (2 * t + 1) ^ 2 * (2 * ℓ + 3) ^ 2) : ℝ)
      ≤ 12 + 2 * Real.logb 2 Tb + 2 * Real.logb 2 Lb := by
  refine' le_trans ( Nat.cast_le.mpr ( Nat.log_mono_right _ ) ) _;
  exact 900 * t ^ 2 * ℓ ^ 2;
  · nlinarith only [ sq ( t - ℓ : ℤ ), mul_le_mul_of_nonneg_left ht1 ( Nat.zero_le ℓ ), mul_le_mul_of_nonneg_left hℓ1 ( Nat.zero_le t ), ht1, hℓ1 ];
  · have h_log_bound : Real.logb 2 (900 * t ^ 2 * ℓ ^ 2) ≤ 12 + 2 * Real.logb 2 t + 2 * Real.logb 2 ℓ := by
      rw [ Real.logb_mul, Real.logb_mul ] <;> norm_num <;> try positivity;
      norm_num [ Real.logb, mul_div_assoc ];
      rw [ div_le_iff₀ ( Real.log_pos ( by norm_num ) ) ] ; norm_num [ ← Real.log_rpow, Real.log_le_log ];
    refine' le_trans _ ( h_log_bound.trans _ );
    · rw [ Real.le_logb_iff_rpow_le ] <;> norm_cast <;> try positivity;
      exact Nat.pow_log_le_self 2 ( by positivity );
    · gcongr <;> norm_cast

/-
**Polynomial domination.**  The explicit `winBoundPoly_expr_le` bound, with
`Tb = (Ct+1)v`, `Lb = Al·v⁸·L`, `Lg = Ag·L`, is `≤ B·v⁹·L²` for a universal `B`.
-/
lemma poly_window_dom (Ct Al Ag : ℝ) (hCt : 0 ≤ Ct) (hAl : 0 ≤ Al) (hAg : 0 ≤ Ag) :
    ∃ B : ℝ, 0 < B ∧ ∀ v L : ℝ, 1 ≤ v → 1 ≤ L →
      (2 * ((Ct + 1) * v) + 6)
          * (5 * (Al * v ^ 8 * L) + 4 * ((Ct + 1) * v)
              + 36 * ((Ct + 1) * v) ^ 3 * ((Ag * L) + 2) ^ 2)
        + 31 * ((Ct + 1) * v) + 1
      ≤ B * v ^ 9 * L ^ 2 := by
  -- Let's choose $B = (2 * (Ct + 1) + 6) * (5 * Al + 4 * (Ct + 1) + 36 * (Ct + 1) ^ 3 * (Ag + 2) ^ 2) + 31 * (Ct + 1) + 1$.
  use (2 * (Ct + 1) + 6) * (5 * Al + 4 * (Ct + 1) + 36 * (Ct + 1) ^ 3 * (Ag + 2) ^ 2) + 31 * (Ct + 1) + 1;
  refine' ⟨ by positivity, fun v L hv hL => _ ⟩;
  have h_expand : (2 * ((Ct + 1) * v) + 6) * (5 * (Al * v ^ 8 * L) + 4 * ((Ct + 1) * v) + 36 * ((Ct + 1) * v) ^ 3 * (Ag * L + 2) ^ 2) ≤ (2 * (Ct + 1) + 6) * (5 * Al + 4 * (Ct + 1) + 36 * (Ct + 1) ^ 3 * (Ag + 2) ^ 2) * v ^ 9 * L ^ 2 := by
    have h_expand : 5 * (Al * v ^ 8 * L) + 4 * ((Ct + 1) * v) + 36 * ((Ct + 1) * v) ^ 3 * (Ag * L + 2) ^ 2 ≤ (5 * Al + 4 * (Ct + 1) + 36 * (Ct + 1) ^ 3 * (Ag + 2) ^ 2) * v ^ 8 * L ^ 2 := by
      -- Apply the bounds to each term individually.
      have h_term1 : 5 * (Al * v ^ 8 * L) ≤ 5 * Al * v ^ 8 * L ^ 2 := by
        nlinarith [ show 0 ≤ Al * v ^ 8 by positivity, show 0 ≤ Al * v ^ 8 * L by positivity, show L ≤ L ^ 2 by nlinarith ]
      have h_term2 : 4 * ((Ct + 1) * v) ≤ 4 * (Ct + 1) * v ^ 8 * L ^ 2 := by
        nlinarith [ show 0 ≤ ( Ct + 1 ) * v ^ 8 by positivity, show 0 ≤ ( Ct + 1 ) * v ^ 8 * L ^ 2 by positivity, show v ^ 8 ≥ v by exact le_self_pow₀ hv ( by norm_num ), show L ^ 2 ≥ 1 by nlinarith ]
      have h_term3 : 36 * ((Ct + 1) * v) ^ 3 * (Ag * L + 2) ^ 2 ≤ 36 * (Ct + 1) ^ 3 * (Ag + 2) ^ 2 * v ^ 8 * L ^ 2 := by
        have h_term3 : (Ag * L + 2) ^ 2 ≤ (Ag + 2) ^ 2 * L ^ 2 := by
          nlinarith [ mul_le_mul_of_nonneg_left hL hAg, mul_le_mul_of_nonneg_left hL ( sq_nonneg Ag ), mul_le_mul_of_nonneg_left hL ( sq_nonneg L ), mul_le_mul_of_nonneg_left hL ( sq_nonneg ( Ag * L ) ), mul_le_mul_of_nonneg_left hL ( sq_nonneg ( Ag * L ^ 2 ) ), mul_le_mul_of_nonneg_left hL ( sq_nonneg ( Ag ^ 2 * L ) ), mul_le_mul_of_nonneg_left hL ( sq_nonneg ( Ag ^ 2 * L ^ 2 ) ) ];
        refine le_trans ( mul_le_mul_of_nonneg_left h_term3 <| by positivity ) ?_;
        nlinarith only [ show 0 ≤ ( Ct + 1 ) ^ 3 * ( Ag + 2 ) ^ 2 * L ^ 2 by positivity, show v ^ 3 ≤ v ^ 8 by exact pow_le_pow_right₀ hv ( by norm_num ) ];
      linarith;
    refine le_trans ( mul_le_mul_of_nonneg_left h_expand <| by positivity ) ?_;
    nlinarith [ show 0 ≤ ( 5 * Al + 4 * ( Ct + 1 ) + 36 * ( Ct + 1 ) ^ 3 * ( Ag + 2 ) ^ 2 ) * v ^ 8 * L ^ 2 by positivity ];
  nlinarith [ show 0 ≤ ( 2 * ( Ct + 1 ) + 6 ) * ( 5 * Al + 4 * ( Ct + 1 ) + 36 * ( Ct + 1 ) ^ 3 * ( Ag + 2 ) ^ 2 ) * v ^ 9 * L ^ 2 by positivity, show 0 ≤ 31 * ( Ct + 1 ) * v ^ 9 * L ^ 2 by positivity, show 0 ≤ v ^ 9 * L ^ 2 by positivity, show v ^ 9 * L ^ 2 ≥ v by nlinarith [ show v ^ 9 ≥ v by exact le_self_pow₀ hv ( by norm_num ), show L ^ 2 ≥ 1 by nlinarith ] ]

/-
Bound on `ℓ = ⌈coverLenPoly⌉` in `κ`-terms: `ℓ ≤ A_ℓ · ((κ²)⁻¹)⁸ · log(2/κ)`.
-/
lemma coverCeil_bound (C2 C_t c : ℝ) (hC2 : 0 < C2) (hCt : 0 < C_t) (hc0 : 0 < c)
    (hc : c ≤ 1 / 1000) {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 1 / 2)
    {t : ℕ} (ht1 : 1 ≤ t) (hTb : (t : ℝ) ≤ (C_t + 1) * (κ ^ 2)⁻¹) :
    (⌈coverLenPoly C2 t (c * κ ^ 14) (c * κ ^ 14)⌉₊ : ℝ)
      ≤ (3 * C2 * (C_t + 1) * (14 - Real.log c) / c + 4 * (C_t + 1) + 1)
          * (κ ^ 2)⁻¹ ^ 8 * Real.log (2 / κ) := by
  refine' le_trans ( Nat.ceil_lt_add_one _ |> le_of_lt ) _;
  · exact add_nonneg ( div_nonneg ( mul_nonneg ( mul_nonneg hC2.le ( by positivity ) ) ( Real.log_nonneg ( by rw [ le_div_iff₀ ( by positivity ) ] ; nlinarith [ pow_le_pow_left₀ ( by positivity ) hκ2 14 ] ) ) ) ( by positivity ) ) ( by positivity );
  · -- Apply the bound on `Real.log (2 / (c * κ ^ 14))` from `log_two_div_cmul`.
    have h_log_bound : Real.log (2 / (c * κ ^ 14)) ≤ (14 - Real.log c) * Real.log (2 / κ) := by
      apply log_two_div_cmul hκ hκ2 hc0 (by linarith);
    -- Apply the bound on `Real.log (2 / (c * κ ^ 14))` from `log_two_div_cmul` and simplify.
    have h_simplified : C2 * (3 * t) * Real.log (2 / (c * κ ^ 14)) / (c * κ ^ 14) ≤ 3 * C2 * (C_t + 1) * (14 - Real.log c) / c * (κ ^ 2)⁻¹ ^ 8 * Real.log (2 / κ) := by
      refine le_trans ( div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_left h_log_bound <| by positivity ) <| by positivity ) ?_;
      convert mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left hTb <| show 0 ≤ 3 * C2 * ( 14 - Real.log c ) * Real.log ( 2 / κ ) / ( c * κ ^ 14 ) by exact div_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) <| by linarith [ Real.log_le_sub_one_of_pos hc0 ] ) <| Real.log_nonneg <| by rw [ le_div_iff₀ <| by positivity ] ; linarith ) <| by positivity ) <| show 0 ≤ 1 by positivity using 1 ; ring;
      grind;
    -- Apply the bound on `4 * t` from `hTb`.
    have h_four_t : 4 * (t : ℝ) ≤ 4 * (C_t + 1) * (κ ^ 2)⁻¹ ^ 8 * Real.log (2 / κ) := by
      have h_four_t : 4 * (t : ℝ) ≤ 4 * (C_t + 1) * (κ ^ 2)⁻¹ ^ 8 := by
        nlinarith [ show ( κ ^ 2 ) ⁻¹ ^ 7 ≥ 1 by exact one_le_pow₀ ( by nlinarith [ inv_mul_cancel₀ ( ne_of_gt ( sq_pos_of_pos hκ ) ) ] ) ];
      exact le_trans h_four_t ( le_mul_of_one_le_right ( by positivity ) ( one_le_log_two_div hκ hκ2 ) );
    unfold coverLenPoly;
    have h_one : 1 ≤ (κ ^ 2)⁻¹ ^ 8 * Real.log (2 / κ) := by
      exact one_le_mul_of_one_le_of_one_le ( one_le_pow₀ ( by rw [ inv_eq_one_div, le_div_iff₀ ] <;> nlinarith ) ) ( one_le_log_two_div hκ hκ2 );
    grind +qlia

/-
The `Nat.log` term, with `t ≤ P·v`, `ℓ ≤ Q·v⁹` (`v = (κ²)⁻¹`), is bounded by
`12 + 2 logb₂ P + 2 logb₂ Q + 60·log(2/κ)`.
-/
lemma natLogX_bound {κ P Q : ℝ} (hκ : 0 < κ) (hκ2 : κ ≤ 1 / 2)
    (hP1 : 1 ≤ P) (hQ1 : 1 ≤ Q) {t ℓ : ℕ} (ht1 : 1 ≤ t) (hℓ1 : 1 ≤ ℓ)
    (hTb : (t : ℝ) ≤ P * (κ ^ 2)⁻¹) (hLb : (ℓ : ℝ) ≤ Q * (κ ^ 2)⁻¹ ^ 9) :
    (Nat.log 2 (4 * (2 * t + 1) ^ 2 * (2 * ℓ + 3) ^ 2) : ℝ)
      ≤ 12 + 2 * Real.logb 2 P + 2 * Real.logb 2 Q + 60 * Real.log (2 / κ) := by
  -- Apply the lemma `natLog_prod_sq_le` with the given bounds.
  have h_natLog : (Nat.log 2 (4 * (2 * t + 1) ^ 2 * (2 * ℓ + 3) ^ 2) : ℝ) ≤ 12 + 2 * Real.logb 2 (P * (κ ^ 2)⁻¹) + 2 * Real.logb 2 (Q * (κ ^ 2)⁻¹ ^ 9) := by
    apply natLog_prod_sq_le;
    all_goals linarith [ show ( t : ℝ ) ≥ 1 by norm_cast, show ( ℓ : ℝ ) ≥ 1 by norm_cast ];
  -- Apply the logarithm properties to split the terms.
  have h_log_split : Real.logb 2 (P * (κ ^ 2)⁻¹) = Real.logb 2 P + Real.logb 2 ((κ ^ 2)⁻¹) ∧ Real.logb 2 (Q * (κ ^ 2)⁻¹ ^ 9) = Real.logb 2 Q + 9 * Real.logb 2 ((κ ^ 2)⁻¹) := by
    exact ⟨ by rw [ Real.logb_mul ( by positivity ) ( by positivity ) ], by rw [ Real.logb_mul ( by positivity ) ( by positivity ), Real.logb, Real.logb, Real.logb, Real.log_pow ] ; ring ⟩;
  linarith [ logb_two_inv_sq_le hκ hκ2 ]

/-! ## The aggregate window bound -/

/-
**Aggregate bound (κ⁻¹⁸ L² form).**  For fixed positive constants
`C2, C_t, c` (with `c ≤ 1/1000`), the window `winBoundPoly C2 ⌈C_t/κ²⌉ (cκ¹⁴) (cκ¹⁴)`
(and the height bound `6⌈C_t/κ²⌉`) plus `1` are `≤ B · κ⁻¹⁸ · (log(2/κ))²` for a
universal `B`.
-/
set_option maxHeartbeats 1000000 in
lemma winBoundPoly_le_aux (C2 C_t c : ℝ)
    (hC2 : 0 < C2) (hCt : 0 < C_t) (hc0 : 0 < c) (hc : c ≤ 1 / 1000) :
    ∃ B : ℝ, 0 < B ∧ ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 2 →
      ((winBoundPoly C2 ⌈C_t / κ ^ 2⌉₊ (c * κ ^ 14) (c * κ ^ 14) : ℝ) + 1
          ≤ B * (κ ^ 2)⁻¹ ^ 9 * (Real.log (2 / κ)) ^ 2) ∧
      ((6 * ⌈C_t / κ ^ 2⌉₊ + 1 : ℝ) ≤ B * (κ ^ 2)⁻¹ ^ 9 * (Real.log (2 / κ)) ^ 2) := by
  -- Let's choose the constants Aℓ and Ag.
  set Aℓ : ℝ := (3 * C2 * (C_t + 1) * (14 - Real.log c) / c + 4 * (C_t + 1) + 1) with hAℓ
  set Ag : ℝ := 12 + 2 * Real.logb 2 (C_t + 1) + 2 * Real.logb 2 (2 * Aℓ) + 60 with hAg;
  -- By `poly_window_dom`, we obtain a universal `Bp > 0` satisfying the `v^9 * L^2` bound.
  obtain ⟨Bp, hBp⟩ : ∃ Bp : ℝ, 0 < Bp ∧ ∀ v L : ℝ, 1 ≤ v → 1 ≤ L →
    (2 * ((C_t + 1) * v) + 6) *
      (5 * (Aℓ * v ^ 8 * L) + 4 * ((C_t + 1) * v) +
        36 * ((C_t + 1) * v) ^ 3 * ((Ag * L) + 2) ^ 2) +
      31 * ((C_t + 1) * v) + 1 ≤
    Bp * v ^ 9 * L ^ 2 := by
      apply poly_window_dom;
      · positivity;
      · exact add_nonneg ( add_nonneg ( div_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg zero_le_three hC2.le ) ( by positivity ) ) ( by linarith [ Real.log_le_sub_one_of_pos hc0 ] ) ) hc0.le ) ( by positivity ) ) zero_le_one;
      · exact add_nonneg ( add_nonneg ( add_nonneg ( by norm_num ) ( mul_nonneg zero_le_two ( Real.logb_nonneg ( by norm_num ) ( by linarith ) ) ) ) ( mul_nonneg zero_le_two ( Real.logb_nonneg ( by norm_num ) ( by nlinarith [ show 0 ≤ 3 * C2 * ( C_t + 1 ) * ( 14 - Real.log c ) / c by exact div_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg zero_le_three hC2.le ) ( by linarith ) ) ( by linarith [ Real.log_le_sub_one_of_pos hc0 ] ) ) hc0.le ] ) ) ) ) ( by norm_num );
  refine' ⟨ Bp + 6 * ( C_t + 1 ) + 2, _, _ ⟩;
  · linarith;
  · intro κ hκ hκ2
    set v := (κ ^ 2)⁻¹
    set L := Real.log (2 / κ)
    have hv1 : 1 ≤ v := by
      exact one_le_inv₀ ( sq_pos_of_pos hκ ) |>.2 ( by nlinarith )
    have hL1 : 1 ≤ L := by
      exact one_le_log_two_div hκ hκ2
    have hTb : (⌈C_t / κ ^ 2⌉₊ : ℝ) ≤ (C_t + 1) * v := by
      have := Nat.ceil_lt_add_one ( show 0 ≤ C_t / κ ^ 2 by positivity );
      grind
    have hLbt : (⌈coverLenPoly C2 ⌈C_t / κ ^ 2⌉₊ (c * κ ^ 14) (c * κ ^ 14)⌉₊ : ℝ) ≤ Aℓ * v ^ 8 * L := by
      apply_rules [ coverCeil_bound ];
      exact Nat.ceil_pos.mpr ( by positivity )
    have hℓ1 : 1 ≤ ⌈coverLenPoly C2 ⌈C_t / κ ^ 2⌉₊ (c * κ ^ 14) (c * κ ^ 14)⌉₊ := by
      refine Nat.ceil_pos.mpr ?_;
      refine' add_pos_of_nonneg_of_pos ( div_nonneg ( mul_nonneg ( mul_nonneg hC2.le ( by positivity ) ) ( Real.log_nonneg _ ) ) ( by positivity ) ) ( by positivity );
      rw [ le_div_iff₀ ] <;> nlinarith [ pow_pos hκ 14, pow_le_pow_left₀ ( by positivity ) hκ2 14 ]
    have hLbt1 : 1 ≤ Aℓ * v ^ 8 * L := by
      exact le_trans ( mod_cast hℓ1 ) hLbt;
    have hLg : (Nat.log 2 (4 * (2 * ⌈C_t / κ ^ 2⌉₊ + 1) ^ 2 * (2 * ⌈coverLenPoly C2 ⌈C_t / κ ^ 2⌉₊ (c * κ ^ 14) (c * κ ^ 14)⌉₊ + 3) ^ 2) : ℝ) ≤ Ag * L := by
      have hLg : L ≤ 2 * v := by
        have hL2v : L ≤ 2 / κ := by
          exact le_trans ( Real.log_le_sub_one_of_pos ( by positivity ) ) ( by ring_nf; norm_num [ hκ.ne' ] );
        exact hL2v.trans ( by rw [ div_eq_mul_inv ] ; exact mul_le_mul_of_nonneg_left ( inv_anti₀ ( by positivity ) ( by nlinarith ) ) zero_le_two );
      have hLbloose : (⌈coverLenPoly C2 ⌈C_t / κ ^ 2⌉₊ (c * κ ^ 14) (c * κ ^ 14)⌉₊ : ℝ) ≤ (2 * Aℓ) * v ^ 9 := by
        convert hLbt.trans ( mul_le_mul_of_nonneg_left hLg <| show 0 ≤ Aℓ * v ^ 8 by
                                                                exact mul_nonneg ( by exact add_nonneg ( add_nonneg ( div_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg zero_le_three hC2.le ) ( by positivity ) ) ( by linarith [ Real.log_le_sub_one_of_pos hc0 ] ) ) hc0.le ) ( by positivity ) ) zero_le_one ) ( by positivity ) ) using 1 ; ring;
      have hLg : (Nat.log 2 (4 * (2 * ⌈C_t / κ ^ 2⌉₊ + 1) ^ 2 * (2 * ⌈coverLenPoly C2 ⌈C_t / κ ^ 2⌉₊ (c * κ ^ 14) (c * κ ^ 14)⌉₊ + 3) ^ 2) : ℝ) ≤ 12 + 2 * Real.logb 2 (C_t + 1) + 2 * Real.logb 2 (2 * Aℓ) + 60 * L := by
        apply_rules [ natLogX_bound ];
        · linarith;
        · exact one_le_mul_of_one_le_of_one_le ( by norm_num ) ( by exact le_add_of_nonneg_left <| add_nonneg ( div_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg ( by norm_num ) <| by positivity ) <| by positivity ) <| sub_nonneg.mpr <| by linarith [ Real.log_le_sub_one_of_pos hc0 ] ) <| by positivity ) <| by positivity );
        · exact Nat.ceil_pos.mpr ( by positivity );
      nlinarith [ show 0 ≤ Real.logb 2 ( C_t + 1 ) by exact Real.logb_nonneg ( by norm_num ) ( by linarith ), show 0 ≤ Real.logb 2 ( 2 * Aℓ ) by exact Real.logb_nonneg ( by norm_num ) ( by linarith [ show 1 ≤ Aℓ by exact le_add_of_nonneg_left <| by exact add_nonneg ( div_nonneg ( mul_nonneg ( mul_nonneg ( by positivity ) <| by positivity ) <| by linarith [ Real.log_le_sub_one_of_pos hc0 ] ) <| by positivity ) <| by positivity ] ) ];
    have hwin : (winBoundPoly C2 ⌈C_t / κ ^ 2⌉₊ (c * κ ^ 14) (c * κ ^ 14) : ℝ) ≤ Bp * v ^ 9 * L ^ 2 := by
      refine le_trans ?_ ( hBp.2 v L hv1 hL1 );
      convert winBoundPoly_expr_le _ _ _ _ _ _ _ using 1;
      any_goals linarith;
      · exact Nat.ceil_pos.mpr ( by positivity );
      · exact one_le_mul_of_one_le_of_one_le ( by linarith ) hv1;
    constructor;
    · nlinarith [ show 1 ≤ v ^ 9 * L ^ 2 by exact one_le_mul_of_one_le_of_one_le ( one_le_pow₀ hv1 ) ( one_le_pow₀ hL1 ) ];
    · nlinarith [ show 0 < v ^ 9 * L ^ 2 by positivity, show v ^ 9 * L ^ 2 ≥ v by exact le_trans ( by nlinarith ) ( le_mul_of_one_le_right ( by positivity ) ( one_le_pow₀ hL1 ) ) |> le_trans <| mul_le_mul_of_nonneg_right ( pow_le_pow_right₀ hv1 <| show 9 ≥ 1 by norm_num ) <| by positivity ]

/-
**Closed-form window bound.**  For fixed positive constants `C2, C_t, c`
(with `c ≤ 1/1000`), there is a universal `C` such that for all `0 < κ ≤ 1/2`,
both `winBoundPoly C2 ⌈C_t/κ²⌉ (cκ¹⁴) (cκ¹⁴) + 1` and `6⌈C_t/κ²⌉ + 1` are at most
`C · κ⁻²⁰ · log(2/κ)`.
-/
lemma exists_window_const (C2 C_t c : ℝ)
    (hC2 : 0 < C2) (hCt : 0 < C_t) (hc0 : 0 < c) (hc : c ≤ 1 / 1000) :
    ∃ C : ℝ, 0 < C ∧ ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 2 →
      ((winBoundPoly C2 ⌈C_t / κ ^ 2⌉₊ (c * κ ^ 14) (c * κ ^ 14) : ℝ) + 1
          ≤ C * κ ^ (-20 : ℤ) * Real.log (2 / κ)) ∧
      ((6 * ⌈C_t / κ ^ 2⌉₊ + 1 : ℝ) ≤ C * κ ^ (-20 : ℤ) * Real.log (2 / κ)) := by
  obtain ⟨ B, hBpos, hAux ⟩ := winBoundPoly_le_aux C2 C_t c hC2 hCt hc0 hc;
  refine' ⟨ B, hBpos, fun κ hκ hκ2 => ⟨ _, _ ⟩ ⟩ <;> norm_cast at *;
  · refine' le_trans ( hAux κ hκ hκ2 |>.1 ) _;
    norm_num [ zpow_neg, zpow_ofNat ];
    field_simp;
    nlinarith [ sq_mul_log_two_div_le_one hκ hκ2, one_le_log_two_div hκ hκ2 ];
  · refine' le_trans ( hAux κ hκ hκ2 |>.2 ) _;
    norm_num [ zpow_neg, zpow_ofNat ];
    field_simp;
    nlinarith [ sq_mul_log_two_div_le_one hκ hκ2, one_le_log_two_div hκ hκ2 ]

end LamplighterStability.Dynamics