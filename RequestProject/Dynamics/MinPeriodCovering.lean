import RequestProject.Dynamics.MinPeriodCyl
import RequestProject.Dynamics.MinPeriodRestrict

/-!
# The extension/restriction operator and the geometric-decay core of `lem:covering_per_seq`

This file develops the structural ingredients of `lem:covering_per_seq`
(Section 6.1 of the paper), building on the minimal-period machinery of
`MinPeriod.lean`, `MinPeriodCyl.lean`, and `MinPeriodRestrict.lean`.

* `extCyl r x ℓ` is the cylinder of the extension/restriction `x^ℓ`: the
  `ℓ`-window cylinder of the minimal periodic extension `cfgExt r x`.  For
  `ℓ ≤ r` it is the genuine restriction cylinder `⟦π_ℓ(x)⟧`, and for `ℓ ≥ r` it
  is a shrinking family of subcylinders of `⟦π_r(x)⟧`.

* `extCyl_mono`, `extCyl_eq_cyl_of_le`, `extCyl_self`: basic window monotonicity
  and the identification with restriction cylinders.

* `FIndep.subset`: `F_j`-independence passes to subsets.

* `extCyl_fIndep`: every `x^ℓ`-cylinder (`ℓ ≥ r`) is `F_{per(x)-1}`-independent
  (item (i) of `lem:per_ext_properties`, transported along the inclusion).

* `not_fIndep_cyl_patPeriod`: maximality half of item (i) — `⟦π_r(x)⟧` is *not*
  `F_{per(x)}`-independent.

* `extCyl_shift_incl`: the key periodicity inclusion
  `⟦x^{k+per}⟧ ⊆ (L^{per} ⟦x^k⟧) ∩ ⟦x^k⟧` driving the geometric decay of the
  cylinder measures in Claim 6.2.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators
open scoped Classical

/-- The cylinder of the extension/restriction `x^ℓ`: the `ℓ`-window cylinder of
the minimal periodic extension `cfgExt r x`. -/
def extCyl (r : ℕ) (x : Cfg) (ℓ : ℕ) : Set Cfg := cyl ℓ (proj ℓ (cfgExt r x))

lemma mem_extCyl {r : ℕ} {x : Cfg} {ℓ : ℕ} {z : Cfg} :
    z ∈ extCyl r x ℓ ↔ proj ℓ z = proj ℓ (cfgExt r x) := Iff.rfl

/-- Window monotonicity: enlarging the window shrinks the cylinder. -/
lemma extCyl_mono {r : ℕ} {x : Cfg} {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') :
    extCyl r x ℓ' ⊆ extCyl r x ℓ := by
  intro z hz
  exact proj_mono h hz

/-- For `ℓ ≤ r`, the extension/restriction cylinder is the genuine restriction
cylinder `⟦π_ℓ(x)⟧`. -/
lemma extCyl_eq_cyl_of_le {r : ℕ} {x : Cfg} {ℓ : ℕ} (h : ℓ ≤ r) :
    extCyl r x ℓ = cyl ℓ (proj ℓ x) := by
  unfold extCyl
  congr 1
  ext ⟨i, hi⟩
  simp only [proj]
  rw [cfgExt_eq_on_window r x]
  · exact (Finset.mem_Icc.mp hi).1.trans' (by exact_mod_cast neg_le_neg (by exact_mod_cast h))
  · exact (Finset.mem_Icc.mp hi).2.trans (by exact_mod_cast h)

@[simp] lemma extCyl_self {r : ℕ} {x : Cfg} :
    extCyl r x r = cyl r (proj r x) := extCyl_eq_cyl_of_le le_rfl

/-- `F_j`-independence passes to subsets. -/
lemma FIndep.subset {j : ℕ} {b b' : Set Cfg} (hsub : b' ⊆ b) (h : FIndep j b) :
    FIndep j b' := by
  intro i hi hi0
  exact (h i hi hi0).mono hsub (Set.image_mono hsub)

/-- **Item (i), transported.**  Every `x^ℓ`-cylinder (`ℓ ≥ r`) is
`F_{per(x)-1}`-independent. -/
lemma extCyl_fIndep {r : ℕ} {x : Cfg} {ℓ : ℕ} (h : r ≤ ℓ) :
    FIndep (patPeriod r x - 1) (extCyl r x ℓ) := by
  have hsub : extCyl r x ℓ ⊆ cyl r (proj r x) := by
    have := extCyl_mono (r := r) (x := x) h
    rwa [extCyl_self] at this
  exact (fIndep_cyl_patPeriod_sub_one r x).subset hsub

/-- **Item (i), maximality half.**  `⟦π_r(x)⟧` is *not* `F_{per(x)}`-independent. -/
lemma not_fIndep_cyl_patPeriod (r : ℕ) (x : Cfg) :
    ¬ FIndep (patPeriod r x) (cyl r (proj r x)) := by
  rw [fIndep_cyl_iff_winPerEq]
  intro h
  exact h (patPeriod r x) (patPeriod_pos r x) le_rfl (winPerEq_patPeriod r x)

/-- **Key periodicity inclusion (Claim 6.2 engine).**  For `k ≥ r`,
`⟦x^{k+per}⟧ ⊆ (L^{per} ⟦x^k⟧) ∩ ⟦x^k⟧`. -/
lemma extCyl_shift_incl {r : ℕ} {x : Cfg} {k : ℕ} :
    extCyl r x (k + patPeriod r x) ⊆
      (L ^ (patPeriod r x : ℤ)) '' (extCyl r x k) ∩ extCyl r x k := by
  set p := patPeriod r x with hp
  intro z hz
  -- `z` agrees with `cfgExt r x` on the window `F_{k+p}`.
  have hzeq : ∀ j : ℤ, -((k + p : ℕ) : ℤ) ≤ j → j ≤ ((k + p : ℕ) : ℤ) →
      z j = cfgExt r x j := by
    intro j hj1 hj2
    have := congrFun hz ⟨j, Finset.mem_Icc.mpr ⟨hj1, hj2⟩⟩
    simpa [proj] using this
  have hppos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast patPeriod_pos r x
  refine ⟨?_, extCyl_mono (Nat.le_add_right _ _) hz⟩
  -- `z = L^p (L^{-p} z)` and `L^{-p} z ∈ ⟦x^k⟧`.
  refine ⟨(L ^ (-(p : ℤ))) z, ?_, ?_⟩
  · -- membership of `L^{-p} z` in `extCyl r x k`
    funext i
    obtain ⟨i, hi⟩ := i
    have hib : -(k : ℤ) ≤ i ∧ i ≤ (k : ℤ) := Finset.mem_Icc.mp hi
    simp only [proj]
    -- `(L^{-p} z) i = z (i+p)`
    have hval : ((L ^ (-(p : ℤ))) z) i = z (i + p) := by
      rw [L_zpow_apply]; ring_nf
    rw [hval, hzeq (i + p) (by push_cast; nlinarith [hib.1]) (by push_cast; nlinarith [hib.2]),
      show (i + (p : ℤ)) = i + (p : ℤ) from rfl]
    -- `cfgExt r x (i+p) = cfgExt r x i`
    have := cfgExt_periodic r x i
    rw [hp]
    exact this
  · -- `z = L^p (L^{-p} z)`
    rw [← Equiv.Perm.mul_apply, ← zpow_add]
    simp

/-! ## The geometric decay of cylinder measures (Claim 6.2) -/

/-- Measure-monotone form of `extCyl_shift_incl`. -/
lemma extCyl_inter_measure_le {r : ℕ} {x : Cfg} {k : ℕ} (μ : Measure Cfg) :
    μ (extCyl r x (k + patPeriod r x)) ≤
      μ ((L ^ (patPeriod r x : ℤ)) '' (extCyl r x k) ∩ extCyl r x k) :=
  measure_mono extCyl_shift_incl

/-
**Geometric decay (Claim 6.2, first case engine).**  If, at every stage
`i < N`, the `per`-shift overlap of the cylinder `⟦x^{r+i·per}⟧` is strictly
below `(1-δ)` times its measure, then the measure of `⟦x^{r+N·per}⟧` has decayed
by a factor `(1-δ)^N`.
-/
lemma extCyl_geom_decay {r : ℕ} {x : Cfg} {δ : ℝ} (hδ1 : δ ≤ 1)
    (μ : Measure Cfg) [IsProbabilityMeasure μ] (N : ℕ)
    (hdec : ∀ i < N,
      (μ ((L ^ (patPeriod r x : ℤ)) '' (extCyl r x (r + i * patPeriod r x))
            ∩ extCyl r x (r + i * patPeriod r x))).toReal
        < (1 - δ) * (μ (extCyl r x (r + i * patPeriod r x))).toReal) :
    (μ (extCyl r x (r + N * patPeriod r x))).toReal
      ≤ (1 - δ) ^ N * (μ (cyl r (proj r x))).toReal := by
  induction' N with N ih;
  · simp +decide [ extCyl_self ];
  · convert le_trans _ ( mul_le_mul_of_nonneg_left ( ih fun i hi => hdec i ( Nat.lt_succ_of_lt hi ) ) ( sub_nonneg.mpr hδ1 ) ) using 1;
    · ring;
    · convert le_trans ( ENNReal.toReal_mono _ ( extCyl_inter_measure_le μ ) ) ( le_of_lt ( hdec N ( Nat.lt_succ_self N ) ) ) using 1;
      · ring;
      · exact MeasureTheory.measure_ne_top _ _

/-
Elementary geometric bound: `(1-δ)^N ≤ υ` once `N ≥ log(1/υ)/δ`.
-/
lemma one_sub_pow_le_of_log_le {υ δ : ℝ} (hυ : 0 < υ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {N : ℕ} (hN : Real.log (1 / υ) / δ ≤ N) : (1 - δ) ^ N ≤ υ := by
  refine' le_trans ( pow_le_pow_left₀ _ _ _ ) _;
  exact Real.exp ( -δ );
  · linarith;
  · linarith [ Real.add_one_le_exp ( -δ ) ];
  · rw [ ← Real.exp_nat_mul ];
    rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_exp ];
    rw [ div_le_iff₀ ] at hN <;> norm_num at * <;> linarith

/-
**Claim 6.2** (`claim:62`).  There is a universal constant `C₂ > 0` such
that for every window radius `r ≥ 1`, every pattern (configuration) `x`, every
probability measure `μ`, and every `0 < υ, δ ≤ 1/2`, there is a window
`r ≤ ℓₓ ≤ C₂·r·log(1/υ)/δ` such that either the cylinder `⟦x^{ℓₓ}⟧` has measure
`≤ υ·μ(⟦π_r(x)⟧)` (error case), or it is `F_{per(x)-1}`-independent and the tower
`Tow(⟦x^{ℓₓ}⟧, per(x))` is `δ`-closed (tower case).
-/
theorem claim_62 :
    ∃ C2 : ℝ, 0 < C2 ∧
      ∀ (υ δ : ℝ), 0 < υ → υ ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
        ∀ (r : ℕ) (x : Cfg), 1 ≤ r →
          ∀ (μ : Measure Cfg) [IsProbabilityMeasure μ],
            ∃ ℓx : ℕ, r ≤ ℓx ∧ (ℓx : ℝ) ≤ C2 * r * Real.log (1 / υ) / δ ∧
              ((μ (extCyl r x ℓx)).toReal ≤ υ * (μ (cyl r (proj r x))).toReal ∨
                (FIndep (patPeriod r x - 1) (extCyl r x ℓx) ∧
                  DeltaClosed μ δ (patPeriod r x) (extCyl r x ℓx))) := by
  use 7; norm_num;
  intro υ δ hυ hυ2 hδ hδ2 r x hr μ _; by_cases h : ∀ i : ℕ, i < ⌈Real.log ( 1 / υ ) / δ⌉₊ → ( μ ( ( L ^ ( patPeriod r x : ℤ ) ) '' ( extCyl r x ( r + i * patPeriod r x ) ) ∩ extCyl r x ( r + i * patPeriod r x ) ) ).toReal < ( 1 - δ ) * ( μ ( extCyl r x ( r + i * patPeriod r x ) ) ).toReal;
  · refine' ⟨ r + Nat.ceil ( Real.log ( 1 / υ ) / δ ) * patPeriod r x, _, _, _ ⟩ <;> norm_num;
    · have h_bound : (r + Nat.ceil (Real.log (1 / υ) / δ) * patPeriod r x : ℝ) ≤ 7 * r * Real.log (1 / υ) / δ := by
        have hL : 1 ≤ Real.log (1 / υ) / δ := by
          rw [ le_div_iff₀ hδ ];
          norm_num +zetaDelta at *;
          linarith [ Real.log_le_sub_one_of_pos hυ, Real.log_le_sub_one_of_pos ( show 0 < 2 by norm_num ), Real.log_two_gt_d9, Real.log_le_log ( by positivity ) ( show υ ≤ 2 by linarith ) ]
        have h_bound : (patPeriod r x : ℝ) ≤ 3 * r := by
          exact_mod_cast le_trans ( patPeriod_le r x ) ( by linarith );
        rw [ mul_div_assoc ];
        nlinarith [ Nat.ceil_lt_add_one ( show 0 ≤ Real.log ( 1 / υ ) / δ by positivity ), show ( r : ℝ ) ≥ 1 by norm_cast ];
      aesop;
    · refine' Or.inl ( le_trans ( extCyl_geom_decay _ _ _ _ ) _ );
      exact δ;
      · grind +splitImp;
      · aesop;
      · gcongr;
        convert one_sub_pow_le_of_log_le _ _ _ _ using 1;
        · linarith;
        · linarith;
        · linarith;
        · norm_num [ Real.log_div, hυ.ne' ];
          exact Nat.le_ceil _;
  · obtain ⟨i, hiN, hge⟩ : ∃ i < Nat.ceil (Real.log (1 / υ) / δ), (1 - δ) * (μ (extCyl r x (r + i * patPeriod r x))).toReal ≤ (μ ((L ^ (patPeriod r x : ℤ)) '' (extCyl r x (r + i * patPeriod r x)) ∩ extCyl r x (r + i * patPeriod r x))).toReal := by
      grind;
    refine' ⟨ r + i * patPeriod r x, _, _, _ ⟩;
    · exact Nat.le_add_right _ _;
    · have h_bound : (r + i * patPeriod r x : ℝ) ≤ 7 * r * Real.log (1 / υ) / δ := by
        have hL : Real.log (1 / υ) / δ ≥ 1 := by
          rw [ ge_iff_le, le_div_iff₀ ] <;> norm_num at * <;> try linarith;
          linarith [ Real.log_le_sub_one_of_pos hυ ]
        have h_bound : (patPeriod r x : ℝ) ≤ 3 * r := by
          exact_mod_cast by linarith [ patPeriod_le r x ] ;
        have h_bound : (i : ℝ) ≤ Real.log (1 / υ) / δ := by
          exact le_of_lt ( Nat.lt_ceil.mp hiN );
        ring_nf at *; nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ r ) ] ;
      aesop;
    · exact Or.inr ⟨ extCyl_fIndep ( by nlinarith ), hge ⟩

end LamplighterStability.Dynamics