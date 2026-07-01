import RequestProject.Dynamics.MinPeriod

/-!
# Restriction stability of the minimal period (`lem:per_ext_properties` item (iii))

This file proves item (iii) of `lem:per_ext_properties`: if `r ≥ 2t`, the
configuration `y` has minimal period `per(y) ≤ t` (at window radius `r`), and
`x = y^{2t}` is its restriction to the window `F_{2t}`, then

* `per(x) = per(y)` (`patPeriod_restrict`), and
* the minimal periodic extension of `x` recovers `y` on the window `F_r`
  (`cfgExt_restrict_proj`).

The core combinatorial ingredient is `winPerEq_reduce`: a window comparison that
holds on the small window `F_{2t}` and is compatible with the genuine
`p`-periodicity of `y` on `F_r` propagates to the full window `F_r`.  This is
proved Fine–Wilf-free by reducing each large-window index modulo `p` into the
small window (using the period-`p` shift invariance `cfg_eq_of_add_mul`).
-/

namespace LamplighterStability.Dynamics

open scoped BigOperators
open scoped Classical

/-
**Period-`j` shift invariance on the window.**  If `WinPerEq r y j` holds
(`y` is `j`-periodic on `F_r`), then shifting an index `a ∈ F_r` up by any
multiple `n·j` that stays in `F_r` does not change the value.
-/
lemma cfg_eq_of_add_mul {r : ℕ} {y : Cfg} {j : ℕ} (hj : 1 ≤ j)
    (hper : WinPerEq r y (j : ℤ)) (a : ℤ) (n : ℕ)
    (h1 : -(r : ℤ) ≤ a) (h2 : a + (j : ℤ) * n ≤ r) :
    y (a + (j : ℤ) * n) = y a := by
  induction n <;> simp_all +decide [ mul_add, ← add_assoc ];
  rename_i n ih; specialize ih ( by linarith ) ; specialize hper ( a + j * n + j ) ; simp_all +decide [ add_assoc ] ;
  grind

/-
**Congruent indices carry equal values.**  Under `WinPerEq r y j`, any two
indices `a, b ∈ F_r` that are congruent modulo `j` have `y a = y b`.
-/
lemma cfg_eq_of_congr {r : ℕ} {y : Cfg} {j : ℕ} (hj : 1 ≤ j)
    (hper : WinPerEq r y (j : ℤ)) {a b : ℤ}
    (ha1 : -(r : ℤ) ≤ a) (ha2 : a ≤ r) (hb1 : -(r : ℤ) ≤ b) (hb2 : b ≤ r)
    (hcong : a % (j : ℤ) = b % (j : ℤ)) : y a = y b := by
  by_cases h_cases : a ≤ b;
  · convert cfg_eq_of_add_mul hj hper a ( Int.toNat ( ( b - a ) / ( j : ℤ ) ) ) ha1 _ |> Eq.symm using 1;
    · rw [ Int.toNat_of_nonneg ( Int.ediv_nonneg ( by linarith ) ( by positivity ) ), Int.mul_ediv_cancel' ( Int.dvd_of_emod_eq_zero ( by rw [ Int.sub_emod, hcong ] ; norm_num ) ) ] ; ring;
    · rw [ Int.toNat_of_nonneg ( Int.ediv_nonneg ( sub_nonneg.mpr h_cases ) ( by positivity ) ) ] ; linarith [ Int.ediv_mul_cancel ( show ( j : ℤ ) ∣ b - a from Int.dvd_of_emod_eq_zero ( by rw [ Int.sub_emod, hcong ] ; norm_num ) ) ];
  · -- Since $a > b$, we can write $a = b + k * j$ for some integer $k$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, a = b + k * j := by
      exact ⟨ Int.toNat ( ( a - b ) / j ), by nlinarith [ Int.toNat_of_nonneg ( Int.ediv_nonneg ( sub_nonneg.mpr ( le_of_not_ge h_cases ) ) ( Nat.cast_nonneg j ) ), Int.ediv_mul_cancel ( show ( j : ℤ ) ∣ a - b from Int.dvd_of_emod_eq_zero ( by rw [ Int.sub_emod, hcong ] ; norm_num ) ) ] ⟩;
    grind +suggestions

/-
**Core reduction (`lem:per_ext_properties` (iii), engine).**  If `y` is
genuinely `p`-periodic on `F_r` (`p ≤ t`, `2t ≤ r`) and a window comparison
`WinPerEq (2t) y q` holds on the small window for some `1 ≤ q ≤ p`, then the same
window comparison holds on the full window `F_r`.
-/
lemma winPerEq_reduce {t r : ℕ} (hr : 2 * t ≤ r) {y : Cfg} {p q : ℕ}
    (hp : p ≤ t) (hpper : WinPerEq r y (p : ℤ)) (hq1 : 1 ≤ q) (hqp : q ≤ p)
    (hsmall : WinPerEq (2 * t) y (q : ℤ)) : WinPerEq r y (q : ℤ) := by
  intro k hk1 hk2;
  -- Pick the representative `k' := -(2*t:ℤ) + q + ((k - (-(2*t:ℤ) + q)) % (p:ℤ))`.
  set k' : ℤ := -(2 * t : ℤ) + q + ((k - (-(2 * t : ℤ) + q)) % (p : ℤ)) with hk';
  -- By `cfg_eq_of_congr`, we have `y k = y k'` and `y (k - q) = y (k' - q)`.
  have h_congr : y k = y k' ∧ y (k - q) = y (k' - q) := by
    apply And.intro;
    · apply cfg_eq_of_congr (by linarith) hpper;
      · linarith;
      · linarith;
      · linarith [ Int.emod_nonneg ( k - ( - ( 2 * t ) + q ) ) ( by norm_cast; linarith : ( p : ℤ ) ≠ 0 ) ];
      · linarith [ Int.emod_lt_of_pos ( k - ( - ( 2 * t ) + q ) ) ( by linarith : 0 < ( p : ℤ ) ) ];
      · simp +zetaDelta at *;
    · apply cfg_eq_of_congr (by linarith) hpper;
      · linarith;
      · grind;
      · linarith [ Int.emod_nonneg ( k - ( - ( 2 * t ) + q ) ) ( by linarith : ( p : ℤ ) ≠ 0 ) ];
      · linarith [ Int.emod_lt_of_pos ( k - ( - ( 2 * t ) + q ) ) ( by linarith : 0 < ( p : ℤ ) ) ];
      · simp +decide [ hk', Int.add_emod, Int.sub_emod ];
        simp +decide;
  convert hsmall k' _ _ using 1;
  · exact h_congr.1;
  · grind;
  · exact le_add_of_nonneg_right ( Int.emod_nonneg _ ( by linarith ) );
  · linarith [ Int.emod_lt_of_pos ( k - ( - ( 2 * t ) + q ) ) ( by linarith : 0 < ( p : ℤ ) ) ]

/-
**`lem:per_ext_properties` item (iii), period part.**  For `2t ≤ r` and
`per(y) ≤ t`, the minimal period of the restriction `y^{2t}` equals that of `y`.
-/
lemma patPeriod_restrict {t r : ℕ} (hr : 2 * t ≤ r) {y : Cfg}
    (hy : patPeriod r y ≤ t) :
    patPeriod (2 * t) y = patPeriod r y := by
  refine' le_antisymm ( Finset.min'_le _ _ _ ) _;
  · simp_all +decide [ periodCandidates ];
    refine' ⟨ ⟨ patPeriod_pos r y, by linarith ⟩, _ ⟩;
    intro k hk₁ hk₂;
    convert winPerEq_patPeriod r y k _ _ using 1; all_goals grind;
  · refine' Nat.le_of_not_lt fun h => _;
    have := winPerEq_reduce hr ( hp := hy ) ( hpper := winPerEq_patPeriod r y ) ( hq1 := patPeriod_pos ( 2 * t ) y ) ( hqp := h.le ) ( hsmall := winPerEq_patPeriod ( 2 * t ) y ) ; exact patPeriod_min r y ( patPeriod_pos ( 2 * t ) y ) h this;

/-
**`lem:per_ext_properties` item (iii), extension part.**  For `2t ≤ r` and
`per(y) ≤ t`, the minimal periodic extension of the restriction `y^{2t}` agrees
with `y` on the full window `F_r`.
-/
lemma cfgExt_restrict_proj {t r : ℕ} (hr : 2 * t ≤ r) {y : Cfg}
    (hy : patPeriod r y ≤ t) :
    proj r (cfgExt (2 * t) y) = proj r y := by
  -- By definition of `patPeriod_restrict`, we know that `patPeriod (2 * t) y = patPeriod r y`.
  have h_patPeriod : patPeriod (2 * t) y = patPeriod r y := by
    exact patPeriod_restrict hr hy;
  ext ⟨ i, hi ⟩ ; simp_all +decide [ proj ] ;
  convert cfg_eq_of_congr ( show 1 ≤ patPeriod r y from patPeriod_pos r y ) ( show WinPerEq r y ( patPeriod r y : ℤ ) from winPerEq_patPeriod r y ) _ _ _ _ _ using 1 <;> norm_num at *;
  · linarith [ Int.emod_nonneg ( i + 2 * t ) ( show ( patPeriod ( 2 * t ) y : ℤ ) ≠ 0 from mod_cast ne_of_gt ( patPeriod_pos _ _ ) ) ];
  · exact le_trans ( Int.emod_lt_of_pos _ ( by linarith [ patPeriod_pos ( 2 * t ) y ] ) |> le_of_lt ) ( by linarith [ patPeriod_pos ( 2 * t ) y ] );
  · grind;
  · linarith;
  · simp +decide [ ← h_patPeriod ]

end LamplighterStability.Dynamics