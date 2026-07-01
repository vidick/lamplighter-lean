import RequestProject.Dynamics.MinPeriodOrbit

/-!
# The cylinder partition of the periodic part (`lem:covering_per_seq` backbone)

This file develops the *measure-free, set-theoretic backbone* of the
periodic-covering lemma (`lem:covering_per_seq`, Section 6.1).  Building on the
minimal-period machinery, it establishes:

* `mem_Xperl_iff_patPeriod` : the clean reformulation of the approximately
  periodic part, `x ∈ X_per^ℓ(t) ↔ per_ℓ(x) ≤ t` (Remark `rem:min_per`);

* `patPeriod_restrict_gen` / `cfgExt_restrict_proj_gen` : the *general inner
  radius* form of item (iii) of `lem:per_ext_properties`.  The existing lemmas
  (`patPeriod_restrict`, `cfgExt_restrict_proj`) are hard-coded to inner radius
  `2t`; the covering construction applies the minimal periodic extension at
  inner radius `3t`, so these generalizations (valid for any `2t ≤ s ≤ r`) are
  what let one identify a periodic sequence with the extension of its
  `F_{3t}`-window pattern;

* `Xperl_eq_iUnion_extCyl` and `extCyl_pairwise_disjoint` : the resulting
  decomposition of `X_per^ℓ(t)` (for `ℓ ≥ 3t`) into the *disjoint* family of
  extension cylinders `{ x^ℓ : per_{3t}(x) ≤ t }` indexed by `F_{3t}`-window
  patterns.  This is exactly the family that the inductive tower-construction of
  `lem:covering_per_seq` groups into orbits and refines into towers / error
  pieces.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators
open scoped Classical

/-
**`X_per^ℓ(t)` as a sublevel set of the minimal period** (Remark
`rem:min_per`).  A configuration lies in the approximately periodic part iff its
`F_ℓ`-window pattern has minimal period at most `t`.
-/
lemma mem_Xperl_iff_patPeriod {t ℓ : ℕ} (x : Cfg) :
    x ∈ Xperl t ℓ ↔ patPeriod ℓ x ≤ t := by
  constructor;
  · intro hx;
    contrapose! hx;
    exact Set.notMem_compl_iff.mpr ( fIndep_cyl_iff_winPerEq _ _ _ |>.2 fun i hi₁ hi₂ => patPeriod_min _ _ hi₁ ( by linarith ) );
  · intro h;
    exact fun hx => by have := fIndep_cyl_iff_winPerEq ℓ t x |>.1 hx ( patPeriod ℓ x ) ( patPeriod_pos ℓ x ) h; exact this ( winPerEq_patPeriod ℓ x ) ;

/-
**Window comparison passes to a smaller window.**  If `WinPerEq r y j` holds
and `s ≤ r`, then `WinPerEq s y j` holds (the comparison range shrinks).
-/
lemma winPerEq_mono {s r : ℕ} (hsr : s ≤ r) {y : Cfg} {j : ℤ}
    (h : WinPerEq r y j) : WinPerEq s y j := by
  intro k hk₁ hk₂; exact h k (by linarith) (by linarith);

/-
**General inner-radius window reduction** (`lem:per_ext_properties` (iii),
engine).  If `y` is genuinely `p`-periodic on `F_r` (`p ≤ t`, `2t ≤ s ≤ r`) and a
window comparison `WinPerEq s y q` holds on the inner window for some
`1 ≤ q ≤ p`, then the same window comparison holds on the full window `F_r`.
-/
lemma winPerEq_reduce_gen {t s r : ℕ} (hst : 2 * t ≤ s) (hsr : s ≤ r) {y : Cfg}
    {p q : ℕ} (hp : p ≤ t) (hpper : WinPerEq r y (p : ℤ)) (hq1 : 1 ≤ q)
    (hqp : q ≤ p) (hsmall : WinPerEq s y (q : ℤ)) : WinPerEq r y (q : ℤ) := by
  -- Set the representative `k' := -(s:ℤ) + q + ((k - (-(s:ℤ)+q)) % (p:ℤ))` so that `k' ∈ [-s+q, s]` (using `1 ≤ p` from `hq1 ≤ hqp` chain and `q ≤ p`), then apply `hsmall k'`.
  intro k hk1 hk2
  set k' : ℤ := -(s : ℤ) + q + ((k - (-(s : ℤ) + q)) % (p : ℤ)) with hk';
  have h_congr : y k = y k' ∧ y (k - q) = y (k' - q) := by
    apply And.intro;
    · apply cfg_eq_of_congr (by linarith) hpper;
      · linarith;
      · linarith;
      · linarith [ Int.emod_nonneg ( k - ( -s + q ) ) ( by linarith : ( p : ℤ ) ≠ 0 ) ];
      · linarith [ Int.emod_lt_of_pos ( k - ( -s + q ) ) ( by linarith : 0 < ( p : ℤ ) ) ];
      · simp +zetaDelta at *;
    · apply cfg_eq_of_congr (by linarith) hpper;
      · linarith;
      · linarith;
      · linarith [ Int.emod_nonneg ( k - ( -s + q ) ) ( by linarith : ( p : ℤ ) ≠ 0 ) ];
      · linarith [ Int.emod_lt_of_pos ( k - ( -s + q ) ) ( by linarith : 0 < ( p : ℤ ) ) ];
      · simp +decide [ hk', Int.add_emod, Int.sub_emod ];
        simp +decide [];
  have := hsmall k' ?_ ?_ <;> simp_all +decide;
  · exact Int.emod_nonneg _ ( by linarith );
  · linarith [ Int.emod_lt_of_pos ( k - ( -s + q ) ) ( by linarith : 0 < ( p : ℤ ) ) ]

/-
**General inner-radius restriction of the minimal period**
(`lem:per_ext_properties` (iii), period part).  For `2t ≤ s ≤ r` and
`per_r(y) ≤ t`, the minimal period at the inner window `F_s` equals that at the
outer window `F_r`.
-/
lemma patPeriod_restrict_gen {t s r : ℕ} (hst : 2 * t ≤ s) (hsr : s ≤ r) {y : Cfg}
    (hy : patPeriod r y ≤ t) : patPeriod s y = patPeriod r y := by
  have h_period_eq : patPeriod s y ≤ patPeriod r y := by
    refine' Finset.min'_le _ _ _;
    exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ patPeriod_pos r y ], by linarith [ patPeriod_le r y ] ⟩, winPerEq_mono ( by linarith ) ( winPerEq_patPeriod r y ) ⟩;
  refine' le_antisymm h_period_eq ( le_of_not_gt fun h => _ );
  exact patPeriod_min r y ( by linarith [ patPeriod_pos s y ] ) h ( winPerEq_reduce_gen hst hsr ( by linarith ) ( winPerEq_patPeriod r y ) ( patPeriod_pos s y ) ( by linarith ) ( winPerEq_patPeriod s y ) )

/-
**General inner-radius restriction of the minimal periodic extension**
(`lem:per_ext_properties` (iii), extension part).  For `2t ≤ s ≤ r` and
`per_r(y) ≤ t`, the minimal periodic extension of the inner window pattern agrees
with `y` on the full window `F_r`.
-/
lemma cfgExt_restrict_proj_gen {t s r : ℕ} (hst : 2 * t ≤ s) (hsr : s ≤ r)
    {y : Cfg} (hy : patPeriod r y ≤ t) : proj r (cfgExt s y) = proj r y := by
  ext ⟨ i, hi ⟩;
  simp +decide [ proj ] at hi ⊢;
  convert cfg_eq_of_congr ( patPeriod_pos r y ) ( winPerEq_patPeriod r y ) _ _ _ _ _ using 1 <;> norm_num at *;
  · linarith [ Int.emod_nonneg ( i + s ) ( show ( patPeriod s y : ℤ ) ≠ 0 from mod_cast ne_of_gt ( patPeriod_pos s y ) ) ];
  · rw [ patPeriod_restrict_gen hst hsr hy ];
    exact le_trans ( Int.le_of_lt ( Int.emod_lt_of_pos _ ( by linarith [ patPeriod_pos r y ] ) ) ) ( by linarith );
  · grind;
  · linarith;
  · rw [ patPeriod_restrict_gen hst hsr hy ];
    simp +decide

/-
A periodic sequence lies in the extension cylinder of its own `F_{3t}`-window
pattern: for `3t ≤ ℓ`, if `per_ℓ(y) ≤ t` then `y ∈ y^ℓ` (the extension cylinder
at inner radius `3t`).
-/
lemma mem_extCyl_self {t ℓ : ℕ} (hℓ : 3 * t ≤ ℓ) {y : Cfg}
    (hy : patPeriod ℓ y ≤ t) : y ∈ extCyl (3 * t) y ℓ := by
  have := @cfgExt_restrict_proj_gen t ( 3 * t ) ℓ ?_ ?_ ?_ ?_ <;> norm_num at *;
  convert this.symm using 1;
  · grind;
  · grind;
  · grind +qlia

/-
**The cylinder backbone of `lem:covering_per_seq`.**  For `ℓ ≥ 3t`, the
approximately periodic part `X_per^ℓ(t)` is the union of the extension cylinders
`x^ℓ` ranging over configurations `x` whose `F_{3t}`-window pattern has minimal
period at most `t`.
-/
lemma Xperl_eq_iUnion_extCyl {t ℓ : ℕ} (hℓ : 3 * t ≤ ℓ) :
    Xperl t ℓ = ⋃ (x : Cfg) (_ : patPeriod (3 * t) x ≤ t), extCyl (3 * t) x ℓ := by
  apply Set.eq_of_subset_of_subset;
  · intro x hx; simp_all +decide ;
    exact ⟨ x, by
      have h_patPeriod_le_t : patPeriod ℓ x ≤ t := by
        exact mem_Xperl_iff_patPeriod x |>.1 hx;
      rw [ patPeriod_restrict_gen ( by linarith ) ( by linarith ) h_patPeriod_le_t ] ; linarith, by
      apply mem_extCyl_self hℓ;
      exact mem_Xperl_iff_patPeriod x |>.1 hx ⟩;
  · exact Set.iUnion_subset fun x => Set.iUnion_subset fun hx => extCyl_subset_Xperl hx

/-
**Disjointness of the cylinder backbone.**  Two extension cylinders at inner
radius `3t` whose `F_{3t}`-window patterns differ are disjoint (each is contained
in the cylinder of its window pattern).
-/
lemma extCyl_pairwise_disjoint {r : ℕ} {x y : Cfg} {ℓ : ℕ} (hr : r ≤ ℓ)
    (h : proj r x ≠ proj r y) : Disjoint (extCyl r x ℓ) (extCyl r y ℓ) := by
  -- Both `extCyl r x ℓ` and `extCyl r y ℓ` are contained in `cyl r (proj r (cfgExt))`.
  -- Since `proj r x ≠ proj r y`, their windows differ on `F_r`, so the base cylinders `cyl r (proj r x)` and `cyl r (proj r y)` are disjoint.
  have h_subset : extCyl r x ℓ ⊆ cyl r (proj r x) ∧ extCyl r y ℓ ⊆ cyl r (proj r y) := by
    exact ⟨ fun z hz => by simpa using extCyl_mono hr hz, fun z hz => by simpa using extCyl_mono hr hz ⟩;
  exact Set.disjoint_left.mpr fun z hz₁ hz₂ => Set.disjoint_left.mp ( cyl_disjoint h ) ( h_subset.1 hz₁ ) ( h_subset.2 hz₂ )

end LamplighterStability.Dynamics