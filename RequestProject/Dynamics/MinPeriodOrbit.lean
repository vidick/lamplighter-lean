import RequestProject.Dynamics.MinPeriodCovering
import RequestProject.Dynamics.MinPeriodRestrict

/-!
# Orbit/window combinatorics for `lem:covering_per_seq` (disjointness engine)

This file proves the self-contained combinatorial lemmas that drive the
*disjointness* part of the periodic-covering lemma (`lem:covering_per_seq`,
Section 6.1 of the paper).  They build on the minimal-period machinery
(`MinPeriod.lean`, `MinPeriodRestrict.lean`) and the extension-cylinder API
(`MinPeriodCovering.lean`).

The two ingredients the covering construction needs are:

* **Window pinning** (`proj_zpow_eq_of_proj_eq`): two configurations agreeing on
  a window `F_ℓ` still agree, *after a shift by `i`*, on any smaller window
  `F_s` as long as `s + |i| ≤ ℓ`.  This is what lets a tower floor `L^i b`
  (with base a `ℓ`-window cylinder, `ℓ ≥ 3t`, and `|i| ≤ t`) have a
  well-defined `F_{2t}`-projection.

* **Orbit collision** (`orbit_collision`): if two configurations of minimal
  period `≤ t` (at window radius `3t`) agree on the small window `F_{2t}`, then
  they agree on the full window `F_{3t}`.  This is exactly item (iii) of
  `lem:per_ext_properties` packaged for the covering argument: two tower floors
  that meet must come from the *same* periodic orbit.

Together these reduce all the cross-tower / tower-error disjointness checks in
`lem:covering_per_seq` to the elementary statement that distinct `F_{3t}`-window
patterns have disjoint cylinders.
-/

namespace LamplighterStability.Dynamics

open scoped BigOperators
open scoped Classical

/-
**Window pinning under a shift.**  If `w` and `g` agree on the window `F_ℓ`,
then their `i`-shifts agree on any window `F_s` with `(s : ℤ) + |i| ≤ ℓ`.
-/
lemma proj_zpow_eq_of_proj_eq {w g : Cfg} {s ℓ : ℕ} {i : ℤ}
    (h : proj ℓ w = proj ℓ g) (hsi : (s : ℤ) + |i| ≤ (ℓ : ℤ)) :
    proj s ((L ^ i) w) = proj s ((L ^ i) g) := by
  ext ⟨ k, hk ⟩;
  simp_all +decide [ proj, L_zpow_apply ];
  replace h := congr_fun h ⟨ k - i, by
    grind +qlia ⟩ ; aesop;

/-
`cfgExt r ·` depends only on the window `proj r`.
-/
lemma cfgExt_congr {r : ℕ} {x y : Cfg} (h : proj r x = proj r y) :
    cfgExt r x = cfgExt r y := by
  ext i;
  convert congrFun h ⟨ -r + ( i + r ) % ( patPeriod r x : ℤ ), ?_ ⟩ using 1;
  all_goals norm_num [ cfgExt, proj ];
  · rw [ patPeriod_congr h ];
  · exact ⟨ Int.emod_nonneg _ ( by norm_cast; linarith [ patPeriod_pos r x ] ), by linarith [ Int.emod_lt_of_pos ( i + r ) ( by norm_cast; linarith [ patPeriod_pos r x ] : 0 < ( patPeriod r x : ℤ ) ), show ( patPeriod r x : ℤ ) ≤ 2 * r + 1 from mod_cast patPeriod_le r x ] ⟩

/-
A globally `p`-periodic configuration satisfies the window comparison
`WinPerEq r · p` for every radius `r`.
-/
lemma winPerEq_of_periodic {r : ℕ} {f : Cfg} {p : ℕ}
    (hper : ∀ j : ℤ, f (j + (p : ℤ)) = f j) :
    WinPerEq r f (p : ℤ) := by
  intro k hk₁ hk₂; have := hper ( k - p ) ; ring_nf at *; aesop;

/-
If `f` is globally `p`-periodic with `1 ≤ p ≤ 2r+1`, its minimal window
period at radius `r` is at most `p`.
-/
lemma patPeriod_le_of_periodic {r : ℕ} {f : Cfg} {p : ℕ}
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * r + 1)
    (hper : ∀ j : ℤ, f (j + (p : ℤ)) = f j) :
    patPeriod r f ≤ p := by
  apply Finset.min'_le;
  exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp1, hp2 ⟩, winPerEq_of_periodic hper ⟩

/-
The minimal periodic extension `cfgExt r x` has window period (at the same
radius `r`) at most `patPeriod r x`: it is genuinely `patPeriod r x`-periodic.
-/
lemma patPeriod_cfgExt_le (r : ℕ) (x : Cfg) :
    patPeriod r (cfgExt r x) ≤ patPeriod r x := by
  convert patPeriod_le_of_periodic ( patPeriod_pos r x ) ( patPeriod_le r x ) ( cfgExt_periodic r x ) using 1

/-
A shift of the minimal periodic extension is still `patPeriod r x`-periodic,
hence has window period at most `patPeriod r x`.
-/
lemma patPeriod_zpow_cfgExt_le (r : ℕ) (x : Cfg) (i : ℤ) :
    patPeriod r ((L ^ i) (cfgExt r x)) ≤ patPeriod r x := by
  refine' patPeriod_le_of_periodic (patPeriod_pos r x) (patPeriod_le r x) ?_;
  · simp +decide [ L_zpow_apply ];
    intro j; convert cfgExt_periodic r x ( j - i ) using 1 ; ring;

/-
**Orbit collision (item (iii), packaged).**  Two configurations of minimal
period `≤ t` at radius `3t` that agree on the small window `F_{2t}` agree on the
full window `F_{3t}`.
-/
lemma orbit_collision {t : ℕ} {y₁ y₂ : Cfg}
    (h₁ : patPeriod (3 * t) y₁ ≤ t) (h₂ : patPeriod (3 * t) y₂ ≤ t)
    (h : proj (2 * t) y₁ = proj (2 * t) y₂) :
    proj (3 * t) y₁ = proj (3 * t) y₂ := by
  rw [ ← cfgExt_restrict_proj ( by omega ) h₁, ← cfgExt_restrict_proj ( by omega ) h₂ ];
  rw [ cfgExt_congr h ]

/-
**Extension cylinders land in the periodic part.**  If the window pattern of
`x` at radius `3t` has minimal period `≤ t`, then every extension cylinder
`extCyl (3*t) x ℓ` is contained in `X_per^ℓ(t)`.  This is what
makes the error/base pieces of the covering genuinely subsets of the set being
covered.
-/
lemma extCyl_subset_Xperl {t : ℕ} {x : Cfg} {ℓ : ℕ}
    (hper : patPeriod (3 * t) x ≤ t) :
    extCyl (3 * t) x ℓ ⊆ Xperl t ℓ := by
  intro z hz;
  simp_all +decide [ Xperl, Xaperl ];
  -- By definition of `extCyl`, we know that `proj ℓ z = proj ℓ (cfgExt (3 * t) x)`.
  have h_proj_eq : proj ℓ z = proj ℓ (cfgExt (3 * t) x) := by
    grind +suggestions;
  rw [ h_proj_eq, fIndep_cyl_iff_winPerEq ];
  push_neg;
  use patPeriod (3 * t) x;
  exact ⟨ patPeriod_pos _ _, hper, winPerEq_of_periodic ( cfgExt_periodic _ _ ) ⟩

end LamplighterStability.Dynamics