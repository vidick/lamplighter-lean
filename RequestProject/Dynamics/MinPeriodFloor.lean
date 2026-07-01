import RequestProject.Dynamics.MinPeriodOrbit

/-!
# Floor disjointness for `lem:covering_per_seq` (disjointness engine, part II)

This file supplies the *floor-collision* lemma that drives the disjointness part
of the periodic-covering lemma (`lem:covering_per_seq`, Section 6.1), building on
the orbit / window combinatorics of `MinPeriodOrbit.lean`.

The covering construction represents the approximately periodic part by towers
`Tow(base, per)` whose bases are extension cylinders `extCyl (3t) x ℓₓ`.  Two
tower floors `Lⁱ·base_x` and `Lⁱ'·base_y` can only intersect if the underlying
periodic patterns line up *after the relative shift* `m = i'-i`; this is exactly
`floor_collision` below.  Combined with `orbit_collision`, it reduces every
cross-tower / tower–error disjointness check to comparing `F_{3t}`-window
patterns.

Supporting facts:
* `proj_cfgExt_self` : `proj r (cfgExt r x) = proj r x`;
* `extCyl_defined` : an extension cylinder `extCyl r x ℓ` is `ℓ`-defined;
* `extCyl_subset_cyl` : for `r ≤ ℓ`, `extCyl r x ℓ ⊆ cyl r (proj r x)`.
-/

namespace LamplighterStability.Dynamics

open scoped BigOperators
open scoped Classical

/-
The minimal periodic extension agrees with `x` on the whole window `F_r`,
hence has the same `F_r`-projection.
-/
lemma proj_cfgExt_self (r : ℕ) (x : Cfg) : proj r (cfgExt r x) = proj r x := by
  ext ⟨ i, hi ⟩;
  convert cfgExt_eq_on_window r x ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hi |>.2 ) using 1

/-
An extension cylinder `extCyl r x ℓ` is `ℓ`-defined.
-/
lemma extCyl_defined (r : ℕ) (x : Cfg) (ℓ : ℕ) : Defined ℓ (extCyl r x ℓ) := by
  convert defined_cyl ℓ ( proj ℓ ( cfgExt r x ) ) using 1

/-
For `r ≤ ℓ` an extension cylinder is contained in the `F_r`-cylinder of its
window pattern.
-/
lemma extCyl_subset_cyl {r ℓ : ℕ} (h : r ≤ ℓ) (x : Cfg) :
    extCyl r x ℓ ⊆ cyl r (proj r x) := by
  intro y hy
  have hy' := extCyl_mono h hy
  rwa [extCyl_self] at hy'

/-
**Floor collision.**  If a tower floor `Lⁱ·extCyl (3t) x ℓₓ` meets another
tower floor `Lⁱ'·extCyl (3t) y ℓ_y` (both bases coming from period-`≤ t`
patterns at window radius `3t`, with relative shift `|i - i'| ≤ t`), then the two
underlying periodic patterns agree after the relative shift `i' - i`.
-/
lemma floor_collision {t : ℕ} {x y : Cfg} {ℓx ℓy : ℕ}
    (hx : patPeriod (3 * t) x ≤ t) (hy : patPeriod (3 * t) y ≤ t)
    (hℓx : 3 * t ≤ ℓx) (hℓy : 3 * t ≤ ℓy)
    {i i' : ℤ} (hm : |i - i'| ≤ (t : ℤ))
    {z : Cfg}
    (hz : z ∈ (L ^ i) '' (extCyl (3 * t) x ℓx) ∩ (L ^ i') '' (extCyl (3 * t) y ℓy)) :
    proj (3 * t) (cfgExt (3 * t) x)
      = proj (3 * t) ((L ^ (i' - i)) (cfgExt (3 * t) y)) := by
  obtain ⟨a, ha⟩ : ∃ a ∈ extCyl (3 * t) x ℓx, z = (L ^ i) a := by
    exact hz.1.imp fun x hx => ⟨ hx.1, hx.2.symm ⟩
  obtain ⟨b, hb⟩ : ∃ b ∈ extCyl (3 * t) y ℓy, z = (L ^ i') b := by
    exact hz.2.imp fun b hb => ⟨ hb.1, hb.2.symm ⟩;
  -- By `proj_zpow_eq_of_proj_eq`, we have `proj (2 * t) ((L ^ (i' - i)) b) = proj (2 * t) ((L ^ (i' - i)) (cfgExt (3 * t) y))`.
  have h_proj_eq : proj (2 * t) ((L ^ (i' - i)) b) = proj (2 * t) ((L ^ (i' - i)) (cfgExt (3 * t) y)) := by
    apply proj_zpow_eq_of_proj_eq;
    exact hb.1;
    grind;
  have h_proj_eq : proj (2 * t) a = proj (2 * t) (cfgExt (3 * t) x) := by
    exact proj_mono ( by linarith ) ( mem_cyl_iff _ _ _ |>.1 ha.1 );
  apply orbit_collision;
  · exact le_trans ( patPeriod_cfgExt_le _ _ ) hx;
  · exact le_trans ( patPeriod_zpow_cfgExt_le _ _ _ ) hy;
  · have h_proj_eq : (L ^ (-i)) ((L ^ i') b) = (L ^ (i' - i)) b := by
      rw [ ← Equiv.Perm.mul_apply, ← zpow_add, show -i + i' = i' - i from by ring ]
    aesop

/-- **Floor disjointness.**  Contrapositive packaging of `floor_collision`: if the
underlying periodic patterns do *not* agree after the relative shift `i' - i`
(with `|i - i'| ≤ t`), then the two tower floors are disjoint.  This is the form
consumed by the covering construction's pairwise-disjointness obligations. -/
lemma floor_disjoint {t : ℕ} {x y : Cfg} {ℓx ℓy : ℕ}
    (hx : patPeriod (3 * t) x ≤ t) (hy : patPeriod (3 * t) y ≤ t)
    (hℓx : 3 * t ≤ ℓx) (hℓy : 3 * t ≤ ℓy)
    {i i' : ℤ} (hm : |i - i'| ≤ (t : ℤ))
    (hne : proj (3 * t) (cfgExt (3 * t) x)
      ≠ proj (3 * t) ((L ^ (i' - i)) (cfgExt (3 * t) y))) :
    Disjoint ((L ^ i) '' (extCyl (3 * t) x ℓx))
      ((L ^ i') '' (extCyl (3 * t) y ℓy)) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  exact hne (floor_collision hx hy hℓx hℓy hm ⟨hz, hz'⟩)

end LamplighterStability.Dynamics