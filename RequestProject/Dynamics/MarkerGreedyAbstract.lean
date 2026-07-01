import RequestProject.Dynamics.MarkerLemmas
import RequestProject.Dynamics.CoverFree

/-!
# A greedy marker from an arbitrary window-defined proper colouring

This file generalises `MarkerGreedy.lean` from the fixed colouring `colorKey ℓ`
(the `π_ℓ`-pattern index, with `2^{2ℓ+1}` colours) to an **arbitrary** numeric
colouring `key : Cfg → ℕ` that is

* window-`W`-defined (`hkeydef`),
* bounded by `C` colours (`hbound`), and
* `F_t`-proper on `Ξ` (`hproper`, in the symmetric form needed for independence).

Out of such a colouring the greedy maximal-independent-set algorithm produces a
clopen `t`-marker `Z ⊆ Ξ` that is `(W + C·t)`-defined.  Feeding a *reduced*
colouring (with few colours `C`) then yields a *polynomial* marker window — this
is the point of the Linial colour reduction in `MarkerLinial.lean`.

The proofs are structurally identical to the ones in `MarkerGreedy.lean`; only
the colouring is abstracted.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators

/-- Greedy maximal-independent-set membership for an abstract colouring `key`. -/
noncomputable def inMarkerK (t : ℕ) (key : Cfg → ℕ) (Ξ : Set Cfg) : Cfg → Prop :=
  WellFounded.fix (InvImage.wf key Nat.lt_wfRel.wf)
    (fun x ih =>
      x ∈ Ξ ∧ ∀ i : ℤ, i ∈ Finset.Icc (-(t:ℤ)) (t:ℤ) → i ≠ 0 →
        ∀ hlt : key ((L ^ i) x) < key x, ¬ ih ((L ^ i) x) hlt)

/-- The greedy marker set for an abstract colouring `key`. -/
def markerSetK (t : ℕ) (key : Cfg → ℕ) (Ξ : Set Cfg) : Set Cfg :=
  {x | inMarkerK t key Ξ x}

/-- The defining fixpoint equation for `inMarkerK`. -/
theorem inMarkerK_unfold (t : ℕ) (key : Cfg → ℕ) (Ξ : Set Cfg) (x : Cfg) :
    inMarkerK t key Ξ x ↔
      x ∈ Ξ ∧ ∀ i : ℤ, i ∈ Finset.Icc (-(t:ℤ)) (t:ℤ) → i ≠ 0 →
        key ((L ^ i) x) < key x → ¬ inMarkerK t key Ξ ((L ^ i) x) := by
  unfold inMarkerK
  rw [WellFounded.fix_eq]

/-- The greedy marker is contained in `Ξ`. -/
lemma markerSetK_subset (t : ℕ) (key : Cfg → ℕ) (Ξ : Set Cfg) :
    markerSetK t key Ξ ⊆ Ξ :=
  fun x hx => (inMarkerK_unfold t key Ξ x |>.1 hx).1

/-
**Independence.**  If `key` is `F_t`-proper on `Ξ` (between points of `Ξ`),
the greedy marker is `F_t`-independent.
-/
lemma markerSetK_findep {t : ℕ} {key : Cfg → ℕ} {Ξ : Set Cfg}
    (hproper : ∀ x ∈ Ξ, ∀ i : ℤ, i ∈ Finset.Icc (-(t:ℤ)) (t:ℤ) → i ≠ 0 →
      (L ^ i) x ∈ Ξ → key ((L ^ i) x) ≠ key x) :
    FIndep t (markerSetK t key Ξ) := by
  intro x y hx hy i hi hne hn
  obtain ⟨ z, hz, rfl ⟩ := hi hn;
  have := i hn; simp_all +decide [ markerSetK ] ;
  rw [ inMarkerK_unfold ] at this;
  contrapose! this;
  refine' fun h => ⟨ -x, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.mem_Icc ];
  · linarith;
  · grind +suggestions

/-
**Saturation.**  Every point of `Ξ` is within `F_t` of the marker.
-/
lemma markerSetK_cover (t : ℕ) (key : Cfg → ℕ) (Ξ : Set Cfg) :
    Ξ ⊆ ⋃ (j : ℤ) (_ : j ∈ Finset.Icc (-(t : ℤ)) (t : ℤ)),
      (L ^ j) '' markerSetK t key Ξ := by
  intro x hx;
  by_cases h : inMarkerK t key Ξ x;
  · exact Set.mem_iUnion₂.mpr ⟨ 0, by norm_num, by simpa using h ⟩;
  · by_contra h_contra;
    obtain ⟨j, hj⟩ : ∃ j : ℤ, j ∈ Finset.Icc (-(t:ℤ)) (t:ℤ) ∧ j ≠ 0 ∧ key ((L ^ j) x) < key x ∧ inMarkerK t key Ξ ((L ^ j) x) := by
      contrapose! h;
      exact inMarkerK_unfold t key Ξ x |>.2 ⟨ hx, fun j hj hj' hj'' => h j hj hj' hj'' ⟩;
    refine' h_contra ( Set.mem_iUnion₂.mpr ⟨ -j, _, _ ⟩ ) <;> simp_all +decide;
    · linarith;
    · exact hj.2.2.2

/-
**Uniform definability, inductive core.**  If `key` is `W`-defined and `Ξ` is
`W`-defined, then membership in the marker is determined by the window `W + c·t`
for configurations of colour `≤ c`.
-/
lemma inMarkerK_defined_aux {t W : ℕ} {key : Cfg → ℕ} {Ξ : Set Cfg}
    (hΞ : Defined W Ξ)
    (hkeydef : ∀ x y : Cfg, proj W x = proj W y → key x = key y) :
    ∀ c : ℕ, ∀ x y : Cfg, key x ≤ c →
      proj (W + c * t) x = proj (W + c * t) y →
      (inMarkerK t key Ξ x ↔ inMarkerK t key Ξ y) := by
  intros c x y hc hxy
  induction' c using Nat.strong_induction_on with c ih generalizing x y;
  by_cases hkeyx : key x = 0;
  · -- Since key x = 0, we have key y = 0 by hkeydef.
    have hkeyy : key y = 0 := by
      rw [ ← hkeyx, hkeydef x y ];
      exact proj_mono ( by nlinarith ) hxy;
    rw [ inMarkerK_unfold, inMarkerK_unfold ];
    simp [hkeyx, hkeyy];
    rw [ hΞ x y ( proj_mono ( show W ≤ W + c * t by nlinarith ) hxy ) ];
  · rw [ inMarkerK_unfold, inMarkerK_unfold ];
    have hkeyy : key y = key x := by
      apply hkeydef;
      exact proj_mono ( by nlinarith ) hxy.symm
    have hxΞ : x ∈ Ξ ↔ y ∈ Ξ := by
      exact hΞ x y ( proj_mono ( show W ≤ W + c * t by nlinarith ) hxy )
    simp [hkeyy, hxΞ];
    intro hyΞ;
    constructor <;> intro h i hi₁ hi₂ hi₃ hi₄;
    · convert h i hi₁ hi₂ hi₃ _ using 1;
      · apply ih (key ((L ^ i) y)) (by
        linarith) ((L ^ i) y) ((L ^ i) x) (by
        norm_num) (by
        apply proj_zpow_eq_of_proj_eq;
        exact hxy.symm;
        norm_num +zetaDelta at *;
        nlinarith [ abs_nonneg i, abs_le.mpr ⟨ hi₁, hi₂ ⟩, Nat.pos_of_ne_zero hkeyx ]);
      · convert hi₄ using 1;
        apply hkeydef;
        apply proj_zpow_eq_of_proj_eq;
        convert hxy using 1;
        norm_num;
        exact abs_le.mpr ⟨ by nlinarith [ show ( key x : ℤ ) ≥ 1 by exact_mod_cast Nat.pos_of_ne_zero hkeyx ], by nlinarith [ show ( key x : ℤ ) ≥ 1 by exact_mod_cast Nat.pos_of_ne_zero hkeyx ] ⟩;
    · convert h i hi₁ hi₂ hi₃ _ using 1;
      · apply ih (key ((L ^ i) x)) (by
        linarith) ((L ^ i) x) ((L ^ i) y) (by
        norm_num) (by
        apply proj_zpow_eq_of_proj_eq;
        exact hxy;
        norm_num +zetaDelta at *;
        nlinarith [ abs_nonneg i, abs_le.mpr ⟨ hi₁, hi₂ ⟩, Nat.pos_of_ne_zero hkeyx ]);
      · have h_proj_eq : proj W ((L ^ i) x) = proj W ((L ^ i) y) := by
          apply proj_zpow_eq_of_proj_eq;
          exact hxy;
          norm_num +zetaDelta at *;
          exact abs_le.mpr ⟨ by nlinarith [ show ( c : ℤ ) ≥ 1 by exact_mod_cast Nat.pos_of_ne_zero ( by aesop ) ], by nlinarith [ show ( c : ℤ ) ≥ 1 by exact_mod_cast Nat.pos_of_ne_zero ( by aesop ) ] ⟩;
        grind

/-- **Uniform definability.**  The greedy marker is defined on the window
`W + C·t`. -/
lemma markerSetK_defined {t W C : ℕ} {key : Cfg → ℕ} {Ξ : Set Cfg}
    (hΞ : Defined W Ξ)
    (hkeydef : ∀ x y : Cfg, proj W x = proj W y → key x = key y)
    (hbound : ∀ x, key x < C) :
    Defined (W + C * t) (markerSetK t key Ξ) := by
  intro x y hxy
  exact inMarkerK_defined_aux hΞ hkeydef C x y (Nat.le_of_lt (hbound x)) hxy

/-- **Greedy marker from an abstract colouring.**  Packages the three properties
into the `IsMarker` interface plus measurability and the explicit window. -/
theorem markerOfKey {t W C : ℕ} {key : Cfg → ℕ} {Ξ : Set Cfg}
    (hΞ : Defined W Ξ)
    (hkeydef : ∀ x y : Cfg, proj W x = proj W y → key x = key y)
    (hbound : ∀ x, key x < C)
    (hproper : ∀ x ∈ Ξ, ∀ i : ℤ, i ∈ Finset.Icc (-(t:ℤ)) (t:ℤ) → i ≠ 0 →
      (L ^ i) x ∈ Ξ → key ((L ^ i) x) ≠ key x) :
    ∃ Z : Set Cfg, MeasurableSet Z ∧ Defined (W + C * t) Z ∧ IsMarker t Z Ξ := by
  refine ⟨markerSetK t key Ξ,
    defined_measurableSet (markerSetK_defined hΞ hkeydef hbound),
    markerSetK_defined hΞ hkeydef hbound,
    markerSetK_subset t key Ξ, markerSetK_findep hproper, markerSetK_cover t key Ξ⟩

end LamplighterStability.Dynamics