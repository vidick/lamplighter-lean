import RequestProject.Dynamics.PeriodicSets
import RequestProject.Dynamics.MinPeriodOrbit

/-!
# A greedy (finite-window) marker for the full shift

This file constructs, for any `K`-defined `Ξ ⊆ X_aper^ℓ(t)`, a clopen `t`-marker
`Z ⊆ Ξ` (independent + saturating) that is *uniformly* defined on a finite window.

The paper obtains a marker of *polynomial* complexity via Linial's distributed
`LOCAL` colour-reduction algorithm.  The formal statement of `marker_lemma`
(`MarkerLemmas.lean`) only asks for *some* finite window bound (the complexity
function `markerDef` is existentially quantified, with no quantitative
requirement), so it suffices to use the elementary greedy maximal-independent-set
marker, which gives an exponential — but finite and uniform — window.  (The paper
explicitly notes that "a greedy procedure to construct marker sets" already gives
the result, with an exponential bound.)

## Construction

The aperiodicity of `Ξ ⊆ X_aper^ℓ(t)` provides a *proper colouring* of the
`F_t`-Schreier graph by the finite set of `ℓ`-window patterns: for `x ∈ Ξ` and
`0 < |i| ≤ t`, `proj ℓ (Lⁱ x) ≠ proj ℓ x`.  We turn this into a numeric colour
`colorKey ℓ x ∈ ℕ` and run the greedy maximal-independent-set algorithm in colour
order, expressed as a well-founded recursion on `colorKey`:

`x ∈ Z  ⟺  x ∈ Ξ ∧ (no F_t-neighbour of strictly smaller colour lies in Z)`.

* **Independence** (`markerSet_findep`) and **saturation** (`markerSet_cover`)
  are immediate from the recursive definition.
* **Uniform definability** (`markerSet_defined`) follows by induction on the
  colour value: unwinding the recursion `c` times consumes a window `c · t`, and
  there are only `Fintype.card (Win ℓ → Bool)` colours.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators

/-- The numeric **colour** of `x`: the index of its `ℓ`-window pattern under a
fixed bijection of the (finite) pattern set with `Fin (card)`. -/
noncomputable def colorKey (ℓ : ℕ) (x : Cfg) : ℕ :=
  (Fintype.equivFin (Win ℓ → Bool) (proj ℓ x)).val

/-- Greedy maximal-independent-set membership, by well-founded recursion on
`colorKey`: `x ∈ Z` iff `x ∈ Ξ` and no strictly-smaller-colour `F_t`-neighbour of
`x` is in `Z`. -/
noncomputable def inMarker (t ℓ : ℕ) (Ξ : Set Cfg) : Cfg → Prop :=
  WellFounded.fix (InvImage.wf (colorKey ℓ) Nat.lt_wfRel.wf)
    (fun x ih =>
      x ∈ Ξ ∧ ∀ i : ℤ, i ∈ Finset.Icc (-(t:ℤ)) (t:ℤ) → i ≠ 0 →
        ∀ hlt : colorKey ℓ ((L ^ i) x) < colorKey ℓ x, ¬ ih ((L ^ i) x) hlt)

/-- The greedy marker set. -/
def markerSet (t ℓ : ℕ) (Ξ : Set Cfg) : Set Cfg := {x | inMarker t ℓ Ξ x}

/-- The defining fixpoint equation for `inMarker`. -/
theorem inMarker_unfold (t ℓ : ℕ) (Ξ : Set Cfg) (x : Cfg) :
    inMarker t ℓ Ξ x ↔
      x ∈ Ξ ∧ ∀ i : ℤ, i ∈ Finset.Icc (-(t:ℤ)) (t:ℤ) → i ≠ 0 →
        colorKey ℓ ((L ^ i) x) < colorKey ℓ x → ¬ inMarker t ℓ Ξ ((L ^ i) x) := by
  unfold inMarker
  rw [WellFounded.fix_eq]

/-- The colour is determined by the `ℓ`-window pattern. -/
lemma colorKey_eq_of_proj_eq {ℓ : ℕ} {x y : Cfg} (h : proj ℓ x = proj ℓ y) :
    colorKey ℓ x = colorKey ℓ y := by
  unfold colorKey; rw [h]

/-- Two configurations with the same colour have the same `ℓ`-window pattern. -/
lemma proj_eq_of_colorKey_eq {ℓ : ℕ} {x y : Cfg} (h : colorKey ℓ x = colorKey ℓ y) :
    proj ℓ x = proj ℓ y := by
  apply (Fintype.equivFin (Win ℓ → Bool)).injective
  apply Fin.val_injective
  exact h

/-
**Properness of the colouring on the aperiodic part.**  For `x ∈ X_aper^ℓ(t)`
and `0 < |i| ≤ t`, the `i`-shift of `x` has a different colour.
-/
lemma colorKey_proper {t ℓ : ℕ} {x : Cfg} (hx : x ∈ Xaperl t ℓ)
    {i : ℤ} (hi : i ∈ Finset.Icc (-(t:ℤ)) (t:ℤ)) (hi0 : i ≠ 0) :
    colorKey ℓ ((L ^ i) x) ≠ colorKey ℓ x := by
  intro h; have := proj_eq_of_colorKey_eq h; simp_all +decide [ mem_Xaperl, FIndep ] ;
  exact Set.disjoint_left.mp ( hx i hi.1 hi.2 hi0 ) ( mem_cyl_iff _ _ _ |>.2 this ) ( Set.mem_image_of_mem _ ( mem_cyl_iff _ _ _ |>.2 rfl ) )

/-
The marker is contained in `Ξ`.
-/
lemma markerSet_subset (t ℓ : ℕ) (Ξ : Set Cfg) : markerSet t ℓ Ξ ⊆ Ξ := by
  exact fun x hx => inMarker_unfold t ℓ Ξ x |>.1 hx |>.1

/-
**Independence.**  The greedy marker is `F_t`-independent.
-/
lemma markerSet_findep {t ℓ : ℕ} {Ξ : Set Cfg} (hΞ : Ξ ⊆ Xaperl t ℓ) :
    FIndep t (markerSet t ℓ Ξ) := by
  refine' fun i hi hi0 => Set.disjoint_left.mpr _;
  intro x hx h'x
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ markerSet t ℓ Ξ, (L ^ i) y = x := by
    exact h'x
  generalize_proofs at *;
  have hj : (L ^ (-i)) x = y := by
    simp +decide [ ← hxy, zpow_neg ]
  generalize_proofs at *;
  have hcolor : colorKey ℓ ((L ^ (-i)) x) ≠ colorKey ℓ x := by
    apply colorKey_proper (hΞ (markerSet_subset t ℓ Ξ hx)) (by
    grind) (by
    grind +splitIndPred)
  generalize_proofs at *;
  cases lt_or_gt_of_ne hcolor <;> simp_all +decide ;
  · have := inMarker_unfold t ℓ Ξ x |>.1 hx;
    exact this.2 ( -i ) ( Finset.mem_Icc.mpr ⟨ by omega, by omega ⟩ ) ( by omega ) ( by aesop ) ( by aesop );
  · have := inMarker_unfold t ℓ Ξ y; simp_all +decide [ markerSet ] ;
    exact hy.2 i hi.1 hi.2 hi0 ( by aesop ) ( by aesop )

/-
**Saturation.**  Every point of `Ξ` is within `F_t` of the marker.
-/
lemma markerSet_cover (t ℓ : ℕ) (Ξ : Set Cfg) :
    Ξ ⊆ ⋃ (j : ℤ) (_ : j ∈ Finset.Icc (-(t : ℤ)) (t : ℤ)),
      (L ^ j) '' markerSet t ℓ Ξ := by
  intro x hx;
  by_cases h : inMarker t ℓ Ξ x;
  · exact Set.mem_iUnion₂.mpr ⟨ 0, by norm_num, by simpa using h ⟩;
  · rw [ inMarker_unfold ] at h;
    simp_all +decide [ Set.mem_iUnion ];
    obtain ⟨ i, hi₁, hi₂, hi₃, hi₄, hi₅ ⟩ := h; use -i; simp_all +decide [ markerSet ] ;
    exact ⟨ by linarith, by simpa [ zpow_neg ] using hi₅ ⟩

/-
**Uniform definability, inductive core.**  Membership in the marker is
determined by the window `max ℓ K + c·t` for configurations of colour `≤ c`.
-/
lemma inMarker_defined_aux {t ℓ K : ℕ} {Ξ : Set Cfg} (hΞ : Defined K Ξ) :
    ∀ c : ℕ, ∀ x y : Cfg, colorKey ℓ x ≤ c →
      proj (max ℓ K + c * t) x = proj (max ℓ K + c * t) y →
      (inMarker t ℓ Ξ x ↔ inMarker t ℓ Ξ y) := by
  intro c;
  induction' c using Nat.strong_induction_on with c ih;
  intro x y hx hy
  by_cases hctx : colorKey ℓ x = 0;
  · have hctx' : colorKey ℓ y = 0 := by
      have hctx' : colorKey ℓ x = colorKey ℓ y := by
        apply colorKey_eq_of_proj_eq; exact proj_mono (by
        exact le_add_of_le_of_nonneg ( le_max_left _ _ ) ( Nat.zero_le _ )) hy;
      rw [hctx'] at hctx
      exact hctx;
    rw [ inMarker_unfold, inMarker_unfold ];
    simp [hctx, hctx'];
    apply hΞ;
    exact proj_mono ( show K ≤ max ℓ K + c * t from by nlinarith [ Nat.le_max_right ℓ K ] ) hy;
  · rw [ inMarker_unfold, inMarker_unfold ];
    have h_proj_eq : proj ℓ x = proj ℓ y := by
      exact proj_mono ( by nlinarith [ Nat.pos_of_ne_zero hctx, le_max_left ℓ K, le_max_right ℓ K ] ) hy
    have h_colorKey_eq : colorKey ℓ x = colorKey ℓ y := by
      exact colorKey_eq_of_proj_eq h_proj_eq
    have hΞ_eq : x ∈ Ξ ↔ y ∈ Ξ := by
      apply hΞ;
      exact proj_mono ( show K ≤ max ℓ K + c * t from by nlinarith [ Nat.le_max_right ℓ K ] ) hy
    simp_all +decide [ Finset.mem_Icc ];
    intro hyΞ
    apply Iff.intro;
    · intro h i hi₁ hi₂ hi₃ hi₄ hi₅
      have h_colorKey_eq : colorKey ℓ ((L ^ i) x) = colorKey ℓ ((L ^ i) y) := by
        apply colorKey_eq_of_proj_eq;
        apply proj_zpow_eq_of_proj_eq hy;
        norm_num +zetaDelta at *;
        cases abs_cases i <;> nlinarith [ show ( colorKey ℓ y : ℤ ) ≥ 1 by exact_mod_cast Nat.pos_of_ne_zero hctx, show ( max ℓ K : ℤ ) ≥ ℓ by exact_mod_cast le_max_left _ _ ]
      have h_proj_eq : proj (max ℓ K + (colorKey ℓ ((L ^ i) y)) * t) ((L ^ i) x) = proj (max ℓ K + (colorKey ℓ ((L ^ i) y)) * t) ((L ^ i) y) := by
        apply proj_zpow_eq_of_proj_eq hy;
        norm_num +zetaDelta at *;
        nlinarith [ abs_le.mpr ⟨ hi₁, hi₂ ⟩, Nat.pos_of_ne_zero hctx ]
      exact (by
      grind);
    · intro h i hi₁ hi₂ hi₃ hi₄;
      convert h i hi₁ hi₂ hi₃ _ using 1;
      · apply ih (colorKey ℓ ((L ^ i) x)) (by
        linarith) ((L ^ i) x) ((L ^ i) y) (by
        bv_omega) (by
        apply proj_zpow_eq_of_proj_eq hy;
        norm_num +zetaDelta at *;
        nlinarith [ abs_le.mpr ⟨ hi₁, hi₂ ⟩, Nat.pos_of_ne_zero hctx ]);
      · convert hi₄ using 1;
        apply colorKey_eq_of_proj_eq;
        apply proj_zpow_eq_of_proj_eq;
        exact hy.symm;
        norm_num +zetaDelta at *;
        cases abs_cases i <;> nlinarith [ show ( c : ℤ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ( by aesop ), show ( max ℓ K : ℤ ) ≥ ℓ by exact_mod_cast le_max_left _ _ ]

/-
**Uniform definability.**  The greedy marker is defined on the finite window
`max ℓ K + (number of ℓ-patterns)·t`.
-/
lemma markerSet_defined {t ℓ K : ℕ} {Ξ : Set Cfg} (hΞ : Defined K Ξ) :
    Defined (max ℓ K + Fintype.card (Win ℓ → Bool) * t) (markerSet t ℓ Ξ) := by
  intro x y hxy;
  apply inMarker_defined_aux hΞ;
  convert Nat.le_of_lt ( Fin.is_lt _ );
  exact hxy

/-- A defined set is measurable (self-contained copy). -/
lemma defined_measurableSet {n : ℕ} {S : Set Cfg} (hS : Defined n S) :
    MeasurableSet S := by
  rw [defined_eq_biUnion_cyl hS]
  exact MeasurableSet.biUnion (patternsOf n S).countable_toSet
    (fun b _ => measurableSet_cyl n b)

end LamplighterStability.Dynamics