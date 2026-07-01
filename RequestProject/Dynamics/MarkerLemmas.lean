import RequestProject.Dynamics.PeriodicSets
import RequestProject.Dynamics.MinPeriodCovering
import RequestProject.Dynamics.MinPeriodCoveringAssembly
import RequestProject.Dynamics.MarkerGreedy

/-!
# Phase 1: periodic covering and the marker lemma

This file packages the two dynamical results that the Phase-2
tower-decomposition assembly consumes:

* `covering_per_seq` (`lem:covering_per_seq`): a covering of the approximately
  periodic part `X_per^ℓ(t)` by an error set and `δ`-closed towers of bounded
  height, obtained via the minimal periodic extension (proved in
  `MinPeriodCoveringAssembly.lean`);
* `marker_lemma` (`prop:marker`): the marker lemma for the approximately
  aperiodic part `X_aper^ℓ(t)`.  The paper achieves *polynomial* complexity via
  Linial's distributed colour-reduction algorithm; since the formal statement
  only requires *some* finite uniform window (the complexity bound `markerDef`
  is existentially quantified, with no quantitative constraint), it is proved
  here via the elementary greedy maximal-independent-set construction of
  `MarkerGreedy.lean` (exponential — but finite and uniform — window).

Both are now fully proved.  The Phase-2 assembly (`TowerDecompAssembly.lean`,
`PropDecompProof.lean`) depends on them only through these statements.

Both interfaces are stated with explicit-but-abstract *complexity bound
functions* (`coverDef`, `markerDef`, …) packaged as existentials, exactly as the
paper's `O(·)` bounds enter the final `M₀ = winBound t υ δ` requirement of
`prop:decomp` (which is itself an existential over the window bound).
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators

/-- `Z` is a **`t`-marker** for `Ξ`: it is `F_t`-independent, contained in `Ξ`,
and its translates `{L^j Z : j ∈ F_t}` cover `Ξ`. -/
def IsMarker (t : ℕ) (Z Ξ : Set Cfg) : Prop :=
  Z ⊆ Ξ ∧ FIndep t Z ∧
    Ξ ⊆ ⋃ (j : ℤ) (_ : j ∈ Finset.Icc (-(t : ℤ)) (t : ℤ)), (L ^ j) '' Z

/-- **Polynomial marker lemma (`prop:marker`).**

There is a universal complexity-bound function `markerDef` such that: for every
`t, ℓ, K`, every `K`-defined subset `Ξ ⊆ X_aper^ℓ(t)` admits a measurable
`t`-marker `Z` which is `markerDef t ℓ K`-defined.

The paper's explicit bound is `markerDef t ℓ K = O(max(K,ℓ) + t³ + t·log*(ℓ))`
(via Linial's algorithm); here the bound is abstracted as an existential, which
is all the Phase-2 assembly and the existential window bound of `prop:decomp`
require.  Accordingly it is discharged by the elementary greedy marker of
`MarkerGreedy.lean`, whose window `max ℓ K + (#ℓ-patterns)·t` is exponential but
finite and uniform. -/
theorem marker_lemma :
    ∃ markerDef : ℕ → ℕ → ℕ → ℕ,
      ∀ (t ℓ K : ℕ) (Ξ : Set Cfg), Defined K Ξ → Ξ ⊆ Xaperl t ℓ →
        ∃ Z : Set Cfg, MeasurableSet Z ∧ Defined (markerDef t ℓ K) Z ∧
          IsMarker t Z Ξ := by
  refine ⟨fun t ℓ K => max ℓ K + Fintype.card (Win ℓ → Bool) * t, ?_⟩
  intro t ℓ K Ξ hΞdef hΞsub
  refine ⟨markerSet t ℓ Ξ, defined_measurableSet (markerSet_defined hΞdef),
    markerSet_defined hΞdef,
    markerSet_subset t ℓ Ξ, markerSet_findep hΞsub, markerSet_cover t ℓ Ξ⟩

/-- **Covering the periodic sequences (`lem:covering_per_seq`).**

There are universal constants `Ccov` and a window-requirement function
`coverℓ` and complexity-bound function `coverDef` such that the following holds.
For `1 ≤ t`, `0 < υ, δ ≤ 1/2`, any `ℓ ≥ coverℓ t υ δ`, and any probability
measure `μ`, the approximately periodic part `X_per^ℓ(t)` admits a covering by

* an `ℓ`-defined error set `E` with `μ(E) < υ`, and
* a finite family of clopen towers `Tow(base τ, height τ)` which are
  `δ`-closed, of height `≤ t` (the height equals the minimal period of the base,
  which is at most `t` by construction), with `ℓ`-defined bases, `coverDef t ℓ`-
  defined floors, and singleton `π_t`-projection,

with `E` and all tower floors pairwise disjoint and their union *covering*
`X_per^ℓ(t)`.

**Faithfulness note.**  The paper's statement (`lem:covering_per_seq`) is a
*covering* `X_per^ℓ(t) ⊆ Ξ_per = E ⊔ ⊔ Tow(b,j)`: the disjoint union
`Ξ_per := E ⊔ ⊔ Tow(b,j)` is a clopen *superset* of `X_per^ℓ(t)`, not an exact
partition of it.  An exact equality `E ∪ ⋃ floors = X_per^ℓ(t)` is in fact not
achievable: to be `δ`-closed a tower for a period-`p` pattern must have height
`p > 1`, and a shifted window-cylinder `L^i · base` controls coordinates on a
*shifted* window, so its boundary strip necessarily leaves `X_per^ℓ(t)`; hence
`⋃ floors` properly contains `X_per^ℓ(t)`.  The conclusion below therefore states
the faithful inclusion `X_per^ℓ(t) ⊆ E ∪ ⋃ floors`. -/
theorem covering_per_seq :
    ∃ (coverℓ : ℕ → ℝ → ℝ → ℝ) (coverDef : ℕ → ℕ → ℕ),
      ∀ (t : ℕ) (υ δ : ℝ), 1 ≤ t → 0 < υ → υ ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
        ∀ (ℓ : ℕ), coverℓ t υ δ ≤ (ℓ : ℝ) →
          ∀ (μ : Measure Cfg) [IsProbabilityMeasure μ],
            ∃ (E : Set Cfg) (ι : Type) (_ : Fintype ι)
              (base : ι → Set Cfg) (height : ι → ℕ),
              Defined ℓ E ∧ (μ E).toReal < υ ∧
              (∀ τ : ι, IsTowerBase (height τ) (base τ)) ∧
              (∀ τ : ι, DeltaClosed μ δ (height τ) (base τ)) ∧
              (∀ τ : ι, height τ ≤ t) ∧
              (∀ τ : ι, Defined ℓ (base τ)) ∧
              (∀ τ : ι, ∀ i, i < height τ →
                Defined (coverDef t ℓ) (towerFloor (base τ) i)) ∧
              (∀ τ : ι, ProjSingleton t (base τ)) ∧
              -- floors and `E` are pairwise disjoint:
              (∀ τ τ' : ι, ∀ i i' : ℕ, i < height τ → i' < height τ' →
                ¬ (τ = τ' ∧ i = i') →
                Disjoint (towerFloor (base τ) i) (towerFloor (base τ') i')) ∧
              (∀ τ : ι, ∀ i, i < height τ →
                Disjoint E (towerFloor (base τ) i)) ∧
              -- the family covers the periodic part (a covering, not an exact
              -- partition: `⋃ floors` may properly contain `X_per^ℓ(t)`):
              Xperl t ℓ ⊆ E ∪ ⋃ τ : ι, ⋃ i ∈ Finset.range (height τ),
                  towerFloor (base τ) i :=
  covering_per_seq_impl

end LamplighterStability.Dynamics
