import RequestProject.Dynamics.ApproxInvMeasure

/-!
# The error-set measure bound for `lem:covering_per_seq`

This file proves the elementary—but genuinely reusable—measure estimate that
controls the *error set* `E` in the periodic-covering lemma
(`lem:covering_per_seq`, Section 6.1 of the paper).

In the inductive construction of that lemma, the error set is a disjoint union of
"case-1" cylinders, one for some of the `F_n`-window patterns `x`, each of
measure at most `υ·μ(⟦x⟧)`.  The paper bounds its total measure by
`μ(E) ≤ ∑_{x ∈ {0,1}^{F_n}} υ·μ(⟦x⟧) ≤ υ`,
using that the `F_n`-cylinders partition the whole space and hence their measures
sum to `1`.

We isolate the two facts:

* `sum_measure_cyl_eq_one` — the `F_n`-cylinders partition `X`, so their measures
  sum to `1` (for any probability measure);
* `error_set_measure_le` — if a family `f p ⊆ ⟦p⟧` (`p` ranging over a finite set
  of patterns) is measurable with `μ(f p) ≤ υ·μ(⟦p⟧)`, then
  `μ(⋃ₚ f p) ≤ υ`.  (Disjointness of the `f p` is automatic, since they live in
  the pairwise-disjoint cylinders `⟦p⟧`.)

These are stated over the project's full-shift model (`ShiftSpace.lean`,
`ApproxInvMeasure.lean`) and are independent of the still-open covering
construction; they supply its error-bound ingredient.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators
open scoped Classical

/-- **The `F_n`-cylinders partition the space.**  For any probability measure
`μ`, the measures of all `F_n`-window cylinders sum to `1`. -/
lemma sum_measure_cyl_eq_one (n : ℕ) (μ : Measure Cfg) [IsProbabilityMeasure μ] :
    ∑ p : Win n → Bool, μ (cyl n p) = 1 := by
  have huniv : patternsOf n (Set.univ : Set Cfg) = Finset.univ := by
    ext p; simp [mem_patternsOf]
  have := measure_defined_eq_sum (defined_univ n) μ
  rw [measure_univ, huniv] at this
  rw [← this]

/-
**The error-set measure bound** (`lem:covering_per_seq`, error part).
If, for each pattern `p` in a finite set `S`, `f p` is a measurable subset of the
cylinder `⟦p⟧` with `μ(f p) ≤ υ·μ(⟦p⟧)`, then the disjoint union `⋃_{p∈S} f p`
has measure at most `υ`.
-/
lemma error_set_measure_le {n : ℕ} (μ : Measure Cfg) [IsProbabilityMeasure μ]
    {υ : ℝ} (hυ : 0 ≤ υ) (S : Finset (Win n → Bool))
    (f : (Win n → Bool) → Set Cfg)
    (hsub : ∀ p ∈ S, f p ⊆ cyl n p)
    (hmeas : ∀ p ∈ S, MeasurableSet (f p))
    (hbound : ∀ p ∈ S, (μ (f p)).toReal ≤ υ * (μ (cyl n p)).toReal) :
    (μ (⋃ p ∈ S, f p)).toReal ≤ υ := by
  rw [ MeasureTheory.measure_biUnion_finset ];
  · rw [ ENNReal.toReal_sum ];
    · refine' le_trans ( Finset.sum_le_sum hbound ) _;
      rw [ ← Finset.mul_sum _ _ _ ];
      refine' mul_le_of_le_one_right hυ _;
      refine' le_trans _ ( show ( ∑ p : Win n → Bool, ( μ ( cyl n p ) |> ENNReal.toReal ) ) ≤ 1 from _ );
      · exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => ENNReal.toReal_nonneg;
      · rw [ ← ENNReal.toReal_sum ];
        · rw [ sum_measure_cyl_eq_one ] ; norm_num;
        · exact fun _ _ => MeasureTheory.measure_ne_top _ _;
    · exact fun p hp => MeasureTheory.measure_ne_top _ _;
  · intro p hp q hq hpq; exact Set.disjoint_left.mpr fun x hx hx' => by have := Set.disjoint_left.mp ( cyl_disjoint ( show p ≠ q from hpq ) ) ( hsub p hp hx ) ( hsub q hq hx' ) ; contradiction;
  · grind +revert

end LamplighterStability.Dynamics