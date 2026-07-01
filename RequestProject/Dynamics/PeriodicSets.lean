import RequestProject.Dynamics.ApproxInvMeasure

/-!
# Approximately (a)periodic clopen sets (`def:approx_per`, Phase 0)

This file formalizes the clopen approximations to the periodic / aperiodic parts
of the full shift used in the proof of the tower-decomposition proposition
(`prop:decomp`, Sections 4–5 of the paper):

* `Xaperl t ℓ` = the sequences `x` whose `ℓ`-window cylinder `⟦π_ℓ(x)⟧` is
  `F_t`-independent (Definition `def:approx_per`, `X_aper^ℓ(t)`);
* `Xperl t ℓ` = its complement (`X_per^ℓ(t)`).

These are elementary clopen / `ℓ`-defined sets; the deeper dynamical lemmas about
them (`lem:covering_per_seq`, `prop:marker`) live in `MarkerLemmas.lean`.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators

/-- **`X_aper^ℓ(t)`** (`def:approx_per`).  The set of configurations `x` whose
`ℓ`-window cylinder `⟦π_ℓ(x)⟧` is `F_t`-independent. -/
def Xaperl (t ℓ : ℕ) : Set Cfg := {x | FIndep t (cyl ℓ (proj ℓ x))}

/-- **`X_per^ℓ(t)`** (`def:approx_per`), the complement of `X_aper^ℓ(t)`. -/
def Xperl (t ℓ : ℕ) : Set Cfg := (Xaperl t ℓ)ᶜ

lemma mem_Xaperl {t ℓ : ℕ} {x : Cfg} :
    x ∈ Xaperl t ℓ ↔ FIndep t (cyl ℓ (proj ℓ x)) := Iff.rfl

/-- Two configurations agreeing on `F_ℓ` have the same `ℓ`-window cylinder. -/
lemma cyl_proj_eq_of_proj_eq {ℓ : ℕ} {x y : Cfg} (h : proj ℓ x = proj ℓ y) :
    cyl ℓ (proj ℓ x) = cyl ℓ (proj ℓ y) := by rw [h]

/-- `X_aper^ℓ(t)` is `ℓ`-defined. -/
lemma defined_Xaperl (t ℓ : ℕ) : Defined ℓ (Xaperl t ℓ) := by
  intro x y hxy
  simp only [mem_Xaperl, cyl_proj_eq_of_proj_eq hxy]


/-- `X_aper^ℓ(t)` is measurable. -/
lemma measurableSet_Xaperl (t ℓ : ℕ) : MeasurableSet (Xaperl t ℓ) := by
  classical
  rw [defined_eq_biUnion_cyl (defined_Xaperl t ℓ)]
  exact MeasurableSet.biUnion (patternsOf ℓ (Xaperl t ℓ)).countable_toSet
    (fun b _ => measurableSet_cyl ℓ b)


end LamplighterStability.Dynamics
