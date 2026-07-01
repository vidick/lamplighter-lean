import RequestProject.Dynamics.ApproxInvMeasure

/-!
# Tower decomposition for approximately invariant measures (`prop:decomp`)

This file holds the **definition** `IsTowerPartition` used to state the
tower-decomposition proposition (`prop:decomp`, Section 5 of the paper).

The proposition itself (`prop_decomp`) is *proved* — not merely stated — in
`RequestProject.Dynamics.PropDecompProof`, a file late in the import DAG that can
see the full Kakutani–Rokhlin / marker / covering assembly machinery
(`TowerDecompAssembly.lean`, `PropDecompAssembly.lean`, `KakutaniRokhlin.lean`).
Because those files all import the present one (for `IsTowerPartition`), Lean's
import DAG forbids writing the proof here; only the `Prop`-valued definition lives
here.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators

/-- A family of clopen towers (with bases `base τ` and heights `height τ`,
indexed by a finite set) **partitions** `X ∖ e`: the floors are pairwise
disjoint, their union is `eᶜ`, and each base is a genuine tower base of its
height. -/
def IsTowerPartition (e : Set Cfg) {ι : Type} (base : ι → Set Cfg)
    (height : ι → ℕ) : Prop :=
  (∀ τ τ' : ι, ∀ i i' : ℕ, i < height τ → i' < height τ' →
      ¬ (τ = τ' ∧ i = i') →
      Disjoint (towerFloor (base τ) i) (towerFloor (base τ') i'))
    ∧ (⋃ τ : ι, ⋃ i ∈ Finset.range (height τ), towerFloor (base τ) i) = eᶜ
    ∧ (∀ τ : ι, IsTowerBase (height τ) (base τ))

end LamplighterStability.Dynamics
