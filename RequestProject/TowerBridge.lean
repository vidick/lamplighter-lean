import Mathlib
import RequestProject.PVMAlgebra
import RequestProject.ProjectionTowers
import RequestProject.Dynamics.TowerDecomp
import RequestProject.Dynamics.PropDecompAssembly

/-!
# Tower bridge: the matrix `Edef`-projection decomposition of a tower partition

This file connects the **measure-theoretic tower partition** produced by
`prop_decomp` (over the shift space `Cfg = ℤ → Bool`) to the **matrix-side
orthogonal decomposition** of `ℂ^d` by the projection-valued measure
`Edef M (EpatB M B) S = ∑_{p ∈ π_M(S)} EpatB M B p` of a commuting family
`B : Win M → Matrix (Fin d) (Fin d) ℂ` of Hermitian involutions
(`MeasureBridge.lean`, `MeasureInstantiation.lean`, `PVMAlgebra.lean`).

These are the facts the final Section 5 aggregate-Pythagoras step needs:

* `Edef_floors_pairwiseOrthProj` — the floors `i ↦ Edef M E (towerFloor b i)` of a
  single tower base `b` of height `j` are pairwise orthogonal matrix projections
  (`PairwiseOrthProj j`): projection-ness from `Edef_isProj`, orthogonality from
  `Edef_mul_of_disjoint` together with `IsTowerBase`.
* `Edef_biUnion_finset` — finite additivity of `Edef` over a pairwise-disjoint
  family of `M`-definable sets.
* `Edef_partition_resolution` — the **resolution of identity** for an entire
  `IsTowerPartition`:
  `E_e + ∑_τ ∑_{i<height τ} E_{floor τ i} = 1`, i.e. the orthogonal
  decomposition `ℂ^d = E_e ℂ^d ⊕ ⨁_{τ,i} E_{floor τ i} ℂ^d`.
-/

namespace LamplighterStability.MeasureBridge

open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureInstantiation
open scoped BigOperators
open Matrix

variable {d : ℕ}

/-
The floors `i ↦ Edef M (EpatB M B) (towerFloor b i)` of a single tower base
`b` of height `j` form a family of pairwise orthogonal matrix projections.
-/
lemma Edef_floors_pairwiseOrthProj (M j : ℕ)
    (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {b : Set Cfg} (hbase : IsTowerBase j b) :
    PairwiseOrthProj j (fun i => Edef M (EpatB M B) (towerFloor b i)) := by
  refine' ⟨ fun i hi => Edef_isProj M B hBh hB2 hBc _, _ ⟩;
  exact fun i hi k hk hik => Edef_mul_of_disjoint M B hB2 hBc ( hbase i k hi hk hik )

/-
Finite additivity of `Edef` over a pairwise-disjoint family of `M`-definable
sets.
-/
lemma Edef_biUnion_finset (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    {κ : Type*} [DecidableEq κ] (s : Finset κ) (f : κ → Set Cfg)
    (hdef : ∀ k ∈ s, Defined M (f k))
    (hdisj : ∀ k ∈ s, ∀ k' ∈ s, k ≠ k' → Disjoint (f k) (f k')) :
    Edef M (EpatB M B) (⋃ k ∈ s, f k) = ∑ k ∈ s, Edef M (EpatB M B) (f k) := by
  induction' s using Finset.induction with k s' hks' ih generalizing f;
  · simp +decide [ Edef ];
    convert Finset.sum_empty;
    simp +decide [ patternsOf ];
    intro x; exact Set.Nonempty.ne_empty (cyl_nonempty M x) ;
  · rw [ Finset.set_biUnion_insert, Edef_union_of_disjoint ];
    · rw [ Finset.sum_insert hks', ih f ( fun x hx => hdef x ( Finset.mem_insert_of_mem hx ) ) ( fun x hx y hy hxy => hdisj x ( Finset.mem_insert_of_mem hx ) y ( Finset.mem_insert_of_mem hy ) hxy ) ];
    · exact hdef k ( Finset.mem_insert_self _ _ );
    · exact Set.disjoint_iUnion₂_right.mpr fun x hx => hdisj k ( Finset.mem_insert_self _ _ ) x ( Finset.mem_insert_of_mem hx ) ( by aesop )

/-
**Resolution of identity for a tower partition.**  If `(e, base, height)` is
an `IsTowerPartition` with every floor and the error set `M`-definable, then the
matrix projections `E_e` and the floor projections `E_{floor τ i}` sum to the
identity, exhibiting the orthogonal decomposition
`ℂ^d = E_e ℂ^d ⊕ ⨁_{τ, i<height τ} E_{floor τ i} ℂ^d`.
-/
lemma Edef_partition_resolution (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    {e : Set Cfg} {ι : Type} [Fintype ι] {base : ι → Set Cfg} {height : ι → ℕ}
    (hpart : IsTowerPartition e base height)
    (hedef : Defined M e)
    (hfloordef : ∀ τ, ∀ i, i < height τ → Defined M (towerFloor (base τ) i)) :
    Edef M (EpatB M B) e
      + ∑ τ : ι, ∑ i ∈ Finset.range (height τ),
          Edef M (EpatB M B) (towerFloor (base τ) i) = 1 := by
  have h_sum_floors : Edef M (EpatB M B) e + Edef M (EpatB M B) (⋃ τ : ι, ⋃ i ∈ Finset.range (height τ), towerFloor (base τ) i) = 1 := by
    have h_sum_floors : Edef M (EpatB M B) e + Edef M (EpatB M B) eᶜ = 1 := by
      rw [ ← Edef_univ ];
      rw [ ← Edef_union_of_disjoint M B hedef disjoint_compl_right, Set.union_compl_self ];
    convert h_sum_floors using 2 ; rw [ hpart.2.1 ];
  convert h_sum_floors using 2;
  convert Edef_biUnion_finset M B ( Finset.univ.sigma fun τ => Finset.range ( height τ ) ) ( fun ⟨ τ, i ⟩ => towerFloor ( base τ ) i ) _ _ |> Eq.symm using 1;
  · erw [ Finset.sum_sigma ];
  · congr! 1;
    ext; simp [Finset.mem_sigma, Finset.mem_range];
  · -- Since ι is a finite type, its elements are decidable. Therefore, the product of ι and ℕ is decidable.
    apply Classical.decEq;
  · aesop;
  · simp +zetaDelta at *;
    exact fun k hk k' hk' hne => hpart.1 _ _ _ _ hk hk' ( by contrapose! hne; aesop )

end LamplighterStability.MeasureBridge