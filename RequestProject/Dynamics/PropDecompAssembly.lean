import RequestProject.Dynamics.TowerDecompAssembly

/-!
# Part 0 — scaffolding for the `prop_decomp` assembly

This file collects the elementary combinatorial / measure-theoretic helper
lemmas about the shift space that the `prop_decomp` (tower-decomposition)
assembly needs but that are not yet in the project.  They are pure bookkeeping
about `Defined`, `ProjSingleton`, `IsTowerBase`, `towerFloor`, and
`IsTowerPartition`, and are independent of the deeper marker / covering content.

Contents:

* **Step 1 — bookkeeping.**  Monotonicity / subset behaviour of `ProjSingleton`
  and `IsTowerBase`; `Defined` closed under finite unions.
* **Step 2 — partition glue.**  Two finite tower families whose floors are
  jointly pairwise disjoint and jointly cover `eᶜ` assemble into a single
  `IsTowerPartition` over `Sum`.
* **Step 3 — height-dichotomy splitting.**  A tower can be refined by its
  `π_j`-patterns into finitely many sub-towers each with singleton
  `π_j`-projection, preserving `Defined` floors and the tower-base property.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators

/-! ## Step 1 — bookkeeping -/

/-
`ProjSingleton` is preserved by passing to a subset.
-/
lemma ProjSingleton.subset {j : ℕ} {b b' : Set Cfg} (hb : ProjSingleton j b)
    (hsub : b' ⊆ b) : ProjSingleton j b' := by
  obtain ⟨ p, hp ⟩ := hb;
  exact ⟨ p, fun x hx => hp ( hsub hx ) ⟩

/-
A singleton `π_j`-projection restricts to a singleton `π_{j'}`-projection for
`j' ≤ j`.
-/
lemma ProjSingleton.mono_window {j j' : ℕ} {b : Set Cfg} (hjj' : j' ≤ j)
    (hb : ProjSingleton j b) : ProjSingleton j' b := by
  -- Let `p` be the unique length-`j` pattern such that `b ⊆ cyl j p`.
  obtain ⟨p, hp⟩ := hb;
  use fun i => p ⟨i.val, by
    exact Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp i.2 ], by linarith [ Finset.mem_Icc.mp i.2 ] ⟩⟩;
  intro x hx; specialize hp hx; simp_all +decide [ cyl ] ;
  exact funext fun i => hp ▸ rfl

/-
The tower-base property is preserved by passing to a subset.
-/
lemma IsTowerBase.subset {j : ℕ} {b b' : Set Cfg} (hb : IsTowerBase j b)
    (hsub : b' ⊆ b) : IsTowerBase j b' := by
  -- Assume `IsTowerBase j b"` (i.e., pairwise disjoint floors of `b`) holds.
  -- To prove the same for `b'`, take an arbitrary pair of floors `i i'` of `b'` and show disjointness.
  rcases j with j
  intro τ τ' i i' hi hi' hne
  generalize_proofs at *;
  contrapose! hb;
  simp_all +decide [ IsTowerBase, Set.subset_def ];
  obtain ⟨ x, hx ⟩ := hb.2; use τ, i, τ', i'; simp_all +decide [ Set.disjoint_left ] ;
  exact ⟨ x, hsub _ ( hne _ hx ), hsub _ ( hb.1 _ hx ) ⟩

/-
The tower-base property is monotone in the height.
-/
lemma IsTowerBase.mono_height {j j' : ℕ} {b : Set Cfg} (hjj' : j' ≤ j)
    (hb : IsTowerBase j b) : IsTowerBase j' b := by
  intro i i' hi hi' hne;
  exact hb i i' ( by linarith ) ( by linarith ) hne

/-
A union of two `n`-defined sets is `n`-defined.
-/
lemma defined_union {n : ℕ} {A B : Set Cfg} (hA : Defined n A) (hB : Defined n B) :
    Defined n (A ∪ B) := by
  intro x y hxy;
  have := hA x y hxy; have := hB x y hxy; aesop;

/-
A finite union of `n`-defined sets is `n`-defined.
-/
lemma defined_biUnion_finset {n : ℕ} {ι : Type*} (s : Finset ι) {f : ι → Set Cfg}
    (hf : ∀ i ∈ s, Defined n (f i)) : Defined n (⋃ i ∈ s, f i) := by
  induction' s using Finset.induction with i s hi ih;
  all_goals try exact Classical.decEq _;
  · -- The union of the empty set is the empty set, which is defined.
    simp [defined_empty];
  · simp_all +decide [];
    exact defined_union hf.1 ih

/-! ## Step 2 — partition glue -/

/-
**Gluing two tower families.**  If two finite tower families have jointly
pairwise-disjoint floors that together cover `eᶜ`, and each base is a genuine
tower base, then the `Sum`-indexed family is an `IsTowerPartition` of `eᶜ`.
-/
lemma isTowerPartition_sum {e : Set Cfg} {ι₁ ι₂ : Type}
    (base₁ : ι₁ → Set Cfg) (height₁ : ι₁ → ℕ)
    (base₂ : ι₂ → Set Cfg) (height₂ : ι₂ → ℕ)
    (hbase₁ : ∀ τ, IsTowerBase (height₁ τ) (base₁ τ))
    (hbase₂ : ∀ τ, IsTowerBase (height₂ τ) (base₂ τ))
    (hdisj₁ : ∀ τ τ' : ι₁, ∀ i i' : ℕ, i < height₁ τ → i' < height₁ τ' →
      ¬ (τ = τ' ∧ i = i') →
      Disjoint (towerFloor (base₁ τ) i) (towerFloor (base₁ τ') i'))
    (hdisj₂ : ∀ τ τ' : ι₂, ∀ i i' : ℕ, i < height₂ τ → i' < height₂ τ' →
      ¬ (τ = τ' ∧ i = i') →
      Disjoint (towerFloor (base₂ τ) i) (towerFloor (base₂ τ') i'))
    (hcross : ∀ (τ₁ : ι₁) (τ₂ : ι₂) (i i' : ℕ),
      i < height₁ τ₁ → i' < height₂ τ₂ →
      Disjoint (towerFloor (base₁ τ₁) i) (towerFloor (base₂ τ₂) i'))
    (hcover : (⋃ τ : ι₁, ⋃ i ∈ Finset.range (height₁ τ), towerFloor (base₁ τ) i)
        ∪ (⋃ τ : ι₂, ⋃ i ∈ Finset.range (height₂ τ), towerFloor (base₂ τ) i)
        = eᶜ) :
    IsTowerPartition e (Sum.elim base₁ base₂) (Sum.elim height₁ height₂) := by
  unfold IsTowerPartition; simp_all +decide [ Set.ext_iff ];
  exact fun b a i i' hi hi' => Disjoint.symm ( hcross a b i' i hi' hi )

/-! ## Step 3 — height-dichotomy splitting -/


end LamplighterStability.Dynamics