import RequestProject.Dynamics.PropDecompProof
import RequestProject.Dynamics.MarkerLinial

/-!
# Polynomial-window tower decomposition (`prop:decomp` with the polynomial marker)

This is `prop_decomp` re-derived with the *polynomial* marker lemma
`marker_lemma_poly` (Linial colour reduction) in place of the exponential greedy
`marker_lemma`.  The dynamical assembly is identical; only the marker complexity
function changes, so the returned window bound `winBound` is now polynomial in
`t`, `1/υ`, `1/δ` (and the definability level `ℓ`).
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators

theorem prop_decomp_poly :
    ∃ (Cerr : ℝ) (winBound : ℕ → ℝ → ℝ → ℝ), 0 < Cerr ∧
      ∀ (t : ℕ) (υ δ η : ℝ), 1 ≤ t → 0 < υ → υ ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
        0 < η → η ≤ 1 / 2 →
        ∀ (M₀ : ℕ), winBound t υ δ ≤ (M₀ : ℝ) →
          ∀ (μ : Measure Cfg) [IsProbabilityMeasure μ], ApproxInvMeasure M₀ η μ →
            ∃ (e : Set Cfg), Defined M₀ e ∧
              (μ e).toReal ≤ Cerr * (t : ℝ) ^ 6 * (υ + δ + η) ∧
              ∃ (ι : Type) (_ : Fintype ι) (base : ι → Set Cfg) (height : ι → ℕ),
                IsTowerPartition e base height ∧
                (∀ τ : ι, ∀ i, i < height τ →
                  Defined M₀ (towerFloor (base τ) i)) ∧
                (∀ τ : ι,
                  (height τ < t ∧ DeltaClosed μ δ (height τ) (base τ)) ∨
                  (t ≤ height τ ∧ height τ < 6 * t + 1)) ∧
                (∀ τ : ι, ProjSingleton (height τ) (base τ)) := by
  classical
  obtain ⟨Ccb, hCcb, hCB⟩ := complement_bound
  obtain ⟨covℓ, covDef, hCov⟩ := covering_per_seq
  obtain ⟨mDef, hMark⟩ := marker_lemma_poly
  refine ⟨9 * Ccb + 19,
    fun t υ δ =>
      ((2 * t * ((⌈covℓ t υ δ⌉₊ + covDef t ⌈covℓ t υ δ⌉₊)
            + mDef t ⌈covℓ t υ δ⌉₊ (⌈covℓ t υ δ⌉₊ + covDef t ⌈covℓ t υ δ⌉₊))
        + 6 * ((⌈covℓ t υ δ⌉₊ + covDef t ⌈covℓ t υ δ⌉₊)
            + mDef t ⌈covℓ t υ δ⌉₊ (⌈covℓ t υ δ⌉₊ + covDef t ⌈covℓ t υ δ⌉₊))
        + 31 * t + 1 : ℕ) : ℝ),
    by positivity, ?_⟩
  intro t υ δ η ht hυ hυ2 hδ hδ2 hη hη2 M₀ hM₀ μ _inst hμ
  simp only [] at hM₀
  set ℓ := ⌈covℓ t υ δ⌉₊ with hℓdef
  -- `K` bounds the complexity of the periodic covering data (error set `E` and
  -- tower floors); `Ξ_aper := (E ∪ ⋃ floors)ᶜ` is then `K`-defined.
  set K := ℓ + covDef t ℓ with hKdef
  set D := K + mDef t ℓ K with hDdef
  have hM : 2 * t * D + 6 * D + 31 * t + 1 ≤ M₀ := by exact_mod_cast hM₀
  have hℓD : ℓ ≤ D := by omega
  have hmD : mDef t ℓ K ≤ D := by omega
  have hcD : covDef t ℓ ≤ D := by omega
  have hKD : K ≤ D := by omega
  have hbnd1 : 2 * D + 6 * t + 1 ≤ M₀ := by omega
  have hbnd2 : 2 * t * D ≤ M₀ := by omega
  have hbnd3 : D + 30 * t ≤ M₀ := by omega
  obtain ⟨E, ι₁, fι₁, base₁, height₁, hEdef, hEμ, hTB₁, hclosed₁, hheight₁,
    hbasedef₁, hfloordef₁, hPS₁, hdisj₁, hEdisj₁, hcover₁⟩ :=
    hCov t υ δ ht hυ hυ2 hδ hδ2 ℓ (by exact_mod_cast Nat.le_ceil _) μ
  -- The aperiodic clopen target `Ξ_aper` is the complement of the periodic
  -- covering `E ∪ ⋃ floors`.  Because the covering is only an inclusion
  -- `X_per^ℓ(t) ⊆ E ∪ ⋃ floors` (the faithful `covering_per_seq`), this set is a
  -- *subset* of `X_aper^ℓ(t)`, and the aperiodic towers built inside it are
  -- automatically (exactly) disjoint from the periodic floors and `E`.
  set Ξ : Set Cfg :=
      (E ∪ ⋃ τ : ι₁, ⋃ i ∈ Finset.range (height₁ τ), towerFloor (base₁ τ) i)ᶜ
    with hΞdef_eq
  -- `Ξ` is `K`-defined (hence `D`-defined).
  have hEK : Defined K E := hEdef.mono (by omega)
  have hUdef : Defined K (⋃ τ : ι₁, ⋃ i ∈ Finset.range (height₁ τ),
      towerFloor (base₁ τ) i) :=
    defined_iUnion (fun τ => defined_biUnion_finset _
      (fun i hi => (hfloordef₁ τ i (Finset.mem_range.mp hi)).mono (by omega)))
  have hΞdefK : Defined K Ξ := by
    rw [hΞdef_eq]; exact defined_compl (defined_union hEK hUdef)
  -- `Ξ ⊆ X_aper^ℓ(t)`, from `X_per^ℓ(t) ⊆ E ∪ ⋃ floors`.
  have hΞsub : Ξ ⊆ Xaperl t ℓ := by
    intro x hx
    rw [hΞdef_eq] at hx
    by_contra hxa
    exact hx (hcover₁ hxa)
  -- `E ∪ ⋃ floors = Ξᶜ` (definitional, used to assemble the exact partition).
  have hcompl : E ∪ (⋃ τ : ι₁, ⋃ i ∈ Finset.range (height₁ τ),
      towerFloor (base₁ τ) i) = Ξᶜ := by
    rw [hΞdef_eq, compl_compl]
  -- build the marker for `Ξ` (not for all of `X_aper^ℓ(t)`): this forces
  -- `Z ⊆ Ξ`, so `Z` avoids `E` and every periodic floor.
  obtain ⟨Z, hZmeas, hZdef, hZsub, hZfindep, hZsat⟩ :=
    hMark t ℓ K Ξ hΞdefK hΞsub
  -- the marker is (exactly) disjoint from each periodic floor, since `Z ⊆ Ξ`.
  have hZdisj : ∀ τ i, i < height₁ τ → Disjoint Z (towerFloor (base₁ τ) i) := by
    intro τ i hi
    rw [Set.disjoint_left]
    intro x hxZ hxF
    have hxΞ := hZsub hxZ
    rw [hΞdef_eq] at hxΞ
    exact hxΞ (Or.inr (Set.mem_iUnion.2
      ⟨τ, Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hi, hxF⟩⟩))
  have h2tpos : (0 : ℝ) < 2 * (t : ℝ) := by positivity
  have hDdiv : (D : ℝ) ≤ (M₀ : ℝ) / (2 * t) := by
    rw [le_div_iff₀ h2tpos]
    have : ((2 * t * D : ℕ) : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hbnd2
    push_cast at this ⊢; nlinarith [this]
  -- per-term complement bound
  have hcb : ∀ i : ℤ, i ∈ Finset.Icc (-(t : ℤ)) (t : ℤ) →
      (μ (((L ^ i) '' Z) \ Ξ)).toReal ≤ Ccb * ((t : ℝ) ^ 4 * η + (t : ℝ) ^ 3 * δ + υ) := by
    intro i hi
    have hi2t : i ∈ Finset.Icc (-(2 * t : ℤ)) (2 * t : ℤ) := by
      rw [Finset.mem_Icc] at hi ⊢; omega
    have h02t : (0 : ℤ) ∈ Finset.Icc (-(2 * t : ℤ)) (2 * t : ℤ) := by
      rw [Finset.mem_Icc]; omega
    have h0img : (L ^ (0 : ℤ)) '' Ξ = Ξ := by
      rw [zpow_zero]; simp
    have hsub : ((L ^ i) '' Z) \ ((L ^ (0 : ℤ)) '' Ξ) ⊆
        E ∪ ⋃ τ : ι₁, ⋃ i' ∈ Finset.range (height₁ τ), towerFloor (base₁ τ) i' := by
      rw [h0img, hΞdef_eq]
      rintro x ⟨_, hxΞ⟩; exact not_not.mp hxΞ
    have key := hCB t υ δ η M₀ D μ Ξ Z E ι₁ fι₁ base₁ height₁ ht hυ hδ hη hμ
      (hΞdefK.mono hKD) (hZdef.mono hmD) hDdiv hbnd3
      (fun τ => le_trans (hheight₁ τ) (by omega))
      (fun τ i hi => (hfloordef₁ τ i hi).mono hcD) hclosed₁ hdisj₁ hEμ hZsub hZdisj
      i 0 hi2t h02t hsub
    rwa [h0img] at key
  exact prop_decomp_core ht hυ hδ hη hμ hCcb (hZdef.mono hmD) (hΞdefK.mono hKD)
    hℓD hbnd1 hbnd3
    hZfindep hZsat hEdef hEμ hTB₁ hclosed₁ hheight₁
    (fun τ i hi => (hfloordef₁ τ i hi).mono hcD) hPS₁ hdisj₁ hEdisj₁ hcompl hcb


end LamplighterStability.Dynamics
