import RequestProject.Dynamics.PropDecompPoly

/-!
# Polynomial-window tower decomposition with an **explicit** window bound

`prop_decomp_poly` (`PropDecompPoly.lean`) re-derives the tower decomposition
with the polynomial marker lemma, but its window bound `winBound` is supplied
*existentially* (it depends on the hidden covering-complexity function `covℓ`).

Here we re-run the same proof using the **explicit** covering lemma
`covering_per_seq_explicit` (which exposes `covℓ t υ δ = C2·(3t)·log(2/υ)/δ + 4t`
and `covDef t ℓ = ℓ + t`) and the **explicit** marker window `markerDefPoly`,
so that the returned window bound is a *closed-form* expression
`winBoundPoly C2 t υ δ` in `t`, `υ`, `δ` (with one universal constant `C2`).
This explicit shape is what the final assembly needs to verify the closed-form
polynomial modulus `M = ⌈C κ⁻²⁰ log(2/κ)⌉` of Theorem 1.1.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators

/-- The explicit covering-window length:
`coverLenPoly C2 t υ δ = C2·(3t)·log(2/υ)/δ + 4t`. -/
noncomputable def coverLenPoly (C2 : ℝ) (t : ℕ) (υ δ : ℝ) : ℝ :=
  C2 * (3 * t) * Real.log (2 / υ) / δ + 4 * t

/-- The explicit closed-form tower-decomposition window.  With
`ℓ = ⌈coverLenPoly C2 t υ δ⌉₊`, `K = 2ℓ + t`, `D = K + markerDefPoly t ℓ K`, it
equals `2tD + 6D + 31t + 1`. -/
noncomputable def winBoundPoly (C2 : ℝ) (t : ℕ) (υ δ : ℝ) : ℕ :=
  2 * t * ((2 * ⌈coverLenPoly C2 t υ δ⌉₊ + t)
        + markerDefPoly t ⌈coverLenPoly C2 t υ δ⌉₊ (2 * ⌈coverLenPoly C2 t υ δ⌉₊ + t))
    + 6 * ((2 * ⌈coverLenPoly C2 t υ δ⌉₊ + t)
        + markerDefPoly t ⌈coverLenPoly C2 t υ δ⌉₊ (2 * ⌈coverLenPoly C2 t υ δ⌉₊ + t))
    + 31 * t + 1

theorem prop_decomp_poly_explicit :
    ∃ (Cerr C2 : ℝ), 0 < Cerr ∧ 0 < C2 ∧
      ∀ (t : ℕ) (υ δ η : ℝ), 1 ≤ t → 0 < υ → υ ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
        0 < η → η ≤ 1 / 2 →
        ∀ (M₀ : ℕ), winBoundPoly C2 t υ δ ≤ M₀ →
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
  obtain ⟨C2, hC2pos, hCov⟩ := covering_per_seq_explicit
  refine ⟨9 * Ccb + 19, C2, by positivity, hC2pos, ?_⟩
  intro t υ δ η ht hυ hυ2 hδ hδ2 hη hη2 M₀ hM₀ μ _inst hμ
  simp only [winBoundPoly] at hM₀
  set ℓ := ⌈coverLenPoly C2 t υ δ⌉₊ with hℓdef
  set K := 2 * ℓ + t with hKdef
  set D := K + markerDefPoly t ℓ K with hDdef
  have hM : 2 * t * D + 6 * D + 31 * t + 1 ≤ M₀ := by exact_mod_cast hM₀
  have hℓD : ℓ ≤ D := by omega
  have hmD : markerDefPoly t ℓ K ≤ D := by omega
  have hℓtD : ℓ + t ≤ D := by omega
  have hKD : K ≤ D := by omega
  have hbnd1 : 2 * D + 6 * t + 1 ≤ M₀ := by omega
  have hbnd2 : 2 * t * D ≤ M₀ := by omega
  have hbnd3 : D + 30 * t ≤ M₀ := by omega
  have hℓge : coverLenPoly C2 t υ δ ≤ (ℓ : ℝ) := by rw [hℓdef]; exact Nat.le_ceil _
  obtain ⟨E, ι₁, fι₁, base₁, height₁, hEdef, hEμ, hTB₁, hclosed₁, hheight₁,
    hbasedef₁, hfloordef₁, hPS₁, hdisj₁, hEdisj₁, hcover₁⟩ :=
    hCov t υ δ ht hυ hυ2 hδ hδ2 ℓ (by simpa [coverLenPoly] using hℓge) μ
  set Ξ : Set Cfg :=
      (E ∪ ⋃ τ : ι₁, ⋃ i ∈ Finset.range (height₁ τ), towerFloor (base₁ τ) i)ᶜ
    with hΞdef_eq
  have hEK : Defined K E := hEdef.mono (by omega)
  have hUdef : Defined K (⋃ τ : ι₁, ⋃ i ∈ Finset.range (height₁ τ),
      towerFloor (base₁ τ) i) :=
    defined_iUnion (fun τ => defined_biUnion_finset _
      (fun i hi => (hfloordef₁ τ i (Finset.mem_range.mp hi)).mono (by omega)))
  have hΞdefK : Defined K Ξ := by
    rw [hΞdef_eq]; exact defined_compl (defined_union hEK hUdef)
  have hΞsub : Ξ ⊆ Xaperl t ℓ := by
    intro x hx
    rw [hΞdef_eq] at hx
    by_contra hxa
    exact hx (hcover₁ hxa)
  have hcompl : E ∪ (⋃ τ : ι₁, ⋃ i ∈ Finset.range (height₁ τ),
      towerFloor (base₁ τ) i) = Ξᶜ := by
    rw [hΞdef_eq, compl_compl]
  obtain ⟨Z, hZmeas, hZdef, hZsub, hZfindep, hZsat⟩ :=
    marker_lemma_poly_explicit t ℓ K Ξ hΞdefK hΞsub
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
      (fun τ i hi => (hfloordef₁ τ i hi).mono hℓtD) hclosed₁ hdisj₁ hEμ hZsub hZdisj
      i 0 hi2t h02t hsub
    rwa [h0img] at key
  exact prop_decomp_core ht hυ hδ hη hμ hCcb (hZdef.mono hmD) (hΞdefK.mono hKD)
    hℓD hbnd1 hbnd3
    hZfindep hZsat hEdef hEμ hTB₁ hclosed₁ hheight₁
    (fun τ i hi => (hfloordef₁ τ i hi).mono hℓtD) hPS₁ hdisj₁ hEdisj₁ hcompl hcb

end LamplighterStability.Dynamics
