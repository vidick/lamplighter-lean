import Mathlib
import RequestProject.Section5Delta1
import RequestProject.Dynamics.TowerDecomp

/-!
# Section 5: the aggregate floor-equivariance (`δ₁`) bound for a tower partition

Specializing `floor_defect_aggregate` to the family of **all floors** of a tower
partition `(e, base, height)` gives the aggregate `O(η)` bound that controls the
sum of per-tower equivariance defects `δ₁^τ` in `tower_rep_final`:

```
∑_τ ∑_{i<height τ} ‖T* E_{floor τ i} T − E_{floor τ (i+1)}‖²  ≤  4·η,
```

where `η = ∑_x ‖T* E_{cyl x} T − E_{L·cyl x}‖²` is the cylinder-level operator
equivariance budget (the `hopdef` hypothesis of `tower_rep_final`).  The floors
of a partition are pairwise disjoint and `m`-definable, and
`towerFloor b (i+1) = L '' towerFloor b i`, so each summand is exactly a
`floor_defect_aggregate` term.
-/

namespace LamplighterStability.MeasureBridge

open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureInstantiation
open scoped BigOperators
open Matrix

variable {d : ℕ}

/-
**Aggregate floor-equivariance bound (`∑_τ δ₁^τ = O(η)`).**
-/
theorem floor_equiv_aggregate (m : ℕ)
    {T : Matrix (Fin d) (Fin d) ℂ} (hT : star T * T = 1) (hT' : T * star T = 1)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {e : Set Cfg} {ιτ : Type} [Fintype ιτ] {base : ιτ → Set Cfg} {height : ιτ → ℕ}
    (hpart : IsTowerPartition e base height)
    (hfloordef : ∀ τ i, i < height τ → Defined m (towerFloor (base τ) i))
    {η : ℝ}
    (hη : ∑ x : Win m → Bool,
            normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (cyl m x) * T
              - Edef (m + 1) (EpatB (m + 1) B) ((L : Equiv.Perm Cfg) '' cyl m x)) ^ 2 ≤ η) :
    ∑ τ : ιτ, ∑ i ∈ Finset.range (height τ),
        normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) i) * T
          - Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) (i + 1))) ^ 2
      ≤ 4 * η := by
  have := @LamplighterStability.MeasureBridge.floor_defect_aggregate;
  refine' le_trans _ ( mul_le_mul_of_nonneg_left hη zero_le_four );
  convert this m hT hT' B hBh hB2 hBc ( fun k : Σ τ : ιτ, Fin ( height τ ) => towerFloor ( base k.1 ) k.2 ) ( fun k => hfloordef k.1 k.2 k.2.isLt ) ( fun k k' hne => ?_ ) using 1;
  · simp +decide only [Finset.sum_sigma', ← towerFloor_succ];
    refine' Finset.sum_bij ( fun x _ => ⟨ x.fst, ⟨ x.snd, by
      exact Finset.mem_range.mp ( Finset.mem_sigma.mp ‹_› |>.2 ) ⟩ ⟩ ) _ _ _ _ <;> simp +decide;
    · grind;
    · exact fun b => ⟨ b.1, b.2, b.2.2, rfl ⟩;
  · rcases k with ⟨ τ, i ⟩ ; rcases k' with ⟨ τ', i' ⟩ ; simp +decide [ towerFloor ] at hne ⊢;
    by_cases h : τ = τ' <;> simp +decide [ h ] at hne ⊢;
    · subst h;
      convert hpart.1 τ τ i i' i.isLt i'.isLt ( by simpa [ Fin.ext_iff ] using hne ) using 1;
    · have := hpart.1 τ τ' i i' i.isLt i'.isLt; simp +decide [ h ] at this; exact this;

end LamplighterStability.MeasureBridge