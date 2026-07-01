import Mathlib
import RequestProject.TowerBridge
import RequestProject.TowerToRep
import RequestProject.MeasureInstantiation

/-!
# Section 5 resolution of identity at the tower level

For a tower partition `(e, base, height)` of the PVM-induced spectral measure of
a commuting family `B` of Hermitian involutions, this file packages the
**tower-level** resolution of identity used by the final aggregate gluing
(`Section5.aggregate_block_rep`): the `Option ιτ`-indexed family

```
G none      = E_e                              (the error block)
G (some τ)   = P_τ = ∑_{i<height τ} E_{floor τ i}   (the τ-th tower block)
```

is a resolution of identity by pairwise-orthogonal Hermitian idempotents.  This
groups the *floor-level* resolution `Edef_partition_resolution` into tower
blocks, which is the form the per-tower block representation
(`block_rep_of_approx_tower`) feeds into.
-/

namespace LamplighterStability.MeasureBridge

open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureInstantiation
open scoped BigOperators
open Matrix

variable {d : ℕ}

/-- The tower-level resolution family: the error block `E_e` together with the
tower supports `P_τ = ∑_{i<height τ} E_{floor τ i}`. -/
noncomputable def towerResG (m : ℕ) (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    {ιτ : Type} (e : Set Cfg) (base : ιτ → Set Cfg) (height : ιτ → ℕ) :
    Option ιτ → Matrix (Fin d) (Fin d) ℂ :=
  fun s => s.elim (Edef (m + 1) (EpatB (m + 1) B) e)
    (fun τ => towerSupport (height τ)
      (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) i)))

/-
**Tower-level resolution of identity.**  The family `towerResG` consists of
pairwise-orthogonal Hermitian idempotents summing to `1`.
-/
set_option maxHeartbeats 1000000 in
theorem towerResG_resolution (m : ℕ) (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {e : Set Cfg} {ιτ : Type} [Fintype ιτ] {base : ιτ → Set Cfg} {height : ιτ → ℕ}
    (hpart : IsTowerPartition e base height)
    (hedef : Defined (m + 1) e)
    (hfloordef : ∀ τ i, i < height τ → Defined (m + 1) (towerFloor (base τ) i)) :
    (∀ s, (towerResG m B e base height s).IsHermitian) ∧
    (∀ s, IsIdempotentElem (towerResG m B e base height s)) ∧
    (∑ s, towerResG m B e base height s = 1) ∧
    (∀ s s', s ≠ s' → towerResG m B e base height s
        * towerResG m B e base height s' = 0) := by
  refine' ⟨ fun s => _, fun s => _, _, _ ⟩;
  · cases s <;> simp +decide [ towerResG ];
    · exact Edef_isProj _ _ hBh hB2 hBc _ |>.1;
    · apply_rules [ towerSupport_isHermitian, Edef_floors_pairwiseOrthProj ];
      exact hpart.2.2 _;
  · rcases s with ( _ | τ ) <;> simp +decide [ *, towerResG ];
    · exact LamplighterStability.MeasureBridge.Edef_isProj ( m + 1 ) B hBh hB2 hBc e |>.2;
    · exact towerSupport_idem ( Edef_floors_pairwiseOrthProj ( m + 1 ) ( height τ ) B hBh hB2 hBc ( hpart.2.2 τ ) );
  · rw [Fintype.sum_option]
    exact Edef_partition_resolution (m + 1) B hpart hedef hfloordef
  · rintro ( _ | s ) ( _ | t ) <;> simp +decide [ towerResG ];
    · have h_disjoint : ∀ i < height t, Disjoint e (towerFloor (base t) i) := by
        intro i hi; have := hpart.2.1; simp_all +decide [ Set.disjoint_left ] ;
        intro x hx; replace this := Set.ext_iff.mp this x; simp_all +decide [ Set.mem_iUnion ] ;
      unfold towerSupport; simp +decide [ Finset.mul_sum ] ;
      exact Finset.sum_eq_zero fun i hi => Edef_mul_of_disjoint ( m + 1 ) B hB2 hBc <| h_disjoint i <| Finset.mem_range.mp hi;
    · -- By definition of `towerSupport`, we know that `towerSupport (height s) (fun i => Edef (m + 1) (EpatB (m + 1) B) ((L ^ i) '' base s))` is the sum of the projections onto the floors of the tower.
      have h_towerSupport : towerSupport (height s) (fun i => Edef (m + 1) (EpatB (m + 1) B) ((L ^ i) '' base s)) = ∑ i ∈ Finset.range (height s), Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base s) i) := by
        rfl;
      have h_disjoint : ∀ i < height s, Disjoint (towerFloor (base s) i) e := by
        have := hpart.2.1; simp_all +decide [ Set.disjoint_left ] ;
        intro i hi x hx; replace this := Set.ext_iff.mp this x; simp_all +decide [ Set.mem_iUnion ] ;
        exact this.mp ⟨ s, i, hi, hx ⟩;
      rw [ h_towerSupport, Finset.sum_mul ];
      exact Finset.sum_eq_zero fun i hi => Edef_mul_of_disjoint ( m + 1 ) B hB2 hBc ( h_disjoint i ( Finset.mem_range.mp hi ) );
    · intro hst
      have h_disjoint : ∀ i < height s, ∀ j < height t, Disjoint (towerFloor (base s) i) (towerFloor (base t) j) := by
        exact fun i hi j hj => hpart.1 s t i j hi hj ( by aesop );
      rw [ towerSupport, towerSupport ];
      rw [ Finset.sum_mul ];
      exact Finset.sum_eq_zero fun i hi => by rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_eq_zero fun j hj => Edef_mul_of_disjoint ( m + 1 ) B hB2 hBc ( h_disjoint i ( Finset.mem_range.mp hi ) j ( Finset.mem_range.mp hj ) ) ;

end LamplighterStability.MeasureBridge