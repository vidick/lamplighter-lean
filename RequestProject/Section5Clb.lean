import Mathlib
import RequestProject.Foundations
import RequestProject.MeasureBridge
import RequestProject.MeasureInstantiation
import RequestProject.PVMAlgebra
import RequestProject.TowerBridge

/-!
# Section 5 bridge: symmetric-difference Hilbert–Schmidt identity for `Edef`
(`lem:clb2` core)

This file proves the **exact** identity that converts a measure-theoretic
statement about a pair of `M`-definable sets `S, T` into a Hilbert–Schmidt
distance between their spectral projections `Edef M (EpatB M B) ·`:

```
‖E_S − E_T‖²_HS = μ(S ∖ T) + μ(T ∖ S) = μ(S △ T),
```

where `μ = pvmMeasure M (EpatB M B)`.  Both sides are computed atom-by-atom: the
projections `E_{S∖T}` and `E_{T∖S}` are orthogonal (the underlying pattern sets
are disjoint), so the squared HS distance is just the sum of their normalized
traces, which are the corresponding measures by `pvmMeasure_defined_toReal`.

This is the matrix-side input the Section 5 per-tower construction needs to bound
the closing defect `‖T* E_{L^{j-1}b} T − E_b‖²` (`lem:clb`, `lem:clb2`) from the
measure-level `DeltaClosed` hypothesis.
-/

namespace LamplighterStability.MeasureBridge

open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureInstantiation
open scoped BigOperators ENNReal
open Matrix

variable {d : ℕ}

/-
For an `M`-definable set `T`, the patterns of `S ∖ T` are exactly the
patterns of `S` that are not patterns of `T`.  (An `M`-cylinder is an atom, so it
is either contained in `T` or disjoint from it.)
-/
lemma patternsOf_diff (M : ℕ) {S T : Set Cfg} (hT : Defined M T) :
    patternsOf M (S \ T) = patternsOf M S \ patternsOf M T := by
  ext p; simp [patternsOf];
  constructor;
  · intro h;
    exact ⟨ fun x hx => h hx |>.1, fun hx => by obtain ⟨ x, hx' ⟩ := cyl_nonempty M p; exact h hx' |>.2 ( hx hx' ) ⟩;
  · intro hp x hx; have := hp.1 hx; simp_all +decide [ Set.subset_def ] ;
    obtain ⟨ y, hy, hy' ⟩ := hp.2; specialize hT x y; simp_all +decide [ cyl ] ;

/-
The difference of two `Edef` projections of `M`-definable sets is the
difference of the projections of the (disjoint) set differences.
-/
lemma Edef_sub_eq (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    {S T : Set Cfg} (hS : Defined M S) (hT : Defined M T) :
    Edef M (EpatB M B) S - Edef M (EpatB M B) T
      = Edef M (EpatB M B) (S \ T) - Edef M (EpatB M B) (T \ S) := by
  unfold Edef; rw [patternsOf_diff M hT, patternsOf_diff M hS]
  rw [← Finset.sum_inter_add_sum_diff (patternsOf M S) (patternsOf M T) (EpatB M B),
      ← Finset.sum_inter_add_sum_diff (patternsOf M T) (patternsOf M S) (EpatB M B),
      Finset.inter_comm (patternsOf M T) (patternsOf M S)]
  abel

/-
**`lem:clb2` core (trace form).**  The squared Hilbert–Schmidt distance
between the spectral projections of two `M`-definable sets is the sum of the
normalized traces of the projections of the two set differences.
-/
lemma Edef_sub_normHS_sq (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {S T : Set Cfg} (hS : Defined M S) (hT : Defined M T) :
    normHS (Edef M (EpatB M B) S - Edef M (EpatB M B) T) ^ 2
      = ntrace (Edef M (EpatB M B) (S \ T))
        + ntrace (Edef M (EpatB M B) (T \ S)) := by
  have h_proj : IsProj (Edef M (EpatB M B) (S \ T)) ∧ IsProj (Edef M (EpatB M B) (T \ S)) := by
    exact ⟨ Edef_isProj M B hBh hB2 hBc _, Edef_isProj M B hBh hB2 hBc _ ⟩;
  rw [ Edef_sub_eq M B hS hT ];
  rw [ normHS_sq_eq_ntrace, ← ntrace_add ];
  have h_mul : Edef M (EpatB M B) (S \ T) * Edef M (EpatB M B) (T \ S) = 0 ∧ Edef M (EpatB M B) (T \ S) * Edef M (EpatB M B) (S \ T) = 0 := by
    apply And.intro;
    · apply Edef_mul_of_disjoint M B hB2 hBc (disjoint_sdiff_sdiff);
    · apply Edef_mul_of_disjoint M B hB2 hBc (disjoint_sdiff_sdiff.symm);
  simp_all +decide [ sub_mul, mul_sub, IsProj ];
  simp_all +decide [ IsIdempotentElem.eq, Matrix.IsHermitian ]

/-
**`lem:clb2` core (measure form).**  The squared Hilbert–Schmidt distance
between the spectral projections of two `M`-definable sets equals the measure of
their symmetric difference.
-/
lemma Edef_sub_normHS_sq_measure (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {S T : Set Cfg} (hS : Defined M S) (hT : Defined M T) :
    normHS (Edef M (EpatB M B) S - Edef M (EpatB M B) T) ^ 2
      = (pvmMeasure M (EpatB M B) (S \ T)).toReal
        + (pvmMeasure M (EpatB M B) (T \ S)).toReal := by
  convert Edef_sub_normHS_sq M B hBh hB2 hBc hS hT using 1;
  congr! 1;
  · convert pvmMeasure_defined_toReal M ( EpatB M B ) ( fun p => EpatB_isHermitian M B hBh hBc p ) ( fun p => EpatB_isIdempotent M B hB2 hBc p ) ( defined_diff hS hT ) using 1;
  · convert pvmMeasure_defined_toReal M ( EpatB M B ) ( fun p => EpatB_isHermitian M B hBh hBc p ) ( fun p => EpatB_isIdempotent M B hB2 hBc p ) ( defined_diff hT hS ) using 1

end LamplighterStability.MeasureBridge