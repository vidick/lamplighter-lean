import Mathlib
import RequestProject.Section5Glue
import RequestProject.TowerBridge
import RequestProject.TowerEquiv
import RequestProject.Section5Clb
import RequestProject.MeasureInstantiation

/-!
# Section 5: the aggregate equivariance (`δ₁`) bound

This file proves the bridge converting the **cylinder-level** operator
equivariance defect (the `η` hypothesis of `tower_rep_final`) into an aggregate
**floor-level** bound, via the cross-term-free `p_ortho` estimate.

* `Edef_defined_eq_sum_cyl` — for an `m`-definable set `S`,
  `Edef (m+1) E S = ∑_{x ∈ patternsOf m S} Edef (m+1) E (cyl m x)`.
* `Edef_Limage_eq_sum_cyl` — the shifted version
  `Edef (m+1) E (L '' S) = ∑_{x ∈ patternsOf m S} Edef (m+1) E (L '' cyl m x)`.
* `floor_defect_aggregate` — for any finite family of pairwise-disjoint
  `m`-definable sets `S k`,
  `∑_k ‖T* E(S k) T − E(L '' S k)‖² ≤ 4·∑_{x} ‖T* E(cyl m x) T − E(L '' cyl m x)‖²`.
-/

namespace LamplighterStability.MeasureBridge

open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureInstantiation
open scoped BigOperators
open Matrix

variable {d : ℕ}

/-
For an `m`-definable set `S`, the `(m+1)`-spectral projection of `S` is the
sum of those of the `m`-cylinders it contains.
-/
lemma Edef_defined_eq_sum_cyl (m : ℕ) (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    {S : Set Cfg} (hS : Defined m S) :
    Edef (m + 1) (EpatB (m + 1) B) S
      = ∑ x ∈ patternsOf m S, Edef (m + 1) (EpatB (m + 1) B) (cyl m x) := by
  convert Edef_biUnion_finset ( m + 1 ) B ( patternsOf m S ) ( fun x => cyl m x ) ?_ ?_ using 1;
  · convert defined_eq_biUnion_cyl hS using 1;
    constructor <;> intro h;
    · convert defined_eq_biUnion_cyl hS using 1;
    · congr;
  · exact fun x hx => Defined.mono ( Nat.le_succ _ ) ( defined_cyl _ _ );
  · exact fun k hk k' hk' h => cyl_disjoint h

/-
The shifted version of `Edef_defined_eq_sum_cyl`.
-/
lemma Edef_Limage_eq_sum_cyl (m : ℕ) (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    {S : Set Cfg} (hS : Defined m S) :
    Edef (m + 1) (EpatB (m + 1) B) ((L : Equiv.Perm Cfg) '' S)
      = ∑ x ∈ patternsOf m S,
          Edef (m + 1) (EpatB (m + 1) B) ((L : Equiv.Perm Cfg) '' cyl m x) := by
  convert Edef_biUnion_finset ( m + 1 ) B ( patternsOf m S ) ( fun x => ( L : Equiv.Perm Cfg ) '' cyl m x ) _ _ using 1;
  · rw [Dynamics.defined_eq_biUnion_cyl hS, Set.image_iUnion₂];
    rw [ ← Dynamics.defined_eq_biUnion_cyl hS ];
  · intro k hk;
    convert defined_shift ( defined_cyl m k ) 1 using 1;
  · exact fun k hk k' hk' hne => Set.disjoint_image_of_injective ( show Function.Injective L from Equiv.injective _ ) ( cyl_disjoint hne )

/-
**Aggregate equivariance (`δ₁`) bound.**  For a finite family of
pairwise-disjoint `m`-definable sets `S k`, the total floor-level equivariance
defect is at most four times the total cylinder-level defect (the `η` sum).
-/
lemma floor_defect_aggregate (m : ℕ)
    {T : Matrix (Fin d) (Fin d) ℂ} (_hT : star T * T = 1) (hT' : T * star T = 1)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {κ : Type*} [Fintype κ] (S : κ → Set Cfg)
    (hSdef : ∀ k, Defined m (S k))
    (hSdisj : ∀ k k', k ≠ k' → Disjoint (S k) (S k')) :
    ∑ k, normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (S k) * T
        - Edef (m + 1) (EpatB (m + 1) B) ((L : Equiv.Perm Cfg) '' S k)) ^ 2
      ≤ 4 * ∑ x : Win m → Bool,
          normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (cyl m x) * T
            - Edef (m + 1) (EpatB (m + 1) B) ((L : Equiv.Perm Cfg) '' cyl m x)) ^ 2 := by
  -- Apply `p_ortho_fintype` to the hypothesis `hSdisj`.
  have := p_ortho_fintype (fun x => star T * Edef (m + 1) (EpatB (m + 1) B) (cyl m x) * T)
      (fun x => Edef (m + 1) (EpatB (m + 1) B) ((L : Equiv.Perm Cfg) '' cyl m x))
      (fun x => by
        constructor <;> simp +decide [ *, IsIdempotentElem ];
        · simp +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
          simp +decide [ ← Matrix.mul_assoc, star_eq_conjTranspose ];
          rw [ Edef_isProj ( m + 1 ) B hBh hB2 hBc ( cyl m x ) |>.1 ];
        · simp +decide [ ← mul_assoc ];
          have := Edef_isIdempotent ( m + 1 ) B hB2 hBc ( cyl m x );
          simp_all +decide [ mul_assoc, IsIdempotentElem ]) (fun x => by
        apply_rules [ Edef_isProj ])
      (fun x y hxy => by
        convert congr_arg ( fun x => star T * x * T ) ( Edef_mul_of_disjoint ( m + 1 ) B hB2 hBc ( cyl_disjoint hxy ) ) using 1 ; simp +decide [ mul_assoc ];
        · simp +decide [ ← mul_assoc, hT' ];
        · simp +decide []) (fun x y hxy => by
        apply Edef_mul_of_disjoint (m + 1) B hB2 hBc (Set.disjoint_image_of_injective (L).injective (cyl_disjoint hxy)) |> fun h => h)
      (fun k => patternsOf m (S k)) (by
      exact fun i k a => patternsOf_disjoint (hSdisj i k a));
  convert this using 3;
  simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, Edef_defined_eq_sum_cyl m B ( hSdef _ ), Edef_Limage_eq_sum_cyl m B ( hSdef _ ) ]

/-
The `(i+1)`-st floor of a tower is the shift of its `i`-th floor.
-/
lemma towerFloor_succ (b : Set Cfg) (i : ℕ) :
    towerFloor b (i + 1) = (L : Equiv.Perm Cfg) '' towerFloor b i := by
  aesop


end LamplighterStability.MeasureBridge
