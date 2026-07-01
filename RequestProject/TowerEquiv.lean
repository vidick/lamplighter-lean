import Mathlib
import RequestProject.Foundations
import RequestProject.MuInvariance
import RequestProject.TowerLowd
import RequestProject.MeasureBridge
import RequestProject.MeasureInstantiation

/-!
# Matrix-level approximate `T`-equivariance of the PVM projections `Edef`

This file supplies the **matrix-side approximate equivariance bound** that the
Section 5 per-tower construction (`assembly_final`, building
`IsApproxClosedProjTower` for each tower) needs: conjugating the spectral
projection `Edef (cyl m b)` of a window cylinder by the unitary `T` is, up to a
controlled Hilbert–Schmidt error, the projection `Edef (L '' cyl m b)` of the
shifted cylinder.  The error is governed by the *same* per-coordinate
equivariance defect `‖T* B_k T − B_{k+1}‖` that controls the measure-invariance
defect in `approxInvMeasure_EpatB`.

The key elementary ingredient is the **per-pattern atom defect bound**
`atom_defect_le`: for two families `C, D` of Hermitian involutions,
`‖atom C x − atom D x‖_HS ≤ ∑_i ‖proj (C i) (x i) − proj (D i) (x i)‖_HS`,
proved by peeling the first factor and using that the projection factors are
Hilbert–Schmidt contractions (`normHS_proj_mul_le` / `normHS_mul_proj_le`).
Since each factor difference is `½` of `C_i − D_i`, this gives the clean
`½ ∑_i ‖C_i − D_i‖` corollary `atom_defect_le'`.
-/

namespace LamplighterStability

open scoped BigOperators
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-
The difference of two projection factors `½(1 + (-1)^b B)` is
`½(-1)^b (C − D)`; in Hilbert–Schmidt norm it is `½‖C − D‖`.
-/
lemma proj_sub_normHS (C D : Matrix ι ι ℂ) (b : Bool) :
    normHS (proj C b - proj D b) = (1 / 2) * normHS (C - D) := by
  unfold proj;
  cases b <;> simp +decide [ ← smul_sub, normHS_smul ];
  convert normHS_smul ( 2⁻¹ : ℂ ) ( -C + D ) using 1 <;> norm_num [ neg_add_eq_sub, smul_sub ];
  convert normHS_neg ( D - C ) using 1 ; simp +decide [ sub_eq_neg_add ]

/-
**Per-pattern atom defect bound.**  For families `C, D` of Hermitian
involutions (with `D` commuting), the Hilbert–Schmidt distance between the atoms
`atom C x` and `atom D x` is at most the sum over coordinates of the projection
factor distances.
-/
lemma atom_defect_le {n : ℕ} {C D : Fin n → Matrix ι ι ℂ}
    (hCh : ∀ i, (C i).IsHermitian) (hC2 : ∀ i, C i * C i = 1)
    (hDh : ∀ i, (D i).IsHermitian) (hD2 : ∀ i, D i * D i = 1)
    (hDc : ∀ i k, Commute (D i) (D k)) (x : Fin n → Bool) :
    normHS (atom C x - atom D x)
      ≤ ∑ i : Fin n, normHS (proj (C i) (x i) - proj (D i) (x i)) := by
  induction' n with n ih <;> simp_all +decide [ Fin.sum_univ_succ, atom_succ ];
  have h_triangle : normHS (proj (C 0) (x 0) * atom (fun i => C i.succ) (fun i => x i.succ) - proj (D 0) (x 0) * atom (fun i => D i.succ) (fun i => x i.succ))
        ≤ normHS (proj (C 0) (x 0) * (atom (fun i => C i.succ) (fun i => x i.succ) - atom (fun i => D i.succ) (fun i => x i.succ))) + normHS ((proj (C 0) (x 0) - proj (D 0) (x 0)) * atom (fun i => D i.succ) (fun i => x i.succ)) := by
          convert normHS_add_le _ _ using 2 ; simp +decide [ mul_sub, sub_mul ];
  refine le_trans h_triangle ?_;
  refine' add_comm ( normHS ( proj ( C 0 ) ( x 0 ) - proj ( D 0 ) ( x 0 ) ) ) _ ▸ add_le_add _ _;
  · refine' le_trans ( normHS_proj_mul_le _ ) _;
    · exact ⟨ proj_isHermitian ( hCh 0 ) _, proj_isIdempotent ( hC2 0 ) _ ⟩;
    · exact ih ( fun i => hCh i.succ ) ( fun i => hC2 i.succ ) ( fun i => hDh i.succ ) ( fun i => hD2 i.succ ) ( fun i k => hDc i.succ k.succ ) _;
  · apply normHS_mul_proj_le;
    exact ⟨ atom_isHermitian ( fun i => hDh _ ) ( fun i k => hDc _ _ ) _, atom_isIdempotent ( fun i => hD2 _ ) ( fun i k => hDc _ _ ) _ ⟩

/-
**Per-pattern atom defect bound (clean form).**  In terms of the generator
differences `C_i − D_i`, the atom defect is at most `½ ∑_i ‖C_i − D_i‖`.
-/
lemma atom_defect_le' {n : ℕ} {C D : Fin n → Matrix ι ι ℂ}
    (hCh : ∀ i, (C i).IsHermitian) (hC2 : ∀ i, C i * C i = 1)
    (hDh : ∀ i, (D i).IsHermitian) (hD2 : ∀ i, D i * D i = 1)
    (hDc : ∀ i k, Commute (D i) (D k)) (x : Fin n → Bool) :
    normHS (atom C x - atom D x)
      ≤ (1 / 2) * ∑ i : Fin n, normHS (C i - D i) := by
  refine' le_trans ( atom_defect_le hCh hC2 hDh hD2 hDc x ) _;
  rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i _ ↦ by rw [ proj_sub_normHS ] ;

end LamplighterStability

namespace LamplighterStability.MeasureInstantiation

open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureBridge
open scoped BigOperators
open Matrix

variable {d : ℕ}


end LamplighterStability.MeasureInstantiation