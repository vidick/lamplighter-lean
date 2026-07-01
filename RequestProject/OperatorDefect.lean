import Mathlib
import RequestProject.MuInvariance
import RequestProject.MeasureBridge
import RequestProject.MeasureInstantiation

/-!
# Operator-side approximate `T`-invariance defect of the PVM `Edef`

This is the Hilbert–Schmidt (operator) analogue of `mu_invariance_measure`
(`MuInvariance.lean`), which controlled the *trace* (L¹) invariance defect that
defines `ApproxInvMeasure`.  Here we control the *operator* (HS, L²) defect

`∑_{x} ‖T* E_⟦x⟧ T − E_{L⟦x⟧}‖²_HS`

over all window cylinders `x : Win m → Bool`, which is the quantity that drives
the per-tower approximate-closedness defect `δ₁^τ` of Lemma `lem:clb` in
Section 5.

The proof is identical in shape to `approxInvMeasure_EpatB`: the marginalization
identities `Edef_cyl_eq` / `Edef_Lcyl_eq` rewrite each summand as an atom defect
of the middle sub-family `Bmid`, the reindexing `x ↦ x ∘ winEquiv⁻¹` matches the
two sums, and `mu_invariance_equivariance` supplies the final bound.
-/

namespace LamplighterStability.MeasureInstantiation

open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureBridge
open scoped BigOperators
open Matrix

variable {d : ℕ}

/-
**Operator (HS) invariance defect of `Edef`.**  For a commuting family `B`
of Hermitian involutions and a unitary `T`, the total Hilbert–Schmidt defect of
approximate `T`-invariance over all window cylinders is bounded by the matrix
equivariance defect `∑_k ‖T* Bmid_k T − Bmid_{k+1}‖²` of the middle sub-family.
-/
lemma operator_defect_le (m : ℕ)
    {T : Matrix (Fin d) (Fin d) ℂ} (hT : T ∈ unitary (Matrix (Fin d) (Fin d) ℂ))
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j)) :
    ∑ x : Win m → Bool,
        normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (cyl m x) * T
          - Edef (m + 1) (EpatB (m + 1) B) ((L : Equiv.Perm Cfg) '' cyl m x)) ^ 2
      ≤ ((2 * (m : ℝ) + 1) / 2) * ∑ k : Fin (2 * m + 1),
          normHS (star T * Bmid m B k.castSucc * T - Bmid m B k.succ) ^ 2 := by
  convert LamplighterStability.mu_invariance_equivariance hT (Bmid m B) (fun i => hBh _) (fun i => hB2 _) (fun i j => hBc _ _) using 1;
  · refine' Finset.sum_bij ( fun x _ => fun k => x ( winEquiv m |>.symm k ) ) _ _ _ _ <;> simp +decide;
    · exact fun a₁ a₂ h => funext fun x => by simpa using congr_fun h ( winEquiv m x ) ;
    · exact fun b => ⟨ fun k => b ( winEquiv m k ), by ext; simp +decide ⟩;
    · intro a; rw [ Edef_cyl_eq m B a, Edef_Lcyl_eq m B a ] ;
      rfl;
  · norm_cast

end LamplighterStability.MeasureInstantiation