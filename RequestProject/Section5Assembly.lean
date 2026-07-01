import Mathlib
import RequestProject.TowerBridge
import RequestProject.TowerEquiv
import RequestProject.TowerRep
import RequestProject.TowerRounding
import RequestProject.MuInvariance
import RequestProject.MeasureBridge
import RequestProject.MeasureInstantiation
import RequestProject.PVMAlgebra
import RequestProject.Section5BackHalf
import RequestProject.Section5PerTower
import RequestProject.Section5Sign
import RequestProject.Section5Clb
import RequestProject.Section5Delta1
import RequestProject.Section5DeltaAgg
import RequestProject.Section5Resolution
import RequestProject.Section5Aggregate
import RequestProject.Section5Glue
import RequestProject.Section5Keystone
import RequestProject.Section5KeystoneAssembly

/-!
# Section 5 back half: from a tower decomposition to a nearby representation

This file packages the genuinely new content of Section 5 of the paper
("Proof of the main results", the part *after* the order-two reduction, the
commuting-involution replacement, and the tower decomposition `prop_decomp`):
the construction of a nearby unitary representation of the lamplighter group out
of the measure-theoretic tower partition.

The single interface lemma is `tower_rep_final`.  Its inputs are exactly the
output of `prop_decomp` applied to the PVM-induced measure
`μ = pvmMeasure (m+1) (EpatB (m+1) B)` of a commuting family `B` of Hermitian
involutions, plus the matrix-side operator equivariance defect `hopdef` (the
Hilbert–Schmidt form of approximate `T`-invariance).  Its output is a pair of
unitaries `A', T'` realizing the lamplighter relations, with the two Pythagorean
closeness bounds

* `‖B₀ − A'‖²_HS ≤ Cback · t⁶ · (υ + δ + η)`,
* `‖T − T'‖²_HS  ≤ Cback · (1/t + t⁶·(υ + δ + η))`,

where `B₀ = B 0` is the center involution.  These are the paper's
`O(t⁶(υ+δ+η))` and `O(1/t + t⁶(υ+δ+η))` bounds (Lemmas `lem:tower-long`,
`lem:tower-short`, `lem:clb`, `lem:clb2`, Claim `claim:b-B`, Claim
`claim:approx_inv_supp`, and the final Pythagoras over
`Edef_partition_resolution`).

The parameter choice `t = ⌈Cκ⁻²⌉`, `δ = υ = cκ¹⁴`, `η = O(κ¹⁴)` turning these
into the final `κ/2` bounds is done by the caller (`assembly_final_exp` /
`assembly_final`), so this interface is shared verbatim by the exponential and
polynomial versions of the main theorem.
-/

namespace LamplighterStability.Section5

open scoped BigOperators
open Matrix
open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureBridge LamplighterStability.MeasureInstantiation

/-- **Section 5 back half (interface).**  From the tower decomposition of the
PVM-induced measure of a commuting family `B` of Hermitian involutions, build a
nearby lamplighter representation `(A', T')`.

`Cerr` is the constant from `prop_decomp`'s error-set measure bound; the produced
constant `Cback` depends only on `Cerr` (and is universal in everything else). -/
theorem tower_rep_final (Cerr : ℝ) :
    ∃ Cback : ℝ, 0 < Cback ∧
      ∀ {d : ℕ} [NeZero d] {m t : ℕ}, 1 ≤ t →
        ∀ {δ υ η : ℝ}, 0 < υ → υ ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 → 0 < η → η ≤ 1 / 2 →
        ∀ (T : Matrix (Fin d) (Fin d) ℂ),
          star T * T = 1 → T * star T = 1 →
        ∀ (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ),
          (∀ i, (B i).IsHermitian) → (∀ i, B i * B i = 1) →
          (∀ i j, Commute (B i) (B j)) →
        ∀ (e : Set Cfg) (ιτ : Type) [Fintype ιτ]
          (base : ιτ → Set Cfg) (height : ιτ → ℕ),
          IsTowerPartition e base height →
          Defined m e →
          (∀ τ i, i < height τ → Defined m (towerFloor (base τ) i)) →
          (∀ τ, (height τ < t ∧
                  DeltaClosed (pvmMeasure (m + 1) (EpatB (m + 1) B)) δ
                    (height τ) (base τ)) ∨
                (t ≤ height τ ∧ height τ < 6 * t + 1)) →
          (∀ τ, ProjSingleton (height τ) (base τ)) →
          (pvmMeasure (m + 1) (EpatB (m + 1) B) e).toReal
            ≤ Cerr * (t : ℝ) ^ 6 * (υ + δ + η) →
          (∀ τ, height τ < m + 1) →
          (∑ x : Win m → Bool,
              normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (cyl m x) * T
                - Edef (m + 1) (EpatB (m + 1) B)
                    ((L : Equiv.Perm Cfg) '' cyl m x)) ^ 2 ≤ η) →
          ∃ A' T' : Matrix.unitaryGroup (Fin d) ℂ,
            (A' : Matrix (Fin d) (Fin d) ℂ) ^ 2 = 1 ∧
            (∀ i : ℤ, Commute (A' : Matrix.unitaryGroup (Fin d) ℂ)
              (T' ^ (-i) * A' * T' ^ i)) ∧
            normHS (B (winCenter m) - (A' : Matrix (Fin d) (Fin d) ℂ)) ^ 2
              ≤ Cback * (t : ℝ) ^ 6 * (υ + δ + η) ∧
            normHS (T - (T' : Matrix (Fin d) (Fin d) ℂ)) ^ 2
              ≤ Cback * ((1 : ℝ) / (t : ℝ) + (t : ℝ) ^ 6 * (υ + δ + η)) := by
  obtain ⟨Cd, hCd, hdelta2⟩ := delta2_aggregate
  refine ⟨200000 * (|Cerr| + 1) * (Cd + 1),
    mul_pos (mul_pos (by norm_num) (by positivity)) (by linarith), ?_⟩
  intro d _ m t ht δ υ η hυ hυ2 hδ hδ2 hη hη2 T hTl hTr B hBh hB2 hBc e ιτ _ base height
    hpart hedef hfloordef hdich hsing herr hheight hopdef
  classical
  obtain ⟨hGh, hGi, hGsum, hGortho⟩ := towerResG_resolution m B hBh hB2 hBc hpart
    (Defined.mono (Nat.le_succ _) hedef)
    (fun τ i hi => Defined.mono (Nat.le_succ _) (hfloordef τ i hi))
  choose A V hAL hAR hAh hAsq hVL hVR hVstar hcomm hcomm' hbA hbT hboff using
    key_block_data m T hTl hTr B hBh hB2 hBc e base height hpart hsing
  have hN0 : 0 ≤ ntrace (towerResG m B e base height (none : Option ιτ)) :=
    ntrace_proj_nonneg (hGh none) (hGi none)
  have hntr : ntrace (towerResG m B e base height (none : Option ιτ))
      ≤ |Cerr| * (t : ℝ) ^ 6 * (υ + δ + η) := by
    have heq : ntrace (towerResG m B e base height (none : Option ιτ))
        = (pvmMeasure (m + 1) (EpatB (m + 1) B) e).toReal :=
      (pvmMeasure_defined_toReal (m + 1) (EpatB (m + 1) B)
        (fun p => EpatB_isHermitian (m + 1) B hBh hBc p)
        (fun p => EpatB_isIdempotent (m + 1) B hB2 hBc p)
        (Defined.mono (Nat.le_succ _) hedef)).symm
    rw [heq]
    exact le_trans herr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self Cerr) (by positivity)) (by linarith))
  have h6t : ∀ τ, (height τ : ℝ) ≤ 6 * (t : ℝ) := by
    intro τ
    rcases hdich τ with ⟨h, _⟩ | ⟨_, h⟩ <;>
      · have hh : height τ ≤ 6 * t := by omega
        exact_mod_cast hh
  have hd1 : ∑ τ, keyD1 m T B (base τ) (height τ) ≤ 4 * η :=
    key_d1_le_4eta m hTl hTr B hBh hB2 hBc hpart hfloordef hopdef
  have hd2 : ∑ τ, keyD2g m T B (base τ) (height τ) ≤ Cd * (δ + η + 1 / (t : ℝ)) := by
    have h := hdelta2 ht hδ hδ2 hη hη2 T hTl hTr B hBh hB2 hBc e ιτ base height hpart
      hedef hfloordef hdich hsing hheight hopdef
    simpa only [keyD2g, keyD2] using h
  have hBcomm : ∀ s, towerResG m B e base height s * B (winCenter m)
      = B (winCenter m) * towerResG m B e base height s := by
    intro s
    rcases s with _ | τ
    · simp only [towerResG, Option.elim_none]
      exact (Edef_commute_B (m + 1) B hBc (winCenter m) e).symm
    · simp only [towerResG, Option.elim_some, towerSupport, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ =>
        (Edef_commute_B (m + 1) B hBc (winCenter m) (towerFloor (base τ) i)).symm
  exact tower_rep_arith t ht hδ hυ hη Cerr Cd hCd.le
    (towerResG m B e base height) hGh hGi hGsum hGortho T (B (winCenter m)) hTl hTr
    A V hAL hAR hAh hAsq hVL hVR hVstar hcomm hcomm' hBcomm hN0 hntr
    height (fun τ => keyD1 m T B (base τ) (height τ))
    (fun τ => keyD2g m T B (base τ) (height τ))
    (fun τ => keyD1_nonneg m T B (base τ) (height τ))
    h6t hd1 hd2 hbA hbT hboff

end LamplighterStability.Section5
