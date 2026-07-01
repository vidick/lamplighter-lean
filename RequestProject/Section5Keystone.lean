import Mathlib
import RequestProject.ProjectionTowers
import RequestProject.TowerToRep
import RequestProject.TowerRep
import RequestProject.TowerLowd
import RequestProject.Section5BlockAlgebra
import RequestProject.Section5PerTower
import RequestProject.Section5Glue
import RequestProject.Section5Clb
import RequestProject.Section5Delta1
import RequestProject.Section5DeltaAgg
import RequestProject.Section5Delta2
import RequestProject.Section5Sign
import RequestProject.Section5Resolution
import RequestProject.MeasureBridge
import RequestProject.MeasureInstantiation
import RequestProject.MuInvariance

/-!
# Section 5 keystone: analytic helper lemmas for `tower_rep_final`

This file isolates the remaining analytic ingredients of the Section 5
keystone (`Section5.tower_rep_final`), so that the final assembly is pure wiring:

* `lem_lowd_uniform` / `block_rep_uniform` — the rounding lemma and the per-tower
  block representation with the **dimension-independent** constant made explicit
  (`300`, resp. `1200`), so a single constant works for every tower and every
  dimension.

* `delta2_aggregate` — the aggregate `δ₂` (closing-defect) bound: the sum over
  towers of the closing defects `‖T* P_{j-1} T − P_0‖²` is `O(δ + η + 1/t)`,
  via the short/long tower dichotomy (`lem:clb`/`lem:clb2`).
-/

namespace LamplighterStability

open scoped BigOperators
open Matrix
open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureBridge LamplighterStability.MeasureInstantiation

/-- **Uniform-constant `lem:lowd`.**  The rounding lemma `lem_lowd` with the
dimension-independent constant `300` made explicit. -/
theorem lem_lowd_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ} {δ₁ δ₂ : ℝ}
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (h : IsApproxClosedProjTower j P R δ₁ δ₂) :
    ∃ (P' : ℕ → Matrix ι ι ℂ) (R' : Matrix ι ι ℂ),
      IsClosedProjTower j P' R' ∧
      (∀ i < j, ProjLE (P' i) (P i)) ∧
      (R' * (1 - towerSupport j P') = 1 - towerSupport j P') ∧
      TowerClose j P P' R R'
        (300 * ((j : ℝ) * δ₁)) (300 * ((j : ℝ) ^ 2 * δ₁ + δ₂)) := by
  obtain ⟨P', hP'proj, hP'le, hP'rank, hP'sumle, hP'gap⟩ := claim_p_bound j P h.1;
  obtain ⟨V, hsrc, hrng, hsvd⟩ := exists_rounding_isometries h.2.1 hP'proj hP'rank;
  refine' ⟨ P', roundedR j P' V, _, _, _, _, _ ⟩;
  · refine' ⟨ _, _ ⟩;
    · refine' ⟨ _, _ ⟩;
      · exact ⟨ hP'proj, subproj_orth h.1 hP'proj hP'le ⟩;
      · refine' ⟨ roundedR_unitary hP'proj _ hsrc hrng, _ ⟩;
        · exact subproj_orth h.1 hP'proj hP'le;
        · intro i hi;
          convert roundedR_conj_proj hP'proj ( subproj_orth h.1 hP'proj hP'le ) hsrc hrng ( show i < j from Nat.lt_of_succ_lt hi ) using 1;
          unfold cyc; aesop;
    · intro hj;
      convert roundedR_conj_proj hP'proj ( subproj_orth h.1 hP'proj hP'le ) hsrc hrng ( Nat.sub_lt hj zero_lt_one ) using 1;
      rcases j with ( _ | _ | j ) <;> simp_all +decide [ cyc ];
  · exact hP'le;
  · exact roundedR_comp hP'proj ( subproj_orth h.1 hP'proj hP'le ) hsrc;
  · refine' le_trans _ ( mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( trace_gap_bound h ) ( Nat.cast_nonneg _ ) ) ( by norm_num ) );
    refine' le_trans _ ( mul_le_mul_of_nonneg_left hP'sumle ( by norm_num ) );
    rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by rw [ ← neg_sub, normHS_neg ] ; exact le_mul_of_one_le_left ( sq_nonneg _ ) ( by norm_num ) ;
  · convert roundedR_close2 h.2.1 hδ₁ hδ₂ h.1.1 h.1.2 hP'proj ( subproj_orth h.1 hP'proj hP'le ) hsrc hrng _ _ _ hsvd using 1;
    · exact le_trans ( by simpa only [ normHS_sub_comm ] using hP'sumle ) ( mul_le_mul_of_nonneg_left ( trace_gap_bound h ) ( Nat.cast_nonneg _ ) );
    · exact h.2.2.1;
    · rcases j with ( _ | j ) <;> simp_all +decide [ IsApproxClosedProjTower ]

/-- **Uniform-constant per-tower block representation.**  Same content as
`block_rep_of_approx_tower`, with the dimension-independent constant `1200` made
explicit, so a single constant works for every tower. -/
theorem block_rep_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    {j : ℕ} (hj : 0 < j) {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ} {δ₁ δ₂ : ℝ}
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂) (hτ : IsApproxClosedProjTower j P R δ₁ δ₂)
    {B : Matrix ι ι ℂ} {x : ℕ → Bool}
    (hsign : ∀ i < j, B * P i = signC (x i) • P i) :
    ∃ A V : Matrix ι ι ℂ,
      towerSupport j P * A = A ∧ A * towerSupport j P = A ∧
      A.IsHermitian ∧ A * A = towerSupport j P ∧
      towerSupport j P * V = V ∧ V * towerSupport j P = V ∧
      V * Vᴴ = towerSupport j P ∧
      (∀ i : ℕ, Commute A (V ^ i * A * Vᴴ ^ i)) ∧
      (∀ i : ℕ, Commute A (Vᴴ ^ i * A * V ^ i)) ∧
      normHS (towerSupport j P * B * towerSupport j P - A) ^ 2
        ≤ 1200 * ((j : ℝ) * δ₁) ∧
      normHS (towerSupport j P * R * towerSupport j P - V) ^ 2
        ≤ 1200 * ((j : ℝ) ^ 2 * δ₁ + δ₂) := by
  obtain ⟨P', R', hclosed, hP'le, hRcomp, hTC⟩ := lem_lowd_uniform hδ₁ hδ₂ hτ
  set hPorig := hτ.1
  set hP' := hclosed.1.1
  set hP'proj := hP'.1
  set hGproj : IsProj (towerSupport j P) := ⟨towerSupport_isHermitian hPorig, towerSupport_idem hPorig⟩
  set hGabs : ∀ k < j, towerSupport j P * P' k = P' k := fun k hk => towerSupport_mul_subproj hPorig hP'proj hP'le hk;
  refine' ⟨ blockA j P' ( towerSupport j P ) x, blockV j P' ( towerSupport j P ) R', _, _, _, _, _, _ ⟩;
  any_goals rw [ blockA_supp_left ];
  any_goals rw [ blockV_supp_right ];
  any_goals assumption;
  · apply blockA_supp_right;
    · exact hP';
    · exact hGproj;
    · exact hGabs;
  · apply blockA_isHermitian;
    · exact hP';
    · exact hGproj;
  · apply blockA_sq;
    · exact hP';
    · exact hGproj;
    · exact hGabs;
  · rw [ blockV_supp_left ];
    · exact hGproj;
    · exact hGabs;
    · exact hclosed;
    · exact hj;
  · refine' ⟨ rfl, _, _, _, _, _ ⟩;
    · apply blockV_unitary;
      · exact hP';
      · exact hGproj;
      · exact hGabs;
      · exact hclosed;
      · exact hj;
    · apply_rules [ LamplighterStability.blockA_blockV_commute, LamplighterStability.blockA_blockVstar_commute ];
    · exact fun i => blockA_blockVstar_commute hP' hGproj hGabs hclosed hj x i;
    · have := blockA_close hPorig hP'proj hP'le hsign hTC.1;
      nlinarith [ this, mul_nonneg (Nat.cast_nonneg j) hδ₁ ];
    · have := blockV_close hj hPorig hclosed hP'le hTC.1 hTC.2;
      nlinarith [ this, show ( j : ℝ ) ≥ 1 by norm_cast, mul_nonneg (Nat.cast_nonneg j) hδ₁,
        mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg j)) hδ₁, hδ₂ ]

/-- **Aggregate `δ₂` (closing-defect) bound (`lem:clb`/`lem:clb2`).**  For a tower
partition of the PVM-induced measure of a commuting family `B` of Hermitian
involutions, the sum over towers of the closing defects
`‖T* P_{j-1} T − P_0‖²` (where `P_i = Edef(towerFloor (base τ) i)`,
`j = height τ`) is `O(δ + η + 1/t)`, using the dichotomy: short towers
(`DeltaClosed δ`) contribute `O(δ + η)`, long towers (`t ≤ height < 6t+1`)
contribute `O(η + 1/t)`.  The constant `Cd` is universal. -/
theorem delta2_aggregate :
    ∃ Cd : ℝ, 0 < Cd ∧
      ∀ {d : ℕ} [NeZero d] {m t : ℕ}, 1 ≤ t →
        ∀ {δ η : ℝ}, 0 < δ → δ ≤ 1 / 2 → 0 < η → η ≤ 1 / 2 →
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
          (∀ τ, height τ < m + 1) →
          (∑ x : Win m → Bool,
              normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (cyl m x) * T
                - Edef (m + 1) (EpatB (m + 1) B)
                    ((L : Equiv.Perm Cfg) '' cyl m x)) ^ 2 ≤ η) →
          ∑ τ : ιτ,
              (if 0 < height τ then
                normHS (star T *
                    Edef (m + 1) (EpatB (m + 1) B)
                      (towerFloor (base τ) (height τ - 1)) * T
                  - Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) 0)) ^ 2
              else 0)
            ≤ Cd * (δ + η + 1 / (t : ℝ)) := by
  refine ⟨16, by norm_num, ?_⟩
  intro d _ m t ht δ η hδ hδ2 hη hη2 T hTl hTr B hBh hB2 hBc e ιτ _ base height
    hpart hedef hfloordef hdich hsing hheight hopdef
  -- per-tower uniform bound, summed
  have hstep : ∀ τ : ιτ,
      (if 0 < height τ then
          normHS (star T * Edef (m + 1) (EpatB (m + 1) B)
              (towerFloor (base τ) (height τ - 1)) * T
            - Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) 0)) ^ 2
        else 0)
        ≤ 4 * (∑ i ∈ Finset.range (height τ),
              normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) i) * T
                - Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) (i + 1))) ^ 2)
          + (4 * δ + 4 / (t : ℝ)) * (∑ i ∈ Finset.range (height τ),
              (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) i)).toReal) := by
    intro τ
    exact keyD2g_uniform_le ht hTl hTr B hBh hB2 hBc hδ.le
      (fun i hi => hfloordef τ i hi) (hdich τ)
  -- aggregate the two right-hand sums
  have hft : ∑ τ : ιτ, ∑ i ∈ Finset.range (height τ),
      normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) i) * T
        - Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) (i + 1))) ^ 2 ≤ 4 * η :=
    floor_equiv_aggregate m hTl hTr B hBh hB2 hBc hpart hfloordef hopdef
  have hmu : ∑ τ : ιτ, ∑ i ∈ Finset.range (height τ),
      (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) i)).toReal ≤ 1 :=
    sum_floor_measure_le_one B hBh hB2 hBc hpart hfloordef
  have hcoef : (0 : ℝ) ≤ 4 * δ + 4 / (t : ℝ) := by positivity
  have hsum_le : ∑ τ : ιτ,
        (if 0 < height τ then
            normHS (star T * Edef (m + 1) (EpatB (m + 1) B)
                (towerFloor (base τ) (height τ - 1)) * T
              - Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) 0)) ^ 2
          else 0)
        ≤ ∑ τ : ιτ,
            (4 * (∑ i ∈ Finset.range (height τ),
                  normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) i) * T
                    - Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) (i + 1))) ^ 2)
              + (4 * δ + 4 / (t : ℝ)) * (∑ i ∈ Finset.range (height τ),
                  (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) i)).toReal)) :=
        Finset.sum_le_sum (fun τ _ => hstep τ)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum_le
  have h2 : (4 * δ + 4 / (t : ℝ)) * (∑ τ : ιτ, ∑ i ∈ Finset.range (height τ),
              (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) i)).toReal)
            ≤ (4 * δ + 4 / (t : ℝ)) * 1 :=
    mul_le_mul_of_nonneg_left hmu hcoef
  have hinvpos : (0 : ℝ) ≤ 1 / (t : ℝ) := by positivity
  have h1 : 4 * (∑ τ : ιτ, ∑ i ∈ Finset.range (height τ),
        normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) i) * T
          - Edef (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) (i + 1))) ^ 2)
      ≤ 4 * (4 * η) := by linarith [hft]
  rw [mul_one] at h2
  refine hsum_le.trans (le_trans (add_le_add h1 h2) ?_)
  have e1 : (4 : ℝ) / (t : ℝ) = 4 * (1 / (t : ℝ)) := by ring
  rw [e1]
  nlinarith [hδ.le, hinvpos]

end LamplighterStability
