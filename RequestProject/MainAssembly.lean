import Mathlib
import RequestProject.Foundations
import RequestProject.OrderTwoStability
import RequestProject.CommutingProjections
import RequestProject.MuInvariance
import RequestProject.PVMToMeasure
import RequestProject.TowerToRep
import RequestProject.TowerRounding
import RequestProject.TowerRep
import RequestProject.Section5Assembly
import RequestProject.MeasureFull
import RequestProject.BudgetLemmas
import RequestProject.Dynamics.PropDecompProof
import RequestProject.Dynamics.PropDecompPolyExplicit
import RequestProject.Dynamics.WindowBound

set_option maxHeartbeats 1000000

/-!
# Block C — the final assembly (`Proof of the main results`, Section 5)

This file assembles the proof of the main theorem
(`LamplighterStability.lamplighter_HS_stability`, Theorem 1.1) out of the
ingredients developed in the rest of the project, following Section 5 of the
paper *"Polynomial Hilbert–Schmidt stability of the lamplighter group"*.

The proof has the following structure (paper, Section 5):

1. **Pre-processing.**  Given a pair `(A,T)` of unitaries with `‖A²-1‖ ≤ ε` and
   small orbit commutators, one first applies the order-two stability lemma
   (DGLT Prop. 1.4, proved as `order_two_stability`) to replace `A` by a genuine
   order-two unitary `A₀` with `‖A-A₀‖ ≤ ε`.  This is the only step factored out
   at the top level here (`core_main`); the rest is bundled into
   `assembly_final`.

2. **`assembly_final`** packages everything after the order-two reduction, i.e.
   the genuinely new content of the paper:
   * replace `A₀,ᵢ = T^{-i}A₀T^i` by nearby *commuting* involutions `Bᵢ`
     (Chao et al., `chao_commuting_projections`);
   * form the ordered-atom PVM `E` of the `Bᵢ` and the induced probability
     measure `μ(b) = tr(E_b)`, which is `(M-1,ε'')`-invariant by
     `mu_invariance_measure` / `pvm_to_meas_le`;
   * apply the tower-decomposition black box `prop_decomp` to `μ`;
   * for each tower, build the approximate closed projection tower `(E_b,…;T)`,
     identify the sign pattern (`claim:b-B`), and round it to a representation
     via `rep_from_approx_tower` (`lem:tower-long` / `lem:tower-short`);
   * glue the per-tower representations by Pythagoras over the orthogonal
     decomposition `ℋ = ⨁_τ P_τℋ ⊕ E_eℋ`, and choose the parameters
     `t = ⌈Cκ⁻²⌉`, `δ = υ = cκ¹⁴` to obtain the final `κ/2` bounds.

   This single, faithfully-stated interface packages Block C; it is now fully
   proved, consuming `chao_commuting_projections`, the polynomial-window tower
   decomposition `prop_decomp_poly_explicit`, the closed-form window estimate
   `exists_window_const`, and the already-proved matrix toolkit.

The top-level theorem `core_main` (whose statement is identical to
`lamplighter_HS_stability`) is then `order_two_stability` followed by
`assembly_final`, and `lamplighter_HS_stability` itself is `core_main`.
-/

namespace LamplighterStability

open scoped BigOperators
open Matrix
open MeasureTheory
open LamplighterStability.Dynamics LamplighterStability.MeasureBridge
  LamplighterStability.MeasureInstantiation LamplighterStability.OrbitConstruction

/-- **Final assembly (everything after the order-two reduction).**

Given the parameters of Theorem 1.1, the original pair `(A,T)` of unitaries
satisfying the standing assumptions, *and* a genuine order-two unitary `A₀` with
`‖A-A₀‖ ≤ ε`, there exist unitaries `A', T'` with `A'² = 1`, commuting orbit,
and `‖A-A'‖ ≤ κ`, `‖T-T'‖ ≤ κ`.

This interface packages the genuinely new content of Section 5 (the dynamical
tower-decomposition construction).  It is stated over plain matrices (with
explicit unitarity hypotheses) so that it composes directly with
`order_two_stability`. -/
theorem assembly_final :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (κ : ℝ), 0 < κ → κ ≤ 1 / 2 →
        ∀ (M : ℕ) (ε : ℝ),
          M = ⌈C * κ ^ (-20 : ℤ) * Real.log (2 / κ)⌉₊ →
          ε = c * κ ^ 7 / (M : ℝ) ^ 2 →
          ∀ (d : ℕ) (A T : Matrix.unitaryGroup (Fin d) ℂ),
            normHS ((A : Matrix (Fin d) (Fin d) ℂ) ^ 2 - 1) ≤ ε →
            (∀ i : ℕ, i ≤ 2 * M →
              normHS (⁅(A : Matrix (Fin d) (Fin d) ℂ),
                (star (T : Matrix (Fin d) (Fin d) ℂ)) ^ i
                  * (A : Matrix (Fin d) (Fin d) ℂ)
                  * (T : Matrix (Fin d) (Fin d) ℂ) ^ i⁆) ≤ ε) →
            ∀ A₀ : Matrix (Fin d) (Fin d) ℂ,
              A₀ ∈ Matrix.unitaryGroup (Fin d) ℂ → A₀ ^ 2 = 1 →
              normHS ((A : Matrix (Fin d) (Fin d) ℂ) - A₀) ≤ ε →
              ∃ A' T' : Matrix.unitaryGroup (Fin d) ℂ,
                (A' : Matrix (Fin d) (Fin d) ℂ) ^ 2 = 1 ∧
                (∀ i : ℤ, Commute (A' : Matrix.unitaryGroup (Fin d) ℂ)
                  (T' ^ (-i) * A' * T' ^ i)) ∧
                normHS ((A : Matrix (Fin d) (Fin d) ℂ)
                    - (A' : Matrix (Fin d) (Fin d) ℂ)) ≤ κ ∧
                normHS ((T : Matrix (Fin d) (Fin d) ℂ)
                    - (T' : Matrix (Fin d) (Fin d) ℂ)) ≤ κ := by
  classical
  obtain ⟨Cerr, C2, hCerr, hC2pos, hPD⟩ := prop_decomp_poly_explicit
  obtain ⟨Cback, hCback, hTRF⟩ := Section5.tower_rep_final Cerr
  -- universal constants
  set C_t : ℝ := 8 * Cback + 8 with hC_tdef
  have hC_tpos : 0 < C_t := by positivity
  set D : ℝ := Cback * (C_t + 1) ^ 6 with hDdef
  have hDpos : 0 < D := by positivity
  set c : ℝ := 1 / (810016 * D + 1000) with hcdef
  have hcpos : 0 < c := by positivity
  have hc1000 : c ≤ 1 / 1000 := by
    rw [hcdef, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [hDpos]
  have hDc : D * c ≤ 1 / 810016 := by
    rw [hcdef, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hDpos]
  have hcD : D * (2 * c + 64800 * c ^ 2) ≤ 1 / 8 := by
    nlinarith [hDc, hc1000, hcpos, hDpos.le,
      mul_le_mul hDc hc1000 hcpos.le (by norm_num : (0 : ℝ) ≤ 1 / 810016)]
  have hCbackC : Cback ≤ C_t / 8 := by rw [hC_tdef]; nlinarith [hCback]
  -- the closed-form polynomial window constant
  obtain ⟨Cwin, hCwin0, hWin⟩ :=
    exists_window_const C2 C_t c hC2pos hC_tpos hcpos hc1000
  refine ⟨Cwin, c, hCwin0, hcpos, ?_⟩
  intro κ hκ0 hκ2 M ε hM hε d A T hsq hcomm A₀ hA₀u hA₀sq hA₀d
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- `d = 0`: everything over `Fin 0` is trivial (subsingleton, `normHS = 0`).
    subst hd
    refine ⟨A, T, Subsingleton.elim _ _, fun i => Subsingleton.elim _ _, ?_, ?_⟩
    · rw [sub_self, normHS_zero]; exact le_of_lt hκ0
    · rw [sub_self, normHS_zero]; exact le_of_lt hκ0
  · haveI : NeZero d := ⟨hd.ne'⟩
    -- parameter setup
    set t : ℕ := ⌈C_t / κ ^ 2⌉₊ with htdef
    set υ : ℝ := c * κ ^ 14 with hυdef
    -- window bounds from `exists_window_const`, transported to `t`, `υ`
    obtain ⟨hWinA, hWinB⟩ := hWin κ hκ0 hκ2
    have hMcast : Cwin * κ ^ (-20 : ℤ) * Real.log (2 / κ) ≤ (M : ℝ) := by
      rw [hM]; exact Nat.le_ceil _
    have hMge : winBoundPoly C2 t υ υ + 1 ≤ M := by
      have h : ((winBoundPoly C2 t υ υ + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
        push_cast; linarith [hWinA, hMcast]
      exact_mod_cast h
    have h6tge : 6 * t + 1 ≤ M := by
      have h : ((6 * t + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
        push_cast; linarith [hWinB, hMcast]
      exact_mod_cast h
    set m : ℕ := M - 1 with hmdef
    have hMm : M = m + 1 := by omega
    have h6tm : 6 * t ≤ m := by omega
    have hwin : winBoundPoly C2 t υ υ ≤ m := by omega
    set η : ℝ := 2592 * ((m : ℝ) + 1) ^ 4 * (5 * ε) ^ 2 with hηdef
    clear_value m
    clear hmdef hMcast hMge h6tge hWinA hWinB
    -- basic facts about κ and t
    have hκsq : κ ^ 2 ≤ 1 / 4 := by nlinarith [hκ0, hκ2]
    have hκ12 : κ ^ 12 ≤ 1 := pow_le_one₀ hκ0.le (by linarith)
    have hκ14 : κ ^ 14 ≤ 1 := pow_le_one₀ hκ0.le (by linarith)
    have ht : 1 ≤ t := Nat.one_le_ceil_iff.mpr (div_pos hC_tpos (by positivity))
    have htlb : C_t / κ ^ 2 ≤ (t : ℝ) := Nat.le_ceil _
    have htub : (t : ℝ) ≤ (C_t + 1) / κ ^ 2 := by
      have h1 : (t : ℝ) < C_t / κ ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
      have h2 : (1 : ℝ) ≤ 1 / κ ^ 2 := by rw [le_div_iff₀ (by positivity)]; nlinarith
      rw [add_div]; nlinarith
    -- ε reexpressed with `m`
    have hεeq : ε = c * κ ^ 7 / ((m : ℝ) + 1) ^ 2 := by
      rw [hε, hMm]; push_cast; ring
    have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hεpos : 0 < ε := by rw [hεeq]; positivity
    -- η value and bounds
    have hηval : η = 64800 * c ^ 2 * κ ^ 14 := by
      rw [hηdef, hεeq]; field_simp; ring
    have hη0 : 0 < η := by rw [hηval]; positivity
    have hη2 : η ≤ 1 / 2 := by
      rw [hηval]
      have hc2 : c ^ 2 ≤ 1 / 1000000 := by
        calc c ^ 2 ≤ (1 / 1000 : ℝ) ^ 2 := pow_le_pow_left₀ hcpos.le hc1000 2
          _ = 1 / 1000000 := by norm_num
      have h1 : c ^ 2 * κ ^ 14 ≤ 1 / 1000000 := by
        calc c ^ 2 * κ ^ 14 ≤ c ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hκ14 (by positivity)
          _ = c ^ 2 := mul_one _
          _ ≤ 1 / 1000000 := hc2
      calc 64800 * c ^ 2 * κ ^ 14 = 64800 * (c ^ 2 * κ ^ 14) := by ring
        _ ≤ 64800 * (1 / 1000000) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ ≤ 1 / 2 := by norm_num
    -- υ bounds
    have hυ0 : 0 < υ := by rw [hυdef]; positivity
    have hυ2 : υ ≤ 1 / 2 := by
      rw [hυdef]
      calc c * κ ^ 14 ≤ (1 / 1000 : ℝ) * 1 :=
            mul_le_mul hc1000 hκ14 (by positivity) (by norm_num)
        _ ≤ 1 / 2 := by norm_num
    -- commuting involutions + measure + operator defect
    obtain ⟨B, hBh, hB2, hBc, hclose, hAIM, hopdef⟩ :=
      measure_input_full m T hA₀u (by rw [pow_two] at hA₀sq; exact hA₀sq) A hA₀d
        (fun i hi => hcomm i (by rw [hMm]; omega))
    haveI hprob : IsProbabilityMeasure (pvmMeasure (m + 1) (EpatB (m + 1) B)) :=
      pvmMeasure_isProbability (m + 1) (EpatB (m + 1) B)
        (EpatB_isHermitian (m + 1) B hBh hBc)
        (EpatB_isIdempotent (m + 1) B hB2 hBc) (EpatB_sum (m + 1) B)
    -- apply the polynomial-window tower decomposition
    obtain ⟨e, hedef, hμe, ι, fι, base, height, hpart, hfloordef, hdich, hPS⟩ :=
      hPD t υ υ η ht hυ0 hυ2 hυ0 hυ2 hη0 hη2 m hwin
        (pvmMeasure (m + 1) (EpatB (m + 1) B)) hAIM
    haveI : Fintype ι := fι
    have hheight : ∀ τ, height τ < m + 1 := by
      intro τ; rcases hdich τ with ⟨h, _⟩ | ⟨_, h⟩ <;> omega
    obtain ⟨hTstar, hTstar'⟩ := Unitary.mem_iff.mp T.2
    -- the back-half construction
    obtain ⟨A', T', hA'2, hA'comm, hb1, hb2⟩ :=
      hTRF ht hυ0 hυ2 hυ0 hυ2 hη0 hη2 (T : Matrix (Fin d) (Fin d) ℂ)
        hTstar hTstar' B hBh hB2 hBc e ι base height hpart hedef hfloordef
        hdich hPS hμe hheight hopdef
    -- convert the squared bounds via the budget lemmas
    obtain ⟨hbud1, hbud2⟩ :=
      budget_main hκ0 hCback hCbackC hcpos hc1000 (by
        have h := hcD; rw [hDdef] at h; exact h) htlb htub
    -- rewrite `υ + υ + η` in the back-half bounds to the budget form
    have hsumeq : υ + υ + η = c * κ ^ 14 + c * κ ^ 14 + 64800 * c ^ 2 * κ ^ 14 := by
      rw [hυdef, hηval]
    have hB0A' : normHS (B (Section5.winCenter m)
        - (A' : Matrix (Fin d) (Fin d) ℂ)) ≤ κ / 2 := by
      have hsq : normHS (B (Section5.winCenter m)
          - (A' : Matrix (Fin d) (Fin d) ℂ)) ^ 2 ≤ (κ / 2) ^ 2 := by
        refine hb1.trans ?_
        rw [hsumeq, show ((κ / 2) ^ 2 : ℝ) = κ ^ 2 / 4 by ring]; exact hbud1
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsq
    have hTT' : normHS ((T : Matrix (Fin d) (Fin d) ℂ)
        - (T' : Matrix (Fin d) (Fin d) ℂ)) ≤ κ / 2 := by
      have hsq : normHS ((T : Matrix (Fin d) (Fin d) ℂ)
          - (T' : Matrix (Fin d) (Fin d) ℂ)) ^ 2 ≤ (κ / 2) ^ 2 := by
        refine hb2.trans ?_
        rw [hsumeq, show ((κ / 2) ^ 2 : ℝ) = κ ^ 2 / 4 by ring]; exact hbud2
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hsq
    -- the pre-processing closeness `‖A − B₀‖ ≤ κ/2`
    have hAB0 : normHS ((A : Matrix (Fin d) (Fin d) ℂ)
        - B (Section5.winCenter m)) ≤ κ / 2 := by
      have horbit0 : orbit T A₀ ((Section5.winCenter m : Win (m + 1)) : ℤ) = A₀ := by
        show orbit T A₀ (0 : ℤ) = A₀
        simp [orbit, Tz_zero]
      have hcl := hclose (Section5.winCenter m)
      rw [horbit0] at hcl
      have htri : normHS ((A : Matrix (Fin d) (Fin d) ℂ) - B (Section5.winCenter m))
          ≤ normHS ((A : Matrix (Fin d) (Fin d) ℂ) - A₀)
            + normHS (A₀ - B (Section5.winCenter m)) := by
        have := normHS_add_le ((A : Matrix (Fin d) (Fin d) ℂ) - A₀)
          (A₀ - B (Section5.winCenter m))
        simpa using this
      have hcl' : normHS (A₀ - B (Section5.winCenter m))
          ≤ 4 * ((2 * (m + 1) + 1 : ℕ) : ℝ) * (5 * ε) := by
        rw [normHS_sub_comm]; exact hcl
      calc normHS ((A : Matrix (Fin d) (Fin d) ℂ) - B (Section5.winCenter m))
          ≤ ε + 4 * ((2 * (m + 1) + 1 : ℕ) : ℝ) * (5 * ε) :=
            le_trans htri (add_le_add hA₀d hcl')
        _ ≤ κ / 2 := budget_close hκ0 hκ2 hcpos hc1000 hεeq
    refine ⟨A', T', hA'2, hA'comm, ?_, ?_⟩
    · calc normHS ((A : Matrix (Fin d) (Fin d) ℂ) - (A' : Matrix (Fin d) (Fin d) ℂ))
          ≤ normHS ((A : Matrix (Fin d) (Fin d) ℂ) - B (Section5.winCenter m))
            + normHS (B (Section5.winCenter m) - (A' : Matrix (Fin d) (Fin d) ℂ)) := by
            have := normHS_add_le ((A : Matrix (Fin d) (Fin d) ℂ) - B (Section5.winCenter m))
              (B (Section5.winCenter m) - (A' : Matrix (Fin d) (Fin d) ℂ))
            simpa using this
        _ ≤ κ / 2 + κ / 2 := add_le_add hAB0 hB0A'
        _ = κ := by ring
    · linarith [hTT']

/-- **Theorem 1.1** (main technical theorem), stated with the shared
`LamplighterStability.normHS`.  Identical content to
`lamplighter_HS_stability`; the latter is `core_main`. -/
theorem core_main :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (κ : ℝ), 0 < κ → κ ≤ 1 / 2 →
        ∀ (M : ℕ) (ε : ℝ),
          M = ⌈C * κ ^ (-20 : ℤ) * Real.log (2 / κ)⌉₊ →
          ε = c * κ ^ 7 / (M : ℝ) ^ 2 →
          ∀ (d : ℕ) (A T : Matrix.unitaryGroup (Fin d) ℂ),
            normHS ((A : Matrix (Fin d) (Fin d) ℂ) ^ 2 - 1) ≤ ε →
            (∀ i : ℕ, i ≤ 2 * M →
              normHS (⁅(A : Matrix (Fin d) (Fin d) ℂ),
                (star (T : Matrix (Fin d) (Fin d) ℂ)) ^ i
                  * (A : Matrix (Fin d) (Fin d) ℂ)
                  * (T : Matrix (Fin d) (Fin d) ℂ) ^ i⁆) ≤ ε) →
            ∃ (A' T' : Matrix.unitaryGroup (Fin d) ℂ),
              (A' : Matrix (Fin d) (Fin d) ℂ) ^ 2 = 1 ∧
              (∀ i : ℤ, Commute (A' : Matrix.unitaryGroup (Fin d) ℂ)
                (T' ^ (-i) * A' * T' ^ i)) ∧
              normHS ((A : Matrix (Fin d) (Fin d) ℂ)
                  - (A' : Matrix (Fin d) (Fin d) ℂ)) ≤ κ ∧
              normHS ((T : Matrix (Fin d) (Fin d) ℂ)
                  - (T' : Matrix (Fin d) (Fin d) ℂ)) ≤ κ := by
  obtain ⟨C, c, hC, hc, h⟩ := assembly_final
  refine ⟨C, c, hC, hc, ?_⟩
  intro κ hκ1 hκ2 M ε hM hε d A T hsq hcomm
  obtain ⟨A₀, hA₀u, hA₀sq, hA₀d⟩ :=
    order_two_stability (A : Matrix (Fin d) (Fin d) ℂ) A.2 hsq
  exact h κ hκ1 hκ2 M ε hM hε d A T hsq hcomm A₀ hA₀u hA₀sq hA₀d

end LamplighterStability
