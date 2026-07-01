import Mathlib
import RequestProject.Foundations
import RequestProject.PVMToMeasure
import RequestProject.PVMAlgebra
import RequestProject.ProjectionTowers
import RequestProject.MeasureBridge
import RequestProject.MeasureInstantiation
import RequestProject.Section5Clb
import RequestProject.Section5Delta1
import RequestProject.Section5DeltaAgg
import RequestProject.Dynamics.TowerDecomp
import RequestProject.Dynamics.ApproxInvMeasure
import RequestProject.Dynamics.TowerDecompAssembly

/-!
# Section 5: per-tower and aggregate closing-defect (`δ₂`) bounds (`lem:clb`/`lem:clb2`)

This file provides the analytic ingredients for `delta2_aggregate`
(the closing-defect aggregate of `Section5Keystone`).  The key trick is to bound
the closing defect of each tower in terms of:

* the per-floor equivariance terms
  `ft τ i = ‖T* E_{L^i b} T − E_{L^{i+1} b}‖²` (whose total over the whole tower
  partition is `≤ 4η` by `floor_equiv_aggregate`), and
* the floor measures `μ(L^i b)` (whose total over the whole partition is `≤ 1`).

For **short** (`δ`-closed) towers the closing defect is bounded via the
symmetric-difference identity `Edef_sub_normHS_sq_measure` plus telescoping of the
floor measures (avoiding any high-shift definability budget), and for **long**
towers (`height ≥ t`) via the average-plus-total-variation bound on the floor
measures.  Both cases yield the *uniform* per-tower bound `keyD2g_uniform_le`,
which sums to `O(δ + η + 1/t)`.
-/

namespace LamplighterStability

open scoped BigOperators
open Matrix
open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureBridge LamplighterStability.MeasureInstantiation

variable {d : ℕ}

/-
A `Defined m` set is measurable (it is a finite union of cylinders).
-/
lemma measurableSet_of_defined {m : ℕ} {S : Set Cfg} (hS : Defined m S) :
    MeasurableSet S := by
  convert defined_eq_biUnion_cyl hS ▸ MeasurableSet.biUnion ( Finset.countable_toSet _ ) fun b hb => measurableSet_cyl m b using 1

/-
**Average-plus-total-variation bound.**  For a real sequence and `i < j`,
the value `a i` is at most the average over `[0,j)` plus the total variation.
-/
lemma val_le_avg_add_tv (a : ℕ → ℝ) {j i : ℕ} (hi : i < j) :
    a i ≤ (∑ i' ∈ Finset.range j, a i') / (j : ℝ)
        + ∑ k ∈ Finset.range (j - 1), |a (k + 1) - a k| := by
  have := @abs_sub_le_sum_consecutive;
  rw [ div_add', le_div_iff₀ ] <;> try norm_num ; linarith;
  have := Finset.sum_le_sum fun i' ( hi' : i' ∈ Finset.range j ) => show a i ≤ a i' + ∑ k ∈ Finset.range ( j - 1 ), |a ( k + 1 ) - a k| from by linarith [ abs_le.mp ( this a hi ( Finset.mem_range.mp hi' ) ) ] ; ; norm_num [ mul_comm, Finset.sum_add_distrib ] at this ⊢ ; linarith;

/-
**Per-floor measure step bound.**  The change of the induced measure across
one floor is controlled by the corresponding squared equivariance defect.
-/
lemma meas_step_le_floorTerm {m : ℕ} {T : Matrix (Fin d) (Fin d) ℂ}
    (hTl : star T * T = 1) (hTr : T * star T = 1)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {S S' : Set Cfg} (hS : Defined (m + 1) S) (hS' : Defined (m + 1) S') :
    |(pvmMeasure (m + 1) (EpatB (m + 1) B) S').toReal
       - (pvmMeasure (m + 1) (EpatB (m + 1) B) S).toReal|
     ≤ normHS (star T * Edef (m + 1) (EpatB (m + 1) B) S * T
         - Edef (m + 1) (EpatB (m + 1) B) S') ^ 2 := by
  rw [ pvmMeasure_defined_toReal, pvmMeasure_defined_toReal ];
  any_goals assumption;
  · convert proj_diff_bound ( Edef ( m + 1 ) ( EpatB ( m + 1 ) B ) S' ) ( star T * Edef ( m + 1 ) ( EpatB ( m + 1 ) B ) S * T ) _ _ _ _ using 1;
    rw [ ntrace_conj_unitary ];
    exact ⟨ hTl, hTr ⟩;
    · rw [ ← normHS_neg, neg_sub ];
    · exact Edef_isHermitian _ _ hBh hBc _;
    · exact Edef_isIdempotent _ _ hB2 hBc _;
    · apply isHermitian_conj_unitary;
      exact Edef_isHermitian _ _ hBh hBc _;
    · convert isIdempotentElem_conj_unitary ( show T ∈ unitary ( Matrix ( Fin d ) ( Fin d ) ℂ ) from ⟨ hTl, hTr ⟩ ) ( Edef_isIdempotent ( m + 1 ) B hB2 hBc S ) using 1;
  · exact fun p => EpatB_isHermitian ( m + 1 ) B hBh hBc p;
  · exact fun p => EpatB_isIdempotent ( m + 1 ) B hB2 hBc p;
  · exact fun p => EpatB_isHermitian ( m + 1 ) B hBh hBc p;
  · exact fun p => EpatB_isIdempotent ( m + 1 ) B hB2 hBc p

/-
All floors `towerFloor b i` for `i ≤ j` are `(m+1)`-defined, given that the
floors `i < j` are `m`-defined (`towerFloor b j` is a one-step shift of
`towerFloor b (j-1)`).
-/
lemma floor_defined_succ {m : ℕ} {b : Set Cfg} {j : ℕ} (hj : 1 ≤ j)
    (hfloor : ∀ i, i < j → Defined m (towerFloor b i)) :
    ∀ i, i ≤ j → Defined (m + 1) (towerFloor b i) := by
  intro i hi; rcases lt_or_eq_of_le hi with hi | rfl <;> simp_all +decide [ towerFloor ] ;
  · exact Defined.mono ( Nat.le_succ _ ) ( hfloor i hi );
  · convert defined_shift ( hfloor ( i - 1 ) ( Nat.sub_lt hj zero_lt_one ) ) 1 using 1;
    cases i <;> simp_all +decide [ pow_succ', Set.image_image ]

/-- The squared HS norm of a floor projection is its induced measure. -/
lemma floor_normHS_sq_measure {m : ℕ}
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {S : Set Cfg} (hS : Defined (m + 1) S) :
    normHS (Edef (m + 1) (EpatB (m + 1) B) S) ^ 2
      = (pvmMeasure (m + 1) (EpatB (m + 1) B) S).toReal := by
  rw [normHS_sq_proj (Edef_isProj (m + 1) B hBh hB2 hBc S).1
        (Edef_isProj (m + 1) B hBh hB2 hBc S).2,
      pvmMeasure_defined_toReal (m + 1) (EpatB (m + 1) B)
        (EpatB_isHermitian (m + 1) B hBh hBc) (EpatB_isIdempotent (m + 1) B hB2 hBc) hS]

/-- The squared HS norm of a unitarily-conjugated floor projection is its
induced measure. -/
lemma conj_floor_normHS_sq_measure {m : ℕ} {T : Matrix (Fin d) (Fin d) ℂ}
    (hTl : star T * T = 1) (hTr : T * star T = 1)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {S : Set Cfg} (hS : Defined (m + 1) S) :
    normHS (star T * Edef (m + 1) (EpatB (m + 1) B) S * T) ^ 2
      = (pvmMeasure (m + 1) (EpatB (m + 1) B) S).toReal := by
  have hconj : normHS (star T * Edef (m + 1) (EpatB (m + 1) B) S * T)
      = normHS (Edef (m + 1) (EpatB (m + 1) B) S) := by
    have := normHS_unitary_conj (Unitary.star_mem (show T ∈ unitary (Matrix (Fin d) (Fin d) ℂ) from ⟨hTl, hTr⟩))
      (Edef (m + 1) (EpatB (m + 1) B) S)
    simpa using this
  rw [hconj, floor_normHS_sq_measure B hBh hB2 hBc hS]

/-
**Long-tower closing-defect bound (`lem:clb`).**
-/
lemma keyD2_long_le {m t : ℕ} (ht : 1 ≤ t) {T : Matrix (Fin d) (Fin d) ℂ}
    (hTl : star T * T = 1) (hTr : T * star T = 1)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {b : Set Cfg} {j : ℕ} (hj : t ≤ j)
    (hfloor : ∀ i, i < j → Defined m (towerFloor b i)) :
    normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (j - 1)) * T
        - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b 0)) ^ 2
      ≤ (4 / (t : ℝ)) * (∑ i ∈ Finset.range j,
            (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b i)).toReal)
        + 4 * ∑ i ∈ Finset.range j,
            normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i) * T
              - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (i + 1))) ^ 2 := by
  have h_keyD2 : normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (j - 1)) * T - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b 0)) ^ 2 ≤ 2 * (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b (j - 1))).toReal + 2 * (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b 0)).toReal := by
    have h_step : normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (j - 1)) * T - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b 0)) ≤ normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (j - 1)) * T) + normHS (Edef (m + 1) (EpatB (m + 1) B) (towerFloor b 0)) := by
      convert normHS_sub_le _ _ using 1;
    refine le_trans ( pow_le_pow_left₀ ( normHS_nonneg _ ) h_step 2 ) ?_;
    rw [ ← conj_floor_normHS_sq_measure hTl hTr B hBh hB2 hBc ( Defined.mono ( by norm_num ) ( hfloor _ ( Nat.sub_lt ( by linarith ) zero_lt_one ) ) ), ← floor_normHS_sq_measure B hBh hB2 hBc ( Defined.mono ( by norm_num ) ( hfloor _ ( by linarith ) ) ) ];
    linarith [ sq_nonneg ( normHS ( star T * Edef ( m + 1 ) ( EpatB ( m + 1 ) B ) ( towerFloor b ( j - 1 ) ) * T ) - normHS ( Edef ( m + 1 ) ( EpatB ( m + 1 ) B ) ( towerFloor b 0 ) ) ) ];
  have h_sum_le : ∀ i < j, (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b i)).toReal ≤ (∑ i' ∈ Finset.range j, (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b i')).toReal) / (t : ℝ) + ∑ k ∈ Finset.range (j - 1), |(pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b (k + 1))).toReal - (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b k)).toReal| := by
    intros i hi
    apply val_le_avg_add_tv (fun i' => (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b i')).toReal) hi |> le_trans <| add_le_add (by
    gcongr) le_rfl;
  have h_sum_le : ∑ k ∈ Finset.range (j - 1), |(pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b (k + 1))).toReal - (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b k)).toReal| ≤ ∑ k ∈ Finset.range j, normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b k) * T - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (k + 1))) ^ 2 := by
    refine' le_trans ( Finset.sum_le_sum fun i hi => _ ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.sub_le _ _ ) ) fun _ _ _ => sq_nonneg _ );
    convert meas_step_le_floorTerm hTl hTr B hBh hB2 hBc ( floor_defined_succ ( by linarith [ Finset.mem_range.mp hi ] ) hfloor i ( by linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel ( by linarith : 1 ≤ j ) ] ) ) ( floor_defined_succ ( by linarith [ Finset.mem_range.mp hi ] ) hfloor ( i + 1 ) ( by linarith [ Finset.mem_range.mp hi, Nat.sub_add_cancel ( by linarith : 1 ≤ j ) ] ) ) using 1;
  grind

/-
**Short-tower closing-defect bound (`lem:clb2`).**
-/
lemma keyD2_short_le {m : ℕ} [NeZero d] {T : Matrix (Fin d) (Fin d) ℂ}
    (hTl : star T * T = 1) (hTr : T * star T = 1)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {δ : ℝ} {b : Set Cfg} {j : ℕ} (hj : 1 ≤ j)
    (hfloor : ∀ i, i < j → Defined m (towerFloor b i))
    (hclosed : DeltaClosed (pvmMeasure (m + 1) (EpatB (m + 1) B)) δ j b) :
    normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (j - 1)) * T
        - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b 0)) ^ 2
      ≤ 4 * (∑ i ∈ Finset.range j,
            normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i) * T
              - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (i + 1))) ^ 2)
        + 4 * δ * (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b 0)).toReal := by
  have := @LamplighterStability.MeasureBridge.pvmMeasure_isProbability;
  specialize @this d ‹_› ( m + 1 ) ( EpatB ( m + 1 ) B ) ( EpatB_isHermitian ( m + 1 ) B hBh ‹_› ) ( EpatB_isIdempotent ( m + 1 ) B hB2 ‹_› ) ( EpatB_sum ( m + 1 ) B );
  obtain ⟨hSj, hS0⟩ : Defined (m + 1) (towerFloor b j) ∧ Defined (m + 1) (towerFloor b 0) := by
    exact ⟨ floor_defined_succ hj hfloor j le_rfl, floor_defined_succ hj hfloor 0 ( by linarith ) ⟩;
  have hY : normHS (Edef (m + 1) (EpatB (m + 1) B) (towerFloor b j)
        - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b 0)) ^ 2
      ≤ (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b j)).toReal
          - (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b 0)).toReal
        + 2 * δ * (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b 0)).toReal := by
          have hY : (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b j ∩ towerFloor b 0)).toReal
                      ≥ (1 - δ) * (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b 0)).toReal := by
                        convert hclosed using 1;
                        unfold DeltaClosed; aesop;
          rw [ Edef_sub_normHS_sq_measure ( m + 1 ) B hBh hB2 hBc hSj hS0 ];
          have hY : (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b j)).toReal
                        = (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b j ∩ towerFloor b 0)).toReal
                          + (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b j \ towerFloor b 0)).toReal := by
                            rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_inter_add_diff _ ( measurableSet_of_defined hS0 ) ]; all_goals exact MeasureTheory.measure_ne_top _ _;
          have hY : (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b 0)).toReal
                              = (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b j ∩ towerFloor b 0)).toReal
                                + (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b 0 \ towerFloor b j)).toReal := by
                                  rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_inter_add_diff ( towerFloor b 0 ) ( measurableSet_of_defined hSj ) ];
                                  · rw [ Set.inter_comm ];
                                  · exact MeasureTheory.measure_ne_top _ _;
                                  · exact MeasureTheory.measure_ne_top _ _;
          linarith;
  have hX : normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (j - 1)) * T
            - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b j)) ^ 2
            ≤ ∑ i ∈ Finset.range j, normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i) * T
                - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (i + 1))) ^ 2 := by
                  convert Finset.single_le_sum ( fun i _ => sq_nonneg ( normHS ( star T * Edef ( m + 1 ) ( EpatB ( m + 1 ) B ) ( towerFloor b i ) * T - Edef ( m + 1 ) ( EpatB ( m + 1 ) B ) ( towerFloor b ( i + 1 ) ) ) ) ) ( Finset.mem_range.mpr ( Nat.sub_lt hj zero_lt_one ) ) using 1;
                  rw [ Nat.sub_add_cancel hj ];
  have h_sum : normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (j - 1)) * T
            - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b 0)) ^ 2
            ≤ 2 * normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (j - 1)) * T
                - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b j)) ^ 2
              + 2 * normHS (Edef (m + 1) (EpatB (m + 1) B) (towerFloor b j)
                - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b 0)) ^ 2 := by
                  have h_sum : ∀ (A B : Matrix (Fin d) (Fin d) ℂ), normHS (A + B) ^ 2 ≤ 2 * normHS A ^ 2 + 2 * normHS B ^ 2 := by
                    intros A B
                    have h_sum : normHS (A + B) ^ 2 ≤ (normHS A + normHS B) ^ 2 := by
                      exact pow_le_pow_left₀ ( by exact Real.sqrt_nonneg _ ) ( normHS_add_le A B ) _;
                    linarith [ sq_nonneg ( normHS A - normHS B ) ];
                  convert h_sum ( star T * Edef ( m + 1 ) ( EpatB ( m + 1 ) B ) ( towerFloor b ( j - 1 ) ) * T - Edef ( m + 1 ) ( EpatB ( m + 1 ) B ) ( towerFloor b j ) ) ( Edef ( m + 1 ) ( EpatB ( m + 1 ) B ) ( towerFloor b j ) - Edef ( m + 1 ) ( EpatB ( m + 1 ) B ) ( towerFloor b 0 ) ) using 1 ; abel_nf;
  have h_sum : (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b j)).toReal
                - (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b 0)).toReal
              ≤ ∑ i ∈ Finset.range j, normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i) * T
                  - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (i + 1))) ^ 2 := by
                    have h_sum : (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b j)).toReal
                                  - (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b 0)).toReal
                                = ∑ i ∈ Finset.range j, ((pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b (i + 1))).toReal
                                    - (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b i)).toReal) := by
                                      rw [ Finset.sum_range_sub ( fun i => ( pvmMeasure ( m + 1 ) ( EpatB ( m + 1 ) B ) ( towerFloor b i ) |> ENNReal.toReal ) ) ];
                    rw [h_sum];
                    refine' Finset.sum_le_sum fun i hi => _;
                    have := @meas_step_le_floorTerm;
                    exact le_of_abs_le ( this hTl hTr B hBh hB2 hBc ( floor_defined_succ hj hfloor i ( by linarith [ Finset.mem_range.mp hi ] ) ) ( floor_defined_succ hj hfloor ( i + 1 ) ( by linarith [ Finset.mem_range.mp hi ] ) ) );
  linarith

/-
**Uniform per-tower closing-defect bound.**  Covers both branches of the
height-versus-closedness dichotomy with a single nonnegative-coefficient bound,
ready to be summed over the tower partition.
-/
lemma keyD2g_uniform_le {m t : ℕ} [NeZero d] (ht : 1 ≤ t) {T : Matrix (Fin d) (Fin d) ℂ}
    (hTl : star T * T = 1) (hTr : T * star T = 1)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {δ : ℝ} (hδ : 0 ≤ δ) {b : Set Cfg} {j : ℕ}
    (hfloor : ∀ i, i < j → Defined m (towerFloor b i))
    (hdich : (j < t ∧ DeltaClosed (pvmMeasure (m + 1) (EpatB (m + 1) B)) δ j b)
            ∨ (t ≤ j ∧ j < 6 * t + 1)) :
    (if 0 < j then
        normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (j - 1)) * T
          - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b 0)) ^ 2
      else 0)
      ≤ 4 * (∑ i ∈ Finset.range j,
            normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i) * T
              - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (i + 1))) ^ 2)
        + (4 * δ + 4 / (t : ℝ)) * (∑ i ∈ Finset.range j,
            (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor b i)).toReal) := by
  by_cases hj : 0 < j;
  · rcases hdich with hdich | hdich;
    · rw [ if_pos hj ];
      refine le_trans ( keyD2_short_le hTl hTr B hBh hB2 hBc hj hfloor hdich.2 ) ?_;
      gcongr;
      · exact le_add_of_nonneg_right ( by positivity );
      · exact le_trans ( by norm_num ) ( Finset.single_le_sum ( fun i _ => ENNReal.toReal_nonneg ) ( Finset.mem_range.mpr hj ) );
    · have := keyD2_long_le ht hTl hTr B hBh hB2 hBc hdich.1 hfloor;
      rw [ if_pos hj ] ; nlinarith [ show ( 0 : ℝ ) ≤ ∑ i ∈ Finset.range j, ( ( pvmMeasure ( m + 1 ) ( EpatB ( m + 1 ) B ) ) ( towerFloor b i ) |> ENNReal.toReal ) by exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg ] ;
  · aesop

/-
**Total floor-measure bound.**  The sum of all floor measures over a tower
partition is at most `1` (the floors are pairwise disjoint with union `eᶜ`).
-/
lemma sum_floor_measure_le_one {m : ℕ} [NeZero d]
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {e : Set Cfg} {ιτ : Type} [Fintype ιτ] {base : ιτ → Set Cfg} {height : ιτ → ℕ}
    (hpart : IsTowerPartition e base height)
    (hfloordef : ∀ τ i, i < height τ → Defined m (towerFloor (base τ) i)) :
    ∑ τ : ιτ, ∑ i ∈ Finset.range (height τ),
        (pvmMeasure (m + 1) (EpatB (m + 1) B) (towerFloor (base τ) i)).toReal ≤ 1 := by
  convert ENNReal.toReal_mono _ _;
  rw [ ENNReal.toReal_sum, Finset.sum_sigma' ];
  any_goals exact ENNReal.toReal_one.symm;
  · haveI := pvmMeasure_isProbability ( m + 1 ) ( EpatB ( m + 1 ) B ) ( EpatB_isHermitian ( m + 1 ) B hBh hBc ) ( EpatB_isIdempotent ( m + 1 ) B hB2 hBc ) ( EpatB_sum ( m + 1 ) B ) ; exact fun _ _ => MeasureTheory.measure_ne_top _ _;
  · norm_num;
  · rw [ ← MeasureTheory.measure_biUnion_finset ];
    · convert MeasureTheory.measure_mono ( Set.subset_univ _ ) using 1;
      · convert pvmMeasure_univ ( m + 1 ) ( EpatB ( m + 1 ) B ) ( fun p => EpatB_isHermitian ( m + 1 ) B hBh hBc p ) ( fun p => EpatB_isIdempotent ( m + 1 ) B hB2 hBc p ) ( EpatB_sum ( m + 1 ) B ) |> Eq.symm;
      · infer_instance;
    · intro a ha b hb hab; have := hpart.1 a.1 b.1 a.2 b.2; aesop;
    · exact fun x hx => measurableSet_of_defined ( hfloordef _ _ ( Finset.mem_range.mp ( Finset.mem_sigma.mp hx |>.2 ) ) )

end LamplighterStability