import RequestProject.Dynamics.MarkerLemmas
import RequestProject.Dynamics.TowerDecomp

/-!
# Phase 2: the tower-decomposition assembly

This file carries out the measure-theoretic assembly of `prop:decomp`
(`prop_decomp`) from the Phase-1 interfaces (`covering_per_seq`, `marker_lemma`)
and the already-proved approximate-invariance lemma `approxInv_pow`
(`lem:approx_inv_measures`).

We build it bottom-up:

1. **Elementary `FIndep` / tower-floor manipulations** (fully proved here): how
   `F_t`-independence and tower floors behave under the shift `L`.  These are the
   combinatorial core of the Kakutani–Rokhlin "markers → towers" step.
2. **`complement_bound`** (`lem:complement-bound`): the measure that translates of
   the marker set escape the aperiodic part is small.  Built on `approxInv_pow`.
3. **The Kakutani–Rokhlin construction** turning the marker set into towers of
   height `t+1 ≤ j ≤ 2t+1`.
4. **The final assembly** producing `prop_decomp`.

Phase 2 depends on Phases 0/1 only through statements, so it can proceed in
parallel with their proofs.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators

/-! ## 1. Elementary `FIndep` / tower-floor manipulations -/

/-
A tower floor of a shifted base is the correspondingly shifted floor:
`towerFloor ((L^m)''b) i = (L^m)''(towerFloor b i)`.
-/
theorem towerFloor_image_shift (b : Set Cfg) (m : ℤ) (i : ℕ) :
    towerFloor ((L ^ m) '' b) i = (L ^ m) '' (towerFloor b i) := by
  unfold towerFloor;
  rw [ Set.image_image, Set.image_image ];
  grind +suggestions

/-
`F_t`-independence is preserved by the shift: if `b` is `F_t`-independent then
so is every translate `(L^m)''b`.  (Used for `W = L^{-t} Z`.)
-/
theorem FIndep.image_shift {t : ℕ} {b : Set Cfg} (h : FIndep t b) (m : ℤ) :
    FIndep t ((L ^ m) '' b) := by
  intro i hi hi0
  rw [ ← Set.image_comp, ← Equiv.Perm.coe_mul, ← zpow_add ];
  rw [ disjoint_shift_iff ];
  simpa using h i hi hi0

/-- A translate of a `t`-marker is again `F_t`-independent. -/
theorem IsMarker.fIndep_image_shift {t : ℕ} {Z Ξ : Set Cfg}
    (h : IsMarker t Z Ξ) (m : ℤ) : FIndep t ((L ^ m) '' Z) :=
  h.2.1.image_shift m

/-- `L ^ i` is measurable as a self-map of `Cfg`. -/
lemma measurable_L_zpow (i : ℤ) : Measurable (fun x : Cfg => (L ^ i) x) := by
  refine measurable_pi_lambda _ (fun n => ?_)
  have h : (fun x : Cfg => (L ^ i) x n) = fun x : Cfg => x (n - i) := by
    funext x; exact L_zpow_apply i x n
  rw [h]; exact measurable_pi_apply _

/-- The `L ^ i`-image of a measurable set is measurable. -/
lemma measurableSet_L_zpow_image {i : ℤ} {S : Set Cfg} (hS : MeasurableSet S) :
    MeasurableSet ((L ^ i) '' S) := by
  have h : (L ^ i) '' S = (fun x : Cfg => (L ^ (-i)) x) ⁻¹' S := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : (L ^ (-i)) ((L ^ i) y) = y := by
        rw [← Equiv.Perm.mul_apply, ← zpow_add]; simp
      rw [hy']; exact hy
    · intro hx
      exact ⟨(L ^ (-i)) x, hx, by rw [← Equiv.Perm.mul_apply, ← zpow_add]; simp⟩
  rw [h]; exact measurable_L_zpow (-i) hS

/-- A set difference of two `n`-defined sets is `n`-defined. -/
lemma defined_diff {n : ℕ} {A B : Set Cfg} (hA : Defined n A) (hB : Defined n B) :
    Defined n (A \ B) := by
  intro x y hxy
  simp only [Set.mem_diff, hA x y hxy, hB x y hxy]

/-- An intersection of two `n`-defined sets is `n`-defined. -/
lemma defined_inter {n : ℕ} {A B : Set Cfg} (hA : Defined n A) (hB : Defined n B) :
    Defined n (A ∩ B) := by
  intro x y hxy
  simp only [Set.mem_inter_iff, hA x y hxy, hB x y hxy]

/-- An `n`-defined set is measurable (it is a finite union of cylinders). -/
lemma Defined.measurableSet {n : ℕ} {S : Set Cfg} (hS : Defined n S) :
    MeasurableSet S := by
  rw [defined_eq_biUnion_cyl hS]
  exact Finset.measurableSet_biUnion _ (fun b _ => measurableSet_cyl n b)

/-! ## 1b. Symmetric-difference bound (`lem:approx_inv_measures` part (ii))

Part (i) of `lem:approx_inv_measures` is `approxInv_pow` (in `ApproxInvMeasure`).
Part (ii) — the symmetric-difference bound under `δ`-closedness — is the next
building block toward `complement_bound`. -/

/-
**`lem:approx_inv_measures` part (ii).**  For an `(M,η)`-invariant measure and
a pairwise-disjoint family of `k`-defined measurable sets `{b i}` with
`|q| + k ≤ M`, if the family is `δ`-closed under `L^q` (i.e.
`(1-δ)·μ(⋃ b i) ≤ ∑ μ(L^q b i ∩ b i)`), then
`∑ μ(L^q b i △ b i) ≤ 2δ·μ(⋃ b i) + |q|·η`.
-/
theorem approxInv_symmDiff {M : ℕ} {η δ : ℝ} {μ : Measure Cfg}
    [IsProbabilityMeasure μ] (hμ : ApproxInvMeasure M η μ)
    {ι : Type*} [Fintype ι] {b : ι → Set Cfg}
    {k : ℕ} {q : ℤ} (hqk : q.natAbs + k ≤ M)
    (hdisj : Pairwise (Function.onFun Disjoint b))
    (hmeas : ∀ i, MeasurableSet (b i))
    (hdef : ∀ i, Defined k (b i))
    (hclosed : (1 - δ) * (μ (⋃ i, b i)).toReal ≤
      ∑ i, (μ ((L ^ q) '' b i ∩ b i)).toReal) :
    ∑ i, (μ (symmDiff ((L ^ q) '' b i) (b i))).toReal ≤
      2 * δ * (μ (⋃ i, b i)).toReal + (q.natAbs : ℝ) * η := by
  -- Apply the triangle inequality to the sum of the measures of the symmetric differences.
  have h_triangle : ∑ i, (μ (symmDiff ((L ^ q) '' (b i)) (b i))).toReal ≤ ∑ i, ((μ ((L ^ q) '' (b i))).toReal + (μ (b i)).toReal - 2 * (μ ((L ^ q) '' (b i) ∩ (b i))).toReal) := by
    refine' Finset.sum_le_sum fun i _ => _;
    rw [ show symmDiff ( ( L ^ q ) '' b i ) ( b i ) = ( ( L ^ q ) '' b i ) \ ( b i ) ∪ ( b i ) \ ( ( L ^ q ) '' b i ) by rfl, MeasureTheory.measure_union ];
    · rw [ ENNReal.toReal_add ];
      · rw [ show μ ( ( L ^ q ) '' b i ) = μ ( ( L ^ q ) '' b i \ b i ) + μ ( ( L ^ q ) '' b i ∩ b i ) from ?_, show μ ( b i ) = μ ( b i \ ( L ^ q ) '' b i ) + μ ( ( L ^ q ) '' b i ∩ b i ) from ?_ ];
        · rw [ ENNReal.toReal_add, ENNReal.toReal_add ] <;> norm_num;
          linarith;
        · rw [ ← MeasureTheory.measure_inter_add_diff ( b i ) ( show MeasurableSet ( ⇑ ( L ^ q ) '' b i ) from ?_ ) ];
          · rw [ add_comm, Set.inter_comm ];
          · have := hmeas i;
            convert this.preimage ( show Measurable ( L ^ ( -q ) ) from ?_ ) using 1;
            · ext; simp [Set.mem_preimage];
            · refine' measurable_pi_lambda _ _;
              intro a; exact (by
              convert measurable_pi_apply ( a + q ) using 1;
              ext; simp +decide [] ; ring;
              convert L_zpow_apply ( -q ) _ _ using 1 ; ring;
              rotate_left;
              rotate_left;
              exact ‹Cfg›;
              exact a;
              · simp +decide [ zpow_neg ];
              · grind);
        · rw [ ← MeasureTheory.measure_inter_add_diff ( ( L ^ q ) '' b i ) ( hmeas i ) ];
          ring;
      · exact MeasureTheory.measure_ne_top _ _;
      · exact MeasureTheory.measure_ne_top _ _;
    · grind;
    · refine' MeasurableSet.diff ( hmeas i ) _;
      have := hmeas i;
      convert this.preimage ( show Measurable ( L ^ ( -q ) ) from ?_ ) using 1;
      · ext; simp [Set.mem_preimage];
      · refine' measurable_pi_lambda _ _;
        intro a; exact (by
        convert measurable_pi_apply ( a + q ) using 1;
        ext; simp +decide [] ; ring;
        convert L_zpow_apply ( -q ) _ _ using 1 ; ring;
        rotate_left;
        rotate_left;
        exact ‹Cfg›;
        exact a;
        · simp +decide [ zpow_neg ];
        · grind);
  have h_sum_measures : ∑ i, (μ (b i)).toReal = (μ (⋃ i, b i)).toReal := by
    rw [ MeasureTheory.measure_iUnion hdisj ];
    · rw [ tsum_fintype, ENNReal.toReal_sum ];
      exact fun i _ => MeasureTheory.measure_ne_top _ _;
    · assumption;
  have h_approx_inv : ∑ i, (μ ((L ^ q) '' (b i))).toReal ≤ (μ (⋃ i, b i)).toReal + q.natAbs * η := by
    have h_approx_inv : ∑ i, |(μ ((L ^ q) '' (b i))).toReal - (μ (b i)).toReal| ≤ q.natAbs * η := by
      apply approxInv_pow hμ hqk hdisj hdef;
    have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => le_abs_self ( ( μ ( ( L ^ q ) '' b i ) |> ENNReal.toReal ) - ( μ ( b i ) |> ENNReal.toReal ) ) ; simp_all +decide [ Finset.sum_add_distrib ] ; linarith;
  norm_num [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _ ] at * ; linarith

/-
**`lem:approx_inv_measures` part (ii), "moreover" assertion (powered version).**
For an `(M,η)`-invariant measure and a pairwise-disjoint family of `k`-defined
measurable sets `{b i}` that is `δ`-closed under `L^q`, if `m : ℕ` is such that
`|q·m| + |q| + k ≤ M`, then
`∑ μ(L^{q·m} b i △ b i) ≤ 2·m·δ·μ(⋃ b i) + 2·|q|·m²·η`.
This is the inductive consequence of `approxInv_symmDiff` (base case `m = 1`)
used repeatedly in `lem:complement-bound`. -/
/-- Image-algebra step for `approxInv_symmDiff_pow`: the symmetric difference of
consecutive powers is the `L^{q m}`-image of the one-step symmetric difference. -/
lemma shift_image_symmDiff (q : ℤ) (m : ℕ) (s : Set Cfg) :
    symmDiff ((L ^ (q * ((m : ℤ) + 1))) '' s) ((L ^ (q * (m : ℤ))) '' s)
      = (L ^ (q * (m : ℤ))) '' (symmDiff ((L ^ q) '' s) s) := by
  have h1 : (L ^ (q * ((m : ℤ) + 1))) '' s = (L ^ (q * (m : ℤ))) '' ((L ^ q) '' s) := by
    rw [Set.image_image, show q * ((m : ℤ) + 1) = q * (m : ℤ) + q by ring, zpow_add,
      Equiv.Perm.coe_mul]
    rfl
  rw [h1, ← Set.image_symmDiff (Equiv.injective _)]

/-- General image/symmetric-difference shift identity:
`symmDiff ((L^(c+a))''s) ((L^c)''s) = (L^c) '' (symmDiff ((L^a)''s) s)`. -/
lemma image_symmDiff_shift (a c : ℤ) (s : Set Cfg) :
    symmDiff ((L ^ (c + a)) '' s) ((L ^ c) '' s)
      = (L ^ c) '' (symmDiff ((L ^ a) '' s) s) := by
  have h1 : (L ^ (c + a)) '' s = (L ^ c) '' ((L ^ a) '' s) := by
    rw [Set.image_image, zpow_add, Equiv.Perm.coe_mul]
    rfl
  rw [h1, ← Set.image_symmDiff (Equiv.injective _)]

set_option maxHeartbeats 1000000 in
theorem approxInv_symmDiff_pow {M : ℕ} {η δ : ℝ} {μ : Measure Cfg}
    [IsProbabilityMeasure μ] (hμ : ApproxInvMeasure M η μ)
    {ι : Type*} [Fintype ι] {b : ι → Set Cfg}
    {k : ℕ} {q : ℤ} (m : ℕ)
    (hqmk : (q * (m : ℤ)).natAbs + q.natAbs + k ≤ M)
    (hdisj : Pairwise (Function.onFun Disjoint b))
    (hmeas : ∀ i, MeasurableSet (b i))
    (hdef : ∀ i, Defined k (b i))
    (_hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hclosed : (1 - δ) * (μ (⋃ i, b i)).toReal ≤
      ∑ i, (μ ((L ^ q) '' b i ∩ b i)).toReal) :
    ∑ i, (μ (symmDiff ((L ^ (q * (m : ℤ))) '' b i) (b i))).toReal ≤
      2 * (m : ℝ) * δ * (μ (⋃ i, b i)).toReal
        + 2 * (q.natAbs : ℝ) * (m : ℝ) ^ 2 * η := by
  induction' m with m ih;
  · simp +decide [ symmDiff ];
  · have hqmk' : (q * m).natAbs + q.natAbs + k ≤ M := by
      norm_num [ Int.natAbs_mul ] at *;
      nlinarith [ abs_nonneg q, abs_of_nonneg ( by positivity : 0 ≤ ( m : ℤ ) + 1 ) ];
    have h_step : ∑ i, (μ (symmDiff ((L ^ (q * ((m : ℤ) + 1))) '' (b i)) ((L ^ (q * (m : ℤ))) '' (b i)))).toReal ≤ ∑ i, (μ (symmDiff ((L ^ q) '' (b i)) (b i))).toReal + 2 * (q.natAbs : ℝ) * m * η := by
      have h_step : ∑ i, (μ ((L ^ (q * (m : ℤ))) '' (((L ^ q) '' (b i)) \ (b i)))).toReal ≤ ∑ i, (μ (((L ^ q) '' (b i)) \ (b i))).toReal + (q.natAbs : ℝ) * m * η := by
        have := approxInv_pow hμ ( by linarith : ( q * m |> Int.natAbs ) + ( k + q.natAbs ) ≤ M ) ( show Pairwise ( Function.onFun Disjoint fun i => ( L ^ q ) '' b i \ b i ) from ?_ ) ( show ∀ i, Defined ( k + q.natAbs ) ( ( L ^ q ) '' b i \ b i ) from ?_ );
        · have h_step : ∑ i, (μ ((L ^ (q * (m : ℤ))) '' (((L ^ q) '' (b i)) \ (b i)))).toReal ≤ ∑ i, (μ (((L ^ q) '' (b i)) \ (b i))).toReal + ∑ i, |(μ ((L ^ (q * (m : ℤ))) '' (((L ^ q) '' (b i)) \ (b i)))).toReal - (μ (((L ^ q) '' (b i)) \ (b i))).toReal| := by
            rw [ ← Finset.sum_add_distrib ];
            exact Finset.sum_le_sum fun i _ => by cases abs_cases ( ( μ ( ( L ^ ( q * m ) ) '' ( ( L ^ q ) '' b i \ b i ) ) |> ENNReal.toReal ) - ( μ ( ( L ^ q ) '' b i \ b i ) |> ENNReal.toReal ) ) <;> linarith;
          simp_all +decide [ Int.natAbs_mul ];
          linarith;
        · intro i j hij; specialize hdisj hij; simp_all +decide [ Set.disjoint_left ] ;
        · exact fun i => defined_diff ( defined_shift ( hdef i ) q ) ( Defined.mono ( Nat.le_add_right _ _ ) ( hdef i ) );
      have h_step2 : ∑ i, (μ ((L ^ (q * (m : ℤ))) '' ((b i) \ ((L ^ q) '' (b i))))).toReal ≤ ∑ i, (μ ((b i) \ ((L ^ q) '' (b i)))).toReal + (q.natAbs : ℝ) * m * η := by
        have := @approxInv_pow M η μ;
        specialize this hμ ( show ( q * m ).natAbs + ( k + q.natAbs ) ≤ M from by linarith ) ( show Pairwise ( Function.onFun Disjoint fun i => b i \ ⇑ ( L ^ q ) '' b i ) from fun i j hij => ?_ ) ( show ∀ i, Defined ( k + q.natAbs ) ( b i \ ⇑ ( L ^ q ) '' b i ) from fun i => ?_ );
        · exact Disjoint.mono Set.diff_subset Set.diff_subset ( hdisj hij );
        · exact defined_diff ( Defined.mono ( Nat.le_add_right _ _ ) ( hdef i ) ) ( defined_shift ( hdef i ) q );
        · refine' le_trans ( Finset.sum_le_sum fun i _ => show ( μ ( ⇑ ( L ^ ( q * m ) ) '' ( b i \ ⇑ ( L ^ q ) '' b i ) ) |> ENNReal.toReal ) ≤ ( μ ( b i \ ⇑ ( L ^ q ) '' b i ) |> ENNReal.toReal ) + |( μ ( ⇑ ( L ^ ( q * m ) ) '' ( b i \ ⇑ ( L ^ q ) '' b i ) ) |> ENNReal.toReal ) - ( μ ( b i \ ⇑ ( L ^ q ) '' b i ) |> ENNReal.toReal )| from _ ) _;
          · cases abs_cases ( ( μ ( ⇑ ( L ^ ( q * m ) ) '' ( b i \ ⇑ ( L ^ q ) '' b i ) ) |> ENNReal.toReal ) - ( μ ( b i \ ⇑ ( L ^ q ) '' b i ) |> ENNReal.toReal ) ) <;> linarith;
          · simp_all +decide [ Finset.sum_add_distrib, Int.natAbs_mul ];
      convert add_le_add h_step h_step2 using 1;
      · rw [ ← Finset.sum_add_distrib ] ; congr ; ext i ; rw [ shift_image_symmDiff ] ; ring;
        rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_union ];
        · rw [ ← Set.image_union, symmDiff ];
          rfl;
        · simp +decide [ Set.disjoint_left ];
          tauto;
        · apply_rules [ measurableSet_L_zpow_image, measurableSet_L_zpow_image ];
          exact MeasurableSet.diff ( hmeas i ) ( measurableSet_L_zpow_image ( hmeas i ) );
        · exact MeasureTheory.measure_ne_top _ _;
        · exact MeasureTheory.measure_ne_top _ _;
      · simp +decide [ symmDiff, add_assoc, add_left_comm, add_comm ];
        rw [ ← Finset.sum_add_distrib ];
        rw [ Finset.sum_congr rfl fun i _ => ?_ ];
        rotate_left;
        use fun i => ( μ ( b i \ ⇑ ( L ^ q ) '' b i ) |> ENNReal.toReal ) + ( μ ( ⇑ ( L ^ q ) '' b i \ b i ) |> ENNReal.toReal );
        · rw [ MeasureTheory.measure_union ];
          · rw [ add_comm, ENNReal.toReal_add ] <;> norm_num;
          · exact disjoint_sdiff_sdiff;
          · exact MeasurableSet.diff ( hmeas i ) ( measurableSet_L_zpow_image ( hmeas i ) );
        · ring;
    have h_triangle : ∀ i, (μ (symmDiff ((L ^ (q * ((m : ℤ) + 1))) '' (b i)) (b i))).toReal ≤ (μ (symmDiff ((L ^ (q * ((m : ℤ) + 1))) '' (b i)) ((L ^ (q * (m : ℤ))) '' (b i)))).toReal + (μ (symmDiff ((L ^ (q * (m : ℤ))) '' (b i)) (b i))).toReal := by
      intro i
      have h_triangle : μ (symmDiff ((L ^ (q * ((m : ℤ) + 1))) '' (b i)) (b i)) ≤ μ (symmDiff ((L ^ (q * ((m : ℤ) + 1))) '' (b i)) ((L ^ (q * (m : ℤ))) '' (b i))) + μ (symmDiff ((L ^ (q * (m : ℤ))) '' (b i)) (b i)) := by
        refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ );
        grind +qlia;
      convert ENNReal.toReal_mono _ h_triangle using 1;
      · rw [ ENNReal.toReal_add ] <;> norm_num;
      · exact ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ MeasureTheory.measure_lt_top _ _, MeasureTheory.measure_lt_top _ _ ⟩ );
    have h_approxInv_symmDiff : ∑ i, (μ (symmDiff ((L ^ q) '' (b i)) (b i))).toReal ≤ 2 * δ * (μ (⋃ i, b i)).toReal + (q.natAbs : ℝ) * η := by
      apply approxInv_symmDiff hμ;
      any_goals assumption;
      linarith [ abs_nonneg ( q * m ) ];
    norm_num +zetaDelta at *;
    exact le_trans ( Finset.sum_le_sum fun _ _ => h_triangle _ ) ( by rw [ Finset.sum_add_distrib ] ; nlinarith [ ih hqmk', show ( 0 : ℝ ) ≤ |↑q| * η by positivity ] )

/-! ## 1c. Building blocks for the complement bound -/

/-
Translating a family of symmetric differences by `L^r` changes the total
measure by at most `2|r|η` (two applications of `approxInv_pow`, one for each
set-difference half).
-/
lemma translate_pair_diff_sum
    {M D' : ℕ} {η : ℝ} {μ : Measure Cfg} [IsProbabilityMeasure μ]
    {σ : Type*} [Fintype σ] {A B : σ → Set Cfg}
    (hμ : ApproxInvMeasure M η μ)
    (hA : ∀ τ, Defined D' (A τ)) (hB : ∀ τ, Defined D' (B τ))
    (hAdisj : Pairwise (Function.onFun Disjoint A))
    (hBdisj : Pairwise (Function.onFun Disjoint B))
    (hAmeas : ∀ τ, MeasurableSet (A τ)) (hBmeas : ∀ τ, MeasurableSet (B τ))
    (r : ℤ) (hMc : r.natAbs + D' ≤ M) :
    ∑ τ, (μ ((L ^ r) '' (symmDiff (A τ) (B τ)))).toReal
      ≤ ∑ τ, (μ (symmDiff (A τ) (B τ))).toReal + 2 * (r.natAbs : ℝ) * η := by
  have h_split : (∑ τ, (μ ((L ^ r) '' (symmDiff (A τ) (B τ)))).toReal) =
    (∑ τ, (μ ((A τ \ B τ) ∪ (B τ \ A τ))).toReal) + (∑ τ, ((μ ((L ^ r) '' (A τ \ B τ))).toReal - (μ (A τ \ B τ)).toReal)) + (∑ τ, ((μ ((L ^ r) '' (B τ \ A τ))).toReal - (μ (B τ \ A τ)).toReal)) := by
      rw [ ← Finset.sum_add_distrib, ← Finset.sum_add_distrib ];
      refine' Finset.sum_congr rfl fun τ _ => _;
      rw [ show symmDiff ( A τ ) ( B τ ) = ( A τ \ B τ ) ∪ ( B τ \ A τ ) by rfl, Set.image_union ];
      rw [ MeasureTheory.measure_union, MeasureTheory.measure_union ];
      · rw [ ENNReal.toReal_add, ENNReal.toReal_add ] <;> norm_num;
        ring;
      · exact disjoint_sdiff_sdiff;
      · exact MeasurableSet.diff ( hBmeas τ ) ( hAmeas τ );
      · simp +decide [ Set.disjoint_left ];
        tauto;
      · exact measurableSet_L_zpow_image ( MeasurableSet.diff ( hBmeas τ ) ( hAmeas τ ) );
  -- Apply the approximation result to each term in the sum.
  have h_approx : ∀ (C D : σ → Set Cfg), (∀ τ, Defined D' (C τ)) → (∀ τ, MeasurableSet (C τ)) → (∀ τ, Defined D' (D τ)) → (∀ τ, MeasurableSet (D τ)) → Pairwise (Function.onFun Disjoint C) → Pairwise (Function.onFun Disjoint D) → (∑ τ, |(μ ((L ^ r) '' (C τ \ D τ))).toReal - (μ (C τ \ D τ)).toReal|) ≤ (r.natAbs : ℝ) * η := by
    intros C D hC hCmeas hD hDmeas hCdisj hDdisj;
    convert approxInv_pow hμ ( show r.natAbs + D' ≤ M from hMc ) ( show Pairwise ( Function.onFun Disjoint fun τ => C τ \ D τ ) from ?_ ) ( show ∀ τ, Defined D' ( C τ \ D τ ) from ?_ ) using 1;
    · exact fun i j hij => Disjoint.mono Set.diff_subset Set.diff_subset ( hCdisj hij );
    · exact fun τ => defined_diff ( hC τ ) ( hD τ );
  have := h_approx A B hA hAmeas hB hBmeas hAdisj hBdisj;
  linarith! [ show ∑ τ, |( μ ( ( L ^ r ) '' ( B τ \ A τ ) ) |> ENNReal.toReal ) - ( μ ( B τ \ A τ ) |> ENNReal.toReal )| ≤ ↑r.natAbs * η from h_approx B A hB hBmeas hA hAmeas hBdisj hAdisj, show ∑ τ, ( ( μ ( ( L ^ r ) '' ( A τ \ B τ ) ) |> ENNReal.toReal ) - ( μ ( A τ \ B τ ) |> ENNReal.toReal ) ) ≤ ↑r.natAbs * η from le_trans ( Finset.sum_le_sum fun _ _ => le_abs_self _ ) this, show ∑ τ, ( ( μ ( ( L ^ r ) '' ( B τ \ A τ ) ) |> ENNReal.toReal ) - ( μ ( B τ \ A τ ) |> ENNReal.toReal ) ) ≤ ↑r.natAbs * η from le_trans ( Finset.sum_le_sum fun _ _ => le_abs_self _ ) ( h_approx B A hB hBmeas hA hAmeas hBdisj hAdisj ) ]

/-
**Per-orbit symmetric-difference bound.**  For a pairwise-disjoint family of
`D`-defined `δ`-closed (under `L^h`) bases, the total measure of the symmetric
difference between the `w`-translate and the `(w mod h)`-translate of each base
is controlled, with the `δ`-term *linear* in `|w/h|`.  This is the core estimate
behind `lem:complement-bound`; here `w / h` and `w % h` are Euclidean.
-/
set_option maxHeartbeats 1600000 in
lemma orbit_shift_symmDiff_bound
    {M D h : ℕ} {δ η : ℝ} {μ : Measure Cfg} [IsProbabilityMeasure μ]
    {σ : Type*} [Fintype σ] {base : σ → Set Cfg}
    (hh : 1 ≤ h) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hμ : ApproxInvMeasure M η μ)
    (hbasedef : ∀ τ, Defined D (base τ))
    (hbasemeas : ∀ τ, MeasurableSet (base τ))
    (hclosed : ∀ τ, DeltaClosed μ δ h (base τ))
    (hdisj : Pairwise (Function.onFun Disjoint base))
    (w : ℤ) (hMc : 2 * w.natAbs + 2 * h + D ≤ M) :
    ∑ τ, (μ (symmDiff ((L ^ w) '' base τ) ((L ^ (w % (h : ℤ))) '' base τ))).toReal
      ≤ 2 * ((w / (h : ℤ)).natAbs : ℝ) * δ * (μ (⋃ τ, base τ)).toReal
        + (8 * (h : ℝ) * ((w / (h : ℤ)).natAbs : ℝ) ^ 2
            + 4 * (w.natAbs : ℝ) + 8 * (h : ℝ)) * η := by
  -- Set `q := w / (h:ℤ)`, `s := w % (h:ℤ)`, `n := q.natAbs`.
  set q := w / (h : ℤ)
  set s := w % (h : ℤ)
  set n := q.natAbs;
  -- Step A (translate by `s`).
  have stepA : ∑ τ, (μ (symmDiff ((L ^ w) '' (base τ)) ((L ^ s) '' (base τ)))).toReal ≤
    ∑ τ, (μ (symmDiff ((L ^ ((h : ℤ) * q)) '' (base τ)) (base τ))).toReal + 2 * (s.natAbs : ℝ) * η := by
      have stepA : ∑ τ, (μ (symmDiff ((L ^ w) '' (base τ)) ((L ^ s) '' (base τ)))).toReal = ∑ τ, (μ ((L ^ s) '' (symmDiff ((L ^ ((h : ℤ) * q)) '' (base τ)) (base τ)))).toReal := by
        have h_stepA : ∀ τ, symmDiff ((L ^ w) '' (base τ)) ((L ^ s) '' (base τ)) = (L ^ s) '' (symmDiff ((L ^ ((h : ℤ) * q)) '' (base τ)) (base τ)) := by
          intro τ
          have h_stepA : w = s + (h : ℤ) * q := by
            rw [ Int.emod_add_mul_ediv ];
          convert image_symmDiff_shift ( ( h : ℤ ) * q ) s ( base τ ) using 1;
          rw [ ← h_stepA ];
        exact Finset.sum_congr rfl fun _ _ => h_stepA _ ▸ rfl;
      convert translate_pair_diff_sum hμ ( fun τ => defined_shift ( hbasedef τ ) ( ( h : ℤ ) * q ) ) ( fun τ => ( hbasedef τ ).mono ( by linarith [ show ( ( h : ℤ ) * q ).natAbs ≥ 0 by positivity ] ) ) ( fun τ τ' hne => ?_ ) ( fun τ τ' hne => ?_ ) ( fun τ => measurableSet_L_zpow_image ( hbasemeas τ ) ) ( fun τ => hbasemeas τ ) s ?_ using 1;
      · exact Set.disjoint_image_of_injective ( Equiv.injective _ ) ( hdisj hne );
      · exact hdisj hne;
      · have h_bound : (h : ℤ) * q + s = w := by
          rw [ Int.mul_ediv_add_emod ];
        cases abs_cases w <;> cases abs_cases s <;> cases abs_cases ( h * q ) <;> linarith [ Int.emod_nonneg w ( by positivity : ( h : ℤ ) ≠ 0 ), Int.emod_lt_of_pos w ( by positivity : ( h : ℤ ) > 0 ) ];
  -- Step B (reduce `(h:ℤ)*q` to the nonnegative power `(h:ℤ)*(n:ℤ)`).
  have stepB : ∑ τ, (μ (symmDiff ((L ^ ((h : ℤ) * q)) '' (base τ)) (base τ))).toReal ≤
    ∑ τ, (μ (symmDiff ((L ^ ((h : ℤ) * (n : ℤ))) '' (base τ)) (base τ))).toReal + 2 * ((h : ℤ) * q).natAbs * η := by
      by_cases hq : 0 ≤ q;
      · simp +decide [ n, abs_of_nonneg hq ] ; positivity;
      · have stepB : ∀ τ, symmDiff ((L ^ ((h : ℤ) * q)) '' (base τ)) (base τ) = (L ^ ((h : ℤ) * q)) '' (symmDiff ((L ^ ((h : ℤ) * (n : ℤ))) '' (base τ)) (base τ)) := by
          intro τ
          have h_eq : (L ^ ((h : ℤ) * q)) '' (base τ) = (L ^ ((h : ℤ) * (-n : ℤ))) '' (base τ) := by
            grind;
          convert image_symmDiff_shift ( ( h : ℤ ) * n ) ( ( h : ℤ ) * ( -n ) ) ( base τ ) using 1;
          · simp +decide [ h_eq, symmDiff_comm ];
          · grind +qlia;
        have := translate_pair_diff_sum hμ ( fun τ => ( defined_shift ( hbasedef τ ) ( ( h : ℤ ) * n ) ) ) ( fun τ => ( hbasedef τ ).mono ( Nat.le_add_right _ _ ) ) ( fun τ τ' hττ' => ?_ ) ( fun τ τ' hττ' => hdisj hττ' ) ( fun τ => measurableSet_L_zpow_image ( hbasemeas τ ) ) ( fun τ => hbasemeas τ ) ( ( h : ℤ ) * q ) ?_ <;> simp_all +decide [ Int.natAbs_mul ];
        · exact Set.disjoint_image_of_injective ( Equiv.injective _ ) ( hdisj hττ' );
        · simp +zetaDelta at *;
          cases abs_cases ( w / h ) <;> cases abs_cases w <;> nlinarith [ Int.mul_ediv_add_emod w h, Int.emod_nonneg w ( by positivity : ( h : ℤ ) ≠ 0 ), Int.emod_lt_of_pos w ( by positivity : ( h : ℤ ) > 0 ) ];
  -- Step C (`approxInv_symmDiff_pow`).
  have stepC : ∑ τ, (μ (symmDiff ((L ^ ((h : ℤ) * (n : ℤ))) '' (base τ)) (base τ))).toReal ≤
    2 * (n : ℝ) * δ * (μ (⋃ τ, base τ)).toReal + 2 * (h : ℝ) * (n : ℝ) ^ 2 * η := by
      have stepC : (1 - δ) * (μ (⋃ τ, base τ)).toReal ≤
        ∑ τ, (μ ((L ^ (h : ℤ)) '' (base τ) ∩ (base τ))).toReal := by
          have stepC : (1 - δ) * (μ (⋃ τ, base τ)).toReal ≤
            ∑ τ, (1 - δ) * (μ (base τ)).toReal := by
              rw [ ← Finset.mul_sum _ _ _, MeasureTheory.measure_iUnion hdisj ( fun τ => hbasemeas τ ) ];
              rw [ tsum_fintype, ENNReal.toReal_sum ];
              exact fun _ _ => MeasureTheory.measure_ne_top _ _;
          exact stepC.trans ( Finset.sum_le_sum fun τ _ => hclosed τ );
      apply approxInv_symmDiff_pow hμ n;
      any_goals assumption;
      norm_num +zetaDelta at *;
      rw [ ← Int.ofNat_le ] at * ; simp_all +decide [ abs_mul, abs_of_nonneg ];
      cases abs_cases ( w / h ) <;> cases abs_cases w <;> nlinarith [ Int.mul_ediv_add_emod w h, Int.emod_nonneg w ( by positivity : ( h : ℤ ) ≠ 0 ), Int.emod_lt_of_pos w ( by positivity : ( h : ℤ ) > 0 ) ];
  -- Note that $|w| = |h * q + s| \geq |h * q| - |s|$ and $|s| < h$.
  have h_abs : (h * q).natAbs ≤ w.natAbs + h := by
    cases abs_cases ( h * q ) <;> cases abs_cases w <;> nlinarith [ Int.mul_ediv_add_emod w h, Int.emod_nonneg w ( by positivity : ( h : ℤ ) ≠ 0 ), Int.emod_lt_of_pos w ( by positivity : ( h : ℤ ) > 0 ) ];
  -- Note that $|s| < h$.
  have h_abs_s : s.natAbs ≤ h := by
    exact Nat.le_of_lt ( Int.natAbs_lt_natAbs_of_nonneg_of_lt ( Int.emod_nonneg _ ( by positivity ) ) ( Int.emod_lt_of_pos _ ( by positivity ) ) );
  nlinarith [ ( by norm_cast : ( h * q |> Int.natAbs : ℝ ) ≤ w.natAbs + h ), ( by norm_cast : ( s.natAbs : ℝ ) ≤ h ), show ( 0 : ℝ ) ≤ η * n ^ 2 by positivity, show ( 0 : ℝ ) ≤ η * n by positivity, show ( 0 : ℝ ) ≤ η by positivity ]

/-
If `Z` is disjoint from `B`, then `μ(Z ∩ A) ≤ μ(A △ B)`.
-/
lemma inter_le_symmDiff {Z A B : Set Cfg} {μ : Measure Cfg} [IsFiniteMeasure μ]
    (hZB : Z ∩ B = ∅) :
    (μ (Z ∩ A)).toReal ≤ (μ (symmDiff A B)).toReal := by
  gcongr;
  · exact MeasureTheory.measure_ne_top _ _;
  · intro x hx; rw [ symmDiff ] ; by_cases h : x ∈ B <;> simp_all +decide [ Set.ext_iff ] ;

/-
**Single height-class complement bound.**  For a pairwise-disjoint family
`g` of `D`-defined bases that are `δ`-closed under `L^h` and whose first `h`
floors avoid `Z`, the total measure of `Z` met by the `(i-k)`-translates
(`0 ≤ i < h`) is `O(t²δ·μ(⋃g) + t²h·η)`.
-/
lemma complement_class_bound {t h : ℕ} {δ η : ℝ} {M D : ℕ} {μ : Measure Cfg}
    [IsProbabilityMeasure μ]
    {Z : Set Cfg} {σ : Type*} [Fintype σ] {g : σ → Set Cfg}
    (ht : 1 ≤ t) (hh : 1 ≤ h) (hht : h ≤ 6 * t + 1) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hμ : ApproxInvMeasure M η μ)
    (hgdef : ∀ τ, Defined D (g τ))
    (hMD : D + 30 * t ≤ M)
    (hclosed : ∀ τ, DeltaClosed μ δ h (g τ))
    (hgdisj : Pairwise (Function.onFun Disjoint g))
    (hZdisj : ∀ (τ : σ) (i : ℕ), i < h → Disjoint Z ((L ^ (i : ℤ)) '' g τ))
    (k : ℤ) (hk : k.natAbs ≤ 2 * t) :
    ∑ i ∈ Finset.range h, ∑ τ : σ, (μ (Z ∩ (L ^ ((i : ℤ) - k)) '' g τ)).toReal
      ≤ 200 * (t : ℝ) ^ 2 * δ * (μ (⋃ τ, g τ)).toReal
        + 2000 * (t : ℝ) ^ 2 * (h : ℝ) * η := by
  trans (∑ i ∈ Finset.range h, ∑ τ, (μ (symmDiff ((L ^ (i - k)) '' (g τ)) ((L ^ ((i - k) % (h : ℤ))) '' (g τ)))).toReal);
  · refine' Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun τ _ => inter_le_symmDiff _;
    convert Set.disjoint_iff_inter_eq_empty.mp ( hZdisj τ ( Int.toNat ( ( i - k ) % h ) ) _ ) using 1;
    · rw [ Int.toNat_of_nonneg ( Int.emod_nonneg _ ( by positivity ) ) ];
    · linarith [ Int.emod_lt_of_pos ( i - k ) ( by positivity : 0 < ( h : ℤ ) ), Int.toNat_of_nonneg ( Int.emod_nonneg ( i - k ) ( by positivity : ( h : ℤ ) ≠ 0 ) ) ];
  · refine' le_trans ( Finset.sum_le_sum fun i hi => orbit_shift_symmDiff_bound hh hδ hη hμ _ _ _ hgdisj _ _ ) _;
    any_goals tauto;
    · exact fun τ => Defined.measurableSet ( hgdef τ );
    · grind;
    · -- Apply the bounds on the terms involving `δ` and `η`.
      have h_bounds : ∀ i ∈ Finset.range h, (↑((↑i - k) / ↑h).natAbs : ℝ) ≤ 8 * t ∧ (↑(↑i - k).natAbs : ℝ) ≤ 8 * t ∧ (↑h * ↑((↑i - k) / ↑h).natAbs ^ 2 : ℝ) ≤ 120 * t ^ 2 := by
        intro i hi
        have h_abs : (↑i - k).natAbs ≤ 8 * t := by
          grind
        have h_div_abs : ((↑i - k) / ↑h).natAbs ≤ 8 * t := by
          exact le_trans ( Nat.le_of_lt_succ ( by cases abs_cases ( ( i - k ) / h ) <;> cases abs_cases ( i - k ) <;> nlinarith [ Int.mul_ediv_add_emod ( i - k ) h, Int.emod_nonneg ( i - k ) ( by positivity : ( h : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( i - k ) ( by positivity : ( h : ℤ ) > 0 ) ] ) ) h_abs
        have h_prod_abs : (↑h * ((↑i - k) / ↑h).natAbs ^ 2 : ℝ) ≤ 120 * t ^ 2 := by
          have h_prod_abs : (↑h * ((↑i - k) / ↑h).natAbs ^ 2 : ℝ) ≤ (↑((↑i - k).natAbs) + ↑h) * ((↑i - k) / ↑h).natAbs := by
            have h_prod_abs : (↑h * ((↑i - k) / ↑h).natAbs : ℝ) ≤ (↑((↑i - k).natAbs) + ↑h) := by
              norm_cast;
              cases abs_cases ( ( i : ℤ ) - k ) <;> cases abs_cases ( ( i - k ) / h : ℤ ) <;> nlinarith [ Int.mul_ediv_add_emod ( i - k ) h, Int.emod_nonneg ( i - k ) ( by positivity : ( h : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( i - k ) ( by positivity : ( h : ℤ ) > 0 ) ];
            nlinarith only [ h_prod_abs ];
          refine le_trans h_prod_abs ?_;
          exact le_trans ( mul_le_mul ( add_le_add ( Nat.cast_le.mpr h_abs ) ( Nat.cast_le.mpr hht ) ) ( Nat.cast_le.mpr h_div_abs ) ( by positivity ) ( by positivity ) ) ( by norm_cast; nlinarith only [ ht, hh, hht, h_abs, h_div_abs ] )
        exact ⟨by
        exact_mod_cast h_div_abs, by
          exact_mod_cast h_abs, by
          convert h_prod_abs using 1⟩;
      refine' le_trans ( Finset.sum_le_sum fun i hi => add_le_add ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left ( h_bounds i hi |>.1 ) zero_le_two ) hδ |> mul_le_mul_of_nonneg_right <| ENNReal.toReal_nonneg ) <| mul_le_mul_of_nonneg_right ( show ( 8 * h * ( ( i - k ) / h |> Int.natAbs ) ^ 2 + 4 * ( i - k |> Int.natAbs ) + 8 * h : ℝ ) ≤ 120 * t ^ 2 * 8 + 4 * 8 * t + 8 * h by nlinarith only [ h_bounds i hi ] ) hη ) _;
      norm_num;
      refine' add_le_add _ _;
      · nlinarith [ show ( h : ℝ ) ≤ 6 * t + 1 by norm_cast, show ( t : ℝ ) ≥ 1 by norm_cast, show ( 0 : ℝ ) ≤ δ * ( μ ( ⋃ τ, g τ ) |> ENNReal.toReal ) by positivity, show ( 0 : ℝ ) ≤ t * δ * ( μ ( ⋃ τ, g τ ) |> ENNReal.toReal ) by positivity ];
      · nlinarith only [ show ( h : ℝ ) ≤ 6 * t + 1 by norm_cast, show ( t : ℝ ) ≥ 1 by norm_cast, show ( h : ℝ ) * η ≥ 0 by positivity, show ( t : ℝ ) * η ≥ 0 by positivity, show ( h : ℝ ) * t * η ≥ 0 by positivity, show ( t : ℝ ) ^ 2 * η ≥ 0 by positivity ]

/-
**Aggregated `S'` bound** (grouping the towers by height).  The total
measure of `Z` met by the `(i-k)`-translates of all tower floors is
`O(t⁴η + t³δ)`.
-/
lemma complement_S' {t : ℕ} {δ η : ℝ} {M D : ℕ} {μ : Measure Cfg}
    [IsProbabilityMeasure μ]
    {Z : Set Cfg} {ι : Type} [Fintype ι] {base : ι → Set Cfg} {height : ι → ℕ}
    (ht : 1 ≤ t) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hμ : ApproxInvMeasure M η μ)
    (hMD : D + 30 * t ≤ M)
    (hheight : ∀ τ, height τ ≤ 6 * t + 1)
    (hfloordef : ∀ τ i, i < height τ → Defined D (towerFloor (base τ) i))
    (hclosed : ∀ τ, DeltaClosed μ δ (height τ) (base τ))
    (hdisj : ∀ τ τ' : ι, ∀ i i' : ℕ, i < height τ → i' < height τ' →
      ¬ (τ = τ' ∧ i = i') →
      Disjoint (towerFloor (base τ) i) (towerFloor (base τ') i'))
    (hZdisj : ∀ τ i, i < height τ → Disjoint Z (towerFloor (base τ) i))
    (k : ℤ) (hk : k.natAbs ≤ 2 * t) :
    ∑ τ : ι, ∑ i ∈ Finset.range (height τ),
        (μ (Z ∩ (L ^ ((i : ℤ) - k)) '' base τ)).toReal
      ≤ 100000 * ((t : ℝ) ^ 4 * η + (t : ℝ) ^ 3 * δ) := by
  refine' le_trans _ _;
  exact ∑ H ∈ Finset.range ( 6 * t + 2 ), ( 200 * ( t : ℝ ) ^ 2 * δ + 2000 * ( t : ℝ ) ^ 2 * ( H : ℝ ) * η );
  · refine' le_trans _ ( Finset.sum_le_sum fun H _ => show ( 200 * t ^ 2 * δ + 2000 * t ^ 2 * H * η ) ≥ ∑ i ∈ Finset.range H, ∑ τ ∈ Finset.filter ( fun τ => height τ = H ) Finset.univ, ( μ ( Z ∩ ( L ^ ( i - k : ℤ ) ) '' base τ ) |> ENNReal.toReal ) from _ );
    · have h_regroup : ∑ τ, ∑ i ∈ Finset.range (height τ), (μ (Z ∩ (L ^ (i - k : ℤ)) '' base τ)).toReal = ∑ H ∈ Finset.range (6 * t + 2), ∑ τ ∈ Finset.filter (fun τ => height τ = H) Finset.univ, ∑ i ∈ Finset.range H, (μ (Z ∩ (L ^ (i - k : ℤ)) '' base τ)).toReal := by
        simp +decide only [Finset.sum_sigma'];
        refine' Finset.sum_bij ( fun x hx => ⟨ height x.fst, x.fst, x.snd ⟩ ) _ _ _ _ <;> simp +decide;
        · exact fun a ha => ⟨ Nat.lt_succ_of_le ( hheight a.fst ), ha ⟩;
        · grind;
      rw [ h_regroup ];
      exact Finset.sum_le_sum fun _ _ => Finset.sum_comm.le;
    · by_cases hH : 1 ≤ H <;> simp_all +decide [];
      · have := @complement_class_bound t H δ η M D μ;
        specialize @this ( by infer_instance ) Z ( { τ : ι // height τ = H } ) ( by infer_instance ) ( fun τ => base τ ) ht hH ( by linarith ) hδ hη hμ ( fun τ => ?_ ) ( by linarith ) ( fun τ => ?_ ) ( fun τ τ' h => ?_ ) ( fun τ i hi => ?_ ) k hk;
        · simpa [ towerFloor ] using hfloordef τ.1 0 ( by linarith [ τ.2 ] );
        · simpa [ τ.2 ] using hclosed τ.1;
        · convert hdisj τ.val τ'.val 0 0 _ _ _ using 1 <;> simp +decide [ τ.2, τ'.2 ];
          · linarith;
          · linarith;
          · exact fun h' => h <| Subtype.ext h';
        · grind +qlia;
        · convert this.trans _ using 1;
          · refine' Finset.sum_congr rfl fun i hi => _;
            refine' Finset.sum_bij ( fun τ _ => ⟨ τ, by aesop ⟩ ) _ _ _ _ <;> aesop;
          · exact add_le_add ( mul_le_of_le_one_right ( by positivity ) ( ENNReal.toReal_le_of_le_ofReal ( by positivity ) ( by exact le_trans ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by norm_num ) ) ) ) le_rfl;
      · positivity;
  · norm_num [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
    rw [ ← Nat.cast_sum, Finset.sum_range_id ];
    norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mod_two_of_bodd ] ; ring_nf;
    nlinarith [ show ( t : ℝ ) ≥ 1 by norm_cast, show ( t : ℝ ) ^ 3 ≥ t ^ 2 by gcongr <;> norm_cast, show ( t : ℝ ) ^ 4 ≥ t ^ 3 by gcongr <;> norm_cast, mul_nonneg hδ hη ]

/-
**Strip the outer translate** (`approxInv_pow`).  The total measure of the
floors met by `L^k Z` differs from the `S'` quantity by at most `|k|η ≤ 2tη`.
-/
set_option maxHeartbeats 1600000 in
lemma complement_strip {t : ℕ} {η : ℝ} {M D : ℕ} {μ : Measure Cfg}
    [IsProbabilityMeasure μ]
    {Z : Set Cfg} {ι : Type} [Fintype ι] {base : ι → Set Cfg} {height : ι → ℕ}
    (ht : 1 ≤ t) (hη : 0 ≤ η)
    (hμ : ApproxInvMeasure M η μ)
    (hZdef : Defined D Z)
    (hMD : D + 30 * t ≤ M)
    (hheight : ∀ τ, height τ ≤ 6 * t + 1)
    (hfloordef : ∀ τ i, i < height τ → Defined D (towerFloor (base τ) i))
    (hdisj : ∀ τ τ' : ι, ∀ i i' : ℕ, i < height τ → i' < height τ' →
      ¬ (τ = τ' ∧ i = i') →
      Disjoint (towerFloor (base τ) i) (towerFloor (base τ') i'))
    (k : ℤ) (hk : k.natAbs ≤ 2 * t) :
    ∑ τ : ι, ∑ i ∈ Finset.range (height τ),
        (μ ((L ^ k) '' Z ∩ towerFloor (base τ) i)).toReal
      ≤ (∑ τ : ι, ∑ i ∈ Finset.range (height τ),
          (μ (Z ∩ (L ^ ((i : ℤ) - k)) '' base τ)).toReal) + 2 * (t : ℝ) * η := by
  have h_approxInv_pow : ∀ (J : Type) [Fintype J] (b : J → Set Cfg) (hJ : ∀ j, Defined (D + 8 * t) (b j)) (hJdisj : Pairwise (Function.onFun Disjoint b)) (hJmeas : ∀ j, MeasurableSet (b j)), ∑ j, |(μ ((L ^ k) '' (b j))).toReal - (μ (b j)).toReal| ≤ (k.natAbs : ℝ) * η := by
    intros J _ b hb hb_disj hb_meas;
    convert approxInv_pow hμ ( show k.natAbs + ( D + 8 * t ) ≤ M from by linarith ) hb_disj hb using 1;
  have h_sum_le : ∑ τ : ι, ∑ i ∈ Finset.range (height τ), (μ ((L ^ k) '' (Z ∩ (L ^ ((i : ℤ) - k)) '' (base τ)))).toReal ≤ ∑ τ : ι, ∑ i ∈ Finset.range (height τ), (μ (Z ∩ (L ^ ((i : ℤ) - k)) '' (base τ))).toReal + (k.natAbs : ℝ) * η := by
    have h_sum_le : ∑ j : Σ τ : ι, Fin (height τ), |(μ ((L ^ k) '' (Z ∩ (L ^ ((j.2 : ℤ) - k)) '' (base j.1)))).toReal - (μ (Z ∩ (L ^ ((j.2 : ℤ) - k)) '' (base j.1))).toReal| ≤ (k.natAbs : ℝ) * η := by
      apply h_approxInv_pow;
      · intro j j' hj; specialize hdisj j.1 j'.1 ( j.2 : ℕ ) ( j'.2 : ℕ ) ; simp_all +decide [ Set.disjoint_left ] ;
        intro a ha₁ ha₂ ha₃; specialize hdisj ( by contrapose! hj; aesop ) ; simp_all +decide [ zpow_sub ] ;
        contrapose! hdisj; simp_all +decide [ Equiv.Perm.mul_def ] ;
        use (L ^ k) a;
        simp_all +decide [ Equiv.Perm.inv_def ];
        convert And.intro ha₂ ha₃ using 1;
        · rw [ show ( Equiv.symm ( L ^ ( j.snd : ℕ ) ) ) = L ^ ( - ( j.snd : ℤ ) ) from ?_ ];
          · rw [ ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply ] ; group;
          · ext; simp +decide [ Equiv.Perm.inv_def ] ;
        · rw [ show ( Equiv.symm ( L ^ ( j'.snd : ℕ ) ) ) = L ^ ( - ( j'.snd : ℤ ) ) from ?_ ];
          · rw [ ← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply ] ; group;
          · ext; simp +decide [] ;
      · intro j;
        refine' MeasurableSet.inter _ _;
        · exact hZdef.measurableSet;
        · apply measurableSet_L_zpow_image;
          exact Defined.measurableSet ( hfloordef j.1 0 ( by linarith [ Fin.is_lt j.2 ] ) ) |> fun h => by simpa [ towerFloor ] using h;
      · intro j;
        apply defined_inter;
        · exact Defined.mono ( by linarith ) hZdef;
        · apply Defined.mono;
          rotate_right;
          exact D + Int.natAbs ( j.2 - k );
          · grind;
          · convert defined_shift ( hfloordef j.1 0 ( by linarith [ Fin.is_lt j.2 ] ) ) ( j.2 - k ) using 1;
            unfold towerFloor; aesop;
    have h_sum_le : ∑ j : Σ τ : ι, Fin (height τ), (μ ((L ^ k) '' (Z ∩ (L ^ ((j.2 : ℤ) - k)) '' (base j.1)))).toReal ≤ ∑ j : Σ τ : ι, Fin (height τ), (μ (Z ∩ (L ^ ((j.2 : ℤ) - k)) '' (base j.1))).toReal + (k.natAbs : ℝ) * η := by
      have h_sum_le : ∑ j : Σ τ : ι, Fin (height τ), (μ ((L ^ k) '' (Z ∩ (L ^ ((j.2 : ℤ) - k)) '' (base j.1)))).toReal - ∑ j : Σ τ : ι, Fin (height τ), (μ (Z ∩ (L ^ ((j.2 : ℤ) - k)) '' (base j.1))).toReal ≤ ∑ j : Σ τ : ι, Fin (height τ), |(μ ((L ^ k) '' (Z ∩ (L ^ ((j.2 : ℤ) - k)) '' (base j.1)))).toReal - (μ (Z ∩ (L ^ ((j.2 : ℤ) - k)) '' (base j.1))).toReal| := by
        rw [ ← Finset.sum_sub_distrib ] ; exact Finset.sum_le_sum fun _ _ => le_abs_self _;
      linarith;
    convert h_sum_le using 1 <;> norm_num [ Finset.sum_sigma', Finset.sum_range ];
  convert h_sum_le.trans _ using 1;
  · refine' Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i hi => _;
    rw [ Set.image_inter ];
    · simp +decide [ ← Set.image_comp ];
      congr! 2;
      congr! 2;
      rw [ ← Equiv.Perm.mul_apply, ← zpow_add ] ; norm_num;
    · exact Equiv.injective _;
  · gcongr ; norm_cast

/-
**Escape glue.**  If `S` is covered by `E` together with the tower floors,
then `μ(S) ≤ μ(E) + ∑ μ(S ∩ floor)`.
-/
lemma escape_glue {μ : Measure Cfg} [IsProbabilityMeasure μ]
    {ι : Type} [Fintype ι] {base : ι → Set Cfg} {height : ι → ℕ}
    {S E : Set Cfg}
    (hsub : S ⊆ E ∪ ⋃ τ : ι, ⋃ i ∈ Finset.range (height τ),
      towerFloor (base τ) i) :
    (μ S).toReal ≤ (μ E).toReal + ∑ τ : ι, ∑ i ∈ Finset.range (height τ),
        (μ (S ∩ towerFloor (base τ) i)).toReal := by
  refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| show S ⊆ E ∪ ⋃ τ, ⋃ i ∈ Finset.range ( height τ ), S ∩ towerFloor ( base τ ) i from _ ) _;
  · exact MeasureTheory.measure_ne_top _ _;
  · intro x hx; specialize hsub hx; aesop;
  · refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_union_le _ _ ) _;
    · exact ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ MeasureTheory.measure_lt_top _ _, MeasureTheory.measure_lt_top _ _ ⟩ );
    · refine' le_trans ( ENNReal.toReal_add_le ) _;
      refine' add_le_add le_rfl _;
      refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_iUnion_le _ ) _;
      · simp +decide [];
      · rw [ ENNReal.tsum_toReal_eq ];
        · rw [ tsum_fintype ];
          gcongr;
          refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_biUnion_finset_le _ _ ) _;
          · exact ne_of_lt ( lt_of_le_of_lt ( Finset.sum_le_sum fun _ _ => MeasureTheory.measure_mono ( Set.inter_subset_right ) ) ( by simp +decide ) );
          · rw [ ENNReal.toReal_sum ];
            exact fun _ _ => MeasureTheory.measure_ne_top _ _;
        · exact fun _ => MeasureTheory.measure_ne_top _ _

/-! ## 2. The complement bound (`lem:complement-bound`)

The statement is phrased abstractly over the *output* of the periodic covering:
a pairwise-disjoint family of `δ`-closed, `D`-defined towers of height `≤ 6t+1`,
together with an `ℓ`-defined error set `E` of measure `< υ`, whose union is the
periodic part.  Given a marker set `Z ⊆ Ξ_aper` disjoint from all tower floors
and `D'`-defined, with `μ` being `(M,η)`-invariant for `M` large enough, the
measure that translates of `Z` escape `Ξ_aper` is `O(t⁴η + t³δ + υ)`.
-/

/-- **`lem:complement-bound`.**

With the periodic-covering data made explicit (a pairwise-disjoint family of
`δ`-closed, `D`-defined towers of height `≤ 6t+1`, an error set `E` with
`μ(E) < υ`, and a marker set `Z ⊆ Ξ_aper` disjoint from all floors, all
`D`-defined with `D ≤ M/(2t)` while `μ` is `(M,η)`-invariant), the measure that
translates of `Z` escape `Ξ_aper` is `O(t⁴η + t³δ + υ)`.  The escape set is
assumed contained in the periodic covering `E ∪ ⋃ floors`, which is exactly what
holds in the assembly.  The `O(·)` constant is packaged as the existential
`Ccb`.

**Faithfulness note.**  The proof shifts the (`D`-defined) marker and tower
bases by amounts of size `O(t)`, so it requires the `(M,η)`-invariance window
`M` to dominate `D` *and* those shifts.  The abstract hypothesis `D ≤ M/(2t)`
alone does not control the shifts when both `D` and `M` are small, so we add the
explicit largeness hypothesis `D + 30*t ≤ M`.  This is satisfied in every use of
the lemma, where `M = M₀ ≥ winBound t υ δ` is taken far larger than `t` and `D`. -/
theorem complement_bound :
    ∃ Ccb : ℝ, 0 < Ccb ∧
      ∀ (t : ℕ) (υ δ η : ℝ) (M D : ℕ) (μ : Measure Cfg) [IsProbabilityMeasure μ]
        (Ξaper Z E : Set Cfg) (ι : Type) (_ : Fintype ι)
        (base : ι → Set Cfg) (height : ι → ℕ),
        1 ≤ t → 0 < υ → 0 < δ → 0 < η → ApproxInvMeasure M η μ →
        Defined D Ξaper → Defined D Z → (D : ℝ) ≤ (M : ℝ) / (2 * t) →
        D + 30 * t ≤ M →
        (∀ τ : ι, height τ ≤ 6 * t + 1) →
        (∀ τ : ι, ∀ i, i < height τ → Defined D (towerFloor (base τ) i)) →
        (∀ τ : ι, DeltaClosed μ δ (height τ) (base τ)) →
        (∀ τ τ' : ι, ∀ i i' : ℕ, i < height τ → i' < height τ' →
          ¬ (τ = τ' ∧ i = i') →
          Disjoint (towerFloor (base τ) i) (towerFloor (base τ') i')) →
        (μ E).toReal < υ → Z ⊆ Ξaper →
        (∀ τ : ι, ∀ i, i < height τ → Disjoint Z (towerFloor (base τ) i)) →
          ∀ k₁ k₂ : ℤ, k₁ ∈ Finset.Icc (-(2 * t : ℤ)) (2 * t) →
            k₂ ∈ Finset.Icc (-(2 * t : ℤ)) (2 * t) →
            (((L ^ k₁) '' Z) \ ((L ^ k₂) '' Ξaper)) ⊆
                E ∪ ⋃ τ : ι, ⋃ i ∈ Finset.range (height τ),
                  towerFloor (base τ) i →
            (μ (((L ^ k₁) '' Z) \ ((L ^ k₂) '' Ξaper))).toReal ≤
              Ccb * ((t : ℝ) ^ 4 * η + (t : ℝ) ^ 3 * δ + υ) := by
  refine ⟨100002, by norm_num, ?_⟩
  intro t υ δ η M D μ _ Ξaper Z E ι _ base height ht hυ hδ hη hμ _hΞdef hZdef _hDM hMlarge hheight hfloordef hclosed
    hdisj hEυ _hZΞ hZdisj k₁ k₂ hk₁ _hk₂ hsub
  have hk1nat : k₁.natAbs ≤ 2 * t := by
    rw [Finset.mem_Icc] at hk₁; omega
  -- Escape glue: the escape set is covered by `E` and the floors.
  have hglue := escape_glue (μ := μ) (base := base) (height := height)
    (S := ((L ^ k₁) '' Z) \ ((L ^ k₂) '' Ξaper)) (E := E) hsub
  -- Each `S ∩ floor` is contained in `(L^k₁ Z) ∩ floor`.
  have hmono : ∀ τ : ι, ∀ i ∈ Finset.range (height τ),
      (μ ((((L ^ k₁) '' Z) \ ((L ^ k₂) '' Ξaper)) ∩ towerFloor (base τ) i)).toReal
        ≤ (μ ((L ^ k₁) '' Z ∩ towerFloor (base τ) i)).toReal := by
    intro τ i _
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (Set.inter_subset_inter_left _ Set.diff_subset))
  have hsum_mono :
      ∑ τ : ι, ∑ i ∈ Finset.range (height τ),
          (μ ((((L ^ k₁) '' Z) \ ((L ^ k₂) '' Ξaper)) ∩ towerFloor (base τ) i)).toReal
        ≤ ∑ τ : ι, ∑ i ∈ Finset.range (height τ),
          (μ ((L ^ k₁) '' Z ∩ towerFloor (base τ) i)).toReal :=
    Finset.sum_le_sum fun τ _ => Finset.sum_le_sum (hmono τ)
  have hstrip := complement_strip (μ := μ) (base := base) (height := height)
    (Z := Z) ht (le_of_lt hη) hμ hZdef hMlarge hheight hfloordef hdisj k₁ hk1nat
  have hS' := complement_S' (μ := μ) (base := base) (height := height)
    (Z := Z) ht (le_of_lt hδ) (le_of_lt hη) hμ hMlarge hheight hfloordef hclosed
    hdisj hZdisj k₁ hk1nat
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have htpos : (0 : ℝ) ≤ (t : ℝ) := by positivity
  have hηnn : (0 : ℝ) ≤ η := le_of_lt hη
  have hδnn : (0 : ℝ) ≤ δ := le_of_lt hδ
  -- `2 t η ≤ 2 t⁴ η`.
  have htη : 2 * (t : ℝ) * η ≤ 2 * (t : ℝ) ^ 4 * η := by
    have ht4 : (t : ℝ) ≤ (t : ℝ) ^ 4 := by
      calc (t : ℝ) = (t : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (t : ℝ) ^ 4 := pow_le_pow_right₀ ht1 (by norm_num)
    nlinarith [ht4, hηnn]
  have e2 : (100002 : ℝ) * ((t : ℝ) ^ 4 * η + (t : ℝ) ^ 3 * δ + υ)
      = 100000 * ((t : ℝ) ^ 4 * η + (t : ℝ) ^ 3 * δ)
          + (2 * (t : ℝ) ^ 4 * η + 2 * (t : ℝ) ^ 3 * δ + 100002 * υ) := by ring
  rw [e2]
  have ht3δ : (0 : ℝ) ≤ (t : ℝ) ^ 3 * δ := mul_nonneg (by positivity) hδnn
  linarith [hglue, hsum_mono, hstrip, hS', le_of_lt hEυ, htη, le_of_lt hυ, ht3δ]

/-! ## 3–4. Kakutani–Rokhlin construction and final assembly

The final assembly combines:
* the periodic covering (`covering_per_seq`): error `E` + `δ`-closed towers of
  height `≤ 6t+1` covering `X_per^ℓ(t)`;
* the marker set (`marker_lemma`) for `Ξ_aper`, turned via the first-return
  ("Kakutani–Rokhlin") construction into towers of height `t+1 ≤ j ≤ 2t+1`
  covering `X_aper^ℓ(t)` up to error `O(t⁶(η+δ+υ))` (using `complement_bound`);
* a final split of the high towers by `π_j` to enforce the singleton-projection
  conclusion.

This produces `prop_decomp` (proved in `TowerDecomp.lean`).  The construction is
recorded here as the remaining Phase-2 target; the elementary manipulations in
Section 1 and the complement bound in Section 2 are its proved building blocks.
-/

end LamplighterStability.Dynamics