import RequestProject.Dynamics.ShiftSpace

/-!
# Approximately invariant measures (Block B)

This file formalizes Definition `def:approx_inv_meas` (approximately invariant
measure on the full shift) and the elementary measure-combinatorics lemma
`lem:approx_inv_measures`, both from the paper.  These are the genuinely
provable measure-theoretic ingredients of the tower-decomposition machinery.

The deeper `lem:complement-bound` (which relies on the marker construction) is
stated here as an interface to be supplied by the marker / decomposition layer.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators
open scoped Classical

/-- The right shift `L` as a measurable equivalence of `Cfg = ℤ → Bool`. -/
def shiftME : Cfg ≃ᵐ Cfg where
  toEquiv := L
  measurable_toFun := by
    refine measurable_pi_lambda _ (fun i => ?_)
    simpa using measurable_pi_apply (i - 1)
  measurable_invFun := by
    refine measurable_pi_lambda _ (fun i => ?_)
    simpa using measurable_pi_apply (i + 1)

@[simp] lemma shiftME_coe : (shiftME : Cfg → Cfg) = (L : Cfg → Cfg) := rfl

lemma measurableSet_shift_image {S : Set Cfg} (hS : MeasurableSet S) :
    MeasurableSet ((L : Equiv.Perm Cfg) '' S) :=
  shiftME.measurableSet_image.mpr hS

/-- **Definition (approximately invariant measure).**  A probability measure `μ`
on `X = {0,1}^ℤ` is `(M,η)`-invariant if the marginals of `μ` and `L_*μ` on
`{0,1}^{F_M}` are `η`-close in total variation:
`∑_{b ∈ {0,1}^{F_M}} |μ(L⟦b⟧) − μ(⟦b⟧)| ≤ η`. -/
def ApproxInvMeasure (M : ℕ) (η : ℝ) (μ : Measure Cfg) : Prop :=
  ∑ b : Win M → Bool, |(μ ((L : Equiv.Perm Cfg) '' cyl M b)).toReal
      - (μ (cyl M b)).toReal| ≤ η

/-! ## Definability lemmas -/

/-- A coarser window determines a finer one: if two configurations agree on
`F_n` they agree on `F_m` for `m ≤ n`. -/
lemma proj_mono {m n : ℕ} (hmn : m ≤ n) {x y : Cfg} (h : proj n x = proj n y) :
    proj m x = proj m y := by
  funext i
  have hi : i.1 ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
    have := i.2
    simp only [Finset.mem_Icc] at this ⊢
    exact ⟨le_trans (by exact_mod_cast neg_le_neg (by exact_mod_cast hmn)) this.1,
      le_trans this.2 (by exact_mod_cast hmn)⟩
  have := congrFun h ⟨i.1, hi⟩
  simpa [proj] using this

/-- `n`-definability is monotone in `n`. -/
lemma Defined.mono {m n : ℕ} (hmn : m ≤ n) {S : Set Cfg} (hS : Defined m S) :
    Defined n S := by
  intro x y hxy
  exact hS x y (proj_mono hmn hxy)

/-! ## Cylinder decomposition of a definable set -/

/-- The set of `M`-patterns whose cylinder is contained in `S`. -/
noncomputable def patternsOf (M : ℕ) (S : Set Cfg) : Finset (Win M → Bool) :=
  Finset.univ.filter (fun b => cyl M b ⊆ S)

lemma mem_patternsOf {M : ℕ} {S : Set Cfg} {b : Win M → Bool} :
    b ∈ patternsOf M S ↔ cyl M b ⊆ S := by
  simp [patternsOf]

/-- Every cylinder set is nonempty (a pattern always has an extension). -/
lemma cyl_nonempty (M : ℕ) (b : Win M → Bool) : (cyl M b).Nonempty := by
  classical
  refine ⟨fun i => if h : i ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) then b ⟨i, h⟩ else false, ?_⟩
  funext i
  simp only [proj, i.2, dif_pos]

/-- Patterns of disjoint sets are disjoint as finsets. -/
lemma patternsOf_disjoint {M : ℕ} {S T : Set Cfg} (h : Disjoint S T) :
    Disjoint (patternsOf M S) (patternsOf M T) := by
  rw [Finset.disjoint_left]
  intro b hbS hbT
  obtain ⟨x, hx⟩ := cyl_nonempty M b
  exact (Set.disjoint_left.mp h ((mem_patternsOf.mp hbS) hx) ((mem_patternsOf.mp hbT) hx))

/-- An `M`-defined set is the (finite, disjoint) union of the `M`-cylinders it
contains. -/
lemma defined_eq_biUnion_cyl {M : ℕ} {S : Set Cfg} (hS : Defined M S) :
    S = ⋃ b ∈ patternsOf M S, cyl M b := by
  apply Set.eq_of_subset_of_subset
  · intro x hx
    refine Set.mem_biUnion (mem_patternsOf.mpr ?_) (mem_cyl_proj M x)
    intro y hy
    exact (hS y x hy).2 hx
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp hx
    exact (mem_patternsOf.mp hb) hxb

/-- Measure of an `M`-defined measurable set as a sum over its cylinders. -/
lemma measure_defined_eq_sum {M : ℕ} {S : Set Cfg} (hS : Defined M S)
    (μ : Measure Cfg) :
    μ S = ∑ b ∈ patternsOf M S, μ (cyl M b) := by
  conv_lhs => rw [defined_eq_biUnion_cyl hS]
  refine measure_biUnion_finset ?_ (fun b _ => measurableSet_cyl M b)
  intro b _ b' _ hbb'
  exact cyl_disjoint hbb'

/-- Measure of `L` applied to an `M`-defined measurable set, as a sum over its
cylinders. -/
lemma measure_shift_defined_eq_sum {M : ℕ} {S : Set Cfg} (hS : Defined M S)
    (μ : Measure Cfg) :
    μ ((L : Equiv.Perm Cfg) '' S)
      = ∑ b ∈ patternsOf M S, μ ((L : Equiv.Perm Cfg) '' cyl M b) := by
  conv_lhs => rw [defined_eq_biUnion_cyl hS, Set.image_iUnion₂]
  refine measure_biUnion_finset ?_
    (fun b _ => measurableSet_shift_image (measurableSet_cyl M b))
  intro b _ b' _ hbb'
  exact Set.disjoint_image_of_injective (Equiv.injective L) (cyl_disjoint hbb')

/-
Action of the integer power of the shift on coordinates: `(L^i x) n = x (n-i)`.
-/
lemma L_zpow_apply (i : ℤ) (x : Cfg) (n : ℤ) : (L ^ i) x n = x (n - i) := by
  rcases i with ( _ | i ) <;> norm_num at *;
  · induction ‹ℕ› <;> simp_all +decide [ pow_succ' ];
    rename_i k hk;
    convert congr_arg ( fun f => f ( n - 1 ) ) ( show ( L ^ k ) x = fun i => x ( i - k ) from ?_ ) using 1;
    · grind;
    · refine' Nat.recOn k _ _ <;> simp_all +decide [ pow_succ', Function.comp ];
      intro n hn; ext i; simp +decide [ L_apply ] ; ring;
  · induction' i with i ih generalizing x n <;> simp_all +decide [ pow_succ' ];
    convert ih ( L.symm x ) n using 1 ; simp +decide [ Int.negSucc_eq, sub_eq_add_neg, add_assoc ]

/-
Shifting a `k`-defined set by `L^i` yields a `(k+|i|)`-defined set.
-/
lemma defined_shift {k : ℕ} {S : Set Cfg} (hS : Defined k S) (i : ℤ) :
    Defined (k + i.natAbs) ((L ^ i) '' S) := by
  intro x y hxy
  have h_proj : ∀ m : ℤ, |m| ≤ k → (x (m + i)) = (y (m + i)) := by
    intro m hm; have := congr_fun hxy ⟨ m + i, ?_ ⟩ ; simp_all +decide [ proj ] ;
    grind;
  convert hS ( ( L ^ ( -i ) ) x ) ( ( L ^ ( -i ) ) y ) _ using 1 <;> simp_all +decide [];
  ext ⟨ m, hm ⟩ ; specialize h_proj m ; simp_all +decide [ proj ] ;
  convert h_proj ( abs_le.mpr ⟨ by linarith [ Finset.mem_Icc.mp hm ], by linarith [ Finset.mem_Icc.mp hm ] ⟩ ) using 1;
  · convert L_zpow_apply ( -i ) x m using 1 ; ring;
    · simp +decide [ zpow_neg ];
    · grind +splitIndPred;
  · convert L_zpow_apply ( -i ) y m using 1 ; ring;
    · simp +decide [ zpow_neg ];
    · ring

/-! ## The main lemma `lem:approx_inv_measures` -/

/-
**Base case (one shift step).**  For an `(M,η)`-invariant measure and a
finite pairwise-disjoint collection of `M`-defined sets, the total variation
between the family and its `L`-translate is at most `η`.
-/
lemma approxInv_one_step {M : ℕ} {η : ℝ} {μ : Measure Cfg} [IsFiniteMeasure μ]
    (hμ : ApproxInvMeasure M η μ) {ι : Type*} [Fintype ι] {b : ι → Set Cfg}
    (hdisj : Pairwise (Function.onFun Disjoint b))
    (hdef : ∀ i, Defined M (b i)) :
    ∑ i, |(μ ((L : Equiv.Perm Cfg) '' b i)).toReal - (μ (b i)).toReal| ≤ η := by
  refine' le_trans _ hμ;
  -- Applying the triangle inequality to the sum, we get:
  have h_triangle : ∀ i, |(μ (L '' (b i))).toReal - (μ (b i)).toReal| ≤ ∑ p ∈ patternsOf M (b i), |(μ (L '' (cyl M p))).toReal - (μ (cyl M p)).toReal| := by
    intro i
    have h_diff : (μ (L '' (b i))).toReal - (μ (b i)).toReal = ∑ p ∈ patternsOf M (b i), ((μ (L '' (cyl M p))).toReal - (μ (cyl M p)).toReal) := by
      rw [ measure_shift_defined_eq_sum ( hdef i ) μ, measure_defined_eq_sum ( hdef i ) μ, ENNReal.toReal_sum, ENNReal.toReal_sum, Finset.sum_sub_distrib ]; all_goals exact fun _ _ => MeasureTheory.measure_ne_top _ _;
    exact h_diff ▸ Finset.abs_sum_le_sum_abs _ _
  generalize_proofs at *;
  refine' le_trans ( Finset.sum_le_sum fun i _ => h_triangle i ) _;
  rw [ ← Finset.sum_biUnion ];
  · exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => abs_nonneg _;
  · exact fun i _ j _ hij => patternsOf_disjoint ( hdisj hij )

/-
`lem:approx_inv_measures (i)`: the aggregated total variation under `L^q` is
at most `|q|·η`.
-/
lemma approxInv_pow {M : ℕ} {η : ℝ} {μ : Measure Cfg} [IsFiniteMeasure μ]
    (hμ : ApproxInvMeasure M η μ) {ι : Type*} [Fintype ι] {b : ι → Set Cfg}
    {k : ℕ} {q : ℤ} (hqk : q.natAbs + k ≤ M)
    (hdisj : Pairwise (Function.onFun Disjoint b))
    (hdef : ∀ i, Defined k (b i)) :
    ∑ i, |(μ ((L ^ q) '' b i)).toReal - (μ (b i)).toReal|
      ≤ (q.natAbs : ℝ) * η := by
  induction' q using Int.induction_on with q IH q IH;
  · simp +decide;
  · -- Apply the triangle inequality to each term in the sum.
    have h_triangle : ∀ i, |(μ ((L ^ (q + 1 : ℤ)) '' (b i))).toReal - (μ (b i)).toReal| ≤ |(μ ((L ^ (q + 1 : ℤ)) '' (b i))).toReal - (μ ((L ^ (q : ℤ)) '' (b i))).toReal| + |(μ ((L ^ (q : ℤ)) '' (b i))).toReal - (μ (b i)).toReal| := by
      exact fun i => abs_sub_le _ _ _;
    refine' le_trans ( Finset.sum_le_sum fun i _ => h_triangle i ) _;
    refine' le_trans ( Finset.sum_le_sum fun i _ => _ ) _;
    use fun i => |(μ (L '' ((L ^ q) '' (b i)))).toReal - (μ ((L ^ q) '' (b i))).toReal| + |(μ ((L ^ q) '' (b i))).toReal - (μ (b i)).toReal|;
    · norm_cast ; simp +decide [ pow_succ', Set.image_image ];
    · rw [ Finset.sum_add_distrib ];
      refine' le_trans ( add_le_add ( approxInv_one_step hμ _ _ ) ( IH _ ) ) _;
      · intro i j hij; specialize hdisj hij; simp_all +decide [ Set.disjoint_left ] ;
      · intro i;
        exact Defined.mono ( show k + q ≤ M from by norm_cast at *; linarith ) ( defined_shift ( hdef i ) q );
      · omega;
      · norm_cast ; simp +decide [ add_mul ];
        linarith;
  · -- Apply the triangle inequality to each term in the sum.
    have h_triangle : ∀ i, |(μ ((L ^ (-q - 1 : ℤ)) '' (b i))).toReal - (μ (b i)).toReal| ≤ |(μ ((L ^ (-q : ℤ)) '' (b i))).toReal - (μ (b i)).toReal| + |(μ ((L ^ (-q - 1 : ℤ)) '' (b i))).toReal - (μ ((L ^ (-q : ℤ)) '' (b i))).toReal| := by
      grind;
    -- Apply the approximation invariant property to the second sum.
    have h_approx : ∑ i, |(μ ((L ^ (-q - 1 : ℤ)) '' (b i))).toReal - (μ ((L ^ (-q : ℤ)) '' (b i))).toReal| ≤ η := by
      convert approxInv_one_step hμ ( show Pairwise ( Function.onFun Disjoint fun i => ( L ^ ( -q - 1 : ℤ ) ) '' b i ) from ?_ ) ( fun i => ?_ ) using 1;
      · refine' Finset.sum_congr rfl fun i _ => _;
        rw [ abs_sub_comm ];
        rw [ show ( L ^ ( -q : ℤ ) ) = L * ( L ^ ( -q - 1 : ℤ ) ) by group ] ; simp +decide [ Set.image_image ] ;
      · intro i j hij; specialize hdisj hij; simp_all +decide [ Set.disjoint_left ] ;
      · refine' defined_shift ( hdef i ) _ |> fun h => h.mono _;
        linarith;
    refine' le_trans ( Finset.sum_le_sum fun i _ => h_triangle i ) _;
    rw [ Finset.sum_add_distrib ];
    refine' le_trans ( add_le_add ( IH _ ) h_approx ) _;
    · omega;
    · norm_num [ Int.natAbs_eq_iff ];
      rw [ abs_of_nonpos ] <;> linarith

end LamplighterStability.Dynamics