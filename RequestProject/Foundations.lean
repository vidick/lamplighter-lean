import Mathlib

open scoped BigOperators ComplexOrder
open Matrix

/-!
# Foundations for the lamplighter Hilbert–Schmidt stability proof

This file collects elementary, reusable facts about the **normalized
Hilbert–Schmidt norm**, the **normalized trace**, and the associated real
**Hilbert–Schmidt inner product** of complex matrices, which are used throughout
the proof of the main theorem of the paper *"Polynomial Hilbert–Schmidt
stability of the lamplighter group"*.

The conventions, for `A` a square complex matrix indexed by a finite type `ι`
with `d = |ι|`:

* normalized trace `tr(A) = (1/d)·Re Tr(A)` (`ntrace`);
* real Hilbert–Schmidt inner product `⟨A, B⟩ = (1/d)·Re Tr(Aᴴ B)` (`innerHS`);
* normalized Hilbert–Schmidt norm `‖A‖_HS = √(⟨A, A⟩) = √((1/d) ∑_{i,j} |A_{ij}|²)`
  (`normHS`).

The file is organised as a small but reasonably broad library:

* `ntrace`: additivity, behaviour under `star`/transpose, cyclicity
  (`ntrace_mul_comm`), value on `1`, positivity on positive-semidefinite
  matrices;
* `innerHS`: symmetry, (real-)bilinearity, the identity `⟨A, A⟩ = ‖A‖_HS²`, and
  the Cauchy–Schwarz inequality;
* `normHS`: nonnegativity, the unfolded square, vanishing/definiteness, scaling,
  `star`-invariance, the triangle inequality, the value `1` on unitaries, and
  invariance under multiplication / conjugation by unitaries;
* projections: trace positivity and the headline inequality `proj_diff_bound`
  (Lemma `lem:proj_diff_bound` of the paper).
-/

namespace LamplighterStability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **normalized Hilbert–Schmidt norm** of a square complex matrix indexed
by a finite type `ι`:
`‖A‖_HS = √((1/|ι|) ∑_{i,j} |A_{ij}|²)`. -/
noncomputable def normHS (A : Matrix ι ι ℂ) : ℝ :=
  Real.sqrt ((1 / (Fintype.card ι : ℝ)) * ∑ i, ∑ j, ‖A i j‖ ^ 2)

/-- The **normalized trace** of a square complex matrix: `tr(A) = (1/|ι|) Tr(A)`.
We take the real part; for the matrices we care about (Hermitian ones, and in
particular projections) the trace is real. -/
noncomputable def ntrace (A : Matrix ι ι ℂ) : ℝ :=
  (1 / (Fintype.card ι : ℝ)) * (A.trace).re

/-- The **real Hilbert–Schmidt inner product** of two square complex matrices:
`⟨A, B⟩ = (1/|ι|)·Re Tr(Aᴴ B)`. It is the real inner product whose associated
norm is `normHS`. -/
noncomputable def innerHS (A B : Matrix ι ι ℂ) : ℝ :=
  (1 / (Fintype.card ι : ℝ)) * (Matrix.trace (Aᴴ * B)).re

/-! ## The normalized trace -/

omit [DecidableEq ι] in
@[simp] lemma ntrace_zero : ntrace (0 : Matrix ι ι ℂ) = 0 := by
  -- The trace of the zero matrix is zero, so multiplying by 1/d gives zero.
  simp [ntrace, Matrix.trace]

omit [DecidableEq ι] in
lemma ntrace_add (A B : Matrix ι ι ℂ) : ntrace (A + B) = ntrace A + ntrace B := by
  unfold ntrace; simp +decide [ Matrix.trace_add ] ; ring;

omit [DecidableEq ι] in
lemma ntrace_neg (A : Matrix ι ι ℂ) : ntrace (-A) = - ntrace A := by
  unfold ntrace; simp +decide [ Matrix.trace ] ;

omit [DecidableEq ι] in
lemma ntrace_sub (A B : Matrix ι ι ℂ) : ntrace (A - B) = ntrace A - ntrace B := by
  convert ntrace_add A ( -B ) using 1;
  rw [ ntrace_neg, sub_eq_add_neg ]

omit [DecidableEq ι] in
/-- The normalized trace is invariant under conjugate-transpose (it records only
the real part of the trace, and `Tr(Aᴴ) = conj(Tr A)`). -/
lemma ntrace_conjTranspose (A : Matrix ι ι ℂ) : ntrace (Aᴴ) = ntrace A := by
  unfold ntrace; simp +decide [ Matrix.trace ] ;

omit [DecidableEq ι] in
/-- Cyclicity of the normalized trace. -/
lemma ntrace_mul_comm (A B : Matrix ι ι ℂ) : ntrace (A * B) = ntrace (B * A) := by
  unfold ntrace; simp +decide [ mul_comm ] ;
  exact Or.inl ( by rw [ Matrix.trace_mul_comm ] )

/-- The normalized trace of the identity matrix is `1` (when `ι` is nonempty). -/
lemma ntrace_one [Nonempty ι] : ntrace (1 : Matrix ι ι ℂ) = 1 := by
  simp_all +decide [ ntrace, Matrix.trace ]

omit [DecidableEq ι] in
/-- The normalized trace of a positive-semidefinite matrix is nonnegative. -/
lemma ntrace_nonneg_of_posSemidef {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    0 ≤ ntrace A := by
      convert mul_nonneg ( one_div_nonneg.mpr ( Nat.cast_nonneg ( Fintype.card ι ) ) ) ( Matrix.PosSemidef.trace_nonneg hA ) using 1;
      have h_real : A.trace.im = 0 := by
        convert Complex.conj_eq_iff_im.mp _;
        convert congr_arg Matrix.trace hA.1 using 1;
        simp +decide [ Matrix.trace ];
      simp +decide [ Complex.le_def, h_real, ntrace ]

/-! ## The Hilbert–Schmidt inner product -/

omit [DecidableEq ι] in
/-- The Hilbert–Schmidt inner product is symmetric. -/
lemma innerHS_comm (A B : Matrix ι ι ℂ) : innerHS A B = innerHS B A := by
  unfold innerHS; simp +decide [ Matrix.trace ] ;
  simp +decide [ Matrix.mul_apply, mul_comm ]

omit [DecidableEq ι] in
/-- The sum of squared entry-norms equals the real part of `tr(Aᴴ A)`. -/
lemma sum_normSq_eq_trace (M : Matrix ι ι ℂ) :
    (∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) = (Matrix.trace (Mᴴ * M)).re := by
  simp +decide [Matrix.trace, Matrix.mul_apply, Complex.normSq, Complex.sq_norm]
  exact Finset.sum_comm

omit [DecidableEq ι] in
/-- The diagonal of the inner product is the square of the norm. -/
lemma innerHS_self (A : Matrix ι ι ℂ) : innerHS A A = normHS A ^ 2 := by
  unfold innerHS normHS;
  rw [ Real.sq_sqrt ];
  · -- Apply the lemma that states the sum of the squared norms of the entries of a matrix is equal to the real part of the trace of the matrix multiplied by its conjugate transpose.
    have := sum_normSq_eq_trace A;
    aesop;
  · exact mul_nonneg ( by positivity ) ( Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _ )

omit [DecidableEq ι] in
lemma innerHS_self_nonneg (A : Matrix ι ι ℂ) : 0 ≤ innerHS A A := by
  exact innerHS_self A ▸ sq_nonneg _

omit [DecidableEq ι] in
lemma innerHS_add_left (A B C : Matrix ι ι ℂ) :
    innerHS (A + B) C = innerHS A C + innerHS B C := by
      unfold innerHS;
      simp +decide [ Matrix.add_mul, Matrix.trace_add ];
      ring

omit [DecidableEq ι] in
lemma innerHS_add_right (A B C : Matrix ι ι ℂ) :
    innerHS A (B + C) = innerHS A B + innerHS A C := by
      unfold innerHS;
      simp +decide only [mul_add, trace_add, Complex.add_re]

omit [DecidableEq ι] in
lemma innerHS_neg_left (A B : Matrix ι ι ℂ) : innerHS (-A) B = - innerHS A B := by
  unfold innerHS; simp +decide;

omit [DecidableEq ι] in
lemma innerHS_neg_right (A B : Matrix ι ι ℂ) : innerHS A (-B) = - innerHS A B := by
  unfold innerHS; simp +decide [ mul_neg ] ;

omit [DecidableEq ι] in
/-- **Cauchy–Schwarz** for the Hilbert–Schmidt inner product. -/
lemma innerHS_le (A B : Matrix ι ι ℂ) : innerHS A B ≤ normHS A * normHS B := by
  -- Define the total enumeration of the index pairs.
  set ι' := ι × ι;
  -- Apply the Cauchy-Schwarz inequality to the inner product of `A` and `B`.
  have h_cauchy_schwarz : ( (∑ i, ∑ j, starRingEnd ℂ (A i j) * B i j).re : ℝ ) ≤ Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ 2) * Real.sqrt (∑ i, ∑ j, ‖B i j‖ ^ 2) := by
    -- By the Cauchy-Schwarz inequality for sums, we have:
    have h_cauchy_schwarz : ∀ (f g : ι' → ℂ), (∑ i : ι', (starRingEnd ℂ) (f i) * g i).re ≤ Real.sqrt (∑ i : ι', ‖f i‖ ^ 2) * Real.sqrt (∑ i : ι', ‖g i‖ ^ 2) := by
      intro f g
      have h_cauchy_schwarz : Complex.re (∑ i : ι', (starRingEnd ℂ) (f i) * g i) ≤ ∑ i : ι', ‖f i‖ * ‖g i‖ := by
        exact le_trans ( Complex.re_le_norm _ ) ( le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun i _ => by simp +decide ) );
      refine' le_trans h_cauchy_schwarz _;
      exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖f i‖) fun i => ‖g i‖;
    convert h_cauchy_schwarz ( fun p => A p.1 p.2 ) ( fun p => B p.1 p.2 ) using 1 <;> rw [ ← Finset.sum_product' ];
    · rfl;
    · erw [ Finset.sum_product, Finset.sum_product ];
  unfold innerHS normHS; simp_all +decide [ Matrix.trace, Matrix.mul_apply ] ;
  convert mul_le_mul_of_nonneg_left h_cauchy_schwarz ( inv_nonneg.2 ( Nat.cast_nonneg ( Fintype.card ι ) ) ) using 1 <;> ring ; norm_num [ ← sq ] ; ring;
  · exact Or.inl ( Finset.sum_comm );
  · rw [ inv_pow, Real.sq_sqrt ( Nat.cast_nonneg _ ) ] ; ring

omit [DecidableEq ι] in
/-- **Cauchy–Schwarz** (absolute value form). -/
lemma abs_innerHS_le (A B : Matrix ι ι ℂ) : |innerHS A B| ≤ normHS A * normHS B := by
  refine' abs_le.mpr ⟨ _, _ ⟩;
  · have h_cauchy_schwarz : innerHS (-A) B ≤ normHS (-A) * normHS B := by
      apply innerHS_le;
    simp_all +decide [ innerHS_neg_left, normHS ];
    linarith;
  · convert innerHS_le A B

/-! ## The normalized Hilbert–Schmidt norm -/

omit [DecidableEq ι] in
lemma normHS_nonneg (A : Matrix ι ι ℂ) : 0 ≤ normHS A :=
  Real.sqrt_nonneg _

omit [DecidableEq ι] in
/-- The square of the normalized Hilbert–Schmidt norm, unfolded. -/
lemma normHS_sq (A : Matrix ι ι ℂ) :
    normHS A ^ 2 = (1 / (Fintype.card ι : ℝ)) * ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold normHS
  rw [Real.sq_sqrt]
  positivity

omit [DecidableEq ι] in
/-- The square of the normalized Hilbert–Schmidt norm as a trace. -/
lemma normHS_sq_eq_ntrace (A : Matrix ι ι ℂ) : normHS A ^ 2 = ntrace (Aᴴ * A) := by
  rw [normHS_sq, ntrace];
  rw [ ← sum_normSq_eq_trace ]

omit [DecidableEq ι] in
@[simp] lemma normHS_zero : normHS (0 : Matrix ι ι ℂ) = 0 := by
  -- The norm of the zero matrix is zero because the sum of the squares of its entries is zero.
  simp [normHS]

omit [DecidableEq ι] in
@[simp] lemma normHS_neg (A : Matrix ι ι ℂ) : normHS (-A) = normHS A := by
  -- By definition of normHS, we have:
  simp [normHS]

omit [DecidableEq ι] in
lemma normHS_sub_comm (A B : Matrix ι ι ℂ) : normHS (A - B) = normHS (B - A) := by
  rw [ ← normHS_neg, neg_sub ]

omit [DecidableEq ι] in
/-- Scaling: `‖c • A‖_HS = ‖c‖·‖A‖_HS`. -/
lemma normHS_smul (c : ℂ) (A : Matrix ι ι ℂ) :
    normHS (c • A) = ‖c‖ * normHS A := by
      unfold normHS; simp +decide [ mul_pow ] ;
      simp +decide only [← Finset.mul_sum _ _ _];
      rw [ Real.sqrt_mul ( sq_nonneg _ ), Real.sqrt_sq ( norm_nonneg _ ) ] ; ring

omit [DecidableEq ι] in
/-- `normHS` is invariant under the conjugate-transpose (star). -/
lemma normHS_star (A : Matrix ι ι ℂ) : normHS (star A) = normHS A := by
  unfold normHS; simp +decide;
  exact Or.inl ( by rw [ Finset.sum_comm ] )

omit [DecidableEq ι] in
@[simp] lemma normHS_conjTranspose (A : Matrix ι ι ℂ) : normHS (Aᴴ) = normHS A :=
  normHS_star A

omit [DecidableEq ι] in
/-- Definiteness: over a nonempty index type, `normHS A = 0` iff `A = 0`. -/
lemma normHS_eq_zero_iff [Nonempty ι] {A : Matrix ι ι ℂ} :
    normHS A = 0 ↔ A = 0 := by
      rw [ normHS ];
      rw [ Real.sqrt_eq_zero ( mul_nonneg ( by positivity ) ( Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ), mul_eq_zero, one_div, inv_eq_zero, Finset.sum_eq_zero_iff_of_nonneg ] <;> simp +decide;
      · simp +decide [ Finset.sum_eq_zero_iff_of_nonneg, funext_iff, Matrix ];
      · exact fun i => Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq ι] in
/-- **Triangle inequality** for `normHS`. -/
lemma normHS_add_le (A B : Matrix ι ι ℂ) :
    normHS (A + B) ≤ normHS A + normHS B := by
      unfold normHS;
      -- By the Minkowski inequality for sums, we have:
      have h_minkowski : ∀ (x y : EuclideanSpace ℂ (ι × ι)), ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
        exact fun x y => norm_add_le x y;
      simp_all +decide [ EuclideanSpace.norm_eq ];
      convert mul_le_mul_of_nonneg_left ( h_minkowski ( WithLp.toLp 2 ( fun p : ι × ι => A p.1 p.2 ) ) ( WithLp.toLp 2 ( fun p : ι × ι => B p.1 p.2 ) ) ) ( inv_nonneg.mpr ( Real.sqrt_nonneg ( Fintype.card ι : ℝ ) ) ) using 1 <;> simp +decide [ ← mul_add, ← Finset.sum_product' ]

omit [DecidableEq ι] in
/-- Subtraction version of the triangle inequality. -/
lemma normHS_sub_le (A B : Matrix ι ι ℂ) :
    normHS (A - B) ≤ normHS A + normHS B := by
      convert normHS_add_le A ( -B ) using 2 ; norm_num

omit [DecidableEq ι] in
/-- The reverse triangle inequality. -/
lemma abs_normHS_sub_normHS_le (A B : Matrix ι ι ℂ) :
    |normHS A - normHS B| ≤ normHS (A - B) := by
      refine' abs_sub_le_iff.mpr ⟨ _, _ ⟩;
      · have := normHS_add_le ( A - B ) B; simp_all +decide ;
      · have := normHS_add_le ( B - A ) A; simp_all +decide [ normHS_sub_comm ] ;

/-! ## Unitary invariance -/

/-- The normalized Hilbert–Schmidt norm of the identity is `1`. -/
lemma normHS_one [Nonempty ι] : normHS (1 : Matrix ι ι ℂ) = 1 := by
  refine Real.sqrt_eq_one.mpr ?_;
  simp +decide [ Matrix.one_apply ];
  rw [ inv_mul_eq_div, div_eq_iff ] <;> norm_cast <;> aesop

/-- Left multiplication by a unitary preserves `normHS`. -/
lemma normHS_unitary_left {U : Matrix ι ι ℂ} (hU : U ∈ unitary (Matrix ι ι ℂ))
    (A : Matrix ι ι ℂ) : normHS (U * A) = normHS A := by
      rw [ normHS, normHS ];
      have h_unitary : (Matrix.trace ((U * A)ᴴ * (U * A))).re = (Matrix.trace (Aᴴ * A)).re := by
        have h_unitary : Uᴴ * U = 1 := by
          convert hU.1 using 1;
        simp +decide [ ← mul_assoc ];
        simp +decide [ Matrix.mul_assoc, h_unitary ];
      have := sum_normSq_eq_trace ( U * A ) ; have := sum_normSq_eq_trace A; aesop;

/-- Right multiplication by a unitary preserves `normHS`. -/
lemma normHS_unitary_right {U : Matrix ι ι ℂ} (hU : U ∈ unitary (Matrix ι ι ℂ))
    (A : Matrix ι ι ℂ) : normHS (A * U) = normHS A := by
      have := @LamplighterStability.normHS_unitary_left;
      convert this ( Unitary.star_mem hU ) ( star A ) using 1;
      · convert LamplighterStability.normHS_star _ using 2 ; simp +decide;
      · convert LamplighterStability.normHS_star A |> Eq.symm using 1

/-- Conjugation by a unitary preserves `normHS`. -/
lemma normHS_unitary_conj {U : Matrix ι ι ℂ} (hU : U ∈ unitary (Matrix ι ι ℂ))
    (A : Matrix ι ι ℂ) : normHS (U * A * star U) = normHS A := by
      convert normHS_unitary_left hU ( A * star U ) using 1;
      · rw [ Matrix.mul_assoc ];
      · convert normHS_unitary_right ( Unitary.star_mem hU ) A |> Eq.symm using 1

/-- A unitary matrix has normalized Hilbert–Schmidt norm `1`. -/
lemma normHS_of_unitary [Nonempty ι] {U : Matrix ι ι ℂ}
    (hU : U ∈ unitary (Matrix ι ι ℂ)) : normHS U = 1 := by
      convert normHS_unitary_left hU 1 using 1;
      · rw [ mul_one ];
      · exact Eq.symm ( normHS_one )

/-! ## Projections -/

omit [DecidableEq ι] in
/-- For a projection (Hermitian idempotent), the squared norm equals the trace. -/
lemma normHS_sq_proj {P : Matrix ι ι ℂ} (hPh : P.IsHermitian)
    (hPi : IsIdempotentElem P) : normHS P ^ 2 = ntrace P := by
      convert normHS_sq_eq_ntrace P using 1;
      simp_all +decide [ Matrix.IsHermitian, IsIdempotentElem ]

omit [DecidableEq ι] in
/-- The normalized trace of a projection is nonnegative. -/
lemma ntrace_proj_nonneg {P : Matrix ι ι ℂ} (hPh : P.IsHermitian)
    (hPi : IsIdempotentElem P) : 0 ≤ ntrace P := by
      convert normHS_sq_proj hPh hPi ▸ sq_nonneg ( normHS P ) using 1

/-- **Lemma `lem:proj_diff_bound`.** For any two orthogonal projections `P, Q`
(Hermitian idempotents), the difference of their normalized traces is bounded by
the square of the normalized Hilbert–Schmidt distance between them:
`|tr(P) - tr(Q)| ≤ ‖P - Q‖_HS²`. -/
lemma proj_diff_bound (P Q : Matrix ι ι ℂ)
    (hPh : P.IsHermitian) (hPi : IsIdempotentElem P)
    (hQh : Q.IsHermitian) (hQi : IsIdempotentElem Q) :
    |ntrace P - ntrace Q| ≤ normHS (P - Q) ^ 2 := by
  -- From Step 2, we have $a ≥ 0$ and $b ≥ 0$, where $a = ntrace P - (1/d)*(trace (P*Q)).re$ and $b = ntrace Q - (1/d)*(trace (P*Q)).re$.
  have h_nonneg : (ntrace P - (1 / (Fintype.card ι : ℝ)) * ((Matrix.trace (P * Q)).re)) ≥ 0 ∧ (ntrace Q - (1 / (Fintype.card ι : ℝ)) * ((Matrix.trace (P * Q)).re)) ≥ 0 := by
    have h_nonneg : (Matrix.trace ((1 - Q) * P * ((1 - Q) * P).conjTranspose)).re ≥ 0 ∧ (Matrix.trace ((1 - P) * Q * ((1 - P) * Q).conjTranspose)).re ≥ 0 := by
      have h_nonneg : ∀ (M : Matrix ι ι ℂ), 0 ≤ (Matrix.trace (M * M.conjTranspose)).re := by
        simp +decide [ Matrix.trace, Matrix.mul_apply ];
        exact fun M => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ );
      exact ⟨ h_nonneg _, h_nonneg _ ⟩;
    simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc, Matrix.conjTranspose_mul, Matrix.trace_mul_comm P ];
    simp_all +decide [ Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, IsIdempotentElem ];
    simp_all +decide [ ntrace, Matrix.mul_assoc, Matrix.trace_mul_comm Q ];
    simp_all +decide [ Matrix.mul_assoc, Matrix.trace_mul_comm P ];
    exact ⟨ mul_le_mul_of_nonneg_left h_nonneg.1 ( by positivity ), mul_le_mul_of_nonneg_left h_nonneg.2 ( by positivity ) ⟩;
  -- From Step 1, we have $normHS (P - Q)^2 = ntrace P + ntrace Q - 2*(1/d)*(trace (P*Q)).re$.
  have h_eq : (normHS (P - Q)) ^ 2 = (ntrace P) + (ntrace Q) - 2 * (1 / (Fintype.card ι : ℝ)) * ((Matrix.trace (P * Q)).re) := by
    rw [ normHS_sq, ntrace, ntrace, sum_normSq_eq_trace ];
    simp +decide [ Matrix.trace_mul_comm Q, Matrix.mul_sub, Matrix.sub_mul, hPh.eq, hQh.eq ]
    rw [ hPi.eq, hQi.eq ] ; ring
  exact abs_le.mpr ⟨ by linarith, by linarith ⟩

end LamplighterStability