import Mathlib

open scoped BigOperators ComplexConjugate InnerProductSpace
open RCLike

namespace SepProj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Sequentially apply `T 0, T 1, …, T (m-1)` to `x`, with `T 0` applied first.
So `seqApply T m x = T (m-1) (T (m-2) (… (T 0 x)))`. -/
def seqApply (T : ℕ → E →L[ℂ] E) : ℕ → E → E
  | 0, x => x
  | (k + 1), x => T k (seqApply T k x)

@[simp] lemma seqApply_zero (T : ℕ → E →L[ℂ] E) (x : E) : seqApply T 0 x = x := rfl

@[simp] lemma seqApply_succ (T : ℕ → E →L[ℂ] E) (k : ℕ) (x : E) :
    seqApply T (k + 1) x = T k (seqApply T k x) := rfl

/-
Telescoping identity for the displacement vector:
`x - seqApply T m x = ∑_{j<m} (seqApply T j x - T j (seqApply T j x))`.
-/
lemma seqApply_sub_eq_sum (T : ℕ → E →L[ℂ] E) (m : ℕ) (x : E) :
    x - seqApply T m x =
      ∑ j ∈ Finset.range m, (seqApply T j x - T j (seqApply T j x)) := by
  induction' m with m ih generalizing x;
  · simp +decide [ seqApply ];
  · rw [ Finset.sum_range_succ, ← ih ];
    rw [ seqApply_succ, sub_add_sub_cancel ]

/-
Telescoping identity for the squared-norm drop (uses self-adjointness and idempotence):
`‖x‖² - ‖seqApply T m x‖² = ∑_{j<m} ‖seqApply T j x - T j (seqApply T j x)‖²`.
-/
lemma normSq_sub_eq_sum (T : ℕ → E →L[ℂ] E) (m : ℕ)
    (hsa : ∀ j < m, ∀ u v : E, ⟪T j u, v⟫_ℂ = ⟪u, T j v⟫_ℂ)
    (hidem : ∀ j < m, ∀ u : E, T j (T j u) = T j u)
    (x : E) :
    ‖x‖ ^ 2 - ‖seqApply T m x‖ ^ 2 =
      ∑ j ∈ Finset.range m, ‖seqApply T j x - T j (seqApply T j x)‖ ^ 2 := by
  induction' m with m ih;
  · simp +decide [ seqApply ];
  · rw [ Finset.sum_range_succ, ← ih ( fun j hj => hsa j ( Nat.lt_succ_of_lt hj ) ) ( fun j hj => hidem j ( Nat.lt_succ_of_lt hj ) ) ];
    simp +decide [ @norm_sub_sq ℂ ];
    have := hsa m m.lt_succ_self ( seqApply T m x ) ( ( T m ) ( seqApply T m x ) ) ; simp_all +decide [ inner_self_eq_norm_sq_to_K ]
    norm_num [ ← this, Complex.ext_iff, sq ] ; ring

/-
**Lemma 3** (sequential projection estimate).  Let `T 0, …, T (m-1)` be self-adjoint
idempotents, `y = seqApply T m x` their ordered product applied to `x`, and
`a = ∑_{j<m} ‖x - T j x‖²`.  Then `‖x - y‖² ≤ a` and `‖x‖² - ‖y‖² ≤ 4a`.
-/
theorem lemma3 (T : ℕ → E →L[ℂ] E) (m : ℕ)
    (hsa : ∀ j < m, ∀ u v : E, ⟪T j u, v⟫_ℂ = ⟪u, T j v⟫_ℂ)
    (hidem : ∀ j < m, ∀ u : E, T j (T j u) = T j u)
    (x : E) :
    ‖x - seqApply T m x‖ ^ 2 ≤ ∑ j ∈ Finset.range m, ‖x - T j x‖ ^ 2 ∧
    ‖x‖ ^ 2 - ‖seqApply T m x‖ ^ 2 ≤ 4 * ∑ j ∈ Finset.range m, ‖x - T j x‖ ^ 2 := by
  -- Let $y = seqApply T m x$ and $a = ∑_{j<m} ‖x - T j x‖²$.
  set y := seqApply T m x
  set a := ∑ j ∈ Finset.range m, ‖x - (T j) x‖^2
  have ha : 0 ≤ a := by
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hy : ‖x - y‖^2 ≤ a := by
    -- By the properties of the inner product and the Cauchy-Schwarz inequality, we have:
    have h_inner_bound : ∀ j < m, Complex.re ⟪x, seqApply T j x - T j (seqApply T j x)⟫_ℂ ≤ ‖x - T j x‖ * ‖seqApply T j x - T j (seqApply T j x)‖ := by
      intro j hj
      have h_inner_bound : Complex.re ⟪x, seqApply T j x - T j (seqApply T j x)⟫_ℂ = Complex.re ⟪x - T j x, seqApply T j x - T j (seqApply T j x)⟫_ℂ := by
        simp +decide [ hsa j hj ];
        rw [ hidem j hj ] ; ring;
      exact h_inner_bound.symm ▸ le_trans ( Complex.re_le_norm _ ) ( norm_inner_le_norm _ _ );
    -- Summing the inequalities from h_inner_bound over all $j < m$, we get:
    have h_sum_bound : Complex.re ⟪x, ∑ j ∈ Finset.range m, (seqApply T j x - T j (seqApply T j x))⟫_ℂ ≤ Real.sqrt a * Real.sqrt (∑ j ∈ Finset.range m, ‖seqApply T j x - T j (seqApply T j x)‖^2) := by
      have h_sum_bound : Complex.re ⟪x, ∑ j ∈ Finset.range m, (seqApply T j x - T j (seqApply T j x))⟫_ℂ ≤ ∑ j ∈ Finset.range m, ‖x - T j x‖ * ‖seqApply T j x - T j (seqApply T j x)‖ := by
        convert Finset.sum_le_sum fun i hi => h_inner_bound i ( Finset.mem_range.mp hi ) using 1 ; simp +decide
      refine' le_trans h_sum_bound _;
      rw [ ← Real.sqrt_mul ha ];
      refine' Real.le_sqrt_of_sq_le _;
      exact
        Finset.sum_mul_sq_le_sq_mul_sq (Finset.range m) (fun i => ‖x - (T i) x‖) fun i =>
          ‖seqApply T i x - (T i) (seqApply T i x)‖
    -- Using the polarization identity, we have:
    have h_polarization : ‖x - y‖^2 = 2 * Complex.re ⟪x, x - y⟫_ℂ - (‖x‖^2 - ‖y‖^2) := by
      simp +decide [ @norm_sub_sq ℂ ]
      norm_cast ; ring
    -- Using the fact that $‖x‖^2 - ‖y‖^2 = ∑_{j<m} ‖seqApply T j x - T j (seqApply T j x)‖^2$, we can substitute this into the polarization identity.
    have h_subst : ‖x‖^2 - ‖y‖^2 = ∑ j ∈ Finset.range m, ‖seqApply T j x - T j (seqApply T j x)‖^2 := by
      convert normSq_sub_eq_sum T m hsa hidem x using 1;
    -- Using the fact that $x - y = \sum_{j<m} (seqApply T j x - T j (seqApply T j x))$, we can substitute this into the polarization identity.
    have h_subst_sum : x - y = ∑ j ∈ Finset.range m, (seqApply T j x - T j (seqApply T j x)) := by
      convert seqApply_sub_eq_sum T m x using 1;
    simp_all +decide [ Complex.ext_iff ];
    nlinarith [ sq_nonneg ( Real.sqrt a - Real.sqrt ( ∑ j ∈ Finset.range m, ‖seqApply T j x - ( T j ) ( seqApply T j x )‖ ^ 2 ) ), Real.mul_self_sqrt ha, Real.mul_self_sqrt ( show 0 ≤ ∑ j ∈ Finset.range m, ‖seqApply T j x - ( T j ) ( seqApply T j x )‖ ^ 2 by exact Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ]
  have hL : ‖x‖^2 - ‖y‖^2 ≤ 4 * a := by
    -- Using the polarization identity, we have ‖x - y‖² = 2 * Re⟪x, x - y⟫ - L.
    have h_polarization : ‖x - y‖^2 = 2 * Complex.re (inner ℂ x (x - y)) - (‖x‖^2 - ‖y‖^2) := by
      simp +decide [ @norm_sub_sq ℂ ]
      norm_cast ; ring
    -- Using the key inner product bound, we have Re⟪x, x - y⟫_ℂ ≤ √a * √L.
    have h_inner_bound : Complex.re (inner ℂ x (x - y)) ≤ Real.sqrt a * Real.sqrt (‖x‖^2 - ‖y‖^2) := by
      -- Using the key inner product bound, we have Re⟪x, d j⟫_ℂ ≤ ‖x - T j x‖ * ‖d j‖.
      have h_inner_bound : ∀ j < m, Complex.re (inner ℂ x (seqApply T j x - T j (seqApply T j x))) ≤ ‖x - (T j) x‖ * ‖seqApply T j x - T j (seqApply T j x)‖ := by
        intro j hj
        have h_inner_bound : Complex.re (inner ℂ x (seqApply T j x - T j (seqApply T j x))) = Complex.re (inner ℂ (x - T j x) (seqApply T j x - T j (seqApply T j x))) := by
          simp +decide [ hsa j hj ];
          rw [ hidem j hj ] ; ring;
        exact h_inner_bound.symm ▸ le_trans ( Complex.re_le_norm _ ) ( norm_inner_le_norm _ _ );
      -- Summing the inequalities from h_inner_bound, we get Re⟪x, x - y⟫_ℂ ≤ ∑_{j<m} ‖x - T j x‖ * ‖d j‖.
      have h_sum_inner_bound : Complex.re (inner ℂ x (x - y)) ≤ ∑ j ∈ Finset.range m, ‖x - (T j) x‖ * ‖seqApply T j x - T j (seqApply T j x)‖ := by
        rw [ seqApply_sub_eq_sum ];
        convert Finset.sum_le_sum fun j hj => h_inner_bound j ( Finset.mem_range.mp hj ) using 1;
        simp +decide
      -- Using the Cauchy-Schwarz inequality, we have ∑_{j<m} ‖x - T j x‖ * ‖d j‖ ≤ √(∑_{j<m} ‖x - T j x‖²) * √(∑_{j<m} ‖d j‖²).
      have h_cauchy_schwarz : ∑ j ∈ Finset.range m, ‖x - (T j) x‖ * ‖seqApply T j x - T j (seqApply T j x)‖ ≤ Real.sqrt (∑ j ∈ Finset.range m, ‖x - (T j) x‖^2) * Real.sqrt (∑ j ∈ Finset.range m, ‖seqApply T j x - T j (seqApply T j x)‖^2) := by
        exact
          Real.sum_mul_le_sqrt_mul_sqrt (Finset.range m) (fun i => ‖x - (T i) x‖) fun i =>
            ‖seqApply T i x - (T i) (seqApply T i x)‖
      convert h_sum_inner_bound.trans h_cauchy_schwarz using 2;
      rw [ ← normSq_sub_eq_sum T m hsa hidem x ];
    by_cases hL : ‖x‖^2 - ‖y‖^2 ≥ 0;
    · nlinarith [ sq_nonneg ( Real.sqrt a - Real.sqrt ( ‖x‖ ^ 2 - ‖y‖ ^ 2 ) ), Real.mul_self_sqrt ha, Real.mul_self_sqrt hL ];
    · linarith [ show 0 ≤ a by positivity ]
  exact ⟨hy, hL⟩

end SepProj