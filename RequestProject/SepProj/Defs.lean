import Mathlib

open scoped BigOperators
open Matrix

namespace SepProj

section Rect
variable {l m : Type*} [Fintype l] [Fintype m]

/-- The (unnormalized) Hilbert–Schmidt inner product of two matrices of the same shape:
`⟪X, Y⟫ = Tr(Xᴴ Y)`. -/
noncomputable def hsIP (X Y : Matrix l m ℂ) : ℂ := (Xᴴ * Y).trace

/-- The `d`-scaled Hilbert–Schmidt squared norm `(1/d) Tr(Xᴴ X)`.  On `d × d` matrices this is the
paper's `‖·‖₂²`; on larger (tensor) spaces and rectangular matrices it is `‖·‖₂,d²`. -/
noncomputable def hsNormSq (d : ℕ) (X : Matrix l m ℂ) : ℝ := (Xᴴ * X).trace.re / d

/-- The `d`-scaled Hilbert–Schmidt norm `((1/d) Tr(Xᴴ X))^{1/2}`. -/
noncomputable def hsNorm (d : ℕ) (X : Matrix l m ℂ) : ℝ := Real.sqrt (hsNormSq d X)

lemma hsNormSq_eq_sum (d : ℕ) (X : Matrix l m ℂ) :
    hsNormSq d X = (∑ i, ∑ j, ‖X i j‖ ^ 2) / d := by
  unfold hsNormSq;
  simp +decide [ Matrix.trace, Matrix.mul_apply, Complex.normSq, Complex.sq_norm ];
  exact congrArg₂ _ ( Finset.sum_comm ) rfl

lemma trace_conjTranspose_mul_self_re_nonneg (X : Matrix l m ℂ) :
    0 ≤ (Xᴴ * X).trace.re := by
  simp +decide [ Matrix.trace, Matrix.mul_apply ];
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ )

lemma hsNormSq_nonneg (d : ℕ) (X : Matrix l m ℂ) : 0 ≤ hsNormSq d X := by
  unfold hsNormSq; rw [ div_nonneg_iff ] ;
  exact Or.inl ⟨ trace_conjTranspose_mul_self_re_nonneg X, Nat.cast_nonneg _ ⟩

lemma hsNorm_nonneg (d : ℕ) (X : Matrix l m ℂ) : 0 ≤ hsNorm d X :=
  Real.sqrt_nonneg _

lemma hsNorm_sq (d : ℕ) (X : Matrix l m ℂ) : (hsNorm d X) ^ 2 = hsNormSq d X := by
  rw [hsNorm, Real.sq_sqrt (hsNormSq_nonneg d X)]

end Rect

section Square
variable {m : Type*} [Fintype m] [DecidableEq m]

/-- A matrix is a projection if it is Hermitian and idempotent. -/
def IsProj (X : Matrix m m ℂ) : Prop := X.IsHermitian ∧ X * X = X

/-- The commutator of two matrices. -/
noncomputable def comm (A B : Matrix m m ℂ) : Matrix m m ℂ := A * B - B * A

omit [DecidableEq m] in
@[simp] lemma comm_def (A B : Matrix m m ℂ) : comm A B = A * B - B * A := rfl

/-- Clean form of the spectral theorem: every Hermitian matrix factors as `U * diagonal lam * Uᴴ`
for a unitary `U` and real eigenvalues `lam`. -/
lemma hermitian_decomp {A : Matrix m m ℂ} (hA : A.IsHermitian) :
    ∃ (U : Matrix m m ℂ) (lam : m → ℝ), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * Matrix.diagonal (fun i => (lam i : ℂ)) * Uᴴ := by
  refine ⟨hA.eigenvectorUnitary, hA.eigenvalues, ?_, ?_, ?_⟩
  · have := (hA.eigenvectorUnitary).2; rw [Matrix.mem_unitaryGroup_iff'] at this; exact this
  · have := (hA.eigenvectorUnitary).2; rw [Matrix.mem_unitaryGroup_iff] at this; exact this
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    convert h using 2

end Square

end SepProj