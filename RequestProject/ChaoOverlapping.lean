import Mathlib

open Matrix
open scoped Matrix.Norms.Frobenius
open scoped BigOperators
open scoped ComplexOrder

set_option maxHeartbeats 4000000

/-!
# Separating nearly-commuting projections in the Hilbert–Schmidt (Frobenius) norm

*Provenance.* This file is an externally supplied, fully self-contained and
`sorry`-free formalization of Theorem 3.2 of "Overlapping qubits" (Chao,
Reichardt, Sutherland, Vidick, arXiv:1701.01062), the result cited as
`lem:ab-close` in the paper. It is imported here unchanged. The bridge from the
statement proved here (`Overlapping.separating_projections`, stated in the
**unnormalized** Frobenius norm) to the **normalized** Hilbert–Schmidt interface
`LamplighterStability.chao_commuting_projections` used by the rest of the project
is developed in `RequestProject.ChaoBridge`.

This file formalizes Theorem 3.2 of "Overlapping qubits" (Chao, Reichardt, Sutherland, Vidick,
arXiv:1701.01062), but with the operator norm replaced throughout by the Hilbert–Schmidt /
Frobenius norm `‖A‖ = sqrt (Tr (Aᴴ A))` (the norm written in the request, here the standard
unnormalized Hilbert–Schmidt norm; `Matrix.Norms.Frobenius`).

The statement (`separating_projections`): if `P₁,…,Pₙ` are orthogonal projections with
`‖[Pᵢ,Pⱼ]‖ ≤ ε` for all `i,j` and `ε ≤ 1/(48 n)`, then there are pairwise-commuting projections
`Q₁,…,Qₙ` with `‖Pᵢ − Qᵢ‖ ≤ 8 n ε`.

The proof is the same constructive block-diagonalization / eigenvalue-rounding induction as in the
paper; we checked that every step transfers verbatim to the Hilbert–Schmidt norm. The only
quantitative change is that the commutator cross-term in the block-diagonalization lemma
(`comm_bd_bound`) carries a constant `3` (a clean upper bound for the sharp `2√2` coming from the
Hilbert–Schmidt Pythagoras identity) instead of the operator-norm constant `2`. This changes the
smallness threshold from the paper's `1/(32 n)` to `1/(48 n)`; the displacement bound `8 n ε` is
identical to the paper's.

(The Hilbert–Schmidt norm is used in its unnormalized form `sqrt (Tr (Aᴴ A))`, exactly as written
in the request. The `1/√d`-normalized variant is a genuinely different statement whose constants
would depend on the dimension `d`, because Hilbert–Schmidt submultiplicativity then picks up a
factor of `√d`.)
-/

namespace Overlapping

variable {d : ℕ}

/-- Commutator of two matrices. -/
noncomputable def comm (A B : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ := A * B - B * A

/-- An orthogonal projection: Hermitian and idempotent. -/
def IsProj (Q : Matrix (Fin d) (Fin d) ℂ) : Prop := Q.IsHermitian ∧ Q * Q = Q

/-- `0 ≼ P ≼ I` in the Loewner order. -/
def InUI (P : Matrix (Fin d) (Fin d) ℂ) : Prop := P.PosSemidef ∧ (1 - P).PosSemidef

/-- Block-diagonalization of `P` with respect to the projection `Q`. -/
noncomputable def bd (Q P : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Q * P * Q + (1 - Q) * P * (1 - Q)

/-- The projection obtained from a Hermitian matrix by rounding its eigenvalues to `0` or `1`. -/
noncomputable def roundProj (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian) :
    Matrix (Fin d) (Fin d) ℂ :=
  (hP.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
    (diagonal (fun i => if (1:ℝ)/2 ≤ hP.eigenvalues i then (1:ℂ) else 0)) *
    ((hP.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ)

/-! ## Basic commutator algebra -/

theorem comm_self_zero (A : Matrix (Fin d) (Fin d) ℂ) : comm A A = 0 := by
  simp [comm]

theorem comm_neg (A B : Matrix (Fin d) (Fin d) ℂ) : comm A B = - comm B A := by
  simp [comm]

theorem comm_eq_zero_symm {A B : Matrix (Fin d) (Fin d) ℂ} (h : comm A B = 0) :
    comm B A = 0 := by
  rw [comm_neg] at h ⊢; (
  unfold comm at *; simp_all +decide [ sub_eq_zero ] ;)

/-! ## Frobenius norm foundations -/

/-
`‖A‖² = Re (Tr (Aᴴ A))`.
-/
theorem frob_sq_trace (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖A‖ ^ 2 = (trace (Aᴴ * A)).re := by
  convert congr_arg ( fun x : ℝ => x ^ 2 ) ( Matrix.frobenius_norm_def A ) using 1;
  norm_num [ Complex.normSq, Complex.sq_norm ];
  norm_num [ ← Real.sqrt_eq_rpow, Matrix.trace, Matrix.mul_apply ];
  rw [ Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ ) ), Finset.sum_comm ]

/-
Left multiplication by a unitary preserves the Frobenius norm.
-/
theorem frob_unitary_left {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖U * A‖ = ‖A‖ := by
  -- By definition of Frobenius norm, we have ‖U*A‖^2 = (trace ((U*A)ᴴ * (U*A))).re.
  have h_norm_sq : (‖U * A‖ ^ 2) = (trace ((U * A)ᴴ * (U * A))).re ∧ (‖A‖ ^ 2) = (trace (Aᴴ * A)).re := by
    exact ⟨ frob_sq_trace _, frob_sq_trace _ ⟩;
  -- Since $U$ is unitary, we have $Uᴴ * U = 1$.
  have h_unitary : Uᴴ * U = 1 := by
    exact hU.1;
  simp_all +decide [ Matrix.mul_assoc, Matrix.conjTranspose_mul ];
  simp_all +decide [ ← Matrix.mul_assoc ];
  rw [ ← sq_eq_sq₀ ( norm_nonneg _ ) ( norm_nonneg _ ), h_norm_sq.1, h_norm_sq.2 ]

/-
Right multiplication by a unitary preserves the Frobenius norm.
-/
theorem frob_unitary_right {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖A * U‖ = ‖A‖ := by
  -- By the properties of the trace, we can rewrite the trace of the product as the trace of the product in the opposite order.
  have h_trace : (trace ((A * U)ᴴ * (A * U))).re = (trace (Aᴴ * A)).re := by
    simp_all +decide [ ← mul_assoc, Matrix.mem_unitaryGroup_iff ];
    rw [ ← Matrix.trace_mul_comm ] ; simp_all +decide [ mul_assoc, star_eq_conjTranspose ] ;
    simp +decide [ ← mul_assoc, hU ];
  rw [ ← sq_eq_sq₀ ( norm_nonneg _ ) ( norm_nonneg _ ), frob_sq_trace, frob_sq_trace, h_trace ]

/-
Conjugation by a unitary preserves the Frobenius norm.
-/
theorem frob_conj_unitary {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖U * A * Uᴴ‖ = ‖A‖ := by
  have h1 : Uᴴ ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    simp_all +decide [ Matrix.mem_unitaryGroup_iff ];
    simp_all +decide [ mul_eq_one_comm, star ]
  rw [frob_unitary_right h1, frob_unitary_left hU]

/-
Squared Frobenius norm of a diagonal matrix.
-/
theorem frob_diagonal_sq (v : Fin d → ℂ) :
    ‖(diagonal v)‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  rw [ frob_sq_trace, Matrix.trace ];
  norm_num [ Matrix.mul_apply, Complex.normSq, Complex.sq_norm ]

/-
Pythagoras for the Frobenius inner product: if `Tr (Xᴴ Y) = 0` then `‖X+Y‖² = ‖X‖²+‖Y‖²`.
-/
theorem frob_sq_add_orth {X Y : Matrix (Fin d) (Fin d) ℂ} (h : trace (Xᴴ * Y) = 0) :
    ‖X + Y‖ ^ 2 = ‖X‖ ^ 2 + ‖Y‖ ^ 2 := by
  rw [ frob_sq_trace, frob_sq_trace, frob_sq_trace ];
  simp +decide [ h, add_mul, mul_add, Matrix.trace_add ];
  convert congr_arg Complex.re ( congr_arg Star.star h ) using 1 ; simp +decide [ Matrix.trace ];
  simp +decide [ Matrix.mul_apply, mul_comm ]

/-! ## Block orthogonality (for Lemma 3.3) -/

/-
For a projection `Q`, the two diagonal blocks of `M` have total squared norm at most `‖M‖²`.
-/
theorem frob_block_pyth_le {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q)
    (M : Matrix (Fin d) (Fin d) ℂ) :
    ‖Q * M * Q‖ ^ 2 + ‖(1 - Q) * M * (1 - Q)‖ ^ 2 ≤ ‖M‖ ^ 2 := by
  have h_orthogonal : trace ((Q * M * Q)ᴴ * ((1 - Q) * M * (1 - Q))) = 0 ∧ trace ((Q * M * Q)ᴴ * (Q * M * (1 - Q))) = 0 ∧ trace ((Q * M * Q)ᴴ * ((1 - Q) * M * Q)) = 0 ∧ trace (((1 - Q) * M * (1 - Q))ᴴ * (Q * M * (1 - Q))) = 0 ∧ trace (((1 - Q) * M * (1 - Q))ᴴ * ((1 - Q) * M * Q)) = 0 ∧ trace ((Q * M * (1 - Q))ᴴ * ((1 - Q) * M * Q)) = 0 := by
    simp_all +decide [ IsProj, Matrix.IsHermitian, Matrix.mul_assoc, Matrix.trace_mul_comm Q ];
    simp_all +decide [ sub_mul, mul_sub ];
    simp_all +decide [ ← mul_assoc, ← Matrix.trace_mul_comm Q ];
  have h_orthogonal : ‖M‖^2 = ‖Q * M * Q + (1 - Q) * M * (1 - Q) + Q * M * (1 - Q) + (1 - Q) * M * Q‖^2 := by
    simp +decide [ mul_sub, sub_mul, mul_assoc ];
    exact congr_arg Norm.norm ( by abel1 );
  rw [ h_orthogonal, frob_sq_add_orth, frob_sq_add_orth, frob_sq_add_orth ];
  · exact le_add_of_le_of_nonneg ( le_add_of_nonneg_right ( sq_nonneg _ ) ) ( sq_nonneg _ );
  · tauto;
  · simp_all +decide [ Matrix.add_mul, Matrix.trace_add ];
  · simp_all +decide [ Matrix.add_mul, Matrix.trace_add ]

/-
Decomposition of a commutator with a projection into the two off-diagonal blocks.
-/
theorem comm_proj_decomp {Q : Matrix (Fin d) (Fin d) ℂ}
    (P : Matrix (Fin d) (Fin d) ℂ) :
    comm Q P = Q * P * (1 - Q) - (1 - Q) * P * Q := by
  unfold comm; simp +decide [ mul_sub, sub_mul ] ;

/-
The squared norm of `[Q,P]` splits into the two off-diagonal blocks.
-/
theorem frob_comm_proj_sq {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q)
    (P : Matrix (Fin d) (Fin d) ℂ) :
    ‖comm Q P‖ ^ 2 = ‖Q * P * (1 - Q)‖ ^ 2 + ‖(1 - Q) * P * Q‖ ^ 2 := by
  -- Apply the orthogonality result to the two off-diagonal blocks.
  have h_block_orth : trace ((Q * P * (1 - Q))ᴴ * ((1 - Q) * P * Q)) = 0 := by
    have h_trace : (Q * P * (1 - Q))ᴴ * ((1 - Q) * P * Q) = (1 - Q) * Pᴴ * Q * (1 - Q) * P * Q := by
      simp +decide [ Matrix.mul_assoc, Matrix.conjTranspose_mul, hQ.1.eq ];
    have := hQ.2; simp_all +decide [ mul_assoc, sub_mul, mul_sub ] ;
  convert frob_sq_add_orth ( show trace ( ( Q * P * ( 1 - Q ) ) ᴴ * ( - ( ( 1 - Q ) * P * Q ) ) ) = 0 from ?_ ) using 1;
  · rw [ comm_proj_decomp ];
    rw [ sub_eq_add_neg ];
  · norm_num [ Matrix.norm_def ];
  · simp_all +decide [ Matrix.mul_assoc ]

/-! ## Lemma 3.3 : block-diagonalization -/

theorem bd_isHermitian {Q P : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q) (hP : P.IsHermitian) :
    (bd Q P).IsHermitian := by
  unfold bd; simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ] ;
  rw [ hQ.1.eq ]

/-
`bd Q P` commutes with `Q`.
-/
theorem bd_commutes (Q P : Matrix (Fin d) (Fin d) ℂ) (hQ : IsProj Q) :
    comm Q (bd Q P) = 0 := by
  unfold bd;
  simp +decide [ comm, mul_add, add_mul, mul_assoc, sub_mul, mul_sub ];
  simp_all +decide [ ← mul_assoc, IsProj ]

/-
Block-diagonalization moves `P` by exactly `‖[Q,P]‖`.
-/
theorem bd_dist {Q P : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q) (hP : P.IsHermitian) :
    ‖bd Q P - P‖ = ‖comm Q P‖ := by
  -- By definition of $bd$, we have $bd Q P - P = -(Q * P * (1 - Q)) + -((1 - Q) * P * Q)$.
  have h_decomp : bd Q P - P = -(Q * P * (1 - Q)) + -((1 - Q) * P * Q) := by
    unfold bd; simp +decide [ mul_sub, sub_mul ] ; abel_nf;
  -- Apply the Pythagorean theorem for the Frobenius norm.
  have h_pyth : ‖-(Q * P * (1 - Q)) + -((1 - Q) * P * Q)‖ ^ 2 = ‖-(Q * P * (1 - Q))‖ ^ 2 + ‖-((1 - Q) * P * Q)‖ ^ 2 := by
    apply frob_sq_add_orth;
    simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
    simp_all +decide [ IsProj, Matrix.IsHermitian ];
    simp_all +decide [ mul_sub, sub_mul, ← mul_assoc ];
  have := frob_comm_proj_sq hQ P; simp_all +decide [ sq ] ;
  rw [ ← sq_eq_sq₀ ( norm_nonneg _ ) ( norm_nonneg _ ), sq, sq, h_pyth, this ]

/-
Block-diagonalization preserves `0 ≼ · ≼ I`.
-/
theorem bd_InUI {Q P : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q) (hP : InUI P) :
    InUI (bd Q P) := by
  constructor;
  · have h_pos_semidef : (Q * P * Q).PosSemidef ∧ ((1 - Q) * P * (1 - Q)).PosSemidef := by
      have h_pos_semidef : ∀ (B : Matrix (Fin d) (Fin d) ℂ), P.PosSemidef → (B * P * B.conjTranspose).PosSemidef := by
        exact fun B hPSD => Matrix.PosSemidef.mul_mul_conjTranspose_same hPSD B
      exact ⟨ by simpa [ hQ.1.eq ] using h_pos_semidef Q hP.1, by simpa [ hQ.1.eq ] using h_pos_semidef ( 1 - Q ) hP.1 ⟩;
    exact h_pos_semidef.1.add h_pos_semidef.2;
  · unfold bd;
    convert Matrix.PosSemidef.add ( Matrix.PosSemidef.conjTranspose_mul_mul_same ( show Matrix.PosSemidef ( 1 - P ) from hP.2 ) Q ) ( Matrix.PosSemidef.conjTranspose_mul_mul_same ( show Matrix.PosSemidef ( 1 - P ) from hP.2 ) ( 1 - Q ) ) using 1 ; norm_num [ mul_assoc, hQ.2 ] ; abel_nf;
    simp_all +decide [ IsProj, Matrix.IsHermitian ] ; ext i j ; norm_num ; ring;
    simp +decide [ mul_sub, sub_mul, hQ.2 ] ; ring

/-
An off-diagonal block has norm at most the commutator.
-/
theorem frob_offblock_le_left {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q)
    (P : Matrix (Fin d) (Fin d) ℂ) : ‖Q * P * (1 - Q)‖ ≤ ‖comm Q P‖ := by
  have h := frob_comm_proj_sq hQ P;
  nlinarith [ norm_nonneg ( comm Q P ), norm_nonneg ( Q * P * ( 1 - Q ) ), norm_nonneg ( ( 1 - Q ) * P * Q ) ]

/-
An off-diagonal block has norm at most the commutator.
-/
theorem frob_offblock_le_right {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q)
    (P : Matrix (Fin d) (Fin d) ℂ) : ‖(1 - Q) * P * Q‖ ≤ ‖comm Q P‖ := by
  have h_norm_sq : ‖comm Q P‖^2 = ‖Q * P * (1 - Q)‖^2 + ‖(1 - Q) * P * Q‖^2 := by
    convert frob_comm_proj_sq hQ P using 1;
  nlinarith [ norm_nonneg ( comm Q P ), norm_nonneg ( Q * P * ( 1 - Q ) ), norm_nonneg ( ( 1 - Q ) * P * Q ) ]

/-
The commutator of `bd` splits into the two corner commutators.
-/
theorem comm_bd_split {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q)
    (P₁ P₂ : Matrix (Fin d) (Fin d) ℂ) :
    comm (bd Q P₁) (bd Q P₂) =
      comm (Q * P₁ * Q) (Q * P₂ * Q) +
        comm ((1 - Q) * P₁ * (1 - Q)) ((1 - Q) * P₂ * (1 - Q)) := by
  unfold comm bd;
  simp_all +decide [ mul_assoc, add_mul, mul_add, sub_mul, mul_sub ];
  simp_all +decide [ ← mul_assoc, hQ.2 ];
  abel1

/-
The two corner commutators are Frobenius-orthogonal.
-/
theorem comm_bd_split_orth {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q)
    (P₁ P₂ : Matrix (Fin d) (Fin d) ℂ) :
    trace ((comm (Q * P₁ * Q) (Q * P₂ * Q))ᴴ *
      comm ((1 - Q) * P₁ * (1 - Q)) ((1 - Q) * P₂ * (1 - Q))) = 0 := by
  unfold comm;
  simp_all +decide [ Matrix.mul_assoc, Matrix.conjTranspose_mul, IsProj ];
  simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc, sub_mul, mul_sub ];
  grind

/-
Bound on the `Q`-corner commutator.
-/
theorem comm_corner_bound {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q)
    (P₁ P₂ : Matrix (Fin d) (Fin d) ℂ) :
    ‖comm (Q * P₁ * Q) (Q * P₂ * Q)‖ ≤
      ‖Q * comm P₁ P₂ * Q‖ + 2 * ‖comm Q P₁‖ * ‖comm Q P₂‖ := by
  have h_comm_eq : comm (Q * P₁ * Q) (Q * P₂ * Q) = Q * comm P₁ P₂ * Q - (Q * P₁ * (1 - Q)) * ((1 - Q) * P₂ * Q) + (Q * P₂ * (1 - Q)) * ((1 - Q) * P₁ * Q) := by
    unfold comm; simp +decide [ mul_assoc, sub_mul, mul_sub ] ;
    simp +decide [ ← mul_assoc, hQ.2 ];
  have h_comm_eq : ‖comm (Q * P₁ * Q) (Q * P₂ * Q)‖ ≤ ‖Q * comm P₁ P₂ * Q‖ + ‖Q * P₁ * (1 - Q)‖ * ‖(1 - Q) * P₂ * Q‖ + ‖Q * P₂ * (1 - Q)‖ * ‖(1 - Q) * P₁ * Q‖ := by
    rw [h_comm_eq];
    exact le_trans ( norm_add_le _ _ ) ( add_le_add ( le_trans ( norm_sub_le _ _ ) ( add_le_add ( le_rfl ) ( norm_mul_le _ _ ) ) ) ( norm_mul_le _ _ ) );
  have h_comm_eq : ‖Q * P₁ * (1 - Q)‖ ≤ ‖comm Q P₁‖ ∧ ‖(1 - Q) * P₂ * Q‖ ≤ ‖comm Q P₂‖ ∧ ‖Q * P₂ * (1 - Q)‖ ≤ ‖comm Q P₂‖ ∧ ‖(1 - Q) * P₁ * Q‖ ≤ ‖comm Q P₁‖ := by
    exact ⟨ frob_offblock_le_left hQ P₁, frob_offblock_le_right hQ P₂, frob_offblock_le_left hQ P₂, frob_offblock_le_right hQ P₁ ⟩;
  nlinarith [ norm_nonneg ( Q * P₁ * ( 1 - Q ) ), norm_nonneg ( ( 1 - Q ) * P₂ * Q ), norm_nonneg ( Q * P₂ * ( 1 - Q ) ), norm_nonneg ( ( 1 - Q ) * P₁ * Q ) ]

/-
Bound on the `(1-Q)`-corner commutator.
-/
theorem comm_corner_bound' {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q)
    (P₁ P₂ : Matrix (Fin d) (Fin d) ℂ) :
    ‖comm ((1 - Q) * P₁ * (1 - Q)) ((1 - Q) * P₂ * (1 - Q))‖ ≤
      ‖(1 - Q) * comm P₁ P₂ * (1 - Q)‖ + 2 * ‖comm Q P₁‖ * ‖comm Q P₂‖ := by
  -- By definition of commutator, we can write
  have h_comm : comm ((1 - Q) * P₁ * (1 - Q)) ((1 - Q) * P₂ * (1 - Q)) =
    (1 - Q) * comm P₁ P₂ * (1 - Q) - ((1 - Q) * P₁ * Q) * (Q * P₂ * (1 - Q)) + ((1 - Q) * P₂ * Q) * (Q * P₁ * (1 - Q)) := by
      simp +decide [ comm, mul_sub, sub_mul, mul_assoc ];
      grind +locals;
  rw [ h_comm ];
  -- Apply the triangle inequality to the right-hand side.
  have h_triangle : ‖(1 - Q) * P₁ * Q * (Q * P₂ * (1 - Q))‖ + ‖(1 - Q) * P₂ * Q * (Q * P₁ * (1 - Q))‖ ≤ 2 * ‖comm Q P₁‖ * ‖comm Q P₂‖ := by
    refine' le_trans ( add_le_add ( norm_mul_le _ _ ) ( norm_mul_le _ _ ) ) _;
    refine' le_trans ( add_le_add ( mul_le_mul ( frob_offblock_le_right hQ P₁ ) ( frob_offblock_le_left hQ P₂ ) ( by positivity ) ( by positivity ) ) ( mul_le_mul ( frob_offblock_le_right hQ P₂ ) ( frob_offblock_le_left hQ P₁ ) ( by positivity ) ( by positivity ) ) ) _ ; ring_nf ; norm_num;
  refine' le_trans ( norm_add_le _ _ ) _;
  linarith [ norm_sub_le ( ( 1 - Q ) * comm P₁ P₂ * ( 1 - Q ) ) ( ( 1 - Q ) * P₁ * Q * ( Q * P₂ * ( 1 - Q ) ) ) ]

/-
Lemma 3.3 (Frobenius version): the block-diagonalized commutator bound, with constant `3`.
-/
theorem comm_bd_bound {Q P₁ P₂ : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q) :
    ‖comm (bd Q P₁) (bd Q P₂)‖ ≤ ‖comm P₁ P₂‖ + 3 * ‖comm Q P₁‖ * ‖comm Q P₂‖ := by
  -- Let $C = \text{comm}(\text{bd } Q P₁, \text{bd } Q P₂)$.
  set C := comm (bd Q P₁) (bd Q P₂);
  -- By the properties of the commutator and the block-diagonalization, we have:
  have hC : ‖C‖ ^ 2 = ‖comm (Q * P₁ * Q) (Q * P₂ * Q)‖ ^ 2 + ‖comm ((1 - Q) * P₁ * (1 - Q)) ((1 - Q) * P₂ * (1 - Q))‖ ^ 2 := by
    grind +suggestions;
  -- By the properties of the commutator and the block-diagonalization, we have the following bounds:
  have h_bounds : ‖comm (Q * P₁ * Q) (Q * P₂ * Q)‖ ≤ ‖Q * comm P₁ P₂ * Q‖ + 2 * ‖comm Q P₁‖ * ‖comm Q P₂‖ ∧ ‖comm ((1 - Q) * P₁ * (1 - Q)) ((1 - Q) * P₂ * (1 - Q))‖ ≤ ‖(1 - Q) * comm P₁ P₂ * (1 - Q)‖ + 2 * ‖comm Q P₁‖ * ‖comm Q P₂‖ := by
    exact ⟨ comm_corner_bound hQ P₁ P₂, comm_corner_bound' hQ P₁ P₂ ⟩;
  -- By the properties of the commutator and the block-diagonalization, we have the following inequality:
  have h_ineq : ‖Q * comm P₁ P₂ * Q‖ ^ 2 + ‖(1 - Q) * comm P₁ P₂ * (1 - Q)‖ ^ 2 ≤ ‖comm P₁ P₂‖ ^ 2 := by
    convert frob_block_pyth_le hQ ( comm P₁ P₂ ) using 1;
  have h_final : ‖C‖ ^ 2 ≤ (‖comm P₁ P₂‖ + 3 * ‖comm Q P₁‖ * ‖comm Q P₂‖) ^ 2 := by
    have h_final : (‖Q * comm P₁ P₂ * Q‖ + 2 * ‖comm Q P₁‖ * ‖comm Q P₂‖) ^ 2 + (‖(1 - Q) * comm P₁ P₂ * (1 - Q)‖ + 2 * ‖comm Q P₁‖ * ‖comm Q P₂‖) ^ 2 ≤ (‖comm P₁ P₂‖ + 3 * ‖comm Q P₁‖ * ‖comm Q P₂‖) ^ 2 := by
      have h_ineq : 4 * (‖Q * comm P₁ P₂ * Q‖ + ‖(1 - Q) * comm P₁ P₂ * (1 - Q)‖) ≤ 6 * ‖comm P₁ P₂‖ := by
        nlinarith only [ sq_nonneg ( ‖Q * comm P₁ P₂ * Q‖ - ‖( 1 - Q ) * comm P₁ P₂ * ( 1 - Q )‖ ), h_ineq, norm_nonneg ( comm P₁ P₂ ) ];
      nlinarith only [ show 0 ≤ ‖comm Q P₁‖ * ‖comm Q P₂‖ by positivity, h_ineq, ‹‖Q * comm P₁ P₂ * Q‖ ^ 2 + ‖ ( 1 - Q ) * comm P₁ P₂ * ( 1 - Q )‖ ^ 2 ≤ ‖comm P₁ P₂‖ ^ 2› ];
    exact hC.symm ▸ le_trans ( add_le_add ( pow_le_pow_left₀ ( norm_nonneg _ ) h_bounds.1 2 ) ( pow_le_pow_left₀ ( norm_nonneg _ ) h_bounds.2 2 ) ) h_final;
  exact le_of_pow_le_pow_left₀ ( by positivity ) ( by positivity ) h_final

/-! ## Projections are in `[0,1]` -/

theorem isProj_InUI {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q) : InUI Q := by
  constructor;
  · obtain ⟨hQ_herm, hQ_idemp⟩ := hQ;
    convert Matrix.posSemidef_conjTranspose_mul_self Q using 1;
    rw [ hQ_herm.eq, hQ_idemp ];
  · have h_pos_semidef : (1 - Q) = (1 - Q)ᴴ * (1 - Q) := by
      simp_all +decide [ IsProj, Matrix.IsHermitian ];
      simp +decide [ sub_mul, mul_sub, hQ ]
    generalize_proofs at *; (
    convert Matrix.posSemidef_conjTranspose_mul_self ( 1 - Q ) using 1)

/-! ## Rounding (spectral) facts -/

/-
Spectral decomposition in the convenient `U * diag(λ) * Uᴴ` form.
-/
theorem spectral_form (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian) :
    P = (hP.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
        diagonal (fun i => (hP.eigenvalues i : ℂ)) *
        ((hP.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
  convert hP.spectral_theorem using 1

/-- The eigenvector unitary, as a matrix, lies in the unitary group. -/
theorem eigenvectorUnitary_mem (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian) :
    (hP.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) ∈ Matrix.unitaryGroup (Fin d) ℂ :=
  (hP.eigenvectorUnitary).2

/-
If `M` commutes with `diagonal a` and `c` is constant on the level sets of `a`, then `M`
commutes with `diagonal c`.
-/
theorem commute_diagonal_of_commute {a c : Fin d → ℂ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hac : ∀ i j, a i = a j → c i = c j)
    (h : M * diagonal a = diagonal a * M) :
    M * diagonal c = diagonal c * M := by
  simp_all +decide [ ← Matrix.ext_iff, mul_comm, Matrix.mul_apply ];
  simp_all +decide [ diagonal ];
  grind

/-
The trace of a product of two positive semidefinite matrices is nonnegative.
-/
open scoped MatrixOrder in
theorem trace_mul_psd_nonneg {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  -- Let $S = \sqrt{A}$, then $S$ is positive semidefinite.
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin d) (Fin d) ℂ, S * S = A ∧ S.IsHermitian := by
    refine ⟨CFC.sqrt A, CFC.sqrt_mul_sqrt_self A (ha := Matrix.nonneg_iff_posSemidef.mpr hA), ?_⟩
    exact (CFC.sqrt_nonneg A).posSemidef.1
  have h_trace_nonneg : 0 ≤ (S * B * Sᴴ).trace := by
    convert Matrix.PosSemidef.trace_nonneg ( hB.mul_mul_conjTranspose_same S ) using 1;
  convert h_trace_nonneg using 1 ; simp +decide [ ← hS.1, mul_assoc ];
  rw [ ← Matrix.trace_mul_comm ] ; simp +decide [ ← mul_assoc, hS.2.eq ] ;

theorem roundProj_isProj (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian) :
    IsProj (roundProj P hP) := by
  constructor <;> simp +decide [ roundProj ];
  · simp +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
    congr! 2 ; aesop;
  · simp +decide [ mul_assoc ];
    simp +decide [ Matrix.IsHermitian.eigenvectorUnitary ];
    simp +decide [ ← mul_assoc, ← Matrix.ext_iff ];
    grind

theorem roundProj_comm_self (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian) :
    comm (roundProj P hP) P = 0 := by
  unfold comm roundProj;
  rw [ sub_eq_zero ];
  convert congr_arg ( fun x => ( hP.eigenvectorUnitary : Matrix ( Fin d ) ( Fin d ) ℂ ) * x * ( hP.eigenvectorUnitary : Matrix ( Fin d ) ( Fin d ) ℂ ) ᴴ ) ( show diagonal ( fun i => if 1 / 2 ≤ hP.eigenvalues i then 1 else 0 ) * diagonal ( fun i => hP.eigenvalues i : Fin d → ℂ ) = diagonal ( fun i => hP.eigenvalues i : Fin d → ℂ ) * diagonal ( fun i => if 1 / 2 ≤ hP.eigenvalues i then 1 else 0 ) from ?_ ) using 1;
  · convert congr_arg ( fun x => ( hP.eigenvectorUnitary : Matrix ( Fin d ) ( Fin d ) ℂ ) * diagonal ( fun i => if 1 / 2 ≤ hP.eigenvalues i then 1 else 0 ) * ( hP.eigenvectorUnitary : Matrix ( Fin d ) ( Fin d ) ℂ ) ᴴ * x ) ( spectral_form P hP ) using 1 ; norm_num [ mul_assoc ];
    simp +decide [ ← mul_assoc ];
    simp +decide [ mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ];
  · convert congr_arg ( fun x => x * ( ( hP.eigenvectorUnitary : Matrix ( Fin d ) ( Fin d ) ℂ ) * diagonal ( fun i => if 1 / 2 ≤ hP.eigenvalues i then 1 else 0 ) * ( hP.eigenvectorUnitary : Matrix ( Fin d ) ( Fin d ) ℂ ) ᴴ ) ) ( spectral_form P hP ) using 1 ; simp +decide [ ← mul_assoc ];
    simp +decide [ mul_assoc, mul_eq_one_comm.mp ( show ( hP.eigenvectorUnitary : Matrix ( Fin d ) ( Fin d ) ℂ ) * ( hP.eigenvectorUnitary : Matrix ( Fin d ) ( Fin d ) ℂ ) ᴴ = 1 from by simp [ Matrix.IsHermitian.eigenvectorUnitary ] ) ];
  · ext i j ; by_cases hi : i = j <;> aesop

/-
The rounding is a spectral function of `P`, so it commutes with everything `P` commutes with.
-/
theorem roundProj_commutant {P R : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian)
    (hPR : comm P R = 0) : comm (roundProj P hP) R = 0 := by
  -- Let U = (hP.eigenvectorUnitary : Matrix ..), Λ = diagonal (fun i => (hP.eigenvalues i:ℂ)), D = diagonal b.
  set U := (hP.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  set Λ := diagonal (fun i => (hP.eigenvalues i : ℂ))
  set D := diagonal (fun i => if (1 : ℝ) / 2 ≤ hP.eigenvalues i then (1 : ℂ) else 0);
  have hUU : Uᴴ * U = 1 := by
    simp +zetaDelta at *;
    simp +decide [ Matrix.IsHermitian.eigenvectorUnitary ]
  have hUU' : U * Uᴴ = 1 := by
    rw [ ← mul_eq_one_comm, hUU ];
  have hMΛ : Λ * (Uᴴ * R * U) = (Uᴴ * R * U) * Λ := by
    have hMΛ : P * R = R * P := by
      exact eq_of_sub_eq_zero hPR;
    have hMΛ : P = U * Λ * Uᴴ := by
      convert spectral_form P hP using 1;
    apply_fun ( fun x => Uᴴ * x * U ) at ‹P * R = R * P›; simp_all +decide [ Matrix.mul_assoc ] ;
    simp_all +decide [ ← Matrix.mul_assoc ];
  have hMD : (Uᴴ * R * U) * D = D * (Uᴴ * R * U) := by
    apply commute_diagonal_of_commute;
    rotate_right;
    use fun i => hP.eigenvalues i;
    · aesop;
    · exact hMΛ.symm;
  have h_comm : (U * D * Uᴴ) * R = R * (U * D * Uᴴ) := by
    apply_fun ( fun x => U * x * Uᴴ ) at hMD;
    simp_all +decide [ Matrix.mul_assoc ];
    simp_all +decide [ ← Matrix.mul_assoc ];
  convert sub_eq_zero.mpr h_comm using 1

/-
The squared distance from `P` to its rounding is the sum of squared eigenvalue rounding errors.
-/
theorem roundProj_dist_sq (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian) :
    ‖P - roundProj P hP‖ ^ 2 =
      ∑ i, (min (hP.eigenvalues i) (1 - hP.eigenvalues i)) ^ 2 := by
  -- By definition of roundProj, we have P - roundProj P hP = U * diagonal (fun i => (hP.eigenvalues i:ℂ) - b i) * Uᴴ.
  have h_diff : P - roundProj P hP = (hP.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
    diagonal (fun i => (hP.eigenvalues i:ℂ) - (if (1:ℝ)/2 ≤ hP.eigenvalues i then (1:ℂ) else 0)) *
    ((hP.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
      convert congr_arg₂ ( · - · ) ( spectral_form P hP ) ( show roundProj P hP = ( hP.eigenvectorUnitary : Matrix ( Fin d ) ( Fin d ) ℂ ) * diagonal ( fun i => if 1 / 2 ≤ hP.eigenvalues i then 1 else 0 ) * ( hP.eigenvectorUnitary : Matrix ( Fin d ) ( Fin d ) ℂ ) ᴴ from rfl ) using 1;
      simp +decide [ ← mul_sub, ← sub_mul, mul_assoc ];
  convert congr_arg ( fun x : ℝ => x ^ 2 ) ( frob_conj_unitary ( eigenvectorUnitary_mem P hP ) ( diagonal ( fun i => ( hP.eigenvalues i : ℂ ) - if ( 1 : ℝ ) / 2 ≤ hP.eigenvalues i then ( 1 : ℂ ) else 0 ) ) ) using 1;
  · rw [h_diff];
  · convert ( frob_diagonal_sq ( fun i => ( hP.eigenvalues i : ℂ ) - if ( 1 : ℝ ) / 2 ≤ hP.eigenvalues i then ( 1 : ℂ ) else 0 ) ) |> Eq.symm using 1;
    refine' Finset.sum_congr rfl fun i _ => _ ; split_ifs <;> norm_num [ Complex.normSq, Complex.sq_norm ] ; ring;
    · rw [ min_eq_right ] <;> nlinarith;
    · rw [ min_eq_left ( by linarith ) ]

/-
Each eigenvalue rounding error is at most the distance to the rounding.
-/
theorem roundProj_eigval_le (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian) (i : Fin d) :
    min (hP.eigenvalues i) (1 - hP.eigenvalues i) ≤ ‖P - roundProj P hP‖ := by
  convert roundProj_dist_sq P hP |> Eq.ge |> fun x => Real.le_sqrt_of_sq_le ( x.trans' <| Finset.single_le_sum ( fun j _ => sq_nonneg ( min ( hP.eigenvalues j ) ( 1 - hP.eigenvalues j ) ) ) <| Finset.mem_univ i ) using 1;
  rw [ Real.sqrt_sq ( norm_nonneg _ ) ]

/-
Squared Frobenius distance from a Hermitian matrix to a projection, in trace form.
-/
theorem sqdist_proj {P X : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian) (hX : IsProj X) :
    ‖P - X‖ ^ 2 = (trace (P * P)).re - 2 * (trace (P * X)).re + (trace X).re := by
  convert frob_sq_trace ( P - X ) using 1 ; ring;
  simp +decide [ sub_mul, mul_sub, hP.eq, hX.1.eq ] ; ring;
  rw [ ← Matrix.trace_mul_comm X P ] ; rw [ hX.2 ] ; ring;

/-
The positive part `(2P-1) · rp` of `2P-1` is positive semidefinite.
-/
theorem roundProj_pos_psd (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian) :
    ((P + P - 1) * roundProj P hP).PosSemidef := by
  have h_diag : ∃ D : Matrix (Fin d) (Fin d) ℂ, D.IsHermitian ∧ D.PosSemidef ∧ (P + P - 1) * roundProj P hP = D := by
    -- Let U = (hP.eigenvectorUnitary : Matrix ..). Establish hUU : Uᴴ*U = 1 and hUU' : U*Uᴴ = 1.
    set U : Matrix (Fin d) (Fin d) ℂ := (hP.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
    have hUU : Uᴴ * U = 1 := by
      convert mul_eq_one_comm.mp _;
      · infer_instance;
      · convert hP.eigenvectorUnitary.2.2
    have hUU' : U * Uᴴ = 1 := by
      rw [ ← mul_eq_one_comm, hUU ];
    -- Show the equality heq : (P + P - 1) * roundProj P hP = U * diagonal (fun i => (2*(hP.eigenvalues i : ℂ) - 1) * (if (1:ℝ)/2 ≤ hP.eigenvalues i then (1:ℂ) else 0)) * Uᴴ.
    have heq : (P + P - 1) * roundProj P hP = U * diagonal (fun i => (2 * (hP.eigenvalues i : ℂ) - 1) * (if (1 : ℝ) / 2 ≤ hP.eigenvalues i then (1 : ℂ) else 0)) * Uᴴ := by
      have h_eq : (P + P - 1) = U * diagonal (fun i => (2 * (hP.eigenvalues i : ℂ) - 1)) * Uᴴ := by
        have h_eq : P = U * diagonal (fun i => (hP.eigenvalues i : ℂ)) * Uᴴ := by
          convert spectral_form P hP using 1;
        convert congr_arg ( fun x => x + x - 1 ) h_eq using 1 ; ring;
        ext i j ; norm_num [ Matrix.mul_apply, Matrix.diagonal ] ; ring;
        simp +decide [ Finset.sum_mul _ _ _, Finset.sum_sub_distrib, Matrix.one_apply ];
        convert congr_fun ( congr_fun hUU' i ) j using 1;
      convert congr_arg ( fun x => x * ( U * diagonal ( fun i => if ( 1 : ℝ ) / 2 ≤ hP.eigenvalues i then ( 1 : ℂ ) else 0 ) * Uᴴ ) ) h_eq using 1 ; simp +decide [ mul_assoc ];
      simp +decide [ ← mul_assoc, hUU ];
    refine' ⟨ _, _, _, heq ⟩;
    · simp +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
      congr! 2;
      ext i j ; by_cases hi : i = j <;> simp +decide [ hi ];
      split_ifs <;> norm_num [ Complex.ext_iff ];
    · convert Matrix.PosSemidef.mul_mul_conjTranspose_same _ U using 1;
      constructor <;> norm_num;
      · ext i j; by_cases hi : i = j <;> simp +decide [ hi ] ;
        · split_ifs <;> norm_num [ Complex.ext_iff ];
        · exact if_neg ( Ne.symm hi );
      · intro x; simp +decide [ Finsupp.sum, Matrix.diagonal ] ;
        refine' Finset.sum_nonneg fun i hi => _ ; split_ifs <;> simp_all +decide [ Complex.ext_iff, mul_assoc, mul_comm, mul_left_comm ];
        norm_num [ Complex.mul_conj, Complex.normSq_apply ];
        exact mul_nonneg ( sub_nonneg_of_le ( by norm_cast; linarith ) ) ( by norm_cast; nlinarith );
  aesop

/-
The negated negative part `(2P-1) · (rp-1)` of `2P-1` is positive semidefinite.
-/
theorem roundProj_neg_psd (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.IsHermitian) :
    ((P + P - 1) * (roundProj P hP - 1)).PosSemidef := by
  -- Let U = (hP.eigenvectorUnitary : Matrix ..), Uᴴ*U = 1, U*Uᴴ = 1.
  set U : Matrix (Fin d) (Fin d) ℂ := (hP.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have hU_unitary : Uᴴ * U = 1 ∧ U * Uᴴ = 1 := by
    have := eigenvectorUnitary_mem P hP;
    exact ⟨ this.1, this.2 ⟩;
  -- Show heq : (P + P - 1) * (roundProj P hP - 1) = U * diagonal (fun i => (2*(hP.eigenvalues i : ℂ) - 1) * ((if (1:ℝ)/2 ≤ hP.eigenvalues i then (1:ℂ) else 0) - 1)) * Uᴴ.
  have heq : (P + P - 1) * (roundProj P hP - 1) = U * Matrix.diagonal (fun i => (2*(hP.eigenvalues i : ℂ) - 1) * ((if (1:ℝ)/2 ≤ hP.eigenvalues i then (1:ℂ) else 0) - 1)) * Uᴴ := by
    have heq : (P + P - 1) = U * Matrix.diagonal (fun i => (2*(hP.eigenvalues i : ℂ) - 1)) * Uᴴ := by
      have heq : P = U * Matrix.diagonal (fun i => (hP.eigenvalues i : ℂ)) * Uᴴ := by
        convert spectral_form P hP using 1;
      convert congr_arg ( fun x => x + x - 1 ) heq using 1 ; norm_num [ two_mul, add_mul, mul_add, mul_assoc, hU_unitary ];
      ext i j ; norm_num [ Matrix.mul_apply, Matrix.diagonal ] ; ring;
      simp +decide [ Finset.sum_mul _ _ _, Matrix.one_apply ];
      convert congr_fun ( congr_fun hU_unitary.2 i ) j using 1;
    have heq_round : roundProj P hP = U * Matrix.diagonal (fun i => if (1:ℝ)/2 ≤ hP.eigenvalues i then (1:ℂ) else 0) * Uᴴ := by
      grind +locals;
    simp_all +decide [ mul_assoc, Matrix.mul_sub ];
    simp_all +decide [ ← mul_assoc, mul_sub ];
    simp +decide [ sub_mul, mul_sub, ← Matrix.diagonal_sub ];
  rw [ heq ];
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same;
  constructor;
  · ext i j; by_cases hi : i = j <;> simp +decide [ hi ] ;
    exact if_neg ( Ne.symm hi );
  · intro x; simp +decide [ Finsupp.sum, Matrix.diagonal ] ;
    refine' Finset.sum_nonneg fun i hi => _ ; split_ifs <;> simp_all +decide [ Complex.ext_iff, mul_assoc, mul_comm, mul_left_comm ];
    norm_num [ Complex.mul_conj, Complex.normSq_apply ];
    exact mul_nonneg ( by norm_cast; linarith ) ( by norm_cast; nlinarith )

/-
The real part of the trace of a product of two positive semidefinite matrices is nonnegative.
-/
theorem trace_mul_psd_re_nonneg {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  convert Complex.le_def.mp ( trace_mul_psd_nonneg hA hB ) |>.1 using 1

/-- Spectral rounding is the Frobenius-nearest projection (among all projections). -/
theorem roundProj_optimal {P R : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian)
    (hR : IsProj R) :
    ‖P - roundProj P hP‖ ≤ ‖P - R‖ := by
  set rp := roundProj P hP with hrp
  have hRpsd : R.PosSemidef := (isProj_InUI hR).1
  have h1Rpsd : (1 - R).PosSemidef := (isProj_InUI hR).2
  have ht1 : 0 ≤ (((P + P - 1) * rp) * (1 - R)).trace.re :=
    trace_mul_psd_re_nonneg (roundProj_pos_psd P hP) h1Rpsd
  have ht2 : 0 ≤ (((P + P - 1) * (rp - 1)) * R).trace.re :=
    trace_mul_psd_re_nonneg (roundProj_neg_psd P hP) hRpsd
  have hdiff : ‖P - R‖ ^ 2 - ‖P - rp‖ ^ 2
      = (((P + P - 1) * rp) * (1 - R)).trace.re + (((P + P - 1) * (rp - 1)) * R).trace.re := by
    rw [sqdist_proj hP hR, sqdist_proj hP (roundProj_isProj P hP)]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re]
    ring
  have hsq : ‖P - rp‖ ^ 2 ≤ ‖P - R‖ ^ 2 := by linarith
  exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) hsq

/-
Entrywise expression of the squared Frobenius norm.
-/
theorem frob_sq_entrywise (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  norm_num [ Norm.norm ];
  norm_num [ ← Real.sqrt_eq_rpow, Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ];
  rw [ Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ]

/-
The key per-eigenvalue-pair inequality behind Lemma 3.4.
-/
theorem round_pair_ineq (li lj c : ℝ) (hc : 0 ≤ 1 - 2 * c)
    (hi : min li (1 - li) ≤ c) (hj : min lj (1 - lj) ≤ c) :
    (1 - 2 * c) ^ 2 *
        ((if (1:ℝ)/2 ≤ li then (1:ℝ) else 0) - (if (1:ℝ)/2 ≤ lj then (1:ℝ) else 0)) ^ 2 ≤
      (li - lj) ^ 2 := by
  split_ifs <;> norm_num;
  · positivity;
  · cases min_cases li ( 1 - li ) <;> cases min_cases lj ( 1 - lj ) <;> nlinarith;
  · cases min_cases li ( 1 - li ) <;> cases min_cases lj ( 1 - lj ) <;> nlinarith;
  · positivity

/-
Lemma 3.4 (Frobenius version): the perturbed-commutator bound, stated multiplicatively.
-/
theorem roundProj_comm_bound {P X : Matrix (Fin d) (Fin d) ℂ} (hP : P.IsHermitian)
    (hc : ‖P - roundProj P hP‖ < 1/2) :
    ‖comm (roundProj P hP) X‖ * (1 - 2 * ‖P - roundProj P hP‖) ≤ ‖comm P X‖ := by
  set U := (hP.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set b := fun i => if (1:ℝ)/2 ≤ hP.eigenvalues i then (1:ℂ) else 0 with hb
  set D := diagonal b with hD
  set Λ := diagonal (fun i => (hP.eigenvalues i : ℂ)) with hΛ
  set Y := Uᴴ * X * U with hY;
  -- Step A: ‖comm (roundProj P hP) X‖ = ‖comm D Y‖ and ‖comm P X‖ = ‖comm Λ Y‖.
  have h_comm_eq : ‖comm (roundProj P hP) X‖ = ‖comm D Y‖ ∧ ‖comm P X‖ = ‖comm Λ Y‖ := by
    have h_comm_eq : comm (roundProj P hP) X = U * comm D Y * Uᴴ ∧ comm P X = U * comm Λ Y * Uᴴ := by
      have h_comm_eq : roundProj P hP = U * D * Uᴴ ∧ P = U * Λ * Uᴴ := by
        exact ⟨ rfl, spectral_form P hP ⟩;
      unfold comm; simp +decide [ h_comm_eq, mul_assoc ] ;
      simp +decide [ mul_sub, sub_mul, ← mul_assoc, hY ];
      have h_unitary : U * Uᴴ = 1 ∧ Uᴴ * U = 1 := by
        have := eigenvectorUnitary_mem P hP;
        exact ⟨ this.2, this.1 ⟩;
      simp +decide [ mul_assoc, h_unitary ];
    exact ⟨ by rw [ h_comm_eq.1, frob_conj_unitary ( eigenvectorUnitary_mem P hP ) ], by rw [ h_comm_eq.2, frob_conj_unitary ( eigenvectorUnitary_mem P hP ) ] ⟩;
  -- Step B: it suffices to show ((1-2*c) * ‖comm D Y‖)^2 ≤ ‖comm Λ Y‖^2.
  suffices h_sq : (1 - 2 * ‖P - roundProj P hP‖) ^ 2 * ‖comm D Y‖ ^ 2 ≤ ‖comm Λ Y‖ ^ 2 by
    rw [ h_comm_eq.1, h_comm_eq.2 ];
    nlinarith only [ show 0 ≤ ‖comm Λ Y‖ by positivity, h_sq ];
  -- Apply the entrywise inequality to each term in the sum.
  have h_entrywise : ∀ i j, (1 - 2 * ‖P - roundProj P hP‖) ^ 2 * ‖(comm D Y) i j‖ ^ 2 ≤ ‖(comm Λ Y) i j‖ ^ 2 := by
    intros i j
    have h_entrywise_ineq : (1 - 2 * ‖P - roundProj P hP‖) ^ 2 * ‖(b i - b j) * Y i j‖ ^ 2 ≤ ‖((hP.eigenvalues i : ℂ) - (hP.eigenvalues j : ℂ)) * Y i j‖ ^ 2 := by
      have := round_pair_ineq ( hP.eigenvalues i ) ( hP.eigenvalues j ) ‖P - roundProj P hP‖ ?_ ?_ ?_ <;> norm_num at *;
      · convert mul_le_mul_of_nonneg_right this ( sq_nonneg ( ‖Y i j‖ ) ) using 1 <;> norm_num [ hb ] ; ring;
        · split_ifs <;> norm_num ; ring;
        · norm_cast ; norm_num [ mul_pow ];
      · linarith;
      · have := roundProj_eigval_le P hP i;
        grind;
      · have := roundProj_eigval_le P hP j;
        grind +revert;
    convert h_entrywise_ineq using 2 <;> norm_num [ comm ];
    · simp +zetaDelta at *;
      split_ifs <;> norm_num;
    · simp +decide [ Matrix.mul_apply, hΛ ];
      simp +decide [ Matrix.diagonal ];
      rw [ ← norm_mul ] ; ring;
  convert Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h_entrywise i j using 1 <;> norm_num [ frob_sq_entrywise ] ; ring;
  any_goals exact Finset.univ;
  any_goals exact fun _ => Finset.univ;
  · simp +decide only [Finset.mul_sum _ _ _, Finset.sum_add_distrib, Finset.sum_neg_distrib] ; ring;
    simpa only [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] using by ring;
  · rfl

/-! ## Commutator helpers for the induction -/

theorem comm_add (A B C : Matrix (Fin d) (Fin d) ℂ) :
    comm (A + B) C = comm A C + comm B C := by
  simp only [comm, add_mul, mul_add]; abel

theorem comm_sub (A B C : Matrix (Fin d) (Fin d) ℂ) :
    comm (A - B) C = comm A C - comm B C := by
  simp only [comm, sub_mul, mul_sub]; abel

theorem comm_one_left (A : Matrix (Fin d) (Fin d) ℂ) : comm 1 A = 0 := by
  simp [comm]

/-
If `R` commutes with `A` and with `B`, then it commutes with `A * B`.
-/
theorem comm_mul_eq_zero {A B R : Matrix (Fin d) (Fin d) ℂ}
    (hA : comm A R = 0) (hB : comm B R = 0) : comm (A * B) R = 0 := by
  simp_all +decide [ comm, mul_assoc, sub_eq_iff_eq_add ];
  rw [ ← Matrix.mul_assoc, hA, Matrix.mul_assoc ]

/-! ## The main induction -/

/-
The core inductive lemma. With `e0` a fixed scale, given `m` operators that are Hermitian,
in `[0,1]`, each within `δ` of a projection, and pairwise `ε`-almost-commuting (in the Frobenius
norm), under the smallness conditions `δ + 4 m e0 ≤ 1/4` and `ε + 48 m e0² ≤ 2 e0`, there exist
pairwise-commuting projections `Q i` within `δ + 8 m e0` of the `P i`, with the commutant property
that anything Hermitian commuting with all `P i` also commutes with all `Q i`.
-/
theorem sep_induction (d : ℕ) (e0 : ℝ) (he0 : 0 ≤ e0) :
    ∀ (m : ℕ) (δ ε : ℝ) (P : Fin m → Matrix (Fin d) (Fin d) ℂ),
      0 ≤ δ → 0 ≤ ε →
      δ + 4 * m * e0 ≤ 1/4 →
      ε + 48 * m * e0 ^ 2 ≤ 2 * e0 →
      (∀ i, (P i).IsHermitian) →
      (∀ i, InUI (P i)) →
      (∀ i, ∃ R, IsProj R ∧ ‖P i - R‖ ≤ δ) →
      (∀ i j, ‖comm (P i) (P j)‖ ≤ ε) →
      ∃ Q : Fin m → Matrix (Fin d) (Fin d) ℂ,
        (∀ i, IsProj (Q i)) ∧
        (∀ i j, comm (Q i) (Q j) = 0) ∧
        (∀ i, ‖P i - Q i‖ ≤ δ + 8 * m * e0) ∧
        (∀ R, R.IsHermitian → (∀ i, comm (P i) R = 0) → ∀ i, comm (Q i) R = 0) := by
  intro m;
  induction' m with m ih;
  · aesop;
  · intro δ ε P hδ hε hδb hεb hHerm hUI hWithin hCm;
    -- Set Q0 := roundProj (P 0) (hHerm 0).
    set Q0 := roundProj (P 0) (hHerm 0) with hQ0;
    -- Define P' : Fin m → _ := fun i => bd Q0 (P i.succ).
    set P' : Fin m → Matrix (Fin d) (Fin d) ℂ := fun i => bd Q0 (P i.succ) with hP';
    -- Apply the induction hypothesis to the remaining m matrices.
    obtain ⟨Q', hQ'proj, hQ'comm, hQ'dist, hQ'commutant⟩ := ih (δ + 2 * ε) (ε + 12 * ε ^ 2) P' (by
    positivity) (by
    positivity) (by
    norm_num at * ; nlinarith) (by
    norm_num at *;
    nlinarith [ show ε ≤ 2 * e0 by nlinarith ]) (by
    exact fun i => bd_isHermitian ( roundProj_isProj _ _ ) ( hHerm _ )) (by
    exact fun i => bd_InUI ( roundProj_isProj _ _ ) ( hUI _ )) (by
    intro i
    obtain ⟨R, hRproj, hR⟩ := hWithin i.succ
    use R
    constructor
    exact hRproj
    have hP'R : ‖P' i - R‖ ≤ ‖P' i - P i.succ‖ + ‖P i.succ - R‖ := by
      simpa using norm_add_le ( P' i - P i.succ ) ( P i.succ - R )
    have hP'dist : ‖P' i - P i.succ‖ ≤ 2 * ε := by
      have hP'dist : ‖P' i - P i.succ‖ = ‖comm Q0 (P i.succ)‖ := by
        grind +suggestions;
      have := roundProj_comm_bound (P := P 0) (X := P i.succ) ( hHerm 0 ) ?_;
      · have hP0Q0 : ‖P 0 - Q0‖ ≤ δ := by
          exact roundProj_optimal ( hHerm 0 ) ( hWithin 0 |> Classical.choose_spec |> And.left ) |> le_trans <| hWithin 0 |> Classical.choose_spec |> And.right;
        have hP0Q0 : 1 - 2 * ‖P 0 - Q0‖ ≥ 1 / 2 := by
          norm_num at * ; nlinarith [ show ( m : ℝ ) + 1 ≥ 1 by linarith ];
        nlinarith [ hCm 0 i.succ, norm_nonneg ( comm Q0 ( P i.succ ) ) ];
      · obtain ⟨ R, hRproj, hR ⟩ := hWithin 0;
        exact lt_of_le_of_lt ( roundProj_optimal ( hHerm 0 ) hRproj ) ( by norm_num at *; nlinarith [ show ( m : ℝ ) + 1 ≥ 1 by linarith ] )
    linarith [hP'R, hP'dist]) (by
    intro i j
    have h_comm_bd : ‖comm (P' i) (P' j)‖ ≤ ‖comm (P i.succ) (P j.succ)‖ + 3 * ‖comm Q0 (P i.succ)‖ * ‖comm Q0 (P j.succ)‖ := by
      exact comm_bd_bound (roundProj_isProj _ _);
    have h_comm_Q0 : ∀ i : Fin m, ‖comm Q0 (P i.succ)‖ ≤ 2 * ε := by
      intro i
      have h_comm_Q0_i : ‖comm Q0 (P i.succ)‖ * (1 - 2 * ‖P 0 - Q0‖) ≤ ‖comm (P 0) (P i.succ)‖ := by
        apply roundProj_comm_bound (hHerm 0);
        obtain ⟨ R, hR₁, hR₂ ⟩ := hWithin 0;
        exact lt_of_le_of_lt ( roundProj_optimal ( hHerm 0 ) hR₁ ) ( by linarith [ show ( δ : ℝ ) ≤ 1 / 4 by push_cast at *; nlinarith ] );
      have h_comm_Q0_i : ‖P 0 - Q0‖ ≤ δ := by
        obtain ⟨ R, hR₁, hR₂ ⟩ := hWithin 0;
        exact le_trans ( roundProj_optimal ( hHerm 0 ) hR₁ ) hR₂;
      have h_comm_Q0_i : 1 - 2 * ‖P 0 - Q0‖ ≥ 1 / 2 := by
        norm_num at * ; nlinarith [ show ( m : ℝ ) ≥ 1 by norm_cast; exact Nat.succ_le_of_lt ( Fin.pos i ) ];
      nlinarith [ hCm 0 i.succ, norm_nonneg ( comm Q0 ( P i.succ ) ) ];
    exact h_comm_bd.trans ( by nlinarith [ hCm i.succ j.succ, h_comm_Q0 i, h_comm_Q0 j, norm_nonneg ( comm ( P i.succ ) ( P j.succ ) ), norm_nonneg ( comm Q0 ( P i.succ ) ), norm_nonneg ( comm Q0 ( P j.succ ) ) ] ));
    refine' ⟨ Fin.cons Q0 Q', _, _, _, _ ⟩ <;> simp +decide [ Fin.forall_fin_succ ];
    · exact ⟨ roundProj_isProj _ _, hQ'proj ⟩;
    · refine' ⟨ ⟨ comm_self_zero _, _ ⟩, _ ⟩;
      · intro i;
        convert hQ'commutant Q0 ( roundProj_isProj _ _ |>.1 ) _ i using 1;
        · rw [ comm_neg ];
          rw [ neg_eq_iff_add_eq_zero ];
          convert congr_arg ( fun x => x + x ) ( hQ'commutant Q0 ( roundProj_isProj _ _ |>.1 ) _ i ) using 1;
          · norm_num;
          · grind +suggestions;
        · exact fun i => bd_commutes Q0 ( P i.succ ) ( roundProj_isProj _ _ ) |> fun h => comm_eq_zero_symm h;
      · refine' fun i => ⟨ hQ'commutant Q0 ( roundProj_isProj _ _ |>.1 ) _ i, fun j => hQ'comm i j ⟩;
        exact fun i => bd_commutes Q0 ( P i.succ ) ( roundProj_isProj _ _ ) |> fun h => comm_eq_zero_symm h;
    · refine' ⟨ _, _ ⟩;
      · refine' le_trans _ ( le_add_of_nonneg_right <| by positivity );
        exact roundProj_optimal ( hHerm 0 ) ( hWithin 0 |> Classical.choose_spec |> And.left ) |> le_trans <| hWithin 0 |> Classical.choose_spec |> And.right;
      · intro i
        have hP'dist_i : ‖P' i - P i.succ‖ ≤ 2 * ε := by
          have hP'dist_i : ‖comm Q0 (P i.succ)‖ ≤ 2 * ε := by
            have hP'dist_i : ‖comm Q0 (P i.succ)‖ * (1 - 2 * ‖P 0 - Q0‖) ≤ ‖comm (P 0) (P i.succ)‖ := by
              apply roundProj_comm_bound (hHerm 0);
              obtain ⟨ R, hR₁, hR₂ ⟩ := hWithin 0;
              exact lt_of_le_of_lt ( roundProj_optimal ( hHerm 0 ) hR₁ ) ( by nlinarith [ show ( m : ℝ ) + 1 ≥ 1 by linarith ] );
            have hP'dist_i : ‖P 0 - Q0‖ ≤ δ := by
              obtain ⟨ R, hR₁, hR₂ ⟩ := hWithin 0;
              exact le_trans ( roundProj_optimal ( hHerm 0 ) hR₁ ) hR₂;
            have hP'dist_i : 1 - 2 * ‖P 0 - Q0‖ ≥ 1 / 2 := by
              norm_num at * ; nlinarith [ show ( m : ℝ ) ≥ 0 by positivity ];
            nlinarith [ hCm 0 i.succ, norm_nonneg ( comm Q0 ( P i.succ ) ) ];
          convert hP'dist_i using 1;
          convert bd_dist _ _ using 1;
          · exact roundProj_isProj _ _;
          · exact hHerm _;
        have hP'dist_i : ‖P i.succ - Q' i‖ ≤ ‖P i.succ - P' i‖ + ‖P' i - Q' i‖ := by
          simpa using norm_add_le ( P i.succ - P' i ) ( P' i - Q' i );
        rw [ norm_sub_rev ] at * ; nlinarith [ hQ'dist i, show ( m : ℝ ) ≥ 0 by positivity ];
    · intro R hR hR0 hR';
      refine' ⟨ _, hQ'commutant R hR _ ⟩;
      · exact roundProj_commutant ( hHerm 0 ) hR0;
      · intro i;
        have hP'R : comm (P' i) R = comm (Q0 * P i.succ * Q0) R + comm ((1 - Q0) * P i.succ * (1 - Q0)) R := by
          unfold comm; simp +decide [ mul_assoc, sub_mul, mul_sub ] ;
          unfold P'; simp +decide [ bd, mul_assoc, sub_mul, mul_sub ] ;
          simp +decide [ mul_assoc, add_mul, mul_add, sub_mul, mul_sub ] ; abel_nf;
        grind +suggestions

/-! ## Main theorem -/

/-
**Theorem 3.2 of arXiv:1701.01062, Hilbert–Schmidt (Frobenius) norm version.**

If `P₁,…,Pₙ` are orthogonal projections on `ℂ^d` with `‖[Pᵢ,Pⱼ]‖ ≤ ε` (Frobenius norm) for all
`i,j`, and `ε ≤ 1/(48 n)`, then there exist pairwise-commuting projections `Q₁,…,Qₙ` with
`‖Pᵢ − Qᵢ‖ ≤ 8 n ε`.
-/
theorem separating_projections (d n : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hsmall : ε ≤ 1 / (48 * n))
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ i, IsProj (P i))
    (hcomm : ∀ i j, ‖comm (P i) (P j)‖ ≤ ε) :
    ∃ Q : Fin n → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, IsProj (Q i)) ∧
      (∀ i j, comm (Q i) (Q j) = 0) ∧
      (∀ i, ‖P i - Q i‖ ≤ 8 * n * ε) := by
  by_contra! h_contra;
  -- Apply the sep_induction theorem with the given parameters.
  have := sep_induction d ε hε n 0 ε P (by linarith) (by linarith) (by
  rcases n with ( _ | n ) <;> norm_num at *;
  nlinarith [ mul_inv_cancel₀ ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ]) (by
  rcases n with ( _ | n ) <;> norm_num at *;
  nlinarith [ mul_inv_cancel₀ ( by linarith : ( n : ℝ ) + 1 ≠ 0 ), mul_le_mul_of_nonneg_left hsmall hε ]) (by
  exact fun i => hP i |>.1) (by
  exact fun i => isProj_InUI ( hP i )) (by
  exact fun i => ⟨ P i, hP i, by norm_num ⟩) (by
  assumption);
  obtain ⟨ Q, hQ₁, hQ₂, hQ₃, hQ₄ ⟩ := this; specialize h_contra Q hQ₁ hQ₂; obtain ⟨ i, hi ⟩ := h_contra; linarith [ hQ₃ i ] ;

end Overlapping