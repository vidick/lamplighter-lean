import Mathlib
import RequestProject.HSLemma2

/-!
# Phase C of the note's Lemma 2: the invariant nearest rank-`d` spectral projection

Given a self-adjoint operator `M` on a finite-dimensional complex inner product space `K` that
commutes with a finite abelian unitary representation `π`, we build the orthogonal projection `F`
onto `d` common eigenvectors of `M` (and `π`) corresponding to the `d` largest eigenvalues of `M`.
This `F` is a rank-`d` projection, commutes with `π`, and is a **nearest** rank-`d` projection to
`M` in Hilbert–Schmidt norm: `‖M − F‖_HS ≤ ‖M − E‖_HS` for any rank-`d` projection `E`.  This is
the Ky-Fan step (`HSLemma2.knapsack_top`) combined with the joint diagonalization
(`JointDiag.exists_orthonormalBasis_joint_eigenvector_unitary`).
-/

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ComplexInnerProductSpace
open Finset HSMaps
open ContinuousLinearMap (adjoint)

namespace HSLemma2

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
variable {G : Type} [CommGroup G] [Fintype G] [DecidableEq G]

/-! ### A diagonal projection in a given orthonormal basis -/

/-- The orthogonal projection onto `span {b k : k ∈ S}` for an orthonormal basis `b`. -/
def diagProj {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ K) (S : Finset (Fin n)) : K →L[ℂ] K :=
  ∑ k ∈ S, (innerSL ℂ (b k)).smulRight (b k)

omit [FiniteDimensional ℂ K] in
lemma diagProj_apply_basis {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ K) (S : Finset (Fin n))
    (j : Fin n) : diagProj b S (b j) = if j ∈ S then b j else 0 := by
  unfold diagProj;
  split_ifs <;> simp_all +decide [ Finset.sum_apply, innerSL_apply_apply ];
  · rw [ Finset.sum_eq_single j ] <;> simp_all +decide [ orthonormal_iff_ite.mp b.orthonormal ];
  · exact Finset.sum_eq_zero fun i hi => by rw [ b.orthonormal.2 ( by aesop ) ] ; simp +decide ;

lemma diagProj_selfadjoint {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ K) (S : Finset (Fin n)) :
    adjoint (diagProj b S) = diagProj b S := by
  refine' ContinuousLinearMap.ext fun x => _;
  refine' ext_inner_right ℂ fun y => _;
  simp +decide [ diagProj, adjoint ];
  simp +decide [ sum_inner, inner_smul_left, inner_smul_right ];
  grind

omit [FiniteDimensional ℂ K] in
lemma diagProj_idem {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ K) (S : Finset (Fin n)) :
    diagProj b S ∘L diagProj b S = diagProj b S := by
  ext x;
  rw [ ← b.sum_repr x ] ; simp +decide [ diagProj_apply_basis ] ;
  rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
  · exact Finset.sum_congr rfl fun i hi => by rw [ if_pos hi, diagProj_apply_basis ] ; simp +decide [ hi ] ;
  · aesop

lemma trace_diagProj {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ K) (S : Finset (Fin n)) :
    LinearMap.trace ℂ K (diagProj b S).toLinearMap = (S.card : ℂ) := by
  simp +decide [ diagProj ]

omit [FiniteDimensional ℂ K] in
/-
`diagProj` commutes with any operator that is diagonal in the basis `b`.
-/
lemma diagProj_commute {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ K) (S : Finset (Fin n))
    (T : K →L[ℂ] K) (hT : ∀ k, ∃ ν : ℂ, T (b k) = ν • b k) :
    T ∘L diagProj b S = diagProj b S ∘L T := by
  ext x;
  obtain ⟨c, hc⟩ : ∃ c : Fin n → ℂ, x = ∑ k, c k • b k := by
    exact ⟨ _, Eq.symm ( b.sum_repr x ) ⟩;
  choose ν hν using hT;
  simp +decide [ hc, hν, diagProj_apply_basis ];
  rw [ ← Finset.sum_subset ( Finset.subset_univ S ) ];
  · exact Finset.sum_congr rfl fun x hx => by rw [ if_pos hx, hν ] ;
  · aesop

omit [FiniteDimensional ℂ K] in
/-
`Tr (T ∘ diagProj b S) = ∑_{k ∈ S} ⟨b k, T (b k)⟩`.
-/
lemma trace_comp_diagProj {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ K) (S : Finset (Fin n)) (T : K →L[ℂ] K) :
    LinearMap.trace ℂ K (T ∘L diagProj b S).toLinearMap = ∑ k ∈ S, inner ℂ (b k) (T (b k)) := by
  convert ( LinearMap.trace_eq_matrix_trace ℂ b.toBasis ( T.comp ( diagProj b S ) ) ) using 1;
  simp +decide [ LinearMap.toMatrix_apply, Matrix.trace ];
  simp +decide [ OrthonormalBasis.repr_apply_apply, innerSL_apply_apply, diagProj ];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; simp +decide [ orthonormal_iff_ite.mp b.orthonormal ]

omit [FiniteDimensional ℂ K] in
/-
`Tr T = ∑_k ⟨b k, T (b k)⟩` over an orthonormal basis.
-/
lemma trace_eq_sum_basis {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ K) (T : K →L[ℂ] K) :
    LinearMap.trace ℂ K T.toLinearMap = ∑ k, inner ℂ (b k) (T (b k)) := by
  convert LinearMap.trace_eq_sum_inner ( T.toLinearMap ) b using 1

/-! ### Joint eigenbasis with real `M`-eigenvalues -/

omit [DecidableEq G] in
/-
A self-adjoint `M` commuting with the abelian unitary representation `π` admits a common
orthonormal eigenbasis, with the `M`-eigenvalues real.
-/
lemma exists_joint_eigenbasis (π : G →* (K →L[ℂ] K)) (hπ : ∀ g, π g ∈ unitary (K →L[ℂ] K))
    (M : K →L[ℂ] K) (hMsa : adjoint M = M) (hMcomm : ∀ y, π y ∘L M = M ∘L π y) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ K)
      (μ : Fin (Module.finrank ℂ K) → ℝ),
      (∀ k, M (b k) = (μ k : ℂ) • b k) ∧
      (∀ k x, ∃ ν : ℂ, π x (b k) = ν • b k) := by
  obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ K, (∀ k, ∃ ζ : ℂ, M (b k) = ζ • b k) ∧ (∀ k x, ∃ ν : ℂ, π x (b k) = ν • b k) := by
    obtain ⟨b, hb⟩ := JointDiag.exists_orthonormalBasis_joint_eigenvector_unitary (fun i => Option.casesOn i M π) (by
    intro i j; cases i <;> cases j <;> simp +decide [ *, Commute ] ;
    · simp +decide [ SemiconjBy ];
    · simp_all +decide [ SemiconjBy, ContinuousLinearMap.ext_iff ];
    · (expose_names; exact Commute.semiconjBy (hMcomm val))) (by
    simp +decide [ Commute ];
    simp +decide [ SemiconjBy, star ];
    rintro ( _ | i ) ( _ | j ) <;> simp +decide [ * ];
    · have h_adj : adjoint (π j) = π j⁻¹ := by
        convert pi_adjoint π hπ j using 1;
      have := hMcomm j⁻¹; simp_all +decide [ ContinuousLinearMap.ext_iff ] ;
    · exact hMcomm i;
    · simp +decide [ pi_adjoint π hπ ];
      rw [ ← map_mul, ← map_mul, mul_comm ]);
    exact ⟨ b, fun k => hb k none, fun k x => hb k ( some x ) ⟩;
  choose ζ hζ using hb.1;
  -- Since $M$ is self-adjoint, we have $\langle b k, M (b k) \rangle = \langle M (b k), b k \rangle$.
  have h_self_adjoint : ∀ k, inner ℂ (b k) (M (b k)) = starRingEnd ℂ (inner ℂ (b k) (M (b k))) := by
    intro k
    have h_self_adjoint : inner ℂ (b k) (M (b k)) = inner ℂ (M (b k)) (b k) := by
      rw [ ← ContinuousLinearMap.adjoint_inner_right, hMsa ];
    rw [ h_self_adjoint, inner_conj_symm ];
    exact h_self_adjoint.symm;
  refine' ⟨ b, fun k => ζ k |> Complex.re, _, _ ⟩ <;> simp_all +decide [ Complex.ext_iff ];
  intro k; rw [ ← Complex.re_add_im ( ζ k ) ] ; simp +decide [ show ( ζ k |> Complex.im ) = 0 by linarith [ h_self_adjoint k ] ] ;

/-
Frobenius expansion `hsq (M - X) = Re Tr(M²) - 2 Re Tr(M X) + d` for a rank-`d` orthogonal
projection `X` and self-adjoint `M`.
-/
lemma hsq_M_sub_sa_idem (M X : K →L[ℂ] K) (hMsa : adjoint M = M)
    (hXsa : adjoint X = X) (hXidem : X ∘L X = X) {d : ℕ}
    (hXtr : LinearMap.trace ℂ K X.toLinearMap = (d : ℂ)) :
    hsq (M - X)
      = (LinearMap.trace ℂ K (M ∘L M).toLinearMap).re
        - 2 * (LinearMap.trace ℂ K (M ∘L X).toLinearMap).re + (d : ℝ) := by
  unfold hsq;
  simp +decide [ hMsa, hXsa, hXidem, hXtr, two_mul, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp ];
  grind +suggestions

/-! ### The nearest invariant rank-`d` projection -/

/-
**Phase C of Lemma 2.**  If `M` is self-adjoint and commutes with the abelian unitary
representation `π`, and `E` is a rank-`d` orthogonal projection (`Tr E = d`, `d ≤ dim K`), then
there is a rank-`d` orthogonal projection `F` commuting with every `π x` and nearest to `M`:
`hsq (M − F) ≤ hsq (M − E)`.
-/
omit [DecidableEq G] in
lemma exists_invariant_proj_near (π : G →* (K →L[ℂ] K)) (hπ : ∀ g, π g ∈ unitary (K →L[ℂ] K))
    (M : K →L[ℂ] K) (hMsa : adjoint M = M) (hMcomm : ∀ y, π y ∘L M = M ∘L π y)
    (E : K →L[ℂ] K) (hEsa : adjoint E = E) (hEidem : E ∘L E = E) {d : ℕ}
    (hEtr : LinearMap.trace ℂ K E.toLinearMap = (d : ℂ)) (hd : d ≤ Module.finrank ℂ K) :
    ∃ F : K →L[ℂ] K, adjoint F = F ∧ F ∘L F = F ∧
      LinearMap.trace ℂ K F.toLinearMap = (d : ℂ) ∧
      (∀ x, π x ∘L F = F ∘L π x) ∧
      hsq (M - F) ≤ hsq (M - E) := by
  -- Obtain `b, μ` from `exists_joint_eigenbasis π hπ M hMsa hMcomm`: an orthonormal basis with `M (b k) = (μ k : ℂ) • b k` and `∀ k x, ∃ ν, π x (b k) = ν • b k`.
  obtain ⟨b, μ, hb, hμ⟩ := exists_joint_eigenbasis π hπ M hMsa hMcomm;
  obtain ⟨ S, hS₁, hS₂ ⟩ := knapsack_top μ d hd;
  refine' ⟨ diagProj b S, _, _, _, _, _ ⟩;
  · exact diagProj_selfadjoint b S;
  · exact diagProj_idem b S;
  · convert trace_diagProj b S;
    exact hS₁.symm;
  · exact fun x => diagProj_commute b S _ fun k => hμ k x;
  · have h_trace_MF : (LinearMap.trace ℂ K (M ∘L diagProj b S).toLinearMap).re = ∑ k ∈ S, μ k := by
      have := trace_comp_diagProj b S M; simp_all +decide [] ;
    have h_trace_ME : (LinearMap.trace ℂ K (M ∘L E).toLinearMap).re = ∑ k, μ k * (inner ℂ (b k) (E (b k))).re := by
      have h_trace_ME : (LinearMap.trace ℂ K (M ∘L E).toLinearMap).re = ∑ k, (inner ℂ (b k) (M (E (b k)))).re := by
        convert congr_arg Complex.re ( trace_eq_sum_basis b ( M ∘L E ) ) using 1;
        simp +decide [];
      have h_trace_ME : ∀ k, ⟪b k, M (E (b k))⟫ = ⟪M (b k), E (b k)⟫ := by
        intro k; rw [ ← ContinuousLinearMap.adjoint_inner_right ] ; simp +decide [ hMsa ] ;
      simp_all +decide [];
    have h_trace_ME_le : (LinearMap.trace ℂ K (M ∘L E).toLinearMap).re ≤ ∑ k ∈ S, μ k := by
      convert hS₂ ( fun k => ( inner ℂ ( b k ) ( E ( b k ) ) |> Complex.re ) ) _ _ _ using 1;
      · intro k
        have h_inner_nonneg : 0 ≤ (inner ℂ (b k) (E (b k))).re := by
          have h_inner_nonneg : ⟪b k, E (b k)⟫ = ⟪E (b k), E (b k)⟫ := by
            rw [ ← ContinuousLinearMap.adjoint_inner_right, hEsa ];
            replace hEidem := congr_arg ( fun f => f ( b k ) ) hEidem; aesop;
          rw [ h_inner_nonneg, inner_self_eq_norm_sq_to_K ] ; norm_num;
          norm_cast ; positivity
        exact h_inner_nonneg;
      · intro k
        have h_inner_le_one : ‖E (b k)‖ ≤ 1 := by
          have := opNorm_le_one_of_sa_idem E hEsa hEidem;
          exact le_trans ( ContinuousLinearMap.le_opNorm E _ ) ( mul_le_of_le_one_left ( norm_nonneg _ ) this |> le_trans <| by simp +decide [ b.orthonormal.1 ] );
        have h_inner_le_one : ‖⟪b k, E (b k)⟫‖ ≤ 1 := by
          exact le_trans ( norm_inner_le_norm _ _ ) ( by simpa [ b.orthonormal.1 k ] using h_inner_le_one );
        exact le_trans ( Complex.re_le_norm _ ) h_inner_le_one;
      · convert congr_arg Complex.re hEtr using 1;
        rw [ trace_eq_sum_basis b ];
        simp +decide [];
    rw [ hsq_M_sub_sa_idem, hsq_M_sub_sa_idem ] <;> try assumption;
    · linarith;
    · exact diagProj_selfadjoint b S;
    · exact diagProj_idem b S;
    · convert trace_diagProj b S using 1 ; aesop

end HSLemma2

end