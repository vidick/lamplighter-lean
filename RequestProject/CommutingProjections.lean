import RequestProject.ProjectionTowers
import RequestProject.ChaoBridge
import RequestProject.ChaoN2

set_option maxHeartbeats 2000000

/-!
# Chao et al., Theorem 3.2 — nearby commuting projections (`lem:ab-close`)

This file states and proves the Hilbert–Schmidt version of the
"nearby commuting projections" stability result cited in the pre-processing step
of the proof of the main theorem (Section 5 of the paper).  The main result
`chao_commuting_projections` is now fully proved (in the `O(N²)` displacement
form `5·n²·ε₀`); see `RequestProject.ChaoN2`.

It is deliberately kept in a file that imports **only** sorry-free
matrix/operator-algebra material (`RequestProject.ProjectionTowers`,
`RequestProject.ChaoBridge`, and `RequestProject.ChaoN2`, the last transporting
the sorry-free Gowers–Hatami normalized-HS separation theorem into the matrix
interface), so that the proof cannot accidentally depend on the dynamical black
box `prop_decomp` or any other unfinished interface.
-/

namespace LamplighterStability

open scoped BigOperators
open Matrix

/-
**Spectral rounding / nearest projection.**  For a Hermitian matrix `R`,
there is a projection `Q` (its spectral rounding) which (i) commutes with every
matrix commuting with `R` and (ii) is a *nearest* projection to `R` in the
normalized Hilbert–Schmidt norm: `‖R − Q‖_HS ≤ ‖R − P‖_HS` for every projection
`P`.

Proof sketch.  Diagonalize `R = U D Uᴴ` with `D` real diagonal (Mathlib's
`Matrix.IsHermitian.spectral_theorem`).  Take `Q = U D' Uᴴ` with `D'` the diagonal
matrix rounding each eigenvalue to the nearest of `{0,1}` (`d ↦ if 1/2 ≤ d then 1
else 0`); `Q` is a projection and, being a polynomial in `R` (functional calculus
on a finite spectrum), commutes with everything `R` commutes with.  For optimality
fix a projection `P`; conjugating by the unitary `U` preserves `normHS`, so it
suffices to compare `‖D − P'‖_HS` with `‖D − D'‖_HS` for the projection
`P' = Uᴴ P U`.  Writing `D = diag(dᵢ)`, expand
`‖D − P'‖_HS² = ∑ᵢ (dᵢ − P'ᵢᵢ)² + ∑_{i≠j} |P'ᵢⱼ|²` (the diagonal entries `P'ᵢᵢ`
are real in `[0,1]`).  For a projection, `P'ᴴ P' = P'`, so `∑ⱼ |P'ᵢⱼ|² = P'ᵢᵢ`,
hence `∑_{j≠i} |P'ᵢⱼ|² = P'ᵢᵢ(1 − P'ᵢᵢ)`.  Therefore each coordinate contributes
`f(P'ᵢᵢ)` with `f(p) = (dᵢ − p)² + p(1 − p) = dᵢ² + p(1 − 2dᵢ)`, which is linear in
`p`; over `p ∈ [0,1]` its minimum is `min(dᵢ², (dᵢ−1)²) = (dᵢ − round dᵢ)²`,
attained at `D'`.  Summing over `i` gives `‖D − D'‖_HS ≤ ‖D − P'‖_HS`.
-/
theorem exists_nearest_proj {d : ℕ} (R : Matrix (Fin d) (Fin d) ℂ)
    (hR : R.IsHermitian) :
    ∃ Q : Matrix (Fin d) (Fin d) ℂ, IsProj Q ∧
      (∀ S : Matrix (Fin d) (Fin d) ℂ, Commute S R → Commute S Q) ∧
      (∀ P : Matrix (Fin d) (Fin d) ℂ, IsProj P → normHS (R - Q) ≤ normHS (R - P)) := by
  revert R;
  -- Diagonalize R = U D Uᴴ via `Matrix.IsHermitian.spectral_theorem`, where U is unitary and D = diagonal (fun i => (hR.eigenvalues i : ℂ)) is real diagonal.
  intro R hR
  obtain ⟨U, D, hU, hD⟩ : ∃ U : Matrix (Fin d) (Fin d) ℂ, ∃ D : Fin d → ℝ, U ∈ unitary (Matrix (Fin d) (Fin d) ℂ) ∧ R = U * Matrix.diagonal (fun i => (D i : ℂ)) * star U := by
    have := Matrix.IsHermitian.spectral_theorem hR;
    refine' ⟨ _, _, _, this ⟩;
    convert Subtype.mem ( hR.eigenvectorUnitary : unitary ( Matrix ( Fin d ) ( Fin d ) ℂ ) ) using 1;
  -- Let $Q = U * D' * Uᴴ$ where $D'$ is the diagonal matrix with entries $round(D_i)$.
  obtain ⟨D', hD'⟩ : ∃ D' : Fin d → ℝ, (∀ i, D' i = if 1 / 2 ≤ D i then 1 else 0) ∧ (∀ P' : Matrix (Fin d) (Fin d) ℂ, IsProj P' → normHS (Matrix.diagonal (fun i => (D i : ℂ)) - P') ≥ normHS (Matrix.diagonal (fun i => (D i : ℂ)) - Matrix.diagonal (fun i => (D' i : ℂ)))) := by
    refine' ⟨ _, fun i => rfl, _ ⟩;
    intro P' hP'
    have h_diag : ∀ i, ‖(D i : ℂ) - P' i i‖^2 + ∑ j ∈ Finset.univ.erase i, ‖P' i j‖^2 ≥ ‖(D i : ℂ) - (if 1 / 2 ≤ D i then 1 else 0 : ℂ)‖^2 := by
      intro i
      have h_diag_i : ‖(D i : ℂ) - P' i i‖^2 + ∑ j ∈ Finset.univ.erase i, ‖P' i j‖^2 ≥ ‖(D i : ℂ) - P' i i‖^2 + (P' i i).re * (1 - (P' i i).re) := by
        have h_diag_i : ∑ j, ‖P' i j‖^2 = (P' i i).re := by
          have h_diag_i : ∑ j, ‖P' i j‖^2 = (P' * P'ᴴ) i i := by
            simp +decide [ Matrix.mul_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq ];
          have h_diag_i : P' * P'ᴴ = P' := by
            have := hP'.1; simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ] ;
            exact hP'.2;
          simp_all +decide [ Complex.ext_iff ];
          norm_cast at * ; aesop;
        simp_all +decide [];
        norm_num [ Complex.normSq, Complex.sq_norm ] ; ring_nf ; norm_num;
        have := hP'.1; simp_all +decide [ Matrix.IsHermitian ] ;
        replace this := congr_fun ( congr_fun this i ) i; simp_all +decide [ Complex.ext_iff ] ;
        norm_num [ show ( P' i i |> Complex.im ) = 0 by linarith ];
      split_ifs <;> norm_num [ Complex.normSq, Complex.sq_norm ] at *;
      · have h_diag_i : (P' i i).re ∈ Set.Icc 0 1 := by
          have h_diag_i : (P' i i).re * (1 - (P' i i).re) ≥ 0 := by
            have h_diag_i : ∑ j, ‖P' i j‖^2 = (P' i i).re := by
              have h_diag_i : ∑ j, ‖P' i j‖^2 = (P' * P'ᴴ) i i := by
                simp +decide [ Matrix.mul_apply, Complex.normSq, Complex.sq_norm ];
                exact Finset.sum_congr rfl fun _ _ => by simp +decide [ Complex.ext_iff ] ; ring;
              convert congr_arg Complex.re h_diag_i using 1;
              rw [ show P' * P'ᴴ = P' from _ ];
              have := hP'.1;
              simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
              exact hP'.2;
            simp_all +decide [ Complex.normSq, Complex.sq_norm ];
            nlinarith [ h_diag_i ▸ Finset.single_le_sum ( fun x _ => add_nonneg ( mul_self_nonneg ( P' i x |> Complex.re ) ) ( mul_self_nonneg ( P' i x |> Complex.im ) ) ) ( Finset.mem_univ i ) ];
          constructor <;> nlinarith only [ h_diag_i ];
        nlinarith [ h_diag_i.1, h_diag_i.2 ];
      · have h_diag_i : (P' i i).re ∈ Set.Icc 0 1 := by
          have h_diag_i : (P' i i).re * (1 - (P' i i).re) ≥ 0 := by
            have h_diag_i : ∑ j, ‖P' i j‖^2 = (P' i i).re := by
              have h_diag_i : ∑ j, ‖P' i j‖^2 = (P' * P'ᴴ) i i := by
                simp +decide [ Matrix.mul_apply, Complex.normSq, Complex.sq_norm ];
                exact Finset.sum_congr rfl fun _ _ => by simp +decide [ Complex.ext_iff ] ; ring;
              have h_diag_i : P' * P'ᴴ = P' := by
                have := hP'.1; simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ] ;
                exact hP'.2;
              simp_all +decide [ Complex.ext_iff ];
              norm_cast at * ; aesop;
            simp_all +decide [ Complex.normSq, Complex.sq_norm ];
            nlinarith [ h_diag_i ▸ Finset.single_le_sum ( fun x _ => add_nonneg ( mul_self_nonneg ( P' i x |> Complex.re ) ) ( mul_self_nonneg ( P' i x |> Complex.im ) ) ) ( Finset.mem_univ i ) ];
          constructor <;> nlinarith;
        nlinarith [ h_diag_i.1, h_diag_i.2, mul_le_mul_of_nonneg_left ‹D i < 1 / 2›.le h_diag_i.1 ];
    refine' Real.sqrt_le_sqrt _;
    simp_all +decide [ Matrix.diagonal ];
    refine' mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun i _ => _ ) ( by positivity );
    convert h_diag i using 1;
    · rw [ Finset.sum_eq_single i ] <;> aesop;
    · rw [ Finset.sum_eq_add_sum_diff_singleton ( Finset.mem_univ i ) ];
      rw [ Finset.sum_congr rfl fun j hj => by rw [ if_neg ( by aesop ) ] ] ; norm_num;
  refine' ⟨ U * Matrix.diagonal ( fun i => ( D' i : ℂ ) ) * star U, _, _, _ ⟩;
  · constructor;
    · simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
      ext i j ; simp +decide [ Matrix.mul_apply, Matrix.diagonal ];
    · simp_all +decide [ IsIdempotentElem, Matrix.mul_assoc ];
      simp_all +decide [ ← mul_assoc, mem_unitaryGroup_iff ];
      exact congr_arg₂ _ ( congr_arg₂ _ rfl ( by ext i j; by_cases hi : i = j <;> aesop ) ) rfl;
  · intro S hS
    have h_comm : Commute (star U * S * U) (Matrix.diagonal (fun i => (D i : ℂ))) := by
      simp_all +decide [ mul_assoc, Commute ];
      simp_all +decide [ SemiconjBy, ← mul_assoc ];
      convert congr_arg ( fun x => star U * x * U ) hS using 1 <;> simp +decide [ Matrix.mul_assoc, hU.1 ];
      simp_all +decide [ ← mul_assoc, mem_unitaryGroup_iff ];
    have h_comm_diag : Commute (star U * S * U) (Matrix.diagonal (fun i => (D' i : ℂ))) := by
      ext i j; by_cases hi : i = j <;> simp_all +decide [] ;
      · ring;
      · replace h_comm := congr_fun ( congr_fun h_comm i ) j; simp_all +decide [ Matrix.mul_apply, mul_comm ] ;
        simp_all +decide [ Matrix.diagonal ];
        grind;
    simp_all +decide [ Commute ];
    simp_all +decide [ SemiconjBy, mul_assoc ];
    convert congr_arg ( fun x => U * x * star U ) h_comm_diag using 1 <;> simp +decide [ ← mul_assoc, hU.2 ];
    simp_all +decide [ mul_assoc, Matrix.mem_unitaryGroup_iff ];
  · intro P hP
    have h_conj : normHS (R - P) = normHS (Matrix.diagonal (fun i => (D i : ℂ)) - star U * P * U) := by
      have h_conj : normHS (U * (Matrix.diagonal (fun i => (D i : ℂ)) - star U * P * U) * star U) = normHS (Matrix.diagonal (fun i => (D i : ℂ)) - star U * P * U) := by
        convert normHS_unitary_conj hU _ using 1;
      simp_all +decide [ mul_sub, sub_mul, ← mul_assoc ];
      have := hU.2; simp_all +decide [ Matrix.mul_assoc ] ;
    have h_conj' : normHS (R - U * Matrix.diagonal (fun i => (D' i : ℂ)) * star U) = normHS (Matrix.diagonal (fun i => (D i : ℂ)) - Matrix.diagonal (fun i => (D' i : ℂ))) := by
      have h_conj' : normHS (U * (Matrix.diagonal (fun i => (D i : ℂ)) - Matrix.diagonal (fun i => (D' i : ℂ))) * star U) = normHS (Matrix.diagonal (fun i => (D i : ℂ)) - Matrix.diagonal (fun i => (D' i : ℂ))) := by
        convert normHS_unitary_conj hU _ using 1;
      convert h_conj' using 2 ; simp +decide [ hD ];
      simp +decide [ ← Matrix.mul_sub, ← Matrix.sub_mul ];
    have h_conj'' : IsProj (star U * P * U) := by
      constructor;
      · simp_all +decide [ IsProj ];
        simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
        simp_all +decide [ Matrix.star_eq_conjTranspose ];
      · simp_all +decide [ IsIdempotentElem, Matrix.mul_assoc ];
        simp_all +decide [ ← mul_assoc, hP.2.eq ];
    linarith [ hD'.2 _ h_conj'' ]

/-! ### Pinching and the conditional expectation onto a commuting family

The second core ingredient of the nearby-commuting-projections theorem is a
*conditional expectation*: given a family of pairwise-commuting projections, any
operator can be moved a controlled amount to one that commutes with the whole
family.  We build it by iterated **pinching** `𝒫Q(X) = Q X Q + (1-Q) X (1-Q)`,
which avoids the `2^k` joint-spectral-projection construction. -/

/-- The **pinch** of `X` by `Q`: `Q X Q + (1-Q) X (1-Q)`. -/
noncomputable def pinch {d : ℕ} (Q X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Q * X * Q + (1 - Q) * X * (1 - Q)

/-
Pinching a Hermitian matrix by a projection yields a Hermitian matrix.
-/
lemma pinch_isHermitian {d : ℕ} {Q X : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q)
    (hX : X.IsHermitian) : (pinch Q X).IsHermitian := by
  rcases hQ with ⟨ hQ₁, hQ₂ ⟩;
  unfold pinch;
  simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ]

/-
The pinch of `X` by a projection `Q` commutes with `Q`.
-/
lemma commute_pinch_self {d : ℕ} {Q X : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q) :
    Commute (pinch Q X) Q := by
  unfold pinch;
  ext i j; simp +decide [ mul_sub, sub_mul, mul_assoc ] ;
  simp +decide [ Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul ];
  simp +decide [ Matrix.mul_assoc, hQ.2.eq ];
  simp +decide [ ← Matrix.mul_assoc, hQ.2.eq ]

/-
Pinching is a contraction in the (normalized) Hilbert–Schmidt norm.
-/
lemma normHS_pinch_le {d : ℕ} {Q X : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q) :
    normHS (pinch Q X) ≤ normHS X := by
  convert Real.sqrt_le_sqrt ?_ using 1;
  -- By the properties of the trace and the fact that $Q$ is a projection, we can simplify the expression.
  have h_trace : (Matrix.trace ((Q * X * Q + (1 - Q) * X * (1 - Q))ᴴ * (Q * X * Q + (1 - Q) * X * (1 - Q)))).re = (Matrix.trace (Xᴴ * X)).re - (Matrix.trace ((Q * X * (1 - Q) + (1 - Q) * X * Q)ᴴ * (Q * X * (1 - Q) + (1 - Q) * X * Q))).re := by
    simp +decide [ Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_sub ];
    simp_all +decide [ Matrix.mul_sub, Matrix.sub_mul ];
    rw [ show Qᴴ = Q from hQ.1 ] ; ring;
    simp_all +decide [ Matrix.mul_assoc, Matrix.trace_mul_comm Q ] ; ring;
    simp_all +decide [ ← Matrix.mul_assoc, hQ.2.eq ] ; ring;
  -- Since the trace of a positive semi-definite matrix is non-negative, we have:
  have h_trace_nonneg : 0 ≤ (Matrix.trace ((Q * X * (1 - Q) + (1 - Q) * X * Q)ᴴ * (Q * X * (1 - Q) + (1 - Q) * X * Q))).re := by
    have h_trace_nonneg : ∀ (A : Matrix (Fin d) (Fin d) ℂ), 0 ≤ (Matrix.trace (Aᴴ * A)).re := by
      intro A; simp +decide [ Matrix.trace, Matrix.mul_apply ] ; ring_nf;
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => add_nonneg ( sq_nonneg _ ) ( sq_nonneg _ );
    exact h_trace_nonneg _;
  convert mul_le_mul_of_nonneg_left ( show ( Matrix.trace ( ( Q * X * Q + ( 1 - Q ) * X * ( 1 - Q ) ) ᴴ * ( Q * X * Q + ( 1 - Q ) * X * ( 1 - Q ) ) ) |> Complex.re ) ≤ ( Matrix.trace ( Xᴴ * X ) |> Complex.re ) from by linarith ) ( by positivity : ( 0 : ℝ ) ≤ 1 / ( Fintype.card ( Fin d ) : ℝ ) ) using 1;
  · exact congrArg _ ( sum_normSq_eq_trace _ );
  · grind +suggestions

/-
The HS distance moved by a single pinch is exactly the commutator norm.
-/
lemma normHS_sub_pinch {d : ℕ} {Q X : Matrix (Fin d) (Fin d) ℂ} (hQ : IsProj Q) :
    normHS (X - pinch Q X) = normHS (⁅X, Q⁆) := by
  obtain ⟨hQ_herm, hQ_idemp⟩ := hQ;
  -- Let `Q' = 1 - Q` (a projection orthogonal to `Q`: `Q*Q'=0`, `Q'*Q=0`, `Q+Q'=1`).
  set Q' : Matrix (Fin d) (Fin d) ℂ := 1 - Q;
  -- Using `normHS_sq_eq_ntrace`, both equal `ntrace` of `Aᴴ A` for `A = Q*X*Q' ± Q'*X*Q`.
  have h_norm_sq : normHS (X - pinch Q X) ^ 2 = ntrace ((Q * X * Q' + Q' * X * Q)ᴴ * (Q * X * Q' + Q' * X * Q)) ∧ normHS ⁅X, Q⁆ ^ 2 = ntrace ((-Q * X * Q' + Q' * X * Q)ᴴ * (-Q * X * Q' + Q' * X * Q)) := by
    constructor;
    · rw [ show X - pinch Q X = Q * X * Q' + Q' * X * Q from ?_, normHS_sq_eq_ntrace ];
      unfold pinch;
      grind +suggestions;
    · rw [ normHS_sq_eq_ntrace ];
      simp +zetaDelta at *;
      simp +decide [ hQ_herm.eq, Matrix.mul_sub, Matrix.sub_mul, mul_assoc, LieRing.of_associative_ring_bracket ];
  -- The two summands `Q*X*Q'` and `Q'*X*Q` are HS-orthogonal: `innerHS (Q*X*Q') (Q'*X*Q) = ntrace((Q*X*Q')ᴴ (Q'*X*Q)) = ntrace(Q'*Xᴴ*Q*Q'*X*Q) = 0` since `Q*Q' = 0`; and the cross term with a sign is likewise `0`.
  have h_orthogonal : ntrace ((Q * X * Q')ᴴ * (Q' * X * Q)) = 0 ∧ ntrace ((Q' * X * Q)ᴴ * (Q * X * Q')) = 0 := by
    simp +zetaDelta at *;
    simp_all +decide [ Matrix.IsHermitian, IsIdempotentElem, mul_assoc, sub_mul, mul_sub ];
    simp_all +decide [ ← mul_assoc, ntrace ];
  -- Hence by the Pythagoras identity for HS-orthogonal matrices, `normHS (Q*X*Q' + Q'*X*Q)^2 = normHS(Q*X*Q')^2 + normHS(Q'*X*Q)^2 = normHS(-Q*X*Q' + Q'*X*Q)^2`.
  have h_pythagoras : ntrace ((Q * X * Q' + Q' * X * Q)ᴴ * (Q * X * Q' + Q' * X * Q)) = ntrace ((Q * X * Q')ᴴ * (Q * X * Q')) + ntrace ((Q' * X * Q)ᴴ * (Q' * X * Q)) ∧ ntrace ((-Q * X * Q' + Q' * X * Q)ᴴ * (-Q * X * Q' + Q' * X * Q)) = ntrace ((Q * X * Q')ᴴ * (Q * X * Q')) + ntrace ((Q' * X * Q)ᴴ * (Q' * X * Q)) := by
    simp_all +decide [ add_mul, mul_add, ntrace_add, ntrace_neg ];
  rw [ ← sq_eq_sq₀ ( normHS_nonneg _ ) ( normHS_nonneg _ ), h_norm_sq.1, h_norm_sq.2, h_pythagoras.1, h_pythagoras.2 ]

/-
If `X` commutes with `Q'` and the two projections `Q`, `Q'` commute, then the
pinch of `X` by `Q` still commutes with `Q'`.
-/
lemma commute_pinch_of {d : ℕ} {Q Q' X : Matrix (Fin d) (Fin d) ℂ}
    (hXQ' : Commute X Q') (hQQ' : Commute Q Q') : Commute (pinch Q X) Q' := by
  unfold pinch;
  simp_all +decide [ mul_assoc, Commute ];
  simp_all +decide [ SemiconjBy, mul_sub, sub_mul ];
  simp_all +decide [ mul_assoc, add_mul, mul_add, sub_mul, mul_sub ];
  simp_all +decide [ ← mul_assoc ]

/-
Pinching by `Q` intertwines the commutator with `Q'` when `Q`, `Q'` commute.
-/
lemma pinch_commutator {d : ℕ} {Q Q' X : Matrix (Fin d) (Fin d) ℂ}
    (hQQ' : Commute Q Q') : ⁅pinch Q X, Q'⁆ = pinch Q (⁅X, Q'⁆) := by
  simp +decide only [pinch, Ring.lie_def];
  simp +decide [ mul_sub, sub_mul, ← mul_assoc, hQQ'.eq ];
  simp +decide [ mul_assoc, add_mul, mul_add, sub_mul, mul_sub, hQQ'.eq ] ; abel_nf

/-
**Conditional expectation onto a commuting family.**  Given pairwise-commuting
projections `Q : Fin k → …` and a Hermitian `X`, there is a Hermitian `R`
commuting with every `Q i` and with `normHS (X - R) ≤ ∑ i, normHS ⁅X, Q i⁆`.

Proof by induction on `k` via iterated pinching: pinch `X` successively by
`Q 0, Q 1, …`.  Each pinch by `Q i` makes the result commute with `Q i` and, since
the `Q`'s commute, preserves commutation with the earlier ones
(`commute_pinch_of`).  The HS cost of the `i`-th pinch is `normHS ⁅Rᵢ, Q i⁆`
(`normHS_sub_pinch`), and `⁅Rᵢ, Q i⁆` is the image of `⁅X, Q i⁆` under the earlier
pinches (`pinch_commutator`), which are contractions (`normHS_pinch_le`), so it is
`≤ normHS ⁅X, Q i⁆`.  Telescoping with the triangle inequality gives the bound.
-/
lemma exists_condexp {d k : ℕ} (Q : Fin k → Matrix (Fin d) (Fin d) ℂ)
    (hQ : ∀ i, IsProj (Q i)) (hQcomm : ∀ i j, Commute (Q i) (Q j))
    {X : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian) :
    ∃ R : Matrix (Fin d) (Fin d) ℂ, R.IsHermitian ∧
      (∀ i, Commute R (Q i)) ∧
      (∀ S : Matrix (Fin d) (Fin d) ℂ, (∀ i, Commute S (Q i)) →
        normHS (⁅R, S⁆) ≤ normHS (⁅X, S⁆)) ∧
      normHS (X - R) ≤ ∑ i, normHS (⁅X, Q i⁆) := by
  induction' k with k ih;
  · use X; aesop;
  · obtain ⟨ R₀, hR₀₁, hR₀₂, hR₀₃, hR₀₄ ⟩ := ih ( fun i => Q i.castSucc ) ( fun i => hQ _ ) ( fun i j => hQcomm _ _ );
    refine' ⟨ pinch ( Q ( Fin.last k ) ) R₀, _, _, _, _ ⟩;
    · exact pinch_isHermitian (hQ (Fin.last k)) hR₀₁;
    · intro i;
      refine' Fin.lastCases _ _ i;
      · exact commute_pinch_self ( hQ _ );
      · exact fun i => commute_pinch_of ( hR₀₂ i ) ( hQcomm _ _ );
    · intro S hS;
      rw [ pinch_commutator ];
      · refine' le_trans ( normHS_pinch_le ( hQ _ ) ) ( hR₀₃ _ _ );
        exact fun i => hS _;
      · exact hS _ |> Commute.symm;
    · -- By the triangle inequality, we have:
      have h_triangle : normHS (X - pinch (Q (Fin.last k)) R₀) ≤ normHS (X - R₀) + normHS (R₀ - pinch (Q (Fin.last k)) R₀) := by
        convert normHS_sub_le ( X - R₀ ) ( pinch ( Q ( Fin.last k ) ) R₀ - R₀ ) using 1 ; abel_nf;
        rw [ ← normHS_neg ] ; norm_num;
        exact normHS_sub_comm R₀ (pinch (Q (Fin.last k)) R₀);
      -- By the properties of the pinch operation, we have:
      have h_pinch : normHS (R₀ - pinch (Q (Fin.last k)) R₀) = normHS ⁅R₀, Q (Fin.last k)⁆ := by
        convert normHS_sub_pinch ( hQ ( Fin.last k ) ) using 1;
      rw [ Fin.sum_univ_castSucc ];
      exact le_trans h_triangle ( add_le_add hR₀₄ ( h_pinch.symm ▸ hR₀₃ _ fun i => hQcomm _ _ ) )

/-- **Chao et al., Theorem 3.2 (`lem:ab-close`, normalized Hilbert–Schmidt
version) — `O(N²)` form.**  An almost-commuting family of `n` projections, with
pairwise normalized-HS commutator norm at most `ε₀`, is `5·n²·ε₀`-close to a
genuinely commuting family of projections, *with no smallness threshold on*
`ε₀`.

**Status.** This is now fully proved and `sorry`-free.  It is the matrix form of
the unconditional normalized-Hilbert–Schmidt separation theorem
`hs_separation_N2'` (file `RequestProject.HSLemma2Final`, supplied via the
Gowers–Hatami note), transported across the star-algebra isomorphism
`Matrix.toEuclideanCLM` in `RequestProject.ChaoN2`
(`chao_commuting_projections_N2`).

Compared with the dimension-free linear bound `8·n·ε₀` under the threshold
`ε₀ ≤ 1/(32n)` stated in the paper, this version weakens the displacement bound
to the quadratic `5·n²·ε₀` (and drops the threshold entirely).  The original
linear-in-`n` bound `8·n·ε₀` requires Chao et al.'s specific (non-sequential)
construction — the genuinely external content cited, but not reproved, by the
paper.  For reference, the *dimension-aware* linear version is also available as
`LamplighterStability.chao_commuting_projections_dim`
(`ε₀ ≤ 1/(48 n √d) ⟹ normHS (Q i - P i) ≤ 8 n ε₀`), see
`RequestProject.ChaoBridge`.

The two generic operator-theoretic ingredients of such roundings are also
available in this file, fully proved and axiom-clean: `exists_nearest_proj`
(spectral rounding to a nearest projection commuting with the commutant) and
`exists_condexp` (the conditional expectation onto a commuting family via
iterated pinching). -/
theorem chao_commuting_projections {d n : ℕ} {ε₀ : ℝ}
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i))
    (hcomm : ∀ i j, normHS (⁅P i, P j⁆) ≤ ε₀) :
    ∃ Q : Fin n → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, IsProj (Q i)) ∧ (∀ i j, Commute (Q i) (Q j)) ∧
      (∀ i, normHS (Q i - P i) ≤ 5 * (n : ℝ) ^ 2 * ε₀) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨P, hP, fun i => i.elim0, fun i => i.elim0⟩
  · have hε0 : 0 ≤ ε₀ := le_trans (normHS_nonneg _) (hcomm ⟨0, hn⟩ ⟨0, hn⟩)
    exact chao_commuting_projections_N2 P hP hε0 hcomm

end LamplighterStability