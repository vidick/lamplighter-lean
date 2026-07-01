import RequestProject.HSLemma2Final
import RequestProject.ProjectionTowers

set_option maxHeartbeats 1600000

/-!
# Bridge: the normalized-HS separation theorem in matrix form (`O(N²)` version)

The externally supplied library (files `RequestProject.HS*`, `RequestProject.GowersHatami`,
`RequestProject.JointDiag`, `RequestProject.GHPolar`) proves, *unconditionally* and `sorry`-free,
the **normalized Hilbert–Schmidt separation theorem** for nearly-commuting projections, stated for
continuous linear endomorphisms of `H d = EuclideanSpace ℂ (Fin d)`:

> `hs_separation_N2'` : if `P₁,…,P_N : H d →L[ℂ] H d` are (orthogonal) projections with
> `‖[Pᵢ,Pⱼ]‖₂,d ≤ ε`, then there are pairwise commuting projections `Q₁,…,Q_N` with
> `‖Pᵢ − Qᵢ‖₂,d ≤ 5·N²·ε`.

This file transports that result, verbatim, across the star-algebra isomorphism
`Matrix.toEuclideanCLM : Matrix (Fin d) (Fin d) ℂ ≃⋆ₐ[ℂ] (H d →L[ℂ] H d)` into the
**matrix** interface used by the rest of the project (`IsProj`, `normHS`, the Lie bracket
`⁅·,·⁆`).  The result is `chao_commuting_projections_N2`, the `O(N²)` Hilbert–Schmidt version of
Chao et al.'s nearby-commuting-projections theorem.
-/

namespace LamplighterStability

open scoped BigOperators ComplexInnerProductSpace
open Matrix

variable {d : ℕ}

/-
The bridge `Matrix.toEuclideanCLM` preserves the normalized Hilbert–Schmidt norm:
the matrix `normHS` agrees with the operator-side `hsNorm`.
-/
lemma normHS_eq_hsNorm (M : Matrix (Fin d) (Fin d) ℂ) :
    normHS M = hsNorm (Matrix.toEuclideanCLM (𝕜 := ℂ) M) := by
  convert congr_arg Real.sqrt ?_ using 1;
  convert hsNorm_def_sqrt _;
  unfold hsNormSq;
  simp +decide [ div_eq_inv_mul, EuclideanSpace.norm_eq ];
  exact Or.inl ( by rw [ Finset.sum_comm ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] )

/-
A matrix projection maps to an operator projection (`IsProjCLM`) under the bridge.
-/
lemma isProjCLM_toEuclideanCLM {M : Matrix (Fin d) (Fin d) ℂ} (hM : IsProj M) :
    IsProjCLM (Matrix.toEuclideanCLM (𝕜 := ℂ) M) := by
  refine ⟨?_, ?_⟩
  · have h := map_star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d)) M
    rw [show (star M : Matrix (Fin d) (Fin d) ℂ) = Mᴴ from rfl, hM.1] at h
    simpa using h.symm
  · rw [← map_mul]
    exact congrArg _ hM.2

/-
Conversely, an operator projection pulls back to a matrix projection under the inverse bridge.
-/
lemma isProj_symm_of_isProjCLM {A : H d →L[ℂ] H d} (hA : IsProjCLM A) :
    IsProj ((Matrix.toEuclideanCLM (𝕜 := ℂ)).symm A) := by
  convert hA using 1;
  constructor <;> intro h <;> rcases h with ⟨ h₁, h₂ ⟩ <;> ( simp_all +decide [ IsProj, IsIdempotentElem, ContinuousLinearMap.ext_iff ] );
  simp_all +decide [ Matrix.IsHermitian, toEuclideanCLM ];
  constructor;
  · ext i j; simp +decide [ LinearMap.toMatrix_apply ] ;
    have := ContinuousLinearMap.adjoint_inner_right A ( EuclideanSpace.single i 1 ) ( EuclideanSpace.single j 1 ) ; simp_all +decide [] ;
    simp_all +decide [ EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right ];
  · rw [ ← LinearMap.toMatrix_comp ];
    exact congr_arg _ ( LinearMap.ext h₂ )

/-
**Chao et al., Theorem 3.2 — normalized Hilbert–Schmidt, `O(N²)` version.**
An almost-commuting family of `N` projections, with pairwise normalized-HS commutator norm at
most `ε`, is `5·N²·ε`-close (in the normalized HS norm) to a genuinely commuting family of
projections.  This is the matrix form of the note's unconditional separation theorem
`hs_separation_N2'`, with no smallness threshold on `ε`.
-/
theorem chao_commuting_projections_N2 {n : ℕ} {ε : ℝ}
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i)) (hε0 : 0 ≤ ε)
    (hcomm : ∀ i j, normHS (⁅P i, P j⁆) ≤ ε) :
    ∃ Q : Fin n → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, IsProj (Q i)) ∧ (∀ i j, Commute (Q i) (Q j)) ∧
      (∀ i, normHS (Q i - P i) ≤ 5 * (n : ℝ) ^ 2 * ε) := by
  by_cases hd : 0 < d;
  · obtain ⟨Q', hQ'⟩ : ∃ Q' : Fin n → (H d →L[ℂ] H d),
      (∀ i, IsProjCLM (Q' i)) ∧ (∀ i j, Q' i * Q' j = Q' j * Q' i) ∧
      (∀ i, hsNorm (Matrix.toEuclideanCLM (𝕜:=ℂ) (P i) - Q' i) ≤ 5 * (n : ℝ) ^ 2 * ε) := by
        apply_rules [ hs_separation_N2' ];
        · exact fun i => isProjCLM_toEuclideanCLM ( hP i );
        · intro i j; specialize hcomm i j; simp_all +decide [ normHS_eq_hsNorm, LieRing.of_associative_ring_bracket ] ;
    refine' ⟨ fun i => ( Matrix.toEuclideanCLM ( 𝕜 := ℂ ) ).symm ( Q' i ), _, _, _ ⟩;
    · exact fun i => isProj_symm_of_isProjCLM ( hQ'.1 i );
    · intro i j; ext; simp +decide [ ← map_mul, hQ'.2.1 i j ] ;
    · intro i;
      convert hQ'.2.2 i using 1;
      convert normHS_eq_hsNorm _ using 1;
      rw [ ← hsNorm_neg ] ; simp +decide [ sub_eq_add_neg, add_comm ] ;
  · refine' ⟨ fun i => P i, _, _, _ ⟩ <;> simp_all +decide [ IsProj ];
    · subst hd; aesop;
    · exact fun i => by positivity;

end LamplighterStability