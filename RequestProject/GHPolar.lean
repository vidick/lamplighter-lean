import Mathlib

/-!
# Polar decomposition of a square matrix

This file provides the unitary polar factor of a square complex matrix, used by the
polar-rounding step (`HSPolarRound`) of the dimension-adjustment lemma in
`gh_hs_projection_note.pdf`.

The development is organized as:
* `exists_psd_sqrt` — existence of a positive-semidefinite square root of a PSD matrix;
* `polar_isometry` — given `P` positive semidefinite with `P² = Aᴴ A`, there is a unitary `W`
  with `Wᴴ A = P` (built from `LinearIsometry.extend`);
* `exists_unitary_polar` — the polar decomposition `A = W P` with `W` unitary and `P` PSD.
-/

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ComplexOrder
open Finset Matrix

variable {d : ℕ}

/-
Existence of a positive-semidefinite square root of a positive-semidefinite matrix.
-/
open scoped MatrixOrder in
lemma exists_psd_sqrt (M : Matrix (Fin d) (Fin d) ℂ) (hM : M.PosSemidef) :
    ∃ P : Matrix (Fin d) (Fin d) ℂ, P.PosSemidef ∧ P * P = M :=
  ⟨CFC.sqrt M, (CFC.sqrt_nonneg M).posSemidef,
    CFC.sqrt_mul_sqrt_self M (ha := Matrix.nonneg_iff_posSemidef.mpr hM)⟩

/-
**Polar isometry.**  Given `P` positive semidefinite with `P² = Aᴴ A`, there is a unitary `W`
with `Wᴴ A = P` (so `A = W P`).  Built from `LinearIsometry.extend`.
-/
lemma polar_isometry (A P : Matrix (Fin d) (Fin d) ℂ)
    (hPpsd : P.PosSemidef) (hPsq : P * P = Aᴴ * A) :
    ∃ W : Matrix (Fin d) (Fin d) ℂ, Wᴴ * W = 1 ∧ Wᴴ * A = P := by
  revert A;
  intro A hPsq
  have h_norm_eq : ∀ v : EuclideanSpace ℂ (Fin d), ‖(toEuclideanLin A) v‖ = ‖(toEuclideanLin P) v‖ := by
    have h_norm_eq : ∀ v : EuclideanSpace ℂ (Fin d), ‖(toEuclideanLin A) v‖^2 = ‖(toEuclideanLin P) v‖^2 := by
      intro v
      have h_inner : inner ℂ ((toEuclideanLin A) v) ((toEuclideanLin A) v) = inner ℂ ((toEuclideanLin P) v) ((toEuclideanLin P) v) := by
        have h_inner : inner ℂ ((toEuclideanLin A) v) ((toEuclideanLin A) v) = inner ℂ v ((toEuclideanLin (Aᴴ * A)) v) := by
          simp +decide [ Matrix.mulVec, dotProduct, inner ];
          simp +decide only [Finset.mul_sum _ _ _, mul_comm, mul_left_comm];
          exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
        have h_inner_P : inner ℂ ((toEuclideanLin P) v) ((toEuclideanLin P) v) = inner ℂ v ((toEuclideanLin (Pᴴ * P)) v) := by
          simp +decide [ Matrix.mulVec, dotProduct, inner ];
          simp +decide only [Finset.mul_sum _ _ _, mul_comm, mul_left_comm];
          exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
        have := hPpsd.1; simp_all +decide [ Matrix.IsHermitian ] ;
        simp_all +decide [ toLpLin ]
      rw [ ← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, h_inner ];
    exact fun v => by rw [ ← sq_eq_sq₀ ( norm_nonneg _ ) ( norm_nonneg _ ), h_norm_eq v ] ;
  obtain ⟨W', hW'⟩ : ∃ W' : (EuclideanSpace ℂ (Fin d)) →ₗᵢ[ℂ] (EuclideanSpace ℂ (Fin d)), ∀ v : EuclideanSpace ℂ (Fin d), W' ((toEuclideanLin P) v) = (toEuclideanLin A) v := by
    have h_isometry : ∃ T : (↥(LinearMap.range (toEuclideanLin P))) →ₗᵢ[ℂ] (EuclideanSpace ℂ (Fin d)), ∀ v : EuclideanSpace ℂ (Fin d), T ⟨(toEuclideanLin P) v, LinearMap.mem_range_self _ _⟩ = (toEuclideanLin A) v := by
      have h_isometry : ∀ v w : EuclideanSpace ℂ (Fin d), (toEuclideanLin P) v = (toEuclideanLin P) w → (toEuclideanLin A) v = (toEuclideanLin A) w := by
        intro v w hvw; have := h_norm_eq ( v - w ) ; simp_all +decide [ sub_eq_zero ] ;
      have h_isometry : ∃ T : (↥(LinearMap.range (toEuclideanLin P))) →ₗ[ℂ] (EuclideanSpace ℂ (Fin d)), ∀ v : EuclideanSpace ℂ (Fin d), T ⟨(toEuclideanLin P) v, LinearMap.mem_range_self _ _⟩ = (toEuclideanLin A) v := by
        refine' ⟨ _, _ ⟩;
        refine' { toFun := fun x => ( toEuclideanLin A ) ( Classical.choose x.2 ), map_add' := _, map_smul' := _ };
        all_goals norm_num [ h_isometry ];
        · intro a x hx a_1 x_1 hx_1;
          rw [ ← map_add ];
          grind +revert;
        · intro m a x hx
          have h_eq : (toEuclideanLin P) (m • Classical.choose (show ∃ v, (toEuclideanLin P) v = a from ⟨x, hx⟩)) = (toEuclideanLin P) (Classical.choose (show ∃ v, (toEuclideanLin P) v = m • a from ⟨m • x, by
                                                                                                                                                            rw [ ← hx, map_smul ]⟩)) := by
                                                                                                                                                            all_goals generalize_proofs at *;
                                                                                                                                                            have := Classical.choose_spec ‹∃ x, ( toEuclideanLin P ) x = m • a›; have := Classical.choose_spec ‹∃ x, ( toEuclideanLin P ) x = a›; aesop;
          generalize_proofs at *;
          rw [ ← h_isometry _ _ h_eq ];
          exact map_smul ( toEuclideanLin A ) m _;
        · grind;
      obtain ⟨ T, hT ⟩ := h_isometry;
      refine' ⟨ { toFun := T, map_add' := _, map_smul' := _, norm_map' := _ }, hT ⟩;
      rintro ⟨ x, hx ⟩ ; obtain ⟨ v, rfl ⟩ := hx; aesop;
    obtain ⟨ T, hT ⟩ := h_isometry;
    obtain ⟨W', hW'⟩ : ∃ W' : (EuclideanSpace ℂ (Fin d)) →ₗᵢ[ℂ] (EuclideanSpace ℂ (Fin d)), W' ∘ (Submodule.subtypeL (LinearMap.range (toEuclideanLin P))) = T.toLinearMap := by
      exact ⟨ T.extend, by ext; simp +decide [ LinearIsometry.extend_apply ] ⟩;
    exact ⟨ W', fun v => by simpa [ hT ] using congr_fun hW' ⟨ ( toEuclideanLin P ) v, LinearMap.mem_range_self _ _ ⟩ ⟩;
  -- Realize `W'` as a matrix `W` with `W i j = W' (EuclideanSpace.single j 1) i` so that `toEuclideanLin W = W'` as maps.
  obtain ⟨W, hW⟩ : ∃ W : Matrix (Fin d) (Fin d) ℂ, toEuclideanLin W = W' ∧ Wᴴ * W = 1 := by
    refine' ⟨ Matrix.of fun i j => W' ( EuclideanSpace.single j 1 ) i, _, _ ⟩;
    · ext v i; simp +decide [ Matrix.mulVec, dotProduct ] ;
      rw [ show v = ∑ x, v.ofLp x • EuclideanSpace.single x 1 from ?_ ];
      · simp +decide [ mul_comm, Pi.single_apply ];
      · ext i; simp +decide [] ;
        rw [ Finset.sum_eq_single i ] <;> aesop;
    · have hW'_isometry : ∀ i j : Fin d, inner ℂ (W' (EuclideanSpace.single i 1)) (W' (EuclideanSpace.single j 1)) = if i = j then 1 else 0 := by
        intro i j; rw [ W'.inner_map_map ] ;
        split_ifs <;> simp +decide [ *, inner ];
      ext i j; specialize hW'_isometry i j; simp_all +decide [ Matrix.mul_apply, inner ] ;
      simpa only [ mul_comm, Matrix.one_apply ] using hW'_isometry;
  -- From step 3, `W*P = A` as matrices (compare `mulVec` on standard basis vectors).
  have hWP : W * P = A := by
    ext i j; simp_all +decide [ toEuclideanLin ] ;
    convert congr_arg ( fun x : EuclideanSpace ℂ ( Fin d ) => x i ) ( hW' ( EuclideanSpace.single j 1 ) ) using 1 <;> simp +decide [ toLpLin ];
    convert congr_arg ( fun x : EuclideanSpace ℂ ( Fin d ) => x i ) ( congr_arg ( fun f : EuclideanSpace ℂ ( Fin d ) →ₗ[ℂ] EuclideanSpace ℂ ( Fin d ) => f ( WithLp.toLp 2 ( P.col j ) ) ) hW.1 ) using 1;
  refine' ⟨ W, hW.2, _ ⟩;
  rw [ ← hWP, ← Matrix.mul_assoc, hW.2, Matrix.one_mul ]

/-- **Polar decomposition** (existence of the unitary polar factor).  For any square matrix `A`
there is a unitary `W` and a positive-semidefinite `P` with `P² = Aᴴ A` and `Wᴴ A = P`
(so `A = W P`). -/
lemma exists_unitary_polar (A : Matrix (Fin d) (Fin d) ℂ) :
    ∃ W P : Matrix (Fin d) (Fin d) ℂ,
      Wᴴ * W = 1 ∧ P.PosSemidef ∧ P * P = Aᴴ * A ∧ Wᴴ * A = P := by
  obtain ⟨P, hPpsd, hPsq⟩ := exists_psd_sqrt (Aᴴ * A) (posSemidef_conjTranspose_mul_self A)
  obtain ⟨W, hWuni, hWA⟩ := polar_isometry A P hPpsd hPsq
  exact ⟨W, P, hWuni, hPpsd, hPsq, hWA⟩

end
