import Mathlib
import RequestProject.GowersHatami

/-!
# Normalized Hilbert–Schmidt norm API

This file develops the small API for the *normalized* Hilbert–Schmidt norm
`‖A‖₂,d = √((1/d)·Tr(A* A))` on continuous linear endomorphisms of `H d = ℂ^d`,
used in the formalization of the normalized-HS projection-separation theorem
(`gh_hs_projection_note.pdf`, Theorem 1).

We reuse `hsNormSq` from `RequestProject.GowersHatami`, where
`hsNormSq A = ∑ i, ‖A eᵢ‖²` (the *unnormalized* squared HS norm).
-/

noncomputable section

open scoped BigOperators
open Finset

variable {d : ℕ}

/-- The "Hilbert–Schmidt vector" of `A`: the tuple `(A e₀, …, A e_{d-1})` viewed as an
element of the `L²` space `PiLp 2 (fun _ : Fin d => H d)`.  Its norm-squared is `hsNormSq A`. -/
def hsVec (A : H d →L[ℂ] H d) : PiLp 2 (fun _ : Fin d => H d) :=
  (WithLp.equiv 2 _).symm (fun i => A (EuclideanSpace.single i 1))

lemma hsVec_add (A B : H d →L[ℂ] H d) : hsVec (A + B) = hsVec A + hsVec B := by
  ext i; simp [hsVec]

lemma hsVec_normSq (A : H d →L[ℂ] H d) : ‖hsVec A‖ ^ 2 = hsNormSq A := by
  erw [ PiLp.norm_eq_of_L2 ];
  rw [ Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ] ; rfl

/-- The normalized Hilbert–Schmidt norm `‖A‖₂,d = √((1/d)·Tr(A* A))`. -/
def hsNorm (A : H d →L[ℂ] H d) : ℝ := ‖hsVec A‖ / Real.sqrt d

lemma hsNorm_def_sqrt (A : H d →L[ℂ] H d) :
    hsNorm A = Real.sqrt (hsNormSq A / d) := by
  rw [ ← hsVec_normSq A, Real.sqrt_div' ];
  · rw [ Real.sqrt_sq ( norm_nonneg _ ), hsNorm ];
  · positivity

lemma hsNorm_zero : hsNorm (0 : H d →L[ℂ] H d) = 0 := by
  have h : hsVec (0 : H d →L[ℂ] H d) = 0 := by ext i; simp [hsVec]
  simp [hsNorm, h]

lemma hsNorm_triangle (A B : H d →L[ℂ] H d) :
    hsNorm (A + B) ≤ hsNorm A + hsNorm B := by
  unfold hsNorm;
  rw [ ← add_div, hsVec_add ];
  gcongr;
  exact norm_add_le _ _

lemma hsNorm_sub_triangle (A B C : H d →L[ℂ] H d) :
    hsNorm (A - C) ≤ hsNorm (A - B) + hsNorm (B - C) := by
  convert hsNorm_triangle ( A - B ) ( B - C ) using 1;
  rw [ sub_add_sub_cancel ]

lemma hsNorm_neg (A : H d →L[ℂ] H d) : hsNorm (-A) = hsNorm A := by
  simp [hsNorm];
  rw [ show hsVec ( -A ) = -hsVec A from ?_, norm_neg ];
  ext; simp [hsVec]

lemma hsNorm_smul (c : ℂ) (A : H d →L[ℂ] H d) :
    hsNorm (c • A) = ‖c‖ * hsNorm A := by
  unfold hsNorm;
  convert congr_arg ( fun x : ℝ => x / Real.sqrt d ) ( norm_smul c ( hsVec A ) ) using 1 ; ring

/-
Left multiplication by a unitary preserves the normalized HS norm.
-/
lemma hsNorm_left_unitary {U : H d →L[ℂ] H d}
    (hU : U ∈ unitary (H d →L[ℂ] H d)) (A : H d →L[ℂ] H d) :
    hsNorm (U.comp A) = hsNorm A := by
  unfold hsNorm;
  rw [ ← sq_eq_sq₀, sq, sq ];
  · field_simp;
    rw [ hsVec_normSq, hsVec_normSq, hsNormSq_comp_unitary hU ];
  · positivity;
  · positivity

/-
Right multiplication by a unitary preserves the normalized HS norm.
-/
lemma hsNorm_right_unitary {U : H d →L[ℂ] H d}
    (hU : U ∈ unitary (H d →L[ℂ] H d)) (A : H d →L[ℂ] H d) :
    hsNorm (A.comp U) = hsNorm A := by
  rw [ hsNorm_def_sqrt, hsNorm_def_sqrt ];
  rw [ show hsNormSq ( A.comp U ) = hsNormSq ( ContinuousLinearMap.adjoint U ∘L A.adjoint ) from ?_ ];
  · rw [ hsNormSq_comp_unitary ];
    · simp +decide [ hsNormSq ];
      have h_trace : ∀ (B : H d →L[ℂ] H d), ∑ i : Fin d, ‖B (EuclideanSpace.single i 1)‖ ^ 2 = ∑ i : Fin d, ‖(ContinuousLinearMap.adjoint B) (EuclideanSpace.single i 1)‖ ^ 2 := by
        intro B
        have h_trace : ∑ i : Fin d, ‖B (EuclideanSpace.single i 1)‖ ^ 2 = ∑ i : Fin d, ∑ j : Fin d, ‖(B (EuclideanSpace.single i 1)) j‖ ^ 2 := by
          simp +decide [ EuclideanSpace.norm_eq, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
        have h_trace : ∑ i : Fin d, ∑ j : Fin d, ‖(B (EuclideanSpace.single i 1)) j‖ ^ 2 = ∑ j : Fin d, ∑ i : Fin d, ‖(B.adjoint (EuclideanSpace.single j 1)) i‖ ^ 2 := by
          rw [ Finset.sum_comm ];
          refine' Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => _;
          have := ContinuousLinearMap.adjoint_inner_right B ( EuclideanSpace.single i 1 ) ( EuclideanSpace.single j 1 ) ; simp_all +decide [ EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right ] ;
        convert h_trace using 1;
        simp +decide [ EuclideanSpace.norm_eq, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
      rw [ h_trace ];
      rw [ ContinuousLinearMap.adjoint_adjoint ];
    · constructor;
      · simp_all +decide [ star, ContinuousLinearMap.ext_iff ];
        intro x; exact (by
        have := hU.2;
        convert congr_arg ( fun f => f x ) this using 1);
      · simp +decide [ star ];
        have := hU.1;
        convert this using 1;
  · unfold hsNormSq;
    have h_trace : ∀ (B : H d →L[ℂ] H d), ∑ i : Fin d, ‖B (EuclideanSpace.single i 1)‖ ^ 2 = ∑ i : Fin d, ‖(ContinuousLinearMap.adjoint B) (EuclideanSpace.single i 1)‖ ^ 2 := by
      intro B
      have h_trace : ∑ i : Fin d, ‖B (EuclideanSpace.single i 1)‖ ^ 2 = ∑ i : Fin d, ∑ j : Fin d, ‖(B (EuclideanSpace.single i 1)) j‖ ^ 2 := by
        simp +decide [ EuclideanSpace.norm_eq, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
      have h_trace : ∑ i : Fin d, ∑ j : Fin d, ‖(B (EuclideanSpace.single i 1)) j‖ ^ 2 = ∑ j : Fin d, ∑ i : Fin d, ‖(B.adjoint (EuclideanSpace.single j 1)) i‖ ^ 2 := by
        rw [ Finset.sum_comm ];
        refine' Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => _;
        have := ContinuousLinearMap.adjoint_inner_right B ( EuclideanSpace.single i 1 ) ( EuclideanSpace.single j 1 ) ; simp_all +decide [ EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right ] ;
      convert h_trace using 1;
      simp +decide [ EuclideanSpace.norm_eq, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ];
    convert h_trace _ using 3;
    rw [ ContinuousLinearMap.adjoint_comp ]

end