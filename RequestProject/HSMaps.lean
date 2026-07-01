import Mathlib
import RequestProject.GowersHatami
import RequestProject.HSNorm

/-!
# Trace-based Hilbert–Schmidt norm for maps between finite-dimensional inner product spaces

This file develops a small, reusable Hilbert–Schmidt (Frobenius) norm/trace API for continuous
linear maps `T : E →L[ℂ] F` between finite-dimensional complex inner product spaces, used to
formalize **Lemma 2** of `gh_hs_projection_note_revised-1.pdf` (rounding an almost-invariant
`d`-plane).

The squared HS norm is defined basis-independently via the trace,
`hsq T = (Tr (Tᴴ ∘ T)).re`, and we prove it equals `∑ i, ‖T (b i)‖²` for any orthonormal basis
`b` of the domain.  We also relate it to the existing `hsNormSq`/`hsNorm` on `H d = ℂ^d`.
-/

noncomputable section

open scoped BigOperators ComplexInnerProductSpace
open Finset

namespace HSMaps

variable {E F P : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P]

/-- The unnormalized squared Hilbert–Schmidt (Frobenius) norm of `T : E →L[ℂ] F`,
defined via the trace as `(Tr (Tᴴ ∘ T)).re`. -/
def hsq (T : E →L[ℂ] F) : ℝ :=
  (LinearMap.trace ℂ E ((ContinuousLinearMap.adjoint T ∘L T).toLinearMap)).re

/-- The unnormalized Hilbert–Schmidt (Frobenius) norm `√(hsq T)`. -/
def hsF (T : E →L[ℂ] F) : ℝ := Real.sqrt (hsq T)

/-
`hsq` computed over any orthonormal basis of the domain.
-/
lemma hsq_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] F) :
    hsq T = ∑ i, ‖T (b i)‖ ^ 2 := by
  convert congr_arg Complex.re ( LinearMap.trace_eq_sum_inner ( ( ContinuousLinearMap.adjoint T ∘L T ).toLinearMap ) b ) using 1;
  simp +decide [ ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K ];
  norm_cast

/-
`hsq` is nonnegative.
-/
lemma hsq_nonneg (T : E →L[ℂ] F) : 0 ≤ hsq T := by
  have := @hsq_eq_sum E F ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›;
  exact this ( stdOrthonormalBasis ℂ E ) T ▸ Finset.sum_nonneg fun _ _ => sq_nonneg _

/-
On `H d = ℂ^d`, `hsq` over the standard basis agrees with `hsNormSq`.
-/
lemma hsq_eq_hsNormSq {d : ℕ} (A : H d →L[ℂ] H d) : hsq A = hsNormSq A := by
  have hsq_single : hsq A = ∑ i : Fin d, ‖A (EuclideanSpace.single i 1)‖ ^ 2 := by
    convert hsq_eq_sum ( OrthonormalBasis.ofRepr ( LinearIsometryEquiv.refl ℂ ( EuclideanSpace ℂ ( Fin d ) ) ) ) A;
    erw [ LinearIsometryEquiv.symm_apply_apply ] ; aesop;
  exact hsq_single

/-
For a map out of `H d`, `hsq` is the sum over the standard basis.
-/
lemma hsq_single {d : ℕ} (T : H d →L[ℂ] F) :
    hsq T = ∑ i : Fin d, ‖T (EuclideanSpace.single i 1)‖ ^ 2 := by
  convert hsq_eq_sum (OrthonormalBasis.ofRepr
      (LinearIsometryEquiv.refl ℂ (EuclideanSpace ℂ (Fin d)))) T
  erw [LinearIsometryEquiv.symm_apply_apply]; aesop

/-
`hsq` of an adjoint equals `hsq` of the map (trace symmetry).
-/
lemma hsq_adjoint (T : E →L[ℂ] F) : hsq (ContinuousLinearMap.adjoint T) = hsq T := by
  unfold hsq; simp +decide [ ContinuousLinearMap.adjoint ] ;
  grind +suggestions

/-
`hsF` triangle inequality.
-/
lemma hsF_triangle (S T : E →L[ℂ] F) : hsF (S + T) ≤ hsF S + hsF T := by
  -- Let `b = stdOrthonormalBasis ℂ E`. By `hsq_eq_sum b`, `hsF X = ‖vX‖` where `vX : PiLp 2 (fun i => F)` is `(WithLp.equiv 2 _).symm (fun i => X (b i))`.
  set b := stdOrthonormalBasis ℂ E
  have h_hsf_eq_norm : ∀ X : E →L[ℂ] F, hsF X = ‖(WithLp.equiv 2 _).symm (fun i => X (b i))‖ := by
    intro X
    have h_hsf_eq_norm : hsF X = Real.sqrt (∑ i, ‖X (b i)‖ ^ 2) := by
      rw [ ← hsq_eq_sum b X, hsF ];
    simp +decide [ h_hsf_eq_norm, PiLp.norm_eq_of_L2 ];
  convert norm_add_le ( ( WithLp.equiv 2 ( Fin ( Module.finrank ℂ E ) → F ) ).symm fun i => S ( b i ) ) ( ( WithLp.equiv 2 ( Fin ( Module.finrank ℂ E ) → F ) ).symm fun i => T ( b i ) ) using 1;
  · convert h_hsf_eq_norm ( S + T ) using 1;
  · rw [ h_hsf_eq_norm, h_hsf_eq_norm ]

/-
`hsF` of the negation.
-/
lemma hsF_neg (T : E →L[ℂ] F) : hsF (-T) = hsF T := by
  simp +decide [ hsF, hsq ]

lemma hsF_nonneg (T : E →L[ℂ] F) : 0 ≤ hsF T := Real.sqrt_nonneg _

/-- `hsF` is subadditive across a difference. -/
lemma hsF_sub_triangle (A B C : E →L[ℂ] F) : hsF (A - C) ≤ hsF (A - B) + hsF (B - C) := by
  have := hsF_triangle (A - B) (B - C)
  simpa [sub_add_sub_cancel] using this

/-
Left composition with an operator of operator norm `≤ 1` does not increase `hsF`.
-/
lemma hsF_comp_left_le {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [FiniteDimensional ℂ G] (R : F →L[ℂ] G) (hR : ‖R‖ ≤ 1) (T : E →L[ℂ] F) :
    hsF (R ∘L T) ≤ hsF T := by
  refine' Real.sqrt_le_sqrt _;
  convert hsq_eq_sum ( stdOrthonormalBasis ℂ E ) ( R ∘L T ) |> le_of_eq |> le_trans <| ?_;
  rw [ hsq_eq_sum ( stdOrthonormalBasis ℂ E ) T ];
  exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ ( norm_nonneg _ ) ( by simpa using ContinuousLinearMap.le_of_opNorm_le _ ( hR ) _ ) _

end HSMaps

end