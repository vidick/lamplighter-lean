import Mathlib

/-!
# Simultaneous diagonalization of commuting families

This file proves the keystone analytic input needed to discharge the same-dimensional
stability hypothesis (`AbelianStability`) used in `RequestProject.HSSeparation`: a finite
commuting family of self-adjoint operators on a finite-dimensional inner product space admits a
common orthonormal eigenbasis, and consequently so does a finite commuting family of unitaries
(more generally, normal operators whose adjoints also commute).

These are the "simultaneous diagonalization of a finite abelian unitary representation" facts
flagged by the earlier development as the missing keystone for the note's **Lemma 2** (rounding an
almost invariant `d`-plane).  The symmetric case is obtained from Mathlib's joint-eigenspace
decomposition for commuting symmetric operators
(`LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute`) together with the orthonormal
basis subordinate to an internal direct sum (`DirectSum.IsInternal.subordinateOrthonormalBasis`).
Because the joint-eigenvalue tuples range over the infinite index `ι → 𝕜`, the construction is
first restricted to the (finite) support of the decomposition before the subordinate orthonormal
basis is extracted.  The unitary case is reduced to the symmetric one by diagonalizing the
self-adjoint real and imaginary parts of the operators simultaneously (these pairwise commute when
the operators commute together with their adjoints — automatic for a unitary representation of a
finite abelian group, where `(π i)⁻¹ = star (π i)` is itself a member of the family).
-/

noncomputable section

open scoped BigOperators Function
open Module

namespace JointDiag

/-- **Common orthonormal eigenbasis for a commuting family of symmetric operators.**
A finite, pairwise-commuting family `T` of symmetric `𝕜`-linear operators on a finite-dimensional
inner product space `E` has an orthonormal basis indexed by `Fin (finrank 𝕜 E)` each of whose
vectors is an eigenvector of every `T i`. -/
theorem exists_orthonormalBasis_joint_eigenvector_symmetric
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {ι : Type*} [Fintype ι] (T : ι → E →ₗ[𝕜] E)
    (hsym : ∀ i, (T i).IsSymmetric) (hcomm : Pairwise (Commute on T)) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E,
      ∀ (k : Fin (finrank 𝕜 E)) (i : ι), ∃ μ : 𝕜, T i (b k) = μ • (b k) := by
  classical
  set V : (ι → 𝕜) → Submodule 𝕜 E := fun α => ⨅ j, Module.End.eigenspace (T j) (α j) with hVdef
  have hV : DirectSum.IsInternal V :=
    LinearMap.IsSymmetric.LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hsym hcomm
  have hOF : OrthogonalFamily 𝕜 (fun γ : ι → 𝕜 => (V γ : Submodule 𝕜 E))
      (fun γ => (V γ).subtypeₗᵢ) :=
    LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hsym
  -- The joint-eigenspace decomposition has finite support.
  have hsupp : {α : ι → 𝕜 | V α ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hV.submodule_iSupIndep
  set S : Finset (ι → 𝕜) := hsupp.toFinset with hSdef
  -- Restrict the family to its (finite) support so the subordinate orthonormal basis applies.
  set V' : {α // α ∈ S} → Submodule 𝕜 E := fun s => V s.1 with hV'def
  have hinj : Function.Injective (fun s : {α // α ∈ S} => (s : ι → 𝕜)) := Subtype.val_injective
  have hOF' : OrthogonalFamily 𝕜 (fun s : {α // α ∈ S} => (V' s : Submodule 𝕜 E))
      (fun s => (V' s).subtypeₗᵢ) := hOF.comp hinj
  have hsup' : iSup V' = ⊤ := by
    have h1 : iSup V = ⊤ :=
      (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top V |>.1 hV).2
    rw [← h1]
    apply le_antisymm
    · exact iSup_le (fun s => le_iSup V s.1)
    · refine iSup_le (fun α => ?_)
      by_cases hα : V α = ⊥
      · simp [hα]
      · have : α ∈ S := by rw [hSdef, Set.Finite.mem_toFinset]; exact hα
        exact le_iSup V' ⟨α, this⟩
  have hV' : DirectSum.IsInternal V' := by
    rw [hOF'.isInternal_iff, hsup', Submodule.top_orthogonal_eq_bot]
  set n := finrank 𝕜 E with hn
  refine ⟨hV'.subordinateOrthonormalBasis (rfl : finrank 𝕜 E = n) hOF', ?_⟩
  intro k i
  have hmem := hV'.subordinateOrthonormalBasis_subordinate (rfl : finrank 𝕜 E = n) k hOF'
  set idx := hV'.subordinateOrthonormalBasisIndex (rfl : finrank 𝕜 E = n) k hOF' with hidx
  have hmem2 : (hV'.subordinateOrthonormalBasis (rfl : finrank 𝕜 E = n) hOF') k
      ∈ ⨅ j, Module.End.eigenspace (T j) ((idx : ι → 𝕜) j) := hmem
  rw [Submodule.mem_iInf] at hmem2
  have hki := hmem2 i
  rw [Module.End.mem_eigenspace_iff] at hki
  exact ⟨(idx : ι → 𝕜) i, hki⟩

/-- **Common orthonormal eigenbasis for a commuting family of unitaries (more generally, normal
operators with commuting adjoints).**  If `π : ι → (E →L[ℂ] E)` is a finite family of operators on
a finite-dimensional complex inner product space that pairwise commute and whose members also
commute with one another's adjoints (both conditions are automatic for a unitary representation of
a finite abelian group, where `(π i)⁻¹ = star (π i)` is itself a member of the family), then `E`
has an orthonormal basis indexed by `Fin (finrank ℂ E)` each of whose vectors is an eigenvector of
every `π i`.

This is the "simultaneous diagonalization of a finite abelian unitary representation" fact flagged
by the earlier development as the missing keystone for the note's Lemma 2. -/
theorem exists_orthonormalBasis_joint_eigenvector_unitary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] (π : ι → (E →L[ℂ] E))
    (hcomm : ∀ i j, Commute (π i) (π j))
    (hstar : ∀ i j, Commute (π i) (star (π j))) :
    ∃ b : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E,
      ∀ (k : Fin (finrank ℂ E)) (i : ι), ∃ μ : ℂ, π i (b k) = μ • (b k) := by
  -- Self-adjoint real and imaginary parts of the family, as continuous linear maps.
  set H : ι → (E →L[ℂ] E) := fun i => (2⁻¹ : ℂ) • (π i + star (π i)) with hHdef
  set K : ι → (E →L[ℂ] E) := fun i => (2⁻¹ : ℂ) • (Complex.I • (star (π i) - π i)) with hKdef
  -- All four pairings among the operators and their adjoints commute.
  have b3 : ∀ i j, Commute (star (π i)) (π j) := fun i j => (hstar j i).symm
  have b4 : ∀ i j, Commute (star (π i)) (star (π j)) := fun i j => commute_star_star.mpr (hcomm i j)
  have csum : ∀ i j, Commute (π i + star (π i)) (π j + star (π j)) := fun i j =>
    ((hcomm i j).add_right (hstar i j)).add_left ((b3 i j).add_right (b4 i j))
  have csd : ∀ i j, Commute (π i + star (π i)) (star (π j) - π j) := fun i j =>
    ((hstar i j).sub_right (hcomm i j)).add_left ((b4 i j).sub_right (b3 i j))
  have cds : ∀ i j, Commute (star (π i) - π i) (π j + star (π j)) := fun i j =>
    ((b3 i j).add_right (b4 i j)).sub_left ((hcomm i j).add_right (hstar i j))
  have cdd : ∀ i j, Commute (star (π i) - π i) (star (π j) - π j) := fun i j =>
    ((b4 i j).sub_right (b3 i j)).sub_left ((hstar i j).sub_right (hcomm i j))
  have hHsa : ∀ i, IsSelfAdjoint (H i) := by
    intro i; rw [hHdef]; simp only; rw [IsSelfAdjoint, star_smul, star_add, star_star, add_comm]
    norm_num
  have hKsa : ∀ i, IsSelfAdjoint (K i) := by
    intro i; rw [hKdef]; simp only
    rw [IsSelfAdjoint, star_smul, star_smul, star_sub, star_star]
    simp only [Complex.star_def, Complex.conj_I]
    rw [show (starRingEnd ℂ) (2⁻¹ : ℂ) = 2⁻¹ by rw [map_inv₀, map_ofNat]]
    module
  -- The symmetric family indexed by `ι × Bool` (`false ↦ Re`, `true ↦ Im`).
  set T : ι × Bool → E →ₗ[ℂ] E :=
    fun p => if p.2 then ((K p.1 : E →L[ℂ] E) : E →ₗ[ℂ] E) else ((H p.1 : E →L[ℂ] E) : E →ₗ[ℂ] E)
    with hTdef
  have hsym : ∀ p, (T p).IsSymmetric := by
    intro p; rw [hTdef]; simp only
    by_cases hp : p.2
    · simp only [hp, if_true]; exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hKsa p.1)
    · simp only [hp]; exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hHsa p.1)
  have hcoe : ∀ X Y : E →L[ℂ] E,
      ((X * Y : E →L[ℂ] E) : E →ₗ[ℂ] E) = (X : E →ₗ[ℂ] E) * (Y : E →ₗ[ℂ] E) := fun X Y => rfl
  have coeC : ∀ X Y : E →L[ℂ] E, Commute X Y → Commute ((X : E →ₗ[ℂ] E)) ((Y : E →ₗ[ℂ] E)) := by
    intro X Y h
    have : ((X * Y : E →L[ℂ] E) : E →ₗ[ℂ] E) = ((Y * X : E →L[ℂ] E) : E →ₗ[ℂ] E) := by rw [h]
    rw [hcoe, hcoe] at this; exact this
  have cHH : ∀ i j, Commute (H i) (H j) := fun i j => ((csum i j).smul_left _).smul_right _
  have cHK : ∀ i j, Commute (H i) (K j) := fun i j =>
    (((csd i j).smul_left _).smul_right _).smul_right _
  have cKH : ∀ i j, Commute (K i) (H j) := fun i j =>
    (((cds i j).smul_right _).smul_left _).smul_left _
  have cKK : ∀ i j, Commute (K i) (K j) := fun i j =>
    ((((cdd i j).smul_right _).smul_left _).smul_right _).smul_left _
  have hcommT : Pairwise (Commute on T) := by
    intro p q _
    show Commute (T p) (T q)
    rw [hTdef]; simp only
    by_cases hp : p.2 <;> by_cases hq : q.2 <;> simp only [hp, hq, if_true]
    · exact coeC _ _ (cKK _ _)
    · exact coeC _ _ (cKH _ _)
    · exact coeC _ _ (cHK _ _)
    · exact coeC _ _ (cHH _ _)
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_joint_eigenvector_symmetric T hsym hcommT
  refine ⟨b, fun k i => ?_⟩
  obtain ⟨μ0, hμ0⟩ := hb k (i, false)
  obtain ⟨μ1, hμ1⟩ := hb k (i, true)
  have hH : (H i) (b k) = μ0 • b k := by
    have h := hμ0; rw [hTdef] at h; simpa using h
  have hK : (K i) (b k) = μ1 • b k := by
    have h := hμ1; rw [hTdef] at h; simpa using h
  refine ⟨μ0 + Complex.I * μ1, ?_⟩
  have hsplit : π i = H i + Complex.I • K i := by
    rw [hHdef, hKdef]; simp only
    match_scalars <;>
      first
        | linear_combination (2⁻¹ : ℂ) * Complex.I_sq
        | linear_combination (-2⁻¹ : ℂ) * Complex.I_sq
  rw [hsplit]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hH, hK]
  module

end JointDiag

end
