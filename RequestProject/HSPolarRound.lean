import Mathlib
import RequestProject.HSMaps
import RequestProject.HSLemma2
import RequestProject.GHPolar

/-!
# Polar rounding into the range of a rank-`d` projection (abstract Hilbert space)

This file proves the analytic keystone of the note's **Lemma 2**
(`gh_hs_projection_note_revised-1.pdf`, §3): given an isometry `W : ℂ^d → K` and a rank-`d`
orthogonal projection `F` on a finite-dimensional inner product space `K`, the polar decomposition
of `F W` provides an isometry `U : ℂ^d → K` whose range is `F K` (`U Uᴴ = F`) and which is no
farther from `W` than `F` is from `E = W Wᴴ` in Hilbert–Schmidt norm:
`‖U − W‖²_HS ≤ ‖F − W Wᴴ‖²_HS`.

This is the inequality `∑ⱼ (1 − sⱼ)² ≤ ∑ⱼ (1 − sⱼ²)` for singular values `sⱼ ∈ [0,1]` of `F W`,
phrased trace-theoretically.
-/

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ComplexInnerProductSpace
open Finset HSMaps
open ContinuousLinearMap (adjoint)

namespace HSLemma2

variable {d : ℕ}
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

/-! ### Small `hsq` lemmas -/

/-- `hsq` is invariant under negation. -/
lemma hsq_neg {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : E →L[ℂ] F) : hsq (-T) = hsq T := by
  simp [hsq, ContinuousLinearMap.adjoint]

/-
Right composition with a unitary (an operator `V` with `Vᴴ V = 1` on a finite-dimensional
space) preserves `hsq`.
-/
lemma hsq_comp_right_iso {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (T : E →L[ℂ] F) (V : E →L[ℂ] E) (hV : adjoint V ∘L V = 1) :
    hsq (T ∘L V) = hsq T := by
  obtain ⟨U, hU⟩ : ∃ U : E ≃ₗᵢ[ℂ] E, U.toContinuousLinearEquiv.toContinuousLinearMap = V := by
    refine' ⟨ _, _ ⟩;
    refine' { Equiv.ofBijective V ⟨ _, _ ⟩ with .. };
    all_goals simp_all +decide [ ContinuousLinearMap.ext_iff ];
    · exact fun x y hxy => by have := hV x; have := hV y; aesop;
    · exact LinearMap.surjective_of_injective ( show Function.Injective V from fun x y hxy => by simpa [ hV ] using congr_arg ( adjoint V ) hxy );
    · grind +suggestions;
  rw [ hsq_eq_sum ( stdOrthonormalBasis ℂ E ) ];
  rw [ hsq_eq_sum ( OrthonormalBasis.map ( stdOrthonormalBasis ℂ E ) U ) T ];
  simp +decide [ ← hU ]

/-
The adjoint of an isometry has operator norm `≤ 1`.
-/
lemma opNorm_adjoint_le_one {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (U : E →L[ℂ] F) (hU : adjoint U ∘L U = 1) : ‖adjoint U‖ ≤ 1 := by
  refine' ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => _;
  have h_norm : ∀ x : E, ‖U x‖ = ‖x‖ := by
    intro x
    have h_inner : inner ℂ (U x) (U x) = inner ℂ x x := by
      rw [ ← ContinuousLinearMap.adjoint_inner_right ];
      rw [ show ( adjoint U ) ( U x ) = x from by simpa using congr_arg ( fun f => f x ) hU ];
    simp_all +decide [ inner_self_eq_norm_sq_to_K ];
    norm_cast at h_inner ; simpa using h_inner;
  have := U.adjoint_inner_right ( adjoint U x ) x; simp_all +decide [] ;
  have := this ▸ norm_inner_le_norm ( U ( adjoint U x ) ) x;
  simp_all +decide [ sq ];
  norm_num [ ← ‹ ( ‖ ( adjoint U ) x‖ : ℂ ) * ‖ ( adjoint U ) x‖ = ⟪U ( ( adjoint U ) x ), x⟫ › ] at this ⊢ ; nlinarith [ norm_nonneg x, norm_nonneg ( adjoint U x ) ]

/-! ### The polar-rounding lemma -/

/-
**Existence of an isometry onto a rank-`d` plane.**  A rank-`d` orthogonal projection `F` on `K`
admits an isometry `U₀ : ℂ^d → K` with range exactly `F K` (`U₀ᴴ U₀ = 1`, `U₀ U₀ᴴ = F`,
`F U₀ = U₀`).
-/
lemma exists_isometry_onto_proj
    (F : K →L[ℂ] K) (hFsa : adjoint F = F) (hFidem : F ∘L F = F)
    (hFtr : LinearMap.trace ℂ K F.toLinearMap = (d : ℂ)) :
    ∃ U₀ : H d →L[ℂ] K,
      adjoint U₀ ∘L U₀ = 1 ∧ U₀ ∘L adjoint U₀ = F ∧ F ∘L U₀ = U₀ := by
  have h_range : Module.finrank ℂ (LinearMap.range (F : K →ₗ[ℂ] K)) = d := by
    have h_finrank : LinearMap.trace ℂ K (F : K →ₗ[ℂ] K) = Module.finrank ℂ (LinearMap.range (F : K →ₗ[ℂ] K)) := by
      have h_finrank : ∀ (P : K →ₗ[ℂ] K), P ∘ₗ P = P → (LinearMap.trace ℂ K P) = Module.finrank ℂ (LinearMap.range P) := by
        intro P hP;
        have h_iso : ∃ (f : LinearMap.range P →ₗ[ℂ] K), P = f ∘ₗ LinearMap.rangeRestrict P := by
          exact ⟨ Submodule.subtype _, by ext; simp +decide ⟩;
        obtain ⟨ f, hf ⟩ := h_iso;
        have h_iso : P.rangeRestrict ∘ₗ f = LinearMap.id := by
          ext x;
          obtain ⟨ y, hy ⟩ := x;
          obtain ⟨ z, rfl ⟩ := hy;
          replace hf := congr_arg ( fun g => g z ) hf; simp +decide [] at hf;
          replace hP := congr_arg ( fun g => g z ) hP; simp_all +decide [] ;
          convert hP using 1;
          congr! 2;
          exact Subtype.ext ( by aesop );
        grind +suggestions;
      exact h_finrank _ ( by simpa [ ← ContinuousLinearMap.coe_comp ] using congr_arg ( fun f : K →L[ℂ] K => ( f : K →ₗ[ℂ] K ) ) hFidem );
    exact_mod_cast h_finrank.symm.trans hFtr;
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : (EuclideanSpace ℂ (Fin d)) →ₗᵢ[ℂ] K, LinearMap.range (U₀.toLinearMap) = LinearMap.range (F : K →ₗ[ℂ] K) := by
    have h_iso : Nonempty (EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℂ] (LinearMap.range (F : K →ₗ[ℂ] K))) := by
      refine' ⟨ _ ⟩;
      have h_iso : Nonempty (OrthonormalBasis (Fin d) ℂ (LinearMap.range (F : K →ₗ[ℂ] K))) := by
        exact ⟨ h_range ▸ stdOrthonormalBasis ℂ _ ⟩;
      exact h_iso.some.repr.symm;
    obtain ⟨ U₀ ⟩ := h_iso;
    refine' ⟨ _, _ ⟩;
    refine' { toFun := fun x => U₀ x, map_add' := _, map_smul' := _, norm_map' := _ };
    all_goals simp +decide [ SetLike.ext_iff ];
    · exact fun x => U₀.norm_map x;
    · exact fun x => ⟨ fun ⟨ y, hy ⟩ => by rcases U₀ y |>.2 with ⟨ z, hz ⟩ ; aesop, fun ⟨ y, hy ⟩ => ⟨ U₀.symm ⟨ F y, by aesop ⟩, by simp +decide [ hy ] ⟩ ⟩;
  refine' ⟨ U₀.toContinuousLinearMap, _, _, _ ⟩;
  · ext v; simp +decide [] ;
    grind +suggestions;
  · have hU₀_comp : ∀ x : K, U₀.toContinuousLinearMap (U₀.toContinuousLinearMap.adjoint x) = F x := by
      intro x
      have hU₀_comp : ∀ y ∈ LinearMap.range (F : K →ₗ[ℂ] K), U₀.toContinuousLinearMap (U₀.toContinuousLinearMap.adjoint y) = y := by
        intro y hy
        obtain ⟨z, hz⟩ : ∃ z : EuclideanSpace ℂ (Fin d), U₀ z = y := by
          exact LinearMap.mem_range.mp ( hU₀.symm ▸ hy );
        have hU₀_comp : U₀.toContinuousLinearMap (U₀.toContinuousLinearMap.adjoint (U₀ z)) = U₀ z := by
          rw [ adjoint_isometry_apply ];
          rfl;
        grind;
      have hU₀_comp : ∀ y ∈ (LinearMap.range (F : K →ₗ[ℂ] K))ᗮ, U₀.toContinuousLinearMap (U₀.toContinuousLinearMap.adjoint y) = 0 := by
        intro y hy
        have hU₀_comp : ∀ z : EuclideanSpace ℂ (Fin d), inner ℂ (U₀.toContinuousLinearMap z) y = 0 := by
          intro z
          have hU₀_comp : U₀.toContinuousLinearMap z ∈ LinearMap.range (F : K →ₗ[ℂ] K) := by
            exact hU₀ ▸ LinearMap.mem_range_self _ _;
          exact hy _ hU₀_comp;
        have hU₀_comp : ∀ z : EuclideanSpace ℂ (Fin d), inner ℂ z (U₀.toContinuousLinearMap.adjoint y) = 0 := by
          simp_all +decide [ ContinuousLinearMap.adjoint_inner_right ];
        specialize hU₀_comp ( adjoint U₀.toContinuousLinearMap y ) ; aesop;
      have hU₀_comp : x - F x ∈ (LinearMap.range (F : K →ₗ[ℂ] K))ᗮ := by
        intro y hy; obtain ⟨ z, rfl ⟩ := hy; simp +decide [] ;
        simp +decide [ ← ContinuousLinearMap.adjoint_inner_right, hFsa ];
        simp +decide [ ← ContinuousLinearMap.comp_apply, hFidem ];
      have := ‹∀ y ∈ ( F : K →ₗ[ℂ] K ).rangeᗮ, U₀.toContinuousLinearMap ( adjoint U₀.toContinuousLinearMap y ) = 0› ( x - F x ) hU₀_comp; simp_all +decide [ sub_eq_iff_eq_add ] ;
    exact ContinuousLinearMap.ext hU₀_comp;
  · ext x;
    obtain ⟨ y, hy ⟩ := LinearMap.mem_range.mp ( hU₀.symm ▸ LinearMap.mem_range_self _ x );
    replace hFidem := congr_arg ( fun f => f y ) hFidem; aesop;

open Matrix ComplexOrder in
/-- **Square polar decomposition.**  Any operator `A` on `ℂ^d` factors as `A = V P` with `V`
unitary and `P := Vᴴ A` positive semidefinite. -/
lemma exists_square_polar (A : H d →L[ℂ] H d) :
    ∃ V : H d →L[ℂ] H d,
      adjoint V ∘L V = 1 ∧ V ∘L adjoint V = 1 ∧
      adjoint (adjoint V ∘L A) = adjoint V ∘L A ∧
      (∀ v : H d, 0 ≤ (inner ℂ v ((adjoint V ∘L A) v)).re) := by
  set e := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) with he
  obtain ⟨Wm, Pm, hWW, hPpsd, hPsq, hWA⟩ := exists_unitary_polar (e.symm A)
  -- adjoint of `e M` is `e Mᴴ`
  have hadj : ∀ M : Matrix (Fin d) (Fin d) ℂ,
      adjoint (e M) = e M.conjTranspose := by
    intro M
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]; rfl
  have hcomp : ∀ M N : Matrix (Fin d) (Fin d) ℂ, (e M) ∘L (e N) = e (M * N) := by
    intro M N; show (e M) * (e N) = e (M * N); rw [← map_mul]
  have heA : e (e.symm A) = A := e.apply_symm_apply A
  refine ⟨e Wm, ?_, ?_, ?_, ?_⟩
  · rw [hadj, hcomp, hWW, map_one]
  · rw [hadj, hcomp, (mul_eq_one_comm.mp hWW), map_one]
  · -- `adjoint (e Wm) ∘L A = e Pm`, which is self-adjoint
    have hP : adjoint (e Wm) ∘L A = e Pm := by
      conv_lhs => rw [hadj, ← heA]
      rw [hcomp, hWA]
    rw [hP, hadj, hPpsd.1]
  · intro v
    have hP : adjoint (e Wm) ∘L A = e Pm := by
      conv_lhs => rw [hadj, ← heA]
      rw [hcomp, hWA]
    rw [hP]
    have hval : (e Pm) v = (WithLp.equiv 2 _).symm (Pm.mulVec v) :=
      (Equiv.apply_eq_iff_eq_symm_apply (WithLp.equiv 2 (Fin d → ℂ))).mp rfl
    rw [hval, EuclideanSpace.inner_eq_star_dotProduct]
    have hz := hPpsd.dotProduct_mulVec_nonneg v.ofLp
    have hzre := (Complex.le_def.mp hz).1
    simpa [dotProduct_comm, Equiv.apply_symm_apply] using hzre

lemma exists_polar_isometry
    (W : H d →L[ℂ] K)
    (F : K →L[ℂ] K) (hFsa : adjoint F = F) (hFidem : F ∘L F = F)
    (hFtr : LinearMap.trace ℂ K F.toLinearMap = (d : ℂ)) :
    ∃ U : H d →L[ℂ] K,
      adjoint U ∘L U = 1 ∧ U ∘L adjoint U = F ∧ F ∘L U = U ∧
      adjoint (adjoint U ∘L W) = adjoint U ∘L W ∧
      (∀ v : H d, 0 ≤ (inner ℂ v ((adjoint U ∘L W) v)).re) := by
  obtain ⟨U₀, hU0U0, hU0F, hFU0⟩ := exists_isometry_onto_proj F hFsa hFidem hFtr
  obtain ⟨V, hVV, hVVadj, hPsa, hPpos⟩ := exists_square_polar (adjoint U₀ ∘L W)
  refine ⟨U₀ ∘L V, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc] at *
  · rw [← ContinuousLinearMap.comp_assoc (adjoint U₀) U₀ V, hU0U0]; simpa using hVV
  · rw [← ContinuousLinearMap.comp_assoc V (adjoint V) (adjoint U₀), hVVadj]; simpa using hU0F
  · rw [← ContinuousLinearMap.comp_assoc F U₀ V, hFU0]
  · exact hPsa
  · exact hPpos

/-
Trace cyclicity across `H d` and `K`.
-/
lemma trace_comp_comm_HK (A : H d →L[ℂ] K) (B : K →L[ℂ] H d) :
    LinearMap.trace ℂ K (A ∘L B).toLinearMap
      = LinearMap.trace ℂ (H d) (B ∘L A).toLinearMap := by
  convert LinearMap.trace_comp_comm' ( B.toLinearMap ) ( A.toLinearMap ) using 1

/-
For a self-adjoint positive-semidefinite contraction `P` on `H d` (`P² ≤ 1`), one has
`Tr(P²) ≤ Tr(P)`.
-/
lemma trace_sq_le_of_psd_le_one (P : H d →L[ℂ] H d)
    (hPsa : adjoint P = P)
    (hPpos : ∀ v : H d, 0 ≤ (inner ℂ v (P v)).re)
    (hPle1 : ∀ v : H d, (inner ℂ v ((P ∘L P) v)).re ≤ ‖v‖ ^ 2) :
    (LinearMap.trace ℂ (H d) (P ∘L P).toLinearMap).re
      ≤ (LinearMap.trace ℂ (H d) P.toLinearMap).re := by
  have h_trace_le : ∀ (v : H d), ⟪v, P (P v)⟫.re ≤ ⟪v, v⟫.re := by
    convert hPle1 using 2 ; norm_num [ inner_self_eq_norm_sq_to_K ];
    norm_cast;
  have h_diag : ∃ b : OrthonormalBasis (Fin d) ℂ (H d), ∀ i : Fin d, P (b i) = (inner ℂ (b i) (P (b i))).re • b i := by
    have h_diag : ∀ (T : H d →ₗ[ℂ] H d), T.IsSymmetric → ∃ b : OrthonormalBasis (Fin d) ℂ (H d), ∀ i : Fin d, T (b i) = (inner ℂ (b i) (T (b i))).re • b i := by
      intro T hT_symm
      have h_diag : ∃ b : OrthonormalBasis (Fin d) ℂ (H d), ∀ i : Fin d, ∃ μ : ℂ, T (b i) = μ • b i := by
        have := @JointDiag.exists_orthonormalBasis_joint_eigenvector_symmetric;
        convert this ( fun _ => T ) ( fun _ => hT_symm ) ( fun _ _ _ => rfl ) using 1;
        any_goals exact Fin 1;
        · rw [ show Module.finrank ℂ ( H d ) = d from ?_ ];
          simp +decide [ H ];
        · simp +decide [];
          rw [ show Module.finrank ℂ ( H d ) = d from ?_ ];
          simp +decide [ H ];
        · infer_instance;
      obtain ⟨ b, hb ⟩ := h_diag; use b; intro i; obtain ⟨ μ, hμ ⟩ := hb i; simp_all +decide [] ;
      have := hT_symm ( b i ) ( b i ) ; simp_all +decide [ inner_smul_left, inner_smul_right ] ;
      simp_all +decide [ Complex.ext_iff ];
      rw [ show μ = μ.re by simpa [ Complex.ext_iff ] using by linarith ];
      norm_cast;
    convert h_diag P.toLinearMap _;
    intro x y; simp +decide [ ← ContinuousLinearMap.adjoint_inner_right, hPsa ] ;
  obtain ⟨b, hb⟩ := h_diag
  have h_trace_le : ∀ i : Fin d, (inner ℂ (b i) (P (P (b i)))).re ≤ (inner ℂ (b i) (P (b i))).re := by
    intro i
    have h_inner : ⟪b i, P (P (b i))⟫.re = (inner ℂ (b i) (P (b i))).re * (inner ℂ (b i) (P (b i))).re := by
      rw [ hb i ];
      simp +decide [];
    have := h_trace_le ( b i );
    have := b.orthonormal.1 i; norm_num at *; nlinarith [ hPpos ( b i ) ] ;
  have h_trace_le : (LinearMap.trace ℂ (H d) (P ∘L P).toLinearMap).re = ∑ i : Fin d, (inner ℂ (b i) (P (P (b i)))).re ∧ (LinearMap.trace ℂ (H d) P.toLinearMap).re = ∑ i : Fin d, (inner ℂ (b i) (P (b i))).re := by
    constructor <;> rw [ LinearMap.trace_eq_matrix_trace ℂ b.toBasis ];
    · simp +decide [ LinearMap.toMatrix_apply, Matrix.trace ];
      simp +decide [ OrthonormalBasis.repr_apply_apply ];
    · simp +decide [ LinearMap.toMatrix_apply, Matrix.trace ];
      simp +decide [ OrthonormalBasis.repr_apply_apply ];
  exact h_trace_le.1.symm ▸ h_trace_le.2.symm ▸ Finset.sum_le_sum fun i _ => by solve_by_elim;

/-
**Trace bound for the polar isometry.**  If `U` is an isometry onto `F K` (`Uᴴ U = 1`,
`U Uᴴ = F`, `F U = U`) such that `P := Uᴴ W` is positive semidefinite, then
`hsq (U − W) ≤ hsq (F − W Wᴴ)`.  Both sides expand as `2d − 2 Tr(P)` and `2d − 2 Tr(P²)`
respectively (note `P² = Wᴴ F W` because `U Uᴴ = F`), and `Tr(P²) ≤ Tr(P)` since `P` is a positive
contraction.
-/
lemma hsq_polar_bound
    (W : H d →L[ℂ] K) (hW : adjoint W ∘L W = 1)
    (F : K →L[ℂ] K) (hFsa : adjoint F = F) (hFidem : F ∘L F = F)
    (hFtr : LinearMap.trace ℂ K F.toLinearMap = (d : ℂ))
    (U : H d →L[ℂ] K)
    (hUU : adjoint U ∘L U = 1) (hUF : U ∘L adjoint U = F) (hFU : F ∘L U = U)
    (hPsa : adjoint (adjoint U ∘L W) = adjoint U ∘L W)
    (hPpos : ∀ v : H d, 0 ≤ (inner ℂ v ((adjoint U ∘L W) v)).re) :
    hsq (U - W) ≤ hsq (F - Eproj W) := by
  -- Apply `trace_sq_le_of_psd_le_one P hPsa hPpos hPle1` where `hPle1 : ∀ v, (inner ℂ v ((P ∘L P) v)).re ≤ ‖v‖^2` is proved as follows: since `P` is self-adjoint, `⟪v, (P∘LP) v⟫ = ⟪P v, P v⟫ = ‖P v‖²` (real, `inner_self_eq_norm_sq_to_K`); and `‖P v‖² = ⟪v, (Pᴴ ∘L P) v⟫ = ⟪v, (adjoint W ∘L (U ∘L adjoint U) ∘L W) v⟫ = ⟪v, (adjoint W ∘L F ∘L W) v⟫` (using `hUF : U ∘L adjoint U = F`) `= ⟪W v, F (W v)⟫ = ‖F (W v)‖²` (F self-adjoint idempotent) `≤ ‖W v‖² = ‖v‖²` (since `‖F‖ ≤ 1` as `F` is a projection, and `W` is an isometry: `‖W v‖ = ‖v‖` from `adjoint W ∘L W = 1`). This gives `htrace : (LinearMap.trace ℂ (H d) (P ∘L P).toLinearMap).re ≤ (LinearMap.trace ℂ (H d) P.toLinearMap).re`.
  have htrace : (LinearMap.trace ℂ (H d) ((adjoint U ∘L W) ∘L (adjoint U ∘L W)).toLinearMap).re ≤ (LinearMap.trace ℂ (H d) ((adjoint U ∘L W)).toLinearMap).re := by
    have hPle1 : ∀ v : H d, (inner ℂ v (((adjoint U ∘L W) ∘L (adjoint U ∘L W)) v)).re ≤ ‖v‖ ^ 2 := by
      intro v
      have hPv : ‖(adjoint U ∘L W) v‖ ^ 2 = ⟪v, ((adjoint U ∘L W) ∘L (adjoint U ∘L W)) v⟫.re := by
        have hPv : ‖(adjoint U ∘L W) v‖ ^ 2 = ⟪(adjoint U ∘L W) v, (adjoint U ∘L W) v⟫.re := by
          rw [ ← @inner_self_eq_norm_sq ℂ ] ; norm_num [ inner_self_eq_norm_sq_to_K ] ;
        rw [ hPv, ← ContinuousLinearMap.adjoint_inner_right ];
        rw [ hPsa ];
        rfl;
      have hPv_le : ‖(adjoint U ∘L W) v‖ ^ 2 ≤ ‖F (W v)‖ ^ 2 := by
        have hPv_le : ‖(adjoint U ∘L W) v‖ ^ 2 = ⟪W v, F (W v)⟫.re := by
          simp_all +decide [ ContinuousLinearMap.ext_iff ];
          grind +suggestions;
        have hPv_le : ⟪F (W v), F (W v)⟫ = ⟪W v, F (W v)⟫ := by
          rw [ ← ContinuousLinearMap.adjoint_inner_right, hFsa ];
          rw [ ← ContinuousLinearMap.comp_apply, hFidem ];
        simp_all +decide [ inner_self_eq_norm_sq_to_K ];
        norm_num [ ← hPv_le, sq ];
      have hF_le_one : ‖F‖ ≤ 1 := by
        apply opNorm_le_one_of_sa_idem F hFsa hFidem;
      have hW_le_one : ‖W v‖ ≤ ‖v‖ := by
        have := ContinuousLinearMap.adjoint_inner_right W v ( W v ) ; simp_all +decide [ inner_self_eq_norm_sq_to_K ] ;
        replace hW := congr_arg ( fun f => f v ) hW; simp_all +decide [ ContinuousLinearMap.ext_iff ] ;
        norm_cast at this; nlinarith [ norm_nonneg v, norm_nonneg ( W v ) ] ;
      exact hPv ▸ hPv_le.trans ( by exact le_trans ( pow_le_pow_left₀ ( norm_nonneg _ ) ( ContinuousLinearMap.le_opNorm F _ |> le_trans <| mul_le_of_le_one_left ( norm_nonneg _ ) hF_le_one ) _ ) ( pow_le_pow_left₀ ( norm_nonneg _ ) hW_le_one _ ) );
    apply_rules [ trace_sq_le_of_psd_le_one ];
  convert sub_le_sub_left ( mul_le_mul_of_nonneg_left htrace zero_le_two ) ( 2 * d : ℝ ) using 1;
  · have h_expand : hsq (U - W) = (LinearMap.trace ℂ (H d) ((adjoint U - adjoint W) ∘L (U - W)).toLinearMap).re := by
      simp +decide [ hsq, ContinuousLinearMap.adjoint ];
    simp_all +decide [ ContinuousLinearMap.comp_apply ];
    erw [ LinearMap.trace_id ] ; norm_num ; ring;
  · have h_expand : hsq (F - Eproj W) = (LinearMap.trace ℂ K (F ∘L F).toLinearMap).re - 2 * (LinearMap.trace ℂ K (F ∘L Eproj W).toLinearMap).re + (LinearMap.trace ℂ K (Eproj W ∘L Eproj W).toLinearMap).re := by
      unfold hsq; simp +decide [ hFsa, hFidem ] ; ring;
      rw [ show ( adjoint ( Eproj W ) : K →L[ℂ] K ) = Eproj W from Eproj_selfadjoint W ] ; ring;
      rw [ show ( LinearMap.trace ℂ K ) ( ( Eproj W : K →ₗ[ℂ] K ) ∘ₗ F ) = ( LinearMap.trace ℂ K ) ( F ∘ₗ ( Eproj W : K →ₗ[ℂ] K ) ) from ?_ ] ; ring;
      convert LinearMap.trace_mul_comm ℂ ( Eproj W |> ContinuousLinearMap.toLinearMap ) ( F |> ContinuousLinearMap.toLinearMap ) using 1;
    have h_trace_F : (LinearMap.trace ℂ K (F ∘L Eproj W).toLinearMap).re = (LinearMap.trace ℂ (H d) ((adjoint U ∘L W) ∘L (adjoint U ∘L W)).toLinearMap).re := by
      rw [ ← hUF ];
      convert congr_arg Complex.re ( trace_comp_comm_HK ( U : H d →L[ℂ] K ) ( adjoint U ∘L W ∘L adjoint W ) ) using 1;
      congr! 2;
      ext; simp +decide [] ;
      replace hPsa := congr_arg ( fun f => f ‹_› ) hPsa; aesop;
    have h_trace_Eproj : (LinearMap.trace ℂ K (Eproj W ∘L Eproj W).toLinearMap).re = d := by
      convert congr_arg Complex.re ( HSLemma2.trace_Eproj W hW ) using 1;
      rw [ HSLemma2.Eproj_idem W hW ];
    simp_all +decide [ Eproj ];
    ring

/-- **Polar rounding into a rank-`d` invariant plane.**  Let `W : ℂ^d → K` be an isometry and let
`F` be a rank-`d` orthogonal projection on `K`.  Then there is an isometry `U : ℂ^d → K` with
range exactly `F K` (so `U Uᴴ = F` and `F U = U`) such that
`hsq (U − W) ≤ hsq (F − W Wᴴ)`. -/
lemma exists_isometry_polar_near
    (W : H d →L[ℂ] K) (hW : adjoint W ∘L W = 1)
    (F : K →L[ℂ] K) (hFsa : adjoint F = F) (hFidem : F ∘L F = F)
    (hFtr : LinearMap.trace ℂ K F.toLinearMap = (d : ℂ)) :
    ∃ U : H d →L[ℂ] K,
      adjoint U ∘L U = 1 ∧ U ∘L adjoint U = F ∧ F ∘L U = U ∧
      hsq (U - W) ≤ hsq (F - Eproj W) := by
  obtain ⟨U, hUU, hUF, hFU, hPsa, hPpos⟩ :=
    exists_polar_isometry W F hFsa hFidem hFtr
  exact ⟨U, hUU, hUF, hFU,
    hsq_polar_bound W hW F hFsa hFidem hFtr U hUU hUF hFU hPsa hPpos⟩

end HSLemma2

end