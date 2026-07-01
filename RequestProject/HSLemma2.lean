import Mathlib
import RequestProject.HSMaps
import RequestProject.JointDiag

/-!
# Lemma 2 of the note: rounding an almost-invariant `d`-plane

This file works toward **Lemma 2** of `gh_hs_projection_note_revised-1.pdf`: given a finite abelian
group `G`, a finite-dimensional unitary representation `π : G → U(K)`, an isometry `W : H d → K`,
and a map `f : G → U(H d)` with `‖π(x)W − W f(x)‖₂,d ≤ δ` for all `x`, there is a genuine unitary
representation `σ : G → U(H d)` with `‖f(x) − σ(x)‖₂,d ≤ 5δ`.

The construction averages the rank-`d` projection `E = W Wᴴ` over the representation to get
`M = 𝔼ₓ π(x)ᴴ E π(x)`, a positive contraction commuting with `π`, takes the rank-`d` spectral
projection `F` onto the top eigenvalues of `M` (invariant under `π`), polar-rounds `F W` to an
isometry `U : H d → F K`, and sets `σ(x) = Uᴴ π(x) U`.

This file currently develops the **analytic core** (the bound `hsq (E − M) ≤ δ²·d`, the note's
estimate `(1/d)‖E − M‖²_HS ≤ δ²`) and the standalone combinatorial inequality underlying the
Ky-Fan nearest-projection step.
-/

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ComplexInnerProductSpace
open Finset HSMaps
open ContinuousLinearMap (adjoint)

namespace HSLemma2

variable {d : ℕ}
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
variable {G : Type} [CommGroup G] [Fintype G] [DecidableEq G]

/-! ### Definitions -/

/-- The rank-`d` projection `E = W Wᴴ` onto `W H`. -/
def Eproj (W : H d →L[ℂ] K) : K →L[ℂ] K := W ∘L adjoint W

/-- The averaging operator `𝔼ₓ π(x)ᴴ X π(x)` over the representation. -/
def avgOp (π : G →* (K →L[ℂ] K)) (X : K →L[ℂ] K) : K →L[ℂ] K :=
  ((Fintype.card G : ℂ))⁻¹ • ∑ x : G, (adjoint (π x)) ∘L (X ∘L π x)

/-- The averaged projection `M = 𝔼ₓ π(x)ᴴ E π(x)`. -/
def Mavg (π : G →* (K →L[ℂ] K)) (W : H d →L[ℂ] K) : K →L[ℂ] K := avgOp π (Eproj W)

/-! ### Phase A: basic algebraic facts -/

/-
A self-adjoint idempotent continuous linear map has operator norm `≤ 1`.
-/
lemma opNorm_le_one_of_sa_idem (E : K →L[ℂ] K) (h1 : adjoint E = E) (h2 : E ∘L E = E) :
    ‖E‖ ≤ 1 := by
  refine' ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => _;
  have h_norm_sq : ‖E x‖ ^ 2 = inner ℂ (E x) x := by
    have h_norm_sq : inner ℂ (E x) (E x) = inner ℂ (E x) x := by
      grind +suggestions;
    simp +decide [ ← h_norm_sq, inner_self_eq_norm_sq_to_K ];
  have h_cauchy_schwarz : ‖E x‖ ^ 2 ≤ ‖E x‖ * ‖x‖ := by
    have h_cauchy_schwarz : ‖inner ℂ (E x) x‖ ≤ ‖E x‖ * ‖x‖ := by
      exact norm_inner_le_norm _ _;
    convert h_cauchy_schwarz using 1 ; norm_num [ ← h_norm_sq ];
  nlinarith [ norm_nonneg x ]

omit [DecidableEq G] in
omit [Fintype G] in
/-
The adjoint of a unitary in the representation is the value at the inverse.
-/
lemma pi_adjoint (π : G →* (K →L[ℂ] K)) (hπ : ∀ g, π g ∈ unitary (K →L[ℂ] K)) (x : G) :
    adjoint (π x) = π x⁻¹ := by
  have := hπ x |>.1;
  have h_inv : (adjoint (π x)) * (π x) = 1 ∧ (π x) * (adjoint (π x)) = 1 := by
    have := hπ x |>.2;
    exact ⟨ by simpa [ ContinuousLinearMap.star_eq_adjoint ] using ‹star ( π x ) * π x = 1›, by simpa [ ContinuousLinearMap.star_eq_adjoint ] using ‹π x * star ( π x ) = 1› ⟩;
  have h_inv : (adjoint (π x)) = (π x⁻¹) := by
    have h_inv : (adjoint (π x)) * (π x) = 1 ∧ (π x) * (adjoint (π x)) = 1 := h_inv
    have h_inv' : (π x⁻¹) * (π x) = 1 ∧ (π x) * (π x⁻¹) = 1 := by
      simp +decide [ ← map_mul ]
    grind +suggestions;
  exact h_inv

lemma Eproj_selfadjoint (W : H d →L[ℂ] K) : adjoint (Eproj W) = Eproj W := by
  ext;
  refine' ext_inner_right ℂ _;
  simp +decide [ Eproj, ContinuousLinearMap.adjoint ];
  intro v; rw [ ← ContinuousLinearMap.adjoint_inner_right ] ; simp +decide [ ContinuousLinearMap.adjoint ] ;

lemma Eproj_idem (W : H d →L[ℂ] K) (hW : adjoint W ∘L W = 1) :
    Eproj W ∘L Eproj W = Eproj W := by
  unfold Eproj;
  simp_all +decide [ ContinuousLinearMap.ext_iff ]

lemma Eproj_comp_W (W : H d →L[ℂ] K) (hW : adjoint W ∘L W = 1) :
    Eproj W ∘L W = W := by
  convert congr_arg ( fun f => W ∘L f ) hW using 1

/-
`Tr E = d`.
-/
lemma trace_Eproj (W : H d →L[ℂ] K) (hW : adjoint W ∘L W = 1) :
    LinearMap.trace ℂ K (Eproj W).toLinearMap = (d : ℂ) := by
  have h_trace : (LinearMap.trace ℂ K (Eproj W)) = ∑ j : Fin (Module.finrank ℂ K), ‖(adjoint W) (OrthonormalBasis.toBasis (stdOrthonormalBasis ℂ K) j)‖ ^ 2 := by
    convert LinearMap.trace_eq_matrix_trace ℂ ( stdOrthonormalBasis ℂ K |> OrthonormalBasis.toBasis ) ( Eproj W |> ContinuousLinearMap.toLinearMap ) using 1;
    simp +decide [ LinearMap.toMatrix_apply, Matrix.trace ];
    refine' Finset.sum_congr rfl fun i _ => _;
    convert ( inner_self_eq_norm_sq_to_K _ ) |> Eq.symm using 1;
    convert rfl;
    convert ( stdOrthonormalBasis ℂ K ).repr_apply_apply ( W ( adjoint W ( stdOrthonormalBasis ℂ K i ) ) ) i using 1;
    rw [ ContinuousLinearMap.adjoint_inner_left ];
  have h_trace_eq : ∑ j : Fin (Module.finrank ℂ K), ‖(adjoint W) (OrthonormalBasis.toBasis (stdOrthonormalBasis ℂ K) j)‖ ^ 2 = hsq W := by
    rw [ ← hsq_adjoint ];
    convert hsq_eq_sum ( stdOrthonormalBasis ℂ K ) ( adjoint W ) |> Eq.symm using 1;
  convert h_trace using 1;
  rw [ h_trace_eq, hsq_single ];
  have h_norm : ∀ v : H d, ‖W v‖ = ‖v‖ := by
    intro v
    have h_norm : ‖W v‖ ^ 2 = ‖v‖ ^ 2 := by
      have := ContinuousLinearMap.adjoint_inner_right W v ( W v );
      replace hW := congr_arg ( fun f => f v ) hW; simp_all +decide [ inner_self_eq_norm_sq_to_K ] ;
      norm_cast at this; rw [ ← sq_eq_sq₀ ( norm_nonneg _ ) ( norm_nonneg _ ), this ] ;
    rwa [ sq_eq_sq₀ ( norm_nonneg _ ) ( norm_nonneg _ ) ] at h_norm;
  simp +decide [ h_norm, EuclideanSpace.norm_eq ];
  rw [ Finset.sum_congr rfl fun i _ => by rw [ Finset.sum_eq_single i ] <;> aesop ] ; simp +decide

/-! ### Phase B: the averaging operator and the analytic bound -/

lemma Mavg_selfadjoint (π : G →* (K →L[ℂ] K))
    (W : H d →L[ℂ] K) : adjoint (Mavg π W) = Mavg π W := by
  have h_avg_selfadjoint : ∀ x : G, adjoint ((adjoint (π x)) ∘L (Eproj W ∘L π x)) = (adjoint (π x)) ∘L (Eproj W ∘L π x) := by
    grind +suggestions;
  unfold Mavg; simp +decide [ *, avgOp ] ;
  -- Apply the linearity of the adjoint to pull the scalar multiplication out.
  have h_adj_linear : ∀ (c : ℂ) (T : K →L[ℂ] K), adjoint (c • T) = (starRingEnd ℂ c) • adjoint T := by
    simp +decide [ adjoint ];
  induction' ( Finset.univ : Finset G ) using Finset.induction <;> simp_all +decide [ Finset.sum_insert ]

omit [DecidableEq G] in
/-
`M` commutes with each `π y`.
-/
lemma Mavg_commute (π : G →* (K →L[ℂ] K)) (hπ : ∀ g, π g ∈ unitary (K →L[ℂ] K))
    (W : H d →L[ℂ] K) (y : G) : π y ∘L Mavg π W = Mavg π W ∘L π y := by
  refine' ContinuousLinearMap.ext fun x => _;
  unfold Mavg; simp +decide [] ;
  apply Eq.symm; exact (by
    have h_sum : ∑ x_1 : G, (π x_1⁻¹) ((Eproj W) ((π (x_1 * y)) x)) = ∑ x_1 : G, (π (x_1 * y⁻¹)⁻¹) ((Eproj W) ((π x_1) x)) := by
      apply Finset.sum_bij (fun x_1 _ => x_1 * y);
      · simp +decide;
      · aesop;
      · exact fun b _ => ⟨ b * y⁻¹, Finset.mem_univ _, by simp +decide ⟩;
      · simp +decide [ mul_assoc ]
    unfold avgOp; simp +decide [] ;
    convert h_sum using 2 <;> simp +decide [ Eproj, pi_adjoint π hπ ])

omit [DecidableEq G] in
/-
The key trace identity `Tr(M²) = Tr(E M)`.
-/
lemma trace_Msq_eq_EM (π : G →* (K →L[ℂ] K)) (hπ : ∀ g, π g ∈ unitary (K →L[ℂ] K))
    (W : H d →L[ℂ] K) :
    LinearMap.trace ℂ K (Mavg π W ∘L Mavg π W).toLinearMap
      = LinearMap.trace ℂ K (Eproj W ∘L Mavg π W).toLinearMap := by
  have h_trace_eq : ∀ x : G, (LinearMap.trace ℂ K) ((Mavg π W).comp ((adjoint (π x)) ∘L (Eproj W ∘L π x))).toLinearMap = (LinearMap.trace ℂ K) ((Mavg π W).comp (Eproj W)).toLinearMap := by
    intro x
    have h_trace_eq : (LinearMap.trace ℂ K) ((π x ∘L (Mavg π W) ∘L (adjoint (π x))).comp (Eproj W)).toLinearMap = (LinearMap.trace ℂ K) ((Mavg π W).comp (Eproj W)).toLinearMap := by
      have h_trace_eq : (π x ∘L (Mavg π W) ∘L (adjoint (π x))) = (Mavg π W).comp (π x ∘L (adjoint (π x))) := by
        have := Mavg_commute π hπ W x;
        simp_all +decide [ ContinuousLinearMap.ext_iff ];
      have h_trace_eq : (π x).comp (adjoint (π x)) = 1 := by
        grind +suggestions;
      aesop;
    have h_trace_eq : (LinearMap.trace ℂ K) ((π x ∘L (Mavg π W) ∘L (adjoint (π x))).comp (Eproj W)).toLinearMap = (LinearMap.trace ℂ K) ((Mavg π W).comp ((adjoint (π x)) ∘L (Eproj W ∘L π x))).toLinearMap := by
      convert LinearMap.trace_mul_comm ( R := ℂ ) ( ( π x ).toLinearMap ) ( ( Mavg π W ).toLinearMap * ( adjoint ( π x ) ).toLinearMap * ( Eproj W ).toLinearMap ) using 1;
    grind;
  convert congr_arg ( fun x : ℂ => ( Fintype.card G : ℂ ) ⁻¹ * x ) ( Finset.sum_congr rfl fun x ( hx : x ∈ Finset.univ ) => h_trace_eq x ) using 1;
  · simp +decide [ Finset.mul_sum _ _ _, Mavg, avgOp ];
    simp +decide only [inv_mul_eq_div];
    simp +decide only [div_div, ← sum_div];
    congr! 1;
    rw [ ← map_sum ];
    exact congr_arg _ ( by ext; simp +decide [ Finset.sum_apply, LinearMap.comp_apply ] );
  · simp +decide [ Mavg, avgOp ];
    convert LinearMap.trace_mul_comm ℂ _ _ using 1

/-
The Frobenius expansion `hsq (E − M) = d − Re Tr(E M)`.
-/
lemma hsq_Eproj_sub_Mavg_eq (π : G →* (K →L[ℂ] K)) (hπ : ∀ g, π g ∈ unitary (K →L[ℂ] K))
    (W : H d →L[ℂ] K) (hW : adjoint W ∘L W = 1) :
    hsq (Eproj W - Mavg π W)
      = (d : ℝ) - (LinearMap.trace ℂ K (Eproj W ∘L Mavg π W).toLinearMap).re := by
  convert congr_arg Complex.re ?_ using 1;
  rotate_left;
  exact ( LinearMap.trace ℂ K ) ( ( Eproj W - Mavg π W ) ∘L ( Eproj W - Mavg π W ) |> ContinuousLinearMap.toLinearMap );
  · rw [ show adjoint ( Eproj W - Mavg π W ) = Eproj W - Mavg π W from ?_ ];
    convert congr_arg₂ ( fun x y => x - y ) ( Eproj_selfadjoint W ) ( Mavg_selfadjoint π W ) using 1;
    ext; simp +decide [ ContinuousLinearMap.adjoint ] ;
  · have h_trace : (LinearMap.trace ℂ K (Eproj W ∘L Eproj W).toLinearMap).re = d := by
      rw [ Eproj_idem W hW ];
      convert congr_arg Complex.re ( trace_Eproj W hW ) using 1;
    have h_trace : (LinearMap.trace ℂ K (Mavg π W ∘L Mavg π W).toLinearMap).re = (LinearMap.trace ℂ K (Eproj W ∘L Mavg π W).toLinearMap).re := by
      convert congr_arg Complex.re ( trace_Msq_eq_EM π hπ W ) using 1;
    have h_trace : (LinearMap.trace ℂ K (Eproj W ∘L Mavg π W).toLinearMap).re = (LinearMap.trace ℂ K (Mavg π W ∘L Eproj W).toLinearMap).re := by
      convert congr_arg Complex.re ( LinearMap.trace_mul_comm ℂ ( Eproj W |> ContinuousLinearMap.toLinearMap ) ( Mavg π W |> ContinuousLinearMap.toLinearMap ) ) using 1;
    simp_all +decide [ ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp ]

/-
The averaging identity `d − Re Tr(E M) = 𝔼ₓ ‖(1 − E) π(x) W‖²_HS`.
-/
lemma trace_EM_avg_identity (π : G →* (K →L[ℂ] K)) (hπ : ∀ g, π g ∈ unitary (K →L[ℂ] K))
    (W : H d →L[ℂ] K) (hW : adjoint W ∘L W = 1) :
    (d : ℝ) - (LinearMap.trace ℂ K (Eproj W ∘L Mavg π W).toLinearMap).re
      = (Fintype.card G : ℝ)⁻¹ *
        ∑ x : G, hsq ((1 - Eproj W) ∘L (π x ∘L W)) := by
  have h_avg : (1 / (Fintype.card G : ℝ)) * ∑ x : G, hsq ((1 - Eproj W) ∘L (π x ∘L W)) = (LinearMap.trace ℂ (H d) (1 - (adjoint W ∘L Mavg π W ∘L W).toLinearMap)).re := by
    have h_avg : ∀ x : G, hsq ((1 - Eproj W) ∘L (π x ∘L W)) = (LinearMap.trace ℂ (H d) ((adjoint W) ∘L ((adjoint (π x) ∘L ((1 - Eproj W) ∘L π x)) ∘L W)).toLinearMap).re := by
      intro x;
      unfold hsq;
      congr 2;
      ext; simp +decide [ ContinuousLinearMap.one_apply ] ;
      simp +decide [ Eproj ];
      simp +decide [ show adjoint ( 1 : K →L[ℂ] K ) = 1 from ContinuousLinearMap.adjoint_id ];
      simp_all +decide [ ContinuousLinearMap.ext_iff ];
    have h_avg : ∑ x : G, (LinearMap.trace ℂ (H d) ((adjoint W) ∘L ((adjoint (π x) ∘L ((1 - Eproj W) ∘L π x)) ∘L W)).toLinearMap) = (Fintype.card G : ℂ) • (LinearMap.trace ℂ (H d) ((adjoint W) ∘L ((1 - Mavg π W) ∘L W)).toLinearMap) := by
      have h_avg : ∑ x : G, (adjoint (π x) ∘L ((1 - Eproj W) ∘L π x)) = (Fintype.card G : ℂ) • (1 - Mavg π W) := by
        have h_avg : ∑ x : G, (adjoint (π x) ∘L (1 ∘L π x)) = (Fintype.card G : ℂ) • 1 := by
          have h_avg : ∀ x : G, (adjoint (π x) ∘L (1 ∘L π x)) = 1 := by
            intro x
            have h_unitary : adjoint (π x) ∘L π x = 1 := by
              have := hπ x;
              exact this.1
            exact h_unitary;
          simp +decide [ h_avg ];
          norm_num [ Algebra.smul_def ];
        simp_all +decide [ Mavg, avgOp ];
        simp +decide [ smul_sub ];
      convert congr_arg ( fun f : K →L[ℂ] K => ( LinearMap.trace ℂ ( H d ) ) ( ( adjoint W ).comp ( f.comp W ) |> ContinuousLinearMap.toLinearMap ) ) h_avg using 1;
      · simp +decide [];
        congr! 1;
        · induction' ( Finset.univ : Finset G ) using Finset.induction <;> simp_all +decide [ Finset.sum_insert ];
          simp +decide [ LinearMap.comp_add, LinearMap.add_comp ];
        · induction' ( Finset.univ : Finset G ) using Finset.induction <;> simp_all +decide [ Finset.sum_insert ];
          simp +decide [ LinearMap.comp_add, LinearMap.add_comp ];
      · simp +decide [];
    simp_all +decide [ Complex.ext_iff ];
    convert congr_arg Complex.re ( trace_Eproj W hW ) using 1;
    convert LinearMap.trace_comp_comm' _ _ |> congr_arg Complex.re using 1; all_goals infer_instance;
  have h_trace_cycle : LinearMap.trace ℂ (H d) (adjoint W ∘L Mavg π W ∘L W).toLinearMap = LinearMap.trace ℂ K (Mavg π W ∘L W ∘L adjoint W).toLinearMap := by
    convert LinearMap.trace_comp_comm' _ _ using 1; all_goals infer_instance;
  simp_all +decide [ Eproj, Mavg, avgOp ];
  convert rfl using 2;
  convert LinearMap.trace_mul_comm ℂ _ _ using 2

/-
Per-element bound: `‖(1 − E) π(x) W‖²_HS ≤ ‖π(x)W − W f(x)‖²_HS`.
-/
omit [Fintype G] [DecidableEq G] in
lemma hsq_one_sub_E_le (π : G →* (K →L[ℂ] K))
    (W : H d →L[ℂ] K) (hW : adjoint W ∘L W = 1) (S : H d →L[ℂ] H d) (x : G) :
    hsq ((1 - Eproj W) ∘L (π x ∘L W)) ≤ hsq (π x ∘L W - W ∘L S) := by
  convert pow_le_pow_left₀ ( by exact HSMaps.hsF_nonneg _ ) ( HSMaps.hsF_comp_left_le ( ( 1:K →L[ℂ] K ) - Eproj W ) ?_ ( ( π x ).comp W - W.comp S ) ) 2 using 1 <;> norm_num [ ← sq, HSMaps.hsF ];
  · rw [ Real.sq_sqrt ( HSMaps.hsq_nonneg _ ) ];
    simp +decide [ ← ContinuousLinearMap.comp_assoc, Eproj_comp_W, hW ];
    convert rfl using 2 ; ext ; simp +decide [ Eproj ];
  · rw [ Real.sq_sqrt ( HSMaps.hsq_nonneg _ ) ];
  · apply_rules [ opNorm_le_one_of_sa_idem ];
    · simp +decide [ Eproj_selfadjoint ];
      exact ContinuousLinearMap.adjoint_id;
    · simp +decide [ Eproj_idem W hW ];
      ext; simp +decide [ Eproj ] ;

/-
**The analytic core of Lemma 2**: `hsq (E − M) ≤ δ²·d`, i.e. `(1/d)‖E − M‖²_HS ≤ δ²`.
-/
lemma hsq_Eproj_sub_Mavg_le (π : G →* (K →L[ℂ] K)) (hπ : ∀ g, π g ∈ unitary (K →L[ℂ] K))
    (W : H d →L[ℂ] K) (hW : adjoint W ∘L W = 1) (f : G → (H d →L[ℂ] H d))
    (δ : ℝ)
    (hbound : ∀ x, hsq (π x ∘L W - W ∘L (f x)) ≤ δ ^ 2 * d) :
    hsq (Eproj W - Mavg π W) ≤ δ ^ 2 * d := by
  rw [ hsq_Eproj_sub_Mavg_eq, trace_EM_avg_identity ];
  · rw [ inv_mul_le_iff₀ ( Nat.cast_pos.mpr Fintype.card_pos ) ];
    exact le_trans ( Finset.sum_le_sum fun _ _ => hsq_one_sub_E_le _ _ hW _ _ ) ( by simpa using Finset.sum_le_sum fun x ( hx : x ∈ Finset.univ ) => hbound x );
  · exact hπ;
  · exact hW;
  · exact hπ;
  · exact hW

/-! ### The combinatorial Ky-Fan inequality (standalone, over `ℝ`) -/

/-
**Fractional knapsack / Ky-Fan inequality.**  Given real "eigenvalues" `μ : Fin n → ℝ` and a
target rank `d ≤ n`, there is a `d`-element index set `S` (the indices of the `d` largest `μ`)
such that for every "occupation" vector `p` with `0 ≤ pₖ ≤ 1` and `∑ pₖ = d`, one has
`∑ₖ μₖ pₖ ≤ ∑_{k∈S} μₖ`.  This is the inequality `Tr(M P) ≤ Tr(M F)` underlying the choice of the
nearest rank-`d` spectral projection `F`.
-/
lemma knapsack_top {n : ℕ} (μ : Fin n → ℝ) (d : ℕ) (hd : d ≤ n) :
    ∃ S : Finset (Fin n), S.card = d ∧
      ∀ p : Fin n → ℝ, (∀ k, 0 ≤ p k) → (∀ k, p k ≤ 1) → (∑ k, p k = (d : ℝ)) →
        ∑ k, μ k * p k ≤ ∑ k ∈ S, μ k := by
  by_cases h : d = 0;
  · use ∅; simp [h];
    intro p hp₁ hp₂ hp₃; rw [ Finset.sum_eq_zero_iff_of_nonneg ] at hp₃ <;> aesop;
  · -- Since the collection of `d`-element subsets of `Fin n` is finite and nonempty (as `d ≤ n`), choose `S` with `S.card = d` maximizing `∑ k ∈ S, μ k`.
    obtain ⟨S, hS_card, hS_max⟩ : ∃ S : Finset (Fin n), S.card = d ∧ ∀ T : Finset (Fin n), T.card = d → ∑ k ∈ T, μ k ≤ ∑ k ∈ S, μ k := by
      have h_finite : Finset.Nonempty (Finset.powersetCard d (Finset.univ : Finset (Fin n))) := by
        exact Finset.card_pos.mp ( by simpa using Nat.choose_pos hd );
      have := Finset.exists_max_image ( Finset.powersetCard d Finset.univ ) ( fun T => ∑ k ∈ T, μ k ) h_finite; aesop;
    -- Let `θ` be the minimum of `μ` over `S`.
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, ∀ k ∈ S, θ ≤ μ k ∧ ∀ k ∉ S, μ k ≤ θ := by
      use sInf (μ '' S);
      refine' fun k hk => ⟨ csInf_le _ <| Set.mem_image_of_mem _ hk, fun k hk => le_csInf _ _ ⟩ <;> norm_num;
      · exact Set.Finite.bddBelow <| Set.toFinite _;
      · exact ⟨ _, ‹_› ⟩;
      · contrapose! hS_max;
        obtain ⟨ a, ha₁, ha₂ ⟩ := hS_max; use Insert.insert k ( S.erase a ) ; simp_all +decide [ Finset.card_insert_of_notMem, Finset.sum_insert ] ;
        exact ⟨ Nat.succ_pred_eq_of_pos ( Nat.pos_of_ne_zero h ), by linarith ⟩;
    refine' ⟨ S, hS_card, fun p hp₁ hp₂ hp₃ => _ ⟩;
    have h_sum : ∑ k, μ k * p k - ∑ k ∈ S, μ k ≤ θ * (∑ k ∈ S, (p k - 1) + ∑ k ∉ S, p k) := by
      have h_sum : ∑ k, μ k * p k - ∑ k ∈ S, μ k = ∑ k ∈ S, μ k * (p k - 1) + ∑ k ∉ S, μ k * p k := by
        simp +decide [ mul_sub, Finset.compl_eq_univ_sdiff ];
      rw [ h_sum, mul_add, Finset.mul_sum _ _ _, Finset.mul_sum _ _ _ ];
      exact add_le_add ( Finset.sum_le_sum fun i hi => by nlinarith only [ hθ i hi, hp₁ i, hp₂ i ] ) ( Finset.sum_le_sum fun i hi => by nlinarith only [ hθ ( Classical.choose ( Finset.card_pos.mp ( by linarith [ Nat.pos_of_ne_zero h ] ) ) ) ( Classical.choose_spec ( Finset.card_pos.mp ( by linarith [ Nat.pos_of_ne_zero h ] ) ) ) |>.2 i ( by aesop ), hp₁ i, hp₂ i ] );
    simp_all +decide [ Finset.compl_eq_univ_sdiff ]

end HSLemma2

end