import Mathlib
import RequestProject.HSNorm

/-!
# Reflections and the η-representation

Given projections `P i` we form the reflections `Uᵢ = 1 - 2 Pᵢ`, which are self-adjoint
unitaries, and the map `f(x) = ∏ᵢ Uᵢ^{xᵢ}` (ordered product) for `x ∈ (ℤ/2ℤ)ᴺ`.  The main
result of this file is that `f` is an `η`-representation with `η = 2N(N−1)ε`, where `ε` bounds
the commutators `‖[Pᵢ,Pⱼ]‖₂,d`.  This is the "swap-counting" estimate of the note (§4).

Here products are taken in the ring `H d →L[ℂ] H d`, where multiplication `*` is composition.
-/

noncomputable section

open scoped BigOperators
open Finset

variable {d : ℕ}

/-- `*`-phrased left unitary invariance (composition is `*`). -/
lemma hsNorm_mul_left_unitary {U A : H d →L[ℂ] H d} (hU : U ∈ unitary (H d →L[ℂ] H d)) :
    hsNorm (U * A) = hsNorm A := hsNorm_left_unitary hU A

/-- `*`-phrased right unitary invariance (composition is `*`). -/
lemma hsNorm_mul_right_unitary {U A : H d →L[ℂ] H d} (hU : U ∈ unitary (H d →L[ℂ] H d)) :
    hsNorm (A * U) = hsNorm A := hsNorm_right_unitary hU A

/-- Self-adjoint idempotent (orthogonal projection) as a continuous linear map. -/
def IsProjCLM (Q : H d →L[ℂ] H d) : Prop :=
  ContinuousLinearMap.adjoint Q = Q ∧ Q * Q = Q

/-- The reflection `1 - 2P` associated to a projection `P`. -/
def reflOp (P : H d →L[ℂ] H d) : H d →L[ℂ] H d := 1 - (2 : ℂ) • P

lemma reflOp_adjoint {P : H d →L[ℂ] H d} (hP : IsProjCLM P) :
    ContinuousLinearMap.adjoint (reflOp P) = reflOp P := by
  unfold reflOp; simp +decide [] ;
  congr;
  · exact ContinuousLinearMap.adjoint_id;
  · convert congr_arg ( fun x => 2 • x ) hP.1 using 1;
    · ext; simp [ContinuousLinearMap.adjoint];
      exact Or.inl <| by norm_num [ Complex.ext_iff ] ;
    · module

lemma reflOp_mul_self {P : H d →L[ℂ] H d} (hP : IsProjCLM P) :
    (reflOp P) * (reflOp P) = 1 := by
  ext x;
  simp [reflOp ];
  rw [ show P ( P x ) = P x from by simpa using congr_arg ( fun f => f x ) hP.2 ] ; ring

lemma reflOp_unitary {P : H d →L[ℂ] H d} (hP : IsProjCLM P) :
    reflOp P ∈ unitary (H d →L[ℂ] H d) := by
  constructor;
  · convert reflOp_mul_self hP using 1;
    convert ( congr_arg ( fun x => x * reflOp P ) ( reflOp_adjoint hP ) ) using 1;
  · convert reflOp_mul_self hP using 1;
    exact congr_arg _ ( reflOp_adjoint hP )

/-
The commutator of two reflections is `4` times the commutator of the projections.
-/
lemma comm_reflOp (P Q : H d →L[ℂ] H d) :
    (reflOp P) * (reflOp Q) - (reflOp Q) * (reflOp P)
      = (4 : ℂ) • ((P * Q) - (Q * P)) := by
  ext x; simp +decide [ reflOp ] ; ring;

/-
HS-norm bound on the commutator of reflections.
-/
lemma hsNorm_comm_reflOp (P Q : H d →L[ℂ] H d) (ε : ℝ)
    (h : hsNorm ((P * Q) - (Q * P)) ≤ ε) :
    hsNorm ((reflOp P) * (reflOp Q) - (reflOp Q) * (reflOp P)) ≤ 4 * ε := by
  rw [ comm_reflOp ];
  convert mul_le_mul_of_nonneg_left h zero_le_four using 1;
  convert hsNorm_smul ( 4 : ℂ ) ( P * Q - Q * P ) using 1;
  norm_num [ Norm.norm ]

/-! ### Telescoping: commuting a unitary past a finite product -/

/-
A product of unitaries is unitary.
-/
lemma listprod_unitary (L : List (H d →L[ℂ] H d))
    (hL : ∀ V ∈ L, V ∈ unitary (H d →L[ℂ] H d)) :
    L.prod ∈ unitary (H d →L[ℂ] H d) := by
  convert Submonoid.list_prod_mem _ _;
  assumption

/-
Commutator of a unitary `U` with a product of unitaries is controlled by the sum of the
individual commutators.
-/
lemma hsNorm_comm_listprod (U : H d →L[ℂ] H d)
    (hU : U ∈ unitary (H d →L[ℂ] H d))
    (L : List (H d →L[ℂ] H d)) (hL : ∀ V ∈ L, V ∈ unitary (H d →L[ℂ] H d)) :
    hsNorm (U * L.prod - L.prod * U)
      ≤ (L.map (fun V => hsNorm (U * V - V * U))).sum := by
  induction' L with V L ih generalizing U;
  · simp +decide [ hsNorm ];
    simp [hsVec];
    simp +decide [ Norm.norm ];
  · simp_all +decide [ mul_assoc ];
    have h_triangle : hsNorm (U * (V * L.prod) - V * (L.prod * U)) ≤ hsNorm ((U * V - V * U) * L.prod) + hsNorm (V * (U * L.prod - L.prod * U)) := by
      convert hsNorm_triangle _ _ using 2 ; simp +decide [ mul_assoc, sub_mul, mul_sub ];
    refine le_trans h_triangle ?_;
    refine' add_le_add _ _;
    · have h_unitary : L.prod ∈ unitary (H d →L[ℂ] H d) := by
        exact listprod_unitary _ hL.2;
      convert hsNorm_right_unitary h_unitary ( U * V - V * U ) |> le_of_eq using 1;
    · convert hsNorm_left_unitary hL.1 ( U * L.prod - L.prod * U ) |> le_of_eq |> le_trans <| ih U hU using 1

/-! ### The map `f` -/

/-- `f(x) = ∏ᵢ Uᵢ^{xᵢ}`, the ordered product of reflections. -/
def fCLM {N : ℕ} (P : Fin N → (H d →L[ℂ] H d)) (x : Fin N → ZMod 2) : H d →L[ℂ] H d :=
  (List.ofFn (fun i => (reflOp (P i)) ^ ((x i).val))).prod

lemma fCLM_unitary {N : ℕ} (P : Fin N → (H d →L[ℂ] H d)) (hP : ∀ i, IsProjCLM (P i))
    (x : Fin N → ZMod 2) : fCLM P x ∈ unitary (H d →L[ℂ] H d) := by
  apply listprod_unitary;
  intro V hV
  obtain ⟨i, hi⟩ : ∃ i : Fin N, V = (reflOp (P i)) ^ ((x i).val) := by
    rw [ List.mem_ofFn ] at hV; obtain ⟨ i, rfl ⟩ := hV; exact ⟨ i, rfl ⟩ ;
  convert Submonoid.pow_mem _ ( reflOp_unitary ( hP i ) ) ( x i |> ZMod.val ) using 1

/-
`f` evaluated at a standard generator `eᵢ` is the reflection `Uᵢ`.
-/
lemma fCLM_single {N : ℕ} (P : Fin N → (H d →L[ℂ] H d)) (i : Fin N) :
    fCLM P (Pi.single i 1) = reflOp (P i) := by
  unfold fCLM;
  rw [ List.ofFn_eq_map ];
  rw [ List.prod_map_eq_pow_single i ] <;> aesop

/-
Powers of a self-adjoint unitary add modulo 2.
-/
lemma reflOp_pow_add {P : H d →L[ℂ] H d} (hP : IsProjCLM P) (a b : ZMod 2) :
    ((reflOp P) ^ a.val) * ((reflOp P) ^ b.val) = (reflOp P) ^ ((a + b).val) := by
  fin_cases a <;> fin_cases b <;> simp +decide [];
  convert reflOp_mul_self hP using 1

/-
Splitting off the last coordinate of the ordered product.
-/
lemma fCLM_succ {N : ℕ} (P : Fin (N + 1) → (H d →L[ℂ] H d)) (x : Fin (N + 1) → ZMod 2) :
    fCLM P x = fCLM (fun i => P i.castSucc) (fun i => x i.castSucc)
        * (reflOp (P (Fin.last N))) ^ ((x (Fin.last N)).val) := by
  unfold fCLM;
  rw [ List.ofFn_succ' ];
  simp +decide [ List.prod_append, List.prod_cons ]

/-
Commutator of two reflection-powers (exponents `ZMod 2` values, hence in `{0,1}`) is bounded
by the reflection commutator bound.
-/
lemma hsNorm_comm_reflpow_le {A B : H d →L[ℂ] H d} (ε : ℝ) (hε0 : 0 ≤ ε)
    (h : hsNorm ((reflOp A) * (reflOp B) - (reflOp B) * (reflOp A)) ≤ 4 * ε) (a b : ZMod 2) :
    hsNorm ((reflOp A) ^ a.val * (reflOp B) ^ b.val
        - (reflOp B) ^ b.val * (reflOp A) ^ a.val) ≤ 4 * ε := by
  fin_cases a <;> fin_cases b <;> simp_all +decide;
  · simp [hsNorm];
    unfold hsVec;
    exact le_trans ( by norm_num [ PiLp.norm_eq_of_L2 ] ) ( mul_nonneg zero_le_four hε0 );
  · rw [ show hsNorm 0 = 0 from _ ];
    · linarith;
    · unfold hsNorm; aesop;
  · unfold hsNorm;
    simp +decide [ hsVec ];
    simp +decide [ Norm.norm ] ; positivity;
  · convert h using 1

/-
Moving a fixed unitary `A` past the ordered product `fCLM P y` costs at most `4Nε`,
provided `A` commutes with each factor up to `4ε`.
-/
lemma hsNorm_move_past {N : ℕ} (P : Fin N → (H d →L[ℂ] H d)) (ε : ℝ)
    (A : H d →L[ℂ] H d) (hA : A ∈ unitary (H d →L[ℂ] H d)) (y : Fin N → ZMod 2)
    (hP : ∀ i, IsProjCLM (P i))
    (hAc : ∀ j, hsNorm (A * (reflOp (P j)) ^ (y j).val
        - (reflOp (P j)) ^ (y j).val * A) ≤ 4 * ε) :
    hsNorm (A * fCLM P y - fCLM P y * A) ≤ 4 * (N : ℝ) * ε := by
  convert hsNorm_comm_listprod A hA ( List.ofFn ( fun i => reflOp ( P i ) ^ ( y i |> ZMod.val ) ) ) _ |> le_trans <| ?_ using 1;
  · intro V hV; rw [ List.mem_ofFn ] at hV; obtain ⟨ i, rfl ⟩ := hV; exact Submonoid.pow_mem _ ( reflOp_unitary ( hP i ) ) _;
  · convert List.sum_le_card_nsmul _ _ _ using 1;
    rotate_left;
    all_goals try infer_instance;
    exact 4 * ε;
    · simp +zetaDelta at *;
      exact hAc;
    · simp +decide [ mul_comm, mul_left_comm ]

/-
**Swap-counting / η-representation bound.** `f` is an `η`-representation with `η = 2N(N−1)ε`.
-/
lemma hsNorm_fCLM_eta {N : ℕ} (P : Fin N → (H d →L[ℂ] H d)) (hP : ∀ i, IsProjCLM (P i))
    (ε : ℝ) (hε0 : 0 ≤ ε)
    (hc : ∀ i j, hsNorm ((reflOp (P i)) * (reflOp (P j))
        - (reflOp (P j)) * (reflOp (P i))) ≤ 4 * ε)
    (x y : Fin N → ZMod 2) :
    hsNorm ((fCLM P x) * (fCLM P y) - fCLM P (x + y))
      ≤ 2 * (N : ℝ) * ((N : ℝ) - 1) * ε := by
  induction' N with N ih;
  · unfold fCLM hsNorm;
    unfold hsVec; norm_num [ hsNormSq ] ;
    norm_num [ Norm.norm ];
  · set Pr : Fin N → H d →L[ℂ] H d := fun i => P i.castSucc with hPrdef
    set U : H d →L[ℂ] H d := reflOp (P (Fin.last N)) with hUdef
    have hUu : U ∈ unitary (H d →L[ℂ] H d) := reflOp_unitary (hP (Fin.last N))
    have hPr' : ∀ i, IsProjCLM (Pr i) := fun i => hP i.castSucc
    set xl : ZMod 2 := x (Fin.last N) with hxldef
    set yl : ZMod 2 := y (Fin.last N) with hyldef
    set x' : Fin N → ZMod 2 := fun i => x i.castSucc with hx'def
    set y' : Fin N → ZMod 2 := fun i => y i.castSucc with hy'def
    have hx : fCLM P x = fCLM Pr x' * U ^ xl.val := fCLM_succ P x
    have hy : fCLM P y = fCLM Pr y' * U ^ yl.val := fCLM_succ P y
    have hxy : fCLM P (x + y) = fCLM Pr (x' + y') * U ^ (xl + yl).val := by
      simpa using fCLM_succ P (x + y)
    -- Piece 1: moving `U^xl` past `fCLM Pr y'` costs at most `4Nε`.
    have hP1 : hsNorm (fCLM Pr x' * U ^ xl.val * (fCLM Pr y' * U ^ yl.val)
          - fCLM Pr x' * fCLM Pr y' * U ^ (xl + yl).val) ≤ 4 * (N : ℝ) * ε := by
      have hmove : hsNorm (U ^ xl.val * fCLM Pr y' - fCLM Pr y' * U ^ xl.val) ≤ 4 * (N : ℝ) * ε :=
        hsNorm_move_past Pr ε (U ^ xl.val) (Submonoid.pow_mem _ hUu _) y' hPr'
          (fun j => hsNorm_comm_reflpow_le ε hε0 (hc (Fin.last N) j.castSucc) xl (y' j))
      have hUpow : U ^ (xl + yl).val = U ^ xl.val * U ^ yl.val :=
        (reflOp_pow_add (hP (Fin.last N)) xl yl).symm
      have heq : fCLM Pr x' * U ^ xl.val * (fCLM Pr y' * U ^ yl.val)
            - fCLM Pr x' * fCLM Pr y' * U ^ (xl + yl).val
            = fCLM Pr x' * ((U ^ xl.val * fCLM Pr y' - fCLM Pr y' * U ^ xl.val) * U ^ yl.val) := by
        rw [hUpow]; simp only [mul_sub, sub_mul, mul_assoc]
      rw [heq, hsNorm_mul_left_unitary (fCLM_unitary Pr hPr' x'),
        hsNorm_mul_right_unitary (Submonoid.pow_mem _ hUu _)]
      exact hmove
    -- Piece 2: the first `N` coordinates, by the induction hypothesis.
    have hP2 : hsNorm (fCLM Pr x' * fCLM Pr y' * U ^ (xl + yl).val
          - fCLM Pr (x' + y') * U ^ (xl + yl).val) ≤ 2 * (N : ℝ) * ((N : ℝ) - 1) * ε := by
      have heq : fCLM Pr x' * fCLM Pr y' * U ^ (xl + yl).val
            - fCLM Pr (x' + y') * U ^ (xl + yl).val
            = (fCLM Pr x' * fCLM Pr y' - fCLM Pr (x' + y')) * U ^ (xl + yl).val := by
        rw [sub_mul]
      rw [heq, hsNorm_mul_right_unitary (Submonoid.pow_mem _ hUu _)]
      exact ih Pr hPr' (fun i j => hc i.castSucc j.castSucc) x' y'
    rw [hx, hy, hxy]
    have hsum := (hsNorm_sub_triangle (fCLM Pr x' * U ^ xl.val * (fCLM Pr y' * U ^ yl.val))
      (fCLM Pr x' * fCLM Pr y' * U ^ (xl + yl).val)
      (fCLM Pr (x' + y') * U ^ (xl + yl).val)).trans (add_le_add hP1 hP2)
    have hcast : 4 * (N : ℝ) * ε + 2 * (N : ℝ) * ((N : ℝ) - 1) * ε
        = 2 * ((N : ℝ) + 1) * (((N : ℝ) + 1) - 1) * ε := by ring
    rw [hcast] at hsum
    push_cast
    convert hsum using 2

/-- `f(0) = I`: the ordered product over the all-zero exponent vector is the identity. -/
lemma fCLM_zero {N : ℕ} (P : Fin N → (H d →L[ℂ] H d)) :
    fCLM P 0 = 1 := by
  unfold fCLM
  simp

end