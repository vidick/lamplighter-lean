import RequestProject.SepProj.Defs
import RequestProject.SepProj.Lemma3
import RequestProject.SepProj.Lemma4
import RequestProject.SepProj.Lemma5

open scoped BigOperators InnerProductSpace
open Matrix
open RCLike

namespace SepProj

/-! ## The coherent dilation construction

We model `K_N = H ⊗ (ℂ²)^{⊗N}` by the index type `Fin d × (Fin N → Fin 2)`: the first factor is
`H = ℂ^d`, the second is the `N` ancilla qubits encoded as bit strings.  Operators on `K_N` are
`Matrix (Fin d × (Fin N → Fin 2))`-matrices. -/

/-- The ancilla index: a string of `N` bits. -/
abbrev Anc (N : ℕ) := Fin N → Fin 2

/-- The dilated index `H ⊗ (ℂ²)^{⊗N}`. -/
abbrev Ksp (d N : ℕ) := Fin d × Anc N

variable {d N : ℕ}

/-- The `j`-th factor of a branch: `P j` if the `j`-th bit is `1`, else `I - P j`. -/
noncomputable def facOp (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (j : Fin N) (b : Fin 2) :
    Matrix (Fin d) (Fin d) ℂ :=
  if b = 1 then P j else 1 - P j

/-- The ordered branch operator `T_x = M_{N-1} ⋯ M_1 M_0` where `M_j = facOp P j (x j)`. -/
noncomputable def branchOp (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (x : Anc N) :
    Matrix (Fin d) (Fin d) ℂ :=
  (List.ofFn (fun j : Fin N => facOp P j (x j))).reverse.prod

/-- The dilation isometry `V : H → K_N`, `V (a', x) a = (T_x) a' a`. -/
noncomputable def dil (P : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Ksp d N) (Fin d) ℂ :=
  fun k a => branchOp P k.2 k.1 a

/-- The `i`-th register projection: project onto strings whose `i`-th bit is `1`. -/
noncomputable def reg (i : Fin N) : Matrix (Ksp d N) (Ksp d N) ℂ :=
  Matrix.diagonal (fun k => if k.2 i = 1 then 1 else 0)

/-- The Hilbert–Schmidt pinching by a projection `P`: `E_P(X) = P X P + (I-P) X (I-P)`. -/
noncomputable def pinch1 (P X : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  P * X * P + (1 - P) * X * (1 - P)

/-! ### Foundational facts about the construction -/

/-
Each register projection is diagonal.
-/
lemma reg_isDiag (i : Fin N) : (reg (d := d) i).IsDiag := by
  exact fun k l hkl => by unfold reg; aesop;

/-
Each register projection is a projection.
-/
lemma reg_isProj (i : Fin N) : IsProj (reg (d := d) i) := by
  unfold IsProj reg;
  simp +decide [ Matrix.IsHermitian]

/-
The register projections commute pairwise.
-/
lemma reg_comm (i j : Fin N) : reg (d := d) i * reg j = reg j * reg i := by
  ext ⟨ a, b ⟩ ⟨ c, d ⟩ ; simp +decide [ Matrix.mul_apply, reg ] ; ring;
  simp +decide [ diagonal ];
  grind +revert

/-
The key telescoping identity: summing `T_xᴴ T_x` over all branches gives the identity.
-/
lemma branchOp_sum (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i)) :
    ∑ x : Anc N, (branchOp P x)ᴴ * branchOp P x = 1 := by
  induction N <;> simp_all +decide [ branchOp, IsProj ];
  rename_i n ih; specialize ih ( fun i => P i.succ ) ( fun i => hP _ ) ; simp_all +decide [ ← mul_assoc] ;
  convert congr_arg ( fun x => ( 1 - P 0 ) * x * ( 1 - P 0 ) + P 0 * x * P 0 ) ih using 1;
  · rw [ show ( Finset.univ : Finset ( Fin ( n + 1 ) → Fin 2 ) ) = Finset.image ( fun x : Fin n → Fin 2 => Fin.cons 0 x ) Finset.univ ∪ Finset.image ( fun x : Fin n → Fin 2 => Fin.cons 1 x ) Finset.univ from ?_, Finset.sum_union ];
    · simp +decide [ Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, facOp ];
      rw [ Finset.sum_image, Finset.sum_image ] <;> simp +decide [ Fin.cons ];
      · simp +decide [ hP 0 |>.1.eq ];
      · exact fun x y h => by simpa [ Fin.ext_iff ] using h;
      · exact fun x y h => by simpa [ Fin.ext_iff ] using h;
    · norm_num [ Finset.disjoint_left ];
    · ext x; simp ;
      cases Fin.exists_fin_two.mp ⟨ x 0, rfl ⟩ <;> [ left; right ] <;> use fun i => x i.succ <;> ext i <;> cases i using Fin.inductionOn <;> aesop;
  · simp +decide [ sub_mul, mul_sub, hP 0 ]

/-
The dilation is an isometry: `Vᴴ V = 1`.
-/
lemma dil_isometry (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i)) :
    (dil P)ᴴ * dil P = 1 := by
  convert branchOp_sum P hP using 1;
  ext i j; simp +decide [ Matrix.mul_apply, Matrix.sum_apply ] ;
  convert Fintype.sum_prod_type ( fun x : Fin d × Anc N => ( starRingEnd ℂ ) ( dil P x i ) * dil P x j ) using 1;
  exact Finset.sum_comm

/-- The compressed register observable `A_i = Vᴴ R_i V` on `H`. -/
noncomputable def Aop (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (i : Fin N) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((dil P)ᴴ * reg i : Matrix (Fin d) (Ksp d N) ℂ) * dil P

/-- The rank-`d` projection `E = V Vᴴ` onto the range of the dilation. -/
noncomputable def Erange (P : Fin N → Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Ksp d N) (Ksp d N) ℂ :=
  (dil P * (dil P)ᴴ : Matrix (Ksp d N) (Ksp d N) ℂ)

/-! ### Hilbert–Schmidt contraction helpers -/

/-
Left multiplication by an isometry preserves the `d`-scaled HS norm.
-/
lemma hsNormSq_isom_left {V : Matrix (Ksp d N) (Fin d) ℂ} (hV : Vᴴ * V = 1)
    (Z : Matrix (Fin d) (Fin d) ℂ) : hsNormSq d (V * Z) = hsNormSq d Z := by
  simp_all +decide [ hsNormSq];
  simp +decide [ ← Matrix.mul_assoc];
  simp +decide [ Matrix.mul_assoc, hV ]

/-
Left multiplication by a projection contracts the `d`-scaled HS norm.
-/
lemma hsNormSq_proj_left {R : Matrix (Ksp d N) (Ksp d N) ℂ} (hR : IsProj R)
    (Z : Matrix (Ksp d N) (Fin d) ℂ) : hsNormSq d (R * Z) ≤ hsNormSq d Z := by
  -- It suffices to show `((R*Z)ᴴ * (R*Z)).trace.re ≤ (Zᴴ * Z).trace.re` and divide by `d ≥ 0`.
  suffices h.trace : (Zᴴ * Z - Zᴴ * R * Z).trace.re ≥ 0 by
    refine' div_le_div_of_nonneg_right _ _;
    · convert sub_le_self _ h.trace using 1 ; norm_num [ Matrix.mul_assoc, hR.1.eq ];
      simp +decide [ ← Matrix.mul_assoc, hR.2 ];
    · positivity;
  have h_pos_semidef : ∀ (M : Matrix (Ksp d N) (Fin d) ℂ), (Mᴴ * M).trace.re ≥ 0 := by
    intro M; simp +decide [ Matrix.trace, Matrix.mul_apply ] ;
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg ( mul_self_nonneg _ ) ( mul_self_nonneg _ );
  convert h_pos_semidef ( ( 1 - R ) * Z ) using 1 ; simp +decide [ Matrix.mul_assoc];
  simp +decide [ Matrix.sub_mul, Matrix.mul_sub, hR.1.eq ];
  simp +decide [ ← Matrix.mul_assoc, hR.2 ]

/-
Right multiplication by a projection contracts the `d`-scaled HS norm.
-/
lemma hsNormSq_proj_right {Pm : Matrix (Fin d) (Fin d) ℂ} (hPm : IsProj Pm)
    (Z : Matrix (Ksp d N) (Fin d) ℂ) : hsNormSq d (Z * Pm) ≤ hsNormSq d Z := by
  -- By the properties of the trace and the fact that $Pm$ is a projection, we have:
  have h_trace : ((Z * Pm)ᴴ * (Z * Pm)).trace.re = ((Pm * Zᴴ * Z * Pm)).trace.re := by
    simp +decide [ Matrix.mul_assoc, Matrix.conjTranspose_mul, hPm.1.eq ];
  -- By the properties of the trace and the fact that $Pm$ is a projection, we have $(Pm * Zᴴ * Z * Pm).trace = (Zᴴ * Z * Pm).trace$.
  have h_trace_eq : ((Pm * Zᴴ * Z * Pm)).trace = ((Zᴴ * Z * Pm)).trace := by
    simp +decide only [Matrix.mul_assoc];
    rw [ ← Matrix.trace_mul_comm ] ; simp +decide [ ← Matrix.mul_assoc] ;
    rw [ Matrix.mul_assoc, hPm.2 ];
  -- By the properties of the trace and the fact that $Pm$ is a projection, we have $(Zᴴ * Z * Pm).trace = (Zᴴ * Z).trace - ((1 - Pm) * Zᴴ * Z * (1 - Pm)).trace$.
  have h_trace_split : ((Zᴴ * Z * Pm)).trace = ((Zᴴ * Z)).trace - ((1 - Pm) * Zᴴ * Z * (1 - Pm)).trace := by
    simp +decide [ sub_mul, mul_sub, Matrix.mul_assoc, Matrix.trace_mul_comm Pm ];
    rw [ show Pm * Pm = Pm from hPm.2 ] ; ring;
  -- By the properties of the trace and the fact that $Pm$ is a projection, we have $((1 - Pm) * Zᴴ * Z * (1 - Pm)).trace.re \geq 0$.
  have h_trace_nonneg : 0 ≤ ((1 - Pm) * Zᴴ * Z * (1 - Pm)).trace.re := by
    convert trace_conjTranspose_mul_self_re_nonneg ( Z * ( 1 - Pm ) ) using 1;
    simp +decide [ Matrix.mul_assoc, Matrix.conjTranspose_mul ];
    rw [ hPm.1 ];
  exact div_le_div_of_nonneg_right ( by norm_num [ Complex.ext_iff ] at *; linarith ) ( Nat.cast_nonneg _ )

/-
`E = V Vᴴ` is a projection.
-/
lemma Erange_isProj (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i)) :
    IsProj (Erange P) := by
  constructor;
  · simp +decide [ Erange, Matrix.IsHermitian ];
  · unfold Erange;
    simp +decide only [Matrix.mul_assoc];
    simp +decide only [← Matrix.mul_assoc, dil_isometry P hP];
    rw [ Matrix.mul_one ]

/-
`E = V Vᴴ` has rank `d` (trace `d`).
-/
lemma Erange_trace (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i)) :
    (Erange P).trace.re = (d : ℝ) := by
  convert congr_arg Complex.re ( congr_arg Matrix.trace ( show ( dil P * ( dil P ) ᴴ ) = ( dil P ) * ( dil P ) ᴴ from rfl ) ) using 1;
  rw [ ← Matrix.trace_transpose, Matrix.transpose_mul ] ; norm_num [ dil_isometry P hP ]

/-! ### The two HS identities (eq. 8 and eq. 11 of the note) and the Lemma 3 bounds -/

/-
**Equation (8)**: the commutator norm of a register projection with `E` in terms of the
defect of `A_i`.
-/
lemma comm_reg_Erange (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i)) (i : Fin N) :
    hsNormSq d (comm (reg i) (Erange P))
      = 2 * (Aop P i - Aop P i * Aop P i).trace.re / d := by
  unfold hsNormSq comm Aop Erange;
  simp +decide [ Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub ];
  rw [ show ( reg i ) ᴴ = reg i from ?_ ];
  · simp +decide [ ← Matrix.mul_assoc, dil_isometry P hP ];
    simp +decide [ Matrix.mul_assoc, Matrix.trace_mul_comm ( reg i ) ] ; ring;
    simp +decide [ ← Matrix.mul_assoc, reg_isProj i |>.2 ] ; ring;
    simp +decide [ Matrix.mul_assoc, Matrix.trace_mul_comm ( dil P ) ] ; ring;
    rw [ dil_isometry P hP ] ; norm_num ; ring;
  · exact reg_isProj i |>.1

/-
**Equation (11)**: the displacement `R_i V - V P_i` in terms of `A_i`.
-/
lemma reg_dil_disp (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i)) (i : Fin N) :
    hsNormSq d (reg i * dil P - dil P * P i)
      = hsNormSq d (Aop P i - P i) + (Aop P i - Aop P i * Aop P i).trace.re / d := by
  unfold hsNormSq Aop; norm_num [ Matrix.mul_assoc, Matrix.trace_mul_comm ( reg i ) ] ; ring;
  simp +decide [ Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc ] ; ring;
  simp +decide [ Matrix.mul_assoc ] ; ring;
  simp +decide [ ← Matrix.mul_assoc, dil_isometry P ( fun i => hP i ) ] ; ring;
  rw [ show ( reg i ) ᴴ = reg i from reg_isProj i |>.1 ] ; ring;
  simp +decide [ Matrix.mul_assoc, reg_isProj i |>.2 ] ; ring

/-! ### Pinching properties and the iterated pinching -/

/-
`pinch1` is self-adjoint for the Hilbert–Schmidt inner product.
-/
lemma pinch1_selfadjoint (Pm X Y : Matrix (Fin d) (Fin d) ℂ) (hPm : Pm.IsHermitian) :
    hsIP (pinch1 Pm X) Y = hsIP X (pinch1 Pm Y) := by
  unfold hsIP pinch1;
  simp +decide [ Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub];
  simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc, Matrix.trace_mul_comm Pm ]

/-
`pinch1` is idempotent on projections.
-/
lemma pinch1_idem (Pm X : Matrix (Fin d) (Fin d) ℂ) (hPm : IsProj Pm) :
    pinch1 Pm (pinch1 Pm X) = pinch1 Pm X := by
  simp_all +decide [ IsProj, pinch1 ];
  simp_all +decide [ mul_add, add_mul, mul_assoc, sub_mul, mul_sub ];
  grind

/-
`pinch1` preserves the trace.
-/
lemma pinch1_trace (Pm X : Matrix (Fin d) (Fin d) ℂ) (hPm : IsProj Pm) :
    (pinch1 Pm X).trace = X.trace := by
  unfold pinch1; simp +decide [ mul_assoc, Matrix.trace_mul_comm Pm ] ;
  simp_all +decide [ ← mul_assoc, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub ];
  simp_all +decide [ mul_assoc, Matrix.trace_mul_comm Pm, hPm.2 ]

/-
`pinch1` preserves Hermitian matrices.
-/
lemma pinch1_isHermitian (Pm X : Matrix (Fin d) (Fin d) ℂ) (hPm : IsProj Pm)
    (hX : X.IsHermitian) : (pinch1 Pm X).IsHermitian := by
  unfold pinch1; simp +decide [ *, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_mul ] ;
  simp_all +decide [ mul_assoc, sub_mul, mul_sub, Matrix.IsHermitian ];
  rw [ hPm.1.eq ]

/-
**Equation (4)**: the pinching error equals the commutator (in HS norm).
-/
lemma pinch1_sub_norm (Pm X : Matrix (Fin d) (Fin d) ℂ) (hPm : IsProj Pm) :
    hsNormSq d (X - pinch1 Pm X) = hsNormSq d (comm Pm X) := by
  unfold hsNormSq comm;
  obtain ⟨ hPm₁, hPm₂ ⟩ := hPm;
  simp +decide [ pinch1, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc];
  simp +decide [ Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub, hPm₁.eq ];
  grind +qlia

/-- The iterated pinching `E_{Ms[0]} ∘ ⋯ ∘ E_{Ms[last]}` (the last factor applied first). -/
noncomputable def pinchList (Ms : List (Matrix (Fin d) (Fin d) ℂ)) (X : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Ms.foldr (fun M Y => pinch1 M Y) X

/-- The list `[P 0, P 1, …, P (i-1)]` of projections preceding index `i`. -/
noncomputable def Pbelow (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (i : Fin N) :
    List (Matrix (Fin d) (Fin d) ℂ) :=
  List.ofFn (fun j : Fin (i : ℕ) => P (Fin.castLE (le_of_lt i.isLt) j))

/-
The iterated pinching preserves the trace.
-/
lemma pinchList_trace (Ms : List (Matrix (Fin d) (Fin d) ℂ)) (hMs : ∀ M ∈ Ms, IsProj M)
    (X : Matrix (Fin d) (Fin d) ℂ) : (pinchList Ms X).trace = X.trace := by
  induction' Ms with M Ms ih generalizing X <;> simp_all +decide [ pinchList ];
  rw [ pinch1_trace _ _ hMs.1, ih ]

/-
**Equation (3)**: `A_i = Vᴴ R_i V` equals the iterated pinching of `P_i`.
-/
lemma Aop_eq_pinchList (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i)) (i : Fin N) :
    Aop P i = pinchList (Pbelow P i) (P i) := by
  by_contra h_contra;
  -- By definition of `Aop`, we have:
  have hAop_def : Aop P i = ∑ x : Anc N, if x i = 1 then (branchOp P x)ᴴ * branchOp P x else 0 := by
    ext a b;
    simp +decide [ Aop, Matrix.mul_apply, Finset.sum_ite ];
    unfold dil reg; simp +decide [ Matrix.sum_apply, Matrix.mul_apply] ;
    simp +decide [ Finset.sum_sigma', Matrix.diagonal ];
    rw [ ← Finset.sum_filter ] ; refine' Finset.sum_bij ( fun x hx => ⟨ x.2, x.1 ⟩ ) _ _ _ _ <;> aesop;
  -- We prove the equality by induction on $N$.
  have h_ind : ∀ (N : ℕ) (i : Fin N) (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i)),
    (∑ x : Fin N → Fin 2, if x i = 1 then (List.prod (List.ofFn (fun j => facOp P j (x j))).reverse)ᴴ * List.prod (List.ofFn (fun j => facOp P j (x j))).reverse else 0) = pinchList (List.ofFn (fun j : Fin i => P (Fin.castLE (le_of_lt i.isLt) j))) (P i) := by
      intro N;
      induction' N with N ih;
      · simp +decide ;
      · intro i P hP;
        refine' Fin.cases _ _ i <;> simp +decide [ List.ofFn_succ ];
        · rw [ Finset.sum_ite ];
          rw [ show ( Finset.univ.filter fun x : Fin ( N + 1 ) → Fin 2 => x 0 = 1 ) = Finset.image ( fun x : Fin N → Fin 2 => Fin.cons 1 x ) ( Finset.univ : Finset ( Fin N → Fin 2 ) ) from ?_, Finset.sum_image ] <;> norm_num;
          · simp +decide [ facOp, pinchList ];
            convert congr_arg ( fun x : Matrix ( Fin d ) ( Fin d ) ℂ => ( P 0 )ᴴ * x * P 0 ) ( branchOp_sum ( fun i => P i.succ ) fun i => hP i.succ ) using 1;
            · simp +decide [ Finset.mul_sum _ _ _, Finset.sum_mul, Matrix.mul_assoc, branchOp ];
              congr! 3;
            · have := hP 0; exact this.1.symm ▸ by simp +decide [ this.2 ] ;
          · exact fun x y h => by simpa [ Fin.ext_iff ] using h;
          · ext x; simp ;
            exact ⟨ fun hx => ⟨ fun i => x i.succ, by ext i; cases i using Fin.inductionOn <;> simp +decide [ hx ] ⟩, by rintro ⟨ a, rfl ⟩ ; simp +decide ⟩;
        · intro i;
          convert congr_arg ( fun x => facOp P 0 1 * x * facOp P 0 1 + facOp P 0 0 * x * facOp P 0 0 ) ( ih i ( fun j => P j.succ ) ( fun j => hP j.succ ) ) using 1;
          rw [ show ( Finset.univ : Finset ( Fin ( N + 1 ) → Fin 2 ) ) = Finset.image ( fun x : Fin N → Fin 2 => Fin.cons 0 x ) Finset.univ ∪ Finset.image ( fun x : Fin N → Fin 2 => Fin.cons 1 x ) Finset.univ from ?_, Finset.sum_union ];
          · rw [ Finset.sum_image, Finset.sum_image ] <;> simp +decide [ Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc ];
            · simp +decide [ facOp];
              have := hP 0; have := this.1; simp_all +decide [ Matrix.IsHermitian] ;
              rw [ add_comm ];
            · exact fun x y h => by simpa [ Fin.ext_iff ] using h;
            · exact fun x y h => by simpa [ Fin.ext_iff ] using h;
          · norm_num [ Finset.disjoint_left ];
          · ext x; simp ;
            by_cases hx : x 0 = 0;
            · exact Or.inl ⟨ fun j => x j.succ, by ext j; cases j using Fin.inductionOn <;> simp +decide [ hx ] ⟩;
            · exact Or.inr ⟨ fun j => x j.succ, by ext j; cases j using Fin.inductionOn <;> simp +decide [ show x 0 = 1 from Or.resolve_left ( Fin.exists_fin_two.mp ( by tauto ) ) hx ] ⟩;
  exact h_contra <| hAop_def.trans <| h_ind N i P hP

/-- Flatten a `d × d` matrix to a Euclidean vector; this is a linear isometry for the (unscaled)
Hilbert–Schmidt inner product. -/
noncomputable def flatL (d : ℕ) : Matrix (Fin d) (Fin d) ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d × Fin d) :=
  (LinearEquiv.curry ℂ ℂ (Fin d) (Fin d)).symm.trans
    (WithLp.linearEquiv 2 ℂ (Fin d × Fin d → ℂ)).symm

@[simp] lemma flatL_apply (X : Matrix (Fin d) (Fin d) ℂ) (p : Fin d × Fin d) :
    flatL d X p = X p.1 p.2 := rfl

/-
`flatL` carries the Euclidean inner product to the (unscaled) HS inner product `Tr(Xᴴ Y)`.
-/
lemma flatL_inner (X Y : Matrix (Fin d) (Fin d) ℂ) :
    (inner ℂ (flatL d X) (flatL d Y)) = (Xᴴ * Y).trace := by
  convert ( Fintype.sum_prod_type fun p : Fin d × Fin d => ( starRingEnd ℂ ) ( X p.1 p.2 ) * Y p.1 p.2 ) using 1;
  · norm_num [ inner, EuclideanSpace.inner_eq_star_dotProduct ];
    grind;
  · simp +decide [ Matrix.trace, Matrix.mul_apply ];
    exact Finset.sum_comm

/-
`flatL` relates the Euclidean norm to the `d`-scaled HS norm.
-/
lemma flatL_normSq (X : Matrix (Fin d) (Fin d) ℂ) :
    ‖flatL d X‖ ^ 2 = (d : ℝ) * hsNormSq d X := by
  by_cases hd : d = 0;
  · subst hd; norm_num;
    exact Subsingleton.elim _ _;
  · rw [ EuclideanSpace.norm_eq ] ; norm_num [ hsNormSq_eq_sum ] ; ring;
    rw [ Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _, mul_right_comm, mul_inv_cancel₀ <| by positivity, one_mul, ← Finset.sum_product' ];
    rfl

/-- The pinching `pinch1 M` as a `ℂ`-linear map. -/
noncomputable def pinch1LM (M : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun X := pinch1 M X
  map_add' X Y := by simp only [pinch1]; rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.add_mul]; abel
  map_smul' c X := by
    simp only [pinch1, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, smul_add]

@[simp] lemma pinch1LM_apply (M X : Matrix (Fin d) (Fin d) ℂ) : pinch1LM M X = pinch1 M X := rfl

/-
**Lemma 3** in matrix Hilbert–Schmidt form, applied to a chain of pinchings.
-/
lemma pinchList_lemma3 (Ms : List (Matrix (Fin d) (Fin d) ℂ)) (hMs : ∀ M ∈ Ms, IsProj M)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    hsNormSq d (X - pinchList Ms X) ≤ (Ms.map (fun M => hsNormSq d (X - pinch1 M X))).sum ∧
    hsNormSq d X - hsNormSq d (pinchList Ms X)
      ≤ 4 * (Ms.map (fun M => hsNormSq d (X - pinch1 M X))).sum := by
  set E := EuclideanSpace ℂ (Fin d × Fin d)
  set T : ℕ → E →L[ℂ] E := fun j => LinearMap.toContinuousLinearMap ((flatL d).toLinearMap ∘ₗ pinch1LM (Ms.reverse.getD j 0) ∘ₗ (flatL d).symm.toLinearMap);
  have h_seqApply : ∀ k ≤ Ms.length, seqApply T k (flatL d X) = flatL d (List.foldr (fun M Y => pinch1 M Y) X (Ms.drop (Ms.length - k))) := by
    intro k hk
    induction' k with k ih;
    · simp +decide [ seqApply_zero ];
    · convert congr_arg ( fun x => T k x ) ( ih ( Nat.le_of_succ_le hk ) ) using 1;
      rw [ show Ms.length - k = Ms.length - ( k + 1 ) + 1 by omega, List.drop_eq_getElem_cons ];
      simp +zetaDelta at *;
      grind;
      omega;
  have h_lemma3 : ‖flatL d X - seqApply T Ms.length (flatL d X)‖ ^ 2 ≤ ∑ j ∈ Finset.range Ms.length, ‖flatL d X - T j (flatL d X)‖ ^ 2 ∧ ‖flatL d X‖ ^ 2 - ‖seqApply T Ms.length (flatL d X)‖ ^ 2 ≤ 4 * ∑ j ∈ Finset.range Ms.length, ‖flatL d X - T j (flatL d X)‖ ^ 2 := by
    apply SepProj.lemma3;
    · intro j hj u v; simp +decide [ T, inner ] ;
      convert pinch1_selfadjoint ( Ms.reverse[j]?.getD 0 ) ( ( flatL d ).symm u ) ( ( flatL d ).symm v ) ( hMs _ _ |>.1 ) using 1;
      · convert flatL_inner ( pinch1 ( Ms.reverse[j]?.getD 0 ) ( ( flatL d ).symm u ) ) ( ( flatL d ).symm v ) using 1;
      · convert flatL_inner ( ( flatL d ).symm u ) ( pinch1 ( Ms.reverse[j]?.getD 0 ) ( ( flatL d ).symm v ) ) using 1;
      · grind;
    · intro j hj u;
      convert congr_arg ( fun x => flatL d x ) ( pinch1_idem ( Ms.reverse.getD j 0 ) ( ( flatL d ).symm u ) ( hMs _ _ ) ) using 1;
      grind +qlia;
  have h_norm_sq : ∀ j < Ms.length, ‖flatL d X - T j (flatL d X)‖ ^ 2 = d * hsNormSq d (X - pinch1 (Ms.reverse.getD j 0) X) := by
    intro j hj;
    convert flatL_normSq ( X - pinch1 ( Ms.reverse.getD j 0 ) X ) using 1;
  have h_sum_norm_sq : ∑ j ∈ Finset.range Ms.length, ‖flatL d X - T j (flatL d X)‖ ^ 2 = d * (List.map (fun M => hsNormSq d (X - pinch1 M X)) Ms).sum := by
    rw [ Finset.sum_congr rfl fun j hj => h_norm_sq j ( Finset.mem_range.mp hj ) ] ; norm_num [ Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring;
    rw [ ← Finset.mul_sum _ _ _ ] ; simp +decide [ Finset.sum_range] ; ring;
    rw [ ← List.sum_reverse ] ;
    refine' Or.inl ( congr_arg _ ( List.ext_get _ _ ) ) <;> simp +decide ;
  have h_norm_sq : ‖flatL d X - seqApply T Ms.length (flatL d X)‖ ^ 2 = d * hsNormSq d (X - pinchList Ms X) := by
    convert flatL_normSq ( X - List.foldr ( fun M Y => pinch1 M Y ) X ( List.drop ( Ms.length - Ms.length ) Ms ) ) using 1;
    · grind +locals;
    · simp +decide [ pinchList ]
  have h_norm_sq_X : ‖flatL d X‖ ^ 2 = d * hsNormSq d X := by
    convert flatL_normSq X using 1
  have h_norm_sq_pinchList : ‖seqApply T Ms.length (flatL d X)‖ ^ 2 = d * hsNormSq d (pinchList Ms X) := by
    convert flatL_normSq ( List.foldr ( fun M Y => pinch1 M Y ) X ( List.drop ( Ms.length - Ms.length ) Ms ) ) using 1 ; aesop;
    unfold pinchList; aesop;
  rcases d with ( _ | d ) <;> norm_num at *;
  · simp +decide [ hsNormSq ];
  · constructor <;> nlinarith

/-
The sum of pinching errors along `Pbelow P i` is at most `i ε²`.
-/
lemma Pbelow_sum_le (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i))
    (ε : ℝ) (hcomm : ∀ i j, hsNorm d (comm (P i) (P j)) ≤ ε) (i : Fin N) :
    ((Pbelow P i).map (fun M => hsNormSq d (P i - pinch1 M (P i)))).sum ≤ (i : ℝ) * ε ^ 2 := by
  unfold Pbelow;
  refine' le_trans ( List.sum_le_sum fun x hx => _ ) _;
  use fun x => ε ^ 2;
  · rw [ pinch1_sub_norm ];
    · rw [ List.mem_ofFn ] at hx;
      obtain ⟨ j, rfl ⟩ := hx; specialize hcomm ( Fin.castLE ( Nat.le_of_lt i.2 ) j ) i; simp_all +decide  ;
      exact le_trans ( by rw [ ← hsNorm_sq ] ) ( pow_le_pow_left₀ ( by exact hsNorm_nonneg _ _ ) hcomm 2 );
    · rw [ List.mem_ofFn ] at hx; aesop;
  · norm_num [ List.sum_ofFn ]

/-
**Equation (5)**: the iterated-pinching error bound from Lemma 3.
-/
lemma Aop_sub_bound (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i))
    (ε : ℝ) (hcomm : ∀ i j, hsNorm d (comm (P i) (P j)) ≤ ε) (i : Fin N) :
    hsNormSq d (Aop P i - P i) ≤ (i : ℝ) * ε ^ 2 := by
  convert le_trans ( pinchList_lemma3 ( Pbelow P i ) _ _ |>.1 ) ( Pbelow_sum_le P hP ε hcomm i ) using 1;
  · rw [ ← Aop_eq_pinchList P hP i ] ; unfold hsNormSq ; ring;
    simp +decide [ Matrix.trace, Matrix.mul_apply, sub_mul, mul_sub ] ; ring;
  · unfold Pbelow; aesop;

/-
**Equation (7)**: the defect bound `τ(A_i - A_i²) ≤ 4 i ε²` from Lemma 3.
-/
lemma Aop_defect_bound (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i))
    (ε : ℝ) (hcomm : ∀ i j, hsNorm d (comm (P i) (P j)) ≤ ε) (i : Fin N) :
    (Aop P i - Aop P i * Aop P i).trace.re / d ≤ 4 * (i : ℝ) * ε ^ 2 := by
  convert le_trans ( pinchList_lemma3 ( Pbelow P i ) _ _ |>.2 ) ( mul_le_mul_of_nonneg_left ( Pbelow_sum_le P hP ε hcomm i ) zero_le_four ) using 1;
  · convert congr_arg ( fun x : ℝ => x / d ) ( show ( Aop P i - Aop P i * Aop P i ).trace.re = ( P i |> Matrix.trace |> Complex.re ) - ( Aop P i * Aop P i |> Matrix.trace |> Complex.re ) from ?_ ) using 1;
    · rw [ ← Aop_eq_pinchList P hP i ] ; ring;
      unfold hsNormSq;
      rw [ show ( Aop P i )ᴴ = Aop P i from ?_ ];
      · rw [ show ( P i )ᴴ = P i from hP i |>.1 ] ; ring;
        rw [ hP i |>.2 ] ; ring;
      · unfold Aop; simp +decide [ Matrix.mul_assoc] ;
        rw [ reg_isProj i |>.1 ];
    · rw [ Matrix.trace_sub ];
      rw [ Aop_eq_pinchList P hP i, pinchList_trace _ _ _ ] ; norm_num;
      unfold Pbelow; aesop;
  · ring;
  · unfold Pbelow; aesop;

/-! ### HS-norm helpers and the numeric bound for the final assembly -/

/-
The `d`-scaled HS norm is invariant under negation of the argument.
-/
lemma hsNorm_neg (X : Matrix (Ksp d N) (Fin d) ℂ) : hsNorm d (-X) = hsNorm d X := by
  unfold hsNorm hsNormSq; norm_num;

/-
Left multiplication by an isometry preserves the HS norm.
-/
lemma hsNorm_isom_left {V : Matrix (Ksp d N) (Fin d) ℂ} (hV : Vᴴ * V = 1)
    (Z : Matrix (Fin d) (Fin d) ℂ) : hsNorm d (V * Z) = hsNorm d Z := by
  unfold hsNorm;
  rw [ hsNormSq_isom_left hV ]

/-
Left multiplication by a projection contracts the HS norm.
-/
lemma hsNorm_proj_left {R : Matrix (Ksp d N) (Ksp d N) ℂ} (hR : IsProj R)
    (Z : Matrix (Ksp d N) (Fin d) ℂ) : hsNorm d (R * Z) ≤ hsNorm d Z := by
  exact Real.sqrt_le_sqrt <| hsNormSq_proj_left hR Z

/-
Right multiplication by a projection contracts the HS norm.
-/
lemma hsNorm_proj_right {Pm : Matrix (Fin d) (Fin d) ℂ} (hPm : IsProj Pm)
    (Z : Matrix (Ksp d N) (Fin d) ℂ) : hsNorm d (Z * Pm) ≤ hsNorm d Z := by
  exact Real.sqrt_le_sqrt <| hsNormSq_proj_right hPm Z

/-
The triangle inequality for the `d`-scaled HS norm (on `K × H` matrices).
-/
lemma hsNorm_triangle (A B : Matrix (Ksp d N) (Fin d) ℂ) :
    hsNorm d (A + B) ≤ hsNorm d A + hsNorm d B := by
  by_cases hd : d = 0 <;> simp_all +decide [ hsNorm ];
  · unfold hsNormSq; aesop;
  · rw [ hsNormSq_eq_sum, hsNormSq_eq_sum, hsNormSq_eq_sum ];
    -- By the properties of the Euclidean norm, we can apply the Minkowski inequality to the sums.
    have h_minkowski : ∀ (u v : Fin d × Ksp d N → ℂ), Real.sqrt (∑ i, ‖u i + v i‖ ^ 2) ≤ Real.sqrt (∑ i, ‖u i‖ ^ 2) + Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
      have h_minkowski : ∀ (u v : EuclideanSpace ℂ (Fin d × Ksp d N)), ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
        exact fun u v => norm_add_le u v;
      simp_all +decide [ EuclideanSpace.norm_eq ];
    convert div_le_div_of_nonneg_right ( h_minkowski ( fun p => A p.2 p.1 ) ( fun p => B p.2 p.1 ) ) ( Real.sqrt_nonneg d ) using 1;
    · rw [ Real.sqrt_div' _ ( Nat.cast_nonneg _ ), ← Finset.sum_product' ] ; norm_num [ Finset.sum_add_distrib, add_sq ] ; ring;
      rw [ mul_comm, ← Equiv.sum_comp ( Equiv.prodComm _ _ ) ] ; norm_num;
    · rw [ ← Finset.sum_product', ← Finset.sum_product' ] ; norm_num [ add_div, Real.sqrt_div_self ] ;
      exact congrArg₂ ( · + · ) ( by rw [ ← Equiv.sum_comp ( Equiv.prodComm _ _ ) ] ; norm_num ) ( by rw [ ← Equiv.sum_comp ( Equiv.prodComm _ _ ) ] ; norm_num )

/-
Gauss sum over `Fin N`.
-/
lemma sum_fin_cast (N : ℕ) : ∑ i : Fin N, (i : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
  convert Finset.sum_range_id N using 1 ; norm_num [ Finset.sum_range _, div_eq_mul_inv ];
  rw [ ← @Nat.cast_inj ℚ ] ; simp +decide [ mul_assoc ] ; ring;
  cases N <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.mod_two_of_bodd ] ; ring;
  norm_num [ ← @Rat.cast_inj ℝ ]

/-
The numeric bound `4√(2N(N-1)) + √(5 i) ≤ 8N`.
-/
lemma sep_numeric {N : ℕ} (hN : 0 < N) (i : ℝ) (hi0 : 0 ≤ i) (hi : i ≤ (N : ℝ) - 1) :
    4 * Real.sqrt (2 * (N : ℝ) * ((N : ℝ) - 1)) + Real.sqrt (5 * i) ≤ 8 * (N : ℝ) := by
  -- Use `Real.sqrt_sq`, `Real.sqrt_le_sqrt`, `Real.sqrt_mul_self`, `Real.sqrt_le_one`, and `nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 2, Real.sqrt_nonneg 5]` to verify `4√2 + √5 ≤ 8`.
  have h_bound : 4 * Real.sqrt 2 + Real.sqrt 5 ≤ 8 := by
    nlinarith [ sq_nonneg ( Real.sqrt 2 - Real.sqrt 5 ), Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.mul_self_sqrt ( show 0 ≤ 5 by norm_num ) ];
  -- Apply the bound to the left-hand side.
  have h_lhs_bound : 4 * Real.sqrt (2 * N * (N - 1)) ≤ 4 * Real.sqrt 2 * N ∧ Real.sqrt (5 * i) ≤ Real.sqrt 5 * N := by
    constructor;
    · rw [ mul_assoc ];
      rw [ mul_assoc, Real.sqrt_mul ( by positivity ) ];
      exact mul_le_mul_of_nonneg_left ( mul_le_mul_of_nonneg_left ( Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith [ show ( N : ℝ ) ≥ 1 by norm_cast ] ⟩ ) ( by positivity ) ) ( by positivity );
    · rw [ Real.sqrt_le_iff ];
      exact ⟨ by positivity, by rw [ mul_pow, Real.sq_sqrt ] <;> nlinarith [ show ( N : ℝ ) ≥ 1 by norm_cast ] ⟩;
  nlinarith [ ( by norm_cast : ( 1 : ℝ ) ≤ N ) ]

/-- The matched projection `Q_i = Wᴴ R_i W` on `H`. -/
noncomputable def Qop (W : Matrix (Ksp d N) (Fin d) ℂ) (i : Fin N) : Matrix (Fin d) (Fin d) ℂ :=
  (Wᴴ * reg i : Matrix (Fin d) (Ksp d N) ℂ) * W

/-
`W Q_i = R_i W` when `W` is an isometry onto `F = W Wᴴ` and `F` commutes with `R_i`.
-/
lemma WQ_eq (W : Matrix (Ksp d N) (Fin d) ℂ) (hWiso : Wᴴ * W = 1)
    (F : Matrix (Ksp d N) (Ksp d N) ℂ) (hWF : W * Wᴴ = F)
    (hFcomm : ∀ i, reg i * F = F * reg i) (i : Fin N) :
    (W * Qop W i : Matrix (Ksp d N) (Fin d) ℂ) = reg i * W := by
  unfold Qop; simp +decide [ ← Matrix.mul_assoc, hWF] ;
  rw [ ← hFcomm i, ← hWF, Matrix.mul_assoc ];
  rw [ Matrix.mul_assoc, hWiso, Matrix.mul_one ]

/-
`Q_i = Wᴴ R_i W` is a projection.
-/
lemma Qop_isProj (W : Matrix (Ksp d N) (Fin d) ℂ) (hWiso : Wᴴ * W = 1)
    (F : Matrix (Ksp d N) (Ksp d N) ℂ) (hWF : W * Wᴴ = F)
    (hFcomm : ∀ i, reg i * F = F * reg i) (i : Fin N) :
    IsProj (Qop W i) := by
  constructor;
  · unfold Qop; simp +decide [ Matrix.IsHermitian, Matrix.mul_assoc] ;
    rw [ reg_isProj i |>.1 ];
  · unfold Qop; simp +decide [ ← Matrix.mul_assoc ] ;
    simp +decide [ Matrix.mul_assoc, hWF, hFcomm i ];
    simp +decide [ ← hWF];
    simp +decide [ ← Matrix.mul_assoc, hWiso, reg_isProj i |>.2 ]

/-
The `Q_i = Wᴴ R_i W` pairwise commute.
-/
lemma Qop_comm (W : Matrix (Ksp d N) (Fin d) ℂ) (hWiso : Wᴴ * W = 1)
    (F : Matrix (Ksp d N) (Ksp d N) ℂ) (hWF : W * Wᴴ = F)
    (hFcomm : ∀ i, reg i * F = F * reg i) (i j : Fin N) :
    Qop W i * Qop W j = Qop W j * Qop W i := by
  unfold Qop;
  simp_all +decide [ ← Matrix.mul_assoc ];
  simp_all +decide [ Matrix.mul_assoc, ← hWF ];
  simp_all +decide [ ← Matrix.mul_assoc, reg_comm ]

/-
The displacement bound for a single index, given the isometry `W` close to `V`.
-/
lemma disp_bound (P : Fin N → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i))
    (ε : ℝ) (hε : 0 ≤ ε) (hcomm : ∀ i j, hsNorm d (comm (P i) (P j)) ≤ ε)
    (W : Matrix (Ksp d N) (Fin d) ℂ) (hWiso : Wᴴ * W = 1)
    (F : Matrix (Ksp d N) (Ksp d N) ℂ) (hWF : W * Wᴴ = F)
    (hFcomm : ∀ i, reg i * F = F * reg i)
    (hVW : hsNorm d (dil P - W) ≤ 2 * Real.sqrt (2 * (N : ℝ) * ((N : ℝ) - 1)) * ε) (i : Fin N) :
    hsNorm d (P i - Qop W i) ≤ 8 * (N : ℝ) * ε := by
  -- By the triangle inequality and the contraction properties, we can bound the norm of the difference.
  have h_diff_bound : hsNorm d (reg i * W - W * P i) ≤ 2 * hsNorm d (dil P - W) + hsNorm d (reg i * dil P - dil P * P i) := by
    have h_diff_bound : hsNorm d (reg i * W - W * P i) ≤ hsNorm d ((reg i * (W - dil P))) + hsNorm d ((reg i * dil P - dil P * P i)) + hsNorm d (((dil P - W) * P i)) := by
      have h_diff_bound : reg i * W - W * P i = reg i * (W - dil P) + (reg i * dil P - dil P * P i) + (dil P - W) * P i := by
        abel_nf;
        norm_num [ Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc ] ; abel_nf;
      rw [h_diff_bound];
      exact le_trans ( hsNorm_triangle _ _ ) ( add_le_add ( hsNorm_triangle _ _ ) le_rfl );
    have h_contraction : hsNorm d (reg i * (W - dil P)) ≤ hsNorm d (W - dil P) ∧ hsNorm d ((dil P - W) * P i) ≤ hsNorm d (dil P - W) := by
      exact ⟨ hsNorm_proj_left ( reg_isProj i ) _, hsNorm_proj_right ( hP i ) _ ⟩;
    linarith [ show hsNorm d ( W - dil P ) = hsNorm d ( dil P - W ) from by rw [ ← hsNorm_neg ] ; congr; ext; simp +decide [ sub_eq_neg_add ] ];
  -- By the properties of the norm and the triangle inequality, we can bound the norm of the difference.
  have h_diff_bound_final : hsNorm d (P i - Qop W i) ≤ hsNorm d (W * (Qop W i - P i)) := by
    rw [ ← hsNorm_neg, ← hsNorm_isom_left hWiso ] ; norm_num [ Matrix.mul_sub ] ;
  have h_diff_bound_final : hsNorm d (W * (Qop W i - P i)) ≤ hsNorm d (reg i * W - W * P i) := by
    rw [ Matrix.mul_sub, WQ_eq W hWiso F hWF hFcomm i ];
  have h_diff_bound_final : hsNorm d (reg i * dil P - dil P * P i) ≤ Real.sqrt (5 * (i : ℝ)) * ε := by
    have h_diff_bound_final : hsNormSq d (reg i * dil P - dil P * P i) ≤ 5 * (i : ℝ) * ε ^ 2 := by
      rw [ reg_dil_disp P hP i ];
      convert add_le_add ( Aop_sub_bound P hP ε hcomm i ) ( Aop_defect_bound P hP ε hcomm i ) using 1 ; ring;
    exact Real.sqrt_le_iff.mpr ⟨ by positivity, by rw [ mul_pow, Real.sq_sqrt <| by positivity ] ; linarith ⟩;
  have := sep_numeric ( show 0 < N from Fin.pos i ) ( i : ℝ ) ( Nat.cast_nonneg _ ) ( by linarith [ show ( i : ℝ ) + 1 ≤ N from mod_cast Nat.succ_le_of_lt i.2 ] );
  nlinarith

/-
**Theorem 1** (Hilbert–Schmidt separation of projections).
Let `P 0, …, P (N-1)` be projections on a `d`-dimensional Hilbert space `H = ℂ^d`, and assume that
all pairwise commutators are at most `ε` in the normalized Hilbert–Schmidt norm `‖·‖₂` (the
`d`-scaled HS norm).  Then there are pairwise commuting projections `Q 0, …, Q (N-1)` on `H` with
`‖P i - Q i‖₂ ≤ 8 N ε` for every `i`.
-/
theorem separation_of_projections
    (d N : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (P : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hP : ∀ i, IsProj (P i))
    (hcomm : ∀ i j, hsNorm d (comm (P i) (P j)) ≤ ε) :
    ∃ Q : Fin N → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, IsProj (Q i)) ∧
      (∀ i j, Q i * Q j = Q j * Q i) ∧
      (∀ i, hsNorm d (P i - Q i) ≤ 8 * (N : ℝ) * ε) := by
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Ksp d N) (Ksp d N) ℂ, IsProj E ∧ E.trace.re = (d : ℝ) ∧ (∀ i, reg i * E = E * reg i) ∧ hsNormSq d (Erange P - E) ≤ 8 * (N : ℝ) * ((N : ℝ) - 1) * ε ^ 2 := by
    have h_comm_reg_Erange : ∀ i, hsNormSq d (comm (reg i) (Erange P)) ≤ 8 * (i : ℝ) * ε ^ 2 := by
      intro i
      have := comm_reg_Erange P hP i
      have := Aop_defect_bound P hP ε hcomm i
      simp_all +decide [ hsNormSq ];
      ring_nf at *; linarith;
    have h_sum_comm_reg_Erange : ∑ i : Fin N, hsNormSq d (comm (reg i) (Erange P)) ≤ 4 * (N : ℝ) * ((N : ℝ) - 1) * ε ^ 2 := by
      convert Finset.sum_le_sum fun i _ => h_comm_reg_Erange i using 1 ; ring;
      rw [ ← Finset.sum_mul _ _ _ ] ; rw [ ← Finset.mul_sum _ _ _ ] ; rw [ sum_fin_cast ] ; ring;
    obtain ⟨F, hFproj, hFtr, hFcomm, hEF⟩ := lemma4_diag d (reg) reg_isDiag reg_isProj (Erange P) (Erange_isProj P hP) (Erange_trace P hP);
    exact ⟨ F, hFproj, hFtr, hFcomm, by linarith ⟩;
  obtain ⟨W, hW⟩ : ∃ W : Matrix (Ksp d N) (Fin d) ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = E ∧ hsNorm d (dil P - W) ≤ 2 * Real.sqrt (2 * (N : ℝ) * ((N : ℝ) - 1)) * ε := by
    obtain ⟨W, hW⟩ : ∃ W : Matrix (Ksp d N) (Fin d) ℂ, Wᴴ * W = 1 ∧ W * Wᴴ = E ∧ hsNorm d (dil P - W) ≤ hsNorm d (dil P * (dil P)ᴴ - E) := by
      apply lemma5 d (dil P) (dil_isometry P hP) E hE.left (by
      aesop);
    refine' ⟨ W, hW.1, hW.2.1, hW.2.2.trans _ ⟩;
    convert Real.sqrt_le_sqrt hE.2.2.2 using 1 ; ring;
    rw [ show - ( N * ε ^ 2 * 8 : ℝ ) + N ^ 2 * ε ^ 2 * 8 = ( - ( N * 2 ) + N ^ 2 * 2 ) * ε ^ 2 * 4 by ring, Real.sqrt_mul', Real.sqrt_mul' ] <;> norm_num ; ring;
    · exact Or.inl ( by rw [ Real.sqrt_sq hε ] );
    · positivity;
  use fun i => Qop W i;
  exact ⟨ fun i => Qop_isProj W hW.1 E hW.2.1 hE.2.2.1 i, fun i j => Qop_comm W hW.1 E hW.2.1 hE.2.2.1 i j, fun i => disp_bound P hP ε hε hcomm W hW.1 E hW.2.1 hE.2.2.1 hW.2.2 i ⟩

end SepProj