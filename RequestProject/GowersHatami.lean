import Mathlib

/-!
# The Gowers-Hatami Theorem

This file formalizes the Gowers-Hatami theorem on approximate representations of finite groups.

## Main Result

If `G` is a finite group and `φ : G → unitary (H →L[ℂ] H)` is an ε-approximate homomorphism
in the Hilbert-Schmidt norm (i.e., `𝔼_{x,y} ‖φ(xy) - φ(x)φ(y)‖²_HS ≤ ε`), then there exists
a genuine unitary representation `ψ` of `G` on a larger Hilbert space `K` and an isometry
`V : H →ₗᵢ[ℂ] K` such that `𝔼_x ‖φ(x) - V† ∘ ψ(x) ∘ V‖²_HS ≤ ε`.

## Proof Strategy

The proof constructs:
- `K = G → H` (with L² inner product), i.e., `PiLp 2 (fun _ : G => H)`
- `ψ(g)` = right regular representation: `(ψ(g) f)(x) = f(x * g)`
- `V : H → K` defined by `(V v)(g) = (1/√|G|) • φ(g) v`

The key estimate uses Jensen's inequality for the HS norm and unitary invariance.

## References

* T. Gowers, O. Hatami, "Inverse and stability theorems for approximate representations of
  finite groups", 2017.
-/

noncomputable section

open scoped ComplexInnerProductSpace
open Finset

variable {d : ℕ}

/-- The Hilbert space H = ℂ^d. -/
abbrev H (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-! ### Hilbert-Schmidt norm -/

/-- The Hilbert-Schmidt (Frobenius) norm squared of an endomorphism, defined as
`∑ i, ‖A(eᵢ)‖²` where `{eᵢ}` is the standard orthonormal basis. -/
def hsNormSq (A : H d →L[ℂ] H d) : ℝ :=
  ∑ i : Fin d, ‖A (EuclideanSpace.single i 1)‖ ^ 2


/-
Unitary invariance of HS norm: ‖U ∘ A‖²_HS = ‖A‖²_HS for unitary U.
-/
lemma hsNormSq_comp_unitary {A : H d →L[ℂ] H d} {U : H d →L[ℂ] H d}
    (hU : U ∈ unitary (H d →L[ℂ] H d)) :
    hsNormSq (U.comp A) = hsNormSq A := by
  -- Since U is unitary, we have ‖U(x)‖ = ‖x‖ for all x.
  have h_unitary_norm : ∀ x : H d, ‖U x‖ = ‖x‖ := by
    intro x;
    grind +suggestions;
  exact Finset.sum_congr rfl fun i _ => by rw [ ContinuousLinearMap.comp_apply, h_unitary_norm ] ;


/-! ### Setup: Group, approximate representation, defect -/

variable (G : Type*) [Group G] [Fintype G] [DecidableEq G]

/-- The defect of an approximate homomorphism φ:
  `defect φ = 𝔼_{x,y} ‖φ(xy) - φ(x)φ(y)‖²_HS`. -/
def approxRepDefect (φ : G → H d →L[ℂ] H d) : ℝ :=
  ((Fintype.card G : ℝ) ^ 2)⁻¹ *
    ∑ x : G, ∑ y : G, hsNormSq (φ (x * y) - (φ x).comp (φ y))

/-! ### The larger Hilbert space K and the construction -/

/-- The larger Hilbert space `K = L²(G, H)`. -/
abbrev K (G : Type*) (d : ℕ) := PiLp 2 (fun (_ : G) => H d)

/-- The right regular representation on K: `(ψ g f)(x) = f(x * g)`. -/
def rightRegular (g : G) : K G d →ₗ[ℂ] K G d where
  toFun f := (WithLp.equiv 2 _).symm (fun x => f (x * g))
  map_add' _ _ := by ext; simp [WithLp.equiv]
  map_smul' _ _ := by ext; simp [WithLp.equiv]

/-- The right regular representation is a group homomorphism (a representation). -/
def rightRegularRep : Representation ℂ G (K G d) where
  toFun := rightRegular G
  map_one' := by
    ext f x; simp [rightRegular, WithLp.equiv]
  map_mul' g₁ g₂ := by
    ext f x; simp [rightRegular, WithLp.equiv, mul_assoc]

/-- Scaling constant c = 1/√|G| used in the Gowers-Hatami embedding. -/
def ghScale (G : Type*) [Fintype G] : ℂ :=
  (((Fintype.card G : ℝ).sqrt)⁻¹ : ℝ)

/-- The embedding V : H → K defined by `(V v)(g) = (1/√|G|) • φ(g) v`. -/
def gowersHatamiV (φ : G → H d →L[ℂ] H d) : H d →ₗ[ℂ] K G d where
  toFun v := (WithLp.equiv 2 _).symm
    (fun g => (ghScale G) • (φ g v))
  map_add' v₁ v₂ := by
    ext g
    simp [WithLp.equiv, map_add, smul_add, ghScale]
  map_smul' c v := by
    apply (WithLp.equiv 2 _).injective
    funext g
    show (ghScale G) • (φ g (c • v)) = c • ((ghScale G) • (φ g v))
    rw [map_smul, smul_comm]

omit [DecidableEq G] in
/-
V preserves inner products when φ takes values in unitaries.
-/
lemma gowersHatamiV_inner (φ : G → ↥(unitary (H d →L[ℂ] H d)))
    (v₁ v₂ : H d) :
    @inner ℂ _ _ (gowersHatamiV G (fun g => (φ g : H d →L[ℂ] H d)) v₁)
                   (gowersHatamiV G (fun g => (φ g : H d →L[ℂ] H d)) v₂)
    = @inner ℂ _ _ v₁ v₂ := by
  unfold gowersHatamiV;
  simp +decide [ ghScale, inner ];
  -- Since $\varphi(g)$ is unitary, we have $\langle \varphi(g) v_1, \varphi(g) v_2 \rangle = \langle v_1, v_2 \rangle$.
  have h_unitary : ∀ g : G, ∑ x : Fin d, (starRingEnd ℂ) ((φ g).val v₁ x) * ((φ g).val v₂ x) = ∑ x : Fin d, (starRingEnd ℂ) (v₁ x) * (v₂ x) := by
    intro g;
    have h_unitary : ∀ (v₁ v₂ : H d), ∑ x : Fin d, (starRingEnd ℂ) ((φ g).val v₁ x) * ((φ g).val v₂ x) = ∑ x : Fin d, (starRingEnd ℂ) (v₁ x) * (v₂ x) := by
      intro v₁ v₂
      have h_unitary : (φ g).val.adjoint.comp (φ g).val = 1 := by
        have := φ g |>.2.1;
        convert this using 1
      have h_unitary : ∀ (v₁ v₂ : H d), inner ℂ ((φ g).val v₁) ((φ g).val v₂) = inner ℂ v₁ v₂ := by
        intro v₁ v₂; replace h_unitary := congr_arg ( fun f => inner ℂ v₁ ( f v₂ ) ) h_unitary; simp_all +decide [] ;
        rw [ ← h_unitary, ContinuousLinearMap.adjoint_inner_right ];
      convert h_unitary v₁ v₂ using 1;
      · exact Finset.sum_congr rfl fun _ _ => by rw [ mul_comm ] ; rfl;
      · ac_rfl;
    exact h_unitary v₁ v₂;
  simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
  simp_all +decide [ ← Finset.mul_sum _ _ _ ];
  field_simp;
  rw [ sq, Complex.ext_iff ] ; norm_num [ Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im ]

/-
V is a linear isometry.
-/
def gowersHatamiIso (φ : G → ↥(unitary (H d →L[ℂ] H d))) :
    H d →ₗᵢ[ℂ] K G d where
  toLinearMap := gowersHatamiV G (fun g => (φ g : H d →L[ℂ] H d))
  norm_map' v := by
    have := gowersHatamiV_inner G φ v v;
    have h_norm : ‖(gowersHatamiV G (fun g => (φ g : H d →L[ℂ] H d)) v)‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [ ← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, this ];
    rwa [ sq_eq_sq₀ ( norm_nonneg _ ) ( norm_nonneg _ ) ] at h_norm

/-! ### Key lemma: adjoint of isometry -/

/-
V†(Vv) = v for a linear isometry V.
-/
lemma adjoint_isometry_apply {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →ₗᵢ[ℂ] F) (v : E) :
    V.toContinuousLinearMap.adjoint (V v) = v := by
  refine' ext_inner_left ℂ fun w => _;
  simp +decide [ ContinuousLinearMap.adjoint_inner_right ]

/-
‖a - V†w‖ ≤ ‖Va - w‖ for an isometry V.
This follows from V†V = I and contractivity of V†.
-/
lemma norm_sub_adjoint_le {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →ₗᵢ[ℂ] F) (a : E) (w : F) :
    ‖a - V.toContinuousLinearMap.adjoint w‖ ≤ ‖V a - w‖ := by
  have h_norm_le : ‖V.toContinuousLinearMap.adjoint (V a - w)‖ ≤ ‖V a - w‖ := by
    exact le_trans ( ContinuousLinearMap.le_opNorm _ _ ) ( mul_le_of_le_one_left ( norm_nonneg _ ) ( by simp +decide [ LinearIsometry.norm_toContinuousLinearMap_le ] ) );
  convert h_norm_le using 2;
  rw [ map_sub, adjoint_isometry_apply ]

/-! ### Pointwise computation of V(φ(g)v) - ψ(g)(Vv) -/

omit [DecidableEq G] in
/-
The x-th component of `V(φ(g)v) - ψ(g)(Vv)` is
`ghScale G • (φ(x)φ(g) - φ(xg))v`.
-/
lemma gowersHatami_diff_apply
    (φ : G → H d →L[ℂ] H d) (g : G) (v : H d) (x : G) :
    (gowersHatamiV G φ ((φ g) v) - (rightRegular G g) (gowersHatamiV G φ v)) x =
    (ghScale G) • ((φ x).comp (φ g) - φ (x * g)) v := by
  simp [gowersHatamiV, rightRegular];
  rw [ smul_sub ]

omit [DecidableEq G] in
/-
HS norm bound for a single g:
`‖φ(g) - V†ψ(g)V‖²_HS ≤ (1/|G|) ∑_x ‖φ(xg) - φ(x)φ(g)‖²_HS`
-/
lemma gowersHatami_per_g_bound
    (φ : G → ↥(unitary (H d →L[ℂ] H d))) (g : G) :
    hsNormSq ((φ g : H d →L[ℂ] H d) -
      (gowersHatamiIso G φ).toContinuousLinearMap.adjoint.comp
        ((rightRegularRep G g).toContinuousLinearMap.comp
          (gowersHatamiIso G φ).toContinuousLinearMap)) ≤
    ((Fintype.card G : ℝ))⁻¹ *
      ∑ x : G, hsNormSq ((φ (x * g) : H d →L[ℂ] H d) -
        ((φ x : H d →L[ℂ] H d)).comp (φ g : H d →L[ℂ] H d)) := by
  have h_sum : ∀ i : Fin d, ‖(↑(φ g) - (ContinuousLinearMap.adjoint (gowersHatamiIso G φ).toContinuousLinearMap).comp ((LinearMap.toContinuousLinearMap ((rightRegularRep G) g)).comp (gowersHatamiIso G φ).toContinuousLinearMap)) (EuclideanSpace.single i 1)‖ ^ 2 ≤ (1 / (Fintype.card G : ℝ)) * ∑ x : G, ‖((φ x).val.comp (φ g).val - (φ (x * g)).val) (EuclideanSpace.single i 1)‖ ^ 2 := by
    intro i
    have h_pointwise : ‖(gowersHatamiIso G φ).toContinuousLinearMap ((φ g : H d →L[ℂ] H d) (EuclideanSpace.single i 1)) - (LinearMap.toContinuousLinearMap ((rightRegularRep G) g)).comp (gowersHatamiIso G φ).toContinuousLinearMap (EuclideanSpace.single i 1)‖ ^ 2 = (1 / (Fintype.card G : ℝ)) * ∑ x : G, ‖((φ x).val.comp (φ g).val - (φ (x * g)).val) (EuclideanSpace.single i 1)‖ ^ 2 := by
      have h_pointwise : ‖(gowersHatamiIso G φ).toContinuousLinearMap ((φ g : H d →L[ℂ] H d) (EuclideanSpace.single i 1)) - (LinearMap.toContinuousLinearMap ((rightRegularRep G) g)).comp (gowersHatamiIso G φ).toContinuousLinearMap (EuclideanSpace.single i 1)‖ ^ 2 = ∑ x : G, ‖(gowersHatamiIso G φ).toContinuousLinearMap ((φ g : H d →L[ℂ] H d) (EuclideanSpace.single i 1)) x - (LinearMap.toContinuousLinearMap ((rightRegularRep G) g)).comp (gowersHatamiIso G φ).toContinuousLinearMap (EuclideanSpace.single i 1) x‖ ^ 2 := by
        have h_pointwise : ∀ (f : K G d), ‖f‖ ^ 2 = ∑ x : G, ‖f x‖ ^ 2 := by
          simp +decide [ PiLp.norm_eq_of_L2 ];
          exact fun f => Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _;
        convert h_pointwise _ using 2;
      simp_all +decide [ gowersHatamiIso, gowersHatamiV, rightRegularRep, rightRegular ];
      simp +decide [ ← smul_sub, norm_smul, ghScale ];
      simp +decide [ mul_pow, Finset.mul_sum _ _ _, abs_of_nonneg, Real.sqrt_nonneg ];
    convert norm_sub_adjoint_le ( gowersHatamiIso G φ ) ( ( φ g : H d →L[ℂ] H d ) ( EuclideanSpace.single i 1 ) ) ( ( LinearMap.toContinuousLinearMap ( rightRegularRep G g ) ).comp ( gowersHatamiIso G φ ).toContinuousLinearMap ( EuclideanSpace.single i 1 ) ) |> fun h => pow_le_pow_left₀ ( norm_nonneg _ ) h 2 using 1;
    exact h_pointwise.symm;
  convert Finset.sum_le_sum fun i _ => h_sum i using 1;
  simp +decide [ hsNormSq, Finset.mul_sum _ _ _ ];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ norm_sub_rev ] )

/-! ### Main theorem -/

omit [DecidableEq G] in
/-
**Gowers-Hatami Theorem**: If `φ : G → unitary(H →L[ℂ] H)` is an approximate
homomorphism with defect at most `ε`, then there exists a genuine representation `ψ` of `G`
on `K = L²(G, H)` and an isometry `V : H →ₗᵢ[ℂ] K` such that the average HS-distance
between `φ(g)` and `V† ∘ ψ(g) ∘ V` is at most `ε`.

More precisely:
  `𝔼_g ‖φ(g) - V† ∘ ψ(g) ∘ V‖²_HS ≤ ε`
where ψ is the right regular representation on K and V is the natural embedding.
-/
theorem gowers_hatami
    (φ : G → ↥(unitary (H d →L[ℂ] H d)))
    (ε : ℝ) (hε : approxRepDefect G (fun g => (φ g : H d →L[ℂ] H d)) ≤ ε) :
    ∃ (ψ : Representation ℂ G (K G d))
      (V : H d →ₗᵢ[ℂ] K G d),
    ((Fintype.card G : ℝ)⁻¹ *
      ∑ g : G, hsNormSq
        ((φ g : H d →L[ℂ] H d) -
         V.toContinuousLinearMap.adjoint.comp
           ((ψ g).toContinuousLinearMap.comp V.toContinuousLinearMap))) ≤ ε := by
  refine ⟨rightRegularRep G, gowersHatamiIso G φ, ?_⟩
  -- Step 1: Bound each term using gowersHatami_per_g_bound
  have h_per_g := fun g => gowersHatami_per_g_bound G φ g
  -- Step 2: Average over g and compare with defect
  refine' le_trans _ hε;
  convert mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun g _ => h_per_g g ) ( inv_nonneg.mpr ( Nat.cast_nonneg ( Fintype.card G ) ) ) using 1;
  unfold approxRepDefect;
  simp +decide only [pow_two, mul_inv, ← Finset.mul_sum _ _ _];
  rw [ Finset.sum_comm ] ; ring

end