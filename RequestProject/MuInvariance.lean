import RequestProject.Foundations
import RequestProject.PVMToMeasure

open scoped BigOperators ComplexOrder
open Matrix

/-!
# Approximate equivariance of the PVM and invariance of `μ` (`lem:mu-invariance`)

This file formalizes **Lemma `lem:mu-invariance`** of the paper *"Polynomial
Hilbert–Schmidt stability of the lamplighter group"*.

## Mathematical content

Fix a unitary `T` and a finite family of commuting Hermitian involutions
`B_i` (`i` in some interval).  The projection-valued measure on the full shift
attaches to a binary string `x` the *atom*
`E_⟦x⟧ = ∏_i ½(I + (-1)^{x_i} B_i)`.
Conjugating by `T` and using `T* T = 1` gives
`T* E_⟦x⟧ T = ∏_i ½(I + (-1)^{x_i} T* B_i T)`,
while the shifted atom is `E_{L⟦x⟧} = ∏_i ½(I + (-1)^{x_i} B_{i+1})`.

The lemma states the *approximate equivariance* bound
`∑_x ‖ T* E_⟦x⟧ T − E_{L⟦x⟧} ‖²_HS  ≤  (n/2) · ∑_j ‖ T* B_j T − B_{j+1} ‖²_HS`,
where `n` is the number of factors.  Combined with the standing assumption
`‖ T* B_j T − B_{j+1} ‖²_HS ≤ ε'` this is the paper's `ε'' = O(M² ε')` bound.
The approximate invariance of `μ` then follows from `lem:PVM-to-meas`
(`pvm_to_meas_le`).

## Proof strategy

We work with two abstract families `C, D : Fin n → Matrix ι ι ℂ` of Hermitian
involutions (with `D` commuting) playing the roles of `C_i = T* B_i T` and
`D_i = B_{i+1}`, and the *atom* `atom C x = ∏_i ½(I + (-1)^{x_i} C_i)`.

The core estimate `mu_sqrt_bound` is proved by **induction on the number of
factors**, peeling the first factor `i = 0`.  Writing
`atom C x − atom D x = (p₀ − q₀)·(tail-D-atom) + p₀·(tail-C-atom − tail-D-atom)`
(where `p₀ = ½(I+(-1)^{x₀}C₀)`, `q₀ = ½(I+(-1)^{x₀}D₀)`), the L²-triangle
inequality (`normHS_l2_add_le`) splits the defect into two pieces, each handled
by a **Pythagoras identity** for projection-valued measures (`pyth_left`,
`pyth_right`): summing `‖G·M‖²` (resp. `‖M·G‖²`) over a family `G` of Hermitian
idempotents with `∑ G = 1` recovers `‖M‖²`.  This yields the recursion
`√Sₙ ≤ (1/√2)‖C₀−D₀‖ + √Sₙ₋₁`, hence the linear-in-`n` (polynomial) constant,
avoiding any exponential blow-up.
-/

namespace LamplighterStability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The projection factors `½(I + (-1)^b B)` -/

/-- The sign `(-1)^b` as a complex number: `+1` for `false` (bit `0`), `-1` for
`true` (bit `1`). -/
def signC (b : Bool) : ℂ := if b then -1 else 1

@[simp] lemma signC_false : signC false = 1 := rfl
@[simp] lemma signC_true : signC true = -1 := rfl

lemma signC_sq (b : Bool) : signC b * signC b = 1 := by
  cases b <;> simp [signC]

/-- The factor `½(I + (-1)^b B)`.  For `B` a Hermitian involution this is the
spectral projection onto the `(-1)^b`-eigenspace of `B`. -/
noncomputable def proj (B : Matrix ι ι ℂ) (b : Bool) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • (1 + signC b • B)

/-
`proj B` is Hermitian when `B` is.
-/
omit [Fintype ι] in
lemma proj_isHermitian {B : Matrix ι ι ℂ} (hB : B.IsHermitian) (b : Bool) :
    (proj B b).IsHermitian := by
      unfold proj;
      cases b <;> simp_all +decide [ Matrix.IsHermitian, Matrix.conjTranspose_smul ]

/-
`proj B b` is idempotent when `B² = 1`.
-/
lemma proj_isIdempotent {B : Matrix ι ι ℂ} (hB2 : B * B = 1) (b : Bool) :
    IsIdempotentElem (proj B b) := by
      unfold proj;
      simp +decide [ IsIdempotentElem, mul_add, add_mul, smul_smul, hB2 ];
      ext i j; norm_num; ring;
      rw [ show signC b ^ 2 = 1 by cases b <;> simp +decide [ signC ] ] ; ring

/-
The two factors sum to the identity: `½(I−B) + ½(I+B) = I`.
-/
omit [Fintype ι] in
lemma proj_add (B : Matrix ι ι ℂ) : proj B true + proj B false = 1 := by
  ext i j; simp +decide [ proj, signC ] ; ring;

/-
Conjugation distributes through a single factor: `T*·proj B b·T = proj (T*BT) b`.
-/
lemma proj_conj {T B : Matrix ι ι ℂ} (hT : star T * T = 1) (b : Bool) :
    proj (star T * B * T) b = star T * proj B b * T := by
      unfold proj;
      simp +decide [ mul_add, add_mul, mul_assoc, hT ]

/-
Two factors commute when the underlying matrices commute.
-/
lemma proj_commute {B B' : Matrix ι ι ℂ} (h : Commute B B') (b b' : Bool) :
    Commute (proj B b) (proj B' b') := by
      unfold proj;
      simp +decide [ Commute ];
      simp +decide [ SemiconjBy, mul_add, add_mul, h.eq ];
      module

/-! ## Atoms: ordered products of the projection factors -/

/-- The atom `atom C x = ∏_i ½(I + (-1)^{x_i} C_i)`, an ordered product
(matrices do not commute in general). -/
noncomputable def atom {n : ℕ} (C : Fin n → Matrix ι ι ℂ) (x : Fin n → Bool) :
    Matrix ι ι ℂ :=
  (List.ofFn (fun i => proj (C i) (x i))).prod

@[simp] lemma atom_zero (C : Fin 0 → Matrix ι ι ℂ) (x : Fin 0 → Bool) :
    atom C x = 1 := by simp [atom]

/-
Peel off the first factor.
-/
lemma atom_succ {n : ℕ} (C : Fin (n + 1) → Matrix ι ι ℂ) (x : Fin (n + 1) → Bool) :
    atom C x = proj (C 0) (x 0) * atom (fun i => C i.succ) (fun i => x i.succ) := by
  unfold atom;
  simp +decide [ List.ofFn_eq_map ]

/-
The first factor commutes with the rest of an atom, when the family commutes.
-/
lemma commute_proj_atom {n : ℕ} {C : Fin (n + 1) → Matrix ι ι ℂ}
    (hCc : ∀ i k, Commute (C i) (C k)) (x : Fin (n + 1) → Bool) :
    Commute (proj (C 0) (x 0)) (atom (fun i => C i.succ) (fun i => x i.succ)) := by
  refine' Commute.list_prod_right _ _ _;
  grind +suggestions

/-
An atom of a commuting family of Hermitian involutions is Hermitian.
-/
lemma atom_isHermitian {n : ℕ} {C : Fin n → Matrix ι ι ℂ}
    (hCh : ∀ i, (C i).IsHermitian) (hCc : ∀ i k, Commute (C i) (C k))
    (x : Fin n → Bool) : (atom C x).IsHermitian := by
      induction' n with n ih <;> simp_all +decide [ atom_succ ];
      rw [ Matrix.IsHermitian ];
      rw [ Matrix.conjTranspose_mul, proj_isHermitian ( hCh 0 ) ( x 0 ) |> Matrix.IsHermitian.eq ];
      rw [ Matrix.IsHermitian.eq ( ih ( fun i => hCh i.succ ) ( fun i k => hCc _ _ ) _ ) ];
      exact Commute.symm ( commute_proj_atom hCc x )

/-
An atom of a commuting family of Hermitian involutions is idempotent.
-/
lemma atom_isIdempotent {n : ℕ} {C : Fin n → Matrix ι ι ℂ}
    (hC2 : ∀ i, C i * C i = 1) (hCc : ∀ i k, Commute (C i) (C k))
    (x : Fin n → Bool) : IsIdempotentElem (atom C x) := by
      induction' n with n ih;
      · exact one_mul _;
      · convert IsIdempotentElem.mul_of_commute ( commute_proj_atom hCc x ) _ _ using 1;
        · exact atom_succ C x;
        · exact proj_isIdempotent ( hC2 0 ) _;
        · exact ih ( fun i => hC2 _ ) ( fun i k => hCc _ _ ) _

/-
The atoms form a resolution of the identity: `∑_x atom C x = 1`.
(No commutativity is needed — it is the distributive expansion of
`∏_i (proj C_i false + proj C_i true) = ∏_i I = I`.)
-/
lemma sum_atom_eq_one {n : ℕ} (C : Fin n → Matrix ι ι ℂ) :
    ∑ x : Fin n → Bool, atom C x = 1 := by
      induction' n with n ih <;> simp_all +decide [ atom_succ ];
      -- By Fintype.sum_equiv, we can rewrite the sum over Fin (n + 1) → Bool as a sum over Bool × (Fin n → Bool).
      have h_sum_equiv : ∑ x : Fin (n + 1) → Bool, proj (C 0) (x 0) * atom (fun i => C i.succ) (fun i => x i.succ) = ∑ b : Bool, ∑ t : Fin n → Bool, proj (C 0) b * atom (fun i => C i.succ) t := by
        rw [ ← Finset.sum_product' ];
        refine' Finset.sum_bij ( fun x _ => ( x 0, fun i => x i.succ ) ) _ _ _ _ <;> simp +decide;
        · exact fun a₁ a₂ h₁ h₂ => funext fun i => by induction i using Fin.inductionOn <;> simp_all +decide [ funext_iff ] ;
        · exact ⟨ fun b => ⟨ Fin.cons false b, rfl, rfl ⟩, fun b => ⟨ Fin.cons true b, rfl, rfl ⟩ ⟩;
      simp_all +decide [ ← Finset.mul_sum _ _ _, proj_add ]

/-
Conjugation distributes over an atom: `T*·(atom C x)·T = atom (T*·C·T) x`.
-/
lemma atom_conj {n : ℕ} {T : Matrix ι ι ℂ} (hT : star T * T = 1) (hT' : T * star T = 1)
    (C : Fin n → Matrix ι ι ℂ) (x : Fin n → Bool) :
    atom (fun i => star T * C i * T) x = star T * atom C x * T := by
      induction' n with n ih;
      · simp +decide [ atom_zero, hT ];
      · rw [ atom_succ, atom_succ ];
        rw [ proj_conj hT, ih ];
        grind +revert

/-! ## Auxiliary facts on the normalized trace and norm -/

/-
Additivity of the normalized trace over a finite sum.
-/
omit [DecidableEq ι] in
lemma ntrace_sum {σ : Type*} (s : Finset σ) (f : σ → Matrix ι ι ℂ) :
    ntrace (∑ i ∈ s, f i) = ∑ i ∈ s, ntrace (f i) := by
      unfold ntrace;
      simp +decide [ ← Finset.mul_sum _ _ _ ]

/-! ## Pythagoras identities for projection-valued measures -/

/-
**Left Pythagoras.** For a family `G` of Hermitian idempotents summing to the
identity, `∑_s ‖G_s · M‖²_HS = ‖M‖²_HS`.
-/
lemma pyth_left {σ : Type*} [Fintype σ] {G : σ → Matrix ι ι ℂ}
    (hGh : ∀ s, (G s).IsHermitian) (hGi : ∀ s, IsIdempotentElem (G s))
    (hsum : ∑ s, G s = 1) (M : Matrix ι ι ℂ) :
    ∑ s, normHS (G s * M) ^ 2 = normHS M ^ 2 := by
      simp +decide only [normHS_sq_eq_ntrace];
      convert ntrace_sum Finset.univ ( fun s => Mᴴ * G s * M ) using 1;
      · simp +decide [ Matrix.mul_assoc, ntrace_sum ];
        simp_all +decide [ IsIdempotentElem, Matrix.IsHermitian ];
        simp +decide only [← Matrix.mul_assoc, hGi];
      · rw [ ← ntrace_sum ];
        simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hsum ]

/-
**Right Pythagoras.** For a family `G` of Hermitian idempotents summing to the
identity, `∑_s ‖M · G_s‖²_HS = ‖M‖²_HS`.
-/
lemma pyth_right {σ : Type*} [Fintype σ] {G : σ → Matrix ι ι ℂ}
    (hGh : ∀ s, (G s).IsHermitian) (hGi : ∀ s, IsIdempotentElem (G s))
    (hsum : ∑ s, G s = 1) (M : Matrix ι ι ℂ) :
    ∑ s, normHS (M * G s) ^ 2 = normHS M ^ 2 := by
      convert pyth_left ( fun s => hGh s |> fun h => h.conjTranspose ) ( fun s => hGi s |> fun h => ?_ ) ?_ ( star M ) using 1;
      · simp +decide only [star];
        simp +decide only [normHS_sq_eq_ntrace];
        simp +decide [ Matrix.mul_assoc, Matrix.conjTranspose_mul ];
        simp +decide only [← Matrix.mul_assoc, ntrace_mul_comm];
      · simp +decide [ normHS_sq ];
        exact Or.inl ( Finset.sum_comm );
      · simp_all +decide [ IsIdempotentElem, Matrix.IsHermitian ];
      · simp_all +decide [ Matrix.IsHermitian ]

/-! ## The L²-triangle inequality (Minkowski) for `normHS` -/

/-
Minkowski's inequality for the `ℓ²`-aggregate of the Hilbert–Schmidt norm.
-/
omit [DecidableEq ι] in
lemma normHS_l2_add_le {σ : Type*} [Fintype σ] (f g : σ → Matrix ι ι ℂ) :
    Real.sqrt (∑ s, normHS (f s + g s) ^ 2)
      ≤ Real.sqrt (∑ s, normHS (f s) ^ 2) + Real.sqrt (∑ s, normHS (g s) ^ 2) := by
  rw [ Real.sqrt_le_iff ];
  -- Apply the triangle inequality to each term in the sum.
  have h_triangle : ∀ s, (normHS ((f s) + (g s))) ^ 2 ≤ (normHS (f s)) ^ 2 + 2 * (normHS (f s)) * (normHS (g s)) + (normHS (g s)) ^ 2 := by
    exact fun s => by nlinarith only [ normHS_nonneg ( f s + g s ), normHS_nonneg ( f s ), normHS_nonneg ( g s ), normHS_add_le ( f s ) ( g s ) ] ;
  refine' ⟨ by positivity, le_trans ( Finset.sum_le_sum fun _ _ => h_triangle _ ) _ ⟩;
  simp +decide only [Finset.sum_add_distrib];
  rw [ add_sq, Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ), Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ];
  simp +decide only [mul_assoc];
  rw [ ← Finset.mul_sum _ _ _, ← Real.sqrt_mul ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ];
  exact add_le_add_three le_rfl ( mul_le_mul_of_nonneg_left ( Real.le_sqrt_of_sq_le ( by simpa only [ sq, Finset.sum_mul _ _ _ ] using Finset.sum_mul_sq_le_sq_mul_sq _ _ _ ) ) zero_le_two ) le_rfl

/-! ## The core inductive bound -/

/-
Squared-norm form of the two-element resolution `{proj C₀ false, proj C₀ true}`:
the per-`x₀` defect sums to `½ ‖C₀ − D₀‖²`.
-/
lemma sum_bool_proj_sub_sq {C₀ D₀ : Matrix ι ι ℂ} :
    ∑ b : Bool, normHS (proj C₀ b - proj D₀ b) ^ 2 = (1 / 2) * normHS (C₀ - D₀) ^ 2 := by
  have h_diff_proj : ∀ b : Bool, normHS (proj C₀ b - proj D₀ b) = (1 / 2 : ℝ) * normHS (C₀ - D₀) := by
    intro b;
    convert normHS_smul ( signC b / 2 ) ( C₀ - D₀ ) using 1;
    · convert rfl using 2 ; ext i j ; unfold proj ; simp +decide [ div_eq_inv_mul ] ; ring;
    · cases b <;> norm_num [ signC ];
  rw [ Finset.sum_congr rfl fun b _ => by rw [ h_diff_proj b ] ] ; norm_num ; ring

/-
The `W₀` (first telescoping) term: summing over the cube, the part where the
first factor carries the difference reduces (via right-Pythagoras over the tail
`D`-atom resolution) to `½ ‖C₀ − D₀‖²`.
-/
lemma sum_f_term {n : ℕ} (C₀ D₀ : Matrix ι ι ℂ) {D : Fin n → Matrix ι ι ℂ}
    (hDh : ∀ i, (D i).IsHermitian) (hD2 : ∀ i, D i * D i = 1)
    (hDc : ∀ i k, Commute (D i) (D k)) :
    ∑ x : Fin (n + 1) → Bool,
        normHS ((proj C₀ (x 0) - proj D₀ (x 0)) * atom D (fun i => x i.succ)) ^ 2
      = (1 / 2) * normHS (C₀ - D₀) ^ 2 := by
  -- Reindex the sum over (Fin (n+1) → Bool) as ∑ b : Bool, ∑ t : Fin n → Bool, (term at Fin.cons b t).
  have h_reindex : ∑ x : Fin (n + 1) → Bool, normHS ((proj C₀ (x 0) - proj D₀ (x 0)) * atom D (fun i => x i.succ)) ^ 2 = ∑ b : Bool, ∑ t : Fin n → Bool, normHS ((proj C₀ b - proj D₀ b) * atom D t) ^ 2 := by
    rw [ ← Finset.sum_product' ];
    refine' Finset.sum_bij ( fun x _ => ( x 0, fun i => x i.succ ) ) _ _ _ _ <;> simp +decide;
    · exact fun a₁ a₂ h₁ h₂ => funext fun i => by induction i using Fin.inductionOn <;> simp_all +decide [ funext_iff ] ;
    · exact ⟨ fun b => ⟨ Fin.cons false b, rfl, rfl ⟩, fun b => ⟨ Fin.cons true b, rfl, rfl ⟩ ⟩;
  convert sum_bool_proj_sub_sq using 1;
  convert h_reindex using 2;
  convert pyth_right ( fun t => atom_isHermitian hDh hDc t ) ( fun t => atom_isIdempotent hD2 hDc t ) ( sum_atom_eq_one D ) ( proj C₀ ‹_› - proj D₀ ‹_› ) |> Eq.symm using 1

/-
The `U` (recursive telescoping) term: summing over the cube, the part where
the first projection factor multiplies the tail defect reduces (via
left-Pythagoras over the two-element resolution `{proj C₀ false, proj C₀ true}`)
to the tail problem.
-/
lemma sum_g_term {n : ℕ} {C₀ : Matrix ι ι ℂ} (hC₀h : C₀.IsHermitian)
    (hC₀2 : C₀ * C₀ = 1) (C D : Fin n → Matrix ι ι ℂ) :
    ∑ x : Fin (n + 1) → Bool,
        normHS (proj C₀ (x 0)
          * (atom C (fun i => x i.succ) - atom D (fun i => x i.succ))) ^ 2
      = ∑ t : Fin n → Bool, normHS (atom C t - atom D t) ^ 2 := by
  convert Finset.sum_congr rfl _ using 2;
  rotate_left;
  use fun x => normHS ( proj C₀ ( x 0 ) * ( atom C ( fun i => x i.succ ) - atom D ( fun i => x i.succ ) ) ) ^ 2;
  · exact fun _ _ => rfl;
  · have h_reindex : ∑ x : Fin (n + 1) → Bool, normHS (proj C₀ (x 0) * (atom C (fun i => x i.succ) - atom D (fun i => x i.succ))) ^ 2 = ∑ t : Fin n → Bool, ∑ b : Bool, normHS (proj C₀ b * (atom C t - atom D t)) ^ 2 := by
      rw [ ← Finset.sum_product' ];
      refine' Finset.sum_bij ( fun x _ => ( fun i => x i.succ, x 0 ) ) _ _ _ _ <;> simp +decide;
      · exact fun a₁ a₂ h₁ h₂ => funext fun i => by induction i using Fin.inductionOn <;> simp_all +decide [ funext_iff ] ;
      · exact fun a => ⟨ ⟨ Fin.cons false a, rfl, rfl ⟩, ⟨ Fin.cons true a, rfl, rfl ⟩ ⟩;
    rw [ h_reindex ];
    refine' Finset.sum_congr rfl fun t _ => _;
    have := pyth_left ( fun b => proj_isHermitian hC₀h b ) ( fun b => proj_isIdempotent hC₀2 b ) ( by simp +decide [ proj_add ] ) ( atom C t - atom D t ) ; simp_all +decide ;

/-
**Core estimate (square-root form).** For families `C, D : Fin n → Matrix`
of Hermitian involutions, with `D` commuting,
`√(∑_x ‖atom C x − atom D x‖²) ≤ (1/√2) · ∑_j ‖C_j − D_j‖`.
Proved by induction on `n`, peeling the first factor.
-/
lemma mu_sqrt_bound {n : ℕ} (C D : Fin n → Matrix ι ι ℂ)
    (hCh : ∀ i, (C i).IsHermitian) (hC2 : ∀ i, C i * C i = 1)
    (hDh : ∀ i, (D i).IsHermitian) (hD2 : ∀ i, D i * D i = 1)
    (hDc : ∀ i k, Commute (D i) (D k)) :
    Real.sqrt (∑ x : Fin n → Bool, normHS (atom C x - atom D x) ^ 2)
      ≤ (1 / Real.sqrt 2) * ∑ j, normHS (C j - D j) := by
  induction' n with n ih;
  · simp +decide [ atom_zero ];
  · have h_peel : ∀ x : Fin (n + 1) → Bool, atom C x - atom D x = (proj (C 0) (x 0) - proj (D 0) (x 0)) * atom (fun i => D i.succ) (fun i => x i.succ) + proj (C 0) (x 0) * (atom (fun i => C i.succ) (fun i => x i.succ) - atom (fun i => D i.succ) (fun i => x i.succ)) := by
      intro x; rw [ atom_succ, atom_succ ] ; simp +decide [ sub_mul, mul_sub ] ;
    have h_sqrt_sum : Real.sqrt (∑ x : Fin (n + 1) → Bool, normHS ((proj (C 0) (x 0) - proj (D 0) (x 0)) * atom (fun i => D i.succ) (fun i => x i.succ)) ^ 2) = (1 / Real.sqrt 2) * normHS (C 0 - D 0) := by
      convert congr_arg Real.sqrt ( sum_f_term ( C 0 ) ( D 0 ) ( fun i => hDh ( Fin.succ i ) ) ( fun i => hD2 ( Fin.succ i ) ) ( fun i k => hDc _ _ ) ) using 1;
      rw [ Real.sqrt_mul ( by positivity ), Real.sqrt_div ( by positivity ), Real.sqrt_sq ( normHS_nonneg _ ) ] ; norm_num;
    have h_sqrt_sum_g : Real.sqrt (∑ x : Fin (n + 1) → Bool, normHS (proj (C 0) (x 0) * (atom (fun i => C i.succ) (fun i => x i.succ) - atom (fun i => D i.succ) (fun i => x i.succ))) ^ 2) ≤ (1 / Real.sqrt 2) * ∑ j : Fin n, normHS (C j.succ - D j.succ) := by
      convert ih ( fun i => C i.succ ) ( fun i => D i.succ ) ( fun i => hCh _ ) ( fun i => hC2 _ ) ( fun i => hDh _ ) ( fun i => hD2 _ ) ( fun i k => hDc _ _ ) using 1;
      rw [ sum_g_term ( hCh 0 ) ( hC2 0 ) ];
    convert le_trans ( normHS_l2_add_le _ _ ) ( add_le_add h_sqrt_sum.le h_sqrt_sum_g ) using 1;
    · simp +decide only [h_peel];
    · rw [ Fin.sum_univ_succ ] ; ring!;

/-
**Core estimate.** `∑_x ‖atom C x − atom D x‖² ≤ (n/2) · ∑_j ‖C_j − D_j‖²`.
-/
lemma mu_invariance_bound {n : ℕ} (C D : Fin n → Matrix ι ι ℂ)
    (hCh : ∀ i, (C i).IsHermitian) (hC2 : ∀ i, C i * C i = 1)
    (hDh : ∀ i, (D i).IsHermitian) (hD2 : ∀ i, D i * D i = 1)
    (hDc : ∀ i k, Commute (D i) (D k)) :
    ∑ x : Fin n → Bool, normHS (atom C x - atom D x) ^ 2
      ≤ (n / 2 : ℝ) * ∑ j, normHS (C j - D j) ^ 2 := by
  have h_mu_sqrt_bound : Real.sqrt (∑ x : Fin n → Bool, normHS (atom C x - atom D x) ^ 2) ≤ (1 / Real.sqrt 2) * ∑ j, normHS (C j - D j) := by
    exact mu_sqrt_bound C D hCh hC2 hDh hD2 hDc
  have h_cauchy_schwarz : (∑ j : Fin n, normHS (C j - D j)) ^ 2 ≤ n * ∑ j : Fin n, normHS (C j - D j) ^ 2 := by
    convert ( Finset.sum_mul_sq_le_sq_mul_sq _ _ _ ) using 1;
    rotate_left;
    rotate_left;
    exact Fin n;
    all_goals try infer_instance;
    exacts [ Finset.univ, fun _ => 1, fun i => normHS ( C i - D i ), by simp +decide, by simp +decide ];
  rw [ Real.sqrt_le_iff ] at h_mu_sqrt_bound;
  norm_num [ mul_pow ] at * ; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_inv_cancel₀ ( ne_of_gt ( Real.sqrt_pos.mpr zero_lt_two ) ) ]

/-! ## Lemma `lem:mu-invariance` -/

/-
**Lemma `lem:mu-invariance` (approximate equivariance of the PVM).**

Let `T` be a unitary and `B : Fin (n+1) → Matrix ι ι ℂ` a family of commuting
Hermitian involutions (the spectral involutions `B_i`).  Write
`E_⟦x⟧ = atom (B ∘ castSucc) x` and `E_{L⟦x⟧} = atom (B ∘ succ) x` for the PVM
atom and its shift.  Then the squared Hilbert–Schmidt equivariance defect is
controlled by the per-generator defect:
`∑_x ‖ T* E_⟦x⟧ T − E_{L⟦x⟧} ‖²_HS ≤ (n/2) ∑_j ‖ T* B_j T − B_{j+1} ‖²_HS`.
-/
theorem mu_invariance_equivariance {n : ℕ}
    {T : Matrix ι ι ℂ} (hT : T ∈ unitary (Matrix ι ι ℂ))
    (B : Fin (n + 1) → Matrix ι ι ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i k, Commute (B i) (B k)) :
    ∑ x : Fin n → Bool,
        normHS (star T * atom (fun i : Fin n => B i.castSucc) x * T
          - atom (fun i : Fin n => B i.succ) x) ^ 2
      ≤ (n / 2 : ℝ) * ∑ j : Fin n,
          normHS (star T * B j.castSucc * T - B j.succ) ^ 2 := by
  obtain ⟨hTT, hTT'⟩ := hT;
  convert mu_invariance_bound ( fun i => star T * B i.castSucc * T ) ( fun i => B i.succ ) _ _ _ _ _ using 1;
  any_goals tauto;
  · exact Finset.sum_congr rfl fun _ _ => by rw [ atom_conj hTT hTT' ] ;
  · exact fun i => isHermitian_conj_unitary ( hBh _ );
  · grind

/-
**Lemma `lem:mu-invariance` (uniform `ε'` form).**

Under the standing assumption `‖ T* B_j T − B_{j+1} ‖²_HS ≤ ε'` for every `j`,
the equivariance defect is at most `n²/2 · ε' = O(M² ε')`.
-/
theorem mu_invariance_eps {n : ℕ}
    {T : Matrix ι ι ℂ} (hT : T ∈ unitary (Matrix ι ι ℂ))
    (B : Fin (n + 1) → Matrix ι ι ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i k, Commute (B i) (B k))
    {eps : ℝ}
    (hsmall : ∀ j : Fin n, normHS (star T * B j.castSucc * T - B j.succ) ^ 2 ≤ eps) :
    ∑ x : Fin n → Bool,
        normHS (star T * atom (fun i : Fin n => B i.castSucc) x * T
          - atom (fun i : Fin n => B i.succ) x) ^ 2
      ≤ (n ^ 2 / 2 : ℝ) * eps := by
  convert mu_invariance_equivariance hT B hBh hB2 hBc |> le_trans <| _ using 1;
  refine' le_trans ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun _ _ => hsmall _ ) ( by positivity ) ) _ ; norm_num ; ring_nf ; norm_num

/-
**Lemma `lem:mu-invariance` (invariance of the induced measure `μ`).**

The probability measure `μ(b) = tr(E_b)` induced by the PVM (so that
`μ(⟦x⟧) = ntrace (E_⟦x⟧)` and `μ(L⟦x⟧) = ntrace (E_{L⟦x⟧})`) is
`(M-1, ε'')`-invariant: its total-variation defect under the shift is bounded by
the same `ε'' = (n/2) ∑_j ‖T* B_j T − B_{j+1}‖²` that controls the equivariance
defect.  This follows from the equivariance bound (`mu_invariance_equivariance`)
together with `lem:PVM-to-meas` (`pvm_to_meas_le`).
-/
theorem mu_invariance_measure {n : ℕ}
    {T : Matrix ι ι ℂ} (hT : T ∈ unitary (Matrix ι ι ℂ))
    (B : Fin (n + 1) → Matrix ι ι ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i k, Commute (B i) (B k)) :
    ∑ x : Fin n → Bool,
        |ntrace (atom (fun i : Fin n => B i.castSucc) x)
          - ntrace (atom (fun i : Fin n => B i.succ) x)|
      ≤ (n / 2 : ℝ) * ∑ j : Fin n,
          normHS (star T * B j.castSucc * T - B j.succ) ^ 2 := by
  refine' pvm_to_meas_le hT _ _ _ _ _ _ _;
  · exact fun s => atom_isHermitian ( fun i => hBh _ ) ( fun i k => hBc _ _ ) _;
  · exact fun x => atom_isIdempotent ( fun i => hB2 _ ) ( fun i j => hBc _ _ ) _;
  · exact fun s => atom_isHermitian ( fun i => hBh _ ) ( fun i k => hBc _ _ ) _;
  · exact fun s => atom_isIdempotent ( fun i => hB2 _ ) ( fun i k => hBc _ _ ) _;
  · convert mu_invariance_equivariance hT B hBh hB2 hBc using 1;
    exact Finset.sum_congr rfl fun _ _ => by rw [ ← normHS_sub_comm ] ;

end LamplighterStability