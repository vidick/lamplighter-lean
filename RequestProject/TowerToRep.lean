import RequestProject.ProjectionTowers

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

/-!
# From projection towers to representations (`lem:tower_to_rep`)

This file formalizes **Lemma `lem:tower_to_rep`** ("From towers to
representations") of the paper *"Polynomial Hilbert–Schmidt stability of the
lamplighter group"*.

Given a *closed* projection tower `τ = (P₀, …, P_{j-1}; R)` and a sign pattern
`x : ℕ → Bool`, the operators
```
A_{τ,x} = ∑_{i<j} (-1)^{x_i} P_i + (I - P_τ),     T_τ = R*
```
define a unitary representation of the lamplighter group `Γ = ℤ/2 ≀ ℤ`.
Concretely we prove that `A := A_{τ,x}` is a Hermitian involution (`A² = 1`,
hence unitary), `T := R*` is unitary, and `A` commutes with every conjugate
`T^{-i} A T^{i} = R^i A (R*)^i` (and `T^{i} A T^{-i} = (R*)^i A R^i`) for all
`i`, i.e. the defining relations `[a, t^{-i} a t^{i}] = 1` of the lamplighter
group hold.

The proof goes through the **tower algebra** `InTowerAlgebra`, the set of
complex-linear combinations `∑_{k<j} a_k P_k + b (I - P_τ)` of the tower
projections and the complement of the support.  This is an abelian subalgebra
(`commute_of_mem`), contains `A`, and is preserved by conjugation by `R` for a
closed tower (`mem_conj`, `mem_conj'`); hence every orbit element lies in it and
commutes with `A`.
-/

namespace LamplighterStability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **tower algebra**: complex-linear combinations of the tower projections
`P₀, …, P_{j-1}` together with the complement `I - P_τ` of the support. -/
def InTowerAlgebra (j : ℕ) (P : ℕ → Matrix ι ι ℂ) (M : Matrix ι ι ℂ) : Prop :=
  ∃ (a : ℕ → ℂ) (b : ℂ),
    M = (∑ k ∈ Finset.range j, a k • P k) + b • (1 - towerSupport j P)

/-- The Hermitian involution `A_{τ,x} = ∑_{i<j} (-1)^{x_i} P_i + (I - P_τ)`. -/
noncomputable def towerA (j : ℕ) (P : ℕ → Matrix ι ι ℂ) (x : ℕ → Bool) :
    Matrix ι ι ℂ :=
  (∑ k ∈ Finset.range j, (if x k then (-1 : ℂ) else 1) • P k)
    + (1 - towerSupport j P)

/-! ## Elementary algebra of the tower projections -/

/-
A tower projection times the support equals the projection.
-/
omit [DecidableEq ι] in
lemma proj_mul_towerSupport {j : ℕ} {P : ℕ → Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) {k : ℕ} (hk : k < j) :
    P k * towerSupport j P = P k := by
  unfold towerSupport; simp +decide [ Finset.mul_sum _ _ _ ] ;
  rw [ Finset.sum_eq_single_of_mem k ( Finset.mem_range.mpr hk ) ];
  · exact hP.1 k hk |>.2;
  · exact fun i hi hik => hP.2 k hk i ( Finset.mem_range.mp hi ) ( Ne.symm hik )

/-
The support times a tower projection equals the projection.
-/
omit [DecidableEq ι] in
lemma towerSupport_mul_proj {j : ℕ} {P : ℕ → Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) {k : ℕ} (hk : k < j) :
    towerSupport j P * P k = P k := by
  unfold towerSupport; simp +decide [ Finset.sum_mul ] ;
  rw [ Finset.sum_eq_single k ] <;> simp_all +decide [ PairwiseOrthProj ];
  exact hP.1 k hk |>.2

/-
The support of a tower is idempotent.
-/
omit [DecidableEq ι] in
lemma towerSupport_idem {j : ℕ} {P : ℕ → Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) :
    towerSupport j P * towerSupport j P = towerSupport j P := by
  unfold towerSupport; simp +decide [ Finset.sum_mul ] ;
  exact Finset.sum_congr rfl fun i hi => proj_mul_towerSupport hP ( Finset.mem_range.mp hi )

/-
The support of a tower is Hermitian.
-/
omit [DecidableEq ι] in
lemma towerSupport_isHermitian {j : ℕ} {P : ℕ → Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) :
    (towerSupport j P).IsHermitian := by
  unfold towerSupport; simp +decide [ *, Matrix.IsHermitian ] ;
  rw [ Matrix.conjTranspose_sum ];
  exact Finset.sum_congr rfl fun i hi => hP.1 i ( Finset.mem_range.mp hi ) |>.1

/-! ## The product formula and the abelian structure -/

/-
**Central computational lemma.**  The product of two tower-algebra elements
is again a tower-algebra element, with coefficients multiplied entrywise:
`(∑ aₖ Pₖ + b(1-P_τ)) · (∑ cₖ Pₖ + e(1-P_τ)) = ∑ (aₖcₖ) Pₖ + (be)(1-P_τ)`.

This uses that the `Pₖ` are pairwise orthogonal idempotents, that
`Pₖ(1-P_τ) = (1-P_τ)Pₖ = 0`, and that `(1-P_τ)² = 1-P_τ`.
-/
lemma tower_combo_mul {j : ℕ} {P : ℕ → Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (a c : ℕ → ℂ) (b e : ℂ) :
    ((∑ k ∈ Finset.range j, a k • P k) + b • (1 - towerSupport j P))
      * ((∑ k ∈ Finset.range j, c k • P k) + e • (1 - towerSupport j P))
    = (∑ k ∈ Finset.range j, (a k * c k) • P k)
        + (b * e) • (1 - towerSupport j P) := by
  have h_sum : ∀ (k : ℕ) (hk : k < j), (∑ l ∈ Finset.range j, a l • P l) * (c k • P k) = (a k * c k) • P k := by
    intro k hk; simp +decide [ Finset.sum_mul, Finset.smul_sum, smul_smul ] ;
    rw [ Finset.sum_eq_single k ] <;> simp_all +decide [ mul_comm, hP.2 ];
    exact congr_arg _ ( hP.1 k hk |>.2 );
  have h_sum : (∑ k ∈ Finset.range j, a k • P k) * ((1 : Matrix ι ι ℂ) - towerSupport j P) = 0 := by
    simp +decide [ mul_sub, Finset.sum_mul _ _ _ ];
    exact sub_eq_zero_of_eq ( Finset.sum_congr rfl fun i hi => by rw [ proj_mul_towerSupport hP ( Finset.mem_range.mp hi ) ] );
  simp_all +decide [ mul_add, add_mul, Finset.mul_sum _ _ _, Finset.sum_mul, smul_smul ];
  congr! 1;
  · refine' Finset.sum_congr rfl fun k hk => _;
    simp_all +decide [ mul_sub, sub_mul, towerSupport_mul_proj ];
  · simp +decide [ mul_comm b e ];
    simp +decide [ mul_sub, sub_mul, towerSupport_idem hP ]

/-
Any two elements of the tower algebra commute.
-/
lemma commute_of_mem {j : ℕ} {P : ℕ → Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) {M N : Matrix ι ι ℂ}
    (hM : InTowerAlgebra j P M) (hN : InTowerAlgebra j P N) :
    Commute M N := by
  obtain ⟨a, b, hM⟩ := hM
  obtain ⟨c, e, hN⟩ := hN;
  rw [ hM, hN, Commute ];
  simp +decide [ SemiconjBy, tower_combo_mul hP ];
  simp +decide only [mul_comm]

/-! ## Membership closure -/

/-
A single tower projection lies in the tower algebra.
-/
omit [Fintype ι] in
lemma mem_proj {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {l : ℕ} (hl : l < j) :
    InTowerAlgebra j P (P l) := by
  use fun k => if k = l then 1 else 0, 0; simp +decide [ hl ] ;

/-
The complement of the support lies in the tower algebra.
-/
omit [Fintype ι] in
lemma mem_comp {j : ℕ} {P : ℕ → Matrix ι ι ℂ} :
    InTowerAlgebra j P (1 - towerSupport j P) := by
  exact ⟨ fun _ => 0, 1, by simp +decide ⟩

/-
The tower algebra is closed under addition.
-/
omit [Fintype ι] in
lemma InTowerAlgebra.add {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {M N : Matrix ι ι ℂ}
    (hM : InTowerAlgebra j P M) (hN : InTowerAlgebra j P N) :
    InTowerAlgebra j P (M + N) := by
  rcases hM with ⟨ a, b, rfl ⟩ ; rcases hN with ⟨ c, d, rfl ⟩ ; refine' ⟨ fun k => a k + c k, b + d, _ ⟩ ; simp +decide [ add_smul, Finset.sum_add_distrib ] ; abel_nf;

/-
The tower algebra is closed under scalar multiplication.
-/
omit [Fintype ι] in
lemma InTowerAlgebra.smul {j : ℕ} {P : ℕ → Matrix ι ι ℂ} (c : ℂ) {M : Matrix ι ι ℂ}
    (hM : InTowerAlgebra j P M) :
    InTowerAlgebra j P (c • M) := by
  obtain ⟨ a, b, rfl ⟩ := hM; use fun k => c * a k, c * b; simp +decide [ Finset.smul_sum, smul_smul ] ;

/-
The tower algebra is closed under finite sums.
-/
omit [Fintype ι] in
lemma InTowerAlgebra.sum {j : ℕ} {P : ℕ → Matrix ι ι ℂ}
    {α : Type*} (s : Finset α) (f : α → Matrix ι ι ℂ)
    (h : ∀ i ∈ s, InTowerAlgebra j P (f i)) :
    InTowerAlgebra j P (∑ i ∈ s, f i) := by
  induction' s using Finset.induction with i s hi ih;
  exact ⟨ fun _ => 0, 0, by simp +decide ⟩;
  convert InTowerAlgebra.add ( h i ( Finset.mem_insert_self i s ) ) ( ih fun x hx => h x ( Finset.mem_insert_of_mem hx ) ) using 1;
  grind;
  exact Classical.decEq α

/-
`A_{τ,x}` lies in the tower algebra.
-/
omit [Fintype ι] in
lemma towerA_mem {j : ℕ} {P : ℕ → Matrix ι ι ℂ} (x : ℕ → Bool) :
    InTowerAlgebra j P (towerA j P x) := by
  exact ⟨ fun k => if x k then -1 else 1, 1, by simp +decide [ towerA ] ⟩

/-! ## Properties of `A_{τ,x}` -/

/-
`A_{τ,x}` is Hermitian.
-/
lemma towerA_isHermitian {j : ℕ} {P : ℕ → Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (x : ℕ → Bool) :
    (towerA j P x).IsHermitian := by
  unfold towerA; simp +decide [ Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_sum ] ;
  congr! 2;
  · split_ifs <;> simp_all +decide; all_goals exact hP.1 _ ‹_› |>.1;
  · exact towerSupport_isHermitian hP

/-
`A_{τ,x}² = 1`.
-/
lemma towerA_sq {j : ℕ} {P : ℕ → Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (x : ℕ → Bool) :
    towerA j P x * towerA j P x = 1 := by
  convert tower_combo_mul hP ( fun k => if x k then -1 else 1 ) ( fun k => if x k then -1 else 1 ) 1 1 using 1;
  · simp +decide [ towerA ];
  · rw [ Finset.sum_congr rfl fun _ _ => by aesop ] ; norm_num [ towerSupport ]

/-
`A_{τ,x}` is unitary.
-/
lemma towerA_unitary {j : ℕ} {P : ℕ → Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (x : ℕ → Bool) :
    towerA j P x ∈ unitary (Matrix ι ι ℂ) := by
  constructor;
  · rw [ star_eq_conjTranspose, towerA_isHermitian hP ];
    exact towerA_sq hP x;
  · rw [ star_eq_conjTranspose, towerA_isHermitian hP ];
    exact towerA_sq hP x

/-! ## Invariance of the tower algebra under conjugation by `R` -/

/-
For a closed tower, conjugation by `R*` sends `P_τ` to itself.
-/
lemma towerSupport_conj {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) :
    Rᴴ * towerSupport j P * R = towerSupport j P := by
  obtain ⟨hP, hR⟩ := hτ.left;
  rcases j with ( _ | j ) <;> simp_all +decide [ towerSupport ];
  simp_all +decide [ Finset.mul_sum _ _ _, Finset.sum_mul, Matrix.mul_assoc ];
  have := hτ.2;
  rw [ Finset.sum_range_succ, Finset.sum_range_succ' ];
  exact congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun i hi => hR.2 i ( Finset.mem_range.mp hi ) ) ( this ( Nat.succ_pos _ ) ▸ by simp +decide [ Matrix.mul_assoc ] )

/-
For a closed tower, conjugation by `R` sends `P_τ` to itself.
-/
lemma towerSupport_conj' {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) :
    R * towerSupport j P * Rᴴ = towerSupport j P := by
  have h_unitary : R * Rᴴ = 1 ∧ Rᴴ * R = 1 := by
    exact ⟨ hτ.1.2.1.2, hτ.1.2.1.1 ⟩;
  have := towerSupport_conj hτ hj; simp_all +decide [ mul_assoc ] ;
  grind +qlia

/-
For a closed tower, `R* P_k R` lies in the tower algebra (it equals
`P_{(k+1) mod j}`).
-/
lemma Rconj_proj_mem {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) {k : ℕ} (hk : k < j) :
    InTowerAlgebra j P (Rᴴ * P k * R) := by
  by_cases h : k + 1 < j;
  · have h_eq : Rᴴ * P k * R = P (k + 1) := by
      exact hτ.1.2.2 k h;
    exact h_eq.symm ▸ mem_proj h;
  · convert mem_proj ( show 0 < j from hj ) using 1;
    · convert hτ.2 hj using 1;
      rw [ show k = j - 1 by omega ];
    · infer_instance

/-
For a closed tower, `R P_k R*` lies in the tower algebra (it equals
`P_{(k-1) mod j}`).
-/
lemma Rconj'_proj_mem {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) {k : ℕ} (hk : k < j) :
    InTowerAlgebra j P (R * P k * Rᴴ) := by
  by_cases hk0 : k = 0;
  · obtain ⟨l, hl⟩ : ∃ l < j, R * P 0 * Rᴴ = P l := by
      use j - 1;
      have := hτ.2 hj;
      have hR_unitary : R * Rᴴ = 1 ∧ Rᴴ * R = 1 := by
        exact ⟨ hτ.1.2.1.2, hτ.1.2.1.1 ⟩;
      simp +decide [ ← this, ← mul_assoc, hR_unitary ];
      grind;
    exact hk0.symm ▸ hl.2 ▸ mem_proj hl.1;
  · obtain ⟨l, hl⟩ : ∃ l, l < j ∧ k = l + 1 := by
      exact ⟨ k - 1, by omega, by rw [ Nat.sub_add_cancel ( Nat.pos_of_ne_zero hk0 ) ] ⟩;
    have h_eq : R * P k * Rᴴ = P l := by
      have h_eq : Rᴴ * P l * R = P k := by
        have := hτ.1.2.2 l; aesop;
      have h_unitary : R * Rᴴ = 1 ∧ Rᴴ * R = 1 := by
        exact ⟨ hτ.1.2.1.2, hτ.1.2.1.1 ⟩;
      simp +decide [ ← h_eq, mul_assoc, h_unitary ];
      rw [ ← Matrix.mul_assoc, h_unitary.1, Matrix.one_mul ];
    exact h_eq.symm ▸ mem_proj hl.1

/-
The tower algebra is invariant under conjugation by `R*` (for a closed
tower).
-/
lemma mem_conj {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) {M : Matrix ι ι ℂ}
    (hM : InTowerAlgebra j P M) :
    InTowerAlgebra j P (Rᴴ * M * R) := by
  obtain ⟨a, b, hM⟩ := hM;
  -- Substitute M into the expression Rᴴ * M * R and simplify.
  have h_subst : Rᴴ * M * R = (∑ k ∈ Finset.range j, a k • (Rᴴ * P k * R)) + b • (1 - towerSupport j P) := by
    simp +decide [ hM, mul_add, add_mul, Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc ];
    simp +decide [ ← mul_assoc, sub_mul, mul_sub ];
    have := hτ.1.2.1.1;
    exact congr_arg _ ( by rw [ show Rᴴ * towerSupport j P * R = towerSupport j P from by simpa [ mul_assoc ] using towerSupport_conj hτ hj ] ; simpa [ mul_assoc ] using this );
  exact h_subst ▸ InTowerAlgebra.add ( InTowerAlgebra.sum _ _ fun i hi => InTowerAlgebra.smul _ ( Rconj_proj_mem hτ hj ( Finset.mem_range.mp hi ) ) ) ( InTowerAlgebra.smul _ mem_comp )

/-
The tower algebra is invariant under conjugation by `R` (for a closed
tower).
-/
lemma mem_conj' {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) {M : Matrix ι ι ℂ}
    (hM : InTowerAlgebra j P M) :
    InTowerAlgebra j P (R * M * Rᴴ) := by
  -- By definition of `InTowerAlgebra`, we can write $M$ as a linear combination of the projections and the identity.
  obtain ⟨a, b, hM⟩ : ∃ (a : ℕ → ℂ) (b : ℂ), M = (∑ k ∈ Finset.range j, a k • P k) + b • (1 - towerSupport j P) := by
    exact hM;
  -- By definition of `InTowerAlgebra`, we can write $R * M * Rᴴ$ as a linear combination of the projections and the identity.
  have hRMR : R * M * Rᴴ = (∑ k ∈ Finset.range j, a k • (R * P k * Rᴴ)) + b • (1 - towerSupport j P) := by
    simp +decide [ hM, mul_add, add_mul, mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul ];
    simp +decide [ sub_mul, mul_sub ];
    rw [ ← Matrix.mul_assoc, towerSupport_conj' hτ hj ];
    have := hτ.1.2.1;
    exact this.2 ▸ rfl;
  exact hRMR.symm ▸ InTowerAlgebra.add ( InTowerAlgebra.sum _ _ fun k hk => InTowerAlgebra.smul _ ( Rconj'_proj_mem hτ hj ( Finset.mem_range.mp hk ) ) ) ( InTowerAlgebra.smul _ mem_comp )

/-
The tower algebra is invariant under conjugation by `R^i` (for a closed
tower).
-/
lemma mem_conj_pow {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) {M : Matrix ι ι ℂ}
    (hM : InTowerAlgebra j P M) (i : ℕ) :
    InTowerAlgebra j P (R ^ i * M * Rᴴ ^ i) := by
  induction i <;> simp_all +decide [ pow_succ', mul_assoc ];
  convert mem_conj' hτ hj ( show InTowerAlgebra j P ( R ^ ‹_› * ( M * Rᴴ ^ ‹_› ) ) from by assumption ) using 1 ; simp +decide [ ← mul_assoc, ← pow_succ' ];
  simp +decide [ mul_assoc, pow_succ ]

/-
The tower algebra is invariant under conjugation by `(R*)^i` (for a closed
tower).
-/
lemma mem_conj_pow' {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) {M : Matrix ι ι ℂ}
    (hM : InTowerAlgebra j P M) (i : ℕ) :
    InTowerAlgebra j P (Rᴴ ^ i * M * R ^ i) := by
  induction' i with i ih;
  · simpa using hM;
  · convert mem_conj hτ hj ( ih ) using 1 ; simp +decide [ pow_succ', mul_assoc ];
    rw [ ← pow_succ', ← pow_succ ]

/-! ## The main lemma -/

/-
**Lemma `lem:tower_to_rep` (From towers to representations).**

Let `(P, R)` be a closed projection tower of height `j > 0` and `x : ℕ → Bool` a
sign pattern.  Setting `A = A_{τ,x} = ∑_{i<j} (-1)^{x_i} P_i + (I - P_τ)` and
`T = R*`, the pair `(A, T)` is a genuine pair of unitaries realizing the
lamplighter group: `A` is a Hermitian involution (`A² = 1`, hence unitary), `T`
is unitary, and `A` commutes with every orbit element `T^{-i} A T^{i}` and
`T^{i} A T^{-i}` (here `T^{-i} A T^{i} = R^i A (R*)^i`).
-/
theorem tower_to_rep {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) (x : ℕ → Bool) :
    (towerA j P x).IsHermitian ∧
    towerA j P x * towerA j P x = 1 ∧
    towerA j P x ∈ unitary (Matrix ι ι ℂ) ∧
    Rᴴ ∈ unitary (Matrix ι ι ℂ) ∧
    (∀ i : ℕ, Commute (towerA j P x) (R ^ i * towerA j P x * Rᴴ ^ i)) ∧
    (∀ i : ℕ, Commute (towerA j P x) (Rᴴ ^ i * towerA j P x * R ^ i)) := by
  refine' ⟨ _, _, _, _, _ ⟩;
  · exact towerA_isHermitian hτ.1.1 x;
  · exact towerA_sq hτ.1.1 x;
  · exact towerA_unitary hτ.1.1 x;
  · exact Unitary.star_mem hτ.1.2.1;
  · exact ⟨ fun i => commute_of_mem hτ.1.1 ( towerA_mem x ) ( mem_conj_pow hτ hj ( towerA_mem x ) i ), fun i => commute_of_mem hτ.1.1 ( towerA_mem x ) ( mem_conj_pow' hτ hj ( towerA_mem x ) i ) ⟩

end LamplighterStability