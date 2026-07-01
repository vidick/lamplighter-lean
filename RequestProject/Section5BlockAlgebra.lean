import Mathlib
import RequestProject.ProjectionTowers
import RequestProject.TowerToRep
import RequestProject.MuInvariance

/-!
# Block tower algebra (per-tower block operators, Section 5)

This file develops the **block tower algebra** relative to an ambient projection
`G` (the resolution block of a single tower in `Edef_partition_resolution`).  It
mirrors the absolute tower algebra `InTowerAlgebra` of `TowerToRep.lean`, but
with the global identity `1` replaced by a projection `G` dominating the tower
support `P_τ = towerSupport j P`.

Concretely, for a closed projection tower `(P, R)` of height `j` whose floors all
satisfy `G · P_k = P_k` (so `P_τ ≤ G`), the algebra
`{ ∑_{k<j} a_k P_k + b (G − P_τ) }` is a commutative `*`-subalgebra with unit
`G`, closed under conjugation by the **block unitary** `V = R·P_τ + (G − P_τ)`.
This is exactly the structure needed to read off the per-tower block operators

```
A_τ = ∑_{k<j} (−1)^{x_k} P_k + (G − P_τ),     V_τ = R·P_τ + (G − P_τ)
```

feeding the global gluing lemma `Section5.block_lamplighter_construction`.  The
two squared-Hilbert–Schmidt closeness bounds are added in the per-tower assembly
that consumes this file.
-/

namespace LamplighterStability

open scoped BigOperators
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **block tower algebra** relative to an ambient projection `G`:
complex-linear combinations of the tower projections `P₀,…,P_{j-1}` together with
the *block complement* `G − P_τ` of the support. -/
def InBlockAlgebra (j : ℕ) (P : ℕ → Matrix ι ι ℂ) (G : Matrix ι ι ℂ)
    (M : Matrix ι ι ℂ) : Prop :=
  ∃ (a : ℕ → ℂ) (b : ℂ),
    M = (∑ k ∈ Finset.range j, a k • P k) + b • (G - towerSupport j P)

/-! ## Elementary interplay of the block projection `G` with the tower -/

omit [DecidableEq ι] in
lemma proj_mul_G {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) {k : ℕ} (hk : k < j) :
    P k * G = P k := by
  -- Since $G$ is Hermitian, we have $Gᴴ = G$.
  have hG_conjTranspose : Gᴴ = G := by
    exact hG.1;
  -- Since $P k$ is Hermitian, we have $(P k)ᴴ = P k$.
  have hP_conjTranspose : (P k)ᴴ = P k := by
    exact hP.1 k hk |>.1;
  simpa [ hG_conjTranspose, hP_conjTranspose ] using congr_arg Matrix.conjTranspose ( hGabs k hk )

omit [DecidableEq ι] in
lemma G_mul_towerSupport {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (hGabs : ∀ k < j, G * P k = P k) :
    G * towerSupport j P = towerSupport j P := by
  unfold towerSupport; simp +decide [ *, Finset.mul_sum ] ;
  exact Finset.sum_congr rfl fun i hi => hGabs i ( Finset.mem_range.mp hi )

omit [DecidableEq ι] in
lemma towerSupport_mul_G {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) :
    towerSupport j P * G = towerSupport j P := by
  -- By linearity of matrix multiplication, we can distribute the multiplication over the sum.
  have h_dist : (∑ i ∈ Finset.range j, P i) * G = ∑ i ∈ Finset.range j, P i * G := by
    rw [ Finset.sum_mul ];
  -- Substitute hGabs into h_dist to get the desired equality.
  have h_subst : ∑ i ∈ Finset.range j, P i * G = ∑ i ∈ Finset.range j, P i := by
    apply Finset.sum_congr rfl;
    exact fun i hi => proj_mul_G hP hG hGabs ( Finset.mem_range.mp hi );
  exact h_dist.trans h_subst

/-
The block complement `G − P_τ` is a projection.
-/
omit [DecidableEq ι] in
lemma blockGap_isProj {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) :
    IsProj (G - towerSupport j P) := by
  constructor;
  · simp_all +decide [ Matrix.IsHermitian, IsProj ];
    exact towerSupport_isHermitian hP;
  · simp +decide [ IsIdempotentElem, sub_mul, mul_sub, G_mul_towerSupport hGabs, towerSupport_mul_G hP hG hGabs, towerSupport_idem hP ];
    exact hG.2

omit [DecidableEq ι] in
lemma blockGap_mul_proj {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P)
    (hGabs : ∀ k < j, G * P k = P k) {k : ℕ} (hk : k < j) :
    (G - towerSupport j P) * P k = 0 := by
  simp +decide [ sub_mul, hGabs k hk, towerSupport_mul_proj hP hk ]

omit [DecidableEq ι] in
lemma proj_mul_blockGap {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) {k : ℕ} (hk : k < j) :
    P k * (G - towerSupport j P) = 0 := by
  have h_comm : P k * G = P k ∧ P k * towerSupport j P = P k := by
    exact ⟨ proj_mul_G hP hG hGabs hk, proj_mul_towerSupport hP hk ⟩;
  rw [ Matrix.mul_sub, h_comm.1, h_comm.2, sub_self ]

/-! ## The commutative product formula -/

/-
**Block product formula.** The product of two block-algebra elements is
again a block-algebra element with entrywise-multiplied coefficients.
-/
lemma blockCombo_mul {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) (a c : ℕ → ℂ) (b e : ℂ) :
    ((∑ k ∈ Finset.range j, a k • P k) + b • (G - towerSupport j P))
      * ((∑ k ∈ Finset.range j, c k • P k) + e • (G - towerSupport j P))
    = (∑ k ∈ Finset.range j, (a k * c k) • P k)
        + (b * e) • (G - towerSupport j P) := by
  simp +decide [ add_mul, mul_add, Finset.sum_mul _ _ _, Finset.mul_sum, Finset.sum_add_distrib, smul_smul ];
  congr! 1;
  · rw [ ← Finset.sum_add_distrib ];
    refine' Finset.sum_congr rfl fun i hi => _;
    rw [ Finset.sum_eq_single i ] <;> simp_all +decide [ mul_comm, smul_smul ];
    · rw [ hP.1 i hi |>.2, blockGap_mul_proj hP hGabs hi ] ; simp +decide;
    · exact fun k hk hki => Or.inr ( hP.2 k hk i hi hki );
  · rw [ Finset.sum_congr rfl fun i hi => by rw [ proj_mul_blockGap hP hG hGabs ( Finset.mem_range.mp hi ) ] ] ; simp +decide [ mul_comm ];
    rw [ blockGap_isProj hP hG hGabs |>.2 ]

/-
Any two elements of the block algebra commute.
-/
lemma blockCombo_commute {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) {M N : Matrix ι ι ℂ}
    (hM : InBlockAlgebra j P G M) (hN : InBlockAlgebra j P G N) :
    Commute M N := by
  obtain ⟨a, b, hM⟩ := hM
  obtain ⟨c, e, hN⟩ := hN
  simp [hM, hN] at *;
  ext i k; simp +decide [ blockCombo_mul hP hG hGabs, mul_comm ] ;

/-! ## Membership closure -/

omit [DecidableEq ι] in
omit [Fintype ι] in
lemma mem_proj_block {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {l : ℕ} (hl : l < j) :
    InBlockAlgebra j P G (P l) := by
  use fun k => if k = l then 1 else 0, 0;
  rw [ Finset.sum_eq_single l ] <;> aesop

omit [DecidableEq ι] in
omit [Fintype ι] in
lemma mem_blockGap {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ} :
    InBlockAlgebra j P G (G - towerSupport j P) := by
  -- By definition of InBlockAlgebra, we need to show that there exist coefficients a and b such that G - towerSupport j P equals the sum of a_k * P_k plus b * (G - towerSupport j P).
  use fun _ => 0, 1
  simp []

omit [DecidableEq ι] in
omit [Fintype ι] in
lemma InBlockAlgebra.add {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {M N : Matrix ι ι ℂ}
    (hM : InBlockAlgebra j P G M) (hN : InBlockAlgebra j P G N) :
    InBlockAlgebra j P G (M + N) := by
  obtain ⟨ a, b, rfl ⟩ := hM
  obtain ⟨ c, d, rfl ⟩ := hN
  use fun k => a k + c k, b + d
  simp [add_smul, Finset.sum_add_distrib]
  abel_nf

omit [DecidableEq ι] in
omit [Fintype ι] in
lemma InBlockAlgebra.smul {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (c : ℂ) {M : Matrix ι ι ℂ} (hM : InBlockAlgebra j P G M) :
    InBlockAlgebra j P G (c • M) := by
  obtain ⟨ a, b, rfl ⟩ := hM; exact ⟨ fun k => c * a k, c * b, by simp +decide [ Finset.smul_sum, smul_smul ] ⟩ ;

omit [DecidableEq ι] in
omit [Fintype ι] in
lemma InBlockAlgebra.sum {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {α : Type*} (s : Finset α) (f : α → Matrix ι ι ℂ)
    (h : ∀ i ∈ s, InBlockAlgebra j P G (f i)) :
    InBlockAlgebra j P G (∑ i ∈ s, f i) := by
  by_contra h_contra;
  exact h_contra <| by
    have h_sum : ∀ (s : Finset α), (∀ i ∈ s, InBlockAlgebra j P G (f i)) → InBlockAlgebra j P G (∑ i ∈ s, f i) := by
      intro s hs; induction' s using Finset.induction_on with i s hi ih; simp_all +decide [] ;
      exact ⟨ fun _ => 0, 0, by simp +decide ⟩;
      convert InBlockAlgebra.add ( hs i ( Finset.mem_insert_self i s ) ) ( ih fun i hi => hs i ( Finset.mem_insert_of_mem hi ) ) using 1;
      grind +suggestions;
      exact Classical.decEq α
    exact h_sum s h

/-! ## The block operators `A_τ` and `V_τ` -/

/-- The per-tower block Hermitian involution
`A_τ = ∑_{k<j} (−1)^{x_k} P_k + (G − P_τ)`. -/
noncomputable def blockA (j : ℕ) (P : ℕ → Matrix ι ι ℂ) (G : Matrix ι ι ℂ)
    (x : ℕ → Bool) : Matrix ι ι ℂ :=
  (∑ k ∈ Finset.range j, signC (x k) • P k) + (G - towerSupport j P)

/-- The per-tower block unitary `V_τ = R·P_τ + (G − P_τ)`. -/
noncomputable def blockV (j : ℕ) (P : ℕ → Matrix ι ι ℂ) (G : Matrix ι ι ℂ)
    (R : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  R * towerSupport j P + (G - towerSupport j P)

omit [DecidableEq ι] in
omit [Fintype ι] in
lemma blockA_mem {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (x : ℕ → Bool) : InBlockAlgebra j P G (blockA j P G x) := by
  exact ⟨ fun k => signC ( x k ), 1, by unfold blockA; simp +decide [ towerSupport ] ⟩

/-! ## Conjugation by the closed-tower unitary -/

/-
For a closed tower, conjugation by `R` sends each floor projection to a
single (cyclically shifted) floor projection.
-/
lemma exists_R_conj_proj {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) {k : ℕ} (hk : k < j) :
    ∃ l, l < j ∧ R * P k * Rᴴ = P l := by
  obtain ⟨l, hl⟩ : ∃ l < j, Rᴴ * P l * R = P k := by
    rcases k with ( _ | k ) <;> simp_all +decide [ IsClosedProjTower ];
    · exact ⟨ j - 1, Nat.pred_lt hk.ne', hτ.2 ⟩;
    · exact ⟨ k, by linarith, hτ.1.2.2 k ( by linarith ) ⟩;
  have h_unitary : R * Rᴴ = 1 := by
    exact hτ.1.2.1.2;
  simp +decide [ ← hl.2, mul_assoc, h_unitary ];
  exact ⟨ l, hl.1, by rw [ ← Matrix.mul_assoc, h_unitary, Matrix.one_mul ] ⟩

/-
For a closed tower, conjugation by `R*` sends each floor projection to a
single (cyclically shifted) floor projection.
-/
lemma exists_Rstar_conj_proj {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) {k : ℕ} (hk : k < j) :
    ∃ l, l < j ∧ Rᴴ * P k * R = P l := by
  rcases lt_or_eq_of_le ( Nat.le_sub_one_of_lt hk ) with hk' | rfl;
  · exact ⟨ k + 1, by omega, hτ.1.2.2 k ( by omega ) ⟩;
  · exact ⟨ 0, hj, hτ.2 hj ⟩

/-
For a closed tower, `R` commutes with the support `P_τ`.
-/
lemma R_comm_towerSupport {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) :
    R * towerSupport j P = towerSupport j P * R := by
  convert congr_arg ( fun x => x * R ) ( towerSupport_conj' hτ hj ) using 1;
  simp +decide [ mul_assoc ];
  rw [ show Rᴴ * R = 1 from hτ.1.2.1.1 ] ; simp +decide

/-
`R · (∑ a_k P_k) · R*` is again a block-algebra element (a real-linear
combination of the cyclically permuted floors).
-/
lemma conj_sum_proj_mem_block {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {R : Matrix ι ι ℂ} (hτ : IsClosedProjTower j P R) (hj : 0 < j)
    (a : ℕ → ℂ) :
    InBlockAlgebra j P G (R * (∑ k ∈ Finset.range j, a k • P k) * Rᴴ) := by
  convert InBlockAlgebra.sum ( Finset.range j ) ( fun k => a k • ( R * P k * Rᴴ ) ) _ using 1;
  · simp +decide [ Matrix.mul_sum, Matrix.sum_mul, mul_assoc ];
  · intro k hk; obtain ⟨ l, hl, h ⟩ := exists_R_conj_proj hτ hj ( Finset.mem_range.mp hk ) ; simp +decide [ h, hl, mem_proj_block, InBlockAlgebra.smul ] ;

/-
`R* · (∑ a_k P_k) · R` is again a block-algebra element.
-/
lemma conj_sum_proj_mem_block' {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {R : Matrix ι ι ℂ} (hτ : IsClosedProjTower j P R) (hj : 0 < j)
    (a : ℕ → ℂ) :
    InBlockAlgebra j P G (Rᴴ * (∑ k ∈ Finset.range j, a k • P k) * R) := by
  have h_sum : Rᴴ * (∑ k ∈ Finset.range j, a k • P k) * R = ∑ k ∈ Finset.range j, a k • (Rᴴ * P k * R) := by
    simp +decide only [Finset.mul_sum, mul_smul_comm, Finset.sum_mul, smul_mul_assoc, mul_assoc];
  convert InBlockAlgebra.sum ( Finset.range j ) ( fun k => a k • ( Rᴴ * P k * R ) ) _;
  intro k hk; obtain ⟨ l, hl, h ⟩ := exists_Rstar_conj_proj hτ hj ( Finset.mem_range.mp hk ) ; simp +decide [ h, InBlockAlgebra.smul, mem_proj_block hl ] ;

/-
The block algebra is closed under conjugation by the block unitary `V_τ`.
-/
lemma blockV_conj_mem {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {R : Matrix ι ι ℂ} (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k)
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) {M : Matrix ι ι ℂ}
    (hM : InBlockAlgebra j P G M) :
    InBlockAlgebra j P G (blockV j P G R * M * (blockV j P G R)ᴴ) := by
  -- By definition of $blockV$, we have $blockV j P G R = R * towerSupport j P + (G - towerSupport j P)$.
  obtain ⟨a, b, hM_eq⟩ := hM
  have h_blockV : blockV j P G R = R * towerSupport j P + (G - towerSupport j P) := by
    rfl;
  -- By definition of $blockV$, we have $blockV j P G R * M * (blockV j P G R)ᴴ = R * (∑ k ∈ Finset.range j, a k • P k) * Rᴴ + b • (G - towerSupport j P)$.
  have h_blockV_mul : blockV j P G R * M * (blockV j P G R)ᴴ = R * (∑ k ∈ Finset.range j, a k • P k) * Rᴴ + b • (G - towerSupport j P) := by
    simp +decide [ h_blockV, hM_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc ];
    have h_simp : towerSupport j P * (∑ k ∈ Finset.range j, a k • P k) = ∑ k ∈ Finset.range j, a k • P k ∧ (∑ k ∈ Finset.range j, a k • P k) * towerSupport j P = ∑ k ∈ Finset.range j, a k • P k ∧ (G - towerSupport j P) * (∑ k ∈ Finset.range j, a k • P k) = 0 ∧ (∑ k ∈ Finset.range j, a k • P k) * (G - towerSupport j P) = 0 := by
      refine' ⟨ _, _, _, _ ⟩;
      · simp +decide [ Finset.mul_sum _ _ _ ];
        exact Finset.sum_congr rfl fun i hi => by rw [ towerSupport_mul_proj hP ( Finset.mem_range.mp hi ) ] ;
      · simp +decide [ Finset.sum_mul ];
        exact Finset.sum_congr rfl fun i hi => by rw [ proj_mul_towerSupport hP ( Finset.mem_range.mp hi ) ] ;
      · simp +decide [ Finset.mul_sum _ _ _ ];
        exact Finset.sum_eq_zero fun i hi => by rw [ blockGap_mul_proj hP hGabs ( Finset.mem_range.mp hi ) ] ; simp +decide ;
      · simp +decide [ Finset.sum_mul ];
        exact Finset.sum_eq_zero fun i hi => by rw [ proj_mul_blockGap hP hG hGabs ( Finset.mem_range.mp hi ) ] ; simp +decide ;
    have h_simp : (G - towerSupport j P) * (G - towerSupport j P) = G - towerSupport j P ∧ (towerSupport j P)ᴴ = towerSupport j P ∧ Gᴴ = G := by
      have h_simp : (G - towerSupport j P) * (G - towerSupport j P) = G - towerSupport j P := by
        exact blockGap_isProj hP hG hGabs |>.2;
      exact ⟨ h_simp, towerSupport_isHermitian hP, hG.1 ⟩;
    simp_all +decide [ ← Matrix.mul_assoc ];
    simp_all +decide [ mul_sub, sub_mul, Matrix.mul_assoc ];
    simp_all +decide [ ← Matrix.mul_assoc, towerSupport_mul_G hP hG hGabs, G_mul_towerSupport hGabs, towerSupport_idem hP ];
  convert InBlockAlgebra.add ( conj_sum_proj_mem_block hτ hj a ) ( InBlockAlgebra.smul b mem_blockGap ) using 1

/-
The block algebra is closed under conjugation by `V_τ*`.
-/
lemma blockVstar_conj_mem {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {R : Matrix ι ι ℂ} (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k)
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) {M : Matrix ι ι ℂ}
    (hM : InBlockAlgebra j P G M) :
    InBlockAlgebra j P G ((blockV j P G R)ᴴ * M * blockV j P G R) := by
  obtain ⟨ a, b, rfl ⟩ := hM;
  -- Expand the product and simplify using the properties of projections and blockGap.
  have h_expand : (blockV j P G R)ᴴ * (∑ k ∈ Finset.range j, a k • P k) * (blockV j P G R) = Rᴴ * (∑ k ∈ Finset.range j, a k • P k) * R := by
    have h_expand : (blockV j P G R)ᴴ = towerSupport j P * Rᴴ + (G - towerSupport j P) := by
      simp +decide [ blockV, Matrix.conjTranspose_mul ];
      rw [ show Gᴴ = G from hG.1, show ( towerSupport j P ) ᴴ = towerSupport j P from ?_ ];
      exact towerSupport_isHermitian hP;
    have h_expand : (G - towerSupport j P) * (∑ k ∈ Finset.range j, a k • P k) = 0 := by
      simp +decide [ Finset.mul_sum _ _ _, sub_mul ];
      exact Finset.sum_eq_zero fun i hi => by rw [ show towerSupport j P * P i = P i from towerSupport_mul_proj hP ( Finset.mem_range.mp hi ) ] ; simp +decide [ hGabs i ( Finset.mem_range.mp hi ) ] ;
    simp_all +decide [ add_mul, mul_assoc ];
    have h_expand : (∑ k ∈ Finset.range j, a k • P k) * blockV j P G R = (∑ k ∈ Finset.range j, a k • P k) * R := by
      simp +decide [ blockV, mul_add, Finset.sum_mul _ _ _ ];
      refine' Finset.sum_congr rfl fun i hi => _;
      simp +decide [ ← mul_assoc, R_comm_towerSupport hτ hj, proj_mul_blockGap hP hG hGabs ( Finset.mem_range.mp hi ) ];
      simp +decide [ mul_assoc ];
      rw [ ← mul_assoc, proj_mul_towerSupport hP ( Finset.mem_range.mp hi ) ];
    simp_all +decide [ ← mul_assoc ];
    have h_expand : towerSupport j P * Rᴴ = Rᴴ * towerSupport j P := by
      have := R_comm_towerSupport hτ hj;
      apply_fun ( fun x => xᴴ ) at this; simp_all +decide [ Matrix.conjTranspose_mul ] ;
      convert this using 1; all_goals rw [ towerSupport_isHermitian hP ];
    simp_all +decide [ mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul ];
    refine' Finset.sum_congr rfl fun x hx => _;
    simp_all +decide [ ← mul_assoc, towerSupport_mul_proj hP ];
  have h_expand : (blockV j P G R)ᴴ * (b • (G - towerSupport j P)) * (blockV j P G R) = b • (G - towerSupport j P) := by
    simp +decide [ blockV, mul_assoc, mul_add, add_mul ];
    have h_expand : (G - towerSupport j P) * (R * towerSupport j P) = 0 ∧ (G - towerSupport j P) * (G - towerSupport j P) = G - towerSupport j P := by
      have h_expand : (G - towerSupport j P) * (R * towerSupport j P) = 0 := by
        have h_expand : (G - towerSupport j P) * towerSupport j P = 0 := by
          simp +decide [ sub_mul ];
          rw [ G_mul_towerSupport hGabs, towerSupport_idem hP, sub_self ];
        convert congr_arg ( fun x => x * R ) h_expand using 1 <;> simp +decide [ mul_assoc, R_comm_towerSupport hτ hj ];
      exact ⟨ h_expand, blockGap_isProj hP hG hGabs |>.2 ⟩;
    simp_all +decide [ ← mul_assoc ];
    have h_expand : (towerSupport j P)ᴴ * Rᴴ * (G - towerSupport j P) = 0 := by
      convert congr_arg Matrix.conjTranspose h_expand.1 using 1 ; simp +decide [ Matrix.mul_assoc, Matrix.conjTranspose_mul ];
      · have h_expand : Gᴴ = G := by
          exact hG.1;
        rw [ h_expand, towerSupport_isHermitian hP ];
      · simp +decide [ Matrix.conjTranspose ];
    simp_all +decide [ Matrix.IsHermitian, IsProj ];
    have h_expand : (towerSupport j P)ᴴ = towerSupport j P := by
      exact towerSupport_isHermitian hP;
    grind;
  convert InBlockAlgebra.add ( conj_sum_proj_mem_block' hτ hj a ) ( InBlockAlgebra.smul b ( mem_blockGap ) ) using 1;
  simp_all +decide [ mul_add, add_mul ]

/-
The block algebra is closed under conjugation by `V_τ^i`.
-/
lemma blockV_pow_conj_mem {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {R : Matrix ι ι ℂ} (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k)
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) {M : Matrix ι ι ℂ}
    (hM : InBlockAlgebra j P G M) (i : ℕ) :
    InBlockAlgebra j P G
      ((blockV j P G R) ^ i * M * ((blockV j P G R)ᴴ) ^ i) := by
  induction' i with i ih;
  · simpa using hM;
  · rw [ pow_succ', pow_succ ];
    convert blockV_conj_mem hP hG hGabs hτ hj ih using 1 ; simp +decide [ mul_assoc ]

lemma blockVstar_pow_conj_mem {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {R : Matrix ι ι ℂ} (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k)
    (hτ : IsClosedProjTower j P R) (hj : 0 < j) {M : Matrix ι ι ℂ}
    (hM : InBlockAlgebra j P G M) (i : ℕ) :
    InBlockAlgebra j P G
      (((blockV j P G R)ᴴ) ^ i * M * (blockV j P G R) ^ i) := by
  induction i <;> simp_all +decide [ pow_succ', mul_assoc ];
  convert blockVstar_conj_mem hP hG hGabs hτ hj _ using 1;
  simp +decide [ ← mul_assoc ];
  rotate_left;
  exact ( blockV j P G R ) ᴴ ^ ‹_› * ( M * blockV j P G R ^ ‹_› );
  · assumption;
  · simp +decide only [mul_assoc];
    rw [ ← pow_succ', ← pow_succ ]

/-
If `(P'_k)` is dominated floorwise by a pairwise-orthogonal family `(P_k)`,
then the ambient support `towerSupport j P` acts as the identity on each `P'_k`.
-/
lemma towerSupport_mul_subproj {j : ℕ} {P P' : ℕ → Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (hP'proj : ∀ i < j, IsProj (P' i))
    (hP'le : ∀ i < j, ProjLE (P' i) (P i)) {k : ℕ} (hk : k < j) :
    towerSupport j P * P' k = P' k := by
  have hP'_k : P k * P' k = P' k := by
    apply proj_mul_eq_self_of_psd_le;
    · exact hP.1 k hk;
    · obtain ⟨ h₁, h₂ ⟩ := hP'proj k hk;
      simp_all +decide [ IsIdempotentElem, Matrix.IsHermitian ];
      exact hP'le k hk;
  have hP'_k : ∀ i < j, i ≠ k → P i * P' k = 0 := by
    intro i hi hik
    have hP'_k : P i * P k = 0 := by
      exact hP.2 i hi k hk hik;
    have hP'_k : P i * P' k = P i * (P k * P' k) := by
      rw [ ‹P k * P' k = P' k› ];
    rw [ hP'_k, ← Matrix.mul_assoc, ‹P i * P k = 0›, Matrix.zero_mul ];
  unfold towerSupport; simp +decide [ *, Finset.sum_mul _ _ _ ] ;
  rw [ Finset.sum_eq_single k ] <;> aesop

/-! ## Structural properties of the block operators -/

omit [DecidableEq ι] in
lemma blockA_isHermitian {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (x : ℕ → Bool) :
    (blockA j P G x).IsHermitian := by
  unfold blockA; simp +decide [ *, Matrix.IsHermitian ] ;
  congr! 1;
  · simp +decide [ Matrix.conjTranspose_sum, Matrix.conjTranspose_smul ];
    exact Finset.sum_congr rfl fun i hi => by rw [ show ( P i ) ᴴ = P i from hP.1 i ( Finset.mem_range.mp hi ) |>.1 ] ; unfold signC; aesop;
  · exact congr_arg₂ _ hG.1 ( towerSupport_isHermitian hP )

lemma blockA_supp_left {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) (x : ℕ → Bool) :
    G * blockA j P G x = blockA j P G x := by
  unfold blockA;
  simp +decide [ mul_add, Finset.mul_sum _ _ _, hG.2.eq, Matrix.mul_sub, G_mul_towerSupport hGabs ];
  exact Finset.sum_congr rfl fun i hi => by rw [ hGabs i ( Finset.mem_range.mp hi ) ] ;

lemma blockA_supp_right {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) (x : ℕ → Bool) :
    blockA j P G x * G = blockA j P G x := by
  unfold blockA; simp +decide [ *, add_mul, Finset.sum_mul _ _ _ ] ;
  refine' congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun i hi => _ ) _;
  · rw [ proj_mul_G hP hG hGabs ( Finset.mem_range.mp hi ) ];
  · rw [ sub_mul, hG.2, towerSupport_mul_G hP hG hGabs ]

/-
`A_τ` is an involution on the block: `A_τ² = G`.
-/
lemma blockA_sq {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) (x : ℕ → Bool) :
    blockA j P G x * blockA j P G x = G := by
  convert blockCombo_mul hP hG hGabs ( fun k => signC ( x k ) ) ( fun k => signC ( x k ) ) 1 1 using 1;
  · simp +decide [ blockA ];
  · simp +decide [ signC_sq, towerSupport ]

lemma blockV_supp_left {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {R : Matrix ι ι ℂ} (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) (hτ : IsClosedProjTower j P R) (hj : 0 < j) :
    G * blockV j P G R = blockV j P G R := by
  -- Expanding `blockV` and using `G * P k = P k` (from `hGabs`), we get `G * (R * towerSupport) = R * towerSupport`.
  -- Then `G * blockV = R * towerSupport + (G - towerSupport) = blockV` since `G` acts as identity on `G - towerSupport`.
  simp [blockV, R_comm_towerSupport hτ hj];
  simp +decide only [mul_add, mul_sub];
  rw [ ← Matrix.mul_assoc, G_mul_towerSupport hGabs ];
  rw [ hG.2 ]

omit [DecidableEq ι] in
lemma blockV_supp_right {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {R : Matrix ι ι ℂ} (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) :
    blockV j P G R * G = blockV j P G R := by
  unfold blockV;
  simp +decide [ add_mul, mul_assoc ];
  rw [ towerSupport_mul_G hP hG hGabs, sub_mul, hG.2 ];
  rw [ towerSupport_mul_G hP hG hGabs ]

/-
`V_τ` is a unitary on the block: `V_τ V_τ* = G`.
-/
lemma blockV_unitary {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {R : Matrix ι ι ℂ} (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) (hτ : IsClosedProjTower j P R) (hj : 0 < j) :
    blockV j P G R * (blockV j P G R)ᴴ = G := by
  -- Let $T = \text{towerSupport } j P$ and $gap = G - T$.
  set T := towerSupport j P
  set gap := G - T;
  -- Expand the product $(R*T + gap) * (T*Rᴴ + gap)$.
  have h_expand : (R * T + gap) * (T * Rᴴ + gap) = R * T * T * Rᴴ + R * T * gap + gap * T * Rᴴ + gap * gap := by
    simp +decide only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc] ; abel_nf;
  -- Now let's simplify each term in the expansion.
  have h_simplify : R * T * T * Rᴴ = T ∧ R * T * gap = 0 ∧ gap * T * Rᴴ = 0 ∧ gap * gap = gap := by
    have h_simplify : R * T * Rᴴ = T ∧ T * gap = 0 ∧ gap * T = 0 ∧ gap * gap = gap := by
      refine' ⟨ _, _, _, _ ⟩;
      · convert towerSupport_conj' hτ hj using 1;
      · rw [ mul_sub, sub_eq_zero ];
        rw [ towerSupport_mul_G hP hG hGabs, towerSupport_idem hP ];
      · rw [ sub_mul, sub_eq_zero ];
        rw [ G_mul_towerSupport hGabs, towerSupport_idem hP ];
      · exact blockGap_isProj hP hG hGabs |>.2;
    simp_all +decide [ mul_assoc ];
    have hT_idem : T * T = T := by
      convert towerSupport_idem hP using 1;
    simp +decide [ ← mul_assoc, hT_idem, h_simplify ];
  -- Substitute the simplified terms back into the expansion.
  have h_final : (R * T + gap) * (T * Rᴴ + gap) = T + gap := by
    aesop;
  convert h_final using 1;
  · unfold blockV; simp +decide [ Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add ] ;
    rw [ show Gᴴ = G from hG.1 ] ; rw [ show ( towerSupport j P ) ᴴ = towerSupport j P from towerSupport_isHermitian hP ] ;
  · rw [ add_sub_cancel ]

/-
The per-block lamplighter relation (`T`-direction).
-/
lemma blockA_blockV_commute {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {R : Matrix ι ι ℂ} (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) (hτ : IsClosedProjTower j P R) (hj : 0 < j)
    (x : ℕ → Bool) (i : ℕ) :
    Commute (blockA j P G x)
      (blockV j P G R ^ i * blockA j P G x * ((blockV j P G R)ᴴ) ^ i) := by
  -- Since blockA and blockV are conjugates, and blockA is in the block algebra, their product should commute with any element in the block algebra.
  have h_comm : Commute (blockA j P G x) (blockV j P G R ^ i * blockA j P G x * (blockV j P G R)ᴴ ^ i) := by
    have h_blockA : InBlockAlgebra j P G (blockA j P G x) := blockA_mem x
    have h_blockV : InBlockAlgebra j P G (blockV j P G R ^ i * blockA j P G x * (blockV j P G R)ᴴ ^ i) := blockV_pow_conj_mem hP hG hGabs hτ hj h_blockA i
    exact blockCombo_commute hP hG hGabs h_blockA h_blockV;
  exact h_comm

/-
The per-block lamplighter relation (`T*`-direction).
-/
lemma blockA_blockVstar_commute {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {G : Matrix ι ι ℂ}
    {R : Matrix ι ι ℂ} (hP : PairwiseOrthProj j P) (hG : IsProj G)
    (hGabs : ∀ k < j, G * P k = P k) (hτ : IsClosedProjTower j P R) (hj : 0 < j)
    (x : ℕ → Bool) (i : ℕ) :
    Commute (blockA j P G x)
      (((blockV j P G R)ᴴ) ^ i * blockA j P G x * blockV j P G R ^ i) := by
  exact blockCombo_commute hP hG hGabs (blockA_mem x)
    (blockVstar_pow_conj_mem hP hG hGabs hτ hj (blockA_mem x) i)

end LamplighterStability