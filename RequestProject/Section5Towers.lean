import Mathlib
import RequestProject.ProjectionTowers
import RequestProject.HSNorm

/-!
# Section 5: block-diagonal assembly of involutions and unitaries

This file provides the *global gluing* infrastructure used in the Section 5
"Proof of Theorem main" assembly (`Section5Assembly.tower_rep_final`): given a
**resolution of the identity** `G : σ → Matrix ι ι ℂ` by pairwise-orthogonal
Hermitian idempotents (`∑ s, G s = 1`), and a family of *blocks* `A s` each
supported on `G s` (i.e. `G s * A s = A s = A s * G s`), the block-diagonal sum
`∑ s, A s` inherits the algebraic structure of the blocks:

* `block_involution_sq` / `block_involution` — if each block is a Hermitian
  involution on its subspace (`A s * A s = G s`), then `∑ s, A s` is a global
  Hermitian involution (`(∑ A)² = 1`) and hence a unitary.
* `block_unitary` — if each block is a unitary on its subspace
  (`(U s)ᴴ * U s = G s = U s * (U s)ᴴ`), then `∑ s, U s` is a global unitary.

These are pure finite-dimensional linear algebra; the orthogonality of distinct
blocks (`A s * A s' = 0` for `s ≠ s'`) is derived from the orthogonality of the
`G s`.
-/

namespace LamplighterStability.Section5

open scoped BigOperators
open Matrix

variable {ι σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]

/-
Distinct blocks are orthogonal: from block support and orthogonality of the
resolution projections.
-/
omit [DecidableEq ι] [Fintype σ] [DecidableEq σ] in
lemma block_mul_block_eq_zero {G : σ → Matrix ι ι ℂ}
    (hGortho : ∀ s s', s ≠ s' → G s * G s' = 0)
    {A : σ → Matrix ι ι ℂ}
    (hAsuppR : ∀ s, A s * G s = A s) (hGsuppL : ∀ s, G s * A s = A s)
    {s s' : σ} (h : s ≠ s') : A s * A s' = 0 := by
  rw [ ← hGsuppL s', ← Matrix.mul_assoc, ← hAsuppR s, Matrix.mul_assoc ];
  simp +decide [ ← Matrix.mul_assoc ];
  simp +decide [ Matrix.mul_assoc, hGortho s s' h ]

/-
The square of a block-diagonal sum of subspace-involutions is the identity.
-/
omit [DecidableEq σ] in
lemma block_involution_sq {G : σ → Matrix ι ι ℂ}
    (hGsum : ∑ s, G s = 1)
    (hGortho : ∀ s s', s ≠ s' → G s * G s' = 0)
    {A : σ → Matrix ι ι ℂ}
    (hAsuppL : ∀ s, G s * A s = A s) (hAsuppR : ∀ s, A s * G s = A s)
    (hAsq : ∀ s, A s * A s = G s) :
    (∑ s, A s) * (∑ s, A s) = 1 := by
  rw [ ← hGsum, Finset.sum_mul_sum ];
  refine' Finset.sum_congr rfl fun s hs => _;
  rw [ Finset.sum_eq_single s ];
  · exact hAsq s;
  · exact fun b _ hbs => block_mul_block_eq_zero hGortho hAsuppR hAsuppL (Ne.symm hbs);
  · aesop

/-
A block-diagonal sum of Hermitian subspace-involutions is a Hermitian
involution, hence a unitary.
-/
omit [DecidableEq σ] in
lemma block_involution {G : σ → Matrix ι ι ℂ}
    (hGsum : ∑ s, G s = 1)
    (hGortho : ∀ s s', s ≠ s' → G s * G s' = 0)
    {A : σ → Matrix ι ι ℂ}
    (hAsuppL : ∀ s, G s * A s = A s) (hAsuppR : ∀ s, A s * G s = A s)
    (hAh : ∀ s, (A s).IsHermitian) (hAsq : ∀ s, A s * A s = G s) :
    (∑ s, A s).IsHermitian ∧ (∑ s, A s) * (∑ s, A s) = 1
      ∧ (∑ s, A s) ∈ unitary (Matrix ι ι ℂ) := by
  refine' ⟨ _, _, _ ⟩;
  · simp_all +decide [ Matrix.IsHermitian, Matrix.conjTranspose_sum ];
  · exact block_involution_sq hGsum hGortho hAsuppL hAsuppR hAsq;
  · constructor;
    · convert block_involution_sq hGsum hGortho hAsuppL hAsuppR hAsq using 1;
      simp +decide;
      exact congr_arg₂ _ ( Finset.sum_congr rfl fun _ _ => hAh _ ) rfl;
    · convert block_involution_sq hGsum hGortho hAsuppL hAsuppR hAsq using 1;
      simp +decide [ Matrix.IsHermitian, star ] at *;
      simp +decide [ Matrix.conjTranspose_sum, hAh ]

/-
A block-diagonal sum of subspace-unitaries is a global unitary, with adjoint
the block-diagonal sum of the block adjoints.
-/
set_option maxHeartbeats 1600000 in
lemma block_unitary {G : σ → Matrix ι ι ℂ}
    (hGh : ∀ s, (G s).IsHermitian)
    (hGsum : ∑ s, G s = 1)
    (hGortho : ∀ s s', s ≠ s' → G s * G s' = 0)
    {U : σ → Matrix ι ι ℂ}
    (hUsuppL : ∀ s, G s * U s = U s) (hUsuppR : ∀ s, U s * G s = U s)
    (hUstar' : ∀ s, U s * (U s)ᴴ = G s) :
    (∑ s, U s) ∈ unitary (Matrix ι ι ℂ)
      ∧ (∑ s, U s)ᴴ = ∑ s, (U s)ᴴ := by
  refine' ⟨ _, _ ⟩ <;> simp_all +decide [ Matrix.IsHermitian ];
  · have h_unitary : (∑ s, U s) * (∑ s, U s)ᴴ = 1 := by
      have h_unitary : ∀ s s', s ≠ s' → U s * (U s')ᴴ = 0 := by
        intro s s' hne
        have hU_s_G_s' : U s * G s' = 0 := by
          have h_ortho : U s = U s * G s := by
            rw [ hUsuppR ]
          generalize_proofs at *; (
          rw [ h_ortho, Matrix.mul_assoc, hGortho s s' hne, Matrix.mul_zero ])
        have hU_s'_G_s : G s' * (U s')ᴴ = (U s')ᴴ := by
          grind +suggestions
        have hU_s_U_s'_conj : U s * (U s')ᴴ = U s * G s' * (U s')ᴴ := by
          rw [ Matrix.mul_assoc, hU_s'_G_s ]
        rw [hU_s_U_s'_conj, hU_s_G_s']
        simp;
      simp_all +decide [ Finset.sum_mul _ _ _ ];
      simp_all +decide [ Matrix.conjTranspose_sum ];
      rw [ Finset.sum_congr rfl fun s hs => by rw [ Finset.mul_sum _ _ _, Finset.sum_eq_single s ( fun t ht => by by_cases h : s = t <;> aesop ) ( by aesop ) ] ] ; aesop
    have h_unitary' : (∑ s, U s)ᴴ * (∑ s, U s) = 1 := by
      rw [ ← mul_eq_one_comm, h_unitary ]
    exact (by
    exact ⟨ h_unitary', h_unitary ⟩);
  · rw [ Matrix.conjTranspose_sum ]

/-
Powers of a block-diagonal sum decompose block-wise: `(∑ U_s)^n = ∑ G_s · U_s^n`.
For `n = 0` this reads `1 = ∑ G_s` (resolution of identity); for `n ≥ 1` the
support `G_s · U_s^n = U_s^n` makes it `∑ U_s^n`.
-/
omit [DecidableEq σ] in
lemma block_pow {G : σ → Matrix ι ι ℂ}
    (hGsum : ∑ s, G s = 1) (hGortho : ∀ s s', s ≠ s' → G s * G s' = 0)
    {U : σ → Matrix ι ι ℂ}
    (hUsuppL : ∀ s, G s * U s = U s) (hUsuppR : ∀ s, U s * G s = U s)
    (n : ℕ) :
    (∑ s, U s) ^ n = ∑ s, G s * (U s) ^ n := by
  induction' n with n ih
  · simp [hGsum]
  · rw [pow_succ, ih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hkey : ∀ s, s ≠ x → G x * U x ^ n * U s = 0 := by
      intro s hs
      have h1 : G x * G s = 0 := hGortho x s hs.symm
      have h2 : U x * G s = 0 := by rw [← hUsuppR x, mul_assoc, h1, mul_zero]
      have h3 : ∀ m, G x * U x ^ m * G s = 0 := by
        intro m
        induction m with
        | zero => simp [h1]
        | succ m ihm => rw [pow_succ, mul_assoc, mul_assoc, h2, mul_zero, mul_zero]
      rw [← hUsuppL s, ← mul_assoc, h3 n, zero_mul]
    rw [Finset.mul_sum, Finset.sum_eq_single x]
    · rw [mul_assoc, ← pow_succ]
    · intro s _ hsx; exact hkey s hsx
    · intro hx; exact absurd (Finset.mem_univ x) hx

/-
A block-diagonal sum commutes with another block-diagonal sum as soon as it does
block-by-block.  Distinct blocks annihilate (`block_mul_block_eq_zero`), so both
products collapse to the diagonal `∑ s, X s * Y s` resp. `∑ s, Y s * X s`.
-/
set_option maxHeartbeats 1600000 in
lemma block_commute {G : σ → Matrix ι ι ℂ}
    (hGortho : ∀ s s', s ≠ s' → G s * G s' = 0)
    {X Y : σ → Matrix ι ι ℂ}
    (hXsuppL : ∀ s, G s * X s = X s) (hXsuppR : ∀ s, X s * G s = X s)
    (hYsuppL : ∀ s, G s * Y s = Y s) (hYsuppR : ∀ s, Y s * G s = Y s)
    (hcomm : ∀ s, Commute (X s) (Y s)) :
    Commute (∑ s, X s) (∑ s, Y s) := by
  -- By definition of commutativity, we need to show that the product of the sums is equal to the commutative product of the sums.
  simp [Commute ];
  simp_all +decide [ SemiconjBy, Finset.sum_mul _ _ _, Finset.mul_sum ];
  have h_zero : ∀ s s', s ≠ s' → X s * Y s' = 0 ∧ Y s * X s' = 0 := by
    intro s s' hne
    have hXsYs' : X s * Y s' = X s * G s * G s' * Y s' := by
      simp +decide [ mul_assoc, hXsuppR, hYsuppL ]
    have hYsXs' : Y s * X s' = Y s * G s * G s' * X s' := by
      simp +decide [ mul_assoc, hYsuppR ];
      grind +qlia
    simp_all +decide [ mul_assoc ];
    have h_zero : X s * G s' = 0 ∧ Y s * G s' = 0 := by
      exact ⟨ by rw [ ← hXsuppR s, mul_assoc, hGortho s s' hne, MulZeroClass.mul_zero ], by rw [ ← hYsuppR s, mul_assoc, hGortho s s' hne, MulZeroClass.mul_zero ] ⟩;
    exact ⟨ by rw [ ← hYsuppL s', ← Matrix.mul_assoc, h_zero.1, Matrix.zero_mul ], by rw [ ← hXsuppL s', ← Matrix.mul_assoc, h_zero.2, Matrix.zero_mul ] ⟩;
  rw [ Finset.sum_congr rfl fun s hs => Finset.sum_eq_single s ( fun t ht => by by_cases h : s = t <;> aesop ) ( by aesop ) ];
  exact Finset.sum_congr rfl fun s hs => by rw [ Finset.sum_eq_single s ( fun s' hs' => by by_cases h : s = s' <;> aesop ) ( by aesop ) ] ; simp +decide [ hcomm s |> Commute.eq ] ;

/-
**Orbit commutation for the block-diagonal lamplighter representation.**  If on
each block `G s` we have a Hermitian-involution generator `A s` and a subspace
unitary `V s` satisfying the per-block lamplighter relation
`Commute (A s) (V s ^ i · A s · (V s)ᴴ ^ i)`, then the global block-diagonal sums
`A' = ∑ A s` and `V' = ∑ V s` satisfy the same relation
`Commute A' (V' ^ i · A' · (V')ᴴ ^ i)`.
-/
set_option maxHeartbeats 1600000 in
lemma block_orbit_commute {G : σ → Matrix ι ι ℂ}
    (hGh : ∀ s, (G s).IsHermitian)
    (hGsum : ∑ s, G s = 1) (hGortho : ∀ s s', s ≠ s' → G s * G s' = 0)
    {A V : σ → Matrix ι ι ℂ}
    (hAsuppL : ∀ s, G s * A s = A s) (hAsuppR : ∀ s, A s * G s = A s)
    (hVsuppL : ∀ s, G s * V s = V s) (hVsuppR : ∀ s, V s * G s = V s)
    (hcomm : ∀ s (i : ℕ), Commute (A s) ((V s) ^ i * A s * ((V s)ᴴ) ^ i))
    (i : ℕ) :
    Commute (∑ s, A s)
      ((∑ s, V s) ^ i * (∑ s, A s) * ((∑ s, V s)ᴴ) ^ i) := by
  have h_expand : (∑ s, V s) ^ i * (∑ s, A s) * (∑ s, V s)ᴴ ^ i =
    ∑ s, (V s) ^ i * A s * (V s).conjTranspose ^ i := by
      have h_expand : (∑ s, V s) ^ i * (∑ s, A s) * (∑ s, (V s).conjTranspose) ^ i =
        ∑ s, ∑ t, ∑ u, G s * (V s) ^ i * G t * A t * G u * (V u).conjTranspose ^ i := by
          have h_expand : (∑ s, V s) ^ i = ∑ s, G s * (V s) ^ i ∧ (∑ s, (V s).conjTranspose) ^ i = ∑ s, G s * (V s).conjTranspose ^ i := by
            apply And.intro;
            · convert block_pow hGsum hGortho hVsuppL hVsuppR i using 1;
            · convert block_pow _ _ _ _ i using 1;
              · exact hGsum;
              · exact hGortho;
              · intro s; specialize hVsuppR s; replace hVsuppR := congr_arg Matrix.conjTranspose hVsuppR; simp_all +decide [ Matrix.IsHermitian ] ;
              · intro s; specialize hVsuppL s; specialize hVsuppR s; replace hVsuppL := congr_arg ( fun m => mᴴ ) hVsuppL; replace hVsuppR := congr_arg ( fun m => mᴴ ) hVsuppR; simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ] ;
          simp +decide only [h_expand, Finset.sum_mul_sum];
          simp +decide only [mul_assoc, Finset.sum_mul];
          refine' Finset.sum_congr rfl fun s hs => Finset.sum_comm.trans ( Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun u hu => _ );
          by_cases h : t = u <;> simp_all +decide [ ← mul_assoc ];
      have h_expand : ∀ s t u, s ≠ t ∨ t ≠ u → G s * (V s) ^ i * G t * A t * G u * (V u).conjTranspose ^ i = 0 := by
        intro s t u hst
        by_cases hst' : s = t;
        · simp_all +decide [ mul_assoc ];
          simp +decide [ ← mul_assoc ];
          have h_expand : ∀ i, G t * V t ^ i * A t = V t ^ i * A t := by
            intro i
            induction' i with i ih;
            · simp +decide [ hAsuppL ];
            · simp +decide [ pow_succ', ← mul_assoc, hVsuppL ];
          simp +decide [ h_expand ];
          have h_expand : ∀ i, V t ^ i * A t * G u = 0 := by
            intro i
            have h_expand : V t ^ i * A t * G u = V t ^ i * (A t * G u) := by
              rw [ Matrix.mul_assoc ];
            have h_expand : A t * G u = 0 := by
              have h_expand : A t * G u = A t * (G t * G u) := by
                rw [ ← hAsuppR t, ← mul_assoc ];
                simp +decide [ hAsuppR ];
              rw [ h_expand, hGortho t u hst, MulZeroClass.mul_zero ];
            rw [ ‹V t ^ i * A t * G u = V t ^ i * ( A t * G u ) ›, h_expand, MulZeroClass.mul_zero ];
          rw [ h_expand i, MulZeroClass.zero_mul ];
        · have h_expand : G s * (V s) ^ i * G t = 0 := by
            have h_expand : ∀ i, G s * (V s) ^ i * G t = 0 := by
              intro i
              induction' i with i ih;
              · simp +decide [ hGortho s t hst' ];
              · simp +decide [ pow_succ, ← mul_assoc ];
                simp +decide [ mul_assoc, ← ih ];
                rw [ show V s * G t = 0 from _ ];
                · simp +decide [ ← mul_assoc, ih ];
                · replace hVsuppR := congr_arg ( · * G t ) ( hVsuppR s ) ; simp_all +decide [ mul_assoc ] ;
            exact h_expand i;
          simp [h_expand];
      have h_expand : ∀ s, ∑ t, ∑ u, G s * (V s) ^ i * G t * A t * G u * (V u).conjTranspose ^ i = G s * (V s) ^ i * A s * (V s).conjTranspose ^ i := by
        intro s
        have h_expand : ∑ t, ∑ u, G s * (V s) ^ i * G t * A t * G u * (V u).conjTranspose ^ i = ∑ t ∈ {s}, ∑ u ∈ {s}, G s * (V s) ^ i * G t * A t * G u * (V u).conjTranspose ^ i := by
          rw [ Finset.sum_eq_single s, Finset.sum_eq_single s ] <;> simp +contextual [ h_expand ];
          · exact fun t ht => h_expand s s t ( by tauto );
          · exact fun t ht => Finset.sum_eq_zero fun u hu => h_expand s t u <| Or.inl <| Ne.symm ht;
        grind +splitImp;
      convert ‹ ( ( ∑ s, V s ) ^ i * ∑ s, A s ) * ( ∑ s, ( V s ) ᴴ ) ^ i = ∑ s, ∑ t, ∑ u, G s * V s ^ i * G t * A t * G u * ( V u ) ᴴ ^ i › using 1;
      · rw [ Matrix.conjTranspose_sum ];
      · rw [ Finset.sum_congr rfl fun s _ => h_expand s ];
        refine' Finset.sum_congr rfl fun s _ => _;
        induction' i with i ih;
        · simp +decide [ hAsuppL ];
        · induction' i + 1 with i ih <;> simp +decide [ *, pow_succ', mul_assoc ];
          grind;
  simp_all +decide [ Commute, mul_assoc ];
  apply block_commute hGortho hAsuppL hAsuppR (fun s => ?_) (fun s => ?_) (fun s => hcomm s i);
  · induction' i with i ih;
    · simp +decide [ hAsuppL ];
    · induction' i + 1 with i ih <;> simp_all +decide [ pow_succ', ← mul_assoc ];
  · induction' i with i ih;
    · simp +decide [ hAsuppR ];
    · simp_all +decide [ pow_succ, ← mul_assoc ];
      simp_all +decide [ mul_assoc, Matrix.IsHermitian ];
      rw [ ← Matrix.conjTranspose_inj ] ; simp +decide [ *, Matrix.mul_assoc, Matrix.conjTranspose_mul ]

end LamplighterStability.Section5