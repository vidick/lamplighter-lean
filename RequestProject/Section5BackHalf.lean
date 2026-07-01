import Mathlib
import RequestProject.Section5Towers
import RequestProject.PVMAlgebra

/-!
# Section 5 back half: reusable assembly lemmas

This file collects self-contained matrix-algebra lemmas used in the Section 5
"Proof of the main results" assembly (`Section5Assembly.tower_rep_final`), namely

* `commute_orbit_int` — packaging the two natural-number conjugation-commutation
  relations of a Hermitian involution `A'` with a unitary `T'` into the single
  integer-indexed lamplighter relation
  `∀ i : ℤ, Commute A' (T'^{-i} · A' · T'^i)` at the level of the unitary group;
* `block_lamplighter_construction` — the **construction half** of the global
  block-diagonal gluing: from a resolution of identity `G` by pairwise-orthogonal
  Hermitian idempotents together with per-block Hermitian involutions `A s` and
  subspace unitaries `V s` satisfying both directions of the per-block
  lamplighter relation, the block-diagonal sums `A' = ∑ A s`, `T' = ∑ V s` form a
  genuine pair `(A', T')` of unitaries with `A'² = 1` realizing the integer
  lamplighter relation.

The accompanying Pythagorean closeness bounds are proved separately (they use the
master HS-Pythagoras `normHS_sq_double_pyth` over the resolution `G`).
-/

namespace LamplighterStability.Section5

open scoped BigOperators
open Matrix

variable {d : ℕ}

/-
**Integer lamplighter relation from the two natural-number directions.**
If a Hermitian involution `A'` and a unitary `T'` (as elements of the unitary
group) satisfy both conjugation-commutation relations
`Commute A' (T'^n · A' · (T'*)^n)` and `Commute A' ((T'*)^n · A' · T'^n)` for all
`n : ℕ`, then they satisfy the integer lamplighter relation
`Commute A' (T'^{-i} · A' · T'^i)` for all `i : ℤ`.
-/
lemma commute_orbit_int (A' T' : unitaryGroup (Fin d) ℂ)
    (hfwd : ∀ n : ℕ, Commute (A' : Matrix (Fin d) (Fin d) ℂ)
      ((T' : Matrix (Fin d) (Fin d) ℂ) ^ n * (A' : Matrix (Fin d) (Fin d) ℂ)
        * (star (T' : Matrix (Fin d) (Fin d) ℂ)) ^ n))
    (hbwd : ∀ n : ℕ, Commute (A' : Matrix (Fin d) (Fin d) ℂ)
      ((star (T' : Matrix (Fin d) (Fin d) ℂ)) ^ n * (A' : Matrix (Fin d) (Fin d) ℂ)
        * (T' : Matrix (Fin d) (Fin d) ℂ) ^ n)) :
    ∀ i : ℤ, Commute (A' : unitaryGroup (Fin d) ℂ) (T' ^ (-i) * A' * T' ^ i) := by
  intro i
  by_cases hi : 0 ≤ i;
  · cases' Int.eq_ofNat_of_zero_le hi with n hn;
    simp_all +decide [ Commute, mul_assoc ];
    simp_all +decide [ SemiconjBy, Subtype.ext_iff ];
  · obtain ⟨ n, rfl ⟩ := Int.exists_eq_neg_ofNat ( le_of_not_ge hi );
    simp_all +decide [ Commute ];
    simp_all +decide [ SemiconjBy, Subtype.ext_iff ]

/-
**Construction half of the block-diagonal lamplighter gluing.**
Given a resolution of identity `G` by pairwise-orthogonal Hermitian idempotents,
per-block Hermitian involutions `A s` (with `A s² = G s`, supported on `G s`) and
per-block subspace unitaries `V s` (with `V s · (V s)* = (V s)* · V s = G s`,
supported on `G s`), both satisfying the per-block lamplighter relations, the
block-diagonal sums `A' = ∑ A s`, `T' = ∑ V s` form a pair of unitaries with
`A'² = 1` satisfying the integer lamplighter relation.
-/
set_option maxHeartbeats 1000000 in
lemma block_lamplighter_construction {σ : Type*} [Fintype σ] [DecidableEq σ]
    {G : σ → Matrix (Fin d) (Fin d) ℂ}
    (hGh : ∀ s, (G s).IsHermitian) (hGsum : ∑ s, G s = 1)
    (hGortho : ∀ s s', s ≠ s' → G s * G s' = 0)
    {A V : σ → Matrix (Fin d) (Fin d) ℂ}
    (hAsuppL : ∀ s, G s * A s = A s) (hAsuppR : ∀ s, A s * G s = A s)
    (hAh : ∀ s, (A s).IsHermitian) (hAsq : ∀ s, A s * A s = G s)
    (hVsuppL : ∀ s, G s * V s = V s) (hVsuppR : ∀ s, V s * G s = V s)
    (hVstarR : ∀ s, V s * (V s)ᴴ = G s)
    (hcomm : ∀ s (i : ℕ), Commute (A s) (V s ^ i * A s * ((V s)ᴴ) ^ i))
    (hcomm' : ∀ s (i : ℕ), Commute (A s) (((V s)ᴴ) ^ i * A s * V s ^ i)) :
    ∃ A' T' : unitaryGroup (Fin d) ℂ,
      (A' : Matrix (Fin d) (Fin d) ℂ) = ∑ s, A s ∧
      (T' : Matrix (Fin d) (Fin d) ℂ) = ∑ s, V s ∧
      (A' : Matrix (Fin d) (Fin d) ℂ) ^ 2 = 1 ∧
      (∀ i : ℤ, Commute (A' : unitaryGroup (Fin d) ℂ) (T' ^ (-i) * A' * T' ^ i)) := by
  -- Apply `block_involution` to construct `A'`.
  obtain ⟨A', hA'⟩ : ∃ A' : unitaryGroup (Fin d) ℂ, (A' : Matrix (Fin d) (Fin d) ℂ) = ∑ s, A s ∧ (A' : Matrix (Fin d) (Fin d) ℂ) ^ 2 = 1 := by
    obtain ⟨A', hA'⟩ : ∃ A' : Matrix (Fin d) (Fin d) ℂ, A' = ∑ s, A s ∧ A' * A' = 1 ∧ A'.IsHermitian := by
      exact ⟨ _, rfl, block_involution_sq hGsum hGortho hAsuppL hAsuppR hAsq, block_involution hGsum hGortho hAsuppL hAsuppR hAh hAsq |>.1 ⟩;
    refine' ⟨ ⟨ A', _, _ ⟩, _, _ ⟩ <;> simp_all +decide [ sq ];
    · convert hA'.2.1 using 1;
      simp +decide [ hA'.1, star ];
      exact congr_arg ( fun x => x * ∑ s, A s ) ( Finset.sum_congr rfl fun _ _ => by rw [ hAh _ ] );
    · simp_all +decide [ Matrix.IsHermitian, star ];
      aesop;
    · rw [ ← hA'.1, hA'.2.1 ];
  -- Apply `block_unitary` to construct `T'`.
  obtain ⟨T', hT'⟩ : ∃ T' : unitaryGroup (Fin d) ℂ, (T' : Matrix (Fin d) (Fin d) ℂ) = ∑ s, V s ∧ (T' : Matrix (Fin d) (Fin d) ℂ)ᴴ = ∑ s, (V s)ᴴ := by
    have := @block_unitary;
    exact ⟨ ⟨ _, this hGh hGsum hGortho hVsuppL hVsuppR hVstarR |>.1 ⟩, rfl, this hGh hGsum hGortho hVsuppL hVsuppR hVstarR |>.2 ⟩;
  refine' ⟨ A', T', hA'.1, hT'.1, _, _ ⟩;
  · exact hA'.2;
  · convert LamplighterStability.Section5.commute_orbit_int A' T' _ _;
    · intro n; convert LamplighterStability.Section5.block_orbit_commute hGh hGsum hGortho hAsuppL hAsuppR hVsuppL hVsuppR hcomm n using 1;
      · exact hA'.1;
      · simp +decide [ ← hA'.1, ← hT'.1 ];
        rfl;
    · convert LamplighterStability.Section5.block_orbit_commute hGh hGsum hGortho hAsuppL hAsuppR (fun s => ?_) (fun s => ?_) (fun s i => ?_) using 1;
      rotate_left;
      use fun s => ( V s ) ᴴ;
      · replace hVsuppR := congr_arg ( · ᴴ ) ( hVsuppR s ) ; simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ] ;
      · rw [ ← Matrix.conjTranspose_inj, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hGh s |> IsHermitian.eq ];
        exact hVsuppL s;
      · simpa using hcomm' s i;
      · simp +decide [ ← hA'.1, ← hT'.2, Commute ];
        rfl

/-
A block-diagonal sum `∑ s, A s` of operators each supported on its resolution
projection `G s` compresses to a single block: `G a · (∑ A) · G b = A a` when
`a = b` and `0` otherwise.
-/
lemma block_compress {σ : Type*} [Fintype σ] [DecidableEq σ]
    {G A : σ → Matrix (Fin d) (Fin d) ℂ}
    (hGortho : ∀ s s', s ≠ s' → G s * G s' = 0)
    (hAsuppL : ∀ s, G s * A s = A s) (hAsuppR : ∀ s, A s * G s = A s) (a b : σ) :
    G a * (∑ s, A s) * G b = if a = b then A a else 0 := by
  have h_sum : ∑ s, (G a * A s * G b) = if a = b then A a else 0 := by
    rw [ Finset.sum_eq_single a ];
    · by_cases hab : a = b <;> simp +decide [ hab, hAsuppL, hAsuppR ];
      have := hGortho a b hab; specialize hAsuppR a; replace hAsuppR := congr_arg ( · * G b ) hAsuppR; simp_all +decide [ mul_assoc ] ;
    · intro s _ hs; by_cases hs' : s = b <;> simp_all +decide [ mul_assoc ] ;
      · have := hGortho a b; by_cases ha : a = b <;> simp_all +decide [] ;
        rw [ ← hAsuppL b, ← mul_assoc, hGortho a b ha, Matrix.zero_mul ];
      · simp +decide [ ← mul_assoc ];
        rw [ mul_assoc, ← hAsuppR, mul_assoc, hGortho _ _ hs', mul_zero, mul_zero ];
    · aesop;
  simpa only [ Finset.mul_sum _ _ _, Finset.sum_mul, Matrix.mul_assoc ] using h_sum

/-
**Master Pythagoras for a block-diagonal approximation.**  For a resolution
of identity `G` by pairwise-orthogonal Hermitian idempotents and a block-diagonal
family `A` (each `A s` supported on `G s`), the squared HS distance of any `X`
from the block-diagonal sum `∑ s, A s` splits over the block grid:
`‖X − ∑ A‖² = ∑_a ∑_b ‖G_a X G_b − [a=b] A_a‖²`.
-/
lemma block_diff_double_pyth {σ : Type*} [Fintype σ] [DecidableEq σ]
    {G A : σ → Matrix (Fin d) (Fin d) ℂ}
    (hGh : ∀ s, (G s).IsHermitian) (hGi : ∀ s, IsIdempotentElem (G s))
    (hGsum : ∑ s, G s = 1) (hGortho : ∀ s s', s ≠ s' → G s * G s' = 0)
    (hAsuppL : ∀ s, G s * A s = A s) (hAsuppR : ∀ s, A s * G s = A s)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    normHS (X - ∑ s, A s) ^ 2
      = ∑ a, ∑ b, normHS (G a * X * G b - (if a = b then A a else 0)) ^ 2 := by
  rw [← LamplighterStability.normHS_sq_double_pyth hGh hGi hGsum (X - ∑ s, A s)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_sub, Matrix.sub_mul, block_compress hGortho hAsuppL hAsuppR a b]

/-
**Block-diagonal closeness with vanishing off-diagonal** (the `B₀` case).
If moreover the off-diagonal compressions `G a X G b` (`a ≠ b`) vanish — e.g.
because `X` commutes with every `G s` — then only the diagonal blocks survive:
`‖X − ∑ A‖² = ∑_a ‖G_a X G_a − A_a‖²`.
-/
lemma block_diff_diag_pyth {σ : Type*} [Fintype σ] [DecidableEq σ]
    {G A : σ → Matrix (Fin d) (Fin d) ℂ}
    (hGh : ∀ s, (G s).IsHermitian) (hGi : ∀ s, IsIdempotentElem (G s))
    (hGsum : ∑ s, G s = 1) (hGortho : ∀ s s', s ≠ s' → G s * G s' = 0)
    (hAsuppL : ∀ s, G s * A s = A s) (hAsuppR : ∀ s, A s * G s = A s)
    {X : Matrix (Fin d) (Fin d) ℂ}
    (hXoff : ∀ a b, a ≠ b → G a * X * G b = 0) :
    normHS (X - ∑ s, A s) ^ 2
      = ∑ a, normHS (G a * X * G a - A a) ^ 2 := by
  convert block_diff_double_pyth hGh hGi hGsum hGortho hAsuppL hAsuppR X using 2 with a b;
  rw [ Finset.sum_eq_single a ] <;> simp_all +decide [];
  intro b hb; rw [ if_neg ( Ne.symm hb ) ] ; simp +decide [ hXoff a b ( Ne.symm hb ) ] ;

end LamplighterStability.Section5