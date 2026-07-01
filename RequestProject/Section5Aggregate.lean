import Mathlib
import RequestProject.Section5BackHalf

/-!
# Section 5 aggregate gluing (`tower_rep_final` final step, abstract form)

This file provides the single abstract lemma `aggregate_block_rep` that packages
the global block-diagonal construction of the nearby representation together with
the two Pythagorean closeness bounds, in exactly the output shape required by
`Section5Assembly.tower_rep_final`.

Given a resolution of identity `G` by pairwise-orthogonal Hermitian idempotents,
per-block Hermitian involutions `A s` and subspace unitaries `V s` satisfying the
per-block lamplighter relations, a unitary `T`, and a "center" matrix `Bc`
commuting with every block, it produces unitaries `A', T'` with `A'² = 1`, the
integer lamplighter relation, and:

* `‖Bc − A'‖²_HS ≤ boundA`, derived from the diagonal-only Pythagoras
  (`block_diff_diag_pyth`, off-diagonal vanishing because `Bc` commutes with each
  `G s`), with `boundA` an upper bound for `∑_s ‖G_s Bc G_s − A_s‖²`;
* `‖T − T'‖²_HS ≤ boundT`, derived from the master Pythagoras
  (`block_diff_double_pyth`), with `boundT` an upper bound for the diagonal mass
  `∑_s ‖G_s T G_s − V_s‖²` plus the off-diagonal mass
  `∑_a ∑_{b≠a} ‖G_a T G_b‖²`.

The caller (`tower_rep_final`) supplies the per-block data via
`block_rep_of_approx_tower` (plus the error block) and the bounds via the
measure-theoretic estimates.
-/

namespace LamplighterStability.Section5

open scoped BigOperators
open Matrix

variable {d : ℕ}

/-
**Aggregate block representation.**  Glue per-block lamplighter data over a
resolution of identity into a nearby representation `(A', T')`, with the two final
squared Hilbert–Schmidt closeness bounds discharged by Pythagoras.
-/
theorem aggregate_block_rep {σ : Type*} [Fintype σ] [DecidableEq σ]
    {G : σ → Matrix (Fin d) (Fin d) ℂ}
    (hGh : ∀ s, (G s).IsHermitian) (hGi : ∀ s, IsIdempotentElem (G s))
    (hGsum : ∑ s, G s = 1) (hGortho : ∀ s s', s ≠ s' → G s * G s' = 0)
    {A V : σ → Matrix (Fin d) (Fin d) ℂ}
    (hAsuppL : ∀ s, G s * A s = A s) (hAsuppR : ∀ s, A s * G s = A s)
    (hAh : ∀ s, (A s).IsHermitian) (hAsq : ∀ s, A s * A s = G s)
    (hVsuppL : ∀ s, G s * V s = V s) (hVsuppR : ∀ s, V s * G s = V s)
    (hVstarR : ∀ s, V s * (V s)ᴴ = G s)
    (hcomm : ∀ s (i : ℕ), Commute (A s) (V s ^ i * A s * ((V s)ᴴ) ^ i))
    (hcomm' : ∀ s (i : ℕ), Commute (A s) (((V s)ᴴ) ^ i * A s * V s ^ i))
    {Bc T : Matrix (Fin d) (Fin d) ℂ}
    (hBcomm : ∀ s, G s * Bc = Bc * G s)
    {boundA boundT : ℝ}
    (hboundA : ∑ s, normHS (G s * Bc * G s - A s) ^ 2 ≤ boundA)
    (hboundT : (∑ s, normHS (G s * T * G s - V s) ^ 2)
        + (∑ a, ∑ b ∈ Finset.univ.erase a, normHS (G a * T * G b) ^ 2) ≤ boundT) :
    ∃ A' T' : unitaryGroup (Fin d) ℂ,
      (A' : Matrix (Fin d) (Fin d) ℂ) ^ 2 = 1 ∧
      (∀ i : ℤ, Commute (A' : unitaryGroup (Fin d) ℂ) (T' ^ (-i) * A' * T' ^ i)) ∧
      normHS (Bc - (A' : Matrix (Fin d) (Fin d) ℂ)) ^ 2 ≤ boundA ∧
      normHS (T - (T' : Matrix (Fin d) (Fin d) ℂ)) ^ 2 ≤ boundT := by
  obtain ⟨A', T', hA', hT', hA_sq, hcomm⟩ := block_lamplighter_construction hGh hGsum hGortho hAsuppL hAsuppR hAh hAsq hVsuppL hVsuppR hVstarR hcomm hcomm';
  refine' ⟨ A', T', hA_sq, hcomm, _, _ ⟩;
  · have h_off_diag : ∀ a b, a ≠ b → G a * Bc * G b = 0 := by
      simp +contextual [ hBcomm, mul_assoc, hGortho ];
    have := block_diff_diag_pyth hGh hGi hGsum hGortho hAsuppL hAsuppR ( X := Bc ) ( hXoff := fun a b hab => by simp +decide [ h_off_diag a b hab ] ) ; aesop;
  · have := LamplighterStability.Section5.block_diff_double_pyth hGh hGi hGsum hGortho hVsuppL hVsuppR T;
    rw [ hT' ];
    rw [ this ];
    refine' le_trans _ hboundT;
    rw [ ← Finset.sum_add_distrib ];
    refine' Finset.sum_le_sum fun a _ => _;
    rw [ ← Finset.add_sum_erase _ _ ( Finset.mem_univ a ) ];
    exact add_le_add ( by simp +decide ) ( Finset.sum_le_sum fun b hb => by rw [ if_neg ( Ne.symm ( Finset.ne_of_mem_erase hb ) ) ] ; simp +decide )

end LamplighterStability.Section5