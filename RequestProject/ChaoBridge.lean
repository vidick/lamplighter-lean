import RequestProject.ProjectionTowers
import RequestProject.ChaoOverlapping

/-!
# Bridge: from the Frobenius Chao theorem to the normalized HS interface

The externally supplied file `RequestProject.ChaoOverlapping` proves Theorem 3.2
of Chao et al. (`Overlapping.separating_projections`) for the **unnormalized**
Frobenius norm `‖A‖_F = √(∑_{i,j} |A_{i,j}|²)`, with smallness threshold
`ε ≤ 1/(48 n)` and displacement bound `8 n ε`.

The rest of this project (and the paper) works with the **normalized**
Hilbert–Schmidt norm `normHS A = √((1/d)·∑_{i,j} |A_{i,j}|²)`. The two are
related by the dimension factor
`‖A‖_F = √d · normHS A`  (`frob_eq_card_mul_normHS`).

Because this factor is uniform, the Frobenius theorem yields, verbatim, the
normalized statement **provided the threshold is scaled by `√d`**: this is
`chao_commuting_projections_dim`, which is fully proved here.

The paper's cited statement (`chao_commuting_projections`, in
`RequestProject.CommutingProjections`) instead asks for the *dimension-free*
threshold `ε₀ ≤ 1/(32 n)`. That stronger (dimension-free) constant is **not**
obtainable from the sequential block-diagonalization argument formalized in
`ChaoOverlapping`: in the normalized norm the cross term of the
block-diagonalization lemma picks up a factor of `√d` from Hilbert–Schmidt
submultiplicativity (`normHS (A * B) ≤ √d · normHS A · normHS B`), and replacing
it by the dimension-free operator-norm bound `‖A‖_op ≤ 1` makes the per-step
commutator growth multiplicative (exponential in `n`) instead of additive. The
dimension-free linear bound `8 n ε₀` is exactly the genuinely external content
cited (but not reproved) in the paper.
-/

namespace LamplighterStability

open scoped BigOperators Matrix.Norms.Frobenius
open Matrix

variable {d : ℕ}

/-- The Frobenius norm equals `√d` times the normalized Hilbert–Schmidt norm. -/
theorem frob_eq_card_mul_normHS (A : Matrix (Fin d) (Fin d) ℂ) :
    ‖A‖ = Real.sqrt (Fintype.card (Fin d)) * normHS A := by
  rw [Matrix.frobenius_norm_def, normHS, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_mul (by positivity)]
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp
  · have hc : (Fintype.card (Fin d) : ℝ) ≠ 0 := by simp [h.ne']
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
    simp only [Real.rpow_natCast]
    field_simp

/-- The normalized Hilbert–Schmidt norm equals the Frobenius norm divided by `√d`. -/
theorem normHS_eq_frob_div (A : Matrix (Fin d) (Fin d) ℂ) :
    normHS A = ‖A‖ / Real.sqrt (Fintype.card (Fin d)) := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp [normHS, Matrix.frobenius_norm_def]
  · have hc : Real.sqrt (Fintype.card (Fin d)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (by simp [h]))
    rw [frob_eq_card_mul_normHS]; field_simp

/-- The project's `IsProj` and the imported `Overlapping.IsProj` agree
(both mean Hermitian and idempotent). -/
theorem isProj_iff_overlapping (Q : Matrix (Fin d) (Fin d) ℂ) :
    IsProj Q ↔ Overlapping.IsProj Q := Iff.rfl

/-- The Lie bracket of matrices is the Chao-file commutator. -/
theorem lie_eq_comm (A B : Matrix (Fin d) (Fin d) ℂ) :
    ⁅A, B⁆ = Overlapping.comm A B := by
  simp [Ring.lie_def, Overlapping.comm]

/-
**Chao et al., Theorem 3.2 — normalized HS norm, dimension-aware threshold.**

This is the faithful normalized-norm consequence of the imported Frobenius
theorem `Overlapping.separating_projections`. An almost-commuting family of `n`
projections with pairwise normalized-HS commutator at most `ε₀ ≤ 1/(48 n √d)` is
`8 n ε₀`-close, in the normalized HS norm, to a genuinely commuting family of
projections.

Compared to the paper's `chao_commuting_projections`, the only difference is the
threshold, which here carries the dimension factor `√d` (see the module
docstring): this is precisely what the `√d` in Hilbert–Schmidt submultiplicativity
costs the sequential argument.
-/
theorem chao_commuting_projections_dim {n : ℕ} {ε₀ : ℝ}
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i))
    (hcomm : ∀ i j, normHS (⁅P i, P j⁆) ≤ ε₀)
    (hε : ε₀ ≤ 1 / (48 * (n : ℝ) * Real.sqrt d)) :
    ∃ Q : Fin n → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, IsProj (Q i)) ∧ (∀ i j, Commute (Q i) (Q j)) ∧
      (∀ i, normHS (Q i - P i) ≤ 8 * (n : ℝ) * ε₀) := by
  by_cases hd : d = 0;
  · use fun i => P i; simp_all +decide [ normHS ] ;
    exact ⟨ fun i j => by subst hd; exact Subsingleton.elim _ _, fun i => by nlinarith [ hcomm i i ] ⟩;
  · by_cases hn : n = 0;
    · aesop;
    · obtain ⟨Q, hQ⟩ : ∃ Q : Fin n → Matrix (Fin d) (Fin d) ℂ, (∀ i, Overlapping.IsProj (Q i)) ∧ (∀ i j, Overlapping.comm (Q i) (Q j) = 0) ∧ (∀ i, ‖P i - Q i‖ ≤ 8 * n * (Real.sqrt d * ε₀)) := by
        apply Overlapping.separating_projections;
        · exact mul_nonneg ( Real.sqrt_nonneg _ ) ( le_trans ( by exact normHS_nonneg _ ) ( hcomm ⟨ 0, Nat.pos_of_ne_zero hn ⟩ ⟨ 0, Nat.pos_of_ne_zero hn ⟩ ) );
        · rw [ le_div_iff₀ ] at * <;> first | positivity | nlinarith [ Real.sqrt_nonneg d, Real.sq_sqrt <| Nat.cast_nonneg d ] ;
        · exact fun i => isProj_iff_overlapping _ |>.1 ( hP i );
        · intro i j; specialize hcomm i j; rw [ ← lie_eq_comm ] at *;
          rw [ frob_eq_card_mul_normHS ];
          simpa using mul_le_mul_of_nonneg_left hcomm <| Real.sqrt_nonneg _;
      refine' ⟨ Q, _, _, _ ⟩;
      · exact fun i => isProj_iff_overlapping _ |>.2 ( hQ.1 i );
      · exact fun i j => sub_eq_zero.mp ( hQ.2.1 i j );
      · intro i; specialize hQ; have := hQ.2.2 i; rw [ normHS_eq_frob_div ] ; simp_all +decide [ norm_sub_rev ] ;
        rw [ div_le_iff₀ ( by positivity ) ] ; linarith [ hQ.2.2 i ]

end LamplighterStability