import RequestProject.ProjectionTowers
import RequestProject.ChaoBridge
import RequestProject.ChaoN2
import RequestProject.CommutingProjections
import RequestProject.SepProj.Main

set_option maxHeartbeats 2000000

/-!
# Chao et al., Theorem 3.2 — the improved (linear) nearby-commuting-projections bound

This file states and **proves** the improved linear form of Chao et al.'s
nearby-commuting-projections theorem (`lem:ab-close`), in the project's
dimension-free normalized Hilbert–Schmidt vocabulary:

> `n` projections with pairwise normalized-HS commutators `≤ ε₀` are
> `8·n·ε₀`-close to a genuinely commuting family of projections,
> unconditionally in `ε₀`.

This is the bound the paper actually cites, and the one that recovers the `M²`
tolerance `ε = c·κ⁷/M²` for the main theorem (versus the `M³` supported by the
*quadratic* bound `5·n²·ε₀` proved in
`RequestProject.CommutingProjections`).

The proof is obtained by transferring the self-contained formalization of the
paper *"Separating Nearly Commuting Projections in Normalized Hilbert–Schmidt
Norm"* (`SepProj.separation_of_projections`, in `RequestProject.SepProj.*`) into
this project's vocabulary.  The transfer is purely notational:

* `LamplighterStability.normHS` on `Matrix (Fin d) (Fin d) ℂ` agrees with
  `SepProj.hsNorm d` (both are `√((1/d) ∑_{i,j} |·|²)`);
* `LamplighterStability.IsProj` (Hermitian + idempotent) is definitionally
  `SepProj.IsProj`;
* the Lie bracket `⁅·,·⁆` is `SepProj.comm` (`Ring.lie_def`).

The whole downstream pipeline (`AssemblyChao`, `OrbitInput`,
`OrbitConstruction`, `MeasureFull`, `MainAssembly`) builds on this linear
bound; see `IMPROVED_CHAO_PLAN.md`.

The underlying theorem `SepProj.separation_of_projections` is unconditional in
`ε₀` (it only needs `0 ≤ ε₀`), so this interface carries no smallness
hypothesis.
-/

namespace LamplighterStability

open scoped BigOperators
open Matrix

/-- **Chao et al., Theorem 3.2 (`lem:ab-close`) — improved linear,
dimension-free, normalized Hilbert–Schmidt form.**

An almost-commuting family of `n` projections with pairwise normalized-HS
commutator at most `ε₀` is `8·n·ε₀`-close, in the normalized HS norm,
to a genuinely commuting family of projections.

This is the *linear-in-`n`* bound, as opposed to the *quadratic* `5·n²·ε₀`
bound `chao_commuting_projections`. It is proved by transferring
`SepProj.separation_of_projections` (a self-contained formalization of the
underlying note) into this project's vocabulary. -/
theorem chao_commuting_projections_linear {d n : ℕ} {ε₀ : ℝ}
    (P : Fin n → Matrix (Fin d) (Fin d) ℂ) (hP : ∀ i, IsProj (P i))
    (hcomm : ∀ i j, normHS (⁅P i, P j⁆) ≤ ε₀) :
    ∃ Q : Fin n → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, IsProj (Q i)) ∧ (∀ i j, Commute (Q i) (Q j)) ∧
      (∀ i, normHS (Q i - P i) ≤ 8 * (n : ℝ) * ε₀) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨P, hP, fun i => i.elim0, fun i => i.elim0⟩
  have hε0 : 0 ≤ ε₀ := le_trans (normHS_nonneg _) (hcomm ⟨0, hn⟩ ⟨0, hn⟩)
  -- The normalized HS norm on `Fin d` matrices is exactly `SepProj.hsNorm d`.
  have hbridge : ∀ (X : Matrix (Fin d) (Fin d) ℂ), normHS X = SepProj.hsNorm d X := by
    intro X
    unfold normHS SepProj.hsNorm
    rw [SepProj.hsNormSq_eq_sum, Fintype.card_fin]
    congr 1
    ring
  -- `IsProj` is definitionally the same notion.
  have hP' : ∀ i, SepProj.IsProj (P i) := fun i => ⟨(hP i).1, (hP i).2⟩
  -- Translate the commutator hypothesis.
  have hcomm' : ∀ i j, SepProj.hsNorm d (SepProj.comm (P i) (P j)) ≤ ε₀ := by
    intro i j
    have h := hcomm i j
    rwa [hbridge, Ring.lie_def] at h
  obtain ⟨Q, hQproj, hQcomm, hQbound⟩ :=
    SepProj.separation_of_projections d n ε₀ hε0 P hP' hcomm'
  refine ⟨Q, fun i => ⟨(hQproj i).1, (hQproj i).2⟩, fun i j => hQcomm i j, ?_⟩
  intro i
  have h := hQbound i
  -- `normHS` is invariant under negation, so `‖Q i - P i‖ = ‖P i - Q i‖`.
  have hneg : SepProj.hsNorm d (Q i - P i) = SepProj.hsNorm d (P i - Q i) := by
    unfold SepProj.hsNorm
    congr 1
    rw [SepProj.hsNormSq_eq_sum, SepProj.hsNormSq_eq_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [show (Q i - P i) a b = -((P i - Q i) a b) by simp [Matrix.sub_apply], norm_neg]
  rw [hbridge, hneg]
  exact h

end LamplighterStability
