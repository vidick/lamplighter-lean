import Mathlib
import RequestProject.HSReflections

/-!
# Separation of nearly-commuting projections in the normalized Hilbert–Schmidt norm

This file formalizes **Theorem 1** of `gh_hs_projection_note_revised-1.pdf` ("Separating Nearly
Commuting Projections in Normalized Hilbert–Schmidt Norm"):

> If `P₁,…,P_N` are projections on `ℂ^d` with `‖[Pᵢ,Pⱼ]‖₂,d ≤ ε` for all `i,j`, then there exist
> pairwise commuting projections `Q₁,…,Q_N` with `‖Pᵢ − Qᵢ‖₂,d ≤ 5·N(N−1)·ε`.

The proof reduces the projections to reflections `Uᵢ = 1 − 2Pᵢ`, packages them into an
`η`-representation of `(ℤ/2ℤ)ᴺ` with `η = 2N(N−1)ε` (the swap-counting estimate of
`HSReflections`), applies the **same-dimensional stability** result for finite abelian groups
(`Corollary 1` of the note, with the explicit constant `5`; here stated as the hypothesis
`AbelianStability` and discharged separately in `RequestProject.HSStability`), and rounds the
resulting genuine representation back to commuting projections.

The main results are `hs_separation` (`5·N(N−1)·ε` bound) and its `N²`-form corollary
`hs_separation_N2` (`≤ 5·N²·ε`).
-/

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators
open Finset

variable {d : ℕ}

/-! ### Small extra algebra API -/

/-
A unitary that squares to the identity is self-adjoint.
-/
lemma selfadjoint_of_unitary_sq {u : H d →L[ℂ] H d}
    (hu : u ∈ unitary (H d →L[ℂ] H d)) (h2 : u * u = 1) :
    ContinuousLinearMap.adjoint u = u := by
  have h_adj : star u * u = 1 := by
    exact hu.1;
  convert congr_arg ( fun x => x * u ) h_adj using 1 ; simp +decide [ mul_assoc, h2 ];
  rfl

/-
`Q = (1 - S)/2` is a projection when `S` is a self-adjoint unitary.
-/
lemma Q_isProj {S : H d →L[ℂ] H d} (hSa : ContinuousLinearMap.adjoint S = S) (hS2 : S * S = 1) :
    IsProjCLM ((2 : ℂ)⁻¹ • (1 - S)) := by
  constructor;
  · convert congr_arg ( fun x => ( 2⁻¹ : ℂ ) • x ) ( show ( ContinuousLinearMap.adjoint ( 1 - S ) ) = 1 - S from ?_ ) using 1;
    · ext; simp [ContinuousLinearMap.adjoint];
      exact Or.inl <| by norm_num [ Complex.ext_iff ] ;
    · ext; simp [hSa];
      erw [ ContinuousLinearMap.adjoint_id ] ; norm_num;
  · convert congr_arg ( fun x : H d →L[ℂ] H d => ( 2⁻¹ : ℂ ) • ( 2⁻¹ : ℂ ) • ( 1 - S - S + x ) ) hS2 using 1 <;> norm_num ; ring;
    · ext; norm_num; ring;
    · module

/-
The projections `(1 - S)/2` and `(1 - T)/2` commute when `S` and `T` do.
-/
lemma Q_commute {S T : H d →L[ℂ] H d} (h : S * T = T * S) :
    ((2 : ℂ)⁻¹ • (1 - S)) * ((2 : ℂ)⁻¹ • (1 - T))
      = ((2 : ℂ)⁻¹ • (1 - T)) * ((2 : ℂ)⁻¹ • (1 - S)) := by
  ext; simp +decide [];
  rw [ ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, h ] ; ring

/-
The displacement of `P` from `Q = (1 - S)/2` is half the displacement of the reflection.
-/
lemma hsNorm_P_sub_Q (P S : H d →L[ℂ] H d) :
    hsNorm (P - (2 : ℂ)⁻¹ • (1 - S)) = (2 : ℝ)⁻¹ * hsNorm (reflOp P - S) := by
  convert hsNorm_smul ( 2⁻¹ : ℂ ) ( reflOp P - S ) using 1;
  · unfold reflOp;
    rw [ ← hsNorm_neg ] ; congr ; ext ; norm_num ; ring;
  · norm_num [ Norm.norm ]

/-! ### The same-dimensional stability input (note Corollary 1) -/

/-- **Same-dimensional stability for finite abelian groups** (note Corollary 1, constant `5`),
stated as a hypothesis.  It asserts: from a `‖·‖₂,d`-`δ`-representation of a finite abelian group
`G` (`f(1) = 1`) one obtains a *genuine* unitary representation `σ : G →* U(H)` on the **same**
Hilbert space `H = ℂ^d`, with `‖f(x) − σ(x)‖₂,d ≤ 5·δ` for every `x`.

This is the analytic heart of the note's argument.  It is proved in `RequestProject.HSStability`
from the weak (averaged) Gowers–Hatami theorem via the note's translation-regularization
(Lemma 1) and almost-invariant-subspace rounding (Lemma 2).  Everything else in the note's proof
of Theorem 1 (reduction to reflections, the swap-counting `η`-representation bound, rounding back
to commuting projections, and the edge case `N ≤ 1`) is proved unconditionally in this file. -/
def AbelianStability (d : ℕ) : Prop :=
  0 < d → ∀ {G : Type} [CommGroup G] [Fintype G] [DecidableEq G]
    (f : G → (H d →L[ℂ] H d)), (∀ g, f g ∈ unitary (H d →L[ℂ] H d)) → f 1 = 1 →
    ∀ (δ : ℝ), 0 ≤ δ →
    (∀ x y, hsNorm (f x * f y - f (x * y)) ≤ δ) →
    ∃ σ : G →* (H d →L[ℂ] H d),
      (∀ g, σ g ∈ unitary (H d →L[ℂ] H d)) ∧
      (∀ x, hsNorm (f x - σ x) ≤ 5 * δ)

/-! ### Main reduction -/

/-
The main branch (`N ≥ 2`): apply same-dimensional stability to the swap-counting
`η`-representation and round back to commuting projections.
-/
lemma exists_commuting_proj {N : ℕ} (hAS : AbelianStability d) (hd : 0 < d)
    (P : Fin N → (H d →L[ℂ] H d)) (hP : ∀ i, IsProjCLM (P i))
    (ε : ℝ) (hε0 : 0 ≤ ε)
    (hc : ∀ i j, hsNorm (reflOp (P i) * reflOp (P j) - reflOp (P j) * reflOp (P i)) ≤ 4 * ε)
    (hN : 2 ≤ N) :
    ∃ Q : Fin N → (H d →L[ℂ] H d),
      (∀ i, IsProjCLM (Q i)) ∧ (∀ i j, Q i * Q j = Q j * Q i) ∧
      (∀ i, hsNorm (P i - Q i) ≤ 5 * ((N : ℝ) * ((N : ℝ) - 1)) * ε) := by
  have hδ0 : (0 : ℝ) ≤ 2 * N * (N - 1) * ε := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_of_lt hN
    have : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
    positivity
  obtain ⟨σ, hσ⟩ : ∃ σ : (Multiplicative (Fin N → ZMod 2)) →* (H d →L[ℂ] H d),
      (∀ g, σ g ∈ unitary (H d →L[ℂ] H d)) ∧
      (∀ x, hsNorm (fCLM P (Multiplicative.toAdd x) - σ x) ≤ 5 * (2 * N * (N - 1) * ε)) :=
    hAS hd (fun g => fCLM P (Multiplicative.toAdd g)) (fun g => fCLM_unitary P hP _)
      (by simpa using fCLM_zero P) (2 * N * (N - 1) * ε) hδ0
      (by intro x y
          simpa using hsNorm_fCLM_eta P hP ε hε0 hc
            (Multiplicative.toAdd x) (Multiplicative.toAdd y))
  -- Each generator squares to the identity in `G`, hence `σ` of it squares to `1`.
  have hsq : ∀ i : Fin N, σ (Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)))
      * σ (Multiplicative.ofAdd (Pi.single i 1)) = 1 := by
    intro i
    rw [← map_mul, ← ofAdd_add]
    have hadd : (Pi.single i 1 : Fin N → ZMod 2) + Pi.single i 1 = 0 := by
      rw [← Pi.single_add]
      simp [show (1 : ZMod 2) + 1 = 0 from by decide]
    rw [hadd, ofAdd_zero, map_one]
  refine ⟨fun i => (2 : ℂ)⁻¹ • (1 - σ (Multiplicative.ofAdd (Pi.single i 1))), ?_, ?_, ?_⟩
  · intro i
    exact Q_isProj (selfadjoint_of_unitary_sq (hσ.1 _) (hsq i)) (hsq i)
  · intro i j
    refine Q_commute ?_
    rw [← σ.map_mul, ← σ.map_mul]
    exact congr_arg _ (mul_comm _ _)
  · intro i
    have h_close : hsNorm (reflOp (P i) - σ (Multiplicative.ofAdd (Pi.single i 1)))
        ≤ 5 * (2 * N * (N - 1) * ε) := by
      simpa [fCLM_single P i] using hσ.2 (Multiplicative.ofAdd (Pi.single i 1))
    rw [hsNorm_P_sub_Q]
    calc (2 : ℝ)⁻¹ * hsNorm (reflOp (P i) - σ (Multiplicative.ofAdd (Pi.single i 1)))
        ≤ (2 : ℝ)⁻¹ * (5 * (2 * N * (N - 1) * ε)) :=
          mul_le_mul_of_nonneg_left h_close (by norm_num)
      _ = 5 * ((N : ℝ) * ((N : ℝ) - 1)) * ε := by ring

/-
**Normalized Hilbert–Schmidt separation of projections** (note Theorem 1).
If `P₁,…,P_N` are projections with pairwise commutators of normalized HS norm at most `ε`, then
there exist pairwise commuting projections `Q₁,…,Q_N` with
`‖Pᵢ − Qᵢ‖₂,d ≤ 5·N(N−1)·ε`.
-/
theorem hs_separation {N : ℕ} (hAS : AbelianStability d) (hd : 0 < d)
    (P : Fin N → (H d →L[ℂ] H d)) (hP : ∀ i, IsProjCLM (P i))
    (ε : ℝ) (hε0 : 0 ≤ ε)
    (hcomm : ∀ i j, hsNorm (P i * P j - P j * P i) ≤ ε) :
    ∃ Q : Fin N → (H d →L[ℂ] H d),
      (∀ i, IsProjCLM (Q i)) ∧ (∀ i j, Q i * Q j = Q j * Q i) ∧
      (∀ i, hsNorm (P i - Q i) ≤ 5 * ((N : ℝ) * ((N : ℝ) - 1)) * ε) := by
  by_cases hN : 2 ≤ N
  · -- `N ≥ 2`: the main branch.
    exact exists_commuting_proj hAS hd P hP ε hε0
      (fun i j => hsNorm_comm_reflOp (P i) (P j) ε (hcomm i j)) hN
  · -- `N ≤ 1`: take `Q = P`.  The displacement bound is `0`.
    push_neg at hN
    refine ⟨P, hP, ?_, ?_⟩
    · intro i j
      interval_cases N
      · exact i.elim0
      · have : i = j := Subsingleton.elim _ _
        rw [this]
    · intro i
      have hzero : 5 * ((N : ℝ) * ((N : ℝ) - 1)) * ε = 0 := by
        interval_cases N
        · exact i.elim0
        · norm_num
      rw [hzero, sub_self, hsNorm_zero]

/-- **Normalized Hilbert–Schmidt separation, `N²` form** (note Theorem 1, "In particular" clause).
The displacement bound `5·N(N−1)·ε` is dominated by `5·N²·ε`. -/
theorem hs_separation_N2 {N : ℕ} (hAS : AbelianStability d) (hd : 0 < d)
    (P : Fin N → (H d →L[ℂ] H d)) (hP : ∀ i, IsProjCLM (P i))
    (ε : ℝ) (hε0 : 0 ≤ ε)
    (hcomm : ∀ i j, hsNorm (P i * P j - P j * P i) ≤ ε) :
    ∃ Q : Fin N → (H d →L[ℂ] H d),
      (∀ i, IsProjCLM (Q i)) ∧ (∀ i j, Q i * Q j = Q j * Q i) ∧
      (∀ i, hsNorm (P i - Q i) ≤ 5 * (N : ℝ) ^ 2 * ε) := by
  obtain ⟨Q, hQp, hQc, hQb⟩ := hs_separation hAS hd P hP ε hε0 hcomm
  refine ⟨Q, hQp, hQc, fun i => (hQb i).trans ?_⟩
  have hNN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  nlinarith [hε0, sq_nonneg ((N : ℝ)), mul_nonneg hNN hε0]

end
