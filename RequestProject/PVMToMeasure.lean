import RequestProject.Foundations

open scoped BigOperators ComplexOrder
open Matrix

/-!
# From approximately equivariant PVMs to approximately invariant measures

This file formalizes **Lemma `lem:PVM-to-meas`** of the paper *"Polynomial
Hilbert–Schmidt stability of the lamplighter group"*: an approximately
equivariant projection-valued measure induces an approximately invariant
measure, with the *square* Hilbert–Schmidt defect controlling the
total-variation defect.

The mathematical content is the per-atom estimate
`|tr(E_x) - tr(F_x)| ≤ ‖F_x - T* E_x T‖_HS²`,
which is exactly the projection-trace inequality `proj_diff_bound`
(Lemma `lem:proj_diff_bound`) applied to the two projections `T* E_x T` and
`F_x`, together with the unitary invariance `tr(T* E_x T) = tr(E_x)`.  Summing
over the (finite) collection of atoms `x ∈ {0,1}^{F_M}` and using the
equivariance hypothesis `∑ ‖F_x - T* E_x T‖_HS² ≤ η` yields the bound `η` on the
total-variation defect `∑ |μ(⟦x⟧) - μ(L⟦x⟧)|`.

Here, in the language of the paper:

* `T` is the unitary implementing the dynamics;
* `E s` plays the role of `E_{⟦x⟧}` (the PVM on a cylinder), a projection;
* `F s` plays the role of `E_{L⟦x⟧}` (the PVM on the shifted cylinder), a
  projection;
* `μ(b) = tr(E_b)` is the induced measure, so `ntrace (E s)` is `μ(⟦x⟧)` and
  `ntrace (F s)` is `μ(L⟦x⟧)`;
* `star T * E s * T` is `T* E_{⟦x⟧} T`.
-/

namespace LamplighterStability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Conjugation by a unitary -/

omit [DecidableEq ι] in
/-- Conjugating a Hermitian matrix by a unitary `U` (as `U* A U`) stays
Hermitian. -/
lemma isHermitian_conj_unitary {U A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) : (star U * A * U).IsHermitian := by
  simp_all +decide [ Matrix.IsHermitian, Matrix.mul_assoc ];
  simp +decide [ ← Matrix.mul_assoc, ← star_eq_conjTranspose ]

/-- Conjugating an idempotent by a unitary `U` (as `U* A U`) stays idempotent. -/
lemma isIdempotentElem_conj_unitary {U : Matrix ι ι ℂ}
    (hU : U ∈ unitary (Matrix ι ι ℂ)) {A : Matrix ι ι ℂ}
    (hA : IsIdempotentElem A) : IsIdempotentElem (star U * A * U) := by
  simp_all +decide [ mul_assoc, IsIdempotentElem ];
  simp_all +decide [ ← mul_assoc ]

/-- The normalized trace is invariant under conjugation by a unitary:
`tr(U* A U) = tr(A)`. -/
lemma ntrace_conj_unitary {U : Matrix ι ι ℂ}
    (hU : U ∈ unitary (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) :
    ntrace (star U * A * U) = ntrace A := by
  convert ntrace_mul_comm ( star U * A ) U using 1 ; simp +decide [ ← mul_assoc ];
  cases hU ; aesop

/-! ## The PVM-to-measure inequality -/

/-- **Lemma `lem:PVM-to-meas`** (core per-atom-summed inequality).

Let `T` be a unitary and let `E F : σ → Matrix ι ι ℂ` be two families of
projections (Hermitian idempotents) indexed by a finite type `σ` (the atoms
`x ∈ {0,1}^{F_M}`).  Interpreting `μ(b) = tr(E_b)` as the induced probability
measure (so that `ntrace (E s)` is `μ(⟦x⟧)` and `ntrace (F s)` is `μ(L⟦x⟧)`),
the total-variation defect is bounded by the (squared Hilbert–Schmidt)
equivariance defect:
`∑ |tr(E s) - tr(F s)| ≤ ∑ ‖F s - T* E s T‖_HS²`. -/
lemma pvm_to_meas {σ : Type*} [Fintype σ]
    {T : Matrix ι ι ℂ} (hT : T ∈ unitary (Matrix ι ι ℂ))
    (E F : σ → Matrix ι ι ℂ)
    (hEh : ∀ s, (E s).IsHermitian) (hEi : ∀ s, IsIdempotentElem (E s))
    (hFh : ∀ s, (F s).IsHermitian) (hFi : ∀ s, IsIdempotentElem (F s)) :
    ∑ s, |ntrace (E s) - ntrace (F s)|
      ≤ ∑ s, normHS (F s - star T * E s * T) ^ 2 := by
  apply Finset.sum_le_sum
  intro s _
  rw [(ntrace_conj_unitary hT (E s)).symm]
  refine le_trans (proj_diff_bound (star T * E s * T) (F s)
    (isHermitian_conj_unitary (hEh s)) (isIdempotentElem_conj_unitary hT (hEi s))
    (hFh s) (hFi s)) ?_
  rw [normHS_sub_comm]

/-- **Lemma `lem:PVM-to-meas`** (as stated in the paper).

If the family is `(M,η)`-equivariant, i.e. the squared equivariance defect is at
most `η`, then the induced measure is `(M,η)`-invariant, i.e. the
total-variation defect is at most `η`. -/
lemma pvm_to_meas_le {σ : Type*} [Fintype σ]
    {T : Matrix ι ι ℂ} (hT : T ∈ unitary (Matrix ι ι ℂ))
    (E F : σ → Matrix ι ι ℂ)
    (hEh : ∀ s, (E s).IsHermitian) (hEi : ∀ s, IsIdempotentElem (E s))
    (hFh : ∀ s, (F s).IsHermitian) (hFi : ∀ s, IsIdempotentElem (F s))
    {η : ℝ} (hη : ∑ s, normHS (F s - star T * E s * T) ^ 2 ≤ η) :
    ∑ s, |ntrace (E s) - ntrace (F s)| ≤ η :=
  le_trans (pvm_to_meas hT E F hEh hEi hFh hFi) hη

end LamplighterStability
