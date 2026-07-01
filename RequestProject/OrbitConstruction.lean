import Mathlib
import RequestProject.Foundations
import RequestProject.OrbitInput

set_option maxHeartbeats 1000000

/-!
# Orbit construction (Section 5, step 0)

Given an order-two unitary `A₀` (`A₀² = 1`, `A₀` unitary, hence Hermitian) and a
unitary `T`, this file builds the orbit family `A_i = T^{-i} A₀ T^i` over the
window `Win M = [-M, M]` and verifies the abstract input hypotheses of
`OrbitInput.commuting_involutions_approxInvMeasure`:

* each `A_i` is a Hermitian involution;
* the family is exactly `T`-equivariant: `star T · A_i · T = A_{i+1}`;
* the pairwise commutators are small: `‖⁅A_i, A_j⁆‖ ≤ 5ε`, derived from the
  original orbit-commutator hypotheses `‖⁅A, T^{-i} A T^i⁆‖ ≤ ε` and the
  order-two closeness `‖A − A₀‖ ≤ ε`.
-/

namespace LamplighterStability.OrbitConstruction

open scoped BigOperators
open Matrix
open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.OrbitInput LamplighterStability.MeasureInstantiation
  LamplighterStability.MeasureBridge

variable {d : ℕ}

/-- The integer power `T^i` of a unitary, as a plain matrix. -/
noncomputable def Tz (T : unitaryGroup (Fin d) ℂ) (i : ℤ) :
    Matrix (Fin d) (Fin d) ℂ :=
  ((T ^ i : unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)

lemma Tz_mem (T : unitaryGroup (Fin d) ℂ) (i : ℤ) :
    Tz T i ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := (T ^ i).2

lemma Tz_mul (T : unitaryGroup (Fin d) ℂ) (i j : ℤ) :
    Tz T i * Tz T j = Tz T (i + j) := by
  unfold Tz; rw [_root_.zpow_add]; rfl

lemma Tz_zero (T : unitaryGroup (Fin d) ℂ) : Tz T 0 = 1 := by
  unfold Tz; simp

lemma Tz_star (T : unitaryGroup (Fin d) ℂ) (i : ℤ) :
    star (Tz T i) = Tz T (-i) := by
  unfold Tz
  have : ((T ^ (-i) : unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
      = ((star (T ^ i) : unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) := by
    rw [_root_.zpow_neg]; norm_cast
  rw [this]; rfl


/-- The orbit family `A_i = T^{-i} A₀ T^i`. -/
noncomputable def orbit (T : unitaryGroup (Fin d) ℂ) (A₀ : Matrix (Fin d) (Fin d) ℂ)
    (i : ℤ) : Matrix (Fin d) (Fin d) ℂ :=
  Tz T (-i) * A₀ * Tz T i

lemma orbit_isHermitian {T : unitaryGroup (Fin d) ℂ} {A₀ : Matrix (Fin d) (Fin d) ℂ}
    (hA₀h : A₀.IsHermitian) (i : ℤ) : (orbit T A₀ i).IsHermitian := by
  unfold orbit
  rw [Matrix.IsHermitian, conjTranspose_mul, conjTranspose_mul]
  rw [show (Tz T (-i))ᴴ = Tz T i from by rw [← Matrix.star_eq_conjTranspose, Tz_star]; ring_nf,
      show (Tz T i)ᴴ = Tz T (-i) from by rw [← Matrix.star_eq_conjTranspose, Tz_star],
      show (A₀)ᴴ = A₀ from hA₀h]
  rw [mul_assoc]

lemma orbit_involution {T : unitaryGroup (Fin d) ℂ} {A₀ : Matrix (Fin d) (Fin d) ℂ}
    (hA₀2 : A₀ * A₀ = 1) (i : ℤ) : orbit T A₀ i * orbit T A₀ i = 1 := by
  unfold orbit
  have h1 : Tz T i * Tz T (-i) = 1 := by rw [Tz_mul]; simp [Tz_zero]
  have key : Tz T (-i) * A₀ * Tz T i * (Tz T (-i) * A₀ * Tz T i)
      = Tz T (-i) * (A₀ * (Tz T i * Tz T (-i)) * A₀) * Tz T i := by
    simp only [mul_assoc]
  rw [key, h1, mul_one, hA₀2, mul_one, Tz_mul]; simp [Tz_zero]

lemma orbit_mem_unitary {T : unitaryGroup (Fin d) ℂ} {A₀ : Matrix (Fin d) (Fin d) ℂ}
    (hA₀ : A₀ ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (i : ℤ) :
    orbit T A₀ i ∈ unitary (Matrix (Fin d) (Fin d) ℂ) := by
  unfold orbit
  exact mul_mem (mul_mem (Tz_mem T (-i)) hA₀) (Tz_mem T i)

/-- The orbit is exactly `T`-equivariant. -/
lemma orbit_equiv {T : unitaryGroup (Fin d) ℂ} {A₀ : Matrix (Fin d) (Fin d) ℂ} (i : ℤ) :
    star (T : Matrix (Fin d) (Fin d) ℂ) * orbit T A₀ i * (T : Matrix (Fin d) (Fin d) ℂ)
      = orbit T A₀ (i + 1) := by
  unfold orbit
  have hTstar : star (T : Matrix (Fin d) (Fin d) ℂ) = Tz T (-1) := by
    have : (T : Matrix (Fin d) (Fin d) ℂ) = Tz T 1 := by unfold Tz; simp
    rw [this, Tz_star]
  have hT1 : (T : Matrix (Fin d) (Fin d) ℂ) = Tz T 1 := by unfold Tz; simp
  rw [hTstar, hT1]
  have key : Tz T (-1) * (Tz T (-i) * A₀ * Tz T i) * Tz T 1
      = (Tz T (-1) * Tz T (-i)) * A₀ * (Tz T i * Tz T 1) := by
    simp only [mul_assoc]
  rw [key, Tz_mul, Tz_mul]
  ring_nf

/-
Commutator conjugation: `⁅A_i, A_j⁆ = T^{-i} ⁅A₀, A_{j-i}⁆ T^i`.
-/
lemma orbit_commutator_conj {T : unitaryGroup (Fin d) ℂ} {A₀ : Matrix (Fin d) (Fin d) ℂ}
    (i j : ℤ) :
    ⁅orbit T A₀ i, orbit T A₀ j⁆
      = Tz T (-i) * ⁅A₀, orbit T A₀ (j - i)⁆ * Tz T i := by
  unfold orbit;
  simp +decide [ sub_eq_add_neg ];
  simp +decide [ Tz_mul, mul_assoc, sub_mul, mul_sub, LieRing.of_associative_ring_bracket ];
  simp +decide [ ← mul_assoc, Tz_mul ]

/-
The commutator norm is conjugation-invariant.
-/
lemma orbit_commutator_normHS {T : unitaryGroup (Fin d) ℂ} {A₀ : Matrix (Fin d) (Fin d) ℂ}
    (i j : ℤ) :
    normHS ⁅orbit T A₀ i, orbit T A₀ j⁆ = normHS ⁅A₀, orbit T A₀ (j - i)⁆ := by
  rw [ orbit_commutator_conj ];
  convert normHS_unitary_left (Tz_mem T (-i)) (⁅A₀, orbit T A₀ (j - i)⁆ * Tz T i) using 1;
  · rw [ ← Matrix.mul_assoc ];
  · rw [ ← normHS_unitary_right ( Tz_mem T i ) ]

/-
`‖orbit T A₀ k − orbit T A₀' k‖ = ‖A₀ − A₀'‖`.
-/
lemma orbit_sub_normHS {T : unitaryGroup (Fin d) ℂ} (A₀ A₀' : Matrix (Fin d) (Fin d) ℂ)
    (k : ℤ) : normHS (orbit T A₀ k - orbit T A₀' k) = normHS (A₀ - A₀') := by
  unfold orbit;
  convert LamplighterStability.normHS_unitary_left ( Tz_mem T ( -k ) ) ( ( A₀ - A₀' ) * Tz T k ) using 1;
  · simp +decide only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub];
  · convert LamplighterStability.normHS_unitary_right ( Tz_mem T k ) ( A₀ - A₀' ) |> Eq.symm using 1

/-
Commutator perturbation for unitaries: replacing both arguments within HS
distance `ε` changes the commutator HS-norm by at most `4ε`.
-/
lemma commutator_perturb_le {P Q P' Q' : Matrix (Fin d) (Fin d) ℂ} {ε : ℝ}
    (hP : P ∈ unitary (Matrix (Fin d) (Fin d) ℂ))
    (hQ : Q ∈ unitary (Matrix (Fin d) (Fin d) ℂ))
    (hP' : P' ∈ unitary (Matrix (Fin d) (Fin d) ℂ))
    (hQ' : Q' ∈ unitary (Matrix (Fin d) (Fin d) ℂ))
    (hPP : normHS (P - P') ≤ ε) (hQQ : normHS (Q - Q') ≤ ε) :
    normHS ⁅P, Q⁆ ≤ normHS ⁅P', Q'⁆ + 4 * ε := by
  -- Write `⁅P,Q⁆ - ⁅P',Q'⁆ = (P*Q - P'*Q') - (Q*P - Q'*P')`.
  have h_diff : normHS (⁅P, Q⁆ - ⁅P', Q'⁆) ≤ 4 * ε := by
    have h_diff : normHS (P * Q - P' * Q') ≤ 2 * ε ∧ normHS (Q * P - Q' * P') ≤ 2 * ε := by
      have h_first : normHS (P * Q - P' * Q') ≤ normHS (P * (Q - Q')) + normHS ((P - P') * Q') := by
        convert normHS_add_le ( P * ( Q - Q' ) ) ( ( P - P' ) * Q' ) using 2 ; simp +decide [ mul_sub, sub_mul ];
      exact ⟨ h_first.trans ( by linarith [ normHS_unitary_left hP ( Q - Q' ), normHS_unitary_right hQ' ( P - P' ) ] ), by rw [ show Q * P - Q' * P' = Q * ( P - P' ) + ( Q - Q' ) * P' by simp +decide [ mul_sub, sub_mul ] ] ; linarith [ normHS_add_le ( Q * ( P - P' ) ) ( ( Q - Q' ) * P' ), normHS_unitary_left hQ ( P - P' ), normHS_unitary_right hP' ( Q - Q' ) ] ⟩;
    have h_diff : normHS (⁅P, Q⁆ - ⁅P', Q'⁆) ≤ normHS (P * Q - P' * Q') + normHS (Q * P - Q' * P') := by
      have h_diff : normHS (⁅P, Q⁆ - ⁅P', Q'⁆) ≤ normHS ((P * Q - P' * Q') - (Q * P - Q' * P')) := by
        exact le_of_eq ( by rw [ show ⁅P, Q⁆ = P * Q - Q * P from rfl, show ⁅P', Q'⁆ = P' * Q' - Q' * P' from rfl ] ; abel_nf );
      exact h_diff.trans ( normHS_sub_le _ _ );
    linarith;
  have h_reverse_triangle : normHS ⁅P, Q⁆ ≤ normHS ⁅P', Q'⁆ + normHS (⁅P, Q⁆ - ⁅P', Q'⁆) := by
    have h_triangle : normHS (⁅P', Q'⁆ + (⁅P, Q⁆ - ⁅P', Q'⁆)) ≤ normHS ⁅P', Q'⁆ + normHS (⁅P, Q⁆ - ⁅P', Q'⁆) := by
      convert normHS_add_le _ _ using 1
    aesop;
  linarith

/-
Symmetry of the relation commutator in `k`.
-/
lemma orbit_commutator_symm {T : unitaryGroup (Fin d) ℂ} {A₀ : Matrix (Fin d) (Fin d) ℂ}
    (k : ℤ) :
    normHS ⁅A₀, orbit T A₀ k⁆ = normHS ⁅A₀, orbit T A₀ (-k)⁆ := by
  unfold orbit;
  -- By the properties of the unitary group and the definition of `Tz`, we can simplify the expression.
  have h_simp : Tz T k * ⁅A₀, Tz T (-k) * A₀ * Tz T k⁆ * Tz T (-k) = -⁅A₀, Tz T k * A₀ * Tz T (-k)⁆ := by
    simp +decide [ mul_assoc, Tz, LieRing.of_associative_ring_bracket ];
    simp +decide [ mul_sub, sub_mul, mul_assoc ];
    simp +decide [ ← mul_assoc ];
  convert congr_arg normHS h_simp using 1;
  · convert normHS_unitary_left ( Tz_mem T k ) _ |> Eq.symm using 1;
    convert normHS_unitary_right ( Tz_mem T ( -k ) ) _ using 1;
  · rw [ LamplighterStability.normHS_neg ] ; norm_num

/-
An order-two unitary is Hermitian.
-/
lemma isHermitian_of_unitary_sq {A₀ : Matrix (Fin d) (Fin d) ℂ}
    (hA₀u : A₀ ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (hA₀2 : A₀ * A₀ = 1) :
    A₀.IsHermitian := by
  have := hA₀u.2; simp_all +decide [ Matrix.IsHermitian ] ;
  convert Matrix.inv_eq_left_inv hA₀2 using 1;
  rw [ Matrix.inv_eq_left_inv ];
  convert hA₀u.1 using 1

/-
Connect the integer orbit to the raw matrix powers used in the hypotheses.
-/
lemma orbit_natCast_eq (T : unitaryGroup (Fin d) ℂ) (A₀ : Matrix (Fin d) (Fin d) ℂ)
    (i : ℕ) :
    orbit T A₀ (i : ℤ)
      = (star (T : Matrix (Fin d) (Fin d) ℂ)) ^ i * A₀ * (T : Matrix (Fin d) (Fin d) ℂ) ^ i := by
  unfold orbit;
  simp +decide [ Tz ]

/-
The relation commutator `‖⁅A, A_k⁆‖ ≤ ε` for `|k| ≤ 2M`, reducing the
two-sided window to the one-sided hypothesis via `orbit_commutator_symm`.
-/
lemma orbit_A_bound {M : ℕ} {T : unitaryGroup (Fin d) ℂ}
    {A : Matrix (Fin d) (Fin d) ℂ} {ε : ℝ}
    (hcomm : ∀ i : ℕ, i ≤ 2 * M → normHS ⁅A, orbit T A (i : ℤ)⁆ ≤ ε)
    (k : ℤ) (hk : k.natAbs ≤ 2 * M) :
    normHS ⁅A, orbit T A k⁆ ≤ ε := by
  cases' Int.eq_nat_or_neg k with hk hk;
  rcases hk with ( rfl | rfl ) <;> simp_all +decide;
  convert hcomm _ hk using 1 ; exact orbit_commutator_symm _ ▸ rfl

/-
**Orbit input.**  From an order-two unitary `A₀` close to a unitary `A` and
the orbit-commutator hypotheses for `A`, build the orbit family
`A_i = T^{-i} A₀ T^i` over `Win (m+1)` and verify the abstract input of
`OrbitInput.commuting_involutions_approxInvMeasure` with commutator constant
`5ε`.
-/
theorem orbit_input (m : ℕ) (T : unitaryGroup (Fin d) ℂ)
    {A₀ : Matrix (Fin d) (Fin d) ℂ}
    (hA₀u : A₀ ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (hA₀2 : A₀ * A₀ = 1)
    (A : unitaryGroup (Fin d) ℂ) {ε : ℝ}
    (hA₀d : normHS ((A : Matrix (Fin d) (Fin d) ℂ) - A₀) ≤ ε)
    (hcomm : ∀ i : ℕ, i ≤ 2 * (m + 1) →
      normHS (⁅(A : Matrix (Fin d) (Fin d) ℂ),
        (star (T : Matrix (Fin d) (Fin d) ℂ)) ^ i * (A : Matrix (Fin d) (Fin d) ℂ)
          * (T : Matrix (Fin d) (Fin d) ℂ) ^ i⁆) ≤ ε) :
    (∀ i : Win (m + 1), (orbit T A₀ (i : ℤ)).IsHermitian) ∧
      (∀ i : Win (m + 1), orbit T A₀ (i : ℤ) * orbit T A₀ (i : ℤ) = 1) ∧
      (∀ i j : Win (m + 1), normHS ⁅orbit T A₀ (i : ℤ), orbit T A₀ (j : ℤ)⁆ ≤ 5 * ε) ∧
      (∀ i j : Win (m + 1), (j : ℤ) = (i : ℤ) + 1 →
        star (T : Matrix (Fin d) (Fin d) ℂ) * orbit T A₀ (i : ℤ)
            * (T : Matrix (Fin d) (Fin d) ℂ)
          = orbit T A₀ (j : ℤ)) := by
  refine' ⟨ _, _, _, _ ⟩;
  · exact fun i => orbit_isHermitian ( isHermitian_of_unitary_sq hA₀u hA₀2 ) _;
  · exact fun i => orbit_involution hA₀2 _;
  · -- By `orbit_commutator_normHS`, `normHS ⁅Afam i, Afam j⁆ = normHS ⁅A₀, orbit T A₀ k⁆`.
    intro i j
    set k := (j : ℤ) - (i : ℤ)
    have hk : k.natAbs ≤ 2 * (m + 1) := by
      grind +splitIndPred
    have hcomm_k : normHS ⁅A₀, orbit T A₀ k⁆ ≤ normHS ⁅(A : Matrix (Fin d) (Fin d) ℂ), orbit T (A : Matrix (Fin d) (Fin d) ℂ) k⁆ + 4 * ε := by
      apply commutator_perturb_le hA₀u (orbit_mem_unitary hA₀u k) A.2 (orbit_mem_unitary A.2 k);
      · rw [ ← LamplighterStability.normHS_sub_comm ] ; aesop;
      · rw [ orbit_sub_normHS ];
        rw [ ← LamplighterStability.normHS_sub_comm ] ; aesop;
    convert hcomm_k.trans _ using 1;
    · convert orbit_commutator_normHS i j using 1;
    · convert add_le_add_right ( orbit_A_bound ( show ∀ i : ℕ, i ≤ 2 * ( m + 1 ) → normHS ⁅ ( A : Matrix ( Fin d ) ( Fin d ) ℂ ), orbit T ( A : Matrix ( Fin d ) ( Fin d ) ℂ ) ( i : ℤ ) ⁆ ≤ ε from fun i hi => ?_ ) k hk ) ( 4 * ε ) using 1;
      · ring;
      · ring;
      · convert hcomm i hi using 1;
        rw [ orbit_natCast_eq ];
  · intro i j hj; convert orbit_equiv i.1 using 1; aesop;

/-- **Measure input (combined).**  From the order-two reduction `A₀` and the
orbit-commutator hypotheses, build *commuting* Hermitian involutions `B` over
`Win (m+1)` that are close to the concrete orbit `A_i = T^{-i} A₀ T^i`, and whose
induced PVM probability measure is `(m, η)`-approximately invariant with
`η ≤ 2592·(m+1)^4·(5ε)²`.  This packages Section 5 steps 0–2 (orbit → commuting
involutions → approximately invariant measure) into the single interface consumed
by `prop_decomp`. -/
theorem measure_input (m : ℕ) (T : unitaryGroup (Fin d) ℂ)
    {A₀ : Matrix (Fin d) (Fin d) ℂ}
    (hA₀u : A₀ ∈ unitary (Matrix (Fin d) (Fin d) ℂ)) (hA₀2 : A₀ * A₀ = 1)
    (A : unitaryGroup (Fin d) ℂ) {ε : ℝ}
    (hA₀d : normHS ((A : Matrix (Fin d) (Fin d) ℂ) - A₀) ≤ ε)
    (hcomm : ∀ i : ℕ, i ≤ 2 * (m + 1) →
      normHS (⁅(A : Matrix (Fin d) (Fin d) ℂ),
        (star (T : Matrix (Fin d) (Fin d) ℂ)) ^ i * (A : Matrix (Fin d) (Fin d) ℂ)
          * (T : Matrix (Fin d) (Fin d) ℂ) ^ i⁆) ≤ ε) :
    ∃ B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (B i).IsHermitian) ∧ (∀ i, B i * B i = 1) ∧
      (∀ i j, Commute (B i) (B j)) ∧
      (∀ i, normHS (B i - orbit T A₀ (i : ℤ))
        ≤ 4 * ((2 * (m + 1) + 1 : ℕ) : ℝ) * (5 * ε)) ∧
      ApproxInvMeasure m (2592 * ((m : ℝ) + 1) ^ 4 * (5 * ε) ^ 2)
        (pvmMeasure (m + 1) (EpatB (m + 1) B)) := by
  obtain ⟨hh, h2, hcomm5, hequiv⟩ := orbit_input m T hA₀u hA₀2 A hA₀d hcomm
  exact commuting_involutions_approxInvMeasure m T.2
    (fun i => orbit T A₀ (i : ℤ)) hh h2 hcomm5 hequiv

end LamplighterStability.OrbitConstruction