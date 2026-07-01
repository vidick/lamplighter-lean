import RequestProject.ProjectionTowers

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

/-!
# Block A of the roadmap: finishing the matrix side of the lamplighter argument

This file collects the remaining *self-contained linear-algebra* lemmas of the
*Projection towers* and *Proof of the main results* sections of the paper that
build directly on the already-proved infrastructure in
`RequestProject.ProjectionTowers` and `RequestProject.Foundations`.

* `claim_approx_inv_supp` — Claim `claim:approx_inv_supp`: the support of an
  approximate closed tower is approximately invariant under `R`.
* `p_ortho` — Lemma `lem:p-ortho`: an `L²`-type bound for blockwise sums of two
  pairwise-orthogonal projection families.
* `lem_lowd` — Lemma `lem:lowd` (Rounding approximate closed projection towers).

See `ROADMAP.md` for how these fit into the overall proof of Theorem 1.1.
-/

namespace LamplighterStability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-
**Claim `claim:approx_inv_supp`.** If `(P₀,…,P_{j-1}; R)` is an approximate
`(δ₁,δ₂)`-closed projection tower with support `P_τ = ∑_{i<j} Pᵢ`, then `P_τ` is
approximately invariant under `R`:
`‖R* P_τ R − P_τ‖² ≤ j·(δ₁ + δ₂)`.

(The paper states the slightly sharper `j·δ₁ + δ₂`; the form here is what the
semi-triangle inequality gives directly and is all that is needed downstream.)
-/
lemma claim_approx_inv_supp {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    {δ₁ δ₂ : ℝ} (h : IsApproxClosedProjTower j P R δ₁ δ₂) :
    normHS (Rᴴ * towerSupport j P * R - towerSupport j P) ^ 2
      ≤ (j : ℝ) * (δ₁ + δ₂) := by
  convert semitriangle j ( fun i => Rᴴ * P i * R - if i + 1 < j then P ( i + 1 ) else P 0 ) |> le_trans <| ?_ using 1;
  · congr 2;
    rcases j with ( _ | j ) <;> simp_all +decide [ Finset.sum_range_succ ];
    · unfold towerSupport; aesop;
    · simp +decide [ towerSupport, Finset.sum_range, Matrix.mul_assoc ];
      have := Finset.sum_range_sub ( fun i => P i ) j; simp_all +decide [ Finset.sum_range, Fin.sum_univ_castSucc ] ;
      simp_all +decide [ sub_eq_iff_eq_add, Matrix.mul_add, Matrix.add_mul, Finset.mul_sum _ _ _, Finset.sum_mul ];
      abel1;
  · rcases j with ( _ | j ) <;> simp_all +decide [ Finset.sum_range_succ ];
    exact mul_le_mul_of_nonneg_left ( add_le_add ( by exact le_trans ( Finset.sum_le_sum fun i hi => by rw [ if_pos ( Finset.mem_range.mp hi ) ] ) h.2.2.1 ) h.2.2.2 ) ( by positivity )

/-
**Lemma `lem:p-ortho`.** Let `{Pₓ}`, `{Qₓ}` (indexed by a finite type `X`)
be two families of pairwise-orthogonal projections, and let `b : Fin t → Finset X`
be pairwise disjoint blocks. Then
`∑ᵢ ‖∑_{x∈bᵢ}Pₓ − ∑_{x∈bᵢ}Qₓ‖² ≤ 4·∑ₓ ‖Pₓ − Qₓ‖²`.
-/
set_option maxHeartbeats 4000000 in
lemma p_ortho {X : Type*} [Fintype X] [DecidableEq X] {t : ℕ}
    (P Q : X → Matrix ι ι ℂ)
    (hP : ∀ x, IsProj (P x)) (hQ : ∀ x, IsProj (Q x))
    (hPo : ∀ x y, x ≠ y → P x * P y = 0)
    (hQo : ∀ x y, x ≠ y → Q x * Q y = 0)
    (b : Fin t → Finset X)
    (hb : ∀ i k, i ≠ k → Disjoint (b i) (b k)) :
    ∑ i, normHS ((∑ x ∈ b i, P x) - (∑ x ∈ b i, Q x)) ^ 2
      ≤ 4 * ∑ x, normHS (P x - Q x) ^ 2 := by
  -- By the semi-triangle inequality with k = 2, we have
  have h_semitriangle : ∀ i, (normHS (∑ x ∈ b i, (P x - Q x))) ^ 2 ≤ 2 * ((normHS (∑ x ∈ b i, (P x * (P x - Q x)))) ^ 2 + (normHS (∑ x ∈ b i, ((P x - Q x) * Q x))) ^ 2) := by
    intro i
    have h_sum : ∑ x ∈ b i, (P x - Q x) = ∑ x ∈ b i, (P x * (P x - Q x)) + ∑ x ∈ b i, ((P x - Q x) * Q x) := by
      simp +decide [ mul_sub, sub_mul, hP _ |>.2.eq, hQ _ |>.2.eq ];
    rw [ h_sum ];
    have := normHS_add_le ( ∑ x ∈ b i, P x * ( P x - Q x ) ) ( ∑ x ∈ b i, ( P x - Q x ) * Q x );
    exact le_trans ( pow_le_pow_left₀ ( normHS_nonneg _ ) this 2 ) ( by linarith [ sq_nonneg ( normHS ( ∑ x ∈ b i, P x * ( P x - Q x ) ) - normHS ( ∑ x ∈ b i, ( P x - Q x ) * Q x ) ) ] );
  -- Use Pythagoras for orthogonal ranges: normHS U_i² = ∑_{x∈b i} normHS (P x*(P x - Q x))².
  have h_pythagoras : ∀ i : Fin t, (normHS (∑ x ∈ b i, (P x * (P x - Q x)))) ^ 2 ≤ ∑ x ∈ b i, (normHS ((P x - Q x))) ^ 2 := by
    intro i
    have h_pythagoras_step : (normHS (∑ x ∈ b i, P x * (P x - Q x))) ^ 2 = ∑ x ∈ b i, (normHS (P x * (P x - Q x))) ^ 2 := by
      have h_pythagoras_step : ∀ (s : Finset X), (∀ x ∈ s, ∀ y ∈ s, x ≠ y → (P x * (P x - Q x))ᴴ * (P y * (P y - Q y)) = 0) → (normHS (∑ x ∈ s, P x * (P x - Q x))) ^ 2 = ∑ x ∈ s, (normHS (P x * (P x - Q x))) ^ 2 := by
        intro s hs; rw [ LamplighterStability.normHS_sq_eq_ntrace ] ; simp +decide [ Finset.mul_sum ] ;
        rw [ Finset.sum_congr rfl fun x hx => by rw [ Matrix.conjTranspose_sum, Finset.sum_mul ] ];
        rw [ Finset.sum_congr rfl fun x hx => Finset.sum_eq_single x ( fun y hy => ?_ ) ( ?_ ) ];
        · simp +decide [ ntrace, LamplighterStability.normHS_sq_eq_ntrace ];
          rw [ Finset.mul_sum _ _ _ ];
        · exact fun h => hs y hy x hx h;
        · tauto;
      apply h_pythagoras_step;
      intro x hx y hy hxy
      have h_ortho : (P x * (P x - Q x))ᴴ * (P y * (P y - Q y)) = (P x - Q x) * P x * P y * (P y - Q y) := by
        simp +decide [ Matrix.mul_assoc, Matrix.conjTranspose_mul ];
        simp +decide [ hP x |>.1.eq, hQ x |>.1.eq ];
      simp_all +decide [ mul_assoc, sub_mul, mul_sub ];
    rw [h_pythagoras_step];
    refine' Finset.sum_le_sum fun x hx => _;
    have h_norm_le : ∀ A : Matrix ι ι ℂ, (normHS (P x * A)) ^ 2 ≤ (normHS A) ^ 2 := by
      intro A
      have h_norm_le : (ntrace (Aᴴ * (1 - P x) * A)) ≥ 0 := by
        have h_norm_le : (Aᴴ * (1 - P x) * A).PosSemidef := by
          have h_pos_semidef : (1 - P x).PosSemidef := by
            grind +suggestions;
          convert h_pos_semidef.conjTranspose_mul_mul_same A using 1;
        convert ntrace_nonneg_of_posSemidef h_norm_le using 1;
      simp_all +decide [ Matrix.mul_sub, sub_mul, mul_assoc, normHS_sq_eq_ntrace ];
      simp_all +decide [ ← mul_assoc, IsProj ];
      simp_all +decide [ ntrace, Matrix.trace_sub, Matrix.mul_assoc ];
      simp_all +decide [ ← mul_assoc, Matrix.IsHermitian, IsIdempotentElem ];
      linarith;
    exact h_norm_le _;
  -- Similarly, use Pythagoras for orthogonal ranges: normHS V_i² = ∑_{x∈b i} normHS ((P x - Q x) * Q x)².
  have h_pythagoras' : ∀ i : Fin t, (normHS (∑ x ∈ b i, ((P x - Q x) * Q x))) ^ 2 ≤ ∑ x ∈ b i, (normHS ((P x - Q x))) ^ 2 := by
    intro i
    have h_pythagoras' : (normHS (∑ x ∈ b i, ((P x - Q x) * Q x))) ^ 2 ≤ ∑ x ∈ b i, (normHS ((P x - Q x) * Q x)) ^ 2 := by
      have h_pythagoras' : ∀ (s : Finset X) (f : X → Matrix ι ι ℂ), (∀ x ∈ s, ∀ y ∈ s, x ≠ y → f x * (f y)ᴴ = 0) → (normHS (∑ x ∈ s, f x)) ^ 2 = ∑ x ∈ s, (normHS (f x)) ^ 2 := by
        intros s f hf_orthogonal
        have h_pythagoras' : (ntrace ((∑ x ∈ s, f x)ᴴ * (∑ x ∈ s, f x))) = ∑ x ∈ s, (ntrace ((f x)ᴴ * (f x))) := by
          simp +decide [ Matrix.mul_sum, ntrace ];
          simp +decide [ Matrix.conjTranspose_sum, Finset.mul_sum _ _ _, Finset.sum_mul ];
          rw [ Finset.sum_congr rfl ];
          intro x hx; rw [ Finset.sum_eq_single x ] <;> simp_all +decide ;
          intro y hy hxy; specialize hf_orthogonal y hy x hx hxy; replace hf_orthogonal := congr_arg ( fun m => m.trace.re ) hf_orthogonal; simp_all +decide [ Matrix.trace_mul_comm ( f y ) ] ;
          simp_all +decide [ Matrix.trace, Matrix.mul_apply, mul_comm ];
        convert h_pythagoras' using 1;
        · rw [ normHS_sq_eq_ntrace ];
        · exact Finset.sum_congr rfl fun _ _ => normHS_sq_eq_ntrace _;
      rw [ h_pythagoras' ];
      intro x hx y hy hxy; simp +decide [ Matrix.mul_assoc ] ;
      simp +decide [ ← Matrix.mul_assoc, hQo x y hxy, hQ y |>.1.eq ];
    refine' le_trans h_pythagoras' ( Finset.sum_le_sum fun x hx => _ );
    rw [ normHS_sq_eq_ntrace, normHS_sq_eq_ntrace ];
    have h_posSemidef : ((1 : Matrix ι ι ℂ) - Q x).PosSemidef := by
      exact posSemidef_one_sub_isProj ( hQ x );
    have h_posSemidef : (P x - Q x)ᴴ * (1 - Q x) * (P x - Q x) ∈ {A : Matrix ι ι ℂ | A.PosSemidef} := by
      convert h_posSemidef.conjTranspose_mul_mul_same ( P x - Q x ) using 1;
    have h_posSemidef : ntrace ((P x - Q x)ᴴ * (1 - Q x) * (P x - Q x)) ≥ 0 := by
      apply LamplighterStability.ntrace_nonneg_of_posSemidef; assumption;
    simp_all +decide [ mul_assoc, Matrix.mul_sub, Matrix.sub_mul ];
    simp_all +decide [ IsProj, IsIdempotentElem ];
    simp_all +decide [ ← mul_assoc, Matrix.IsHermitian ];
    grind +suggestions;
  -- Summing over i ∈ Finset.univ : Fin t, and using that the blocks b i are pairwise disjoint (hb), so ∑_i ∑_{x∈b i} normHS (P x - Q x)² ≤ ∑_{x : X} normHS (P x - Q x)² (each x counted at most once; the terms are nonnegative).
  have h_sum_disjoint : ∑ i : Fin t, ∑ x ∈ b i, (normHS ((P x - Q x))) ^ 2 ≤ ∑ x : X, (normHS ((P x - Q x))) ^ 2 := by
    rw [ ← Finset.sum_biUnion ];
    · exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => sq_nonneg _;
    · exact fun i _ j _ hij => hb i j hij;
  refine' le_trans ( Finset.sum_le_sum fun i _ => by simpa only [ Finset.sum_sub_distrib ] using h_semitriangle i ) _;
  rw [ ← Finset.mul_sum _ _ _ ];
  exact le_trans ( mul_le_mul_of_nonneg_left ( Finset.sum_le_sum fun i _ => add_le_add ( h_pythagoras i ) ( h_pythagoras' i ) ) zero_le_two ) ( by rw [ Finset.sum_add_distrib ] ; linarith )

/-!
`lem:lowd` (Rounding approximate closed projection towers) is proved in
`RequestProject.TowerLowd`, building on the lemmas of this file.
-/

end LamplighterStability