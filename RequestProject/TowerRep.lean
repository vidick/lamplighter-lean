import Mathlib
import RequestProject.ProjectionTowers
import RequestProject.TowerToRep
import RequestProject.TowerLowd
import RequestProject.MuInvariance

/-!
# Representations from towers (`lem:tower-long` / `lem:tower-short`)

This file formalizes the quantitative core of the two assembly lemmas
**`lem:tower-long`** ("Representations from high towers") and
**`lem:tower-short`** ("Representations from short towers") of Section 5 of the
paper *"Polynomial Hilbert–Schmidt stability of the lamplighter group"*.

Both lemmas have an identical proof: given an approximate `(δ₁,δ₂)`-closed
projection tower `τ = (P₀,…,P_{j-1}; R)` whose support carries a sign pattern
`x` for an involution `B` (the role of `B₀`, with `B Pᵢ = (-1)^{xᵢ} Pᵢ`,
established by `claim:b-B`), one rounds `τ` to a *true* closed projection tower
`(P'₀,…,P'_{j-1}; R')` via `lem:lowd`, and reads off the representation
operators

```
ρ_τ(a)   = ∑_{i<j} (-1)^{xᵢ} P'ᵢ + (P_τ - P'_τ),
ρ_τ(t⁻¹) = P'_τ R' P'_τ,
```

where `P_τ = ∑ Pᵢ`, `P'_τ = ∑ P'ᵢ`.  The two closeness bounds
```
‖P_τ B P_τ - ρ_τ(a)‖²_HS ≤ C·(j·δ₁),
‖P_τ R P_τ - ρ_τ(t⁻¹)‖²_HS ≤ C·(j²·δ₁ + δ₂)
```
follow from the `(ε₁,ε₂)`-closeness produced by `lem:lowd`:

* the second is *literally* the `ε₂` part of `TowerClose` (note `P_τ R P_τ`
  resp. `P'_τ R' P'_τ` are the two compressions appearing there);
* the first reduces, after cancellation, to
  `P_τ B P_τ - ρ_τ(a) = ∑_{i<j} ((-1)^{xᵢ} - 1)(Pᵢ - P'ᵢ)`, whose squared HS
  norm is, by **Pythagoras** for the pairwise-orthogonal projection family
  `Pᵢ - P'ᵢ`, equal to `∑ |(-1)^{xᵢ}-1|² ‖Pᵢ-P'ᵢ‖² ≤ 4 ∑ ‖Pᵢ-P'ᵢ‖² ≤ 4·ε₁`.

The genuine lamplighter representation built from `(P', R')` is then provided by
`tower_to_rep`.
-/

namespace LamplighterStability

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-
The differences `Pᵢ - P'ᵢ` of a pairwise-orthogonal projection family and a
dominated sub-projection family are themselves pairwise orthogonal.
-/
lemma projLE_diff_orth {j : ℕ} {P P' : ℕ → Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) (hP'proj : ∀ i < j, IsProj (P' i))
    (hP'le : ∀ i < j, ProjLE (P' i) (P i)) :
    ∀ i < j, ∀ k < j, i ≠ k → (P i - P' i) * (P k - P' k) = 0 := by
  intros i hi k hk hne;
  simp +decide only [mul_sub, sub_mul];
  rw [ show P' i = P' i * P i from ?_, show P' k = P k * P' k from ?_ ];
  · have := hP.2 i hi k hk hne; simp_all +decide [ ← mul_assoc ] ;
    simp +decide [ mul_assoc, this ];
  · have := proj_mul_eq_of_psd_le ( hP.1 k hk ) ( hP'proj k hk |>.posSemidef ) ( hP'le k hk );
    rw [ this.1 ];
  · have := hP.1 i hi;
    have := proj_mul_eq_of_psd_le this ( hP'proj i hi |>.posSemidef ) ( hP'le i hi );
    rw [ this.2 ]

/-
**Pythagoras for an orthogonal Hermitian family.**  For a family `G` of
Hermitian matrices that are pairwise orthogonal on `[0,j)` (i.e. `Gᵢ Gₖ = 0` for
`i ≠ k`), the squared HS norm of a real-linear combination splits:
`‖∑ cᵢ Gᵢ‖²_HS = ∑ cᵢ² ‖Gᵢ‖²_HS`.
-/
lemma normHS_sq_sum_orth {j : ℕ} (c : ℕ → ℝ) (G : ℕ → Matrix ι ι ℂ)
    (hGh : ∀ i < j, (G i).IsHermitian)
    (horth : ∀ i < j, ∀ k < j, i ≠ k → G i * G k = 0) :
    normHS (∑ i ∈ Finset.range j, (c i : ℂ) • G i) ^ 2
      = ∑ i ∈ Finset.range j, (c i) ^ 2 * normHS (G i) ^ 2 := by
  have := @ntrace_mul_comm;
  have := @normHS_sq_eq_ntrace;
  rename_i h;
  convert h ( ∑ i ∈ Finset.range j, ( c i : ℂ ) • G i ) ( ∑ i ∈ Finset.range j, ( c i : ℂ ) • G i ) using 1;
  convert this _ using 2;
  · simp +decide [ Matrix.conjTranspose_sum, Matrix.conjTranspose_smul ];
    exact congr_arg₂ _ ( Finset.sum_congr rfl fun i hi => by rw [ hGh i ( Finset.mem_range.mp hi ) |> IsHermitian.eq ] ) rfl;
  · simp +decide [ ntrace, Finset.sum_mul _ _ _, Finset.mul_sum, mul_assoc, mul_left_comm, sq ];
    refine' Finset.sum_congr rfl fun i hi => _;
    rw [ Finset.sum_eq_single i ] <;> simp_all +decide [ Matrix.IsHermitian ];
    · rw [ ← sq, this ];
      simp +decide [ ntrace, hGh i hi ];
    · exact fun k hk hki => Or.inr <| Or.inr <| Or.inr <| by rw [ horth i hi k hk ( Ne.symm hki ) ] ; simp +decide ;

/-
Compression of an involution acting diagonally on a tower: if `B Pᵢ =
(-1)^{xᵢ} Pᵢ` for all floors, then `P_τ B P_τ = ∑_{i<j} (-1)^{xᵢ} Pᵢ`.
-/
lemma towerSupport_conj_sign {j : ℕ} {P : ℕ → Matrix ι ι ℂ}
    (hP : PairwiseOrthProj j P) {B : Matrix ι ι ℂ} {x : ℕ → Bool}
    (hsign : ∀ i < j, B * P i = signC (x i) • P i) :
    towerSupport j P * B * towerSupport j P
      = ∑ i ∈ Finset.range j, signC (x i) • P i := by
  unfold towerSupport; simp +decide [ mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul ] ;
  rw [ Finset.sum_comm, Finset.sum_congr rfl fun i hi => Finset.sum_eq_single i ?_ ?_ ] <;> simp_all +decide [ Finset.sum_range, hP.2 ];
  · exact Finset.sum_congr rfl fun i hi => by rw [ hP.1 i ( Fin.is_lt i ) |>.2 ] ;
  · exact fun k hk hki => Or.inr ( hP.2 i hi k hk ( Ne.symm hki ) )

/-
**Lemma `lem:tower-long` / `lem:tower-short` (quantitative core).**

Let `τ = (P₀,…,P_{j-1}; R)` be an approximate `(δ₁,δ₂)`-closed projection tower
of positive height `j`, and let `B` be an operator (the role of `B₀`) acting as
the sign `(-1)^{xᵢ}` on each floor: `B Pᵢ = (-1)^{xᵢ} Pᵢ`.  Then there is a
universal constant `C > 0` and a *true* closed projection tower
`(P'₀,…,P'_{j-1}; R')` with `P'ᵢ ≤ Pᵢ` such that, setting

```
ρa   = ∑_{i<j} (-1)^{xᵢ} P'ᵢ + (P_τ - P'_τ),
ρtinv = P'_τ R' P'_τ,
```

we have the two closeness bounds
```
‖P_τ B P_τ - ρa‖²_HS    ≤ C·(j·δ₁),
‖P_τ R P_τ - ρtinv‖²_HS ≤ C·(j²·δ₁ + δ₂).
```

A genuine lamplighter representation realizing the tower is obtained by applying
`tower_to_rep` to the closed tower `(P', R')`.
-/
lemma rep_from_approx_tower {j : ℕ} {P : ℕ → Matrix ι ι ℂ}
    {R : Matrix ι ι ℂ} {δ₁ δ₂ : ℝ} (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hτ : IsApproxClosedProjTower j P R δ₁ δ₂)
    {B : Matrix ι ι ℂ} {x : ℕ → Bool}
    (hsign : ∀ i < j, B * P i = signC (x i) • P i) :
    ∃ C : ℝ, 0 < C ∧
      ∃ (P' : ℕ → Matrix ι ι ℂ) (R' : Matrix ι ι ℂ),
        IsClosedProjTower j P' R' ∧
        (∀ i < j, ProjLE (P' i) (P i)) ∧
        normHS (towerSupport j P * B * towerSupport j P
            - ((∑ i ∈ Finset.range j, signC (x i) • P' i)
                + (towerSupport j P - towerSupport j P'))) ^ 2
          ≤ C * ((j : ℝ) * δ₁) ∧
        normHS (towerSupport j P * R * towerSupport j P
            - towerSupport j P' * R' * towerSupport j P') ^ 2
          ≤ C * ((j : ℝ) ^ 2 * δ₁ + δ₂) := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := lem_lowd (ι := ι)
  obtain ⟨ P', R', hP', hP'le, hRcomp, hTC ⟩ := hC₀ hδ₁ hδ₂ hτ;
  refine' ⟨ 4 * C₀, by positivity, P', R', hP', hP'le, _, _ ⟩;
  · have h_diff : towerSupport j P * B * towerSupport j P - (∑ i ∈ Finset.range j, signC (x i) • P' i + (towerSupport j P - towerSupport j P')) = ∑ i ∈ Finset.range j, (if x i then (-2 : ℝ) else 0) • (P i - P' i) := by
      have h_diff : towerSupport j P * B * towerSupport j P = ∑ i ∈ Finset.range j, signC (x i) • P i := by
        apply towerSupport_conj_sign hτ.1 hsign;
      rw [ h_diff ];
      simp +decide [ Finset.sum_sub_distrib, smul_sub, towerSupport ];
      rw [ ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib ];
      rw [ ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib ] ; congr ; ext i ; split_ifs <;> simp +decide [ * ] ; ring;
    have h_norm_sq : normHS (∑ i ∈ Finset.range j, (if x i then (-2 : ℝ) else 0) • (P i - P' i)) ^ 2 = ∑ i ∈ Finset.range j, (if x i then 4 else 0) * normHS (P i - P' i) ^ 2 := by
      convert normHS_sq_sum_orth ( fun i => if x i then -2 else 0 ) ( fun i => P i - P' i ) _ _ using 1;
      · exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> norm_num;
      · exact fun i hi => ( hτ.1.1 i hi |>.1 ).sub ( hP'.1.1.1 i hi |>.1 );
      · exact projLE_diff_orth hτ.1 ( fun i hi => hP'.1.1.1 i hi ) hP'le;
    rw [ h_diff, h_norm_sq ];
    refine' le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( show ( if x i = true then 4 else 0 ) ≤ 4 by split_ifs <;> norm_num ) ( sq_nonneg _ ) ) _;
    rw [ ← Finset.mul_sum _ _ _ ] ; nlinarith [ hTC.1 ];
  · refine' le_trans hTC.2 _;
    exact mul_le_mul_of_nonneg_right ( by linarith ) ( by positivity )

end LamplighterStability