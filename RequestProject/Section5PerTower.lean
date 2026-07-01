import Mathlib
import RequestProject.ProjectionTowers
import RequestProject.TowerToRep
import RequestProject.TowerRep
import RequestProject.TowerLowd
import RequestProject.Section5BlockAlgebra
import RequestProject.MuInvariance

/-!
# Per-tower block representation (`lem:tower-long` / `lem:tower-short`, block form)

This file packages, for a single tower, the **block** version of the
representation-from-tower lemma: starting from an approximate `(δ₁,δ₂)`-closed
projection tower `(P, R)` of height `j` carrying a sign pattern `x` for the
center involution `B`, we produce a pair of *block* operators

```
A_τ = ∑_{k<j} (−1)^{x_k} P'_k + (G − P'_τ),     V_τ = R'·P'_τ + (G − P'_τ),
```

supported on the block `G = P_τ = towerSupport j P`, where `(P', R')` is the
rounded *closed* tower from `lem:lowd` (`lem_lowd`).  The operator `A_τ` is a
Hermitian involution on `G`, `V_τ` a unitary on `G`, and the pair satisfies both
per-block lamplighter relations, with the two squared-Hilbert–Schmidt closeness
bounds

* `‖G·B·G − A_τ‖²_HS ≤ C·(j·δ₁)`,
* `‖G·R·G − V_τ‖²_HS ≤ C·(j²·δ₁ + δ₂)`.

These per-tower blocks feed directly into the global gluing lemma
`Section5.block_lamplighter_construction` together with the resolution of
identity `Edef_partition_resolution`.
-/

namespace LamplighterStability

open scoped BigOperators
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-
The `A_τ`-closeness bound: `‖P_τ·B·P_τ − A_τ‖²_HS ≤ 4·δ₁`, where `δ₁`
dominates `∑_{k<j} ‖P_k − P'_k‖²`.
-/
lemma blockA_close {j : ℕ} {P P' : ℕ → Matrix ι ι ℂ} {B : Matrix ι ι ℂ}
    {x : ℕ → Bool} {δ₁ : ℝ}
    (hPorig : PairwiseOrthProj j P) (hP'proj : ∀ i < j, IsProj (P' i))
    (hP'le : ∀ i < j, ProjLE (P' i) (P i))
    (hsign : ∀ i < j, B * P i = signC (x i) • P i)
    (hsum : ∑ i ∈ Finset.range j, normHS (P i - P' i) ^ 2 ≤ δ₁) :
    normHS (towerSupport j P * B * towerSupport j P
        - blockA j P' (towerSupport j P) x) ^ 2 ≤ 4 * δ₁ := by
  have h_diff : towerSupport j P * B * towerSupport j P - blockA j P' (towerSupport j P) x = ∑ i ∈ Finset.range j, (if x i then -2 else 0 : ℝ) • (P i - P' i) := by
    have h_diff : towerSupport j P * B * towerSupport j P = ∑ i ∈ Finset.range j, signC (x i) • P i :=
      towerSupport_conj_sign hPorig hsign
    simp_all +decide [ blockA, signC ];
    simp +decide [ two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, towerSupport ];
    rw [ ← Finset.sum_neg_distrib ] ; rw [ ← Finset.sum_neg_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext i ; split_ifs <;> simp +decide [ * ] ; ring;
  rw [ h_diff ];
  convert normHS_sq_sum_orth ( fun i => if x i = true then -2 else 0 ) ( fun i => P i - P' i ) _ using 1;
  case convert_1 => exact j;
  · constructor <;> intro h;
    · convert normHS_sq_sum_orth ( fun i => if x i = true then -2 else 0 ) ( fun i => P i - P' i ) _ using 1;
      exact fun i hi => IsHermitian.sub ( hPorig.1 i hi |>.1 ) ( hP'proj i hi |>.1 );
    · convert h ( projLE_diff_orth hPorig hP'proj hP'le ) |> le_of_eq |> le_trans <| ?_ using 1;
      exact le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( show ( if x i = true then -2 else 0 : ℝ ) ^ 2 ≤ 4 by split_ifs <;> norm_num ) ( sq_nonneg _ ) ) ( by simpa [ Finset.mul_sum _ _ _ ] using mul_le_mul_of_nonneg_left hsum zero_le_four );
  · intro i hi; have := hPorig.1 i hi; have := hP'proj i hi; simp_all +decide [ IsProj, IsHermitian ] ;

/-
The squared HS norm of the block gap `P_τ − P'_τ` splits over the floors.
-/
lemma gap_normHS_sq {j : ℕ} {P P' : ℕ → Matrix ι ι ℂ}
    (hPorig : PairwiseOrthProj j P) (hP'proj : ∀ i < j, IsProj (P' i))
    (hP'le : ∀ i < j, ProjLE (P' i) (P i)) :
    normHS (towerSupport j P - towerSupport j P') ^ 2
      = ∑ i ∈ Finset.range j, normHS (P i - P' i) ^ 2 := by
  convert normHS_sq_sum_orth ( fun _ => 1 : ℕ → ℝ ) ( fun i => P i - P' i ) _ _;
  · simp +decide [ towerSupport, Finset.sum_sub_distrib ];
  · ring;
  · exact fun i hi => Matrix.IsHermitian.sub ( hPorig.1 i hi |>.1 ) ( hP'proj i hi |>.1 );
  · intro i hi k hk hik
    have := projLE_diff_orth hPorig hP'proj hP'le
    aesop

/-
The `V_τ`-closeness bound.
-/
lemma blockV_close {j : ℕ} {P P' : ℕ → Matrix ι ι ℂ} {R R' : Matrix ι ι ℂ}
    {δ₁ δ₂ : ℝ} (hj : 0 < j)
    (hPorig : PairwiseOrthProj j P)
    (hclosed : IsClosedProjTower j P' R')
    (hP'le : ∀ i < j, ProjLE (P' i) (P i))
    (hsum : ∑ i ∈ Finset.range j, normHS (P i - P' i) ^ 2 ≤ δ₁)
    (hcomp : normHS (towerSupport j P * R * towerSupport j P
        - towerSupport j P' * R' * towerSupport j P') ^ 2 ≤ δ₂) :
    normHS (towerSupport j P * R * towerSupport j P
        - blockV j P' (towerSupport j P) R') ^ 2 ≤ 2 * δ₂ + 2 * δ₁ := by
  -- By definition of `blockV`, we can rewrite the difference.
  have h_diff : towerSupport j P * R * towerSupport j P - blockV j P' (towerSupport j P) R' = (towerSupport j P * R * towerSupport j P - towerSupport j P' * R' * towerSupport j P') - (towerSupport j P - towerSupport j P') := by
    rw [ blockV ];
    have := LamplighterStability.R_comm_towerSupport hclosed hj; simp_all +decide [ mul_assoc, sub_eq_add_neg ] ;
    simp +decide [ ← mul_assoc, ← this ] ; abel_nf;
    simp +decide [ mul_assoc, LamplighterStability.towerSupport_idem hclosed.1.1 ];
  rw [ h_diff ];
  refine' le_trans ( pow_le_pow_left₀ ( by exact normHS_nonneg _ ) ( normHS_sub_le _ _ ) 2 ) _;
  nlinarith only [ sq_nonneg ( normHS ( towerSupport j P * R * towerSupport j P - towerSupport j P' * R' * towerSupport j P' ) - normHS ( towerSupport j P - towerSupport j P' ) ), hcomp, hsum, gap_normHS_sq hPorig ( hclosed.1.1.1 ) hP'le ]

/-
**Per-tower block representation.**  From an approximate `(δ₁,δ₂)`-closed
projection tower with a sign pattern for the center involution `B`, build the
block operators `A_τ`, `V_τ` supported on `G = P_τ = towerSupport j P`.
-/
theorem block_rep_of_approx_tower {j : ℕ} (hj : 0 < j)
    {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ} {δ₁ δ₂ : ℝ}
    (hδ₁ : 0 ≤ δ₁) (hδ₂ : 0 ≤ δ₂)
    (hτ : IsApproxClosedProjTower j P R δ₁ δ₂)
    {B : Matrix ι ι ℂ} {x : ℕ → Bool}
    (hsign : ∀ i < j, B * P i = signC (x i) • P i) :
    ∃ C : ℝ, 0 < C ∧ ∃ A V : Matrix ι ι ℂ,
      towerSupport j P * A = A ∧ A * towerSupport j P = A ∧
      A.IsHermitian ∧ A * A = towerSupport j P ∧
      towerSupport j P * V = V ∧ V * towerSupport j P = V ∧
      V * Vᴴ = towerSupport j P ∧
      (∀ i : ℕ, Commute A (V ^ i * A * Vᴴ ^ i)) ∧
      (∀ i : ℕ, Commute A (Vᴴ ^ i * A * V ^ i)) ∧
      normHS (towerSupport j P * B * towerSupport j P - A) ^ 2
        ≤ C * ((j : ℝ) * δ₁) ∧
      normHS (towerSupport j P * R * towerSupport j P - V) ^ 2
        ≤ C * ((j : ℝ) ^ 2 * δ₁ + δ₂) := by
  revert hτ;
  obtain ⟨C₀, hC₀, hlow⟩ : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ} {δ₁ δ₂ : ℝ},
      0 ≤ δ₁ → 0 ≤ δ₂ →
      IsApproxClosedProjTower j P R δ₁ δ₂ →
      ∃ (P' : ℕ → Matrix ι ι ℂ) (R' : Matrix ι ι ℂ),
        IsClosedProjTower j P' R' ∧
        (∀ i < j, ProjLE (P' i) (P i)) ∧
        (R' * (1 - towerSupport j P') = 1 - towerSupport j P') ∧
        TowerClose j P P' R R'
          (C₀ * ((j : ℝ) * δ₁)) (C₀ * ((j : ℝ) ^ 2 * δ₁ + δ₂)) := by
            apply lem_lowd;
  intro hτ
  obtain ⟨P', R', hclosed, hP'le, hRcomp, hTC⟩ := hlow hδ₁ hδ₂ hτ
  set hPorig := hτ.1
  set hP' := hclosed.1.1
  set hP'proj := hP'.1
  set hGproj : IsProj (towerSupport j P) := ⟨towerSupport_isHermitian hPorig, towerSupport_idem hPorig⟩
  set hGabs : ∀ k < j, towerSupport j P * P' k = P' k := fun k hk => towerSupport_mul_subproj hPorig hP'proj hP'le hk;
  refine' ⟨ 4 * C₀, by positivity, blockA j P' ( towerSupport j P ) x, blockV j P' ( towerSupport j P ) R', _, _, _, _, _ ⟩;
  · exact blockA_supp_left hGproj hGabs x;
  · exact blockA_supp_right hP' hGproj hGabs x;
  · exact blockA_isHermitian hP' hGproj x;
  · exact blockA_sq hP' hGproj hGabs x;
  · refine' ⟨ _, _, _, _, _, _, _ ⟩;
    exact blockV_supp_left hGproj hGabs hclosed hj;
    exact blockV_supp_right hP' hGproj hGabs;
    · convert blockV_unitary hP' hGproj hGabs hclosed hj using 1;
    · exact fun i => blockA_blockV_commute hP' hGproj hGabs hclosed hj x i;
    · exact fun i => blockA_blockVstar_commute hP' hGproj hGabs hclosed hj x i;
    · convert blockA_close hPorig hP'proj hP'le hsign hTC.1 using 1 ; ring;
    · refine' le_trans ( blockV_close hj hPorig hclosed hP'le hTC.1 hTC.2 ) _;
      nlinarith [ show ( j : ℝ ) ≥ 1 by norm_cast, mul_le_mul_of_nonneg_left ( show ( j : ℝ ) ≥ 1 by norm_cast ) hδ₁, mul_le_mul_of_nonneg_left ( show ( j : ℝ ) ≥ 1 by norm_cast ) hδ₂, mul_le_mul_of_nonneg_left ( show ( j : ℝ ) ≥ 1 by norm_cast ) hC₀.le ]

end LamplighterStability