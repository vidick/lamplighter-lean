import Mathlib
import RequestProject.Section5Keystone
import RequestProject.Section5Aggregate
import RequestProject.Section5Resolution
import RequestProject.Section5Glue
import RequestProject.Section5DeltaAgg
import RequestProject.Section5Sign

/-!
# Section 5 keystone assembly: building blocks for `tower_rep_final`

This file decomposes the global gluing of `Section5.tower_rep_final` into focused
top-level lemmas:

* `keyD1` / `keyD2` — the per-tower equivariance defect (`δ₁`) and closing defect
  (`δ₂`).
* `key_some_block` — the per-tower block representation (combining
  `block_rep_uniform` and `approx_inv_supp_sharp`).
* `key_d1_le_4eta` — the aggregate `δ₁` bound `∑_τ keyD1 ≤ 4η`.
-/

namespace LamplighterStability

open scoped BigOperators
open Matrix
open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureBridge LamplighterStability.MeasureInstantiation

/-- The center index `0 ∈ F_{m+1}` of the window. -/
def Section5.winCenter (m : ℕ) : Win (m + 1) := ⟨0, by simp [Finset.mem_Icc]; positivity⟩

variable {d : ℕ}

/-- The per-tower equivariance defect `δ₁^τ = ∑_{i<j-1} ‖T* P_i T − P_{i+1}‖²`. -/
noncomputable def keyD1 (m : ℕ) (T : Matrix (Fin d) (Fin d) ℂ)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ) (b : Set Cfg) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j - 1),
    normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i) * T
      - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (i + 1))) ^ 2

/-- The per-tower closing defect `δ₂^τ = ‖T* P_{j-1} T − P_0‖²`. -/
noncomputable def keyD2 (m : ℕ) (T : Matrix (Fin d) (Fin d) ℂ)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ) (b : Set Cfg) (j : ℕ) : ℝ :=
  normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (towerFloor b (j - 1)) * T
    - Edef (m + 1) (EpatB (m + 1) B) (towerFloor b 0)) ^ 2

lemma keyD1_nonneg (m : ℕ) (T : Matrix (Fin d) (Fin d) ℂ)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ) (b : Set Cfg) (j : ℕ) :
    0 ≤ keyD1 m T B b j :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma keyD2_nonneg (m : ℕ) (T : Matrix (Fin d) (Fin d) ℂ)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ) (b : Set Cfg) (j : ℕ) :
    0 ≤ keyD2 m T B b j := sq_nonneg _

/-- The guarded closing defect (zero for empty towers). -/
noncomputable def keyD2g (m : ℕ) (T : Matrix (Fin d) (Fin d) ℂ)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ) (b : Set Cfg) (j : ℕ) : ℝ :=
  if 0 < j then keyD2 m T B b j else 0


/-
**Per-tower block representation.**  For a single tower of base `b` and
height `j > 0` (with `j < m+1` and `b` a tower base contained in a single
`j`-cylinder), construct the block operators `A`, `V` supported on the tower
support `P_τ = towerSupport j P` with the three squared-HS bounds feeding the
global gluing.
-/
theorem key_some_block (m : ℕ) (T : Matrix (Fin d) (Fin d) ℂ)
    (hTl : star T * T = 1) (hTr : T * star T = 1)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    (b : Set Cfg) (j : ℕ) (hj : 0 < j)
    (hbase : IsTowerBase j b) (hsing : ProjSingleton j b) :
    ∃ A V : Matrix (Fin d) (Fin d) ℂ,
      towerSupport j (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i)) * A = A ∧
      A * towerSupport j (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i)) = A ∧
      A.IsHermitian ∧
      A * A = towerSupport j (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i)) ∧
      towerSupport j (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i)) * V = V ∧
      V * towerSupport j (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i)) = V ∧
      V * Vᴴ = towerSupport j (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i)) ∧
      (∀ i : ℕ, Commute A (V ^ i * A * Vᴴ ^ i)) ∧
      (∀ i : ℕ, Commute A (Vᴴ ^ i * A * V ^ i)) ∧
      normHS (towerSupport j (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i))
          * B (Section5.winCenter m)
          * towerSupport j (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i)) - A) ^ 2
        ≤ 1200 * ((j : ℝ) * keyD1 m T B b j) ∧
      normHS (towerSupport j (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i))
          * T
          * towerSupport j (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i)) - V) ^ 2
        ≤ 1200 * ((j : ℝ) ^ 2 * keyD1 m T B b j + keyD2 m T B b j) ∧
      normHS (star T
          * towerSupport j (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i))
          * T
          - towerSupport j (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i))) ^ 2
        ≤ 2 * (j : ℝ) * keyD1 m T B b j + 2 * keyD2 m T B b j := by
  obtain ⟨ p₀, hp₀ ⟩ := hsing;
  have hτ : IsApproxClosedProjTower j (fun i => Edef (m + 1) (EpatB (m + 1) B) (towerFloor b i)) T (keyD1 m T B b j) (keyD2 m T B b j) := by
    constructor;
    · apply_rules [ LamplighterStability.MeasureBridge.Edef_floors_pairwiseOrthProj ];
    · exact ⟨ ⟨ hTl, hTr ⟩, le_rfl, le_rfl ⟩;
  convert block_rep_uniform hj ( keyD1_nonneg m T B b j ) ( keyD2_nonneg m T B b j ) hτ _ using 1;
  rotate_left;
  exact B ( Section5.winCenter m );
  use fun i => if h : - ( i : ℤ ) ∈ Finset.Icc ( - ( j : ℤ ) ) ( j : ℤ ) then p₀ ⟨ - ( i : ℤ ), h ⟩ else false;
  · intro i hi;
    convert Edef_floor_center_sign m j i B hB2 hBc hp₀ ( Section5.winCenter m ) rfl _ using 1;
    lia;
    exact Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩;
  · ext;
    constructor <;> rintro ⟨ V, hV₁, hV₂, hV₃, hV₄, hV₅, hV₆, hV₇, hV₈, hV₉, hV₁₀, hV₁₁ ⟩ <;> use V;
    · exact ⟨ hV₁, hV₂, hV₃, hV₄, hV₅, hV₆, hV₇, hV₈, hV₉, hV₁₀, hV₁₁.1 ⟩;
    · exact ⟨ hV₁, hV₂, hV₃, hV₄, hV₅, hV₆, hV₇, hV₈, hV₉, hV₁₀, hV₁₁, approx_inv_supp_sharp hτ ⟩

/-
**Aggregate `δ₁` bound.**  The sum over towers of the per-tower equivariance
defects is at most `4η`.
-/
theorem key_d1_le_4eta (m : ℕ)
    {T : Matrix (Fin d) (Fin d) ℂ} (hTl : star T * T = 1) (hTr : T * star T = 1)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {e : Set Cfg} {ιτ : Type} [Fintype ιτ] {base : ιτ → Set Cfg} {height : ιτ → ℕ}
    (hpart : IsTowerPartition e base height)
    (hfloordef : ∀ τ i, i < height τ → Defined m (towerFloor (base τ) i))
    {η : ℝ}
    (hη : ∑ x : Win m → Bool,
            normHS (star T * Edef (m + 1) (EpatB (m + 1) B) (cyl m x) * T
              - Edef (m + 1) (EpatB (m + 1) B) ((L : Equiv.Perm Cfg) '' cyl m x)) ^ 2 ≤ η) :
    ∑ τ : ιτ, keyD1 m T B (base τ) (height τ) ≤ 4 * η := by
  have := @LamplighterStability.MeasureBridge.floor_equiv_aggregate;
  refine' le_trans _ ( this m hTl hTr B hBh hB2 hBc hpart hfloordef hη );
  exact Finset.sum_le_sum fun τ _ => Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( Nat.sub_le _ _ ) ) fun _ _ _ => sq_nonneg _

/-- A weighted finite sum is bounded by the weight bound times the plain sum. -/
lemma weighted_sum_le {κ : Type*} [Fintype κ] (W : ℝ) (f g : κ → ℝ)
    (hf : ∀ i, f i ≤ W) (hg : ∀ i, 0 ≤ g i) :
    ∑ i, f i * g i ≤ W * ∑ i, g i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hf i) (hg i)

/-
**Per-block data over the tower-level resolution.**  For every block `s` of
the `Option ιτ`-indexed resolution `towerResG`, produce the block operators
`A`, `V` (the error block uses `E_e` itself; tower blocks use `key_some_block`)
together with the structural facts feeding `aggregate_block_rep` and the three
per-block squared-HS bounds.
-/
theorem key_block_data (m : ℕ) (T : Matrix (Fin d) (Fin d) ℂ)
    (hTl : star T * T = 1) (hTr : T * star T = 1)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    (e : Set Cfg) {ιτ : Type} [Fintype ιτ] (base : ιτ → Set Cfg) (height : ιτ → ℕ)
    (hpart : IsTowerPartition e base height)
    (hsing : ∀ τ, ProjSingleton (height τ) (base τ)) :
    ∀ s : Option ιτ, ∃ A V : Matrix (Fin d) (Fin d) ℂ,
      towerResG m B e base height s * A = A ∧
      A * towerResG m B e base height s = A ∧
      A.IsHermitian ∧
      A * A = towerResG m B e base height s ∧
      towerResG m B e base height s * V = V ∧
      V * towerResG m B e base height s = V ∧
      V * Vᴴ = towerResG m B e base height s ∧
      (∀ i : ℕ, Commute A (V ^ i * A * Vᴴ ^ i)) ∧
      (∀ i : ℕ, Commute A (Vᴴ ^ i * A * V ^ i)) ∧
      normHS (towerResG m B e base height s * B (Section5.winCenter m)
            * towerResG m B e base height s - A) ^ 2
        ≤ s.elim (4 * ntrace (towerResG m B e base height (none : Option ιτ)))
            (fun τ => 1200 * ((height τ : ℝ) * keyD1 m T B (base τ) (height τ))) ∧
      normHS (towerResG m B e base height s * T
            * towerResG m B e base height s - V) ^ 2
        ≤ s.elim (4 * ntrace (towerResG m B e base height (none : Option ιτ)))
            (fun τ => 1200 * ((height τ : ℝ) ^ 2 * keyD1 m T B (base τ) (height τ)
              + keyD2g m T B (base τ) (height τ))) ∧
      normHS (star T * towerResG m B e base height s * T
            - towerResG m B e base height s) ^ 2
        ≤ s.elim (4 * ntrace (towerResG m B e base height (none : Option ιτ)))
            (fun τ => 2 * (height τ : ℝ) * keyD1 m T B (base τ) (height τ)
              + 2 * keyD2g m T B (base τ) (height τ)) := by
  intro s; rcases s with _ | τ;
  · refine' ⟨ Edef ( m + 1 ) ( EpatB ( m + 1 ) B ) e, Edef ( m + 1 ) ( EpatB ( m + 1 ) B ) e, _, _, _, _, _, _ ⟩ <;> norm_num [ towerResG ];
    any_goals exact LamplighterStability.MeasureBridge.Edef_isProj ( m + 1 ) B hBh hB2 hBc e |>.2;
    · exact LamplighterStability.MeasureBridge.Edef_isProj _ _ hBh hB2 hBc _ |>.1;
    · refine' ⟨ _, _, _, _, _ ⟩;
      · exact LamplighterStability.MeasureBridge.Edef_isProj ( m + 1 ) B hBh hB2 hBc e |>.2;
      · have := LamplighterStability.MeasureBridge.Edef_isProj ( m + 1 ) B hBh hB2 hBc e |>.1;
        rw [ this.eq ];
        exact LamplighterStability.MeasureBridge.Edef_isProj ( m + 1 ) B hBh hB2 hBc e |>.2;
      · simp +decide [ ← pow_succ, LamplighterStability.MeasureBridge.Edef_isProj ( m + 1 ) B hBh hB2 hBc e |>.1.eq ];
      · intro i; exact (by
        have hE : IsIdempotentElem (Edef (m + 1) (EpatB (m + 1) B) e) := by
          exact LamplighterStability.MeasureBridge.Edef_isProj ( m + 1 ) B hBh hB2 hBc e |>.2;
        have hE : (Edef (m + 1) (EpatB (m + 1) B) e)ᴴ = Edef (m + 1) (EpatB (m + 1) B) e := by
          exact LamplighterStability.MeasureBridge.Edef_isProj ( m + 1 ) B hBh hB2 hBc e |>.1;
        induction i <;> simp_all +decide [ pow_succ, mul_assoc ];
        simp_all +decide [ ← mul_assoc, IsIdempotentElem ]);
      · have := LamplighterStability.compress_sub_proj_le ( LamplighterStability.MeasureBridge.Edef_isProj ( m + 1 ) B hBh hB2 hBc e |>.1 ) ( LamplighterStability.MeasureBridge.Edef_isProj ( m + 1 ) B hBh hB2 hBc e |>.2 ) hTl hTr;
        exact ⟨ by simpa [ hBh ( Section5.winCenter m ) |> IsSelfAdjoint.star_eq ] using LamplighterStability.compress_sub_proj_le ( LamplighterStability.MeasureBridge.Edef_isProj ( m + 1 ) B hBh hB2 hBc e |>.1 ) ( LamplighterStability.MeasureBridge.Edef_isProj ( m + 1 ) B hBh hB2 hBc e |>.2 ) ( show star ( B ( Section5.winCenter m ) ) * B ( Section5.winCenter m ) = 1 from by simpa [ hBh ( Section5.winCenter m ) |> IsSelfAdjoint.star_eq ] using hB2 ( Section5.winCenter m ) ) ( show B ( Section5.winCenter m ) * star ( B ( Section5.winCenter m ) ) = 1 from by simpa [ hBh ( Section5.winCenter m ) |> IsSelfAdjoint.star_eq ] using hB2 ( Section5.winCenter m ) ) |>.1, this ⟩;
  · by_cases h : 0 < height τ
    · have hk := key_some_block m T hTl hTr B hBh hB2 hBc ( base τ ) ( height τ ) h ( hpart.2.2 τ ) ( hsing τ )
      have hkeyD2g : keyD2g m T B (base τ) (height τ) = keyD2 m T B (base τ) (height τ) := by
        rw [keyD2g, if_pos h]
      simpa only [towerResG, Option.elim_some, hkeyD2g] using hk
    · have h0 : height τ = 0 := by omega
      refine ⟨0, 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [towerResG, towerSupport, keyD1, keyD2g, h0]

/-
Scalar inequality behind the `B₀` closeness bound.
-/
lemma boundA_scalar (Cerr Cd : ℝ) (t : ℕ) (ht : 1 ≤ t) (υ δ η N : ℝ)
    (hυ : 0 < υ) (hδ : 0 < δ) (hη : 0 < η) (hCd : 0 ≤ Cd) (hN0 : 0 ≤ N)
    (hN : N ≤ |Cerr| * (t : ℝ) ^ 6 * (υ + δ + η)) :
    4 * N + 1200 * ((6 * (t : ℝ)) * (4 * η))
      ≤ 200000 * (|Cerr| + 1) * (Cd + 1) * (t : ℝ) ^ 6 * (υ + δ + η) := by
  nlinarith [ show ( t : ℝ ) ^ 6 ≥ 1 by exact_mod_cast Nat.one_le_pow _ _ ht, show ( t : ℝ ) ^ 6 * ( υ + δ + η ) ≥ 0 by positivity, show ( |Cerr| + 1 ) * ( Cd + 1 ) ≥ 1 by nlinarith [ abs_nonneg Cerr, show ( 0 : ℝ ) ≤ Cd by positivity ], mul_le_mul_of_nonneg_right ( show ( t : ℝ ) ≤ t ^ 6 by exact_mod_cast Nat.le_self_pow ( by positivity ) _ ) ( show ( 0 : ℝ ) ≤ η by positivity ) ]

/-
Scalar inequality behind the `T` closeness bound.
-/
lemma boundT_scalar (Cerr Cd : ℝ) (t : ℕ) (ht : 1 ≤ t) (υ δ η N : ℝ)
    (hυ : 0 < υ) (hδ : 0 < δ) (hη : 0 < η) (hCd : 0 ≤ Cd) (hN0 : 0 ≤ N)
    (hN : N ≤ |Cerr| * (t : ℝ) ^ 6 * (υ + δ + η)) :
    (4 * N + 1200 * ((6 * (t : ℝ)) ^ 2 * (4 * η) + Cd * (δ + η + 1 / (t : ℝ))))
      + (1 / 2) * (4 * N + (2 * ((6 * (t : ℝ)) * (4 * η))
          + 2 * (Cd * (δ + η + 1 / (t : ℝ)))))
      ≤ 200000 * (|Cerr| + 1) * (Cd + 1)
          * ((1 : ℝ) / (t : ℝ) + (t : ℝ) ^ 6 * (υ + δ + η)) := by
  ring_nf at *;
  have h_bound : (t : ℝ) ^ 6 ≥ 1 ∧ (t : ℝ) ^ 2 ≤ (t : ℝ) ^ 6 ∧ (t : ℝ) ≤ (t : ℝ) ^ 6 := by
    exact ⟨ mod_cast Nat.one_le_pow _ _ ht, mod_cast Nat.pow_le_pow_right ht ( by decide ), mod_cast Nat.le_self_pow ( by decide ) _ ⟩;
  nlinarith [ inv_pos.mpr ( by positivity : 0 < ( t : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( t : ℝ ) ≠ 0 ), mul_nonneg hCd hN0, mul_nonneg hCd ( abs_nonneg Cerr ), mul_nonneg hN0 ( abs_nonneg Cerr ), abs_nonneg Cerr, mul_le_mul_of_nonneg_left h_bound.1 hCd, mul_le_mul_of_nonneg_left h_bound.2.1 hCd, mul_le_mul_of_nonneg_left h_bound.2.2 hCd ]

/-- **Final arithmetic of the keystone gluing.**  Abstract version of the global
assembly: from a resolution of identity, per-block lamplighter data with three
per-block squared-HS bounds in terms of generic nonnegative weights `w1`, `w2`,
and the aggregate bounds `∑ w1 ≤ 4η`, `∑ w2 ≤ Cd·(δ+η+1/t)`, `ntrace (G none) ≤
|Cerr|·t⁶·(υ+δ+η)`, produce the nearby representation with the two final
squared-HS closeness bounds. -/
theorem tower_rep_arith {ιτ : Type} [Fintype ιτ] {dd : ℕ} (t : ℕ) (ht : 1 ≤ t)
    {δ υ η : ℝ} (hδ : 0 < δ) (hυ : 0 < υ) (hη : 0 < η)
    (Cerr Cd : ℝ) (hCd : 0 ≤ Cd)
    [DecidableEq ιτ]
    (G : Option ιτ → Matrix (Fin dd) (Fin dd) ℂ)
    (hGh : ∀ s, (G s).IsHermitian) (hGi : ∀ s, IsIdempotentElem (G s))
    (hGsum : ∑ s, G s = 1) (hGortho : ∀ s s', s ≠ s' → G s * G s' = 0)
    (T Bc : Matrix (Fin dd) (Fin dd) ℂ) (hTl : star T * T = 1) (hTr : T * star T = 1)
    (A V : Option ιτ → Matrix (Fin dd) (Fin dd) ℂ)
    (hAL : ∀ s, G s * A s = A s) (hAR : ∀ s, A s * G s = A s)
    (hAh : ∀ s, (A s).IsHermitian) (hAsq : ∀ s, A s * A s = G s)
    (hVL : ∀ s, G s * V s = V s) (hVR : ∀ s, V s * G s = V s)
    (hVstar : ∀ s, V s * (V s)ᴴ = G s)
    (hcomm : ∀ s (i : ℕ), Commute (A s) (V s ^ i * A s * ((V s)ᴴ) ^ i))
    (hcomm' : ∀ s (i : ℕ), Commute (A s) (((V s)ᴴ) ^ i * A s * V s ^ i))
    (hBcomm : ∀ s, G s * Bc = Bc * G s)
    (hN0 : 0 ≤ ntrace (G none))
    (hntr : ntrace (G none) ≤ |Cerr| * (t : ℝ) ^ 6 * (υ + δ + η))
    (height : ιτ → ℕ) (w1 w2 : ιτ → ℝ)
    (hw1 : ∀ τ, 0 ≤ w1 τ)
    (h6t : ∀ τ, (height τ : ℝ) ≤ 6 * t)
    (hd1 : ∑ τ, w1 τ ≤ 4 * η) (hd2 : ∑ τ, w2 τ ≤ Cd * (δ + η + 1 / (t : ℝ)))
    (hbA : ∀ s, normHS (G s * Bc * G s - A s) ^ 2
        ≤ s.elim (4 * ntrace (G none)) (fun τ => 1200 * ((height τ : ℝ) * w1 τ)))
    (hbT : ∀ s, normHS (G s * T * G s - V s) ^ 2
        ≤ s.elim (4 * ntrace (G none))
            (fun τ => 1200 * ((height τ : ℝ) ^ 2 * w1 τ + w2 τ)))
    (hboff : ∀ s, normHS (star T * G s * T - G s) ^ 2
        ≤ s.elim (4 * ntrace (G none))
            (fun τ => 2 * (height τ : ℝ) * w1 τ + 2 * w2 τ)) :
    ∃ A' T' : Matrix.unitaryGroup (Fin dd) ℂ,
      (A' : Matrix (Fin dd) (Fin dd) ℂ) ^ 2 = 1 ∧
      (∀ i : ℤ, Commute (A' : Matrix.unitaryGroup (Fin dd) ℂ) (T' ^ (-i) * A' * T' ^ i)) ∧
      normHS (Bc - (A' : Matrix (Fin dd) (Fin dd) ℂ)) ^ 2
        ≤ 200000 * (|Cerr| + 1) * (Cd + 1) * (t : ℝ) ^ 6 * (υ + δ + η) ∧
      normHS (T - (T' : Matrix (Fin dd) (Fin dd) ℂ)) ^ 2
        ≤ 200000 * (|Cerr| + 1) * (Cd + 1) * ((1 : ℝ) / (t : ℝ) + (t : ℝ) ^ 6 * (υ + δ + η)) := by
  classical
  have hW1 : ∑ τ, (height τ : ℝ) * w1 τ ≤ (6 * (t : ℝ)) * (4 * η) :=
    le_trans (weighted_sum_le (6 * (t : ℝ)) (fun τ => (height τ : ℝ)) w1 h6t hw1)
      (mul_le_mul_of_nonneg_left hd1 (by positivity))
  have hf2 : ∀ τ, (height τ : ℝ) ^ 2 ≤ (6 * (t : ℝ)) ^ 2 := by
    intro τ
    have h := h6t τ
    have h0 : (0 : ℝ) ≤ (height τ : ℝ) := Nat.cast_nonneg _
    nlinarith [h, h0]
  have hW2 : ∑ τ, (height τ : ℝ) ^ 2 * w1 τ ≤ (6 * (t : ℝ)) ^ 2 * (4 * η) :=
    le_trans (weighted_sum_le ((6 * (t : ℝ)) ^ 2) (fun τ => (height τ : ℝ) ^ 2) w1 hf2 hw1)
      (mul_le_mul_of_nonneg_left hd1 (by positivity))
  have hSA : ∑ s, normHS (G s * Bc * G s - A s) ^ 2
      ≤ 4 * ntrace (G none) + 1200 * ((6 * (t : ℝ)) * (4 * η)) := by
    refine le_trans (Finset.sum_le_sum fun s _ => hbA s) ?_
    rw [Fintype.sum_option]
    simp only [Option.elim]
    have hx : ∑ τ, 1200 * ((height τ : ℝ) * w1 τ) ≤ 1200 * ((6 * (t : ℝ)) * (4 * η)) := by
      rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hW1 (by norm_num)
    linarith
  have hST : ∑ s, normHS (G s * T * G s - V s) ^ 2
      ≤ 4 * ntrace (G none)
        + 1200 * ((6 * (t : ℝ)) ^ 2 * (4 * η) + Cd * (δ + η + 1 / (t : ℝ))) := by
    refine le_trans (Finset.sum_le_sum fun s _ => hbT s) ?_
    rw [Fintype.sum_option]
    simp only [Option.elim]
    have hx : ∑ τ, 1200 * ((height τ : ℝ) ^ 2 * w1 τ + w2 τ)
        ≤ 1200 * ((6 * (t : ℝ)) ^ 2 * (4 * η) + Cd * (δ + η + 1 / (t : ℝ))) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      exact mul_le_mul_of_nonneg_left (add_le_add hW2 hd2) (by norm_num)
    linarith
  have hSoffSum : ∑ s, normHS (star T * G s * T - G s) ^ 2
      ≤ 4 * ntrace (G none)
        + (2 * ((6 * (t : ℝ)) * (4 * η)) + 2 * (Cd * (δ + η + 1 / (t : ℝ)))) := by
    refine le_trans (Finset.sum_le_sum fun s _ => hboff s) ?_
    rw [Fintype.sum_option]
    simp only [Option.elim]
    have hfst : ∑ τ, 2 * (height τ : ℝ) * w1 τ ≤ 2 * ((6 * (t : ℝ)) * (4 * η)) := by
      have he : ∑ τ, 2 * (height τ : ℝ) * w1 τ = 2 * ∑ τ, (height τ : ℝ) * w1 τ := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => by ring
      rw [he]; exact mul_le_mul_of_nonneg_left hW1 (by norm_num)
    have hsnd : ∑ τ, 2 * w2 τ ≤ 2 * (Cd * (δ + η + 1 / (t : ℝ))) := by
      rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hd2 (by norm_num)
    rw [Finset.sum_add_distrib]
    linarith
  have hoffeq : (∑ a, ∑ b ∈ Finset.univ.erase a, normHS (G a * T * G b) ^ 2)
      = (1 / 2) * ∑ s, normHS (star T * G s * T - G s) ^ 2 := by
    rw [show (∑ a, ∑ b ∈ Finset.univ.erase a, normHS (G a * T * G b) ^ 2)
          = ∑ a, (1 / 2) * normHS (star T * G a * T - G a) ^ 2 from
        Finset.sum_congr rfl (fun a _ => offdiag_normHS_sq hGh hGi hGsum hTl hTr a),
      ← Finset.mul_sum]
  refine Section5.aggregate_block_rep hGh hGi hGsum hGortho hAL hAR hAh hAsq hVL hVR hVstar
    hcomm hcomm' hBcomm ?_ ?_
  · exact le_trans hSA (boundA_scalar Cerr Cd t ht υ δ η (ntrace (G none)) hυ hδ hη hCd hN0 hntr)
  · rw [hoffeq]
    have hhalf : (1 / 2 : ℝ) * ∑ s, normHS (star T * G s * T - G s) ^ 2
        ≤ (1 / 2) * (4 * ntrace (G none)
            + (2 * ((6 * (t : ℝ)) * (4 * η)) + 2 * (Cd * (δ + η + 1 / (t : ℝ))))) :=
      mul_le_mul_of_nonneg_left hSoffSum (by norm_num)
    exact le_trans (add_le_add hST hhalf)
      (boundT_scalar Cerr Cd t ht υ δ η (ntrace (G none)) hυ hδ hη hCd hN0 hntr)

end LamplighterStability