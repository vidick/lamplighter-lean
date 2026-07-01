import Mathlib
import RequestProject.GowersHatami
import RequestProject.HSNorm

/-!
# Toward same-dimensional stability (note Corollary 1): the dimension-free intertwiner

This file develops the analytic core of the note's **Lemma 1** (translation regularization,
`gh_hs_projection_note_revised-1.pdf`, §3): the already-formalized weak/averaged Gowers–Hatami
embedding `V : H → K = L²(G,H)` together with the right-regular representation `ψ` on `K` provides,
*dimension-free*, a pointwise approximate intertwiner

  `∑ᵢ ‖ψ(g)(V eᵢ) − V(φ(g) eᵢ)‖²_K ≤ (1/|G|) · ∑ₓ ‖φ(x)φ(g) − φ(xg)‖²_HS`.

For a `δ`-representation the right-hand side is `≤ δ²·d`, so the normalized intertwiner defect is
`≤ δ`, *independently of the inflated dimension `|G|·d` of `K`*.  This is the fact that makes the
note's dimension-recovery (Lemma 2) lose only `O(δ)`.

The computation mirrors `RequestProject.GowersHatami.gowersHatami_per_g_bound`, but for the
intertwiner `ψ(g)∘V − V∘φ(g) : H → K` rather than the compression `φ(g) − V†ψ(g)V : H → H`.
-/

noncomputable section

open scoped ComplexInnerProductSpace BigOperators
open Finset

variable {d : ℕ}

/-
**Dimension-free intertwiner bound** (note Lemma 1, core estimate).  For a representation
`φ : G → U(H)` of a finite group, the Gowers–Hatami isometry `V = gowersHatamiIso G φ` and the
right-regular representation `ψ = rightRegularRep G` satisfy
`∑ᵢ ‖ψ(g)(V eᵢ) − V(φ(g) eᵢ)‖²_K ≤ (1/|G|) · ∑ₓ ‖φ(xg) − φ(x)φ(g)‖²_HS`.
-/
lemma gh_intertwiner_bound (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (φ : G → ↥(unitary (H d →L[ℂ] H d))) (g : G) :
    (∑ i : Fin d, ‖(rightRegularRep G g).toContinuousLinearMap
          ((gowersHatamiIso G φ).toContinuousLinearMap (EuclideanSpace.single i 1))
          - (gowersHatamiIso G φ).toContinuousLinearMap
              ((φ g : H d →L[ℂ] H d) (EuclideanSpace.single i 1))‖ ^ 2)
      ≤ (Fintype.card G : ℝ)⁻¹ *
          ∑ x : G, hsNormSq ((φ (x * g) : H d →L[ℂ] H d)
            - ((φ x : H d →L[ℂ] H d)).comp (φ g : H d →L[ℂ] H d)) := by
  field_simp;
  -- Expand the norm squared using the definition of `gowersHatami_diff_apply`.
  have h_expand : ∀ i : Fin d, ‖(rightRegular G g) (gowersHatamiV G (fun g => (φ g : H d →L[ℂ] H d)) (EuclideanSpace.single i 1)) - gowersHatamiV G (fun g => (φ g : H d →L[ℂ] H d)) ((φ g : H d →L[ℂ] H d) (EuclideanSpace.single i 1))‖ ^ 2 =
    (1 / (Fintype.card G : ℝ)) * ∑ x : G, ‖((φ x : H d →L[ℂ] H d)).comp (φ g : H d →L[ℂ] H d) (EuclideanSpace.single i 1) - (φ (x * g) : H d →L[ℂ] H d) (EuclideanSpace.single i 1)‖ ^ 2 := by
      intro i
      have h_expand : ‖(rightRegular G g) (gowersHatamiV G (fun g => (φ g : H d →L[ℂ] H d)) (EuclideanSpace.single i 1)) - gowersHatamiV G (fun g => (φ g : H d →L[ℂ] H d)) ((φ g : H d →L[ℂ] H d) (EuclideanSpace.single i 1))‖ ^ 2 =
        ∑ x : G, ‖(ghScale G) • ((φ x : H d →L[ℂ] H d).comp (φ g : H d →L[ℂ] H d) - (φ (x * g) : H d →L[ℂ] H d)) (EuclideanSpace.single i 1)‖ ^ 2 := by
          have h_expand : ∀ f : PiLp 2 (fun (_ : G) => H d), ‖f‖ ^ 2 = ∑ x : G, ‖f x‖ ^ 2 := by
            simp +decide [ PiLp.norm_eq_of_L2, Real.sq_sqrt ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ];
            exact fun f => Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _;
          convert h_expand _ using 3;
          convert norm_neg _ using 2 ; simp +decide [];
          convert gowersHatami_diff_apply G ( fun g => ( φ g : H d →L[ℂ] H d ) ) g ( EuclideanSpace.single i 1 ) ‹_› |> Eq.symm using 1;
      simp_all +decide [ norm_smul, ghScale ];
      simp +decide [ mul_pow, Finset.mul_sum _ _ _, abs_of_nonneg, Real.sqrt_nonneg ];
  convert Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ( h_expand i |> le_of_eq ) ( Nat.cast_nonneg ( Fintype.card G ) ) using 1;
  rw [ Finset.sum_mul _ _ _ ];
  congr! 1;
  · exact mul_comm _ _;
  · simp +decide [ hsNormSq, Finset.mul_sum _ _ _ ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ norm_sub_rev ] )

/-- **Dimension-free intertwiner defect** (note Lemma 1, §3).  If `φ` is a `δ`-representation in
the normalized HS norm (so `hsNormSq (φ(xy) − φ(x)φ(y)) ≤ δ²·d` for all `x,y`), then the
intertwiner defect of the Gowers–Hatami embedding is `≤ δ²·d`, **independently of the inflated
dimension `|G|·d` of `K = L²(G,H)`**.  This is the key estimate that lets the note's
dimension-recovery (Lemma 2) lose only `O(δ)`. -/
lemma gh_intertwiner_normSq_le (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (φ : G → ↥(unitary (H d →L[ℂ] H d))) (δ : ℝ)
    (hδ : ∀ x y, hsNormSq ((φ (x * y) : H d →L[ℂ] H d)
        - ((φ x : H d →L[ℂ] H d)).comp (φ y : H d →L[ℂ] H d)) ≤ δ ^ 2 * d)
    (g : G) :
    (∑ i : Fin d, ‖(rightRegularRep G g).toContinuousLinearMap
          ((gowersHatamiIso G φ).toContinuousLinearMap (EuclideanSpace.single i 1))
          - (gowersHatamiIso G φ).toContinuousLinearMap
              ((φ g : H d →L[ℂ] H d) (EuclideanSpace.single i 1))‖ ^ 2)
      ≤ δ ^ 2 * d := by
  refine (gh_intertwiner_bound G φ g).trans ?_
  have hcard : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ x : G, hsNormSq ((φ (x * g) : H d →L[ℂ] H d)
        - ((φ x : H d →L[ℂ] H d)).comp (φ g : H d →L[ℂ] H d))
      ≤ (Fintype.card G : ℝ) * (δ ^ 2 * d) := by
    calc ∑ x : G, hsNormSq ((φ (x * g) : H d →L[ℂ] H d)
            - ((φ x : H d →L[ℂ] H d)).comp (φ g : H d →L[ℂ] H d))
        ≤ ∑ _x : G, δ ^ 2 * d := Finset.sum_le_sum (fun x _ => hδ x g)
      _ = (Fintype.card G : ℝ) * (δ ^ 2 * d) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc (Fintype.card G : ℝ)⁻¹ * ∑ x : G, hsNormSq ((φ (x * g) : H d →L[ℂ] H d)
          - ((φ x : H d →L[ℂ] H d)).comp (φ g : H d →L[ℂ] H d))
      ≤ (Fintype.card G : ℝ)⁻¹ * ((Fintype.card G : ℝ) * (δ ^ 2 * d)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = δ ^ 2 * d := by field_simp

end