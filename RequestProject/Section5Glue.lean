import Mathlib
import RequestProject.Foundations
import RequestProject.ProjectionTowers
import RequestProject.PVMAlgebra
import RequestProject.MuInvariance
import RequestProject.TowerLowd
import RequestProject.TowerRounding

/-!
# Section 5 gluing lemmas (matrix-algebra core)

Self-contained Hilbert–Schmidt matrix-algebra lemmas used in the final Section 5
assembly (`Section5Assembly.tower_rep_final`).  They are stated abstractly over a
finite index type `ι` and a resolution of identity / projection tower, and feed
the aggregate-Pythagoras step.

* `offdiag_normHS_sq` — for a resolution `G` of pairwise-orthogonal Hermitian
  idempotents and a unitary `T`, the off-diagonal block mass from block `a`
  equals half the squared support-invariance defect:
  `∑_{b≠a} ‖G_a T G_b‖² = ½ ‖T* G_a T − G_a‖²`.
* `approx_inv_supp_sharp` — a sharpened form of `claim_approx_inv_supp`: the
  support-invariance defect of an approximate `(δ₁,δ₂)`-closed tower is at most
  `2·j·δ₁ + 2·δ₂` (the closing defect `δ₂` is **not** multiplied by the height).
* `compress_sub_proj_le` — for a projection `G` and a unitary `T`, both the
  compression defect `‖G T G − G‖²` and the conjugation defect `‖T* G T − G‖²`
  are at most `4·tr(G)`.
-/

namespace LamplighterStability

open scoped BigOperators
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-
`normHS (T * G) = normHS G` for `T` an isometry (`star T * T = 1`).
-/
lemma normHS_mul_left_isometry {T G : Matrix ι ι ℂ} (hT : star T * T = 1) :
    normHS (T * G) = normHS G := by
  have h_norm_sq_eq : normHS (T * G) ^ 2 = normHS G ^ 2 := by
    rw [ normHS_sq_eq_ntrace, normHS_sq_eq_ntrace ];
    simp +decide [ ← mul_assoc ];
    simp_all +decide [ Matrix.mul_assoc, star_eq_conjTranspose ];
  rwa [ sq_eq_sq₀ ( normHS_nonneg _ ) ( normHS_nonneg _ ) ] at h_norm_sq_eq

/-
`normHS (star T * G * T) = normHS G` for `T` unitary.
-/
lemma normHS_conj_eq {T G : Matrix ι ι ℂ} (hT : star T * T = 1) (hT' : T * star T = 1) :
    normHS (star T * G * T) = normHS G := by
  -- Since $star T$ is unitary, we can apply the normHS_unitary_conj lemma.
  have h_unitary : star T * star (star T) = 1 ∧ star (star T) * star T = 1 := by
    aesop;
  convert normHS_unitary_conj ( show star T ∈ unitary ( Matrix ι ι ℂ ) from ?_ ) G using 1;
  · rw [ star_star ];
  · constructor <;> tauto

/-
**Off-diagonal block mass.**  For a resolution of identity `G` by
pairwise-orthogonal Hermitian idempotents and a unitary `T`, the total
off-diagonal block mass emanating from block `a` equals half the squared
support-invariance defect of block `a`.
-/
lemma offdiag_normHS_sq {σ : Type*} [Fintype σ] [DecidableEq σ]
    {G : σ → Matrix ι ι ℂ}
    (hGh : ∀ s, (G s).IsHermitian) (hGi : ∀ s, IsIdempotentElem (G s))
    (hsum : ∑ s, G s = 1)
    {T : Matrix ι ι ℂ} (_hT : star T * T = 1) (hT' : T * star T = 1) (a : σ) :
    ∑ b ∈ Finset.univ.erase a, normHS (G a * T * G b) ^ 2
      = (1 / 2) * normHS (star T * G a * T - G a) ^ 2 := by
  -- By Pythagoras' theorem, we have:
  have h_pyth : ∑ b, normHS (G a * T * G b) ^ 2 = normHS (G a * T) ^ 2 := by
    convert pyth_right hGh hGi hsum ( G a * T ) using 1;
  -- By definition of $ntrace$, we have:
  have h_ntrace : normHS (star T * G a * T - G a) ^ 2 = 2 * ntrace (G a) - 2 * ntrace ((G a * T * G a)ᴴ * (G a * T * G a)) := by
    have h_ntrace : normHS (star T * G a * T - G a) ^ 2 = ntrace ((star T * G a * T - G a)ᴴ * (star T * G a * T - G a)) := by
      convert normHS_sq_eq_ntrace ( star T * G a * T - G a ) using 1;
    simp_all +decide [ Matrix.mul_assoc, Matrix.IsHermitian, IsIdempotentElem ];
    simp_all +decide [ sub_mul, mul_sub, ← mul_assoc ];
    simp_all +decide [ star_eq_conjTranspose, Matrix.mul_assoc ];
    simp_all +decide [ ← mul_assoc, ntrace_sub, ntrace_mul_comm ];
    ring;
  -- By definition of $ntrace$, we have $normHS (G a * T) ^ 2 = ntrace (G a)$.
  have h_ntrace_GaT : normHS (G a * T) ^ 2 = ntrace (G a) := by
    have h_ntrace_GaT : normHS (G a * T) ^ 2 = ntrace ((G a * T)ᴴ * (G a * T)) := by
      convert normHS_sq_eq_ntrace ( G a * T ) using 1;
    simp_all +decide [ Matrix.IsHermitian, IsIdempotentElem ];
    simp_all +decide [ ← mul_assoc, ntrace_mul_comm ];
    simp_all +decide [ mul_assoc, star_eq_conjTranspose ];
  have h_ntrace_GaT_Ga : normHS (G a * T * G a) ^ 2 = ntrace ((G a * T * G a)ᴴ * (G a * T * G a)) := by
    convert normHS_sq_eq_ntrace ( G a * T * G a ) using 1;
  rw [ Finset.sum_erase_eq_sub ( Finset.mem_univ a ) ] ; linarith;

/-
**Sharpened support invariance (`claim:approx_inv_supp`).**  For an approximate
`(δ₁,δ₂)`-closed projection tower of height `j`, the support `P_τ = ∑_{i<j} Pᵢ`
satisfies `‖R* P_τ R − P_τ‖² ≤ 2·j·δ₁ + 2·δ₂`; crucially the closing defect `δ₂`
carries no height factor.
-/
lemma approx_inv_supp_sharp {j : ℕ} {P : ℕ → Matrix ι ι ℂ} {R : Matrix ι ι ℂ}
    {δ₁ δ₂ : ℝ} (h : IsApproxClosedProjTower j P R δ₁ δ₂) :
    normHS (Rᴴ * towerSupport j P * R - towerSupport j P) ^ 2
      ≤ 2 * (j : ℝ) * δ₁ + 2 * δ₂ := by
  rcases j with ( _ | j ) <;> simp_all +decide [ IsApproxClosedProjTower ];
  · unfold towerSupport; norm_num; nlinarith;
  · have h_telescope : Rᴴ * towerSupport (j + 1) P * R - towerSupport (j + 1) P = ∑ i ∈ Finset.range (j + 1), (Rᴴ * P i * R - (if i + 1 < j + 1 then P (i + 1) else P 0)) := by
      unfold towerSupport; simp +decide [ Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul ] ;
      rw [ Finset.sum_range_succ', Finset.sum_range_succ ] ; simp +decide [];
      exact Finset.sum_congr rfl fun x hx => by rw [ if_pos ( Finset.mem_range.mp hx ) ] ;
    have h_triangle : normHS (∑ i ∈ Finset.range (j + 1), (Rᴴ * P i * R - (if i + 1 < j + 1 then P (i + 1) else P 0))) ^ 2 ≤ 2 * normHS (∑ i ∈ Finset.range j, (Rᴴ * P i * R - P (i + 1))) ^ 2 + 2 * normHS (Rᴴ * P j * R - P 0) ^ 2 := by
      have h_triangle : normHS (∑ i ∈ Finset.range (j + 1), (Rᴴ * P i * R - (if i + 1 < j + 1 then P (i + 1) else P 0))) ≤ normHS (∑ i ∈ Finset.range j, (Rᴴ * P i * R - P (i + 1))) + normHS (Rᴴ * P j * R - P 0) := by
        convert normHS_add_le _ _ using 2 ; simp +decide [ Finset.sum_range_succ ];
        rw [ Finset.sum_congr rfl fun x hx => if_pos ( Finset.mem_range.mp hx ) ] ; abel1;
      exact le_trans ( pow_le_pow_left₀ ( by exact normHS_nonneg _ ) h_triangle 2 ) ( by linarith [ sq_nonneg ( normHS ( ∑ i ∈ Finset.range j, ( Rᴴ * P i * R - P ( i + 1 ) ) ) - normHS ( Rᴴ * P j * R - P 0 ) ) ] );
    have h_semitriangle : normHS (∑ i ∈ Finset.range j, (Rᴴ * P i * R - P (i + 1))) ^ 2 ≤ (j : ℝ) * ∑ i ∈ Finset.range j, normHS (Rᴴ * P i * R - P (i + 1)) ^ 2 := by
      convert LamplighterStability.semitriangle j ( fun i => Rᴴ * P i * R - P ( i + 1 ) ) using 1;
    rw [ h_telescope ];
    nlinarith [ show ( j : ℝ ) ≥ 0 by positivity, show ( ∑ i ∈ Finset.range j, normHS ( Rᴴ * P i * R - P ( i + 1 ) ) ^ 2 ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => sq_nonneg _ ]

/-
**Error-block bounds.**  For a projection `G` (Hermitian idempotent) and a
unitary `T`, the compression and conjugation defects of `G` are each at most
`4·tr(G)`.
-/
lemma compress_sub_proj_le {G : Matrix ι ι ℂ} (hGh : G.IsHermitian)
    (hGi : IsIdempotentElem G)
    {T : Matrix ι ι ℂ} (hT : star T * T = 1) (hT' : T * star T = 1) :
    normHS (G * T * G - G) ^ 2 ≤ 4 * ntrace G
      ∧ normHS (star T * G * T - G) ^ 2 ≤ 4 * ntrace G := by
  have h1 : normHS (G * T * G - G) ≤ 2 * normHS G := by
    refine' le_trans ( LamplighterStability.normHS_sub_le _ _ ) _;
    have h_bound : normHS (G * (T * G)) ≤ normHS (T * G) := by
      apply LamplighterStability.normHS_proj_mul_le; exact ⟨hGh, hGi⟩;
    simp_all +decide [ ← Matrix.mul_assoc ];
    convert add_le_add h_bound le_rfl using 1 ; ring;
    rw [ show normHS ( T * G ) = normHS G from normHS_mul_left_isometry hT ] ; ring
  have h2 : normHS (star T * G * T - G) ≤ 2 * normHS G := by
    convert normHS_sub_le ( star T * G * T ) G |> le_trans <| add_le_add ( normHS_conj_eq hT hT' |> le_of_eq ) le_rfl using 1 ; ring!;
  have h3 : normHS G ^ 2 = ntrace G := by
    convert normHS_sq_eq_ntrace _;
    rw [ hGh.eq, hGi.eq ];
  exact ⟨ by nlinarith only [ h1, h3, show 0 ≤ normHS ( G * T * G - G ) from normHS_nonneg _ ], by nlinarith only [ h2, h3, show 0 ≤ normHS ( star T * G * T - G ) from normHS_nonneg _ ] ⟩

/-
**`lem:p-ortho`, Fintype-indexed.**  The block-grouping `L²` bound of
`p_ortho` with the blocks indexed by an arbitrary finite type `κ` instead of
`Fin t`.
-/
lemma p_ortho_fintype {X : Type*} [Fintype X] [DecidableEq X]
    {κ : Type*} [Fintype κ]
    (P Q : X → Matrix ι ι ℂ)
    (hP : ∀ x, IsProj (P x)) (hQ : ∀ x, IsProj (Q x))
    (hPo : ∀ x y, x ≠ y → P x * P y = 0)
    (hQo : ∀ x y, x ≠ y → Q x * Q y = 0)
    (b : κ → Finset X)
    (hb : ∀ i k, i ≠ k → Disjoint (b i) (b k)) :
    ∑ i, normHS ((∑ x ∈ b i, P x) - (∑ x ∈ b i, Q x)) ^ 2
      ≤ 4 * ∑ x, normHS (P x - Q x) ^ 2 := by
  obtain ⟨e⟩ : ∃ e : κ ≃ Fin (Fintype.card κ), True := by
    exact ⟨ Fintype.equivFin κ, trivial ⟩;
  convert p_ortho P Q hP hQ hPo hQo ( fun j => b ( e.symm j ) ) ( fun i k hik => ?_ ) using 1;
  · rw [ ← Equiv.sum_comp e.symm ];
  · exact hb _ _ ( by simpa [ e.symm.injective.eq_iff ] using hik )

end LamplighterStability