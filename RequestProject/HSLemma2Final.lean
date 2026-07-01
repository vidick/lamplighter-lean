import Mathlib
import RequestProject.HSPolarRound
import RequestProject.HSSpectral
import RequestProject.HSStability
import RequestProject.HSSeparation

/-!
# Lemma 2 and same-dimensional stability (note Corollary 1), discharging `AbelianStability`

This file assembles the pieces developed in `HSLemma2`, `HSSpectral`, `HSPolarRound` and
`HSStability` into:

* `lemma2_rounding` — the note's **Lemma 2** (`gh_hs_projection_note_revised-1.pdf`, §3): rounding
  an almost-invariant `d`-plane to an exact invariant one, with the constant `5`.
* `abelianStability_holds` — the note's **Corollary 1** (same-dimensional stability for finite
  abelian groups), i.e. a proof of the hypothesis `AbelianStability` from
  `RequestProject.HSSeparation`.

Combining the weak averaged Gowers–Hatami theorem (`GowersHatami.gowers_hatami`, used only through
the dimension-free intertwiner of `HSStability`) with Lemma 2 makes the normalized-HS separation
theorems unconditional.
-/

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ComplexInnerProductSpace
open Finset HSMaps
open ContinuousLinearMap (adjoint)

namespace HSLemma2

variable {d : ℕ}
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
variable {G : Type} [CommGroup G] [Fintype G] [DecidableEq G]

/-! ### Building the close invariant projection (Phases A–C of Lemma 2) -/

/-
Combining the averaging bound `hsq (E − M) ≤ δ²·d` (`hsq_Eproj_sub_Mavg_le`) with the
invariant nearest rank-`d` projection (`exists_invariant_proj_near`) gives a `π`-invariant rank-`d`
projection `F` with `hsq (F − E) ≤ 4 δ²·d`, where `E = W Wᴴ`.
-/
lemma exists_invariant_proj_close (hd : 0 < d)
    (π : G →* (K →L[ℂ] K)) (hπ : ∀ g, π g ∈ unitary (K →L[ℂ] K))
    (W : H d →L[ℂ] K) (hW : adjoint W ∘L W = 1)
    (f : G → (H d →L[ℂ] H d))
    (δ : ℝ)
    (hbound : ∀ x, hsq (π x ∘L W - W ∘L f x) ≤ δ ^ 2 * d) :
    ∃ F : K →L[ℂ] K, adjoint F = F ∧ F ∘L F = F ∧
      LinearMap.trace ℂ K F.toLinearMap = (d : ℂ) ∧
      (∀ x, π x ∘L F = F ∘L π x) ∧
      hsq (F - Eproj W) ≤ 4 * δ ^ 2 * d := by
  -- F is a self-adjoint idempotent with trace d, so d ≤ finrank K.
  have hD_le : d ≤ Module.finrank ℂ K := by
    have h_finrank : Module.finrank ℂ (LinearMap.range (W : H d →ₗ[ℂ] K)) = d := by
      rw [ LinearMap.finrank_range_of_inj ];
      · simp +decide [ H ];
      · intro x y hxy; have := congr_arg ( fun f => f x ) hW; have := congr_arg ( fun f => f y ) hW; simp_all +decide [ ContinuousLinearMap.ext_iff ] ;
    exact h_finrank ▸ Submodule.finrank_le _;
  obtain ⟨F, hF⟩ : ∃ F : K →L[ℂ] K, adjoint F = F ∧ F ∘L F = F ∧ LinearMap.trace ℂ K F.toLinearMap = d ∧ (∀ x, π x ∘L F = F ∘L π x) ∧ hsq (F - Mavg π W) ≤ hsq (Mavg π W - Eproj W) := by
    convert exists_invariant_proj_near π hπ ( Mavg π W ) ( Mavg_selfadjoint π W ) ( Mavg_commute π hπ W ) ( Eproj W ) ( Eproj_selfadjoint W ) ( Eproj_idem W hW ) ( trace_Eproj W hW ) hD_le using 1;
    ext; simp +decide [] ;
    intro h1 h2 h3 h4; rw [ show ( _ - Mavg π W : K →L[ℂ] K ) = - ( Mavg π W - _ ) by abel1, hsq_neg ] ;
  refine' ⟨ F, hF.1, hF.2.1, hF.2.2.1, hF.2.2.2.1, _ ⟩;
  have hF_E : hsq (F - Eproj W) ≤ (hsF (F - Mavg π W) + hsF (Mavg π W - Eproj W)) ^ 2 := by
    convert pow_le_pow_left₀ ( hsF_nonneg _ ) ( hsF_sub_triangle F ( Mavg π W ) ( Eproj W ) ) 2 using 1;
    exact Eq.symm ( Real.sq_sqrt ( hsq_nonneg _ ) );
  have hF_E_bound : hsF (F - Mavg π W) ≤ Real.sqrt (δ ^ 2 * d) ∧ hsF (Mavg π W - Eproj W) ≤ Real.sqrt (δ ^ 2 * d) := by
    have hF_E_bound : hsq (Mavg π W - Eproj W) ≤ δ ^ 2 * d := by
      convert HSLemma2.hsq_Eproj_sub_Mavg_le π hπ W hW f δ hbound using 1;
      rw [ ← hsq_neg, neg_sub ];
    exact ⟨ Real.sqrt_le_sqrt <| by linarith, Real.sqrt_le_sqrt <| by linarith ⟩;
  exact hF_E.trans ( by nlinarith only [ show 0 ≤ hsF ( F - Mavg π W ) from hsF_nonneg _, show 0 ≤ hsF ( Mavg π W - Eproj W ) from hsF_nonneg _, hF_E_bound, Real.mul_self_sqrt ( show 0 ≤ δ ^ 2 * ↑d by positivity ) ] )

/-! ### The representation `σ` and the final pointwise estimate -/

omit [DecidableEq G] in
omit [Fintype G] in
/-
Each operator `σ(x) = Uᴴ π(x) U` is unitary (using `U Uᴴ = F`, `F U = U`, and that `F` commutes
with `π(x)` and its adjoint).
-/
lemma sigma_op_mem_unitary
    (π : G →* (K →L[ℂ] K)) (hπ : ∀ g, π g ∈ unitary (K →L[ℂ] K))
    (F : K →L[ℂ] K)
    (hFcomm : ∀ x, π x ∘L F = F ∘L π x)
    (U : H d →L[ℂ] K)
    (hUU : adjoint U ∘L U = 1) (hUF : U ∘L adjoint U = F) (hFU : F ∘L U = U)
    (x : G) :
    (adjoint U ∘L (π x ∘L U)) ∈ unitary (H d →L[ℂ] H d) := by
  constructor;
  · simp_all +decide [ ContinuousLinearMap.ext_iff ];
    intro y; specialize hπ x; have := hπ.1; have := hπ.2; simp_all +decide [ ContinuousLinearMap.ext_iff, star ] ;
    grind;
  · have := hπ x;
    obtain ⟨ h₁, h₂ ⟩ := this;
    simp_all +decide [ ContinuousLinearMap.ext_iff, star ]

omit [DecidableEq G] in
omit [Fintype G] in
/-
The assignment `x ↦ Uᴴ π(x) U` is multiplicative (using `U Uᴴ = F`, `F U = U`, and that `F`
commutes with `π`).
-/
lemma sigma_op_map_mul
    (π : G →* (K →L[ℂ] K))
    (F : K →L[ℂ] K)
    (hFcomm : ∀ x, π x ∘L F = F ∘L π x)
    (U : H d →L[ℂ] K)
    (hUF : U ∘L adjoint U = F) (hFU : F ∘L U = U)
    (x y : G) :
    adjoint U ∘L (π (x * y) ∘L U)
      = (adjoint U ∘L (π x ∘L U)) ∘L (adjoint U ∘L (π y ∘L U)) := by
  simp_all +decide [ ContinuousLinearMap.ext_iff ];
  simp +decide [ ← hFcomm, hFU ]

omit [DecidableEq G] in
omit [Fintype G] in
/-
The pointwise estimate `‖f(x) − Uᴴ π(x) U‖₂,d ≤ 5δ`.
-/
lemma sigma_op_bound (hd : 0 < d)
    (π : G →* (K →L[ℂ] K)) (hπ : ∀ g, π g ∈ unitary (K →L[ℂ] K))
    (W : H d →L[ℂ] K)
    (f : G → (H d →L[ℂ] H d)) (hf : ∀ x, f x ∈ unitary (H d →L[ℂ] H d))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : ∀ x, hsq (π x ∘L W - W ∘L f x) ≤ δ ^ 2 * d)
    (U : H d →L[ℂ] K)
    (hUU : adjoint U ∘L U = 1)
    (hUWbound : hsq (U - W) ≤ 4 * δ ^ 2 * d)
    (x : G) :
    hsNorm (f x - adjoint U ∘L (π x ∘L U)) ≤ 5 * δ := by
  -- Decompose `U ∘L f x - π x ∘L U` and apply `hsF_triangle` twice.
  have h_decomp : hsF (U ∘L f x - (π x) ∘L U) ≤ 2 * hsF (U - W) + hsF (W ∘L f x - (π x) ∘L W) := by
    have h_decomp : U ∘L f x - (π x) ∘L U = (U - W) ∘L (f x) + (W ∘L f x - (π x) ∘L W) + (π x) ∘L (W - U) := by
      simp +decide [ ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp ];
    -- Apply `hsF_triangle` to each term in the decomposition.
    have h_triangle1 : hsF ((U - W) ∘L (f x)) = hsF (U - W) := by
      apply congr_arg Real.sqrt;
      apply hsq_comp_right_iso;
      exact hf x |>.1
    have h_triangle2 : hsF ((π x) ∘L (W - U)) ≤ hsF (U - W) := by
      convert HSMaps.hsF_comp_left_le ( π x ) ( show ‖π x‖ ≤ 1 from ?_ ) ( W - U ) using 1;
      · rw [ ← HSMaps.hsF_neg, neg_sub ];
      · have h_unitary : ∀ v : K, ‖(π x) v‖ = ‖v‖ := by
          exact?;
        exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp +decide [ h_unitary ] ;
    rw [h_decomp];
    refine' le_trans ( hsF_triangle _ _ ) _;
    refine' le_trans ( add_le_add ( hsF_triangle _ _ ) h_triangle2 ) _;
    linarith;
  -- By `hsF_comp_left_le` with `‖adjoint U‖ ≤ 1` (`opNorm_adjoint_le_one U hUU`), `hsF (f x - adjoint U ∘L (π x ∘L U)) ≤ hsF (U ∘L f x - π x ∘L U)`.
  have h_adj : hsF (f x - (adjoint U).comp ((π x).comp U)) ≤ hsF (U ∘L f x - (π x).comp U) := by
    have h_adj : hsF (f x - (adjoint U).comp ((π x).comp U)) ≤ hsF ((adjoint U).comp (U.comp (f x) - (π x).comp U)) := by
      convert le_rfl using 2;
      simp +decide [ ← ContinuousLinearMap.comp_assoc, hUU ];
      exact ContinuousLinearMap.ext fun _ => rfl;
    refine' le_trans h_adj ( HSMaps.hsF_comp_left_le _ _ _ );
    convert HSLemma2.opNorm_adjoint_le_one U hUU using 1;
  -- By `hsF_neg` and `hbound`, `hsF (W ∘L f x - (π x) ∘L W) = hsF ((π x) ∘L W - W ∘L f x) ≤ δ * Real.sqrt d`.
  have h_neg_bound : hsF (W ∘L f x - (π x).comp W) ≤ δ * Real.sqrt d := by
    convert Real.sqrt_le_sqrt ( hbound x ) using 1;
    · rw [ ← hsq_neg ] ; simp +decide [ hsF ] ;
    · rw [ Real.sqrt_mul ( sq_nonneg _ ), Real.sqrt_sq hδ ];
  -- By `hsF_nonneg` and `hUWbound`, `hsF (U - W) ≤ 2 * δ * Real.sqrt d`.
  have h_UWbound : hsF (U - W) ≤ 2 * δ * Real.sqrt d := by
    exact Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith [ Real.mul_self_sqrt ( Nat.cast_nonneg d ) ] ⟩;
  convert div_le_div_of_nonneg_right ( h_adj.trans ( h_decomp.trans ( add_le_add ( mul_le_mul_of_nonneg_left h_UWbound zero_le_two ) h_neg_bound ) ) ) ( Real.sqrt_nonneg d ) using 1;
  · rw [ hsNorm_def_sqrt, hsF, hsq_eq_hsNormSq ];
    rw [ Real.sqrt_div' _ ( Nat.cast_nonneg _ ) ];
  · rw [ eq_div_iff ] <;> first | positivity | ring;

omit [DecidableEq G] in
omit [Fintype G] in
/-- Given the invariant projection `F` (with `F = U Uᴴ` from polar rounding) and the polar isometry
`U` close to `W`, the operator `σ(x) = Uᴴ π(x) U` is a genuine unitary representation on `ℂ^d`
with `‖f(x) − σ(x)‖₂,d ≤ 5δ`. -/
lemma exists_sigma_near (hd : 0 < d)
    (π : G →* (K →L[ℂ] K)) (hπ : ∀ g, π g ∈ unitary (K →L[ℂ] K))
    (W : H d →L[ℂ] K)
    (f : G → (H d →L[ℂ] H d)) (hf : ∀ x, f x ∈ unitary (H d →L[ℂ] H d))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : ∀ x, hsq (π x ∘L W - W ∘L f x) ≤ δ ^ 2 * d)
    (F : K →L[ℂ] K)
    (hFcomm : ∀ x, π x ∘L F = F ∘L π x)
    (U : H d →L[ℂ] K)
    (hUU : adjoint U ∘L U = 1) (hUF : U ∘L adjoint U = F) (hFU : F ∘L U = U)
    (hUWbound : hsq (U - W) ≤ 4 * δ ^ 2 * d) :
    ∃ σ : G →* (H d →L[ℂ] H d),
      (∀ g, σ g ∈ unitary (H d →L[ℂ] H d)) ∧
      (∀ x, hsNorm (f x - σ x) ≤ 5 * δ) := by
  refine ⟨{ toFun := fun x => adjoint U ∘L (π x ∘L U)
            map_one' := by
              show adjoint U ∘L (π 1 ∘L U) = 1
              rw [map_one, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, hUU]
            map_mul' := fun x y =>
              sigma_op_map_mul π F hFcomm U hUF hFU x y }, ?_, ?_⟩
  · intro g
    exact sigma_op_mem_unitary π hπ F hFcomm U hUU hUF hFU g
  · intro x
    exact sigma_op_bound hd π hπ W f hf δ hδ hbound U hUU hUWbound x

/-! ### Lemma 2 -/

/-- **Lemma 2 (rounding an almost-invariant `d`-plane).**  Let `π : G → U(K)` be a finite-dimensional
unitary representation of a finite abelian group, `W : ℂ^d → K` an isometry, and `f : G → U(ℂ^d)` a
map with `‖π(x)W − W f(x)‖₂,d ≤ δ` for all `x` (here in the squared, unnormalized form
`hsq (π x W − W f(x)) ≤ δ²·d`).  Then there is a genuine unitary representation `σ : G → U(ℂ^d)`
with `‖f(x) − σ(x)‖₂,d ≤ 5δ`. -/
lemma lemma2_rounding (hd : 0 < d)
    (π : G →* (K →L[ℂ] K)) (hπ : ∀ g, π g ∈ unitary (K →L[ℂ] K))
    (W : H d →L[ℂ] K) (hW : adjoint W ∘L W = 1)
    (f : G → (H d →L[ℂ] H d)) (hf : ∀ x, f x ∈ unitary (H d →L[ℂ] H d))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbound : ∀ x, hsq (π x ∘L W - W ∘L f x) ≤ δ ^ 2 * d) :
    ∃ σ : G →* (H d →L[ℂ] H d),
      (∀ g, σ g ∈ unitary (H d →L[ℂ] H d)) ∧
      (∀ x, hsNorm (f x - σ x) ≤ 5 * δ) := by
  obtain ⟨F, hFsa, hFidem, hFtr, hFcomm, hFE⟩ :=
    exists_invariant_proj_close hd π hπ W hW f δ hbound
  obtain ⟨U, hUU, hUF, hFU, hUW⟩ :=
    exists_isometry_polar_near W hW F hFsa hFidem hFtr
  refine exists_sigma_near hd π hπ W f hf δ hδ hbound F hFcomm U hUU hUF hFU ?_
  exact le_trans hUW hFE

end HSLemma2

/-! ### The right-regular representation as a unitary `MonoidHom` -/

open ContinuousLinearMap (adjoint)

/-- The right-regular representation on `K = L²(G,H)` packaged as a `MonoidHom` into the continuous
linear maps. -/
def piRep (G : Type) [Group G] [Fintype G] [DecidableEq G] (d : ℕ) :
    G →* (K G d →L[ℂ] K G d) where
  toFun g := (rightRegularRep G g).toContinuousLinearMap
  map_one' := by
    simp only [map_one]
    ext v; rfl
  map_mul' g h := by
    simp only [map_mul]
    ext v; rfl

lemma piRep_unitary (G : Type) [Group G] [Fintype G] [DecidableEq G] (d : ℕ) (g : G) :
    piRep G d g ∈ unitary (K G d →L[ℂ] K G d) := by
  constructor;
  · ext v x; simp +decide [ star ] ;
    rename_i i; erw [ show ( InnerProductSpace.toDual ℂ ( K G d ) ).symm ( _ ) = _ from ?_ ] ;
    refine' ( InnerProductSpace.toDual ℂ ( K G d ) ).injective _;
    ext w; simp +decide ;
    exact Equiv.sum_comp ( Equiv.mulRight g ) fun x => inner ℂ ( v x ) ( w x );
  · ext v x; simp +decide [ star ] ;
    rw [ show ( adjoint ( piRep G d g ) ) v = ( WithLp.equiv 2 _ ).symm ( fun y => v ( y * g⁻¹ ) ) from ?_ ];
    · simp +decide [ piRep ];
      simp +decide [ rightRegularRep, rightRegular ];
    · refine' ext_inner_left ℂ _;
      intro w; rw [ ContinuousLinearMap.adjoint_inner_right ] ; simp +decide [ piRep ] ;
      simp +decide [ inner, rightRegularRep ];
      rw [ ← Equiv.sum_comp ( Equiv.mulRight g⁻¹ ) ] ; simp +decide [ rightRegular ]

/-! ### Same-dimensional stability (note Corollary 1): discharging `AbelianStability` -/

/-
**Same-dimensional stability for finite abelian groups** (note Corollary 1, constant `5`).
This proves the hypothesis `AbelianStability` from `RequestProject.HSSeparation`.
-/
theorem abelianStability_holds (d : ℕ) : AbelianStability d := by
  intro hd G _ _ _ f hfu hf1 δ hδ hδrep;
  convert HSLemma2.lemma2_rounding hd ( piRep G d ) ( piRep_unitary G d ) ( ( gowersHatamiIso G ( fun g => ⟨ f g, hfu g ⟩ ) ).toContinuousLinearMap ) _ f hfu δ hδ _ using 1;
  · ext; simp +decide [ ContinuousLinearMap.adjoint ] ;
    rename_i x i; erw [ show ( InnerProductSpace.toDual ℂ ( H d ) ).symm ( _ ) = _ from ?_ ] ;
    refine' ( InnerProductSpace.toDual ℂ ( H d ) ).injective _;
    ext y; simp +decide ;
  · convert fun x => gh_intertwiner_normSq_le G ( fun g => ⟨ f g, hfu g ⟩ ) δ _ x using 1;
    · rw [ HSMaps.hsq_single ] ; aesop;
    · intro x y; specialize hδrep x y; rw [ hsNorm_def_sqrt ] at hδrep;
      rw [ Real.sqrt_le_iff ] at hδrep;
      convert mul_le_mul_of_nonneg_right hδrep.2 ( Nat.cast_nonneg d ) using 1;
      rw [ div_mul_cancel₀ _ ( by positivity ) ] ; simp +decide [ hsNormSq ] ;
      exact Finset.sum_congr rfl fun _ _ => by rw [ norm_sub_rev ] ;

/-! ### Unconditional separation theorems -/

/-- **Normalized Hilbert–Schmidt separation of projections** (note Theorem 1), unconditional form.
If `P₁,…,P_N` are projections on `ℂ^d` (`d > 0`) with pairwise commutators of normalized HS norm
at most `ε`, then there exist pairwise commuting projections `Q₁,…,Q_N` with
`‖Pᵢ − Qᵢ‖₂,d ≤ 5·N(N−1)·ε`.  The same-dimensional stability input is discharged by
`abelianStability_holds`. -/
theorem hs_separation' {d N : ℕ} (hd : 0 < d)
    (P : Fin N → (H d →L[ℂ] H d)) (hP : ∀ i, IsProjCLM (P i))
    (ε : ℝ) (hε0 : 0 ≤ ε)
    (hcomm : ∀ i j, hsNorm (P i * P j - P j * P i) ≤ ε) :
    ∃ Q : Fin N → (H d →L[ℂ] H d),
      (∀ i, IsProjCLM (Q i)) ∧ (∀ i j, Q i * Q j = Q j * Q i) ∧
      (∀ i, hsNorm (P i - Q i) ≤ 5 * ((N : ℝ) * ((N : ℝ) - 1)) * ε) :=
  hs_separation (abelianStability_holds d) hd P hP ε hε0 hcomm

/-- **Normalized Hilbert–Schmidt separation, `N²` form** (note Theorem 1), unconditional. -/
theorem hs_separation_N2' {d N : ℕ} (hd : 0 < d)
    (P : Fin N → (H d →L[ℂ] H d)) (hP : ∀ i, IsProjCLM (P i))
    (ε : ℝ) (hε0 : 0 ≤ ε)
    (hcomm : ∀ i j, hsNorm (P i * P j - P j * P i) ≤ ε) :
    ∃ Q : Fin N → (H d →L[ℂ] H d),
      (∀ i, IsProjCLM (Q i)) ∧ (∀ i j, Q i * Q j = Q j * Q i) ∧
      (∀ i, hsNorm (P i - Q i) ≤ 5 * (N : ℝ) ^ 2 * ε) :=
  hs_separation_N2 (abelianStability_holds d) hd P hP ε hε0 hcomm

end