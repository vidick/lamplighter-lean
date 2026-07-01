import RequestProject.Dynamics.KRTowers

/-!
# Proof of the tower-decomposition proposition (`prop:decomp`)

This file *proves* `prop_decomp` (`prop:decomp`, Section 5 of the paper), the
dynamical proposition stated as an interface in `TowerDecomp.lean`.  It lives
late in the import DAG so that it can use the full assembly machinery:

* the periodic covering `covering_per_seq` and the polynomial marker lemma
  `marker_lemma` (`MarkerLemmas.lean`, interfaces);
* the complement / escape bound `complement_bound` and the elementary
  `FIndep`/tower manipulations (`TowerDecompAssembly.lean`);
* the Kakutani–Rokhlin "markers → towers" construction (`KRTowers.lean`).

The construction: choose a window `ℓ`, cover the periodic part `X_per^ℓ(t)` by
`covering_per_seq`, build a marker `Z` for the aperiodic part via `marker_lemma`,
run the first-return construction on `W = L^{-t}(⋂_{i∈F_t}(Z ∩ L^{-i}Ξ))`, and
glue the two families, refining the aperiodic towers by their `π`-patterns to
force the singleton-projection conclusion.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators
open scoped Classical

/-! ## The set `W` from the markers → towers construction -/

/-- `W = L^{-t}(⋂_{i∈F_t}(Z ∩ L^{-i} Ξ))`, the base set of the Kakutani–Rokhlin
construction.  `⋃_{k=0}^{2t} L^k W ⊆ Ξ`, and `W` is `F_t`-independent. -/
def Wset (Z Ξ : Set Cfg) (t : ℕ) : Set Cfg :=
  (L ^ (-(t : ℤ))) '' (⋂ i ∈ Finset.Icc (-(t : ℤ)) (t : ℤ), Z ∩ (L ^ (-i)) '' Ξ)

/-
`W` is `F_t`-independent (it is a translate of a subset of the marker `Z`).
-/
lemma Wset_fIndep {t : ℕ} {Z Ξ : Set Cfg} (hZ : FIndep t Z) :
    FIndep t (Wset Z Ξ t) := by
  convert FIndep.image_shift _ ( -t : ℤ ) using 1;
  intro i hi hi_ne; specialize hZ i ; simp_all +decide [ Set.disjoint_left ] ;
  exact fun a ha => ⟨ i, hi.1, hi.2, fun h => False.elim <| hZ ( ha i hi.1 hi.2 |>.1 ) h ⟩

/-
The orbit segment `⋃_{k=0}^{2t} L^k W` is contained in `Ξ`.
-/
lemma KRorbit_subset {t : ℕ} {Z Ξ : Set Cfg} :
    KRorbit (Wset Z Ξ t) (2 * t) ⊆ Ξ := by
  unfold KRorbit Wset;
  simp +decide [ Set.subset_def, Set.mem_iUnion ];
  intro x k hk h; specialize h ( - ( t - k ) ) ( by omega ) ( by omega ) ; simp_all +decide [] ;
  convert h.2 using 1;
  simp +decide [ sub_eq_add_neg, zpow_add, zpow_neg ]

/-
If `Z` is `Dz`-defined and `Ξ` is `Dx`-defined, then `W` is
`(Dz + Dx + 2t)`-defined.
-/
lemma Wset_defined {t Dz Dx : ℕ} {Z Ξ : Set Cfg} (hZ : Defined Dz Z)
    (hΞ : Defined Dx Ξ) : Defined (Dz + Dx + 2 * t) (Wset Z Ξ t) := by
  -- Prove that the intersection inside `Wset` is `(Dz + Dx + t)`-defined.
  have hInter : Defined (Dz + Dx + t) (⋂ i ∈ Finset.Icc (-(t : ℤ)) t, Z ∩ (L ^ (-i : ℤ)) '' Ξ) := by
    -- Each term $Z ∩ (L ^ (-i)) '' Ξ$ is $(Dz + Dx + t)$-defined.
    have hTerm : ∀ i ∈ Finset.Icc (-(t : ℤ)) t, Defined (Dz + Dx + t) (Z ∩ (L ^ (-i : ℤ)) '' Ξ) := by
      intro i hi
      have hZ_term : Defined (Dz + Dx + t) Z := by
        exact Defined.mono ( by linarith ) hZ
      have hΞ_term : Defined (Dz + Dx + t) ((L ^ (-i : ℤ)) '' Ξ) := by
        refine' Defined.mono ( show Dx + ( -i ).natAbs ≤ Dz + Dx + t from by cases abs_cases ( -i ) <;> linarith [ Finset.mem_Icc.mp hi ] ) ( defined_shift hΞ ( -i ) )
      exact defined_inter hZ_term hΞ_term;
    intro x y hxy; simp +decide [] ;
    constructor <;> intro h i hi₁ hi₂ <;> specialize h i hi₁ hi₂ <;> specialize hTerm i ( Finset.mem_Icc.mpr ⟨ hi₁, hi₂ ⟩ ) <;> have := hTerm x y hxy <;> aesop;
  convert defined_shift hInter ( -t ) using 1 ; ring!;
  omega

/-! ## The refined aperiodic tower family

We index the aperiodic towers by `Fin (2t+1) × (Win (2t+1) → Bool)`: the first
component `k` gives height `k+1` (so heights `1 … 2t+1`), and the second
component `p` refines each base by its `π_{2t+1}`-pattern, forcing the
singleton-projection conclusion. -/

/-- The aperiodic index type. -/
abbrev AperIdx (t : ℕ) : Type := Fin (2 * t + 1) × (Win (2 * t + 1) → Bool)

/-- The refined aperiodic base. -/
def aperBaseR (W : Set Cfg) (t : ℕ) (τ : AperIdx t) : Set Cfg :=
  aperBase W (2 * t) (τ.1.val + 1) ∩ cyl (2 * t + 1) τ.2

/-- The refined aperiodic height. -/
def heightR (t : ℕ) (τ : AperIdx t) : ℕ := τ.1.val + 1

lemma aperBaseR_subset (W : Set Cfg) (t : ℕ) (τ : AperIdx t) :
    aperBaseR W t τ ⊆ aperBase W (2 * t) (τ.1.val + 1) :=
  Set.inter_subset_left

/-
Each refined aperiodic base is a tower base of its height.
-/
lemma aperR_isTowerBase (W : Set Cfg) (t : ℕ) (τ : AperIdx t) :
    IsTowerBase (heightR t τ) (aperBaseR W t τ) := by
  apply IsTowerBase.subset;
  apply aper_isTowerBase;
  exacts [ W, by exact Nat.succ_le_succ ( Fin.is_le _ ), aperBaseR_subset _ _ _ ]

/-
Each refined aperiodic base has singleton `π_{height}`-projection.
-/
lemma aperR_projSingleton (W : Set Cfg) (t : ℕ) (τ : AperIdx t) :
    ProjSingleton (heightR t τ) (aperBaseR W t τ) := by
  refine' ProjSingleton.mono_window _ _;
  exact 2 * t + 1;
  · exact Nat.succ_le_succ ( Fin.is_le _ );
  · exact ⟨ τ.2, fun x hx => hx.2 ⟩

/-
Floor disjointness across the refined aperiodic family.
-/
lemma aperR_disjoint (W : Set Cfg) (t : ℕ) (τ τ' : AperIdx t) (i i' : ℕ)
    (hi : i < heightR t τ) (hi' : i' < heightR t τ') (hne : ¬ (τ = τ' ∧ i = i')) :
    Disjoint (towerFloor (aperBaseR W t τ) i) (towerFloor (aperBaseR W t τ') i') := by
  by_cases h : (τ.1.val + 1 = τ'.1.val + 1 ∧ i = i');
  · simp_all +decide [ Set.disjoint_left ];
    simp_all +decide [ aperBaseR ];
    intro x hx₁ hx₂ hx₃; have := cyl_disjoint ( show τ.2 ≠ τ'.2 from by contrapose! hne; aesop ) ; simp_all +decide [ Set.disjoint_left ] ;
  · refine' Disjoint.mono _ _ ( aper_floors_disjoint _ _ hi hi' h );
    any_goals exact 2 * t;
    any_goals unfold heightR; linarith [ Fin.is_lt τ.1, Fin.is_lt τ'.1 ];
    any_goals exact W;
    · exact Set.image_mono ( aperBaseR_subset _ _ _ );
    · exact Set.image_mono ( aperBaseR_subset _ _ _ )

/-
The refined aperiodic floors tile the orbit segment `KRorbit W (2t)`.
-/
lemma aperR_cover (W : Set Cfg) (t : ℕ) :
    (⋃ τ : AperIdx t, ⋃ i ∈ Finset.range (heightR t τ),
        towerFloor (aperBaseR W t τ) i) = KRorbit W (2 * t) := by
  refine' trans _ ( aper_floors_cover W ( 2 * t ) );
  ext x;
  simp +decide [ aperBaseR, aperFloors ];
  constructor;
  · rintro ⟨ a, b, i, hi, hi', hi'' ⟩;
    exact ⟨ a + 1, ⟨ by linarith [ Fin.is_lt a ], by linarith [ Fin.is_lt a ] ⟩, i, hi', hi ⟩;
  · rintro ⟨ i, ⟨ hi₁, hi₂ ⟩, j, hj₁, hj₂ ⟩;
    refine' ⟨ ⟨ i - 1, _ ⟩, proj ( 2 * t + 1 ) ( ( Equiv.symm ( L ^ j ) ) x ), j, _, _, _ ⟩ <;> norm_num [ heightR ];
    · grind;
    · rwa [ Nat.sub_add_cancel hi₁ ];
    · exact Nat.le_pred_of_lt hj₁

/-
If `W` is `Dw`-defined, every refined aperiodic floor is
`(Dw + 2*(2t) + 1)`-defined.
-/
lemma aperR_floor_defined {Dw t : ℕ} {W : Set Cfg} (hW : Defined Dw W)
    (τ : AperIdx t) (i : ℕ) (hi : i < heightR t τ) :
    Defined (Dw + 2 * (2 * t) + 1) (towerFloor (aperBaseR W t τ) i) := by
  obtain ⟨q, hq⟩ : ∃ q : Win (2 * t + 1) → Bool, aperBaseR W t τ = aperBase W (2 * t) (τ.1.val + 1) ∩ cyl (2 * t + 1) q := by
    exact ⟨ _, rfl ⟩;
  have h_base : Defined (Dw + 2 * t + 1) (aperBaseR W t τ) := by
    have h_base : Defined (Dw + 2 * t) (aperBase W (2 * t) (τ.1.val + 1)) := by
      apply aperBase_defined hW;
    exact hq.symm ▸ defined_inter ( Defined.mono ( by linarith ) h_base ) ( Defined.mono ( by linarith ) ( defined_cyl _ _ ) );
  have h_floor : Defined (Dw + 2 * t + 1 + i) (towerFloor (aperBaseR W t τ) i) := by
    convert defined_shift h_base i using 1;
  exact Defined.mono ( by linarith [ show i ≤ 2 * t from by { unfold heightR at hi; linarith [ Fin.is_lt τ.1 ] } ] ) h_floor

/-
Aperiodic bases of height `< t` are empty (since `W` is `F_t`-independent).
-/
lemma aperBaseR_empty_of_lt {t : ℕ} {W : Set Cfg} (hW : FIndep t W) (τ : AperIdx t)
    (hlt : heightR t τ < t) : aperBaseR W t τ = ∅ := by
  unfold aperBaseR aperBase heightR at *;
  rw [ if_pos ( by linarith ), KRbase_eq_empty_of_le hW ( by linarith ) ( by linarith ) ] ; norm_num

/-! ## Measure of the aperiodic complement -/

/-
If `W` is `Dw`-defined then `KRorbit W N` is `(Dw + N)`-defined.
-/
lemma KRorbit_defined {Dw N : ℕ} {W : Set Cfg} (hW : Defined Dw W) :
    Defined (Dw + N) (KRorbit W N) := by
  apply defined_biUnion_finset;
  intro i hi;
  refine' Defined.mono ( show Dw + N ≥ Dw + i from by linarith [ Finset.mem_range.mp hi ] ) _;
  convert defined_shift hW i using 1

/-
**Escape set inclusion.**  The aperiodic part not covered by the orbit
segment is contained in the union of escape sets `L^k Z \ L^{k-i} Ξ`.
-/
lemma escape_set_incl {t : ℕ} {Z Ξ : Set Cfg}
    (hsat : Ξ ⊆ ⋃ j ∈ Finset.Icc (-(t:ℤ)) (t:ℤ), (L ^ j) '' Z) :
    Ξ \ KRorbit (Wset Z Ξ t) (2 * t) ⊆
      ⋃ k ∈ Finset.Icc (-(t:ℤ)) (t:ℤ), ⋃ i ∈ Finset.Icc (-(t:ℤ)) (t:ℤ),
        ((L ^ k) '' Z) \ ((L ^ (k - i)) '' Ξ) := by
  intro x hx;
  simp +zetaDelta at *;
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, k₀ ∈ Finset.Icc (-(t : ℤ)) (t : ℤ) ∧ (L ^ (-k₀)) x ∈ Z := by
    have := hsat hx.1; simp_all +decide [ Set.subset_def ] ;
  by_cases h : ∀ i : ℤ, i ∈ Finset.Icc (-(t : ℤ)) (t : ℤ) → (L ^ (i - k₀)) x ∈ Ξ;
  · have h_contradiction : (L ^ (-k₀)) x ∈ ⋂ i ∈ Finset.Icc (-(t : ℤ)) (t : ℤ), Z ∩ (L ^ (-i)) '' Ξ := by
      simp_all +decide [ Set.mem_iInter ];
      intro i hi₁ hi₂; specialize h i hi₁ hi₂; simp_all +decide [ zpow_sub ] ;
    have h_contradiction : x ∈ (L ^ (k₀ + t)) '' (Wset Z Ξ t) := by
      use (L ^ (-t : ℤ)) ((L ^ (-k₀ : ℤ)) x);
      simp_all +decide [ Wset ];
      simp +decide [ zpow_add ];
    have h_contradiction : x ∈ KRorbit (Wset Z Ξ t) (2 * t) := by
      refine' Set.mem_iUnion₂.mpr ⟨ Int.toNat ( k₀ + t ), _, _ ⟩ <;> norm_num at *;
      · linarith;
      · rwa [ max_eq_left ( by linarith ) ];
    tauto;
  · push_neg at h;
    obtain ⟨ i, hi, hi' ⟩ := h; use k₀, by simpa using hk₀.2, i; simp_all +decide [ sub_eq_add_neg, zpow_add ] ;
    convert hi' using 1

/-
**Stripping the outer translate.**  Moving the inner `Ξ`-translate to the
origin costs at most `2tη` in measure (`approxInv`).
-/
lemma escape_shift_strip {t : ℕ} (ht : 1 ≤ t) {η : ℝ} (hη : 0 < η)
    {M₀ D : ℕ} {μ : Measure Cfg} [IsProbabilityMeasure μ] (hμ : ApproxInvMeasure M₀ η μ)
    {Z Ξ : Set Cfg} (hZdef : Defined D Z) (hΞdef : Defined D Ξ) (hD : D + 30 * t ≤ M₀)
    {k i : ℤ} (hk : k ∈ Finset.Icc (-(t:ℤ)) (t:ℤ)) (hi : i ∈ Finset.Icc (-(t:ℤ)) (t:ℤ)) :
    (μ (((L ^ k) '' Z) \ ((L ^ (k - i)) '' Ξ))).toReal
      ≤ (μ (((L ^ i) '' Z) \ Ξ)).toReal + 2 * (t:ℝ) * η := by
  -- Set `S := ((L^i) '' Z) \ Ξ`, `m := k - i`.
  set S := (L ^ i) '' Z \ Ξ
  set m := k - i;
  -- Rewrite: `((L^k) '' Z) \ ((L^(k-i)) '' Ξ) = (L^m) '' S`.
  have h_rewrite : ((L ^ k) '' Z) \ ((L ^ (k - i)) '' Ξ) = (L ^ m) '' S := by
    simp +zetaDelta at *;
    ext x; simp [Set.mem_diff];
    -- By definition of exponentiation, we know that $(L^k)^{-1} = L^{-k}$ and $(L^{k-i})^{-1} = L^{i-k}$.
    have h_exp : (L ^ k).symm = L ^ (-k) ∧ (L ^ (k - i)).symm = L ^ (i - k) := by
      simp +decide [ zpow_neg ];
      exact ⟨ rfl, by rw [ show i - k = - ( k - i ) by ring, zpow_neg ] ; rfl ⟩;
    simp +decide [ h_exp ];
    simp +decide [ h_exp, zpow_sub ];
  -- `Defined (D+t) S`: `(L^i) '' Z` is `Defined (D + i.natAbs)`, with `i.natAbs ≤ t`; `Ξ` is `Defined D`; use `defined_diff` and `Defined.mono`.
  have hS_defined : Defined (D + t) S := by
    convert defined_diff ( Defined.mono _ ( defined_shift hZdef i ) ) ( Defined.mono _ hΞdef ) using 1 ; norm_num;
    · cases abs_cases i <;> linarith [ Finset.mem_Icc.mp hi ];
    · linarith;
  -- Now use `approxInv_pow` with the one-element family `b : Fin 1 → Set Cfg := fun _ => S`, `q := m`, window `D + t`.
  have h_approxInv_pow : |(μ ((L ^ m) '' S)).toReal - (μ S).toReal| ≤ (m.natAbs : ℝ) * η := by
    convert approxInv_pow hμ ( show m.natAbs + ( D + t ) ≤ M₀ from ?_ ) ( show Pairwise ( Function.onFun Disjoint fun _ : Fin 1 => S ) from ?_ ) ( show ∀ _ : Fin 1, Defined ( D + t ) S from ?_ ) using 1;
    · norm_num;
    · grind;
    · simp +decide [ Pairwise ];
    · exact fun _ => hS_defined;
  simp_all +decide [ abs_le ];
  rw [ h_rewrite ] ; nlinarith [ show ( |↑m| : ℝ ) ≤ 2 * t by exact_mod_cast abs_le.mpr ⟨ by omega, by omega ⟩ ] ;

/-
**Measure of the aperiodic complement.**  Combining the escape inclusion, the
stripping bound, and the per-term complement bound `hcb`, the aperiodic part
not covered by the Kakutani–Rokhlin towers has measure `O(t⁶(υ+δ+η))`.
-/
lemma escape_measure_bound {t : ℕ} (ht : 1 ≤ t) {υ δ η : ℝ}
    (hυ : 0 < υ) (hδ : 0 < δ) (hη : 0 < η)
    {M₀ D : ℕ} {μ : Measure Cfg} [IsProbabilityMeasure μ] (hμ : ApproxInvMeasure M₀ η μ)
    {Z Ξ : Set Cfg} (hZdef : Defined D Z) (hΞdef : Defined D Ξ) (hD : D + 30 * t ≤ M₀)
    {Ccb : ℝ} (hCcb : 0 < Ccb)
    (hsat : Ξ ⊆ ⋃ j ∈ Finset.Icc (-(t:ℤ)) (t:ℤ), (L ^ j) '' Z)
    (hcb : ∀ i : ℤ, i ∈ Finset.Icc (-(t:ℤ)) (t:ℤ) →
        (μ (((L ^ i) '' Z) \ Ξ)).toReal ≤ Ccb * ((t:ℝ)^4*η + (t:ℝ)^3*δ + υ)) :
    (μ (Ξ \ KRorbit (Wset Z Ξ t) (2 * t))).toReal
      ≤ (9 * Ccb + 18) * (t:ℝ)^6 * (υ + δ + η) := by
  refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono <| escape_set_incl hsat ) _;
  · exact MeasureTheory.measure_ne_top _ _;
  · refine' le_trans _ ( _ : _ ≤ _ );
    exact ∑ k ∈ Finset.Icc ( -t : ℤ ) t, ∑ i ∈ Finset.Icc ( -t : ℤ ) t, ( μ ( ( L ^ k ) '' Z \ ( L ^ ( k - i ) ) '' Ξ ) |> ENNReal.toReal );
    · refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_biUnion_finset_le _ _ ) _;
      · exact ne_of_lt ( lt_of_le_of_lt ( Finset.sum_le_sum fun _ _ => MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide [ * ] ) );
      · rw [ ENNReal.toReal_sum ];
        · refine' Finset.sum_le_sum fun k hk => _;
          refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_biUnion_finset_le _ _ ) _;
          · exact ne_of_lt ( lt_of_le_of_lt ( Finset.sum_le_sum fun _ _ => MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide [ MeasureTheory.IsProbabilityMeasure.measure_univ ] ) );
          · rw [ ENNReal.toReal_sum ];
            exact fun _ _ => MeasureTheory.measure_ne_top _ _;
        · exact fun _ _ => MeasureTheory.measure_ne_top _ _;
    · refine' le_trans ( Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun i hi => _ ) _;
      use fun k i => Ccb * ( t ^ 4 * η + t ^ 3 * δ + υ ) + 2 * t * η;
      · convert escape_shift_strip ht hη hμ hZdef hΞdef hD hk hi |> le_trans <| add_le_add ( hcb i hi ) le_rfl using 1;
      · norm_num [ Int.card_Icc ];
        norm_cast ; norm_num [ Int.toNat_of_nonneg, add_nonneg ] ; ring_nf;
        nlinarith [ show ( t : ℝ ) ^ 6 ≥ t ^ 5 by exact pow_le_pow_right₀ ( by norm_cast ) ( by linarith ), show ( t : ℝ ) ^ 5 ≥ t ^ 4 by exact pow_le_pow_right₀ ( by norm_cast ) ( by linarith ), show ( t : ℝ ) ^ 4 ≥ t ^ 3 by exact pow_le_pow_right₀ ( by norm_cast ) ( by linarith ), show ( t : ℝ ) ^ 3 ≥ t ^ 2 by exact pow_le_pow_right₀ ( by norm_cast ) ( by linarith ), show ( t : ℝ ) ^ 2 ≥ t by exact mod_cast Nat.le_self_pow ( by linarith ) _, show ( t : ℝ ) ≥ 1 by norm_cast, show ( Ccb : ℝ ) * υ > 0 by positivity, show ( Ccb : ℝ ) * δ > 0 by positivity, show ( Ccb : ℝ ) * η > 0 by positivity, show ( η : ℝ ) > 0 by positivity, show ( δ : ℝ ) > 0 by positivity, show ( υ : ℝ ) > 0 by positivity ]

/-
**Set algebra for the final partition.**  If `E ∪ F = Ξᶜ` with `E`, `F`
disjoint and `K ⊆ Ξ`, then `F ∪ K` is the complement of the error set
`E ∪ (Ξ \ K)`.
-/
lemma tower_cover_eq {E F K Ξ : Set Cfg} (hEF : E ∪ F = Ξᶜ) (hEFdisj : Disjoint E F)
    (hKΞ : K ⊆ Ξ) : F ∪ K = (E ∪ (Ξ \ K))ᶜ := by
  simp_all +decide [ Set.ext_iff, Set.disjoint_left ];
  grind

end LamplighterStability.Dynamics

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators

/-
An arbitrary union of `n`-defined sets is `n`-defined (membership in each set,
hence in the union, depends only on the coordinates in `F_n`).
-/
lemma defined_iUnion {n : ℕ} {ι : Type*} {f : ι → Set Cfg}
    (hf : ∀ i, Defined n (f i)) : Defined n (⋃ i, f i) := by
  intro x y hxy
  simp only [Set.mem_iUnion]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, (hf i x y hxy).mp hi⟩,
         fun ⟨i, hi⟩ => ⟨i, (hf i x y hxy).mpr hi⟩⟩

/-
The complement of an `n`-defined set is `n`-defined.
-/
lemma defined_compl {n : ℕ} {A : Set Cfg} (hA : Defined n A) : Defined n Aᶜ := by
  intro x y hxy
  have := hA x y hxy
  simp only [Set.mem_compl_iff, this]

/-
**Core assembly of `prop_decomp`.**  Given the periodic covering data, the
marker `Z`, the numeric window bounds, and the per-term complement bound `hcb`,
assemble the full tower decomposition (with explicit error bound `9*Ccb+19`).
-/
lemma prop_decomp_core {t : ℕ} (ht : 1 ≤ t) {υ δ η : ℝ}
    (hυ : 0 < υ) (hδ : 0 < δ) (hη : 0 < η)
    {M₀ ℓ D : ℕ} {μ : Measure Cfg} [IsProbabilityMeasure μ] (hμ : ApproxInvMeasure M₀ η μ)
    {Ccb : ℝ} (hCcb : 0 < Ccb)
    {Z Ξ : Set Cfg} (hZdef : Defined D Z) (hΞdef : Defined D Ξ)
    (hℓD : ℓ ≤ D) (hbnd1 : 2 * D + 6 * t + 1 ≤ M₀)
    (hbnd3 : D + 30 * t ≤ M₀)
    (hZfindep : FIndep t Z)
    (hZsat : Ξ ⊆ ⋃ j ∈ Finset.Icc (-(t:ℤ)) (t:ℤ), (L ^ j) '' Z)
    {E : Set Cfg} {ι₁ : Type} [Fintype ι₁] {base₁ : ι₁ → Set Cfg} {height₁ : ι₁ → ℕ}
    (hEdef : Defined ℓ E) (hEμ : (μ E).toReal < υ)
    (hTB₁ : ∀ τ, IsTowerBase (height₁ τ) (base₁ τ))
    (hclosed₁ : ∀ τ, DeltaClosed μ δ (height₁ τ) (base₁ τ))
    (hheight₁ : ∀ τ, height₁ τ ≤ t)
    (hfloordef₁ : ∀ τ i, i < height₁ τ → Defined D (towerFloor (base₁ τ) i))
    (hPS₁ : ∀ τ, ProjSingleton t (base₁ τ))
    (hdisj₁ : ∀ τ τ' i i', i < height₁ τ → i' < height₁ τ' → ¬ (τ = τ' ∧ i = i') →
      Disjoint (towerFloor (base₁ τ) i) (towerFloor (base₁ τ') i'))
    (hEdisj₁ : ∀ τ i, i < height₁ τ → Disjoint E (towerFloor (base₁ τ) i))
    (hcompl : E ∪ (⋃ τ : ι₁, ⋃ i ∈ Finset.range (height₁ τ), towerFloor (base₁ τ) i)
        = Ξᶜ)
    (hcb : ∀ i : ℤ, i ∈ Finset.Icc (-(t:ℤ)) (t:ℤ) →
        (μ (((L ^ i) '' Z) \ Ξ)).toReal ≤ Ccb * ((t:ℝ)^4*η + (t:ℝ)^3*δ + υ)) :
    ∃ (e : Set Cfg), Defined M₀ e ∧
      (μ e).toReal ≤ (9 * Ccb + 19) * (t : ℝ) ^ 6 * (υ + δ + η) ∧
      ∃ (ι : Type) (_ : Fintype ι) (base : ι → Set Cfg) (height : ι → ℕ),
        IsTowerPartition e base height ∧
        (∀ τ : ι, ∀ i, i < height τ → Defined M₀ (towerFloor (base τ) i)) ∧
        (∀ τ : ι,
          (height τ < t ∧ DeltaClosed μ δ (height τ) (base τ)) ∨
          (t ≤ height τ ∧ height τ < 6 * t + 1)) ∧
        (∀ τ : ι, ProjSingleton (height τ) (base τ)) := by
  refine' ⟨ _, _, _, _ ⟩;
  exact E ∪ ( Ξ \ KRorbit ( Wset Z Ξ t ) ( 2 * t ) );
  · refine' defined_union _ _;
    · exact Defined.mono ( by linarith ) hEdef;
    · refine' defined_diff _ _;
      · exact hΞdef.mono ( by omega );
      · refine' Defined.mono _ _;
        exact D + D + 2 * t + 2 * t;
        · linarith;
        · convert KRorbit_defined _ using 1;
          exact Wset_defined hZdef hΞdef;
  · refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_union_le _ _ ) _;
    · exact ne_of_lt ( ENNReal.add_lt_top.mpr ⟨ MeasureTheory.measure_lt_top _ _, MeasureTheory.measure_lt_top _ _ ⟩ );
    · rw [ ENNReal.toReal_add ];
      · refine' le_trans ( add_le_add hEμ.le ( escape_measure_bound ht hυ hδ hη hμ hZdef hΞdef hbnd3 hCcb hZsat hcb ) ) _;
        nlinarith [ show ( t : ℝ ) ^ 6 ≥ 1 by exact one_le_pow₀ ( by norm_cast ), show ( t : ℝ ) ^ 6 * υ ≥ υ by exact le_mul_of_one_le_left hυ.le ( one_le_pow₀ ( by norm_cast ) ), show ( t : ℝ ) ^ 6 * δ ≥ δ by exact le_mul_of_one_le_left hδ.le ( one_le_pow₀ ( by norm_cast ) ), show ( t : ℝ ) ^ 6 * η ≥ η by exact le_mul_of_one_le_left hη.le ( one_le_pow₀ ( by norm_cast ) ) ];
      · exact MeasureTheory.measure_ne_top _ _;
      · exact MeasureTheory.measure_ne_top _ _;
  · refine' ⟨ ι₁ ⊕ AperIdx t, inferInstance, Sum.elim base₁ ( aperBaseR ( Wset Z Ξ t ) t ), Sum.elim height₁ ( heightR t ), _, _, _, _ ⟩;
    · apply isTowerPartition_sum;
      any_goals tauto;
      · exact fun τ => aperR_isTowerBase _ t τ;
      · apply aperR_disjoint;
      · intro τ₁ τ₂ i i' hi hi'
        have h_floor₁ : towerFloor (base₁ τ₁) i ⊆ E ∪ ⋃ τ, ⋃ i ∈ Finset.range (height₁ τ), towerFloor (base₁ τ) i := by
          exact Set.subset_union_of_subset_right ( Set.subset_iUnion₂_of_subset τ₁ i ( by aesop ) ) _
        have h_floor₂ : towerFloor (aperBaseR (Wset Z Ξ t) t τ₂) i' ⊆ KRorbit (Wset Z Ξ t) (2 * t) := by
          rw [ ← aperR_cover ];
          exact Set.subset_iUnion₂_of_subset τ₂ i' ( Set.subset_iUnion_of_subset ( Finset.mem_range.mpr hi' ) ( Set.Subset.refl _ ) );
        refine' Set.disjoint_left.mpr _;
        intro x hx₁ hx₂
        have hx1' := h_floor₁ hx₁
        have hx2' := KRorbit_subset (h_floor₂ hx₂)
        rw [hcompl] at hx1'
        exact hx1' hx2';
      · convert tower_cover_eq _ _ _;
        · convert aperR_cover ( Wset Z Ξ t ) t |> Eq.symm using 1;
        · exact hcompl;
        · simp_all +decide [ Set.disjoint_left ];
        · exact aperR_cover _ _ ▸ KRorbit_subset;
    · intro τ i hi;
      rcases τ with ( τ | τ );
      · exact ( hfloordef₁ τ i hi ).mono ( by linarith );
      · refine' Defined.mono _ _;
        exact D + D + 2 * t + 2 * ( 2 * t ) + 1;
        · linarith;
        · convert aperR_floor_defined ( Wset_defined hZdef hΞdef ) τ i hi using 1;
    · rintro ( τ | τ ) <;> simp +decide [ * ];
      · grind;
      · refine' Classical.or_iff_not_imp_left.2 fun h => ⟨ _, _ ⟩;
        · exact le_of_not_gt fun h' => h ⟨ h', by
            rw [ aperBaseR_empty_of_lt ( Wset_fIndep hZfindep ) τ h' ] ; unfold DeltaClosed ; norm_num ⟩;
        · exact Nat.succ_le_of_lt ( lt_of_lt_of_le ( Fin.is_lt _ ) ( by linarith ) );
    · rintro ( τ | τ ) <;> [ exact ProjSingleton.mono_window ( hheight₁ τ ) ( hPS₁ τ ) ; exact aperR_projSingleton _ _ _ ]

/-- **Proposition (Tower decomposition, `prop:decomp`).**

See `TowerDecomp.lean` for the statement's docstring and faithfulness note. -/
theorem prop_decomp :
    ∃ (Cerr : ℝ) (winBound : ℕ → ℝ → ℝ → ℝ), 0 < Cerr ∧
      ∀ (t : ℕ) (υ δ η : ℝ), 1 ≤ t → 0 < υ → υ ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
        0 < η → η ≤ 1 / 2 →
        ∀ (M₀ : ℕ), winBound t υ δ ≤ (M₀ : ℝ) →
          ∀ (μ : Measure Cfg) [IsProbabilityMeasure μ], ApproxInvMeasure M₀ η μ →
            ∃ (e : Set Cfg), Defined M₀ e ∧
              (μ e).toReal ≤ Cerr * (t : ℝ) ^ 6 * (υ + δ + η) ∧
              ∃ (ι : Type) (_ : Fintype ι) (base : ι → Set Cfg) (height : ι → ℕ),
                IsTowerPartition e base height ∧
                (∀ τ : ι, ∀ i, i < height τ →
                  Defined M₀ (towerFloor (base τ) i)) ∧
                (∀ τ : ι,
                  (height τ < t ∧ DeltaClosed μ δ (height τ) (base τ)) ∨
                  (t ≤ height τ ∧ height τ < 6 * t + 1)) ∧
                (∀ τ : ι, ProjSingleton (height τ) (base τ)) := by
  classical
  obtain ⟨Ccb, hCcb, hCB⟩ := complement_bound
  obtain ⟨covℓ, covDef, hCov⟩ := covering_per_seq
  obtain ⟨mDef, hMark⟩ := marker_lemma
  refine ⟨9 * Ccb + 19,
    fun t υ δ =>
      ((2 * t * ((⌈covℓ t υ δ⌉₊ + covDef t ⌈covℓ t υ δ⌉₊)
            + mDef t ⌈covℓ t υ δ⌉₊ (⌈covℓ t υ δ⌉₊ + covDef t ⌈covℓ t υ δ⌉₊))
        + 6 * ((⌈covℓ t υ δ⌉₊ + covDef t ⌈covℓ t υ δ⌉₊)
            + mDef t ⌈covℓ t υ δ⌉₊ (⌈covℓ t υ δ⌉₊ + covDef t ⌈covℓ t υ δ⌉₊))
        + 31 * t + 1 : ℕ) : ℝ),
    by positivity, ?_⟩
  intro t υ δ η ht hυ hυ2 hδ hδ2 hη hη2 M₀ hM₀ μ _inst hμ
  simp only [] at hM₀
  set ℓ := ⌈covℓ t υ δ⌉₊ with hℓdef
  -- `K` bounds the complexity of the periodic covering data (error set `E` and
  -- tower floors); `Ξ_aper := (E ∪ ⋃ floors)ᶜ` is then `K`-defined.
  set K := ℓ + covDef t ℓ with hKdef
  set D := K + mDef t ℓ K with hDdef
  have hM : 2 * t * D + 6 * D + 31 * t + 1 ≤ M₀ := by exact_mod_cast hM₀
  have hℓD : ℓ ≤ D := by omega
  have hmD : mDef t ℓ K ≤ D := by omega
  have hcD : covDef t ℓ ≤ D := by omega
  have hKD : K ≤ D := by omega
  have hbnd1 : 2 * D + 6 * t + 1 ≤ M₀ := by omega
  have hbnd2 : 2 * t * D ≤ M₀ := by omega
  have hbnd3 : D + 30 * t ≤ M₀ := by omega
  obtain ⟨E, ι₁, fι₁, base₁, height₁, hEdef, hEμ, hTB₁, hclosed₁, hheight₁,
    hbasedef₁, hfloordef₁, hPS₁, hdisj₁, hEdisj₁, hcover₁⟩ :=
    hCov t υ δ ht hυ hυ2 hδ hδ2 ℓ (by exact_mod_cast Nat.le_ceil _) μ
  -- The aperiodic clopen target `Ξ_aper` is the complement of the periodic
  -- covering `E ∪ ⋃ floors`.  Because the covering is only an inclusion
  -- `X_per^ℓ(t) ⊆ E ∪ ⋃ floors` (the faithful `covering_per_seq`), this set is a
  -- *subset* of `X_aper^ℓ(t)`, and the aperiodic towers built inside it are
  -- automatically (exactly) disjoint from the periodic floors and `E`.
  set Ξ : Set Cfg :=
      (E ∪ ⋃ τ : ι₁, ⋃ i ∈ Finset.range (height₁ τ), towerFloor (base₁ τ) i)ᶜ
    with hΞdef_eq
  -- `Ξ` is `K`-defined (hence `D`-defined).
  have hEK : Defined K E := hEdef.mono (by omega)
  have hUdef : Defined K (⋃ τ : ι₁, ⋃ i ∈ Finset.range (height₁ τ),
      towerFloor (base₁ τ) i) :=
    defined_iUnion (fun τ => defined_biUnion_finset _
      (fun i hi => (hfloordef₁ τ i (Finset.mem_range.mp hi)).mono (by omega)))
  have hΞdefK : Defined K Ξ := by
    rw [hΞdef_eq]; exact defined_compl (defined_union hEK hUdef)
  -- `Ξ ⊆ X_aper^ℓ(t)`, from `X_per^ℓ(t) ⊆ E ∪ ⋃ floors`.
  have hΞsub : Ξ ⊆ Xaperl t ℓ := by
    intro x hx
    rw [hΞdef_eq] at hx
    by_contra hxa
    exact hx (hcover₁ hxa)
  -- `E ∪ ⋃ floors = Ξᶜ` (definitional, used to assemble the exact partition).
  have hcompl : E ∪ (⋃ τ : ι₁, ⋃ i ∈ Finset.range (height₁ τ),
      towerFloor (base₁ τ) i) = Ξᶜ := by
    rw [hΞdef_eq, compl_compl]
  -- build the marker for `Ξ` (not for all of `X_aper^ℓ(t)`): this forces
  -- `Z ⊆ Ξ`, so `Z` avoids `E` and every periodic floor.
  obtain ⟨Z, hZmeas, hZdef, hZsub, hZfindep, hZsat⟩ :=
    hMark t ℓ K Ξ hΞdefK hΞsub
  -- the marker is (exactly) disjoint from each periodic floor, since `Z ⊆ Ξ`.
  have hZdisj : ∀ τ i, i < height₁ τ → Disjoint Z (towerFloor (base₁ τ) i) := by
    intro τ i hi
    rw [Set.disjoint_left]
    intro x hxZ hxF
    have hxΞ := hZsub hxZ
    rw [hΞdef_eq] at hxΞ
    exact hxΞ (Or.inr (Set.mem_iUnion.2
      ⟨τ, Set.mem_iUnion₂.2 ⟨i, Finset.mem_range.2 hi, hxF⟩⟩))
  have h2tpos : (0 : ℝ) < 2 * (t : ℝ) := by positivity
  have hDdiv : (D : ℝ) ≤ (M₀ : ℝ) / (2 * t) := by
    rw [le_div_iff₀ h2tpos]
    have : ((2 * t * D : ℕ) : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hbnd2
    push_cast at this ⊢; nlinarith [this]
  -- per-term complement bound
  have hcb : ∀ i : ℤ, i ∈ Finset.Icc (-(t : ℤ)) (t : ℤ) →
      (μ (((L ^ i) '' Z) \ Ξ)).toReal ≤ Ccb * ((t : ℝ) ^ 4 * η + (t : ℝ) ^ 3 * δ + υ) := by
    intro i hi
    have hi2t : i ∈ Finset.Icc (-(2 * t : ℤ)) (2 * t : ℤ) := by
      rw [Finset.mem_Icc] at hi ⊢; omega
    have h02t : (0 : ℤ) ∈ Finset.Icc (-(2 * t : ℤ)) (2 * t : ℤ) := by
      rw [Finset.mem_Icc]; omega
    have h0img : (L ^ (0 : ℤ)) '' Ξ = Ξ := by
      rw [zpow_zero]; simp
    have hsub : ((L ^ i) '' Z) \ ((L ^ (0 : ℤ)) '' Ξ) ⊆
        E ∪ ⋃ τ : ι₁, ⋃ i' ∈ Finset.range (height₁ τ), towerFloor (base₁ τ) i' := by
      rw [h0img, hΞdef_eq]
      rintro x ⟨_, hxΞ⟩; exact not_not.mp hxΞ
    have key := hCB t υ δ η M₀ D μ Ξ Z E ι₁ fι₁ base₁ height₁ ht hυ hδ hη hμ
      (hΞdefK.mono hKD) (hZdef.mono hmD) hDdiv hbnd3
      (fun τ => le_trans (hheight₁ τ) (by omega))
      (fun τ i hi => (hfloordef₁ τ i hi).mono hcD) hclosed₁ hdisj₁ hEμ hZsub hZdisj
      i 0 hi2t h02t hsub
    rwa [h0img] at key
  exact prop_decomp_core ht hυ hδ hη hμ hCcb (hZdef.mono hmD) (hΞdefK.mono hKD)
    hℓD hbnd1 hbnd3
    hZfindep hZsat hEdef hEμ hTB₁ hclosed₁ hheight₁
    (fun τ i hi => (hfloordef₁ τ i hi).mono hcD) hPS₁ hdisj₁ hEdisj₁ hcompl hcb

end LamplighterStability.Dynamics