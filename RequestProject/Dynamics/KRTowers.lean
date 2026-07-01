import RequestProject.Dynamics.KakutaniRokhlin

/-!
# Kakutani–Rokhlin towers: capped first-return covering

This file completes the combinatorial core of the "markers → towers"
construction (`sec:mtot` of the paper).  Given a set `W` (a translate of a subset
of the marker set `Z`, so `F_t`-independent), the first-return function
`g : W → {1,…,2t+1}`, capped at `2t+1`, partitions `W` into bases `W_j`
(`aperBase W N j` here, with `N = 2t`); the resulting clopen towers
`Tow(W_j, j)` tile the orbit segment `⋃_{k=0}^{2t} L^k W`.

The key facts proved here are purely combinatorial (no measure theory):

* `aperBase_subset`, `aperBase_clearance` — each base is `⊆ W` and has no return
  to `W` below its height;
* `aperBase_pairwise` — distinct bases are disjoint (`g` is a function);
* `aper_floors_disjoint` — distinct floors of the whole family are disjoint;
* `aper_isTowerBase` — each base is a genuine tower base of its height;
* `aper_floors_cover` — the floors tile `⋃_{k=0}^{N} L^k W` exactly.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators
open scoped Classical

/-- **Capped first-return base.**  The set of `x ∈ Z` with *no* return to `Z`
within the first `N` steps (`g(x) = N+1`, the cap). -/
def KRcap (Z : Set Cfg) (N : ℕ) : Set Cfg :=
  {x | x ∈ Z ∧ ∀ i : ℕ, 0 < i → i ≤ N → (L ^ (i : ℤ)) x ∉ Z}

/-- **Aperiodic tower base of height `j`** (`N = 2t`).  For `j ≤ N` this is the
exact first-return base `KRbase W j`; for `j = N+1` it is the capped base
`KRcap W N`. -/
def aperBase (W : Set Cfg) (N j : ℕ) : Set Cfg :=
  if j ≤ N then KRbase W j else KRcap W N

lemma aperBase_subset (W : Set Cfg) (N j : ℕ) : aperBase W N j ⊆ W := by
  unfold aperBase
  split
  · exact KRbase_subset W j
  · exact fun _ hx => hx.1

/-
**Clearance.**  An element of the height-`j` base has no return to `W` at any
positive level strictly below `j`.
-/
lemma aperBase_clearance {W : Set Cfg} {N j : ℕ} (hj : j ≤ N + 1)
    {x : Cfg} (hx : x ∈ aperBase W N j) {i : ℕ} (hi0 : 0 < i) (hij : i < j) :
    (L ^ (i : ℤ)) x ∉ W := by
  unfold aperBase at hx; split_ifs at hx <;> simp_all +decide [ KRbase, KRcap ] ;
  exact hx.2 i hi0 ( by linarith )

/-
**Bases are pairwise disjoint** (the first-return function is well defined).
-/
lemma aperBase_pairwise {W : Set Cfg} {N j j' : ℕ} (hj1 : 1 ≤ j) (hj1' : 1 ≤ j')
    (hj : j ≤ N + 1) (hj' : j' ≤ N + 1) (hne : j ≠ j') :
    Disjoint (aperBase W N j) (aperBase W N j') := by
  -- By definition of `aperBase`, we know that if `j ≤ N` and `j' ≤ N`, then `aperBase W N j` and `aperBase W N j'` are disjoint because they are defined using different values of `j`.
  apply Set.disjoint_left.mpr;
  intro x hx hx'; cases lt_or_gt_of_ne hne <;> simp_all +decide [ aperBase ] ;
  · split_ifs at hx hx' <;> simp_all +decide [ KRbase, KRcap ];
    · grind;
    · exact hx' j hj1 ( by linarith ) hx.1.2;
    · grind;
    · omega;
  · split_ifs at hx hx' <;> simp_all +decide [ KRbase, KRcap ];
    · exact hx.2.2 j' hj1' ( by linarith ) hx'.1;
    · linarith;
    · exact hx.2 j' hj1' ( by linarith ) hx'.1;
    · grind

/-
**Master floor-disjointness** for the capped aperiodic family.
-/
lemma aper_floors_disjoint {W : Set Cfg} {N j j' i i' : ℕ}
    (hj : j ≤ N + 1) (hj' : j' ≤ N + 1)
    (hi : i < j) (hi' : i' < j') (hne : ¬ (j = j' ∧ i = i')) :
    Disjoint (towerFloor (aperBase W N j) i) (towerFloor (aperBase W N j') i') := by
  apply Set.disjoint_left.mpr
  intro x hx1 hx2;
  obtain ⟨w, hw, rfl⟩ := hx1
  obtain ⟨w', hw', hx⟩ := hx2
  have h_eq : w' = (L ^ ((i - i' : ℤ)) : Equiv.Perm Cfg) w := by
    convert congr_arg ( fun x => ( L ^ ( -i' : ℤ ) ) x ) hx using 1;
    · simp +decide [ zpow_neg ];
    · grind +suggestions;
  by_cases h_cases : i ≥ i';
  · by_cases h_cases : i = i';
    · simp_all +decide [];
      exact aperBase_pairwise ( by linarith ) ( by linarith ) hj hj' hne |> fun h => h.le_bot ⟨ hw, hw' ⟩;
    · have h_contra : (L ^ ((i - i' : ℤ)) : Equiv.Perm Cfg) w ∈ W := by
        exact h_eq ▸ aperBase_subset _ _ _ hw';
      have := aperBase_clearance hj hw ( show 0 < i - i' from Nat.sub_pos_of_lt ( lt_of_le_of_ne ‹_› ( Ne.symm h_cases ) ) ) ( show i - i' < j from by omega ) ; simp_all +decide [] ;
  · have h_eq' : w = (L ^ ((i' - i : ℤ)) : Equiv.Perm Cfg) w' := by
      simp_all +decide [ zpow_sub ];
    have h_contradiction : (L ^ ((i' - i : ℤ)) : Equiv.Perm Cfg) w' ∈ W := by
      exact h_eq'.symm ▸ aperBase_subset _ _ _ hw;
    convert aperBase_clearance hj' hw' ( show 0 < i' - i from Nat.sub_pos_of_lt ( lt_of_not_ge h_cases ) ) ( show i' - i < j' from by omega ) using 1;
    grind

/-- Each aperiodic base is a genuine tower base of its height. -/
lemma aper_isTowerBase {W : Set Cfg} {N j : ℕ} (hj : j ≤ N + 1) :
    IsTowerBase j (aperBase W N j) := by
  intro i i' hi hi' hne
  exact aper_floors_disjoint hj hj hi hi' (by simp [hne])

/-- The orbit segment `⋃_{k=0}^{N} L^k W`. -/
def KRorbit (W : Set Cfg) (N : ℕ) : Set Cfg :=
  ⋃ k ∈ Finset.range (N + 1), (L ^ (k : ℤ)) '' W

/-- The union of all aperiodic floors (heights `1 … N+1`). -/
def aperFloors (W : Set Cfg) (N : ℕ) : Set Cfg :=
  ⋃ j ∈ Finset.Icc 1 (N + 1), ⋃ i ∈ Finset.range j, towerFloor (aperBase W N j) i

/-
**Exact covering.**  The aperiodic floors tile the orbit segment.
-/
lemma aper_floors_cover (W : Set Cfg) (N : ℕ) :
    aperFloors W N = KRorbit W N := by
  refine' Set.Subset.antisymm _ _;
  · unfold aperFloors KRorbit;
    simp +decide [ Set.subset_def, towerFloor ];
    intro x j hj₁ hj₂ i hi hx; use i;
    exact ⟨ by linarith, aperBase_subset _ _ _ hx ⟩;
  · -- We proceed by induction on $k$.
    have h_ind : ∀ k ≤ N, ∀ w ∈ W, (L ^ (k : ℤ)) w ∈ aperFloors W N := by
      intro k hk w hw
      induction' k using Nat.strong_induction_on with k ih generalizing w;
      by_cases h_case : ∃ j ∈ Finset.Icc 1 k, (L ^ (j : ℤ)) w ∈ W;
      · obtain ⟨j₀, hj₀⟩ : ∃ j₀ ∈ Finset.Icc 1 k, (L ^ (j₀ : ℤ)) w ∈ W ∧ ∀ j ∈ Finset.Icc 1 (k - 1), j < j₀ → (L ^ (j : ℤ)) w ∉ W := by
          simp +zetaDelta at *;
          exact ⟨ Nat.find h_case, Nat.find_spec h_case |>.1, Nat.find_spec h_case |>.2, by intros; exact fun h => Nat.find_min h_case ‹_› ⟨ ⟨ by linarith, by omega ⟩, h ⟩ ⟩;
        convert ih ( k - j₀ ) ( Nat.sub_lt ( by linarith [ Finset.mem_Icc.mp hj₀.1 ] ) ( by linarith [ Finset.mem_Icc.mp hj₀.1 ] ) ) ( Nat.sub_le_of_le_add <| by linarith ) ( ( L ^ ( j₀ : ℤ ) ) w ) hj₀.2.1 using 1;
        rw [ ← Equiv.Perm.mul_apply, ← zpow_add ] ; norm_num [ Nat.cast_sub ( show j₀ ≤ k from Finset.mem_Icc.mp hj₀.1 |>.2 ) ];
      · by_cases h_case2 : ∃ j ∈ Finset.Icc 1 N, (L ^ (j : ℤ)) w ∈ W;
        · obtain ⟨j₀, hj₀⟩ : ∃ j₀ ∈ Finset.Icc 1 N, (L ^ (j₀ : ℤ)) w ∈ W ∧ ∀ j ∈ Finset.Icc 1 N, (L ^ (j : ℤ)) w ∈ W → j₀ ≤ j := by
            exact ⟨ Nat.find h_case2, Nat.find_spec h_case2 |>.1, Nat.find_spec h_case2 |>.2, fun j hj hj' => Nat.find_min' h_case2 ⟨ hj, hj' ⟩ ⟩;
          have h_w_in_KRbase : w ∈ KRbase W j₀ := by
            simp_all +decide [ KRbase ];
            exact fun i hi₁ hi₂ hi₃ => not_lt_of_ge ( hj₀.2.2 i hi₁ ( by linarith ) hi₃ ) hi₂;
          have h_w_in_aperBase : w ∈ aperBase W N j₀ := by
            unfold aperBase; aesop;
          have h_k_lt_j₀ : k < j₀ := by
            grind;
          exact Set.mem_iUnion₂.mpr ⟨ j₀, Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Icc.mp hj₀.1 ], by linarith [ Finset.mem_Icc.mp hj₀.1 ] ⟩, Set.mem_iUnion₂.mpr ⟨ k, Finset.mem_range.mpr h_k_lt_j₀, Set.mem_image_of_mem _ h_w_in_aperBase ⟩ ⟩;
        · refine' Set.mem_iUnion₂.mpr ⟨ N + 1, _, _ ⟩ <;> norm_num;
          refine' ⟨ k, hk, _ ⟩ ; simp_all +decide [ aperBase ];
          exact ⟨ hw, fun i hi₁ hi₂ => h_case2 i hi₁ hi₂ ⟩;
    exact Set.iUnion₂_subset fun k hk => Set.image_subset_iff.mpr fun w hw => h_ind k ( Finset.mem_range_succ_iff.mp hk ) w hw

/-! ## Definability -/

/-
If `Z` is `D`-defined then the capped base `KRcap Z N` is `(D+N)`-defined.
-/
lemma KRcap_defined {D : ℕ} {Z : Set Cfg} (hZ : Defined D Z) (N : ℕ) :
    Defined (D + N) (KRcap Z N) := by
  intro x y hxy
  have h_shift : ∀ i : ℕ, i ≤ N → ((L ^ (i : ℤ)) x ∈ Z ↔ (L ^ (i : ℤ)) y ∈ Z) := by
    intro i hi
    have h_shift : ∀ n : Finset.Icc (-↑D : ℤ) ↑D, (L ^ (i : ℤ)) x n = (L ^ (i : ℤ)) y n := by
      intro n
      have h_shift : (L ^ (i : ℤ)) x n = x (n - i) ∧ (L ^ (i : ℤ)) y n = y (n - i) := by
        exact ⟨ L_zpow_apply _ _ _, L_zpow_apply _ _ _ ⟩;
      replace hxy := congr_fun hxy ⟨ n - i, by
        exact Finset.mem_Icc.mpr ⟨ by push_cast; linarith [ Finset.mem_Icc.mp n.2 ], by push_cast; linarith [ Finset.mem_Icc.mp n.2 ] ⟩ ⟩ ; aesop;
    exact hZ _ _ ( funext h_shift );
  constructor <;> intro h <;> have := h_shift 0 <;> simp_all +decide [ KRcap ]

/-
If `W` is `D`-defined then every aperiodic base `aperBase W N j`
(for `j ≤ N+1`) is `(D+N)`-defined.
-/
lemma aperBase_defined {D : ℕ} {W : Set Cfg} (hW : Defined D W) {N j : ℕ} :
    Defined (D + N) (aperBase W N j) := by
  by_cases h : j ≤ N;
  · unfold aperBase;
    rw [ if_pos h ];
    exact KRbase_defined hW j |> fun h => h.mono ( by linarith );
  · convert KRcap_defined hW N using 1;
    exact if_neg h

end LamplighterStability.Dynamics