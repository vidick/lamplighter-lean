import RequestProject.Dynamics.MarkerGreedyAbstract

/-!
# One round of Linial colour reduction on the full shift

Given a colouring `key : Cfg → Fin C` of the configurations and a `2t`-cover-free
family `S : Fin C → Finset (Fin M)` (from `exists_coverFree`), one *local round*
of Linial's algorithm produces a new colouring `redCol : Cfg → Fin M` with the
following properties:

* `redCol x ∈ S (key x)` always (`redCol_mem_S`);
* if `key` is `F_t`-proper at `x` (all `≤ 2t` neighbours have a different colour),
  then `redCol x` avoids `S (key (L^i x))` for every neighbour `i`
  (`redCol_avoid`); hence
* `redCol` is again `F_t`-proper wherever `key` is (`redCol_proper`), with **no
  shrinkage of the proper region** (the choice always lands in `S (key x)`, so the
  neighbour only needs `key`-properness at the *centre*); and
* `redCol` is window-`(W+t)`-defined whenever `key` is window-`W`-defined
  (`redCol_defined`), and uses only `M` colours.

Iterating this twice starting from the `π_ℓ`-pattern colouring (`2^{2ℓ+1}`
colours) brings the colour count down to a polynomial in `t` and `log ℓ`, after
which the greedy marker of `MarkerGreedyAbstract.lean` produces a marker with a
*polynomial* definability window — the polynomial marker lemma `prop:marker`.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators

variable {C M : ℕ}

/-- The multiset of neighbour colours of `x` under `key` (a `Finset (Fin C)` of
size `≤ 2t`). -/
def nbCol (t : ℕ) (key : Cfg → Fin C) (x : Cfg) : Finset (Fin C) :=
  ((Finset.Icc (-(t : ℤ)) (t : ℤ)).erase 0).image (fun i => key ((L ^ i) x))

/-- The candidate set the reduced colour is chosen from: `S (key x)` with the
neighbour colours' sets removed if that leaves something, else all of
`S (key x)`. -/
def redFinset (t : ℕ) (S : Fin C → Finset (Fin M)) (key : Cfg → Fin C) (x : Cfg) :
    Finset (Fin M) :=
  if (S (key x) \ (nbCol t key x).biUnion S).Nonempty
  then S (key x) \ (nbCol t key x).biUnion S
  else S (key x)

lemma redFinset_subset (t : ℕ) (S : Fin C → Finset (Fin M)) (key : Cfg → Fin C) (x : Cfg) :
    redFinset t S key x ⊆ S (key x) := by
  unfold redFinset
  split <;> [exact Finset.sdiff_subset; exact subset_rfl]

lemma redFinset_nonempty (t : ℕ) (S : Fin C → Finset (Fin M))
    (hSne : ∀ c, (S c).Nonempty) (key : Cfg → Fin C) (x : Cfg) :
    (redFinset t S key x).Nonempty := by
  unfold redFinset
  split_ifs with h
  · exact h
  · exact hSne (key x)

/-- The reduced colour: the minimal element of `redFinset`. -/
noncomputable def redCol (t : ℕ) (S : Fin C → Finset (Fin M))
    (hSne : ∀ c, (S c).Nonempty) (key : Cfg → Fin C) (x : Cfg) : Fin M :=
  (redFinset t S key x).min' (redFinset_nonempty t S hSne key x)

lemma redCol_mem_S (t : ℕ) (S : Fin C → Finset (Fin M))
    (hSne : ∀ c, (S c).Nonempty) (key : Cfg → Fin C) (x : Cfg) :
    redCol t S hSne key x ∈ S (key x) :=
  redFinset_subset t S key x ((redFinset t S key x).min'_mem _)

/-
`nbCol` has at most `2t` elements.
-/
lemma nbCol_card_le (t : ℕ) (key : Cfg → Fin C) (x : Cfg) :
    (nbCol t key x).card ≤ 2 * t := by
  refine' le_trans ( Finset.card_image_le ) _;
  rw [ Finset.card_erase_of_mem ] <;> norm_num [ two_mul ];
  linarith

/-
If `key` is `F_t`-proper at `x` (every neighbour differs in colour), the
reduced colour avoids the neighbour colour classes.
-/
lemma redCol_avoid (t : ℕ) (S : Fin C → Finset (Fin M))
    (hSne : ∀ c, (S c).Nonempty) (key : Cfg → Fin C)
    (hcf : ∀ (i : Fin C) (J : Finset (Fin C)), i ∉ J → J.card ≤ 2 * t →
      (S i \ J.biUnion S).Nonempty)
    {x : Cfg}
    (hx : ∀ i : ℤ, i ∈ Finset.Icc (-(t : ℤ)) (t : ℤ) → i ≠ 0 → key ((L ^ i) x) ≠ key x)
    {i : ℤ} (hi : i ∈ Finset.Icc (-(t : ℤ)) (t : ℤ)) (hi0 : i ≠ 0) :
    redCol t S hSne key x ∉ S (key ((L ^ i) x)) := by
  -- Apply the hypothesis `hcf` with `i = key x` and `J = nbCol t key x`.
  have h_redFinset : (S (key x) \ (nbCol t key x).biUnion S).Nonempty := by
    apply hcf;
    · unfold nbCol; aesop;
    · exact nbCol_card_le t key x
  unfold redCol redFinset;
  simp_all +decide [ Finset.min' ];
  exact fun h => Finset.notMem_sdiff_of_mem_right ( Finset.mem_biUnion.mpr ⟨ _, Finset.mem_image.mpr ⟨ i, Finset.mem_erase_of_ne_of_mem hi0 ( Finset.mem_Icc.mpr hi ), rfl ⟩, h ⟩ ) ( Finset.min'_mem _ _ )

/-- **Properness is preserved.**  Wherever `key` is `F_t`-proper, so is `redCol`
(for the centre point; the neighbour need not be in the proper region). -/
lemma redCol_proper (t : ℕ) (S : Fin C → Finset (Fin M))
    (hSne : ∀ c, (S c).Nonempty) (key : Cfg → Fin C)
    (hcf : ∀ (i : Fin C) (J : Finset (Fin C)), i ∉ J → J.card ≤ 2 * t →
      (S i \ J.biUnion S).Nonempty)
    {x : Cfg}
    (hx : ∀ i : ℤ, i ∈ Finset.Icc (-(t : ℤ)) (t : ℤ) → i ≠ 0 → key ((L ^ i) x) ≠ key x)
    {i : ℤ} (hi : i ∈ Finset.Icc (-(t : ℤ)) (t : ℤ)) (hi0 : i ≠ 0) :
    redCol t S hSne key ((L ^ i) x) ≠ redCol t S hSne key x := by
  intro heq
  have hmem : redCol t S hSne key ((L ^ i) x) ∈ S (key ((L ^ i) x)) :=
    redCol_mem_S t S hSne key ((L ^ i) x)
  rw [heq] at hmem
  exact redCol_avoid t S hSne key hcf hx hi hi0 hmem

/-
**Window definability is preserved up to `+t`.**
-/
lemma redCol_defined (t : ℕ) (S : Fin C → Finset (Fin M))
    (hSne : ∀ c, (S c).Nonempty) (key : Cfg → Fin C) {W : ℕ}
    (hkeydef : ∀ x y : Cfg, proj W x = proj W y → key x = key y)
    {x y : Cfg} (hxy : proj (W + t) x = proj (W + t) y) :
    redCol t S hSne key x = redCol t S hSne key y := by
  have h_proj_eq : ∀ i : ℤ, i ∈ Finset.Icc (-(t : ℤ)) (t : ℤ) → proj W ((L ^ i) x) = proj W ((L ^ i) y) := by
    intro i hi;
    apply proj_zpow_eq_of_proj_eq hxy;
    cases abs_cases i <;> push_cast <;> linarith [ Finset.mem_Icc.mp hi ];
  have h_key_eq : key x = key y := by
    exact hkeydef x y ( proj_mono ( by linarith ) hxy )
  have h_nbCol_eq : nbCol t key x = nbCol t key y := by
    ext; simp only [nbCol, Finset.mem_image];
    grind +qlia
  simp only [redCol]
  congr 1
  unfold redFinset
  rw [h_key_eq, h_nbCol_eq]

/-
The number of `ℓ`-window patterns is `2^{2ℓ+1}`.
-/
lemma card_Win_fun (ℓ : ℕ) : Fintype.card (Win ℓ → Bool) = 2 ^ (2 * ℓ + 1) := by
  erw [ Fintype.card_pi ] ; simp +decide;
  ring_nf; omega

/-- The explicit polynomial marker-window function returned by `marker_lemma_poly`
(`prop:marker`): `markerDefPoly t ℓ K = max K (ℓ+2t) + 4(2t+1)²(log₂(4(2t+1)²(2ℓ+3)²)+2)²·t`. -/
def markerDefPoly (t ℓ K : ℕ) : ℕ :=
  max K (ℓ + 2 * t) +
    (4 * (2 * t + 1) ^ 2 * (Nat.log 2 (4 * (2 * t + 1) ^ 2 * (2 * ℓ + 3) ^ 2) + 2) ^ 2) * t

theorem marker_lemma_poly_explicit :
    ∀ (t ℓ K : ℕ) (Ξ : Set Cfg), Defined K Ξ → Ξ ⊆ Xaperl t ℓ →
      ∃ Z : Set Cfg, MeasurableSet Z ∧ Defined (markerDefPoly t ℓ K) Z ∧
        IsMarker t Z Ξ := by
  classical
  unfold markerDefPoly
  intro t ℓ K Ξ hΞdef hΞsub
  -- The initial `π_ℓ`-pattern colouring into `Fin C0`, `C0 = 2^{2ℓ+1}` colours.
  set C0 := Fintype.card (Win ℓ → Bool) with hC0
  set key0 : Cfg → Fin C0 := fun x => (Fintype.equivFin (Win ℓ → Bool)) (proj ℓ x) with hkey0
  have hkey0_def : ∀ x y : Cfg, proj ℓ x = proj ℓ y → key0 x = key0 y := by
    intro x y h; simp only [hkey0]; rw [h]
  have hkey0_proper : ∀ x ∈ Xaperl t ℓ, ∀ i : ℤ, i ∈ Finset.Icc (-(t : ℤ)) (t : ℤ) → i ≠ 0 →
      key0 ((L ^ i) x) ≠ key0 x := by
    intro x hx i hi hi0 heq
    have hpe : proj ℓ ((L ^ i) x) = proj ℓ x := (Fintype.equivFin (Win ℓ → Bool)).injective heq
    exact colorKey_proper hx hi hi0 (colorKey_eq_of_proj_eq hpe)
  -- Round 1.
  obtain ⟨M1, S1, hM1card, hS1cf⟩ := exists_coverFree_fin C0 (2 * t)
  have hS1ne : ∀ c, (S1 c).Nonempty := fun c => by
    simpa using hS1cf c ∅ (Finset.notMem_empty c) (by simp)
  set key1 : Cfg → Fin M1 := redCol t S1 hS1ne key0 with hkey1
  have hkey1_def : ∀ x y : Cfg, proj (ℓ + t) x = proj (ℓ + t) y → key1 x = key1 y :=
    fun x y hxy => redCol_defined t S1 hS1ne key0 hkey0_def hxy
  have hkey1_proper : ∀ x ∈ Xaperl t ℓ, ∀ i : ℤ, i ∈ Finset.Icc (-(t : ℤ)) (t : ℤ) → i ≠ 0 →
      key1 ((L ^ i) x) ≠ key1 x :=
    fun x hx i hi hi0 =>
      redCol_proper t S1 hS1ne key0 hS1cf (fun j hj hj0 => hkey0_proper x hx j hj hj0) hi hi0
  -- Round 2.
  obtain ⟨M2, S2, hM2card, hS2cf⟩ := exists_coverFree_fin M1 (2 * t)
  have hS2ne : ∀ c, (S2 c).Nonempty := fun c => by
    simpa using hS2cf c ∅ (Finset.notMem_empty c) (by simp)
  set key2 : Cfg → Fin M2 := redCol t S2 hS2ne key1 with hkey2
  have hkey2_def : ∀ x y : Cfg, proj (ℓ + t + t) x = proj (ℓ + t + t) y → key2 x = key2 y :=
    fun x y hxy => redCol_defined t S2 hS2ne key1 hkey1_def hxy
  have hkey2_proper : ∀ x ∈ Xaperl t ℓ, ∀ i : ℤ, i ∈ Finset.Icc (-(t : ℤ)) (t : ℤ) → i ≠ 0 →
      key2 ((L ^ i) x) ≠ key2 x :=
    fun x hx i hi hi0 =>
      redCol_proper t S2 hS2ne key1 hS2cf (fun j hj hj0 => hkey1_proper x hx j hj hj0) hi hi0
  -- Greedy marker from the reduced colouring `key2` (with `M2` colours).
  set W := max K (ℓ + 2 * t) with hW
  obtain ⟨Z, hZmeas, hZdef, hZmark⟩ :=
    markerOfKey (t := t) (W := W) (C := M2) (key := fun x => (key2 x).val) (Ξ := Ξ)
      (hΞdef.mono (le_max_left _ _))
      (fun x y hxy => by
        have hk : key2 x = key2 y :=
          hkey2_def x y (proj_mono (by omega : ℓ + t + t ≤ W) hxy)
        exact congrArg Fin.val hk)
      (fun x => (key2 x).is_lt)
      (fun x hx i hi hi0 _ => by
        have hne : key2 ((L ^ i) x) ≠ key2 x := hkey2_proper x (hΞsub hx) i hi hi0
        exact fun hval => hne (Fin.val_injective hval))
  refine ⟨Z, hZmeas, ?_, hZmark⟩
  -- Bound the window: `M2 ≤ Mbound2` via the cover-free cardinality bounds.
  have hM1le : M1 ≤ 4 * (2 * t + 1) ^ 2 * (2 * ℓ + 3) ^ 2 := by
    have hlog : Nat.log 2 C0 = 2 * ℓ + 1 := by
      rw [hC0, card_Win_fun]; exact Nat.log_pow (by norm_num) _
    calc M1 ≤ 4 * (2 * t + 1) ^ 2 * (Nat.log 2 C0 + 2) ^ 2 := hM1card
      _ = 4 * (2 * t + 1) ^ 2 * (2 * ℓ + 3) ^ 2 := by rw [hlog]
  have hM2le : M2 ≤ 4 * (2 * t + 1) ^ 2 *
      (Nat.log 2 (4 * (2 * t + 1) ^ 2 * (2 * ℓ + 3) ^ 2) + 2) ^ 2 := by
    refine le_trans hM2card ?_
    have hlogle : Nat.log 2 M1 ≤ Nat.log 2 (4 * (2 * t + 1) ^ 2 * (2 * ℓ + 3) ^ 2) :=
      Nat.log_mono_right hM1le
    have h2 : Nat.log 2 M1 + 2 ≤ Nat.log 2 (4 * (2 * t + 1) ^ 2 * (2 * ℓ + 3) ^ 2) + 2 := by
      omega
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 2)
  refine hZdef.mono ?_
  have hfin : W + M2 * t ≤ max K (ℓ + 2 * t) +
      (4 * (2 * t + 1) ^ 2 * (Nat.log 2 (4 * (2 * t + 1) ^ 2 * (2 * ℓ + 3) ^ 2) + 2) ^ 2) * t := by
    rw [hW]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hM2le) _
  exact hfin

/-- **Polynomial marker lemma (`prop:marker`), existential form.**  Packages
`marker_lemma_poly_explicit` with the explicit window `markerDefPoly`. -/
theorem marker_lemma_poly :
    ∃ markerDef : ℕ → ℕ → ℕ → ℕ,
      ∀ (t ℓ K : ℕ) (Ξ : Set Cfg), Defined K Ξ → Ξ ⊆ Xaperl t ℓ →
        ∃ Z : Set Cfg, MeasurableSet Z ∧ Defined (markerDef t ℓ K) Z ∧
          IsMarker t Z Ξ :=
  ⟨markerDefPoly, marker_lemma_poly_explicit⟩

end LamplighterStability.Dynamics