import RequestProject.Dynamics.PropDecompAssembly

/-!
# Part 1, step 1 — the Kakutani–Rokhlin markers→towers construction

Given a marker set `Z` (an `F_t`-independent set whose translates cover the
aperiodic part), the first-return / Kakutani–Rokhlin construction turns `Z` into
clopen towers of bounded height: for each height `j`, the base `KRbase Z j` is
the set of `z ∈ Z` whose *next* visit to `Z` (going up the tower via `L`) happens
exactly `j` steps later.  These towers tile the orbit segments between
consecutive `Z`-visits.

This file develops the combinatorial core of that construction (heights, base
definability, and the master floor-disjointness fact).  The measure-theoretic
covering/error estimate that ties it to the aperiodic part is supplied by
`complement_bound` (in `TowerDecompAssembly.lean`); the two are combined in the
`prop_decomp` assembly.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators

/-- **Kakutani–Rokhlin base of height `j`.**  The set of `z ∈ Z` whose first
return to `Z` under `L` (strictly above the ground floor) occurs exactly at
height `j`: `L^j z ∈ Z` while `L^i z ∉ Z` for every `0 < i < j`. -/
def KRbase (Z : Set Cfg) (j : ℕ) : Set Cfg :=
  {x | x ∈ Z ∧ (L ^ (j : ℤ)) x ∈ Z ∧ ∀ i : ℕ, 0 < i → i < j → (L ^ (i : ℤ)) x ∉ Z}

lemma KRbase_subset (Z : Set Cfg) (j : ℕ) : KRbase Z j ⊆ Z :=
  fun _ hx => hx.1

/-
An `F_t`-independent set has no return within the first `t` steps: if `z ∈ Z`
and `0 < i ≤ t` then `L^i z ∉ Z`.
-/
lemma FIndep.no_early_return {t : ℕ} {Z : Set Cfg} (hZ : FIndep t Z)
    {z : Cfg} (hz : z ∈ Z) {i : ℕ} (hi0 : 0 < i) (hit : i ≤ t) :
    (L ^ (i : ℤ)) z ∉ Z := by
  -- By definition of $FIndep$, we know that $Z$ is disjoint from its image under $L^i$ for any $i$ such that $0 < i \leq t$.
  have h_disjoint : Disjoint Z ((L ^ (i : ℤ)) '' Z) := by
    exact hZ i ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) ( by linarith );
  exact fun h => h_disjoint.le_bot ⟨ h, Set.mem_image_of_mem _ hz ⟩

/-
The Kakutani–Rokhlin base of height `j ≤ t` is empty (no early returns).
-/
lemma KRbase_eq_empty_of_le {t : ℕ} {Z : Set Cfg} (hZ : FIndep t Z)
    {j : ℕ} (hj0 : 0 < j) (hjt : j ≤ t) : KRbase Z j = ∅ := by
  ext x;
  simp +zetaDelta at *;
  exact fun hx => hZ.no_early_return hx.1 hj0 hjt hx.2.1

/-
If `Z` is `D`-defined then `KRbase Z j` is `(D + j)`-defined.
-/
lemma KRbase_defined {D : ℕ} {Z : Set Cfg} (hZ : Defined D Z) (j : ℕ) :
    Defined (D + j) (KRbase Z j) := by
  intro x y hxy
  simp [KRbase];
  -- Since $Z$ is $D$-defined, for any $i \leq j$, $(L^i x) \in Z$ if and only if $(L^i y) \in Z$.
  have h_shift : ∀ i : ℕ, i ≤ j → ((L ^ i) x ∈ Z ↔ (L ^ i) y ∈ Z) := by
    intro i hi
    have h_proj : proj D ((L ^ i) x) = proj D ((L ^ i) y) := by
      ext ⟨ n, hn ⟩ ; simp_all +decide [ proj ] ;
      simp_all +decide [ funext_iff, proj ];
      convert hxy ( n - i ) ( by linarith ) ( by linarith ) using 1;
      · convert L_zpow_apply i x n using 1;
      · convert L_zpow_apply i y n using 1;
    exact hZ _ _ h_proj;
  constructor <;> intro h <;> simp_all +decide [];
  · exact ⟨ by simpa using h_shift 0 bot_le |>.1 h.1.1, fun i hi₁ hi₂ => by simpa [ h_shift i hi₂.le ] using h.2.2 i hi₁ hi₂ ⟩;
  · exact ⟨ h_shift 0 bot_le |>.2 h.1.1, fun i hi₁ hi₂ => fun hi₃ => h.2.2 i hi₁ hi₂ <| h_shift i hi₂.le |>.1 hi₃ ⟩

/-
**Master floor-disjointness.**  Distinct floors of the Kakutani–Rokhlin
towers are disjoint: for heights `j, j'`, levels `i < j`, `i' < j'`, unless
`(j,i) = (j',i')`, the floors `L^i (KRbase Z j)` and `L^{i'} (KRbase Z j')` are
disjoint.  (The within-tower case `j = j'` gives `IsTowerBase`; the cross-tower
case `j ≠ j'` gives the partition disjointness.)
-/
lemma KRfloors_disjoint {Z : Set Cfg} {j j' i i' : ℕ}
    (hi : i < j) (hi' : i' < j') (hne : ¬ (j = j' ∧ i = i')) :
    Disjoint (towerFloor (KRbase Z j) i) (towerFloor (KRbase Z j') i') := by
  rw [ Set.disjoint_left ];
  intro x hx hx'; obtain ⟨ z, hz, rfl ⟩ := hx; obtain ⟨ z', hz', hx' ⟩ := hx'; simp_all +decide [] ;
  -- Applying `(L ^ (-(i' : ℤ)))` to both sides of `hx'`, we get `z' = (L ^ (i - i' : ℤ)) z`.
  have hz'_eq : z' = (L ^ (i - i' : ℤ)) z := by
    have hz'_eq : (L ^ (-i' : ℤ)) ((L ^ i') z') = (L ^ (-i' : ℤ)) ((L ^ i) z) := by
      rw [hx'];
    convert hz'_eq using 1 ; group;
    · norm_num [ zpow_neg, zpow_ofNat ];
    · rw [ ← Equiv.Perm.mul_apply, ← zpow_natCast, ← zpow_add ] ; ring;
  -- Consider two cases: $i \geq i'$ and $i < i'$.
  by_cases h_cases : i ≥ i';
  · cases lt_or_eq_of_le h_cases <;> simp_all +decide [ KRbase ];
    · exact hz.2.2 ( i - i' ) ( Nat.sub_pos_of_lt ‹_› ) ( Nat.lt_of_le_of_lt ( Nat.sub_le _ _ ) hi ) ( by simpa [ ← zpow_natCast, Nat.cast_sub ‹i' < i›.le ] using hz'.1.1 );
    · grind +suggestions;
  · -- Since $i < i'$, we have $i' - i > 0$. Let $d = i' - i$, then $0 < d < j'$.
    set d := i' - i with hd
    have hd_pos : 0 < d := by
      exact Nat.sub_pos_of_lt ( lt_of_not_ge h_cases )
    have hd_lt_j' : d < j' := by
      omega;
    -- Since $z' = (L ^ (-d : ℤ)) z$, we have $(L ^ d) z' = z$.
    have hLd_z' : (L ^ d : Cfg ≃ Cfg) z' = z := by
      simp_all +decide [ ← zpow_natCast ];
      rw [ ← Equiv.Perm.mul_apply, ← zpow_add ] ; norm_num [ h_cases.le ];
    have := hz'.2.2 d hd_pos hd_lt_j'; simp_all +decide [ KRbase ] ;


end LamplighterStability.Dynamics