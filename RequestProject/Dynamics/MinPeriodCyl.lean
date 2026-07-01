import RequestProject.Dynamics.MinPeriod

/-!
# Cylinder/period bridging lemmas (`lem:per_ext_properties` item (i))

This file connects the window-comparison predicate `WinPerEq` and the minimal
period `patPeriod` (from `MinPeriod.lean`) with the geometric notions of cylinder
sets and `F_j`-independence (`FIndep`) on the full shift.

The key bridge is `disjoint_cyl_shift_iff`: a window cylinder `⟦π_r(x)⟧` and its
`i`-shift are disjoint *iff* the window comparison `WinPerEq r x i` fails.  From
it we obtain `fIndep_cyl_iff_winPerEq` and, via the minimality of `patPeriod`,
item (i) of `lem:per_ext_properties`: `⟦π_r(x)⟧` is `F_{per(x)-1}`-independent
(`fIndep_cyl_patPeriod_sub_one`).
-/

namespace LamplighterStability.Dynamics

open scoped BigOperators
open scoped Classical

/-
**Bridge (`lem:per_ext_properties` (i), core).**  For `i ≥ 0`, the window
cylinder `⟦π_r(x)⟧` is disjoint from its `i`-shift exactly when the window
comparison `WinPerEq r x i` fails.
-/
lemma disjoint_cyl_shift_iff (r : ℕ) (x : Cfg) {i : ℤ} (hi : 0 ≤ i) :
    Disjoint (cyl r (proj r x)) ((L ^ i) '' (cyl r (proj r x))) ↔ ¬ WinPerEq r x i := by
  rw [ Set.disjoint_left ];
  constructor;
  · contrapose!;
    intro h;
    -- Let's choose any $a$ in the cylinder set $cyl r (proj r x)$.
    obtain ⟨a, ha⟩ : ∃ a : Cfg, a ∈ cyl r (proj r x) ∧ ∀ k : Win r, a (k.1 + i) = x k.1 := by
      use fun k => if k ≤ r then x k else x (k - i);
      constructor;
      · ext k; simp [proj];
        exact fun hk => False.elim <| hk.not_ge <| Finset.mem_Icc.mp k.2 |>.2;
      · intro k; split_ifs <;> simp_all +decide [ WinPerEq ] ;
        grind;
    refine' ⟨ a, ha.1, _ ⟩;
    use fun k => a (k + i);
    constructor;
    · ext k; aesop;
    · ext k; simp +decide [ L_zpow_apply ] ;
  · intro h a ha hb;
    obtain ⟨ b, hb, rfl ⟩ := hb;
    contrapose! h; simp_all +decide [ WinPerEq, cyl ] ;
    simp_all +decide [ funext_iff, proj ];
    intro k hk₁ hk₂; have := ha k ( by linarith ) ( by linarith ) ; have := hb ( k - i ) ( by linarith ) ( by linarith ) ; simp_all +decide [ L_zpow_apply ] ;

/-
Disjointness of a cylinder from its shift is symmetric under `i ↦ -i`.
-/
lemma disjoint_cyl_shift_neg (b : Set Cfg) (i : ℤ) :
    Disjoint b ((L ^ i) '' b) ↔ Disjoint b ((L ^ (-i)) '' b) := by
  simp +decide [ Set.disjoint_left ];
  grind +qlia

/-
**`F_j`-independence of a cylinder in terms of `WinPerEq`.**
-/
lemma fIndep_cyl_iff_winPerEq (r j : ℕ) (x : Cfg) :
    FIndep j (cyl r (proj r x)) ↔ ∀ i : ℕ, 1 ≤ i → i ≤ j → ¬ WinPerEq r x (i : ℤ) := by
  refine' ⟨ fun h i hi₁ hi₂ => _, fun h i hi₁ hi₂ => _ ⟩;
  · contrapose! h;
    exact fun H => absurd ( H i ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) ( by linarith ) ) ( by rw [ disjoint_cyl_shift_iff r x ( by linarith ) ] ; aesop );
  · by_cases hi₃ : 0 < i;
    · exact disjoint_cyl_shift_iff r x hi₃.le |>.2 ( h ( Int.toNat i ) ( by linarith [ Int.toNat_of_nonneg hi₃.le ] ) ( by linarith [ Int.toNat_of_nonneg hi₃.le, Finset.mem_Icc.mp hi₁ ] ) |> fun h => by simpa [ Int.toNat_of_nonneg hi₃.le ] using h );
    · convert disjoint_cyl_shift_neg _ _ |>.2 _ using 1;
      convert disjoint_cyl_shift_iff r x _ |>.2 ( h ( Int.toNat ( -i ) ) _ _ ) using 1;
      · norm_num [ Int.toNat_of_nonneg ( neg_nonneg.mpr ( le_of_not_gt hi₃ ) ) ];
      · exact Nat.cast_nonneg _;
      · grind;
      · linarith [ Finset.mem_Icc.mp hi₁, Int.toNat_of_nonneg ( by linarith [ Finset.mem_Icc.mp hi₁ ] : 0 ≤ -i ) ]

/-
**`lem:per_ext_properties` item (i).**  The window cylinder `⟦π_r(x)⟧` is
`F_{per(x)-1}`-independent.
-/
lemma fIndep_cyl_patPeriod_sub_one (r : ℕ) (x : Cfg) :
    FIndep (patPeriod r x - 1) (cyl r (proj r x)) := by
  rw [ fIndep_cyl_iff_winPerEq ];
  exact fun i hi₁ hi₂ => patPeriod_min r x hi₁ ( lt_of_le_of_lt hi₂ ( Nat.pred_lt ( ne_bot_of_gt ( patPeriod_pos r x ) ) ) )

end LamplighterStability.Dynamics