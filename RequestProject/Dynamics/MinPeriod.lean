import RequestProject.Dynamics.PeriodicSets

/-!
# The minimal periodic extension (`def:min_period`, `lem:per_ext_properties`)

This file builds the *minimal periodic extension* machinery used in the proof of
`lem:covering_per_seq` (Section 6.1 of the paper).  Working directly with
configurations `x : Cfg` (their behaviour depends only on the window `F_r`), we
define:

* `WinPerEq r x j` : the window-comparison predicate
  `(L^j ⟦x⟧)|_{[-r+j, r]} = ⟦x⟧|_{[-r+j, r]}`, i.e. `x k = x (k-j)` for all
  `k ∈ [-r+j, r]` (paper's condition in `eq:def-period`);
* `patPeriod r x` : the minimal period of the window pattern `π_r(x)`, the least
  `j ∈ {1, …, 2r+1}` with `WinPerEq r x j` (it always exists since `j = 2r+1`
  makes the comparison range empty);
* `cfgExt r x` : the minimal periodic extension, the unique `patPeriod r x`-periodic
  configuration agreeing with `x` on `F_r`.

These are elementary but fiddly combinatorics; the deeper covering lemma builds on
them.
-/

namespace LamplighterStability.Dynamics

open scoped BigOperators
open scoped Classical

/-- Window-comparison predicate: `x k = x (k - j)` for all `k ∈ [-r+j, r]`.
This expresses `(L^j ⟦x⟧)|_{[-r+j, r]} = ⟦x⟧|_{[-r+j, r]}` (paper `eq:def-period`).
It depends only on `proj r x`. -/
def WinPerEq (r : ℕ) (x : Cfg) (j : ℤ) : Prop :=
  ∀ k : ℤ, -(r : ℤ) + j ≤ k → k ≤ (r : ℤ) → x k = x (k - j)

/-- The candidate periods in `{1, …, 2r+1}` satisfying the window comparison. -/
noncomputable def periodCandidates (r : ℕ) (x : Cfg) : Finset ℕ :=
  (Finset.Icc 1 (2 * r + 1)).filter (fun j => WinPerEq r x (j : ℤ))

/-
`j = 2r+1` is always a candidate: the comparison range `[-r+(2r+1), r] = [r+1, r]`
is empty.
-/
lemma mem_periodCandidates_top (r : ℕ) (x : Cfg) :
    (2 * r + 1) ∈ periodCandidates r x := by
  exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, fun k hk₁ hk₂ => by omega ⟩

lemma periodCandidates_nonempty (r : ℕ) (x : Cfg) :
    (periodCandidates r x).Nonempty :=
  ⟨_, mem_periodCandidates_top r x⟩

/-- The **minimal period** of the window pattern `π_r(x)`: the least
`j ∈ {1, …, 2r+1}` with `WinPerEq r x j`. -/
noncomputable def patPeriod (r : ℕ) (x : Cfg) : ℕ :=
  (periodCandidates r x).min' (periodCandidates_nonempty r x)

lemma patPeriod_pos (r : ℕ) (x : Cfg) : 1 ≤ patPeriod r x := by
  exact Finset.mem_Icc.mp ( Finset.mem_filter.mp ( Finset.min'_mem ( periodCandidates r x ) ( periodCandidates_nonempty r x ) ) |>.1 ) |>.1

lemma patPeriod_le (r : ℕ) (x : Cfg) : patPeriod r x ≤ 2 * r + 1 := by
  exact Finset.min'_le _ _ ( mem_periodCandidates_top r x )

/-
The minimal period satisfies its own window comparison.
-/
lemma winPerEq_patPeriod (r : ℕ) (x : Cfg) :
    WinPerEq r x (patPeriod r x : ℤ) := by
  convert Finset.mem_filter.mp ( Finset.min'_mem ( periodCandidates r x ) ( periodCandidates_nonempty r x ) ) |>.2

/-
Minimality: no smaller positive `j` satisfies the window comparison.
-/
lemma patPeriod_min (r : ℕ) (x : Cfg) {j : ℕ} (hj : 1 ≤ j)
    (hlt : j < patPeriod r x) : ¬ WinPerEq r x (j : ℤ) := by
  contrapose! hlt; have := Finset.min'_le ( periodCandidates r x ) j; simp_all +decide [ periodCandidates ] ;
  by_cases h : j ≤ 2 * r + 1 <;> simp_all +decide [ patPeriod ];
  · exact this;
  · exact le_trans ( Finset.min'_le _ _ ( mem_periodCandidates_top r x ) ) ( by linarith )

/-
`WinPerEq` depends only on the window `proj r`.
-/
lemma winPerEq_congr {r : ℕ} {x y : Cfg} (h : proj r x = proj r y) {j : ℤ}
    (hj : 0 ≤ j) : WinPerEq r x j → WinPerEq r y j := by
  intro hWinPerEq k hk₁ hk₂; have := h; simp_all +decide [ funext_iff, Win ] ;
  specialize hWinPerEq k ( by linarith ) ( by linarith ) ; simp_all +decide [ proj ] ;
  grind

/-
`patPeriod` depends only on the window `proj r`.
-/
lemma patPeriod_congr {r : ℕ} {x y : Cfg} (h : proj r x = proj r y) :
    patPeriod r x = patPeriod r y := by
  unfold patPeriod;
  congr! 1;
  ext j; simp [periodCandidates];
  intro hj₁ hj₂; exact ⟨ fun h' => winPerEq_congr h ( by positivity ) h', fun h' => winPerEq_congr ( h.symm ) ( by positivity ) h' ⟩ ;

/-! ## The minimal periodic extension `cfgExt` -/

/-- The **minimal periodic extension** of (the window pattern of) `x`: the
configuration obtained by reducing each coordinate `i` to its representative
`-r + ((i+r) mod patPeriod) ∈ [-r, -r + patPeriod)` and reading off `x` there.
By construction it is `patPeriod r x`-periodic, and (using `WinPerEq`) it agrees
with `x` on the window `F_r` (`cfgExt_eq_on_window`). -/
noncomputable def cfgExt (r : ℕ) (x : Cfg) : Cfg :=
  fun i => x (-(r : ℤ) + (i + (r : ℤ)) % (patPeriod r x : ℤ))


/-
`cfgExt r x` is `patPeriod r x`-periodic: shifting the argument by the
period does not change the value.
-/
lemma cfgExt_periodic (r : ℕ) (x : Cfg) (i : ℤ) :
    cfgExt r x (i + (patPeriod r x : ℤ)) = cfgExt r x i := by
  unfold cfgExt;
  norm_num [ add_assoc, Int.add_emod_right ];
  convert rfl using 2;
  norm_num [ add_comm, Int.emod_eq_emod_iff_emod_sub_eq_zero ]

/-
`cfgExt r x` agrees with `x` on the window `[-r, r]`.
-/
lemma cfgExt_eq_on_window (r : ℕ) (x : Cfg) {i : ℤ}
    (hi1 : -(r : ℤ) ≤ i) (hi2 : i ≤ (r : ℤ)) :
    cfgExt r x i = x i := by
  by_contra h_contra;
  -- By induction on $q$, we can show that $x (m + j * q) = x m$ for all $q$ such that $m + j * q \leq r$.
  have h_ind : ∀ q : ℕ, -(r : ℤ) + (i + r) % (patPeriod r x : ℤ) + (patPeriod r x : ℤ) * q ≤ r → x (-(r : ℤ) + (i + r) % (patPeriod r x : ℤ) + (patPeriod r x : ℤ) * q) = x (-(r : ℤ) + (i + r) % (patPeriod r x : ℤ)) := by
    intro q hq
    induction' q with q ih;
    · norm_num;
    · have := winPerEq_patPeriod r x;
      convert this ( -r + ( i + r ) % ( patPeriod r x ) + ( patPeriod r x ) * ( q + 1 ) ) _ _ using 1 <;> push_cast at * <;> ring_nf at *;
      · grind;
      · nlinarith [ Int.emod_nonneg ( r + i ) ( show ( patPeriod r x : ℤ ) ≠ 0 from mod_cast ne_of_gt ( patPeriod_pos r x ) ) ];
      · linarith;
  specialize h_ind ( Int.toNat ( ( i + r ) / ( patPeriod r x : ℤ ) ) ) ?_ <;> simp_all +decide [ Int.toNat_of_nonneg ( Int.ediv_nonneg ( by linarith : 0 ≤ i + r ) ( by linarith [ patPeriod_pos r x ] : 0 ≤ ( patPeriod r x : ℤ ) ) ) ];
  · linarith [ Int.emod_add_mul_ediv ( i + r ) ( patPeriod r x ) ];
  · exact h_contra ( by rw [ show -↑r + ( i + ↑r ) % ↑ ( patPeriod r x ) + ↑ ( patPeriod r x ) * ( ( i + ↑r ) / ↑ ( patPeriod r x ) ) = i by linarith [ Int.emod_add_mul_ediv ( i + r ) ( patPeriod r x : ℤ ) ] ] at h_ind; exact h_ind.symm )

end LamplighterStability.Dynamics