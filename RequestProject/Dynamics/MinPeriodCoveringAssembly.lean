import RequestProject.Dynamics.MinPeriodFloor
import RequestProject.Dynamics.MinPeriodPartition
import RequestProject.Dynamics.MinPeriodErrorBound

/-!
# Assembly of the periodic-covering lemma (`lem:covering_per_seq`, Section 6.1)

This file assembles `lem:covering_per_seq` out of the previously-built
ingredients:

* `claim_62` (the per-pattern error / `δ`-closed-tower dichotomy);
* the disjointness engine `floor_disjoint` (`MinPeriodFloor.lean`);
* the cylinder backbone `Xperl_eq_iUnion_extCyl`, `patPeriod_restrict_gen`,
  `mem_extCyl_self`, `mem_Xperl_iff_patPeriod` (`MinPeriodPartition.lean`);
* the error-set measure bound `error_set_measure_le`
  (`MinPeriodErrorBound.lean`).

The construction works at window radius `r = 3t`.  The `F_{3t}`-window patterns
of period `≤ t` form a finite set; each generates a periodic configuration
`ext p = cfgExt (3t) (padCfg p)`.  Two such patterns lie in the same `L`-orbit
iff their extensions are shifts of each other.  For each orbit we either build a
single `δ`-closed tower from a (canonically chosen) `δ`-closed member, or, if no
member is `δ`-closed, throw the whole orbit into the error set.  Disjointness
across orbits is `floor_disjoint`; the error measure is bounded by
`error_set_measure_le`.

The reusable *geometric core* proved here:

* `padCfg` / `proj_padCfg` — realize a window pattern as a configuration;
* `cfgExt_eq_self_of_periodic` — a globally `≤ t`-periodic configuration is its
  own minimal periodic extension at radius `3t`;
* `periodic_eq_of_proj` — two globally `≤ t`-periodic configurations with equal
  `F_{3t}`-window are equal;
* `Defined.iUnion` — `n`-definedness is closed under arbitrary unions.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory
open scoped BigOperators
open scoped Classical

/-- Realize a window pattern `p : Win n → Bool` as a configuration (`false`
outside the window `F_n`). -/
def padCfg (n : ℕ) (p : Win n → Bool) : Cfg :=
  fun i => if h : i ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) then p ⟨i, h⟩ else false

/-
The `F_n`-window of `padCfg n p` is `p`.
-/
lemma proj_padCfg (n : ℕ) (p : Win n → Bool) : proj n (padCfg n p) = p := by
  exact funext fun x => by unfold proj padCfg; simp +decide [ x.2 ] ;

/-
`n`-definedness is closed under arbitrary unions.
-/
lemma Defined.iUnion {n : ℕ} {ι : Sort*} {f : ι → Set Cfg}
    (h : ∀ i, Defined n (f i)) : Defined n (⋃ i, f i) := by
  intro x y hxy;
  simp +decide [ Set.mem_iUnion, h _ _ _ hxy ]

/-
**Geometric core (self-extension).**  A globally `p`-periodic configuration
with `1 ≤ p ≤ t` equals its own minimal periodic extension at window radius
`3t`.
-/
lemma cfgExt_eq_self_of_periodic {t : ℕ} {z : Cfg} {p : ℕ}
    (hp1 : 1 ≤ p) (hp2 : p ≤ t) (hper : ∀ j : ℤ, z (j + (p : ℤ)) = z j) :
    cfgExt (3 * t) z = z := by
  have h_period : ∀ i : ℤ, cfgExt (3 * t) z i = z i := by
    intro i
    set r := 3 * t + i.natAbs with hr_def
    have hr_le : 3 * t ≤ r := by
      exact Nat.le_add_right _ _
    have hi_mem : i ∈ Finset.Icc (-(r : ℤ)) (r : ℤ) := by
      grind
    have h_patPeriod_le_t : patPeriod r z ≤ t := by
      apply patPeriod_le_of_periodic hp1 (by linarith) (fun j => hper j) |> le_trans <| by linarith;
    have h_proj_eq : proj r (cfgExt (3 * t) z) = proj r z := by
      apply cfgExt_restrict_proj_gen (by linarith) (by linarith) h_patPeriod_le_t
    exact (by
    exact congr_fun h_proj_eq ⟨ i, hi_mem ⟩);
  exact funext h_period

/-
**Geometric core (rigidity).**  Two globally `≤ t`-periodic configurations
that agree on the window `F_{3t}` are equal.
-/
lemma periodic_eq_of_proj {t : ℕ} {z z' : Cfg} {p p' : ℕ}
    (hp1 : 1 ≤ p) (hp2 : p ≤ t) (hper : ∀ j : ℤ, z (j + (p : ℤ)) = z j)
    (hp1' : 1 ≤ p') (hp2' : p' ≤ t) (hper' : ∀ j : ℤ, z' (j + (p' : ℤ)) = z' j)
    (h : proj (3 * t) z = proj (3 * t) z') : z = z' := by
  convert cfgExt_congr h;
  · exact Eq.symm ( cfgExt_eq_self_of_periodic hp1 ( by linarith ) hper );
  · exact Eq.symm ( cfgExt_eq_self_of_periodic hp1' hp2' hper' )

/-! ## Orbit machinery on `F_{3t}`-window patterns of period `≤ t` -/

/-- The canonical periodic configuration of a window pattern `p` at radius `3t`. -/
noncomputable def patExt (t : ℕ) (p : Win (3 * t) → Bool) : Cfg :=
  cfgExt (3 * t) (padCfg (3 * t) p)

/-- The minimal window period of a pattern `p` at radius `3t`. -/
noncomputable def patPer (t : ℕ) (p : Win (3 * t) → Bool) : ℕ :=
  patPeriod (3 * t) (padCfg (3 * t) p)


lemma patPer_pos (t : ℕ) (p : Win (3 * t) → Bool) : 1 ≤ patPer t p := by
  convert patPeriod_pos ( 3 * t ) ( padCfg ( 3 * t ) p ) using 1

/-
`patExt t p` is globally `patPer t p`-periodic.
-/
lemma patExt_periodic (t : ℕ) (p : Win (3 * t) → Bool) (j : ℤ) :
    patExt t p (j + (patPer t p : ℤ)) = patExt t p j := by
  convert cfgExt_periodic ( 3 * t ) ( padCfg ( 3 * t ) p ) j using 1

/-
Any shift of `patExt t p` is globally `patPer t p`-periodic.
-/
lemma patExt_zpow_periodic (t : ℕ) (p : Win (3 * t) → Bool) (m : ℤ) (j : ℤ) :
    ((L ^ m) (patExt t p)) (j + (patPer t p : ℤ)) = ((L ^ m) (patExt t p)) j := by
  grind +suggestions

/-
**Rigidity, packaged for orbits.**  Two patterns of period `≤ t` whose
extensions agree (after a shift `m`) on `F_{3t}` have equal extensions there.
-/
lemma patExt_eq_of_proj {t : ℕ} {p q : Win (3 * t) → Bool}
    (hp : patPer t p ≤ t) (hq : patPer t q ≤ t) (m : ℤ)
    (h : proj (3 * t) (patExt t p) = proj (3 * t) ((L ^ m) (patExt t q))) :
    patExt t p = (L ^ m) (patExt t q) := by
  convert periodic_eq_of_proj ( patPer_pos t p ) hp ( patExt_periodic t p ) ( patPer_pos t q ) hq ( patExt_zpow_periodic t q m ) h using 1

/-
**Orbit floor cover (geometric heart).**  If `patExt t p = L^i (patExt t q)`
with `0 ≤ i < patPer t q`, then the full-window cylinder of `p` sits inside the
`i`-th floor of the tower based at the `ℓq`-window cylinder of `q`.
-/
lemma extCyl_subset_floor {t : ℕ} {p q : Win (3 * t) → Bool}
    (hq : patPer t q ≤ t) {ℓ ℓq : ℕ} (hℓ : ℓq + t ≤ ℓ)
    {i : ℕ} (hi : i < patPer t q)
    (hpq : patExt t p = (L ^ (i : ℤ)) (patExt t q)) :
    extCyl (3 * t) (padCfg (3 * t) p) ℓ
      ⊆ (L ^ (i : ℤ)) '' (extCyl (3 * t) (padCfg (3 * t) q) ℓq) := by
  intro z hz
  refine' ⟨ ( L ^ ( -i : ℤ ) ) z, _, _ ⟩ <;> simp_all +decide [ mem_extCyl ];
  ext ⟨ m, hm ⟩;
  convert congrFun hz ⟨ m + i, _ ⟩ using 1;
  all_goals norm_num [ proj ] at *;
  · convert L_zpow_apply ( -i ) z m using 1 ; norm_num [ L ];
    lia;
  · replace hpq := congr_fun hpq ( m + i ) ; simp_all +decide ;
    convert hpq.symm using 1;
    convert congr_arg ( fun x : Cfg => x m ) ( cfgExt_eq_self_of_periodic ( show 1 ≤ patPer t q from patPer_pos t q ) ( show patPer t q ≤ t from hq ) ( show ∀ j : ℤ, cfgExt ( 3 * t ) ( padCfg ( 3 * t ) q ) ( j + ( patPer t q : ℤ ) ) = cfgExt ( 3 * t ) ( padCfg ( 3 * t ) q ) j from fun j => by
                                                                                                                                                          convert patExt_periodic t q j using 1 ) ) using 1;
    · rw [ cfgExt_eq_self_of_periodic ( show 1 ≤ patPer t q from patPer_pos t q ) ( show patPer t q ≤ t from hq ) ( show ∀ j : ℤ, cfgExt ( 3 * t ) ( padCfg ( 3 * t ) q ) ( j + ( patPer t q : ℤ ) ) = cfgExt ( 3 * t ) ( padCfg ( 3 * t ) q ) j from fun j => by
                                                                                                                      convert patExt_periodic t q j using 1 ) ];
    · convert L_zpow_apply i ( cfgExt ( 3 * t ) ( padCfg ( 3 * t ) q ) ) ( m + i ) using 1 ; ring;
  · constructor <;> linarith [ show ( i : ℤ ) < patPer t q from mod_cast hi, show ( patPer t q : ℤ ) ≤ t from mod_cast hq ]

/-! ## The orbit relation and its equivalence properties -/

/-- Two `F_{3t}`-window patterns lie in the same `L`-orbit if their canonical
periodic extensions are shifts of each other. -/
def sameOrbit (t : ℕ) (p q : Win (3 * t) → Bool) : Prop :=
  ∃ i : ℤ, patExt t p = (L ^ i) (patExt t q)

lemma sameOrbit_refl (t : ℕ) (p : Win (3 * t) → Bool) : sameOrbit t p p := by
  exact ⟨ 0, by simp +decide ⟩

lemma sameOrbit_symm {t : ℕ} {p q : Win (3 * t) → Bool} (h : sameOrbit t p q) :
    sameOrbit t q p := by
  obtain ⟨ i, hi ⟩ := h;
  use -i; simp_all +decide

lemma sameOrbit_trans {t : ℕ} {p q r : Win (3 * t) → Bool}
    (h1 : sameOrbit t p q) (h2 : sameOrbit t q r) : sameOrbit t p r := by
  obtain ⟨ i, hi ⟩ := h1
  obtain ⟨ j, hj ⟩ := h2
  use i + j;
  simp +decide [ zpow_add, hi, hj ]

/-
A same-orbit witness can be reduced to a shift `0 ≤ i < patPer t q`.
-/
lemma sameOrbit_reduce {t : ℕ} {p q : Win (3 * t) → Bool}
    (hq : 1 ≤ patPer t q) (h : sameOrbit t p q) :
    ∃ i : ℕ, i < patPer t q ∧ patExt t p = (L ^ (i : ℤ)) (patExt t q) := by
  obtain ⟨ m, hm ⟩ := h;
  refine' ⟨ Int.toNat ( m % ( patPer t q : ℤ ) ), _, _ ⟩;
  · linarith [ Int.emod_lt_of_pos m ( by positivity : 0 < ( patPer t q : ℤ ) ), Int.toNat_of_nonneg ( Int.emod_nonneg m ( by positivity : ( patPer t q : ℤ ) ≠ 0 ) ) ];
  · rw [ hm, eq_comm ];
    -- Since $patPer t q$ is the period of $patExt t q$, we have $patExt t q (j + patPer t q) = patExt t q j$ for any $j$.
    have h_period : ∀ j : ℤ, patExt t q (j + (patPer t q : ℤ)) = patExt t q j :=
      patExt_periodic t q
    -- By periodicity, we have $patExt t q (j + k * patPer t q) = patExt t q j$ for any integer $k$.
    have h_periodic : ∀ j : ℤ, ∀ k : ℤ, patExt t q (j + k * (patPer t q : ℤ)) = patExt t q j := by
      exact fun j k => by simpa [ add_mul, ← add_assoc ] using Function.Periodic.int_mul h_period k j;
    ext j; simp +decide [ L_zpow_apply ] ;
    rw [ max_eq_left ( Int.emod_nonneg _ ( by positivity ) ) ] ; specialize h_periodic ( j - m ) ( m / patPer t q ) ; simp_all +decide [ Int.emod_def ] ;
    convert h_periodic using 2 ; ring

/-! ## The construction data -/

/-- An injective key on the (finite) type of `F_{3t}`-window patterns, used to
choose a canonical orbit representative. -/
noncomputable def patKey (t : ℕ) (p : Win (3 * t) → Bool) : ℕ :=
  (Fintype.equivFin (Win (3 * t) → Bool) p).val

lemma patKey_injective {t : ℕ} {p q : Win (3 * t) → Bool}
    (h : patKey t p = patKey t q) : p = q := by
  exact Fintype.equivFin _ |>.injective <| Fin.ext h

/-- `p` is a `δ`-closed ("tower") pattern: its `Lx p`-window extension cylinder
is `F_{per-1}`-independent and `δ`-closed. -/
def coverIsTow (t : ℕ) (δ : ℝ) (μ : Measure Cfg) (Lx : (Win (3 * t) → Bool) → ℕ)
    (p : Win (3 * t) → Bool) : Prop :=
  FIndep (patPer t p - 1) (extCyl (3 * t) (padCfg (3 * t) p) (Lx p)) ∧
    DeltaClosed μ δ (patPer t p) (extCyl (3 * t) (padCfg (3 * t) p) (Lx p))

/-- `p` is the chosen leader of its orbit: a tower pattern of period `≤ t` with
minimal key among tower patterns in its orbit. -/
def coverIsLeader (t : ℕ) (δ : ℝ) (μ : Measure Cfg) (Lx : (Win (3 * t) → Bool) → ℕ)
    (p : Win (3 * t) → Bool) : Prop :=
  patPer t p ≤ t ∧ coverIsTow t δ μ Lx p ∧
    ∀ q : Win (3 * t) → Bool, patPer t q ≤ t → coverIsTow t δ μ Lx q →
      sameOrbit t p q → patKey t p ≤ patKey t q

/-- `p`'s orbit has no tower pattern (so the whole orbit goes to the error set). -/
def coverIsErr (t : ℕ) (δ : ℝ) (μ : Measure Cfg) (Lx : (Win (3 * t) → Bool) → ℕ)
    (p : Win (3 * t) → Bool) : Prop :=
  ¬ ∃ q : Win (3 * t) → Bool, patPer t q ≤ t ∧ coverIsTow t δ μ Lx q ∧ sameOrbit t p q

/-- The tower base of index `τ`: the extension cylinder if `τ` is a leader, else
empty. -/
noncomputable def coverBase (t : ℕ) (δ : ℝ) (μ : Measure Cfg)
    (Lx : (Win (3 * t) → Bool) → ℕ) (τ : {p : Win (3 * t) → Bool // patPer t p ≤ t}) :
    Set Cfg :=
  if coverIsLeader t δ μ Lx τ.1 then extCyl (3 * t) (padCfg (3 * t) τ.1) (Lx τ.1) else ∅

/-- The tower height of index `τ`: the period if `τ` is a leader, else `0`. -/
noncomputable def coverHeight (t : ℕ) (δ : ℝ) (μ : Measure Cfg)
    (Lx : (Win (3 * t) → Bool) → ℕ) (τ : {p : Win (3 * t) → Bool // patPer t p ≤ t}) : ℕ :=
  if coverIsLeader t δ μ Lx τ.1 then patPer t τ.1 else 0

/-- The error set: the union of the extension cylinders of all error-orbit
patterns of period `≤ t`. -/
noncomputable def coverErr (t : ℕ) (δ : ℝ) (μ : Measure Cfg)
    (Lx : (Win (3 * t) → Bool) → ℕ) : Set Cfg :=
  ⋃ p ∈ (Finset.univ.filter
      (fun p : Win (3 * t) → Bool => patPer t p ≤ t ∧ coverIsErr t δ μ Lx p)),
    extCyl (3 * t) (padCfg (3 * t) p) (Lx p)

/-
**Existence of a leader.**  If a pattern's orbit contains a tower pattern,
it has a (unique) leader in the same orbit.
-/
lemma exists_leader {t : ℕ} {δ : ℝ} {μ : Measure Cfg}
    {Lx : (Win (3 * t) → Bool) → ℕ} {p : Win (3 * t) → Bool}
    (h : ∃ q, patPer t q ≤ t ∧ coverIsTow t δ μ Lx q ∧ sameOrbit t p q) :
    ∃ L, coverIsLeader t δ μ Lx L ∧ sameOrbit t p L := by
  obtain ⟨q, hq⟩ := h
  set S := Finset.univ.filter (fun r => patPer t r ≤ t ∧ coverIsTow t δ μ Lx r ∧ sameOrbit t p r)
  have hS_nonempty : S.Nonempty := by
    exact ⟨ q, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hq ⟩ ⟩;
  obtain ⟨L, hL⟩ : ∃ L ∈ S, ∀ r ∈ S, patKey t L ≤ patKey t r := by
    exact Finset.exists_min_image _ _ hS_nonempty;
  use L;
  simp +zetaDelta at *;
  exact ⟨ ⟨ hL.1.1, hL.1.2.1, fun q hq₁ hq₂ hq₃ => hL.2 q hq₁ hq₂ ( sameOrbit_trans hL.1.2.2 hq₃ ) ⟩, hL.1.2.2 ⟩

/-! ## The construction obligations -/

variable {t : ℕ} {υ δ : ℝ} {μ : Measure Cfg} {Lx : (Win (3 * t) → Bool) → ℕ} {ℓ : ℕ}

/-
Height bound.
-/
lemma coverHeight_le (τ : {p : Win (3 * t) → Bool // patPer t p ≤ t}) :
    coverHeight t δ μ Lx τ ≤ t := by
  unfold coverHeight;
  split_ifs <;> linarith [ τ.2 ]

/-
Each base is `ℓ`-defined.
-/
lemma coverBase_defined (hℓ : ∀ p, Lx p ≤ ℓ)
    (τ : {p : Win (3 * t) → Bool // patPer t p ≤ t}) :
    Defined ℓ (coverBase t δ μ Lx τ) := by
  unfold coverBase;
  split_ifs <;> [ exact Defined.mono ( hℓ _ ) ( extCyl_defined _ _ _ ) ; exact defined_empty _ ]

/-
Each floor is `(ℓ + t)`-defined.
-/
lemma coverFloor_defined (hℓ : ∀ p, Lx p ≤ ℓ)
    (τ : {p : Win (3 * t) → Bool // patPer t p ≤ t}) {i : ℕ}
    (hi : i < coverHeight t δ μ Lx τ) :
    Defined (ℓ + t) (towerFloor (coverBase t δ μ Lx τ) i) := by
  unfold coverHeight at hi;
  unfold coverBase; split_ifs at hi;
  · split_ifs;
    apply Defined.mono;
    convert Nat.add_le_add ( hℓ τ ) ( show i ≤ t from hi.le.trans τ.2 ) using 1;
    convert defined_shift ( extCyl_defined ( 3 * t ) ( padCfg ( 3 * t ) τ ) ( Lx τ ) ) i using 1;
  · contradiction

/-
Each base has singleton `π_t`-projection.
-/
lemma coverBase_projSingleton (hLb : ∀ p, 3 * t ≤ Lx p)
    (τ : {p : Win (3 * t) → Bool // patPer t p ≤ t}) :
    ProjSingleton t (coverBase t δ μ Lx τ) := by
  unfold coverBase;
  split_ifs <;> simp_all +decide [ ProjSingleton ];
  exact ⟨ _, fun x hx => proj_mono ( show t ≤ Lx τ from le_trans ( by omega ) ( hLb _ ) ) hx ⟩

/-
Each `(base, height)` is a tower base.
-/
lemma coverBase_isTowerBase
    (τ : {p : Win (3 * t) → Bool // patPer t p ≤ t}) :
    IsTowerBase (coverHeight t δ μ Lx τ) (coverBase t δ μ Lx τ) := by
  unfold coverHeight coverBase;
  split_ifs;
  · convert ( isTowerBase_iff_fIndep ( patPer t τ ) ( patPer_pos t τ ) _ ).2 _ using 1;
    rename_i h;
    exact h.2.1.1;
  · tauto

/-
Each tower is `δ`-closed.
-/
lemma coverBase_deltaClosed
    (τ : {p : Win (3 * t) → Bool // patPer t p ≤ t}) :
    DeltaClosed μ δ (coverHeight t δ μ Lx τ) (coverBase t δ μ Lx τ) := by
  unfold coverBase coverHeight DeltaClosed;
  split_ifs <;> simp_all +decide [ coverIsLeader ];
  rename_i h; have := h.2.1.2; aesop;

/-
Tower floors are pairwise disjoint.
-/
lemma coverFloor_disjoint (hLb : ∀ p, 3 * t ≤ Lx p)
    (τ τ' : {p : Win (3 * t) → Bool // patPer t p ≤ t}) (i i' : ℕ)
    (hi : i < coverHeight t δ μ Lx τ) (hi' : i' < coverHeight t δ μ Lx τ')
    (hne : ¬ (τ = τ' ∧ i = i')) :
    Disjoint (towerFloor (coverBase t δ μ Lx τ) i)
      (towerFloor (coverBase t δ μ Lx τ') i') := by
  by_cases hτ : τ.1 = τ'.1;
  · have := coverBase_isTowerBase ( δ := δ ) ( μ := μ ) ( Lx := Lx ) τ; simp_all +decide [ IsTowerBase ] ;
    grind +qlia;
  · convert floor_disjoint ( show patPer t τ.1 ≤ t from τ.2 ) ( show patPer t τ'.1 ≤ t from τ'.2 ) ( hLb τ.1 ) ( hLb τ'.1 ) ( show |(i : ℤ) - (i' : ℤ)| ≤ t from ?_ ) ?_ using 1;
    · unfold coverBase coverHeight at *;
      split_ifs at * <;> simp_all +decide [ towerFloor ];
    · unfold coverBase coverHeight at *; aesop;
    · exact abs_sub_le_iff.mpr ⟨ by linarith [ show ( i : ℤ ) < t from mod_cast lt_of_lt_of_le hi ( coverHeight_le τ ) ], by linarith [ show ( i' : ℤ ) < t from mod_cast lt_of_lt_of_le hi' ( coverHeight_le τ' ) ] ⟩;
    · contrapose! hτ;
      have := patExt_eq_of_proj ( show patPer t τ.1 ≤ t from τ.2 ) ( show patPer t τ'.1 ≤ t from τ'.2 ) ( i' - i ) hτ;
      have := sameOrbit_symm ( show sameOrbit t τ'.1 τ.1 from by
                                use (i : ℤ) - (i' : ℤ);
                                simp_all +decide [ zpow_sub ] );
      have := τ.2; have := τ'.2; simp_all +decide [ coverHeight, coverIsLeader ] ;
      split_ifs at hi hi' <;> simp_all +decide [ coverIsTow ];
      rename_i h₁ h₂;
      exact patKey_injective ( le_antisymm ( h₁.2 _ this h₂.1.1 h₂.1.2 ‹_› ) ( h₂.2 _ ‹_› h₁.1.1 h₁.1.2 ( sameOrbit_symm ‹_› ) ) )

/-
The error set is disjoint from every tower floor.
-/
lemma coverErr_disjoint_floor (hLb : ∀ p, 3 * t ≤ Lx p)
    (τ : {p : Win (3 * t) → Bool // patPer t p ≤ t}) {i : ℕ}
    (hi : i < coverHeight t δ μ Lx τ) :
    Disjoint (coverErr t δ μ Lx) (towerFloor (coverBase t δ μ Lx τ) i) := by
  refine' Set.disjoint_left.mpr _;
  intro x hx; contrapose! hx; simp_all +decide [ coverErr, coverBase, towerFloor ] ;
  intro p hp hp'; contrapose! hp'; simp_all +decide [ coverIsLeader, coverIsTow, coverIsErr ] ;
  use τ.val; simp_all +decide [ coverHeight ] ;
  apply Classical.byContradiction
  intro h_no_orbit;
  have := floor_disjoint ( show patPer t p ≤ t from hp ) ( show patPer t ↑τ ≤ t from hx.1.1 ) ( show 3 * t ≤ Lx p from hLb p ) ( show 3 * t ≤ Lx ↑τ from hLb ↑τ ) ( show |(0 : ℤ) - (i : ℤ)| ≤ t from by
                                                                                                                                                                      grind ) ( show proj ( 3 * t ) ( cfgExt ( 3 * t ) ( padCfg ( 3 * t ) p ) ) ≠ proj ( 3 * t ) ( ( L ^ ( i : ℤ ) ) ( cfgExt ( 3 * t ) ( padCfg ( 3 * t ) ↑τ ) ) ) from by
                                                                                                                                                                                                                    exact fun h => h_no_orbit <| by exact ⟨ i, patExt_eq_of_proj hp hx.1.1 ( i : ℤ ) h ⟩ ; ) ; simp_all +decide [ sameOrbit ] ;
  simp_all +decide [ Set.disjoint_left, extCyl ]

/-
The error set is `ℓ`-defined.
-/
lemma coverErr_defined (hℓ : ∀ p, Lx p ≤ ℓ) :
    Defined ℓ (coverErr t δ μ Lx) := by
  apply Defined.iUnion;
  intro p; exact Defined.iUnion fun _ => Defined.mono (hℓ p) (extCyl_defined (3 * t) (padCfg (3 * t) p) (Lx p)) ;

/-
The error set has measure `< υ`.
-/
lemma coverErr_measure [IsProbabilityMeasure μ] (hυ0 : 0 < υ)
    (hLb : ∀ p, 3 * t ≤ Lx p)
    (hdich : ∀ p : Win (3 * t) → Bool, patPer t p ≤ t →
      (μ (extCyl (3 * t) (padCfg (3 * t) p) (Lx p))).toReal
          ≤ (υ / 2) * (μ (cyl (3 * t) p)).toReal
        ∨ coverIsTow t δ μ Lx p) :
    (μ (coverErr t δ μ Lx)).toReal < υ := by
  refine' lt_of_le_of_lt _ ( half_lt_self hυ0 );
  convert error_set_measure_le ( μ := μ ) ( show 0 ≤ υ / 2 by linarith ) ( Finset.univ.filter fun p : Win ( 3 * t ) → Bool => patPer t p ≤ t ∧ coverIsErr t δ μ Lx p ) ( fun p => extCyl ( 3 * t ) ( padCfg ( 3 * t ) p ) ( Lx p ) ) _ _ _ using 1;
  · simp +zetaDelta at *;
    exact fun p hp hp' => by simpa [ proj_padCfg ] using extCyl_subset_cyl ( hLb p ) ( padCfg ( 3 * t ) p ) ;
  · exact fun p hp => measurableSet_cyl _ _;
  · simp +zetaDelta at *;
    exact fun p hp hp' => Or.resolve_right ( hdich p hp ) fun h => hp' ⟨ p, hp, h, sameOrbit_refl t p ⟩

/-
The family covers the approximately periodic part.
-/
lemma coverErr_covers (ht : 1 ≤ t)
    (hℓ3 : 3 * t ≤ ℓ) (hℓLx : ∀ p, Lx p + t ≤ ℓ) :
    Xperl t ℓ ⊆ coverErr t δ μ Lx ∪
      ⋃ τ : {p : Win (3 * t) → Bool // patPer t p ≤ t},
        ⋃ i ∈ Finset.range (coverHeight t δ μ Lx τ),
          towerFloor (coverBase t δ μ Lx τ) i := by
  intro y hy;
  -- Set `p := proj (3*t) y`.
  set p : Win (3 * t) → Bool := proj (3 * t) y;
  -- By `mem_Xperl_iff_patPeriod (show t ≤ ℓ ...)`, `patPeriod ℓ y ≤ t`. By `patPeriod_restrict_gen (show 2*t ≤ 3*t)(show 3*t ≤ ℓ from hℓ3) (this)`, `patPeriod (3*t) y = patPeriod ℓ y ≤ t`.
  have hp : patPer t p ≤ t := by
    -- By `patPeriod_restrict_gen (show 2*t ≤ 3*t)(show 3*t ≤ ℓ from hℓ3) (this)`, `patPeriod (3*t) y = patPeriod ℓ y ≤ t`.
    have hpatPeriod_eq : patPer t p = patPeriod (3 * t) y := by
      apply patPeriod_congr;
      convert proj_padCfg ( 3 * t ) p using 1;
    exact hpatPeriod_eq.symm ▸ patPeriod_restrict_gen ( show 2 * t ≤ 3 * t by linarith ) ( show 3 * t ≤ ℓ by linarith ) ( by simpa using mem_Xperl_iff_patPeriod y |>.1 hy ) ▸ by simpa using mem_Xperl_iff_patPeriod y |>.1 hy;
  -- By `mem_extCyl_self (show 3*t ≤ ℓ from hℓ3) (patPeriod ℓ y ≤ t)`, `y ∈ extCyl (3*t) y ℓ`, i.e. `proj ℓ y = proj ℓ (cfgExt (3*t) y)`.
  have hy_ext : y ∈ extCyl (3 * t) (padCfg (3 * t) p) ℓ := by
    have hy_ext : y ∈ extCyl (3 * t) y ℓ := by
      apply mem_extCyl_self hℓ3;
      exact mem_Xperl_iff_patPeriod y |>.1 hy;
    convert hy_ext using 1;
    exact Set.ext fun x => by rw [ mem_extCyl, mem_extCyl, cfgExt_congr ( proj_padCfg _ _ ) ] ;
  by_cases hcase : ∃ q : Win (3 * t) → Bool, patPer t q ≤ t ∧ coverIsTow t δ μ Lx q ∧ sameOrbit t p q;
  · obtain ⟨ L, hL₁, hL₂ ⟩ := exists_leader hcase;
    obtain ⟨ i, hi, hi' ⟩ := sameOrbit_reduce ( patPer_pos t L ) hL₂;
    refine' Or.inr ( Set.mem_iUnion₂.mpr ⟨ ⟨ L, hL₁.1 ⟩, i, _, _ ⟩ ) <;> simp_all +decide [ coverHeight, coverBase ];
    exact ( Dynamics.L ^ i ) '' extCyl ( 3 * t ) ( padCfg ( 3 * t ) L ) ( Lx L );
    refine' ⟨ rfl, _ ⟩;
    convert extCyl_subset_floor ( hL₁.1 ) ( hℓLx L ) hi hi' hy_ext using 1;
  · refine' Or.inl ( Set.mem_iUnion₂.mpr ⟨ p, _, _ ⟩ );
    · unfold coverIsErr; aesop;
    · exact extCyl_mono ( by linarith [ hℓLx p ] ) hy_ext

/-! ## The assembled periodic-covering lemma -/

open scoped Classical in
/-- **`lem:covering_per_seq` (assembled).**  The statement matches
`covering_per_seq` of `MarkerLemmas.lean`; the latter is closed by this lemma. -/
theorem covering_per_seq_impl :
    ∃ (coverLen : ℕ → ℝ → ℝ → ℝ) (coverDef : ℕ → ℕ → ℕ),
      ∀ (t : ℕ) (υ δ : ℝ), 1 ≤ t → 0 < υ → υ ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
        ∀ (ℓ : ℕ), coverLen t υ δ ≤ (ℓ : ℝ) →
          ∀ (μ : Measure Cfg) [IsProbabilityMeasure μ],
            ∃ (E : Set Cfg) (ι : Type) (_ : Fintype ι)
              (base : ι → Set Cfg) (height : ι → ℕ),
              Defined ℓ E ∧ (μ E).toReal < υ ∧
              (∀ τ : ι, IsTowerBase (height τ) (base τ)) ∧
              (∀ τ : ι, DeltaClosed μ δ (height τ) (base τ)) ∧
              (∀ τ : ι, height τ ≤ t) ∧
              (∀ τ : ι, Defined ℓ (base τ)) ∧
              (∀ τ : ι, ∀ i, i < height τ →
                Defined (coverDef t ℓ) (towerFloor (base τ) i)) ∧
              (∀ τ : ι, ProjSingleton t (base τ)) ∧
              (∀ τ τ' : ι, ∀ i i' : ℕ, i < height τ → i' < height τ' →
                ¬ (τ = τ' ∧ i = i') →
                Disjoint (towerFloor (base τ) i) (towerFloor (base τ') i')) ∧
              (∀ τ : ι, ∀ i, i < height τ →
                Disjoint E (towerFloor (base τ) i)) ∧
              Xperl t ℓ ⊆ E ∪ ⋃ τ : ι, ⋃ i ∈ Finset.range (height τ),
                  towerFloor (base τ) i := by
  obtain ⟨C2, hC2pos, hC2⟩ := claim_62;
  refine' ⟨ _, _, _ ⟩;
  exact fun t υ δ => C2 * ( 3 * t ) * Real.log ( 2 / υ ) / δ + 4 * t;
  exact fun t ℓ => ℓ + t;
  intro t υ δ ht hυ0 hυ2 hδ0 hδ2 ℓ hℓ μ _;
  -- Define `Lx` by choice.
  obtain ⟨Lx, hLx⟩ : ∃ Lx : (Win (3 * t) → Bool) → ℕ, (∀ p, 3 * t ≤ Lx p) ∧ (∀ p, (Lx p : ℝ) ≤ C2 * (3 * t) * Real.log (2 / υ) / δ) ∧ (∀ p, patPer t p ≤ t → (μ (extCyl (3 * t) (padCfg (3 * t) p) (Lx p))).toReal ≤ (υ / 2) * (μ (cyl (3 * t) p)).toReal ∨ coverIsTow t δ μ Lx p) := by
    choose! Lx hLx₁ hLx₂ hLx₃ using fun p : Win ( 3 * t ) → Bool => hC2 ( υ / 2 ) δ ( by linarith ) ( by linarith ) hδ0 hδ2 ( 3 * t ) ( padCfg ( 3 * t ) p ) ( by linarith ) μ;
    refine' ⟨ Lx, hLx₁, _, _ ⟩ <;> simp_all +decide [ coverIsTow ];
    exact fun p hp => by simpa only [ proj_padCfg ] using hLx₃ p;
  refine' ⟨ coverErr t δ μ Lx, { p : Win ( 3 * t ) → Bool // patPer t p ≤ t }, inferInstance, coverBase t δ μ Lx, coverHeight t δ μ Lx, _, _, _, _, _ ⟩;
  · apply coverErr_defined;
    exact fun p => Nat.cast_le.mp ( le_trans ( hLx.2.1 p ) ( le_trans ( le_add_of_nonneg_right <| by positivity ) hℓ ) );
  · grind +suggestions;
  · exact fun τ => coverBase_isTowerBase τ;
  · exact fun τ => coverBase_deltaClosed τ;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · exact fun τ => coverHeight_le τ;
    · apply coverBase_defined;
      exact fun p => Nat.cast_le.mp ( le_trans ( hLx.2.1 p ) ( le_trans ( le_add_of_nonneg_right <| by positivity ) hℓ ) );
    · intro τ i hi;
      apply coverFloor_defined;
      · intro p; exact_mod_cast ( by linarith [ hLx.2.1 p ] : ( Lx p : ℝ ) ≤ ℓ ) ;
      · exact hi;
    · exact fun τ => coverBase_projSingleton hLx.1 τ;
    · refine' ⟨ _, _, _ ⟩;
      · exact fun τ τ' i i' hi hi' hne => coverFloor_disjoint hLx.1 τ τ' i i' hi hi' hne;
      · exact fun τ i hi => coverErr_disjoint_floor hLx.1 τ hi;
      · apply coverErr_covers;
        · linarith;
        · exact_mod_cast ( by linarith [ show ( 0 : ℝ ) ≤ C2 * ( 3 * t ) * Real.log ( 2 / υ ) / δ by exact div_nonneg ( mul_nonneg ( mul_nonneg hC2pos.le ( by positivity ) ) ( Real.log_nonneg ( by rw [ le_div_iff₀ hυ0 ] ; linarith ) ) ) hδ0.le ] : ( 3 * t : ℝ ) ≤ ℓ );
        · intro p; exact_mod_cast ( by linarith [ hLx.2.1 p ] : ( Lx p : ℝ ) + t ≤ ℓ ) ;

open scoped Classical in
/-- **`lem:covering_per_seq` with explicit complexity functions.**  Identical to
`covering_per_seq_impl`, but exposing the concrete witnesses
`coverLen t υ δ = C2·(3t)·log(2/υ)/δ + 4t` (with `C2 > 0` a universal constant
from `claim_62`) and `coverDef t ℓ = ℓ + t`.  This explicit form is needed to
bound the polynomial tower-decomposition window by a closed-form polynomial. -/
theorem covering_per_seq_explicit :
    ∃ (C2 : ℝ), 0 < C2 ∧
      ∀ (t : ℕ) (υ δ : ℝ), 1 ≤ t → 0 < υ → υ ≤ 1 / 2 → 0 < δ → δ ≤ 1 / 2 →
        ∀ (ℓ : ℕ), C2 * (3 * t) * Real.log (2 / υ) / δ + 4 * t ≤ (ℓ : ℝ) →
          ∀ (μ : Measure Cfg) [IsProbabilityMeasure μ],
            ∃ (E : Set Cfg) (ι : Type) (_ : Fintype ι)
              (base : ι → Set Cfg) (height : ι → ℕ),
              Defined ℓ E ∧ (μ E).toReal < υ ∧
              (∀ τ : ι, IsTowerBase (height τ) (base τ)) ∧
              (∀ τ : ι, DeltaClosed μ δ (height τ) (base τ)) ∧
              (∀ τ : ι, height τ ≤ t) ∧
              (∀ τ : ι, Defined ℓ (base τ)) ∧
              (∀ τ : ι, ∀ i, i < height τ →
                Defined (ℓ + t) (towerFloor (base τ) i)) ∧
              (∀ τ : ι, ProjSingleton t (base τ)) ∧
              (∀ τ τ' : ι, ∀ i i' : ℕ, i < height τ → i' < height τ' →
                ¬ (τ = τ' ∧ i = i') →
                Disjoint (towerFloor (base τ) i) (towerFloor (base τ') i')) ∧
              (∀ τ : ι, ∀ i, i < height τ →
                Disjoint E (towerFloor (base τ) i)) ∧
              Xperl t ℓ ⊆ E ∪ ⋃ τ : ι, ⋃ i ∈ Finset.range (height τ),
                  towerFloor (base τ) i := by
  obtain ⟨C2, hC2pos, hC2⟩ := claim_62;
  refine ⟨C2, hC2pos, ?_⟩;
  intro t υ δ ht hυ0 hυ2 hδ0 hδ2 ℓ hℓ μ _;
  -- Define `Lx` by choice.
  obtain ⟨Lx, hLx⟩ : ∃ Lx : (Win (3 * t) → Bool) → ℕ, (∀ p, 3 * t ≤ Lx p) ∧ (∀ p, (Lx p : ℝ) ≤ C2 * (3 * t) * Real.log (2 / υ) / δ) ∧ (∀ p, patPer t p ≤ t → (μ (extCyl (3 * t) (padCfg (3 * t) p) (Lx p))).toReal ≤ (υ / 2) * (μ (cyl (3 * t) p)).toReal ∨ coverIsTow t δ μ Lx p) := by
    choose! Lx hLx₁ hLx₂ hLx₃ using fun p : Win ( 3 * t ) → Bool => hC2 ( υ / 2 ) δ ( by linarith ) ( by linarith ) hδ0 hδ2 ( 3 * t ) ( padCfg ( 3 * t ) p ) ( by linarith ) μ;
    refine' ⟨ Lx, hLx₁, _, _ ⟩ <;> simp_all +decide [ coverIsTow ];
    exact fun p hp => by simpa only [ proj_padCfg ] using hLx₃ p;
  refine' ⟨ coverErr t δ μ Lx, { p : Win ( 3 * t ) → Bool // patPer t p ≤ t }, inferInstance, coverBase t δ μ Lx, coverHeight t δ μ Lx, _, _, _, _, _ ⟩;
  · apply coverErr_defined;
    exact fun p => Nat.cast_le.mp ( le_trans ( hLx.2.1 p ) ( le_trans ( le_add_of_nonneg_right <| by positivity ) hℓ ) );
  · exact coverErr_measure hυ0 hLx.1 hLx.2.2;
  · exact fun τ => coverBase_isTowerBase τ;
  · exact fun τ => coverBase_deltaClosed τ;
  · refine' ⟨ _, _, _, _, _ ⟩;
    · exact fun τ => coverHeight_le τ;
    · apply coverBase_defined;
      exact fun p => Nat.cast_le.mp ( le_trans ( hLx.2.1 p ) ( le_trans ( le_add_of_nonneg_right <| by positivity ) hℓ ) );
    · intro τ i hi;
      apply coverFloor_defined;
      · intro p; exact_mod_cast ( by linarith [ hLx.2.1 p ] : ( Lx p : ℝ ) ≤ ℓ ) ;
      · exact hi;
    · exact fun τ => coverBase_projSingleton hLx.1 τ;
    · refine' ⟨ _, _, _ ⟩;
      · exact fun τ τ' i i' hi hi' hne => coverFloor_disjoint hLx.1 τ τ' i i' hi hi' hne;
      · exact fun τ i hi => coverErr_disjoint_floor hLx.1 τ hi;
      · apply coverErr_covers;
        · linarith;
        · exact_mod_cast ( by linarith [ show ( 0 : ℝ ) ≤ C2 * ( 3 * t ) * Real.log ( 2 / υ ) / δ by exact div_nonneg ( mul_nonneg ( mul_nonneg hC2pos.le ( by positivity ) ) ( Real.log_nonneg ( by rw [ le_div_iff₀ hυ0 ] ; linarith ) ) ) hδ0.le ] : ( 3 * t : ℝ ) ≤ ℓ );
        · intro p; exact_mod_cast ( by linarith [ hLx.2.1 p ] : ( Lx p : ℝ ) + t ≤ ℓ ) ;

end LamplighterStability.Dynamics