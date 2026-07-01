import Mathlib

/-!
# The full shift `X = {0,1}^ℤ` (Block B foundation)

This file sets up the dynamical model used in Sections 2.1 and 5 of the paper
*"Polynomial Hilbert–Schmidt stability of the lamplighter group"*: the full
(topological Bernoulli) shift over `ℤ`, cylinder sets, `n`-definability of clopen
sets, clopen towers, and periodic points.

We model a configuration as a function `ℤ → Bool` (a point of `{0,1}^ℤ`).  The
**right shift** is `(L x) i = x (i-1)`, packaged as an `Equiv.Perm` so that
integer powers `L^i` (`i : ℤ`) are available.

Everything here is elementary combinatorics / measure theory of cylinder sets;
the deep dynamical statements (marker lemmas, the tower decomposition
`prop:decomp`) are stated in the sibling files and ultimately consumed by the
final assembly.
-/

namespace LamplighterStability.Dynamics

open MeasureTheory

/-- A configuration of the full shift: a point of `{0,1}^ℤ`. -/
abbrev Cfg : Type := ℤ → Bool

/-- The right shift `(L x) i = x (i-1)`. -/
def shiftMap (x : Cfg) : Cfg := fun i => x (i - 1)

/-- The inverse shift `(L⁻¹ x) i = x (i+1)`. -/
def shiftMapInv (x : Cfg) : Cfg := fun i => x (i + 1)

/-- The right shift as a permutation of `Cfg`, so that integer powers are
available via the group structure of `Equiv.Perm`. -/
def L : Equiv.Perm Cfg where
  toFun := shiftMap
  invFun := shiftMapInv
  left_inv := by
    intro x; funext i; simp [shiftMap, shiftMapInv]
  right_inv := by
    intro x; funext i; simp [shiftMap, shiftMapInv]

@[simp] lemma L_apply (x : Cfg) (i : ℤ) : L x i = x (i - 1) := rfl
@[simp] lemma L_symm_apply (x : Cfg) (i : ℤ) : L.symm x i = x (i + 1) := rfl

/-- Window index set `F_n = [-n, n] ⊂ ℤ`. -/
abbrev Win (n : ℕ) : Type := {i : ℤ // i ∈ Finset.Icc (-(n : ℤ)) (n : ℤ)}

/-- Projection of a configuration onto the window `F_n`. -/
def proj (n : ℕ) (x : Cfg) : Win n → Bool := fun i => x i.1

/-- Cylinder set of a window pattern `b : Win n → Bool`. -/
def cyl (n : ℕ) (b : Win n → Bool) : Set Cfg := {x | proj n x = b}

/-- A set `S` is **`n`-defined** if membership depends only on the coordinates in
`F_n`. -/
def Defined (n : ℕ) (S : Set Cfg) : Prop :=
  ∀ x y : Cfg, proj n x = proj n y → (x ∈ S ↔ y ∈ S)

/-- `b` is **`F_j`-independent** if `b ∩ L^i b = ∅` for all `i ∈ F_j \ {0}`. -/
def FIndep (j : ℕ) (b : Set Cfg) : Prop :=
  ∀ i : ℤ, i ∈ Finset.Icc (-(j : ℤ)) (j : ℤ) → i ≠ 0 →
    Disjoint b ((L ^ i) '' b)

/-- The sets making up a clopen tower with base `b` and height `j`:
`b, Lb, …, L^{j-1} b`. -/
def towerFloor (b : Set Cfg) (i : ℕ) : Set Cfg := (L ^ (i : ℤ)) '' b

/-- The set `π_j(b)` is a singleton: all elements of `b` agree on the window
`F_j` (equivalently `b` is contained in a single `j`-cylinder). -/
def ProjSingleton (j : ℕ) (b : Set Cfg) : Prop :=
  ∃ p : Win j → Bool, b ⊆ cyl j p

/-- `b` is the base of a clopen tower of height `j`, i.e. the floors
`b, Lb, …, L^{j-1}b` are pairwise disjoint. -/
def IsTowerBase (j : ℕ) (b : Set Cfg) : Prop :=
  ∀ i i' : ℕ, i < j → i' < j → i ≠ i' →
    Disjoint (towerFloor b i) (towerFloor b i')

/-- A tower `Tow(b,j)` is **`δ`-closed** (w.r.t. a measure `μ`) if
`μ(L^j b ∩ b) ≥ (1-δ) μ(b)`. -/
def DeltaClosed (μ : Measure Cfg) (δ : ℝ) (j : ℕ) (b : Set Cfg) : Prop :=
  (1 - δ) * (μ b).toReal ≤ (μ ((L ^ (j : ℤ)) '' b ∩ b)).toReal

/-- `x` has period at most `t`: there is `1 ≤ s ≤ t` with `L^s x = x`. -/
def IsPerLe (t : ℕ) (x : Cfg) : Prop :=
  ∃ s : ℕ, 1 ≤ s ∧ s ≤ t ∧ shiftMap^[s] x = x

/-- `X_per(t)`: the set of points of period at most `t`. -/
def Xper (t : ℕ) : Set Cfg := {x | IsPerLe t x}


/-! ## Elementary facts -/

/-- Every configuration lies in the cylinder of its own projection. -/
@[simp] lemma mem_cyl_proj (n : ℕ) (x : Cfg) : x ∈ cyl n (proj n x) := rfl

lemma mem_cyl_iff (n : ℕ) (b : Win n → Bool) (x : Cfg) :
    x ∈ cyl n b ↔ proj n x = b := Iff.rfl

/-- Cylinder sets are measurable. -/
lemma measurableSet_cyl (n : ℕ) (b : Win n → Bool) : MeasurableSet (cyl n b) := by
  unfold cyl proj
  apply measurableSet_eq_fun <;> fun_prop

/-- Cylinder sets of distinct patterns are disjoint. -/
lemma cyl_disjoint {n : ℕ} {b b' : Win n → Bool} (h : b ≠ b') :
    Disjoint (cyl n b) (cyl n b') := by
  rw [Set.disjoint_left]
  rintro x hx hx'
  exact h (hx ▸ hx'.symm ▸ rfl)


/-- A cylinder set is `n`-defined. -/
lemma defined_cyl (n : ℕ) (b : Win n → Bool) : Defined n (cyl n b) := by
  intro x y hxy
  simp only [mem_cyl_iff, hxy]

/-- The empty set is `n`-defined. -/
lemma defined_empty (n : ℕ) : Defined n (∅ : Set Cfg) := by
  intro x y _; simp

/-- The whole space is `n`-defined. -/
lemma defined_univ (n : ℕ) : Defined n (Set.univ : Set Cfg) := by
  intro x y _; simp

@[simp] lemma towerFloor_eq (b : Set Cfg) (i : ℕ) :
    towerFloor b i = (L ^ (i : ℤ)) '' b := rfl

/-
Disjointness of two tower floors reduces to `F`-independence of the base:
`L^a b ∩ L^{a'} b = ∅ ⇔ b ∩ L^{a'-a} b = ∅`.
-/
lemma disjoint_shift_iff (b : Set Cfg) (a a' : ℤ) :
    Disjoint ((L ^ a) '' b) ((L ^ a') '' b) ↔ Disjoint b ((L ^ (a' - a)) '' b) := by
  convert Set.disjoint_image_iff ( show Function.Injective ( L ^ a ) from ?_ ) using 1;
  · rw [ ← Set.image_comp, ← Equiv.Perm.coe_mul ];
    rw [ ← zpow_add, add_sub_cancel ];
  · exact Equiv.injective _

/-
`b` is `F_{j-1}`-independent iff it is the base of a clopen tower of
height `j` (paper, Section 2.1).
-/
lemma isTowerBase_iff_fIndep (j : ℕ) (hj : 0 < j) (b : Set Cfg) :
    IsTowerBase j b ↔ FIndep (j - 1) b := by
  constructor <;> intro H <;> simp_all +decide [ IsTowerBase, FIndep ];
  · intros i hi1 hi2 hi3
    by_cases hi_pos : 0 < i;
    · convert H 0 ( Int.toNat i ) ( by linarith ) ( by linarith [ Int.toNat_of_nonneg hi_pos.le ] ) ( by linarith [ Int.toNat_of_nonneg hi_pos.le ] ) using 1 ; aesop;
      cases i <;> aesop;
    · rcases Int.eq_nat_or_neg i with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [];
      specialize H 0 k ; simp_all +decide [ Set.disjoint_left ];
      grind +qlia;
  · intro i i' hi hi' hne; specialize H ( i' - i ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
    convert disjoint_shift_iff b i i' |>.2 ( H ( by omega ) ( by omega ) ( Ne.symm hne ) ) using 1

end LamplighterStability.Dynamics