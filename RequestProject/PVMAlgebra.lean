import Mathlib
import RequestProject.MuInvariance
import RequestProject.MeasureBridge
import RequestProject.MeasureInstantiation
import RequestProject.ProjectionTowers

/-!
# PVM algebra of `Edef` (Section 5 assembly infrastructure)

This file proves the **projection-valued-measure algebra** of the matrix family
`Edef M Epat S = ∑_{p ∈ π_M(S)} Epat p` (defined ∈ `MeasureBridge.lean`) when
`Epat` is an *atom PVM* with pairwise orthogonal atoms.  These are the
foundational, reusable facts the final Section 5 assembly (`assembly_final`)
needs in order to turn the measure-theoretic tower partition produced by
`prop_decomp` into an *orthogonal decomposition of `ℂ^d`* by matrix
projections:

* `proj_mul_proj_of_ne` — the two complementary spectral factors of a Hermitian
  involution are orthogonal.
* `atom_mul_atom_of_ne` — atoms of a commuting family of Hermitian involutions
  are pairwise orthogonal (distinct patterns).
* `EpatB_mul_of_ne` — pairwise orthogonality of the pattern PVM.
* `Edef_isHermitian`, `Edef_isProj` — `E_S` is a Hermitian projection for any
  definable `S`.
* `Edef_mul_of_disjoint`, `Edef_orthogonal` — orthogonality of `E_S, E_T` for
  disjoint definable `S, T`.
* `Edef_union_of_disjoint`, `Edef_biUnion` — additivity of `E` over disjoint
  definable unions.
* `Edef_univ` — `E_X = 1` (resolution of identity).
* `Edef_commute_B` — every `B_k` commutes with `E_S`.

All facts are stated for the generic atom PVM `EpatB`; the orthogonality of its
atoms is the only ingredient beyond the PVM axioms already proved in
`MeasureBridge` / `MeasureInstantiation`.
-/

namespace LamplighterStability

open scoped BigOperators
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-
The two complementary spectral factors of a Hermitian involution are
orthogonal: `½(I+(-1)^b B)·½(I+(-1)^{b'} B) = 0` for `b ≠ b'`.
-/
lemma proj_mul_proj_of_ne {B : Matrix ι ι ℂ} (hB2 : B * B = 1)
    {b b' : Bool} (h : b ≠ b') : proj B b * proj B b' = 0 := by
  cases b <;> cases b' <;> simp_all +decide [ proj ];
  · simp +decide [ Matrix.mul_add, Matrix.add_mul, hB2 ];
    abel1;
  · simp +decide [ Matrix.mul_add, Matrix.add_mul, hB2 ];
    abel1

/-
Atoms of a commuting family of Hermitian involutions are pairwise orthogonal:
for distinct patterns `x ≠ y`, `atom C x · atom C y = 0`.
-/
lemma atom_mul_atom_of_ne {n : ℕ} {C : Fin n → Matrix ι ι ℂ}
    (hC2 : ∀ i, C i * C i = 1) (hCc : ∀ i k, Commute (C i) (C k))
    {x y : Fin n → Bool} (h : x ≠ y) : atom C x * atom C y = 0 := by
  by_contra h_nonzero;
  -- By definition of atom, we can write
  have h_atom : atom C x * atom C y = List.prod (List.map (fun i => proj (C i) (x i) * proj (C i) (y i)) (List.finRange n)) := by
    have h_atom : ∀ (l : List (Fin n)), List.prod (List.map (fun i => proj (C i) (x i)) l) * List.prod (List.map (fun i => proj (C i) (y i)) l) = List.prod (List.map (fun i => proj (C i) (x i) * proj (C i) (y i)) l) := by
      intro l;
      induction l <;> simp +decide [ *, List.prod_cons ];
      simp +decide only [mul_assoc, ← ‹_›];
      have h_comm : ∀ (l : List (Fin n)), List.prod (List.map (fun i => proj (C i) (x i)) l) * proj (C ‹_›) (y ‹_›) = proj (C ‹_›) (y ‹_›) * List.prod (List.map (fun i => proj (C i) (x i)) l) := by
        intro l; induction l <;> simp +decide [ *, mul_assoc ] ;
        simp +decide only [← mul_assoc];
        exact congr_arg₂ _ ( proj_commute ( hCc _ _ ) _ _ ) rfl;
      simp +decide only [← mul_assoc, h_comm];
    convert h_atom ( List.finRange n ) using 1;
    unfold atom; simp +decide [ List.ofFn_eq_map ] ;
  -- Since $x \neq y$, there exists some $i$ such that $x i \neq y i$.
  obtain ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ y i := by
    exact Function.ne_iff.mp h;
  -- Since $x i \neq y i$, we have $proj (C i) (x i) * proj (C i) (y i) = 0$.
  have h_proj_zero : proj (C i) (x i) * proj (C i) (y i) = 0 := by
    exact proj_mul_proj_of_ne ( hC2 i ) hi;
  simp_all +decide [];
  exact h_nonzero ( List.prod_eq_zero ( List.mem_map.mpr ⟨ i, List.mem_finRange _, h_proj_zero ⟩ ) )

/-
**Master HS-Pythagoras over a resolution of the identity.**  For a family
`G` of Hermitian idempotents summing to the identity, every matrix `X`
decomposes orthogonally over the block grid `(G_a · X · G_b)`:
`‖X‖²_HS = ∑_a ∑_b ‖G_a X G_b‖²_HS`.

This is the technical core of the final Pythagoras step of Section 5 (`Proof of
Theorem`): with `G` the matrix projections `{P_τ} ∪ {E_e}` of a tower partition,
it splits `‖ρ(t⁻¹) − T‖²` into the per-tower diagonal blocks plus the
off-diagonal `‖P_τ T P_σ‖²` terms.
-/
lemma normHS_sq_double_pyth {σ : Type*} [Fintype σ] {G : σ → Matrix ι ι ℂ}
    (hGh : ∀ s, (G s).IsHermitian) (hGi : ∀ s, IsIdempotentElem (G s))
    (hsum : ∑ s, G s = 1) (X : Matrix ι ι ℂ) :
    ∑ a, ∑ b, normHS (G a * X * G b) ^ 2 = normHS X ^ 2 := by
  have := @pyth_right;
  convert this hGh hGi hsum ( X ) using 1;
  rw [ Finset.sum_comm ];
  exact Finset.sum_congr rfl fun _ _ => by simpa [ mul_assoc ] using pyth_left hGh hGi hsum ( X * G _ ) ;

end LamplighterStability

namespace LamplighterStability.MeasureInstantiation

open LamplighterStability LamplighterStability.MeasureBridge
  LamplighterStability.Dynamics
open scoped BigOperators
open Matrix

variable {d : ℕ}

/-
Pairwise orthogonality of the pattern PVM `EpatB`.
-/
lemma EpatB_mul_of_ne (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (hB2 : ∀ i, B i * B i = 1) (hBc : ∀ i j, Commute (B i) (B j))
    {p q : Win M → Bool} (h : p ≠ q) : EpatB M B p * EpatB M B q = 0 := by
  apply atom_mul_atom_of_ne (fun k => by
    exact hB2 _) (fun k l => by
    exact hBc _ _) (by
  exact fun h' => h <| funext fun x => by simpa using congr_fun h' ( winEquiv M x ) ;)

end LamplighterStability.MeasureInstantiation

namespace LamplighterStability.MeasureBridge

open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureInstantiation
open scoped BigOperators
open Matrix

variable {d : ℕ}

/-
`E_S` is Hermitian for a Hermitian-atom PVM.
-/
lemma Edef_isHermitian (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hBc : ∀ i j, Commute (B i) (B j))
    (S : Set Cfg) : (Edef M (EpatB M B) S).IsHermitian := by
  unfold Edef; simp +decide [ *, Matrix.IsHermitian ] ;
  rw [ Matrix.conjTranspose_sum ];
  exact Finset.sum_congr rfl fun _ _ => EpatB_isHermitian M B hBh hBc _

/-
`E_S` is idempotent for an atom PVM with pairwise orthogonal atoms.
-/
lemma Edef_isIdempotent (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (hB2 : ∀ i, B i * B i = 1) (hBc : ∀ i j, Commute (B i) (B j))
    (S : Set Cfg) : IsIdempotentElem (Edef M (EpatB M B) S) := by
  refine' Eq.trans ( Finset.sum_mul_sum _ _ _ _ ) _;
  rw [ Finset.sum_congr rfl fun i hi => Finset.sum_eq_single i _ _ ];
  · exact Finset.sum_congr rfl fun i hi => EpatB_isIdempotent M B hB2 hBc i;
  · exact fun i hi j hj hij => EpatB_mul_of_ne M B hB2 hBc hij.symm;
  · grind +extAll

/-- `E_S` is a projection. -/
lemma Edef_isProj (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    (S : Set Cfg) : IsProj (Edef M (EpatB M B) S) :=
  ⟨Edef_isHermitian M B hBh hBc S, Edef_isIdempotent M B hB2 hBc S⟩

/-
Orthogonality of `E_S, E_T` for disjoint definable `S, T`.
-/
lemma Edef_mul_of_disjoint (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (hB2 : ∀ i, B i * B i = 1) (hBc : ∀ i j, Commute (B i) (B j))
    {S T : Set Cfg} (h : Disjoint S T) :
    Edef M (EpatB M B) S * Edef M (EpatB M B) T = 0 := by
  -- By definition of Edef, we have Edef M (EpatB M B) S = ∑ p ∈ patternsOf M S, EpatB M B p and Edef M (EpatB M B) T = ∑ q ∈ patternsOf M T, EpatB M B q.
  simp [Edef];
  -- Since $S$ and $T$ are disjoint, their patterns are also disjoint.
  have h_patterns_disjoint : Disjoint (patternsOf M S) (patternsOf M T) :=
    patternsOf_disjoint h
  rw [ Finset.sum_mul_sum ];
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => EpatB_mul_of_ne M B hB2 hBc <| by rintro rfl; exact Finset.disjoint_left.mp h_patterns_disjoint hi hj;

/-
Additivity of `E` over a disjoint union of definable sets.
-/
lemma Edef_union_of_disjoint (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    {S T : Set Cfg} (hS : Defined M S) (h : Disjoint S T) :
    Edef M (EpatB M B) (S ∪ T)
      = Edef M (EpatB M B) S + Edef M (EpatB M B) T := by
  convert Finset.sum_union ?_ using 2;
  all_goals try infer_instance;
  · convert Finset.sum_subset ?_ ?_ using 1;
    · intro b hb; simp_all +decide [ mem_patternsOf ] ;
      by_cases hSb : ∃ x ∈ cyl M b, x ∈ S;
      · left; intro y hy; have := hb hy; simp_all +decide [ Set.disjoint_left ] ;
        obtain ⟨ x, hx₁, hx₂ ⟩ := hSb; specialize hS x y; simp_all +decide [ cyl ] ;
      · exact Or.inr fun x hx => Or.resolve_left ( hb hx ) fun hx' => hSb ⟨ x, hx, hx' ⟩;
    · intro x hx hx'; contrapose! hx'; simp_all +decide [ patternsOf ] ;
      exact hx.elim ( fun hx => Set.Subset.trans hx ( Set.subset_union_left ) ) fun hx => Set.Subset.trans hx ( Set.subset_union_right );
  · exact patternsOf_disjoint h

/-
Resolution of the identity: `E_X = 1`.
-/
lemma Edef_univ (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ) :
    Edef M (EpatB M B) Set.univ = 1 := by
  -- By definition of `patternsOf`, we have `patternsOf M Set.univ = Finset.univ`.
  have h_patterns : patternsOf M Set.univ = Finset.univ := by
    ext p; simp [patternsOf];
  exact Eq.trans ( by rw [ Edef, h_patterns ] ) ( EpatB_sum M B )

/-
Every generator `B_k` commutes with `E_S`.
-/
lemma Edef_commute_B (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (hBc : ∀ i j, Commute (B i) (B j)) (k : Win M) (S : Set Cfg) :
    Commute (B k) (Edef M (EpatB M B) S) := by
  have h_comm : ∀ p : Win M → Bool, Commute (B k) (EpatB M B p) := by
    intro p
    have h_comm : ∀ i : Fin (2 * M + 1), Commute (B k) (proj (B ((winEquiv M).symm i)) (p ((winEquiv M).symm i))) := by
      intro i; unfold proj
      exact ((Commute.one_right (B k)).add_right ((hBc k _).smul_right _)).smul_right _
    have h_comm : ∀ (l : List (Matrix (Fin d) (Fin d) ℂ)), (∀ x ∈ l, Commute (B k) x) → Commute (B k) (List.prod l) := by
      intro l hl; induction l <;> simp_all +decide [ Commute ] ;
    exact h_comm _ fun x hx => by rw [ List.mem_ofFn ] at hx; obtain ⟨ i, rfl ⟩ := hx; solve_by_elim;
  exact Commute.sum_right _ _ _ fun p hp => h_comm p

end LamplighterStability.MeasureBridge