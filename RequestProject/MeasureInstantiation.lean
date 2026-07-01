import Mathlib
import RequestProject.Foundations
import RequestProject.MuInvariance
import RequestProject.Dynamics.ApproxInvMeasure
import RequestProject.MeasureBridge

/-!
# Instantiating the PVM measure from commuting involutions (Section 5, step 1)

This file performs the measure-side instantiation needed by the final assembly
(`assembly_final`).  From a finite family `B : Win M → Matrix` of pairwise
commuting Hermitian involutions (the "atom" generators), it:

* builds the pattern PVM `EpatB M B p = ∏_i ½(I + (-1)^{p i} B_i)` (an ordered
  atom over the window `F_M = [-M,M]`), and verifies its PVM axioms (Hermitian /
  idempotent / resolution of identity);
* computes its *marginalizations* over `(M-1)`-cylinders and their shifts in
  terms of plain `atom`s of consecutive sub-families (`Edef_cyl_eq`,
  `Edef_Lcyl_eq`);
* concludes that the induced measure `pvmMeasure M (EpatB M B)` is
  `(M-1, η)`-approximately invariant, with `η` controlled by the matrix
  equivariance defect `∑_j ‖T* B_j T − B_{j+1}‖²` via `mu_invariance_measure`.

This is exactly the `ApproxInvMeasure` input consumed by `prop_decomp`.
-/

namespace LamplighterStability.MeasureInstantiation

open MeasureTheory
open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureBridge
open scoped BigOperators ENNReal

variable {d : ℕ}

/-! ## Window ↔ `Fin` reindexing -/

/-- Order isomorphism `Win M ≃ Fin (2M+1)` sending coordinate `i ∈ [-M,M]` to
`(i+M)`.  The atom factors are then listed in coordinate order `-M, …, M`. -/
def winEquiv (M : ℕ) : Win M ≃ Fin (2 * M + 1) where
  toFun i := ⟨(i.1 + M).toNat, by
    have := i.2; rw [Finset.mem_Icc] at this; omega⟩
  invFun k := ⟨(k : ℤ) - M, by
    have := k.2; rw [Finset.mem_Icc]; constructor <;> omega⟩
  left_inv := by
    intro i; have := i.2; rw [Finset.mem_Icc] at this
    apply Subtype.ext; simp; omega
  right_inv := by
    intro k; have := k.2; apply Fin.ext; simp only; omega

/-! ## The pattern PVM -/

/-- The pattern PVM: the ordered atom of the `B`-family, indexed by window
patterns. -/
noncomputable def EpatB (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (p : Win M → Bool) : Matrix (Fin d) (Fin d) ℂ :=
  atom (fun k : Fin (2 * M + 1) => B ((winEquiv M).symm k))
    (fun k => p ((winEquiv M).symm k))

lemma EpatB_isHermitian (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hBc : ∀ i j, Commute (B i) (B j))
    (p : Win M → Bool) : (EpatB M B p).IsHermitian :=
  atom_isHermitian (fun _ => hBh _) (fun _ _ => hBc _ _) _

lemma EpatB_isIdempotent (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (hB2 : ∀ i, B i * B i = 1) (hBc : ∀ i j, Commute (B i) (B j))
    (p : Win M → Bool) : IsIdempotentElem (EpatB M B p) :=
  atom_isIdempotent (fun _ => hB2 _) (fun _ _ => hBc _ _) _

lemma EpatB_sum (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ) :
    ∑ p : Win M → Bool, EpatB M B p = 1 := by
  convert sum_atom_eq_one ( fun k => B ( winEquiv M |> Equiv.symm |> fun e => e k ) ) using 1;
  refine' Finset.sum_bij ( fun p hp => fun k => p ( winEquiv M |> Equiv.symm |> fun e => e k ) ) _ _ _ _ <;> simp +decide [ EpatB ];
  · exact fun a₁ a₂ h => funext fun x => by simpa using congr_fun h ( winEquiv M x ) ;
  · exact fun b => ⟨ fun k => b ( winEquiv M k ), by ext; simp +decide ⟩

/-! ## Marginalization helper lemmas on atoms -/

/-
Summing the first atom factor's bit collapses it to the identity:
`∑_{b₀} atom C (cons b₀ x) = atom (C ∘ succ) x`.
-/
lemma sum_atom_cons {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (C : Fin (n + 1) → Matrix ι ι ℂ) (x : Fin n → Bool) :
    ∑ b0 : Bool, atom C (Fin.cons b0 x) = atom (fun i => C i.succ) x := by
  simp +decide [ atom ];
  rw [ ← add_mul, proj_add, one_mul ]

/-
Summing the last atom factor's bit collapses it to the identity:
`∑_{bₗ} atom C (snoc x bₗ) = atom (C ∘ castSucc) x`.
-/
lemma sum_atom_snoc {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (C : Fin (n + 1) → Matrix ι ι ℂ) (x : Fin n → Bool) :
    ∑ bl : Bool, atom C (Fin.snoc x bl) = atom (fun i => C i.castSucc) x := by
  -- By definition of `atom`, we can split the product into the product of the first `n` elements and the last element.
  have h_atom_split : ∀ (bl : Bool), atom C (Fin.snoc x bl) = atom (fun i => C i.castSucc) x * proj (C (Fin.last n)) bl := by
    unfold atom;
    intro bl; rw [ List.ofFn_succ' ] ; simp +decide [ Fin.snoc ] ;
  simp +decide [ h_atom_split ];
  rw [ ← mul_add, proj_add, mul_one ]

/-! ## Marginalization of the PVM over `(M-1)`-cylinders -/

/-- The middle sub-family of `B`, indexed by `Fin (2m+2)` over coordinates
`[-m, m+1]`. -/
noncomputable def Bmid (m : ℕ) (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ) :
    Fin (2 * m + 2) → Matrix (Fin d) (Fin d) ℂ :=
  fun k => B ⟨(k : ℤ) - m, by
    rw [Finset.mem_Icc]; have := k.2; push_cast; constructor <;> omega⟩

/-- The interior pattern `b : Win m → Bool` re-indexed to `Fin (2m+1)`. -/
def bvec (m : ℕ) (b : Win m → Bool) : Fin (2 * m + 1) → Bool :=
  fun k => b ((winEquiv m).symm k)

/-
**Marginalization over a cylinder.**  Summing the PVM over all window
patterns extending `b` (free endpoints `±(m+1)`) recovers the interior atom of
the sub-family `Bmid ∘ castSucc` (coordinates `[-m, m-1+1] = [-m, m]`).
-/
lemma Edef_cyl_eq (m : ℕ) (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (b : Win m → Bool) :
    Edef (m + 1) (EpatB (m + 1) B) (cyl m b)
      = atom (fun k => Bmid m B k.castSucc) (bvec m b) := by
  -- By definition of `patternsOf`, we know that `patternsOf (m + 1) (cyl m b)` is the set of all sequences that extend `b`.
  have h_patternsOf : patternsOf (m + 1) (cyl m b) = {p : Win (m + 1) → Bool | ∀ i : Win m, p ⟨i.1, by
    grind +qlia⟩ = b i} := by
    ext p; simp [patternsOf, cyl];
    constructor;
    · intro hp a ha hb
      obtain ⟨x, hx⟩ : ∃ x : Cfg, Dynamics.proj (m + 1) x = p := by
        exact ⟨ sect ( m + 1 ) p, proj_sect _ _ ⟩
      generalize_proofs at *;
      convert congr_fun ( hp x hx ) ⟨ a, by assumption ⟩ using 1;
      exact hx ▸ rfl;
    · intro hp a ha; ext i; specialize hp i.1 ( by linarith [ i.2 |> Finset.mem_Icc.mp |> And.left ] ) ( by linarith [ i.2 |> Finset.mem_Icc.mp |> And.right ] ) ; aesop;
  generalize_proofs at *;
  have h_sum : ∑ p ∈ Finset.univ.filter (fun p : Fin (2 * m + 3) → Bool => ∀ i : Fin (2 * m + 1), p (Fin.succ (Fin.castSucc i)) = bvec m b i), atom (fun k => B ((winEquiv (m + 1)).symm k)) p = atom (fun k => Bmid m B k.castSucc) (bvec m b) := by
    have h_sum : ∑ p ∈ Finset.univ.filter (fun p : Fin (2 * m + 3) → Bool => ∀ i : Fin (2 * m + 1), p (Fin.succ (Fin.castSucc i)) = bvec m b i), atom (fun k => B ((winEquiv (m + 1)).symm k)) p = ∑ lo : Bool, ∑ hi : Bool, atom (fun k => B ((winEquiv (m + 1)).symm k)) (Fin.cons lo (Fin.snoc (bvec m b) hi)) := by
      rw [ ← Finset.sum_product' ];
      refine' Finset.sum_bij ( fun p hp => ( p 0, p ( Fin.last _ ) ) ) _ _ _ _ <;> simp +decide [];
      · intro a₁ ha₁ a₂ ha₂ h₀ h₁; ext i; induction i using Fin.inductionOn <;> simp_all +decide [ Fin.last ] ;
        rename_i i hi;
        induction i using Fin.lastCases <;> simp_all +decide [ Fin.castSucc, Fin.succ ];
      · refine' ⟨ ⟨ _, _ ⟩, ⟨ _, _ ⟩ ⟩;
        · refine' ⟨ Fin.cons false ( Fin.snoc ( bvec m b ) false ), _, _, _ ⟩ <;> simp +decide [ Fin.cons ];
          simp +decide [ Fin.last, Fin.snoc ];
        · refine' ⟨ Fin.cons false ( Fin.snoc ( bvec m b ) true ), _, _, _ ⟩ <;> simp +decide [ Fin.cons ];
          simp +decide [ Fin.last, Fin.snoc ];
        · refine' ⟨ Fin.cons true ( Fin.snoc ( bvec m b ) false ), _, _, _ ⟩ <;> simp +decide [ Fin.cons ];
          simp +decide [ Fin.last, Fin.snoc ];
        · refine' ⟨ Fin.cons true ( Fin.snoc ( bvec m b ) true ), _, _, _ ⟩ <;> simp +decide [ Fin.cons ];
          simp +decide [ Fin.last, Fin.snoc ];
      · intro a ha; congr; ext i; induction i using Fin.inductionOn <;> simp_all +decide [ Fin.cons ] ;
        rename_i i hi;
        induction i using Fin.lastCases <;> simp_all +decide [ Fin.snoc ];
        grind +qlia;
    rw [ h_sum, Finset.sum_comm ];
    rw [ Finset.sum_congr rfl fun _ _ => sum_atom_cons _ _ ];
    convert sum_atom_snoc _ _ using 3;
    unfold Bmid winEquiv; simp +decide [] ;
  convert h_sum using 1;
  apply Finset.sum_bij (fun p hp => fun k => p ((winEquiv (m + 1)).symm k));
  · simp_all +decide [ Set.ext_iff, mem_patternsOf ];
    intro p hp i; specialize hp ( i - m ) ( by linarith [ Fin.is_lt i ] ) ( by linarith [ Fin.is_lt i ] ) ; simp_all +decide [ winEquiv, bvec ] ;
  · simp +contextual [ funext_iff, winEquiv ];
    intro a₁ ha₁ a₂ ha₂ h a ha₁' ha₂'; specialize h ⟨ Int.toNat ( a + m + 1 ), by omega ⟩ ; simp_all +decide [ Int.toNat_of_nonneg ( by linarith : 0 ≤ a + m + 1 ) ] ;
  · intro p hp; use fun k => p (winEquiv (m + 1) k); simp_all +decide [ Set.ext_iff ] ;
    refine' ⟨ _, _ ⟩;
    · intro a ha hb; convert hp ⟨ Int.toNat ( a + m ), by omega ⟩ using 1; simp +decide [ winEquiv ] ;
      · congr 2 ; omega;
      · unfold bvec; simp +decide [ winEquiv ] ;
        grind;
    · exact funext fun x => by simp +decide [ winEquiv ] ;
  · exact fun _ _ => rfl

/-
**Marginalization over a shifted cylinder.**  Summing the PVM over all window
patterns whose `L`-preimage extends `b` recovers the interior atom of the
sub-family `Bmid ∘ succ` (coordinates `[-m+1, m+1]`).
-/
set_option maxHeartbeats 1000000 in
lemma Edef_Lcyl_eq (m : ℕ) (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (b : Win m → Bool) :
    Edef (m + 1) (EpatB (m + 1) B) ((L : Equiv.Perm Cfg) '' cyl m b)
      = atom (fun k => Bmid m B k.succ) (bvec m b) := by
  unfold Edef; simp_all +decide [ Set.image ] ;
  rw [ show { x : Cfg | ∃ a ∈ cyl m b, L a = x } = { x : Cfg | ∀ i : Win m, x ( i.1 + 1 ) = b i } from ?_ ];
  · have h_patternsOf : patternsOf (m + 1) {x : Cfg | ∀ i : Win m, x (i.1 + 1) = b i} = {p : Win (m + 1) → Bool | ∀ i : Win m, p ⟨i.1 + 1, by
      grind +splitIndPred⟩ = b i} := by
      all_goals generalize_proofs at *;
      ext p; simp [patternsOf ];
      constructor <;> intro h a ha₁ ha₂;
      · convert h ( show sect ( m + 1 ) p ∈ cyl ( m + 1 ) p from ?_ ) a ha₁ ha₂ using 1
        generalize_proofs at *;
        · unfold sect; aesop;
        · exact funext fun i => by simp +decide [ proj_sect ] ;
      · intro hp hq; specialize h ha₂ hp hq; simp_all +decide [ cyl ] ;
        convert h using 1;
        exact ha₁ ▸ rfl
    generalize_proofs at *;
    have h_sum : ∑ p ∈ Finset.univ.filter (fun p : Fin (2 * m + 3) → Bool => ∀ i : Fin (2 * m + 1), p (Fin.succ (Fin.succ i)) = bvec m b i), atom (fun k => B ((winEquiv (m + 1)).symm k)) p = atom (fun k => Bmid m B k.succ) (bvec m b) := by
      have h_sum : ∑ p ∈ Finset.univ.filter (fun p : Fin (2 * m + 3) → Bool => ∀ i : Fin (2 * m + 1), p (Fin.succ (Fin.succ i)) = bvec m b i), atom (fun k => B ((winEquiv (m + 1)).symm k)) p = ∑ lo : Bool, ∑ hi : Bool, atom (fun k => B ((winEquiv (m + 1)).symm k)) (Fin.cons lo (Fin.cons hi (bvec m b))) := by
        rw [ ← Finset.sum_product' ];
        refine' Finset.sum_bij ( fun p hp => ( p 0, p 1 ) ) _ _ _ _ <;> simp +decide [];
        · intro a₁ ha₁ a₂ ha₂ h₀ h₁; ext i; induction i using Fin.inductionOn <;> simp_all +decide ;
          rename_i i hi;
          induction i using Fin.inductionOn <;> simp_all +decide [ Fin.castSucc ];
        · refine' ⟨ ⟨ ⟨ Fin.cons false ( Fin.cons false ( bvec m b ) ), _, _, _ ⟩, ⟨ Fin.cons false ( Fin.cons true ( bvec m b ) ), _, _, _ ⟩ ⟩, ⟨ ⟨ Fin.cons true ( Fin.cons false ( bvec m b ) ), _, _, _ ⟩, ⟨ Fin.cons true ( Fin.cons true ( bvec m b ) ), _, _, _ ⟩ ⟩ ⟩ <;> simp +decide [ Fin.cons ]; all_goals rfl;
        · intro a ha; congr; ext i; induction i using Fin.inductionOn <;> simp_all +decide [ Fin.cons ] ;
          induction ‹Fin ( 2 * m + 2 ) › using Fin.inductionOn <;> simp_all +decide [ Fin.cases ];
      rw [ h_sum, Finset.sum_comm ];
      rw [ Finset.sum_congr rfl fun _ _ => sum_atom_cons _ _ ];
      convert sum_atom_cons _ _ using 3;
      unfold Bmid winEquiv; simp +decide ;
    convert h_sum using 1;
    apply Finset.sum_bij (fun p hp => fun k => p ((winEquiv (m + 1)).symm k));
    · simp_all +decide [ Set.ext_iff ];
      intro a ha i; specialize ha ( i - m ) ( by linarith [ Fin.is_lt i ] ) ( by linarith [ Fin.is_lt i ] ) ; simp_all +decide [ winEquiv, bvec ] ;
      convert ha using 2 ; ring;
    · exact fun a₁ ha₁ a₂ ha₂ h => funext fun x => by simpa using congr_fun h ( winEquiv ( m + 1 ) x ) ;
    · intro p hp; use fun k => p (winEquiv (m + 1) k); simp_all +decide [ Set.ext_iff ] ;
      refine' ⟨ _, _ ⟩
      all_goals generalize_proofs at *;
      · intro a ha hb; specialize hp ⟨ Int.toNat ( a + m ), by omega ⟩ ; simp_all +decide [ winEquiv ] ;
        convert hp using 2 <;> ring;
        · exact Fin.ext ( by linarith [ Int.toNat_of_nonneg ( by linarith : 0 ≤ 2 + a + m ), Int.toNat_of_nonneg ( by linarith : 0 ≤ a + m ) ] );
        · unfold bvec; simp +decide [ winEquiv ] ;
          grind;
      · exact funext fun x => by simp +decide [ winEquiv ] ;
    · unfold EpatB; aesop;
  · ext x; simp [cyl, L];
    constructor <;> intro h;
    · obtain ⟨ a, rfl, rfl ⟩ := h; simp +decide [ Dynamics.proj, shiftMap ] ;
    · use fun i => x (i + 1);
      exact ⟨ funext fun i => h _ ( by linarith [ i.2 |> Finset.mem_Icc.mp |> And.left ] ) ( by linarith [ i.2 |> Finset.mem_Icc.mp |> And.right ] ), funext fun i => by simp +decide [ shiftMap ] ⟩

/-! ## The induced measure is approximately invariant -/

/-
**Final measure-side instantiation.**  The probability measure induced by
the PVM of a commuting family of Hermitian involutions `B` is
`(m, η)`-approximately invariant, with `η` controlled by the matrix equivariance
defect `∑_k ‖T* B_k T − B_{k+1}‖²` via `mu_invariance_measure`.
-/
theorem approxInvMeasure_EpatB (m : ℕ)
    {T : Matrix (Fin d) (Fin d) ℂ} (hT : T ∈ unitary (Matrix (Fin d) (Fin d) ℂ))
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hBh : ∀ i, (B i).IsHermitian) (hB2 : ∀ i, B i * B i = 1)
    (hBc : ∀ i j, Commute (B i) (B j))
    {η : ℝ}
    (hbound : ((2 * (m : ℝ) + 1) / 2) * ∑ k : Fin (2 * m + 1),
        normHS (star T * Bmid m B k.castSucc * T - Bmid m B k.succ) ^ 2 ≤ η) :
    ApproxInvMeasure m η (pvmMeasure (m + 1) (EpatB (m + 1) B)) := by
  apply MeasureBridge.approxInvMeasure_of_equiv (m + 1) (by omega) (EpatB (m + 1) B) (EpatB_isHermitian (m + 1) B hBh hBc) (EpatB_isIdempotent (m + 1) B hB2 hBc);
  convert hbound.trans' _ using 1;
  convert LamplighterStability.mu_invariance_measure hT ( Bmid m B ) ( fun i => hBh _ ) ( fun i => hB2 _ ) ( fun i j => hBc _ _ ) using 1;
  · refine' Finset.sum_bij ( fun x _ => fun k => x ( winEquiv m |> Equiv.symm |> fun e => e k ) ) _ _ _ _ <;> simp +decide [ Edef_Lcyl_eq, Edef_cyl_eq ];
    · exact fun a₁ a₂ h => funext fun x => by simpa using congr_fun h ( winEquiv m x ) ;
    · exact fun b => ⟨ fun k => b ( winEquiv m k ), by ext; simp +decide ⟩;
    · exact fun a => abs_sub_comm _ _;
  · norm_cast

end LamplighterStability.MeasureInstantiation