import Mathlib

/-!
# Cover-free families (the combinatorial core of Linial colour reduction)

A **Δ-cover-free family** indexed by a finite type `α` is an assignment
`S : α → Finset U` (with `U` finite) such that no `S i` is covered by the union of
`≤ Δ` other members:

`∀ i (J : Finset α), i ∉ J → J.card ≤ Δ → (S i \ J.biUnion S).Nonempty`.

The main result `exists_coverFree` constructs such a family with a *small*
universe, `|U| ≤ 4(Δ+1)²(log₂|α|+2)²`, via the classical Reed–Solomon
construction:

* identify the colours `α` injectively with polynomials of degree `≤ L`
  (`L = log₂|α| + 1`) over a finite field `𝔽_q` (there are `q^{L+1} > |α|` of them
  once `q ≥ 2`);
* take `S p = {(a, p(a)) : a ∈ 𝔽_q}`, a set of size `q`;
* two distinct degree-`≤L` polynomials agree in `≤ L` points, so `S i` meets any
  union of `≤ Δ` other `S j` in `≤ Δ·L < q` points (choosing the prime
  `q ∈ (Δ+1)(L+1), 2(Δ+1)(L+1)]` by Bertrand), leaving `S i` uncovered.

This is the only genuinely number-theoretic ingredient of the polynomial marker
lemma; everything downstream is a one-round local recolouring (`MarkerLinial`).
-/

namespace LamplighterStability.Dynamics

open Polynomial

/-- The polynomial `∑_{k≤L} (c k)·X^k` over `𝔽_q` attached to a coefficient
vector `c : Fin (L+1) → ZMod q`. -/
noncomputable def polOf (q L : ℕ) (c : Fin (L + 1) → ZMod q) : (ZMod q)[X] :=
  ∑ k : Fin (L + 1), Polynomial.C (c k) * Polynomial.X ^ (k : ℕ)

/-
The `k`-th coefficient of `polOf` is `c k`.
-/
lemma polOf_coeff (q L : ℕ) (c : Fin (L + 1) → ZMod q) (k : Fin (L + 1)) :
    (polOf q L c).coeff (k : ℕ) = c k := by
  -- The coefficient of $X^k$ in the polynomial $\sum_{j=0}^{L} c_j X^j$ is $c_k$.
  simp [polOf];
  simp +decide [ Finset.sum_ite_eq, Fin.val_inj ]

/-
`polOf` has degree `≤ L`.
-/
lemma polOf_natDegree_le (q L : ℕ) (c : Fin (L + 1) → ZMod q) :
    (polOf q L c).natDegree ≤ L := by
  exact le_trans ( Polynomial.natDegree_sum_le _ _ ) ( Finset.sup_le fun i hi => Polynomial.natDegree_C_mul_X_pow_le _ _ |> le_trans <| Nat.le_of_lt_succ <| Fin.is_lt i )

/-
`polOf` is injective in its coefficient vector.
-/
lemma polOf_injective (q L : ℕ) : Function.Injective (polOf q L) := by
  intro c c' h_eq
  ext k;
  replace h_eq := congr_arg ( fun p => p.coeff k ) h_eq ; simp_all +decide [ polOf_coeff ] ;

/-
Two distinct degree-`≤L` polynomials agree in at most `L` points.
-/
lemma agree_card_le (q L : ℕ) [Fact (Nat.Prime q)]
    {c c' : Fin (L + 1) → ZMod q} (h : c ≠ c') :
    (Finset.univ.filter
        (fun a : ZMod q => (polOf q L c).eval a = (polOf q L c').eval a)).card ≤ L := by
  refine' le_trans _ ( Nat.le_of_lt_succ _ );
  convert Set.ncard_le_ncard ( show { a : ZMod q | eval a ( polOf q L c ) = eval a ( polOf q L c' ) } ⊆ ( ( polOf q L c - polOf q L c' ).roots.toFinset : Set ( ZMod q ) ) from ?_ ) using 1;
  · rw [ Set.ncard_eq_toFinset_card' ] ; aesop;
  · intro a ha; simp_all +decide [ sub_eq_iff_eq_add ] ;
    exact fun h' => h <| by simpa [ funext_iff ] using polOf_injective q L h';
  · rw [ Set.ncard_coe_finset ] ; exact lt_of_le_of_lt ( Multiset.toFinset_card_le _ ) ( lt_of_le_of_lt ( Polynomial.card_roots' _ ) ( Nat.lt_succ_of_le ( Polynomial.natDegree_sub_le _ _ |> le_trans <| max_le ( polOf_natDegree_le q L c ) ( polOf_natDegree_le q L c' ) ) ) )

/-- **Existence of a small cover-free family.**

For every finite type `α` of colours and degree bound `Δ`, there is a
Δ-cover-free family `S : α → Finset U` over a finite universe `U` of size
`≤ 4(Δ+1)²(log₂|α|+2)²`. -/
theorem exists_coverFree (α : Type) [Fintype α] [DecidableEq α] (Δ : ℕ) :
    ∃ (U : Type) (_ : Fintype U) (_ : DecidableEq U) (S : α → Finset U),
      Fintype.card U ≤ 4 * (Δ + 1) ^ 2 * (Nat.log 2 (Fintype.card α) + 2) ^ 2 ∧
      ∀ (i : α) (J : Finset α), i ∉ J → J.card ≤ Δ →
        (S i \ J.biUnion S).Nonempty := by
  by_contra! h_contra
  obtain ⟨q, hq_prime, hq_bounds⟩ : ∃ q : ℕ, Nat.Prime q ∧ (Δ + 1) * (Nat.log 2 (Fintype.card α) + 2) < q ∧ q ≤ 2 * (Δ + 1) * (Nat.log 2 (Fintype.card α) + 2) := by
    have := Nat.exists_prime_lt_and_le_two_mul ( ( Δ + 1 ) * ( Nat.log 2 ( Fintype.card α ) + 2 ) );
    simpa only [ mul_assoc ] using this ( by positivity );
  haveI := Fact.mk hq_prime; haveI := NeZero.of_gt hq_prime.pos
  obtain ⟨f⟩ : Nonempty (α ↪ (Fin (Nat.log 2 (Fintype.card α) + 1) → ZMod q)) := by
    have h_card : Fintype.card α ≤ q ^ (Nat.log 2 (Fintype.card α) + 1) := by
      exact le_trans ( Nat.le_of_lt ( Nat.lt_pow_succ_log_self ( by decide ) _ ) ) ( Nat.pow_le_pow_left ( by nlinarith [ hq_prime.two_le ] ) _ );
    exact Function.Embedding.nonempty_of_card_le ( by simpa [ ZMod.card ] using h_card )
  have hU_card : Fintype.card (ZMod q × ZMod q) ≤ 4 * (Δ + 1) ^ 2 * (Nat.log 2 (Fintype.card α) + 2) ^ 2 := by
    simp only [ Fintype.card_prod, ZMod.card ]; nlinarith [ hq_bounds.2 ]
  obtain ⟨ i, J, hij, hJ, h ⟩ := h_contra ( ZMod q × ZMod q ) inferInstance inferInstance
    ( fun i => Finset.image ( fun a : ZMod q => ( a, ( polOf q ( Nat.log 2 ( Fintype.card α ) ) ( f i ) ).eval a ) ) Finset.univ ) hU_card
  -- the marker construction's image set has card = q
  have hSi_card : (Finset.image ( fun a : ZMod q => ( a, ( polOf q ( Nat.log 2 ( Fintype.card α ) ) ( f i ) ).eval a ) ) Finset.univ).card = q := by
    rw [ Finset.card_image_of_injOn ( fun a _ b _ hab => by simpa using congrArg Prod.fst hab ) ]
    simp [ ZMod.card ]
  -- S i ⊆ union over J
  rw [ Finset.eq_empty_iff_forall_notMem ] at h
  have hsub : (Finset.image ( fun a : ZMod q => ( a, ( polOf q ( Nat.log 2 ( Fintype.card α ) ) ( f i ) ).eval a ) ) Finset.univ) ⊆
      J.biUnion ( fun j => (Finset.image ( fun a : ZMod q => ( a, ( polOf q ( Nat.log 2 ( Fintype.card α ) ) ( f j ) ).eval a ) ) Finset.univ) ∩ (Finset.image ( fun a : ZMod q => ( a, ( polOf q ( Nat.log 2 ( Fintype.card α ) ) ( f i ) ).eval a ) ) Finset.univ) ) := by
    intro x hx
    have := h x; simp only [ Finset.mem_sdiff, not_and, not_not ] at this
    have hmem := this hx
    rw [ Finset.mem_biUnion ] at hmem ⊢
    obtain ⟨ j, hjJ, hxj ⟩ := hmem
    exact ⟨ j, hjJ, Finset.mem_inter.2 ⟨ hxj, hx ⟩ ⟩
  -- each intersection has card ≤ L
  have hinter : ∀ j ∈ J, ((Finset.image ( fun a : ZMod q => ( a, ( polOf q ( Nat.log 2 ( Fintype.card α ) ) ( f j ) ).eval a ) ) Finset.univ) ∩ (Finset.image ( fun a : ZMod q => ( a, ( polOf q ( Nat.log 2 ( Fintype.card α ) ) ( f i ) ).eval a ) ) Finset.univ)).card ≤ Nat.log 2 (Fintype.card α) := by
    intro j hjJ
    refine le_trans ?_ (agree_card_le q ( Nat.log 2 ( Fintype.card α ) ) ( show f j ≠ f i from fun hh => hij ( by have := f.injective hh; subst this; exact hjJ )))
    refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
    · intro x hx
      rw [ Finset.mem_coe ] at hx
      simp only [ Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and ] at hx
      obtain ⟨ ⟨ a, ha ⟩, ⟨ b, hb ⟩ ⟩ := hx
      subst ha
      simp only [ Prod.mk.injEq ] at hb
      obtain ⟨ hb1, hb2 ⟩ := hb
      subst hb1
      simp only [ Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and ]
      exact hb2.symm
    · intro x hx y hy hxy
      rw [ Finset.mem_coe ] at hx hy
      simp only [ Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and ] at hx hy
      obtain ⟨ ⟨ a, ha ⟩, _ ⟩ := hx
      obtain ⟨ ⟨ b, hb ⟩, _ ⟩ := hy
      subst ha; subst hb
      simp only at hxy ⊢; rw [ hxy ]
  have hfinal : q ≤ J.card * Nat.log 2 (Fintype.card α) := by
    calc q = (Finset.image ( fun a : ZMod q => ( a, ( polOf q ( Nat.log 2 ( Fintype.card α ) ) ( f i ) ).eval a ) ) Finset.univ).card := hSi_card.symm
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ∑ j ∈ J, _ := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ J, Nat.log 2 (Fintype.card α) := Finset.sum_le_sum hinter
      _ = J.card * Nat.log 2 (Fintype.card α) := by rw [ Finset.sum_const, smul_eq_mul ]
  nlinarith [ hq_bounds.1, hJ, Nat.log 2 (Fintype.card α), Nat.mul_le_mul_right (Nat.log 2 (Fintype.card α)) hJ ]

/-- **`Fin`-indexed cover-free family.**  The same as `exists_coverFree` but with
both the colour index and the universe presented as `Fin _`, which is convenient
for iterating the reduction (the universe carries a `LinearOrder`). -/
theorem exists_coverFree_fin (C Δ : ℕ) :
    ∃ (M : ℕ) (S : Fin C → Finset (Fin M)),
      M ≤ 4 * (Δ + 1) ^ 2 * (Nat.log 2 C + 2) ^ 2 ∧
      ∀ (i : Fin C) (J : Finset (Fin C)), i ∉ J → J.card ≤ Δ →
        (S i \ J.biUnion S).Nonempty := by
  obtain ⟨U, instFin, instDec, S, hcard, hcf⟩ := exists_coverFree (Fin C) Δ
  classical
  refine ⟨Fintype.card U, fun c => (S c).image (Fintype.equivFin U), ?_, ?_⟩
  · simpa using hcard
  · intro i J hiJ hJ
    obtain ⟨u, hu⟩ := hcf i J hiJ hJ
    refine ⟨Fintype.equivFin U u, ?_⟩
    rw [Finset.mem_sdiff] at hu ⊢
    obtain ⟨huS, huN⟩ := hu
    refine ⟨Finset.mem_image_of_mem _ huS, ?_⟩
    intro hcontra
    rw [Finset.mem_biUnion] at hcontra
    obtain ⟨j, hjJ, hju⟩ := hcontra
    rw [Finset.mem_image] at hju
    obtain ⟨v, hvS, hve⟩ := hju
    have : v = u := (Fintype.equivFin U).injective hve
    subst this
    exact huN (Finset.mem_biUnion.2 ⟨j, hjJ, hvS⟩)

end LamplighterStability.Dynamics