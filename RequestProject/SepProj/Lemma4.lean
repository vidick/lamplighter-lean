import RequestProject.SepProj.Defs

open scoped BigOperators ComplexOrder
open Matrix
open Classical

namespace SepProj

variable {K : Type*} [Fintype K] [DecidableEq K] {N : ℕ}

/-- The joint "pattern" of a basis index `k` under a diagonal family `R`: the tuple of diagonal
entries `(R i) k k`.  For diagonal projections these are `0/1`, so the pattern records which
register projections fix `k`. -/
def pattern (R : Fin N → Matrix K K ℂ) (k : K) : Fin N → ℂ := fun i => (R i) k k

/-- The joint pinching of `E` by a diagonal commuting family `R`: zero out the entries connecting
indices with different patterns.  This is the conditional expectation onto the block-diagonal
algebra of the family. -/
noncomputable def pinch (R : Fin N → Matrix K K ℂ) (E : Matrix K K ℂ) : Matrix K K ℂ :=
  fun k l => if pattern R k = pattern R l then E k l else 0

/-
A diagonal projection has `0/1` diagonal entries.
-/
omit [DecidableEq K] in
lemma diag_proj_entry {R : Matrix K K ℂ} (hd : R.IsDiag) (hp : IsProj R) (k : K) :
    R k k = 0 ∨ R k k = 1 := by
  have h_diag : R k k * R k k = R k k := by
    convert congr_fun ( congr_fun hp.2 k ) k using 1;
    rw [ Matrix.mul_apply, Finset.sum_eq_single k ] <;> aesop;
  exact or_iff_not_imp_left.mpr fun h => mul_left_cancel₀ h <| by linear_combination' h_diag;

omit [Fintype K] [DecidableEq K] in
@[simp] lemma pinch_apply (R : Fin N → Matrix K K ℂ) (E : Matrix K K ℂ) (k l : K) :
    pinch R E k l = if pattern R k = pattern R l then E k l else 0 := rfl

/-
The pinching of a Hermitian matrix is Hermitian.
-/
omit [Fintype K] [DecidableEq K] in
lemma pinch_isHermitian {R : Fin N → Matrix K K ℂ} {E : Matrix K K ℂ} (hE : E.IsHermitian) :
    (pinch R E).IsHermitian := by
  ext k l; simp +decide [ pinch ] ;
  split_ifs <;> simp_all +decide [ eq_comm ];
  exact hE.apply k l ▸ rfl

/-
The pinching is trace-preserving.
-/
omit [DecidableEq K] in
lemma pinch_trace (R : Fin N → Matrix K K ℂ) (E : Matrix K K ℂ) :
    (pinch R E).trace = E.trace := by
  simp +decide [ Matrix.trace ]

/-
A matrix is block-diagonal w.r.t. the patterns iff it commutes with every (diagonal) `R i`.
-/
omit [DecidableEq K] in
lemma block_of_comm {R : Fin N → Matrix K K ℂ} (hRdiag : ∀ i, (R i).IsDiag)
    {F : Matrix K K ℂ} (hF : ∀ i, R i * F = F * R i) {k l : K} (h : pattern R k ≠ pattern R l) :
    F k l = 0 := by
  simp_all +decide [ funext_iff, Matrix.IsDiag ];
  obtain ⟨ i, hi ⟩ := h; specialize hF i; replace hF := congr_fun ( congr_fun hF k ) l; simp_all +decide [ Matrix.mul_apply, Pairwise ] ;
  rw [ Finset.sum_eq_single k, Finset.sum_eq_single l ] at hF <;> simp_all +decide [ pattern ];
  · exact mul_left_cancel₀ ( sub_ne_zero_of_ne hi ) ( by linear_combination' hF );
  · exact fun j hj => Or.inl ( hRdiag i ( Ne.symm hj ) )

/-
The pinching commutes with each diagonal `R i`.
-/
omit [DecidableEq K] in
lemma pinch_comm {R : Fin N → Matrix K K ℂ} (hRdiag : ∀ i, (R i).IsDiag) (E : Matrix K K ℂ)
    (i : Fin N) : R i * pinch R E = pinch R E * R i := by
  ext k l; by_cases h : pattern R k = pattern R l <;> simp_all +decide [ Matrix.mul_apply, Matrix.IsDiag ] ;
  · rw [ Finset.sum_eq_single k, Finset.sum_eq_single l ] <;> simp_all +decide [ eq_comm, Pairwise ];
    replace h := congr_fun h i; simp_all +decide [ mul_comm, pattern ] ;
  · rw [ Finset.sum_eq_single l, Finset.sum_eq_zero ] <;> simp_all +decide [ Pairwise ];
    · exact Or.inl ( hRdiag i ( by contrapose! h; aesop ) );
    · grind +qlia;
    · grind

/-
**Step 2**: the pinching error is controlled by the sum of squared commutator norms.
-/
omit [DecidableEq K] in
lemma pinch_error_le {R : Fin N → Matrix K K ℂ} (hRdiag : ∀ i, (R i).IsDiag)
    (hRproj : ∀ i, IsProj (R i)) (d : ℕ) (E : Matrix K K ℂ) :
    hsNormSq d (E - pinch R E) ≤ ∑ i, hsNormSq d (comm (R i) E) := by
  -- By definition of $hsNormSq$, we know that
  have h_norm_sq : ∑ k, ∑ l, (if pattern R k = pattern R l then 0 else ‖E k l‖ ^ 2) ≤ ∑ i, ∑ k, ∑ l, ‖(R i) k k - (R i) l l‖ ^ 2 * ‖E k l‖ ^ 2 := by
    have h_sum : ∀ k l, (if pattern R k = pattern R l then 0 else ‖E k l‖ ^ 2) ≤ (∑ i, ‖(R i) k k - (R i) l l‖ ^ 2) * ‖E k l‖ ^ 2 := by
      intro k l
      by_cases h : pattern R k = pattern R l <;> simp [h];
      · exact mul_nonneg ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( sq_nonneg _ );
      · obtain ⟨ i, hi ⟩ := not_forall.mp ( fun h' => h <| funext h' );
        refine' le_mul_of_one_le_left ( sq_nonneg _ ) _;
        refine' le_trans _ ( Finset.single_le_sum ( fun i _ => sq_nonneg ( ‖R i k k - R i l l‖ ) ) ( Finset.mem_univ i ) );
        have h_diag : ∀ i, (R i) k k = 0 ∨ (R i) k k = 1 := by
          exact fun i => diag_proj_entry ( hRdiag i ) ( hRproj i ) k
        have h_diag' : ∀ i, (R i) l l = 0 ∨ (R i) l l = 1 := by
          exact fun i => diag_proj_entry ( hRdiag i ) ( hRproj i ) l
        generalize_proofs at *; (
        cases h_diag i <;> cases h_diag' i <;> simp_all +decide [ pattern ]);
    refine' le_trans ( Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => h_sum k l ) _;
    rw [ Finset.sum_comm ];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_mul _ _ _ ] ;
    exact fun k => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )
  generalize_proofs at *; (
  convert div_le_div_of_nonneg_right h_norm_sq ( Nat.cast_nonneg d ) using 1 <;> norm_num [ hsNormSq_eq_sum ] ; ring!;
  · rw [ mul_comm ] ; congr ; ext x ; congr ; ext y ; aesop;
  · rw [ Finset.sum_div ] ; congr ; ext i ; simp +decide [ Matrix.mul_apply] ; ring;
    rw [ mul_comm ] ; congr ; ext x ; congr ; ext y ; rw [ Finset.sum_eq_single x, Finset.sum_eq_single y ] <;> simp +contextual [ mul_comm ] ; ring;
    · rw [ ← mul_pow, ← norm_mul ] ; ring;
    · exact fun k hk => Or.inl ( hRdiag i hk );
    · exact fun k hk => Or.inl ( hRdiag i ( Ne.symm hk ) ))

/-
The Hilbert–Schmidt norm splits (Pythagoras) across the pinching: if `F` is block-diagonal
(commutes with every `R i`), then `‖E − F‖² = ‖E − pinch E‖² + ‖pinch E − F‖²`.
-/
omit [DecidableEq K] in
lemma pythagoras_split {R : Fin N → Matrix K K ℂ} (hRdiag : ∀ i, (R i).IsDiag) (d : ℕ)
    (E F : Matrix K K ℂ) (hF : ∀ i, R i * F = F * R i) :
    hsNormSq d (E - F) = hsNormSq d (E - pinch R E) + hsNormSq d (pinch R E - F) := by
  -- By the Pythagorean theorem, we have ‖E - F‖² = ‖E - pinch R E‖² + ‖pinch R E - F‖².
  have h_pyth : hsNormSq d (E - F) = hsNormSq d ((E - pinch R E) + (pinch R E - F)) := by
    rw [ sub_add_sub_cancel ];
  convert h_pyth using 1 ; simp +decide [ hsNormSq_eq_sum ] ; ring;
  field_simp;
  rw [ ← Finset.sum_add_distrib, ← Finset.sum_congr rfl ] ; intros ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext ; split_ifs <;> simp +decide [ * ] ; ring;
  rename_i k hk l hl; have := block_of_comm hRdiag hF hl; simp_all +decide  ;

/-
The "defect" `Tr(B − B²)` of the pinching equals the squared pinching error.
-/
omit [DecidableEq K] in
lemma pinch_defect (d : ℕ) {R : Fin N → Matrix K K ℂ} {E : Matrix K K ℂ} (hE : IsProj E) :
    hsNormSq d (E - pinch R E) =
      ((pinch R E).trace.re - ((pinch R E) * (pinch R E)).trace.re) / d := by
  have h_split_sum : (∑ k, ∑ l, ‖(E - pinch R E) k l‖ ^ 2) = (∑ k, ∑ l, ‖E k l‖ ^ 2) - (∑ k, ∑ l, ‖(pinch R E) k l‖ ^ 2) := by
    simp +decide [ sub_eq_add_neg, Complex.normSq, Complex.sq_norm ];
    rw [ ← Finset.sum_neg_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext x ; rw [ ← Finset.sum_neg_distrib ] ; rw [ ← Finset.sum_add_distrib ] ; congr ; ext y ; split_ifs <;> simp +decide [ * ] ; ring;
  have h_trace_sq : ∀ (M : Matrix K K ℂ), M.IsHermitian → (M * M).trace.re = ∑ k, ∑ l, ‖M k l‖ ^ 2 := by
    intro M hM
    have h_trace_sq : (M * M).trace = ∑ k, ∑ l, M k l * starRingEnd ℂ (M k l) := by
      simp +decide [ Matrix.trace, Matrix.mul_apply];
      exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [ ← hM.apply ] ; simp +decide [ mul_comm ] ;
    simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
    norm_cast;
  have h_trace_sq_E : (∑ k, ∑ l, ‖E k l‖ ^ 2) = (E.trace.re) := by
    rw [ ← h_trace_sq E hE.1, hE.2 ];
  rw [ hsNormSq_eq_sum, h_split_sum, h_trace_sq_E, h_trace_sq _ ( pinch_isHermitian hE.1 ) ];
  rw [ pinch_trace ]

/-
Algebraic reduction for the rounding step.  For a Hermitian `B` with `Tr B = d` and a
projection `F` with `Tr F = d`, the normalized Hilbert–Schmidt distance `‖B - F‖²₂,d` is bounded by
`(Tr B - Tr B²)/d` exactly when the trace inequality `Tr(B²) ≤ Tr(B F)` holds.  This is the purely
algebraic content of the rounding lemma; the spectral content is isolated in
`exists_rounding_proj`.
-/
omit [DecidableEq K] in
lemma rounding_of_trace (d : ℕ) (B F : Matrix K K ℂ) (hBherm : B.IsHermitian)
    (hF : IsProj F) (hBtr : B.trace.re = d) (hFtr : F.trace.re = (d : ℝ))
    (htr : (B * B).trace.re ≤ (B * F).trace.re) :
    hsNormSq d (B - F) ≤ (B.trace.re - (B * B).trace.re) / d := by
  by_cases hd : d = 0 <;> simp_all +decide [ hsNormSq ];
  simp_all +decide [ Matrix.IsHermitian, Matrix.mul_sub, sub_mul];
  simp_all +decide [ IsProj, Matrix.IsHermitian ];
  rw [ show ( F * B ).trace.re = ( B * F ).trace.re by rw [ ← Matrix.trace_transpose, Matrix.transpose_mul ] ; simp +decide  ] ; rw [ div_le_div_iff_of_pos_right ( by positivity ) ] ; linarith

/-
Converse of `block_of_comm`: a matrix that is block-diagonal w.r.t. the patterns of a diagonal
family commutes with every member of the family.
-/
omit [DecidableEq K] in
lemma comm_of_block {R : Fin N → Matrix K K ℂ} (hRdiag : ∀ i, (R i).IsDiag)
    {F : Matrix K K ℂ} (hFblock : ∀ k l, pattern R k ≠ pattern R l → F k l = 0) (i : Fin N) :
    R i * F = F * R i := by
  ext k l; by_cases h : pattern R k = pattern R l <;> simp_all +decide [ Matrix.mul_apply] ;
  · rw [ Finset.sum_eq_single k, Finset.sum_eq_single l ] <;> simp_all +decide [ Matrix.IsDiag, mul_comm ];
    · exact Or.inl ( congr_fun h i );
    · exact fun j hj => Or.inl ( hRdiag i ( by aesop ) );
    · exact fun j hj => Or.inl ( hRdiag i ( Ne.symm hj ) );
  · rw [ Finset.sum_eq_single k, Finset.sum_eq_single l ] <;> simp_all +decide [ Matrix.IsDiag ];
    · exact fun j hj => Or.inr ( hRdiag i ( by aesop ) );
    · exact fun j hj => Or.inl ( hRdiag i ( Ne.symm hj ) )

/-
Existence of a "top-`d`" subset: `d` indices carrying the largest values of `lam`.
-/
lemma exists_top_set {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℝ) (d : ℕ)
    (hd : d ≤ Fintype.card ι) :
    ∃ t : Finset ι, t.card = d ∧ ∀ i ∈ t, ∀ j, j ∉ t → lam j ≤ lam i := by
  obtain ⟨t, ht⟩ : ∃ t : Finset ι, t.card = d ∧ ∀ u : Finset ι, u.card = d → (∑ i ∈ t, lam i) ≥ (∑ i ∈ u, lam i) := by
    obtain ⟨t, ht⟩ : ∃ t : Finset ι, t.card = d := by
      have := Finset.exists_subset_card_eq hd; tauto;
    have := Finset.exists_max_image ( Finset.powersetCard d Finset.univ ) ( fun u => ∑ i ∈ u, lam i ) ⟨ t, Finset.mem_powersetCard.mpr ⟨ Finset.subset_univ _, ht ⟩ ⟩ ; aesop;
  refine' ⟨ t, ht.1, fun i hi j hj => _ ⟩;
  have := ht.2 ( Insert.insert j ( t.erase i ) ) ?_ <;> simp_all +decide [ Finset.sum_insert];
  · grind;
  · rw [ Nat.sub_add_cancel ( ht.1 ▸ Finset.card_pos.mpr ⟨ i, hi ⟩ ) ]

/-
Real rearrangement inequality.  If `lam` takes values in `[0,1]` on `s`, sums to `d` over `s`,
and `t ⊆ s` of cardinality `d` collects the largest values, then `∑_{s} lam² ≤ ∑_{t} lam`.
-/
lemma top_d_rearrangement {ι : Type*} (s t : Finset ι) (lam : ι → ℝ) (d : ℕ)
    (hts : t ⊆ s) (htd : t.card = d)
    (hnonneg : ∀ i ∈ s, 0 ≤ lam i) (hle : ∀ i ∈ s, lam i ≤ 1)
    (htop : ∀ i ∈ t, ∀ j ∈ s, j ∉ t → lam j ≤ lam i)
    (hsum : ∑ i ∈ s, lam i = (d : ℝ)) :
    ∑ i ∈ s, (lam i) ^ 2 ≤ ∑ i ∈ t, lam i := by
  -- Choose a threshold `θ` such that `lam j ≤ θ ≤ lam i` for all `j ∈ tc`, `i ∈ t`.
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, (∀ j ∈ s \ t, lam j ≤ θ) ∧ (∀ i ∈ t, θ ≤ lam i) := by
    by_cases ht_empty : t = ∅;
    · exact ⟨ 1, fun j hj => hle j ( Finset.mem_sdiff.mp hj |>.1 ), by simp +decide [ ht_empty ] ⟩;
    · exact ⟨ Finset.min' ( t.image lam ) ⟨ _, Finset.mem_image_of_mem _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ht_empty ) ) ⟩, fun j hj => by obtain ⟨ k, hk, hk' ⟩ := Finset.mem_image.mp ( Finset.min'_mem ( t.image lam ) ⟨ _, Finset.mem_image_of_mem _ ( Classical.choose_spec ( Finset.nonempty_of_ne_empty ht_empty ) ) ⟩ ) ; linarith [ Finset.min'_le _ _ ( Finset.mem_image_of_mem lam hk ), htop _ hk _ ( Finset.mem_sdiff.mp hj |>.1 ) ( Finset.mem_sdiff.mp hj |>.2 ) ], fun i hi => Finset.min'_le _ _ ( Finset.mem_image_of_mem lam hi ) ⟩;
  -- For the tail: each `j ∈ tc` has `lam j ≤ θ` and `lam j ≥ 0`, so `lam j² = lam j · lam j ≤ θ · lam j`. Summing: `∑_{tc} lam j² ≤ θ · ∑_{tc} lam j`.
  have h_tail : ∑ j ∈ s \ t, lam j ^ 2 ≤ θ * ∑ j ∈ s \ t, lam j := by
    simpa only [ Finset.mul_sum _ _ _ ] using Finset.sum_le_sum fun i hi => by nlinarith only [ hθ.1 i hi, hnonneg i ( Finset.mem_sdiff.mp hi |>.1 ) ] ;
  -- For the head: each `i ∈ t` has `lam i ≥ θ` and `1 - lam i ≥ 0` (since `lam i ≤ 1`), so `lam i (1 - lam i) ≥ θ (1 - lam i)`. Summing: `∑_{t} lam i(1-lam i) ≥ θ · ∑_{t}(1 - lam i) = θ · ∑_{tc} lam j`.
  have h_head : ∑ i ∈ t, lam i * (1 - lam i) ≥ θ * ∑ i ∈ t, (1 - lam i) := by
    rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by nlinarith only [ hθ.2 i hi, hle i ( hts hi ), hnonneg i ( hts hi ) ] ;
  simp_all +decide [ mul_sub];
  grind

/-
**Joint diagonalization primitive**.  A Hermitian `B` commuting with a diagonal projection
family `R` admits a block-diagonal unitary eigenbasis: a unitary `U` whose columns are supported on
single pattern blocks, with `B = U diag(lam) Uᴴ` for real eigenvalues `lam`.

This is the single genuinely missing primitive of the rounding lemma — Mathlib has the spectral
theorem for one Hermitian matrix but not the simultaneous (block-respecting) diagonalization of a
commuting family.
-/
lemma exists_block_eigenbasis (R : Fin N → Matrix K K ℂ) (hRdiag : ∀ i, (R i).IsDiag)
    (B : Matrix K K ℂ) (hBherm : B.IsHermitian) (hBcomm : ∀ i, R i * B = B * R i) :
    ∃ (U : Matrix K K ℂ) (lam : K → ℝ),
      Uᴴ * U = 1 ∧ (∀ k l, pattern R k ≠ pattern R l → U k l = 0) ∧
      B = U * Matrix.diagonal (fun k => (lam k : ℂ)) * Uᴴ := by
  set patterns : Finset (Fin N → ℂ) := Finset.image (pattern R) Finset.univ;
  -- For each pattern $p \in \text{patterns}$, let $B_p$ be the restriction of $B$ to the block corresponding to $p$.
  have h_block_diag : ∀ p ∈ patterns, ∃ Up : Matrix {k : K // pattern R k = p} {k : K // pattern R k = p} ℂ, ∃ lamp : {k : K // pattern R k = p} → ℝ, Up.conjTranspose * Up = 1 ∧ (B.submatrix (fun k => k.val) (fun k => k.val)) = Up * Matrix.diagonal (fun k => (lamp k : ℂ)) * Up.conjTranspose := by
    intro p hp;
    have := @hermitian_decomp;
    exact Exists.elim ( this ( show Matrix.IsHermitian ( B.submatrix ( fun k => k.val ) fun k => k.val ) from by simpa [ Matrix.IsHermitian ] using hBherm.submatrix _ ) ) fun U hU => Exists.elim hU fun lam hlam => ⟨ U, lam, hlam.1, hlam.2.2 ⟩;
  choose! Up lamp hUp hlamp using h_block_diag;
  refine' ⟨ fun k l => if h : pattern R k = pattern R l then Up ( pattern R k ) ⟨ k, rfl ⟩ ⟨ l, h.symm ⟩ else 0, fun k => lamp ( pattern R k ) ⟨ k, rfl ⟩, _, _, _ ⟩;
  · ext k l;
    by_cases h : pattern R k = pattern R l <;> simp +decide [ h, Matrix.mul_apply ];
    · rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.univ.filter fun x => pattern R x = pattern R l ) ) ];
      · convert congr_fun ( congr_fun ( hUp ( pattern R l ) ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) ) ⟨ k, h ⟩ ) ⟨ l, rfl ⟩ using 1;
        · refine' Finset.sum_bij ( fun x hx => ⟨ x, by aesop ⟩ ) _ _ _ _ <;> simp +decide ;
          grind +qlia;
        · simp +decide [ Matrix.one_apply];
      · grind;
    · rw [ Finset.sum_eq_zero ] <;> simp +decide [ Matrix.one_apply ];
      · grind +revert;
      · grind;
  · aesop;
  · ext k l; by_cases h : pattern R k = pattern R l <;> simp +decide  ;
    · convert congr_fun ( congr_fun ( hlamp ( pattern R k ) ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) ) ⟨ k, rfl ⟩ ) ⟨ l, h.symm ⟩ using 1 ; simp +decide [ Matrix.mul_apply, Matrix.diagonal ];
      rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.filter ( fun x => pattern R k = pattern R x ) Finset.univ ) ) ];
      · refine' Finset.sum_bij ( fun x hx => ⟨ x, by aesop ⟩ ) _ _ _ _ <;> simp +decide [ h ];
        · exact fun _ _ => Eq.symm ‹_›;
        · grind;
      · grind;
    · simp +decide [ Matrix.mul_apply];
      convert block_of_comm hRdiag hBcomm h using 1;
      refine' Finset.sum_eq_zero fun x hx => _;
      by_cases h' : pattern R l = pattern R x <;> simp +decide [ h'];
      rw [ Finset.sum_eq_zero ] <;> simp +decide ;
      intro y hy; by_cases hy' : y = x <;> simp_all +decide [ Matrix.diagonal ] ;

/-
**Spectral existence core** of the rounding lemma.  Given a Hermitian `B` with `0 ≤ B ≤ 1`,
integer trace `d`, commuting with a diagonal projection family `R`, there is a rank-`d` projection
`F` commuting with every `R i` and with `Tr(B²) ≤ Tr(B F)`.

The spectral content is supplied by `exists_block_eigenbasis`; `F` is the projection onto the `d`
largest eigenvalues, and the trace bound is the rearrangement `top_d_rearrangement`.
-/
lemma exists_rounding_proj (d : ℕ) (R : Fin N → Matrix K K ℂ) (hRdiag : ∀ i, (R i).IsDiag)
    (B : Matrix K K ℂ) (hBherm : B.IsHermitian)
    (hBpos : B.PosSemidef) (hBle : (1 - B).PosSemidef) (hBtr : B.trace.re = d)
    (hBcomm : ∀ i, R i * B = B * R i) :
    ∃ F : Matrix K K ℂ, IsProj F ∧ F.trace.re = d ∧ (∀ i, R i * F = F * R i) ∧
      (B * B).trace.re ≤ (B * F).trace.re := by
  -- By `exists_block_eigenbasis`, obtain
  obtain ⟨U, lam, hUunit, hUblock, hB⟩ := exists_block_eigenbasis R hRdiag B hBherm hBcomm
  set D := Matrix.diagonal (fun k => (lam k : ℂ))
  have hUUH : U * Uᴴ = 1 := by
    rw [ ← mul_eq_one_comm, hUunit ];
  have h_lam_bounds : ∀ k, 0 ≤ lam k ∧ lam k ≤ 1 := by
    intro k
    have h_eigenvalue : star (fun j => U j k) ⬝ᵥ B.mulVec (fun j => U j k) = lam k := by
      have h_eigenvalue : B *ᵥ (fun j => U j k) = lam k • (fun j => U j k) := by
        ext j; simp +decide [ hB, Matrix.mulVec, dotProduct, mul_assoc ] ;
        simp +decide [ ← Matrix.mul_apply];
        simp +decide [ Matrix.mul_assoc, hUunit ];
        simp +decide [ D, Matrix.mul_apply, mul_comm ];
        simp +decide [ diagonal ];
      simp +decide [ h_eigenvalue, dotProduct_smul ];
      replace hUunit := congr_fun ( congr_fun hUunit k ) k; simp_all +decide [ Matrix.mul_apply, dotProduct ] ;
    have := hBpos.dotProduct_mulVec_nonneg ( fun j => U j k );
    have := hBle.dotProduct_mulVec_nonneg ( fun j => U j k ) ; simp_all +decide [ Matrix.sub_mulVec ] ;
    simp_all +decide [ dotProduct, Complex.ext_iff ];
    simp_all +decide [ Complex.le_def];
    have := congr_fun ( congr_fun hUunit k ) k; simp_all +decide [ Matrix.mul_apply, Complex.ext_iff ] ;
  have h_sum_lam : ∑ k, lam k = d := by
    have h_sum_lam : (B.trace).re = (∑ k, lam k) := by
      rw [ hB, Matrix.trace_mul_comm ];
      rw [ ← Matrix.mul_assoc, hUunit, Matrix.one_mul, Matrix.trace_diagonal ] ; norm_num;
    exact h_sum_lam.symm.trans hBtr
  have h_card : d ≤ Fintype.card K := by
    exact_mod_cast ( by have := Finset.sum_le_sum fun k ( _ : k ∈ Finset.univ ) => h_lam_bounds k |>.2; norm_num at this; linarith : ( d : ℝ ) ≤ Fintype.card K )
  obtain ⟨t, ht_card, ht_top⟩ := exists_top_set lam d h_card
  set Dt := Matrix.diagonal (fun k => (if k ∈ t then 1 else 0 : ℂ))
  set F := U * Dt * Uᴴ
  use F;
  refine' ⟨ _, _, _, _ ⟩;
  · constructor;
    · simp +zetaDelta at *;
      simp +decide [ Matrix.IsHermitian, Matrix.mul_assoc];
      exact congr_arg _ ( by ext i j; by_cases hi : i = j <;> aesop );
    · simp +zetaDelta at *;
      simp +decide [ ← mul_assoc];
      simp +decide [ Matrix.mul_assoc, hUunit ];
      exact congr_arg _ ( by ext i j; by_cases hi : i = j <;> aesop );
  · simp +zetaDelta at *;
    rw [ Matrix.trace_mul_comm ];
    simp +decide [ ← mul_assoc, hUunit, ht_card ];
  · intro i
    apply comm_of_block hRdiag
    intro k l hkl
    simp [F, Dt];
    simp +decide [ Matrix.mul_apply];
    simp +decide [ Matrix.diagonal];
    rw [ Finset.sum_eq_zero ] ; intros ; simp +decide ;
    grind +splitImp;
  · have h_trace_BF : (B * F).trace = ∑ k ∈ t, lam k := by
      simp +zetaDelta at *;
      simp +decide [ hB, Matrix.mul_assoc, Matrix.trace_mul_comm U ];
      simp +decide [ ← mul_assoc, hUunit, Matrix.trace ]
    have h_trace_BB : (B * B).trace = ∑ k, (lam k) ^ 2 := by
      simp +decide [ hB, Matrix.mul_assoc, Matrix.trace_mul_comm U ];
      simp +decide [ ← mul_assoc, hUunit];
      simp +decide [ D, Matrix.trace, sq ];
    convert top_d_rearrangement Finset.univ t lam d ( Finset.subset_univ t ) ht_card ( fun i _ => h_lam_bounds i |>.1 ) ( fun i _ => h_lam_bounds i |>.2 ) ( fun i hi j hj hjt => ht_top i hi j hjt ) ( by simpa [ Finset.sum_ite ] using h_sum_lam ) using 1;
    · exact h_trace_BB.symm ▸ by norm_cast;
    · exact h_trace_BF.symm ▸ by norm_cast;

/-- **Spectral rounding** (the one genuinely spectral step).  Given a Hermitian operator `B` with
`0 ≤ B ≤ 1`, integer trace `d`, block-diagonal w.r.t. a diagonal commuting projection family `R`,
there is a rank-`d` projection `F` commuting with every `R i` with
`‖B − F‖²₂,d ≤ (Tr B − Tr B²)/d`.

This is proved by simultaneously diagonalizing `B` and the family `R` and projecting onto the `d`
largest eigenvalues; the inequality is the eigenvalue rearrangement
`∑_{r>d} λ_r² ≤ ∑_{r≤d} λ_r(1−λ_r)`.  Mathlib lacks simultaneous diagonalization of a commuting
family, so this remains the single unproven core. -/
lemma rounding (d : ℕ) (R : Fin N → Matrix K K ℂ) (hRdiag : ∀ i, (R i).IsDiag)
    (B : Matrix K K ℂ) (hBherm : B.IsHermitian)
    (hBpos : B.PosSemidef) (hBle : (1 - B).PosSemidef) (hBtr : B.trace.re = d)
    (hBcomm : ∀ i, R i * B = B * R i) :
    ∃ F : Matrix K K ℂ, IsProj F ∧ F.trace.re = d ∧ (∀ i, R i * F = F * R i) ∧
      hsNormSq d (B - F) ≤ (B.trace.re - (B * B).trace.re) / d := by
  obtain ⟨F, hFproj, hFtr, hFcomm, hFtrace⟩ :=
    exists_rounding_proj d R hRdiag B hBherm hBpos hBle hBtr hBcomm
  exact ⟨F, hFproj, hFtr, hFcomm,
    rounding_of_trace d B F hBherm hFproj hBtr hFtr hFtrace⟩

/-
`pinch R E` is positive semidefinite when `E` is.
-/
omit [DecidableEq K] in
lemma pinch_posSemidef {R : Fin N → Matrix K K ℂ}
    {E : Matrix K K ℂ} (hE : E.PosSemidef) : (pinch R E).PosSemidef := by
  refine' ⟨ _, _ ⟩;
  · exact pinch_isHermitian hE.1;
  · intro x
    set x_p := fun p : Fin N → ℂ => fun i => if pattern R i = p then x i else 0;
    -- By definition of $x_p$, we can rewrite the sum as $\sum_{p \in s} \sum_{k, l} \overline{x_p k} E_{kl} x_p l$.
    have h_sum : ∑ k, ∑ l, star (x k) * (pinch R E k l) * x l = ∑ p ∈ Finset.image (pattern R) Finset.univ, ∑ k, ∑ l, star (x_p p k) * E k l * x_p p l := by
      rw [ Finset.sum_image' ];
      simp +decide [ x_p, pinch ];
      intro i; rw [ Finset.sum_filter ] ; congr; ext j; split_ifs <;> simp_all +decide [ eq_comm ] ;
    -- Since $E$ is positive semidefinite, we have $\sum_{k, l} \overline{x_p k} E_{kl} x_p l \geq 0$ for each $p$.
    have h_pos : ∀ p ∈ Finset.image (pattern R) Finset.univ, 0 ≤ ∑ k, ∑ l, star (x_p p k) * E k l * x_p p l := by
      intro p hp
      have h_pos : 0 ≤ star (x_p p) ⬝ᵥ (E *ᵥ x_p p) := by
        exact PosSemidef.dotProduct_mulVec_nonneg hE (x_p p);
      convert h_pos using 1;
      simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc ];
    convert h_sum.symm ▸ Finset.sum_nonneg h_pos using 1;
    simp +decide [ Finsupp.sum_fintype ]

/-
`pinch R (1 - E)` is positive semidefinite, i.e. `pinch R E ≤ 1`, when `E ≤ 1`.
-/
lemma pinch_le_one {R : Fin N → Matrix K K ℂ}
    {E : Matrix K K ℂ} (hE : (1 - E).PosSemidef) : (1 - pinch R E).PosSemidef := by
  convert pinch_posSemidef (R := R) hE using 1;
  ext i j; by_cases hij : i = j <;> simp +decide [ *, pinch ] ;
  split_ifs <;> ring

/-
A projection is positive semidefinite.
-/
omit [DecidableEq K] in
lemma isProj_posSemidef {E : Matrix K K ℂ} (hE : IsProj E) : E.PosSemidef := by
  convert Matrix.posSemidef_conjTranspose_mul_self E using 1
  generalize_proofs at *;
  rw [ hE.1.eq, hE.2 ]

/-
The complement of a projection is a projection.
-/
lemma isProj_compl {E : Matrix K K ℂ} (hE : IsProj E) : IsProj (1 - E) := by
  constructor;
  · cases hE ; simp_all +decide [ Matrix.IsHermitian ];
  · simp +decide [ sub_mul, mul_sub, hE.2 ]

/-- **Lemma 4** (rounding an almost invariant subspace), specialized to a family of *diagonal*
commuting projections `R 0, …, R (N-1)` on `K` — exactly the situation in the main proof, where the
`Rᵢ` are the ancilla register projections, simultaneously diagonal in the computational basis.
Given a rank-`d` projection `E`, there is a rank-`d` projection `F` commuting with every `Rᵢ` and
`‖E − F‖²₂,d ≤ 2 ∑ᵢ ‖[Rᵢ, E]‖²₂,d`.

The general (non-diagonal) statement reduces to this one by simultaneous diagonalization of the
commuting family; we work directly with the diagonal case used in the application. -/
theorem lemma4_diag (d : ℕ)
    (R : Fin N → Matrix K K ℂ)
    (hRdiag : ∀ i, (R i).IsDiag) (hRproj : ∀ i, IsProj (R i))
    (E : Matrix K K ℂ) (hE : IsProj E) (hErank : E.trace.re = d) :
    ∃ F : Matrix K K ℂ, IsProj F ∧ F.trace.re = d ∧ (∀ i, R i * F = F * R i) ∧
      hsNormSq d (E - F) ≤ 2 * ∑ i, hsNormSq d (comm (R i) E) := by
  -- The pinching `B = pinch R E`.
  set B := pinch R E with hBdef
  have hBherm : B.IsHermitian := pinch_isHermitian hE.1
  have hEpos : E.PosSemidef := isProj_posSemidef hE
  have hBpos : B.PosSemidef := pinch_posSemidef hEpos
  have hBle : (1 - B).PosSemidef := pinch_le_one (isProj_posSemidef (isProj_compl hE))
  have hBtr : B.trace.re = d := by rw [hBdef, pinch_trace]; exact hErank
  have hBcomm : ∀ i, R i * B = B * R i := fun i => pinch_comm hRdiag E i
  obtain ⟨F, hFproj, hFtr, hFcomm, hFbound⟩ :=
    rounding d R hRdiag B hBherm hBpos hBle hBtr hBcomm
  refine ⟨F, hFproj, hFtr, hFcomm, ?_⟩
  -- Pythagoras + the defect identity + Step 2.
  have hsplit := pythagoras_split hRdiag d E F hFcomm
  have hdefect := pinch_defect d (R := R) hE
  have hstep2 := pinch_error_le hRdiag hRproj d E
  rw [hsplit]
  have : hsNormSq d (B - F) ≤ hsNormSq d (E - B) := by
    rw [hdefect]; exact hFbound
  calc hsNormSq d (E - B) + hsNormSq d (B - F)
      ≤ hsNormSq d (E - B) + hsNormSq d (E - B) := by linarith
    _ = 2 * hsNormSq d (E - B) := by ring
    _ ≤ 2 * ∑ i, hsNormSq d (comm (R i) E) := by linarith [hstep2]

end SepProj