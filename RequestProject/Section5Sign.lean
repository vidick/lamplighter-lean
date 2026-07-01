import Mathlib
import RequestProject.MuInvariance
import RequestProject.MeasureBridge
import RequestProject.MeasureInstantiation
import RequestProject.PVMAlgebra
import RequestProject.TowerBridge

/-!
# Section 5 sign pattern (`claim:b-B`)

This file proves the **sign-pattern claim** (paper `claim:b-B`) that the Section 5
per-tower construction needs as the hypothesis `hsign` of
`LamplighterStability.rep_from_approx_tower`: the center involution `B₀ = B c`
(`c` the window coordinate `0`) acts as a *sign* `(-1)^{x_i}` on each floor
projection `Edef (towerFloor (base τ) i)` of a tower whose base lies in a single
`height`-cylinder (`ProjSingleton`).

The chain is:

* `B_mul_proj` — `B · ½(1+(-1)^b B) = (-1)^b · ½(1+(-1)^b B)` for a Hermitian
  involution `B`.
* `C_mul_atom` — for a commuting family of Hermitian involutions,
  `C_j · atom C x = (-1)^{x_j} · atom C x`.
* `EpatB_coord_sign` — the same for the pattern PVM `EpatB`:
  `B c · EpatB p = (-1)^{p c} · EpatB p`.
* `Edef_coord_sign` — for a definable set `S` on which the coordinate `c` is
  constantly `v`, `B c · Edef S = (-1)^v · Edef S`.
* `floor_patterns_center` — every `(m+1)`-pattern of `towerFloor (base) i`
  (`base ⊆ cyl j p₀`, `i ≤ j`) takes, at the center coordinate `0`, the value
  `p₀⟨-i⟩`.
* `Edef_floor_center_sign` — assembling the above: the center involution acts as
  the sign `p₀⟨-i⟩` on the floor projection.
-/

namespace LamplighterStability

open scoped BigOperators
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-
`B · ½(1+(-1)^b B) = (-1)^b · ½(1+(-1)^b B)` for a Hermitian involution `B`.
-/
lemma B_mul_proj {B : Matrix ι ι ℂ} (hB2 : B * B = 1) (b : Bool) :
    B * proj B b = signC b • proj B b := by
  unfold proj;
  simp +decide [ mul_add, smul_smul, hB2 ];
  grind +suggestions

/-
For a commuting family of Hermitian involutions,
`C_j · atom C x = (-1)^{x_j} · atom C x`.
-/
lemma C_mul_atom {n : ℕ} {C : Fin n → Matrix ι ι ℂ}
    (hC2 : ∀ i, C i * C i = 1) (hCc : ∀ i k, Commute (C i) (C k))
    (x : Fin n → Bool) (j : Fin n) :
    C j * atom C x = signC (x j) • atom C x := by
  induction' n with n ih;
  · exact Fin.elim0 j;
  · refine' Fin.cases _ _ j;
    · rw [ atom_succ, ← mul_assoc, B_mul_proj ( hC2 0 ) ];
      rw [ smul_mul_assoc ];
    · intro i
      have h_comm : C i.succ * proj (C 0) (x 0) = proj (C 0) (x 0) * C i.succ := by
        unfold proj; simp +decide [ mul_add, add_mul, hCc _ _ |> Commute.eq ] ;
      rw [ atom_succ ];
      rw [ ← Matrix.mul_assoc, h_comm, Matrix.mul_assoc ];
      rw [ ih ( fun i => hC2 i.succ ) ( fun i j => hCc i.succ j.succ ) _ i, Matrix.mul_smul ]

end LamplighterStability

namespace LamplighterStability.MeasureBridge

open LamplighterStability LamplighterStability.Dynamics
  LamplighterStability.MeasureInstantiation
open scoped BigOperators
open Matrix

variable {d : ℕ}

/-
The pattern PVM: `B c · EpatB p = (-1)^{p c} · EpatB p`.
-/
lemma EpatB_coord_sign (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (hB2 : ∀ i, B i * B i = 1) (hBc : ∀ i j, Commute (B i) (B j))
    (c : Win M) (p : Win M → Bool) :
    B c * EpatB M B p = signC (p c) • EpatB M B p := by
  convert C_mul_atom _ _ _ ( winEquiv M c ) using 1;
  rotate_left;
  convert rfl;
  · exact congr_arg p ( Equiv.symm_apply_apply _ _ );
  · exact fun i => hB2 _;
  · exact fun i k => hBc _ _;
  · convert rfl;
    exact Equiv.symm_apply_apply _ _

/-
For a definable set `S` on which the coordinate `c` is constantly `v` (every
pattern of `S` has value `v` at `c`), `B c · Edef S = (-1)^v · Edef S`.
-/
lemma Edef_coord_sign (M : ℕ) (B : Win M → Matrix (Fin d) (Fin d) ℂ)
    (hB2 : ∀ i, B i * B i = 1) (hBc : ∀ i j, Commute (B i) (B j))
    (c : Win M) (v : Bool) {S : Set Cfg}
    (hconst : ∀ p ∈ patternsOf M S, p c = v) :
    B c * Edef M (EpatB M B) S = signC v • Edef M (EpatB M B) S := by
  rw [ Edef ];
  rw [ Finset.smul_sum, Finset.mul_sum ];
  exact Finset.sum_congr rfl fun p hp => by rw [ EpatB_coord_sign M B hB2 hBc c p, hconst p hp ] ;

/-
Every `(m+1)`-pattern of the floor `towerFloor base i` takes, at the center
coordinate `0`, the value `p₀⟨-i⟩`, where `base ⊆ cyl j p₀` and `i ≤ j`.
-/
lemma floor_patterns_center (m j i : ℕ)
    {base : Set Cfg} {p₀ : Win j → Bool} (hbase : base ⊆ cyl j p₀)
    (c0 : Win (m + 1)) (hc0 : c0.1 = 0)
    (hmem : -(i : ℤ) ∈ Finset.Icc (-(j : ℤ)) (j : ℤ))
    (q : Win (m + 1) → Bool) (hq : q ∈ patternsOf (m + 1) (towerFloor base i)) :
    q c0 = p₀ ⟨-(i : ℤ), hmem⟩ := by
  -- By definition of `patternsOf`, there exists some `x ∈ cyl (m + 1) q` such that `x ∈ towerFloor base i`.
  obtain ⟨x, hx_cyl, hx_floor⟩ : ∃ x, x ∈ cyl (m + 1) q ∧ x ∈ towerFloor base i := by
    exact ⟨ _, cyl_nonempty _ _ |> Classical.choose_spec, mem_patternsOf.mp hq |> fun h => h ( cyl_nonempty _ _ |> Classical.choose_spec ) ⟩;
  obtain ⟨ y, hy_base, rfl ⟩ := hx_floor;
  have := hbase hy_base; simp_all +decide [ cyl ] ;
  unfold Dynamics.proj at *;
  simp +decide [ ← hx_cyl, ← this ];
  convert L_zpow_apply i y c0 using 1;
  rw [ hc0, zero_sub ]

/-- **Sign pattern (`claim:b-B`).**  For a commuting family `B` of Hermitian
involutions, the center involution `B c0` (`c0` the window coordinate `0`) acts
as the sign `p₀⟨-i⟩` on the floor projection `Edef (towerFloor base i)`, where
`base ⊆ cyl j p₀` and `i ≤ j`. -/
lemma Edef_floor_center_sign (m j i : ℕ)
    (B : Win (m + 1) → Matrix (Fin d) (Fin d) ℂ)
    (hB2 : ∀ k, B k * B k = 1) (hBc : ∀ k l, Commute (B k) (B l))
    {base : Set Cfg} {p₀ : Win j → Bool} (hbase : base ⊆ cyl j p₀)
    (c0 : Win (m + 1)) (hc0 : c0.1 = 0)
    (hmem : -(i : ℤ) ∈ Finset.Icc (-(j : ℤ)) (j : ℤ)) :
    B c0 * Edef (m + 1) (EpatB (m + 1) B) (towerFloor base i)
      = signC (p₀ ⟨-(i : ℤ), hmem⟩) • Edef (m + 1) (EpatB (m + 1) B) (towerFloor base i) := by
  exact Edef_coord_sign (m + 1) B hB2 hBc c0 (p₀ ⟨-(i : ℤ), hmem⟩)
    (fun q hq => floor_patterns_center m j i hbase c0 hc0 hmem q hq)

end LamplighterStability.MeasureBridge