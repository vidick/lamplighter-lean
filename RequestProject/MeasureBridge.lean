import Mathlib
import RequestProject.Foundations
import RequestProject.MuInvariance
import RequestProject.Dynamics.ApproxInvMeasure

/-!
# PVM → `Measure Cfg` bridge (Section 5 measure construction)

This file builds, from a finite projection-valued measure `Epat` indexed by
window patterns `p : Win M → Bool`, a genuine probability measure `μ` on the
two-sided shift space `Cfg = ℤ → Bool` whose cylinder values are the atom traces
`μ(⟦p⟧) = tr(E_p)`.

The construction is the **pushforward of the finite atom measure under the
periodic-extension section** `sect : (Win M → Bool) → Cfg` (each pattern is
realized as a configuration extending it).  This avoids the full Kolmogorov
extension theorem: the induced measure is supported on the section image, and
for `M`-definable sets `b` we recover `μ(b) = tr(E_b)` exactly.
-/

namespace LamplighterStability.MeasureBridge

open MeasureTheory
open LamplighterStability LamplighterStability.Dynamics
open scoped BigOperators ENNReal

variable {d : ℕ}

/-- Realize a window pattern `p : Win M → Bool` as a configuration extending it
(extra coordinates set to `false`). -/
noncomputable def sect (M : ℕ) (p : Win M → Bool) : Cfg :=
  fun i => if h : i ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) then p ⟨i, h⟩ else false

/-- The section recovers the pattern on the window. -/
lemma proj_sect (M : ℕ) (p : Win M → Bool) : Dynamics.proj M (sect M p) = p := by
  funext i; simp [Dynamics.proj, sect, i.2]

lemma measurable_sect (M : ℕ) : Measurable (sect M) := by
  refine' measurable_pi_lambda _ _;
  intro a;
  by_cases ha : a ∈ Finset.Icc ( - ( M : ℤ ) ) ( M : ℤ ) <;> simp +decide [ *, sect ];
  exact measurable_pi_apply _

/-- The finite atom measure `ν = ∑_p tr(E_p) · δ_p` on the pattern space. -/
noncomputable def atomMeasure (M : ℕ)
    (Epat : (Win M → Bool) → Matrix (Fin d) (Fin d) ℂ) :
    Measure (Win M → Bool) :=
  ∑ p : Win M → Bool, ENNReal.ofReal (ntrace (Epat p)) • Measure.dirac p

/-- The induced measure on the shift space. -/
noncomputable def pvmMeasure (M : ℕ)
    (Epat : (Win M → Bool) → Matrix (Fin d) (Fin d) ℂ) : Measure Cfg :=
  (atomMeasure M Epat).map (sect M)

/-
Cylinder value: `μ(⟦q⟧) = tr(E_q)`.
-/
lemma pvmMeasure_cyl (M : ℕ)
    (Epat : (Win M → Bool) → Matrix (Fin d) (Fin d) ℂ)
    (q : Win M → Bool) :
    pvmMeasure M Epat (cyl M q) = ENNReal.ofReal (ntrace (Epat q)) := by
  convert MeasureTheory.Measure.map_apply ( measurable_sect M ) ( measurableSet_cyl M q ) using 1;
  unfold atomMeasure; simp +decide [ Set.preimage ] ;
  simp +decide [ Set.indicator, cyl, proj_sect ]

/-
The total mass is `tr(∑_p E_p) = tr(1) = 1` (when `0 < d`).
-/
lemma pvmMeasure_univ [NeZero d] (M : ℕ)
    (Epat : (Win M → Bool) → Matrix (Fin d) (Fin d) ℂ)
    (hHerm : ∀ p, (Epat p).IsHermitian)
    (hIdem : ∀ p, IsIdempotentElem (Epat p))
    (hSum : ∑ p : Win M → Bool, Epat p = 1) :
    pvmMeasure M Epat Set.univ = 1 := by
  convert ( pvmMeasure_cyl M Epat );
  constructor <;> intro h;
  · convert pvmMeasure_cyl M Epat using 1;
  · convert show ( pvmMeasure M Epat ) ( ⋃ p : Win M → Bool, cyl M p ) = 1 from ?_ using 2;
    · exact Set.ext fun x => by simp +decide [ mem_cyl_iff ] ;
    · rw [ MeasureTheory.measure_iUnion ];
      · rw [ tsum_fintype, Finset.sum_congr rfl fun _ _ => h _ ];
        rw [ ← ENNReal.ofReal_sum_of_nonneg ];
        · rw [ ← ntrace_sum, hSum, ntrace_one ] ; norm_num;
        · exact fun p _ => LamplighterStability.ntrace_proj_nonneg ( hHerm p ) ( hIdem p );
      · intro p q hpq; exact (by
        exact Set.disjoint_left.mpr fun x hx hx' => hpq <| by ext i; have := hx.symm; have := hx'.symm; simp_all +decide [ Dynamics.cyl ] ;);
      · exact fun p => measurableSet_cyl M p

lemma pvmMeasure_isProbability [NeZero d] (M : ℕ)
    (Epat : (Win M → Bool) → Matrix (Fin d) (Fin d) ℂ)
    (hHerm : ∀ p, (Epat p).IsHermitian)
    (hIdem : ∀ p, IsIdempotentElem (Epat p))
    (hSum : ∑ p : Win M → Bool, Epat p = 1) :
    IsProbabilityMeasure (pvmMeasure M Epat) :=
  ⟨pvmMeasure_univ M Epat hHerm hIdem hSum⟩

/-- The **PVM on `M`-definable sets**: `E_b = ∑_{p ∈ π_M(b)} E_p`, the matrix
whose normalized trace is `μ(b)`. -/
noncomputable def Edef (M : ℕ)
    (Epat : (Win M → Bool) → Matrix (Fin d) (Fin d) ℂ) (S : Set Cfg) :
    Matrix (Fin d) (Fin d) ℂ :=
  ∑ p ∈ patternsOf M S, Epat p

/-
Value of the induced measure on an `M`-definable measurable set:
`μ(b) = tr(E_b) = ∑_{p ∈ π_M(b)} tr(E_p)`.
-/
lemma pvmMeasure_defined (M : ℕ)
    (Epat : (Win M → Bool) → Matrix (Fin d) (Fin d) ℂ)
    (hHerm : ∀ p, (Epat p).IsHermitian)
    (hIdem : ∀ p, IsIdempotentElem (Epat p))
    {S : Set Cfg} (hS : Defined M S) :
    pvmMeasure M Epat S
      = ENNReal.ofReal (∑ p ∈ patternsOf M S, ntrace (Epat p)) := by
  rw [ ENNReal.ofReal_sum_of_nonneg ];
  · convert measure_defined_eq_sum hS ( pvmMeasure M Epat ) using 1;
    exact Finset.sum_congr rfl fun x hx => by rw [ pvmMeasure_cyl M Epat x ] ;
  · exact fun p hp => LamplighterStability.ntrace_proj_nonneg ( hHerm p ) ( hIdem p )

/-
The real-valued measure of an `M`-definable set equals `tr(E_S)`.
-/
lemma pvmMeasure_defined_toReal (M : ℕ)
    (Epat : (Win M → Bool) → Matrix (Fin d) (Fin d) ℂ)
    (hHerm : ∀ p, (Epat p).IsHermitian)
    (hIdem : ∀ p, IsIdempotentElem (Epat p))
    {S : Set Cfg} (hS : Defined M S) :
    (pvmMeasure M Epat S).toReal = ntrace (Edef M Epat S) := by
  rw [ pvmMeasure_defined M Epat hHerm hIdem hS ];
  convert ENNReal.toReal_ofReal _ using 1;
  · convert LamplighterStability.ntrace_sum _ _;
  · exact Finset.sum_nonneg fun p hp => LamplighterStability.ntrace_proj_nonneg ( hHerm p ) ( hIdem p )

/-
**Reduction of approximate invariance to a matrix-trace equivariance defect.**

The induced measure `μ = pvmMeasure M Epat` is `(M-1, η)`-invariant as soon as the
matrix equivariance defect of the PVM `E` over `(M-1)`-cylinders is `≤ η`.  Both
`cyl (M-1) b` and `L⟦cyl (M-1) b⟧` are `M`-definable, so their measures are the
normalized traces of `Edef M Epat`.
-/
lemma approxInvMeasure_of_equiv (M : ℕ) (hM : 1 ≤ M)
    (Epat : (Win M → Bool) → Matrix (Fin d) (Fin d) ℂ)
    (hHerm : ∀ p, (Epat p).IsHermitian)
    (hIdem : ∀ p, IsIdempotentElem (Epat p))
    {η : ℝ}
    (hEquiv : ∑ b : Win (M - 1) → Bool,
        |ntrace (Edef M Epat ((L : Equiv.Perm Cfg) '' cyl (M - 1) b))
          - ntrace (Edef M Epat (cyl (M - 1) b))| ≤ η) :
    ApproxInvMeasure (M - 1) η (pvmMeasure M Epat) := by
  unfold ApproxInvMeasure;
  convert hEquiv using 2;
  congr! 2;
  · convert pvmMeasure_defined_toReal M Epat hHerm hIdem _;
    convert defined_shift ( defined_cyl ( M - 1 ) _ ) 1 using 1;
    omega;
  · convert pvmMeasure_defined_toReal M Epat hHerm hIdem _;
    exact ( defined_cyl ( M - 1 ) _ ).mono ( Nat.sub_le M 1 )

end LamplighterStability.MeasureBridge