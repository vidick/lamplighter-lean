# Statement comparison — main theorem (`export2`)

This file compares the statement of the main result (Theorem 1.1 of
*"Polynomial Hilbert–Schmidt stability of the lamplighter group"* by Alon Dogon
and Thomas Vidick) with the **formal** Lean statement that is proved in this
repository, so that a reader can check by hand that the formalization is faithful.

- Formal declaration: `LamplighterStability.lamplighter_HS_stability`
- File: `RequestProject/Main.lean`
- Discharged by: `core_main` (assembled in `RequestProject/MainAssembly.lean`)
- Axioms used: `propext`, `Classical.choice`, `Quot.sound` (standard only)

---

## 1. Informal statement (paper, `thm:main`)

> **Polynomial Hilbert-Schmidt stability of the lamplighter group.**
>
> For $A\in M_d(\mathbb{C})$ let
>
> $$\left\lVert A\right\rVert_{\mathrm{HS}}^2=\frac{1}{d}Tr(AA^*).$$
> 
> Let $0 < \kappa \leq 1/2$. Let
>
> $$
> M = \left\lceil C\kappa^{-20}\log(2/\kappa)\right\rceil,
> \qquad
> \varepsilon = c \kappa^7/M^2,
> $$
>
> for universal constants $C,c>0$.
>
> Then for every $d \in \mathbb{N}$ and $A,T \in U(d)$ unitaries such that
>
> $$
> \left\lVert A^2 - 1 \right\rVert_{\mathrm{HS}} \leq \varepsilon
> $$
>
> and
>
> $$
> \left\lVert [A, T^{-i}AT^i] \right\rVert_{\mathrm{HS}} \leq \varepsilon
> \qquad \text{for all } 0 \leq i \leq 2M,
> $$
>
> there exist unitaries $\widetilde{A},\widetilde{T} \in U(d)$ such that
>
> $$
> \widetilde{A}^2 = 1
> $$
>
> and
>
> $$
> \widetilde{T}^{-i}\widetilde{A}\widetilde{T}^i
> \text{ commutes with } \widetilde{A}
> \qquad \text{for all } i \in \mathbb{Z},
> $$
>
> and further
>
> $$
> \left\lVert A - \widetilde{A} \right\rVert_{\mathrm{HS}} \leq \kappa,
> \qquad
> \left\lVert T - \widetilde{T} \right\rVert_{\mathrm{HS}} \leq \kappa.
> $$

---

## 2. Formal statement (Lean)

```lean
theorem lamplighter_HS_stability :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (κ : ℝ), 0 < κ → κ ≤ 1 / 2 →
        ∀ (M : ℕ) (ε : ℝ),
          M = ⌈C * κ ^ (-20 : ℤ) * Real.log (2 / κ)⌉₊ →
          ε = c * κ ^ 7 / (M : ℝ) ^ 2 →
          ∀ (d : ℕ) (A T : Matrix.unitaryGroup (Fin d) ℂ),
            normHS ((A : Matrix (Fin d) (Fin d) ℂ) ^ 2 - 1) ≤ ε →
            (∀ i : ℕ, i ≤ 2 * M →
              normHS (⁅(A : Matrix (Fin d) (Fin d) ℂ),
                (star (T : Matrix (Fin d) (Fin d) ℂ)) ^ i
                  * (A : Matrix (Fin d) (Fin d) ℂ)
                  * (T : Matrix (Fin d) (Fin d) ℂ) ^ i⁆) ≤ ε) →
            ∃ (A' T' : Matrix.unitaryGroup (Fin d) ℂ),
              (A' : Matrix (Fin d) (Fin d) ℂ) ^ 2 = 1 ∧
              (∀ i : ℤ, Commute (A' : Matrix.unitaryGroup (Fin d) ℂ)
                (T' ^ (-i) * A' * T' ^ i)) ∧
              normHS ((A : Matrix (Fin d) (Fin d) ℂ)
                  - (A' : Matrix (Fin d) (Fin d) ℂ)) ≤ κ ∧
              normHS ((T : Matrix (Fin d) (Fin d) ℂ)
                  - (T' : Matrix (Fin d) (Fin d) ℂ)) ≤ κ :=
  core_main
```

---

## 3. Correspondence table

| Paper object | Lean object | Notes |
|---|---|---|
| Universal constants $C, c > 0$ | `∃ C c : ℝ, 0 < C ∧ 0 < c ∧ …` | Existentially quantified up front; the rest of the statement holds for *these* constants, matching "for universal constants $C,c>0$". |
| $0 < \kappa \le 1/2$ | `∀ (κ : ℝ), 0 < κ → κ ≤ 1 / 2` | Identical hypothesis on the tolerance. |
| $M = \lceil C\kappa^{-20}\log(2/\kappa)\rceil$ | `M = ⌈C * κ ^ (-20 : ℤ) * Real.log (2 / κ)⌉₊` | `⌈·⌉₊` is the natural-number ceiling; `M : ℕ`. `κ ^ (-20 : ℤ)` is `κ^{-20}` (zpow). `Real.log` is the natural logarithm, matching $\log$. The argument is passed as a `∀ M` constrained to this exact value (equivalent to substituting the closed form). |
| $\varepsilon = c\,\kappa^7/M^2$ | `ε = c * κ ^ 7 / (M : ℝ) ^ 2` | `M` cast to `ℝ` before squaring; division in `ℝ`. Passed as a `∀ ε` constrained to this exact value. |
| $d \in \mathbb{N}$ | `∀ (d : ℕ)` | Dimension. |
| $A, T \in U(d)$ unitaries | `A T : Matrix.unitaryGroup (Fin d) ℂ` | The unitary group of $d \times d$ complex matrices; the coercion `(A : Matrix (Fin d) (Fin d) ℂ)` recovers the underlying matrix. |
| $\| A^2 - 1 \|_{\mathrm{HS}} \le \varepsilon$ | `normHS ((A : Matrix …) ^ 2 - 1) ≤ ε` | `normHS` is the normalized HS norm (see §4). `1` is the identity matrix. |
| $\| [A, T^{-i}AT^{i}] \|_{\mathrm{HS}} \le \varepsilon$ for $0 \le i \le 2M$ | `∀ i : ℕ, i ≤ 2 * M → normHS (⁅A, (star T) ^ i * A * T ^ i⁆) ≤ ε` | `⁅·,·⁆` is the ring commutator $XY - YX$. Since `star T = T⁻¹` in the unitary group, `(star T) ^ i = T^{-i}`, so `(star T)^i * A * T^i = T^{-i} A T^{i}`. Index range $0 \le i \le 2M$ becomes `i : ℕ, i ≤ 2 * M`. |
| $\exists \widetilde A, \widetilde T \in U(d)$ | `∃ (A' T' : Matrix.unitaryGroup (Fin d) ℂ)` | $\widetilde A = $ `A'`, $\widetilde T = $ `T'`. |
| $\widetilde A^2 = 1$ | `(A' : Matrix …) ^ 2 = 1` | Genuine order-two (involution). |
| $\widetilde T^{-i}\widetilde A\widetilde T^{i}$ commutes with $\widetilde A$, $\forall i \in \mathbb{Z}$ | `∀ i : ℤ, Commute A' (T' ^ (-i) * A' * T' ^ i)` | `Commute x y` is `x * y = y * x`. Integer powers `T' ^ (-i)`, `T' ^ i` taken in the unitary group; quantified over all `i : ℤ`. |
| $\| A - \widetilde A\|_{\mathrm{HS}} \le \kappa$ | `normHS ((A : Matrix …) - (A' : Matrix …)) ≤ κ` | Perturbation bound on `A`. |
| $\| T - \widetilde T\|_{\mathrm{HS}} \le \kappa$ | `normHS ((T : Matrix …) - (T' : Matrix …)) ≤ κ` | Perturbation bound on `T`. |

---

## 4. Definitions referenced

- **`normHS`** (`LamplighterStability.normHS`, from `RequestProject/Foundations.lean`):
  the *normalized* Hilbert–Schmidt norm
  $$\left\lVert X\right\rVert_{\mathrm{HS}}=\sqrt{\tfrac{1}{|\iota|}\sum_{i,j} |X_{ij}|^2}.$$
  For `ι = Fin d` this is $\sqrt{\tfrac{1}{d}\sum_{i,j}|X_{ij}|^2}$, matching the
  paper's normalized HS norm.
- **`⁅·,·⁆`** : the ring (Lie) commutator `X * Y - Y * X`.
- **`star T`** : for `T` in `Matrix.unitaryGroup`, `star T = T⁻¹`, hence
  `(star T) ^ i = T^{-i}`.
- **`⌈·⌉₊`** : `Nat.ceil`, the natural-number ceiling.

---

## 5. Faithfulness assessment

The Lean statement is a faithful transcription of the paper's Theorem 1.1:

- **Constants.** The universal constants $C, c$ are existentially quantified at the
  outermost level, so the theorem asserts the existence of constants for which the
  bound holds — exactly the meaning of "for universal constants $C,c>0$".
- **Closed-form window and tolerance.** $M$ and $\varepsilon$ are bound to the precise
  closed forms from the paper (the `∀ M`/`∀ ε` with equality constraints is logically
  the same as substituting the closed forms directly).
- **Hypotheses.** Both defect hypotheses ($\|A^2-1\|_{\mathrm{HS}} \le \varepsilon$ and the
  approximate commutation along the orbit for $0 \le i \le 2M$) appear unchanged, with
  $T^{-i}AT^i$ rendered via `star`.
- **Conclusion.** All four conclusions are present: $\widetilde A^2 = 1$, the genuine
  commutation $\forall i \in \mathbb{Z}$, and the two perturbation bounds by $\kappa$.
- **No extra hypotheses** are added beyond those in the paper; no hypothesis is
  vacuous, and the statement is not weakened.

One minor presentational difference: the orbit hypothesis is quantified over
`i : ℕ` with `i ≤ 2 * M` (the paper writes $0 \le i \le 2M$), whereas the genuine
commutation conclusion is over all `i : ℤ`; both match the paper exactly.
