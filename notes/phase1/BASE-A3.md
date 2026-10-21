# BASE-A3 — the constant `A₃` of the first-component gain (C2, 2026-10-21)

**Result: branch 2 holds.** The per-cube `𝖰₁`, `𝖲₁` gains that the landed bridge supports are smaller than P6 (3.7)–(3.8), so
LFR row 9's formula for `A₃` is not reached; but `A₃` is a free positive constant of the typing, `A₀` is chosen after it, and
the smaller gains only raise the lower bound on `A₀`. No budget condition bounds `A₃` from above.

## 1. Source constants (P6 pp. 17–18, (3.5)–(3.9))
(3.5)/(3.6) are LF-1 for `Ψ̃`-type data: `||ψ|−1| < c₅`, pair differences `< δ`, cross differences `< δ`. P6 argues: if
`ψ ∈ Ψ̃(·; δ')` then the lifted field satisfies (1.15), (1.16) of P2 with `(9/8) K₁ δ'`; with `(9/8) K₁ δ' ≤ ½ δ_k` the test
`χ'_{k+1}` holds, so a failed test forces `ψ ∉ Ψ̃(·; 4δ_k/(9K₁))`, giving the exponent `γ₀ min{½βδ'²,…} = 8γ₀ p₀²/(9K₁)²`
(with `β δ² = p₀²`, i.e. `a` absorbed) per cube, and `1/(2·6^d K₁²)` for `χ_{k+1}` (tolerance `δ/K₁`).

## 2. What the landed bridge gives
`R/ChiBridge.lean`: `PsiTildeSet T ψ θ ⇒ InDomainR G 0 (3θ)` (the factor 3 is `||Ψ|²−1| ≤ θ(2+θ) ≤ 3θ` in the square form
`r2 : |∑Ψ² − 1| < δ` of the landed `InPsiTilde`, P2's (R2)), then `K₁·3θ < δ`; the landed statement takes `θ = δ/(6K₁)`
(strictness and `θ ≤ 1` slack: `θ` just below `δ/(3K₁)` would do). A failed test therefore gives `ψ_1 ∉ Ψ̃(·; δ/(6K₁))`, and
`lf1_violation_gain` + `baseMainAction_violation_gain_of_geometry` (`Base/BaseWitnessGainQS.lean`) give `𝒜 ≥ γ₀ β₁ θ²/2`,
hence (`violation_gain_real`, `κ = 6K₁`, `β₁ ≥ β/2`, `δ₀² a β = p₀²`) the factor `exp(−γ₀ p₀²/(8 a κ²))` for `½𝒜`,
and with overlap `m` per cube `γ₀ p₀²/(8 a (6K₁)² m)`. Against the source: `1/(288 a)` vs `4/81` (`𝖰₁`, ≈ 14a short) and vs
`1/4` (`𝖲₁`, ≈ 72a short), before the common overlap `6^d`. The pair part of a violation loses nothing; the loss is the
point part through the squared form of `r2`, and the `a` that the source drops (`a ∈ (1, 3/2)`). A sharper bridge would need
`InPsiTilde` with `||Ψ|−1|` (a change of the frozen P2 predicate); not attempted.

## 3. Why a smaller `A₃` suffices (branch 2)
* `Typing.A3` is a field of `Setting`; `Typing.Ok` asks only `A3_pos`; the witness of `PrefixInput` has `A3 := 1`
  (`Spine/Prefix.lean`). The conditions of LF-2 that contain `A₃` (`Counter/Conditions.lean` l0_e, l2, l11_d) have the form
  `C x^{…} ≤ ½ A₃ x^{2p₀}` for `x ≥ x₀` with `2p₀ > p₂`, i.e. lower bounds on `λ*` (`LamStar.lean`, `exists_lamStar`), not on `A₃`.
  `A₃'` (`l10`, `gam_ge`) is the separate constant of the kept costs.
* The consumer `baseFirst_operator_majorant_of_fiveShares` takes `A₃` free: it needs only `2 A₃ λ^{2p₀} ≤ gain`, which is
  `two_A3_le_gainBridge` / `two_A3_le_gainR_of_A1` (`Base/BaseA3.lean`) under `2A₃ ≤ γ₀A₀²/(8a(6K₁)²m)` and `8A₃ ≤ A₁²`.
  `exists_A0_for_A3` gives `A₀'` with this for all `A₀ ≥ A₀'` (the prefix `∃ A₀' ∀ A₀ ≥ A₀'`, LFR §I.1.4; `A₁ = A₀/(4K₂B₅)`).
* So the row-9 clause "`A₃ := ¼ min{…}`" is to be read as the condition `A₀ ≥ A₀'(A₃)`: **`A₀` large relative to the fixed
  `A₃`**, with `A₀' = 1 + 2A₃/c`, `c = γ₀/(8a(6K₁)²m)` (and the analogue for `A₁`). Row 9 (`A₃, A₃', A₃''` "derived from `A₀`") and
  the quantifier prefix are compatible after this reading; nothing else in the budget changes.

## 4. Open
The mixed bridge for `𝖰₁` (`ChiPrimeNewProp` from `Ψ̃` of the mixed data) is not proved; the constant for `𝖰₁` above assumes
the same tolerance `δ/(6K₁)` (the 3/4·δ, 5/4·δ tolerances of `RegMixedIneq` would change `6` to `12` or so — same argument).
Branch 1 (a sharper bridge) is not needed.
