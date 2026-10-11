# Review of `notes/phase1/OBSERVABLES.md` (brief D-TP-review)

Referee report, 2026-10-11. Pure mathematics; no Lean was written or run. Read: `OBSERVABLES.md` in full;
`Balaban/Correlations/C1Star.lean` (`C1Star`, `C1StarF1`–`F3`, `RootFAndC1Star`), `Assembly.lean`,
`LemmaThree.lean` (the only consumer of `C1StarF2`'s `em` clause), `BoundsNu.lean`, `ZeroLimit.lean`/`GoldstoneStep.lean`
(as consumers); the frozen `LogPartitionMultiscale.lean` and `LowTemperatureCorrelations.lean`; P9 pp. 514–519
(text layer of `sources/s002200050510.pdf`, extracted to the scratch directory); `SMALLFIELD.md` §3.5/Thm 5.3;
`LF-RECONSTRUCTION.md` §I.1.1; `POLYMER.md` §§2.5, 4.1. I did not re-read P1, P4–P7 beyond what the above quote.

## Verdict

**Accept with revisions.** The architecture is sound and the part that matters for Root-C (the derivation of
(F1)–(F3) from the last step, the Tannery argument, the dictionary with Root-F) survives an attempt to refute it.
F-B is correct and needs the stated Lean change. F-A is not forced and its stated reason is partly wrong, but the
change is harmless and I recommend it. I found one further statement-level error in `C1StarF2` (O-02: the bound on
`em` is false on small tori) that the document did not see and that must be fixed together with F-B. There are also
bookkeeping slips in Lemma 1.1 (O-04, O-05) that do not change the conclusion. The main risk of the document
(P9 (3.13) on subdomains for the non-product Gaussian measure) is not resolved and cannot be resolved by this review.

## Verdicts on F-A and F-B

**F-A: not needed for correctness; adopt as a safe weakening.**

* Root-F's `kf` is fixed by `L^kf √ν ≤ L`, `1/2 ≤ L^{kf+1}√ν`; it does not mention β, and `RootFAndC1Star` does not
  tie `C1Star.J` to Root-F's `kf`. `J_bounds` (`1/2 ≤ L^J √ν ≤ L²`) is also β-free. So the Lean interface as written
  is satisfiable by a β-independent `J`; it is not contradictory.
* The β-dependence enters only if the *flow* uses P9/P4's own stopping rule: P9 p. 515 takes `k(v)` the smallest index
  with `v_k > (7/8)L^{-2}`, and `v_j = νL^{2j}δ_j` with `δ_j = 1 + O(1/β)` produced by the flow (`SMALLFIELD.md`
  Thm 5.3, `LF-RECONSTRUCTION.md` §I.1.1: `k_f` is the first `k` with `ν_k > (7/8)L^{-2}`). So the document's premise
  about P9's `k` is right. The threshold `k_0` (`β_kν_k ≤ 1`) plays no role in `J`: it only decides which backgrounds
  are `ν`-free (O-06). So `k₀` does not make `J` depend on β in any way that matters.
* What the derivation uses of the last scale is only: the mass window `ν_{J-1} ∈ (cL^{-2}, 1]` at the last
  fluctuation integral (so that the covariance is massive and G-5's `ν_j ∈ [0,1]` holds), and the two inequalities of
  `J_bounds`. The alternative rule `k^♯(ν) = min{k : νL^{2k} > (13/16)L^{-2}}` gives `ν_{k♯} ∈ (0.8L^{-2}, 0.86]` for
  β large (since `|δ_k − 1| ≤ C/β`), which meets that window, and the bookkeeping of the reconstruction already runs on
  the β-free `k̂_f` (`LF-RECONSTRUCTION.md` Lemma I.5.6: `k_f ≤ k̂_f ≤ k_f + 1`). The remaining uncertainty is only
  whether P4 §6 uses `7/8` rather than a fixed positive multiple of `L^{-2}`; I read P9 p. 515 as using only the
  qualitative "massive, mass ≈ L^{-1}".
* Moving `J, J_pos, J_tendsto, J_bounds` inside `data` makes `C1Star` weaker, hence easier to inhabit, and costs about
  40 lines: `Assembly.lean` destructures `J` at line 49 but uses `hJp/hJt/hJb` only after `data β hβS` (lines 82–123),
  so the change is local. I checked that nothing before `intro β` uses `J`.

Exact Lean change (F-A), in `C1Star.lean`: delete the fields `J`, `J_pos`, `J_tendsto`, `J_bounds`, and replace `data` by

```
data : ∀ β : ℝ, βStar ≤ β →
  ∃ (J : ℝ → ℕ) (ξ : ℝ → ℕ → Fin 3 → ℝ) (μ : ℕ → ℝ → (Fin d → ℤ) → ℝ)
    (rtr rlg : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (em : ℕ → ℝ → (Fin d → ℤ) → ℝ)
    (rtrLim rlgLim : ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (rtrZero rlgZero : (Fin d → ℤ) → (Fin d → ℤ) → ℝ),
    (∀ ν ∈ Set.Ioc (0 : ℝ) 1, 1 ≤ J ν) ∧ Tendsto J (𝓝[>] 0) atTop ∧
    (∀ ν ∈ Set.Ioc (0 : ℝ) 1, 1 / 2 ≤ (L : ℝ) ^ J ν * Real.sqrt ν ∧ (L : ℝ) ^ J ν * Real.sqrt ν ≤ (L : ℝ) ^ 2) ∧
    C1StarF1 L γ₀ cXi β ξ ∧ C1StarF2 d N L M hN cStar ρ₀ ρ₁ J β ξ μ em ∧
    C1StarF3 d N L M hN a cStar cPrime ρ₀ J β ξ μ rtr rlg rtrLim rlgLim rtrZero rlgZero
```

and in `Assembly.lean` move the `J`-destructuring of line 49 into the `obtain` of line 85 (`data β hβS`).

**F-B: confirmed. The printed remainder bound is false; the proposed fix is correct.**

* Argument. Take `x−y = z` with `L^{Jθ₀}·C ≲ |z| ≲ L^{J-1}`, `θ₀ = (d−2)/(d−2+ρ₀) < 1`. The exact transverse
  function is, at leading order in `β^{-1}`, `(βγ)^{-1}(−Δ+ν)^{-1}(z)`, and `mainTr` contains only `T_j`, `j < J`.
  By the Woodbury identity (5.3) of the document, `(−Δ+ν)^{-1} = Σ_{j<J} T_j + (tail)`, with tail
  `E = (βγ_{J-1})^{-1} P_J A_J^{-1} P_J^T ≥ 0`, a positive kernel of size `β^{-1}L^{-J(d-2)}` for `|z| ≲ L^J` (the
  kernel `T_j(z)` is positive and smooth near `z = 0`, so `Σ_{j≥J} T_j(z) ≈ c L^{-J(d-2)}`). This tail is not in
  `m_J m_J Σ_{j<J}(βγ_j)^{-1}T_j`, and it cannot be absorbed in the small-field remainders `R_J`, `∂²(R^{(J)}+P^{(J)})`,
  which are `O(β^{-3/2+ρ₁}(1+|z|)^{-(d-2+ρ₀)})` and `O(β_{J-1}^{-2})`. Hence `r_tr` contains `E`. Since
  `L^J√ν ≤ L²` gives `L^{-J(d-2)} ≥ L^{-2(d-2)}ν^{(d-2)/2}`, we have
  `E ≳ β^{-1}ν^{(d-2)/2}`, while `(1+|z|)^{-(d-2+ρ₀)} ≪ ν^{(d-2)/2}` in the window, so for fixed β and ν ↓ 0 no
  constant `c_*` independent of ν works. The conclusion does not depend on which reading of P9 (4.14) one takes (see
  the answer to Q2 below): under the regular reading the same tail sits in the not-yet-integrated field at scale `J`.
  The document's remark in §5.3 that `E'` "is zero in the regular reading" is therefore wrong; `E'` is never zero.
* The upper bound of the tail is as claimed: `L^J ≥ 1/(2√ν)` gives `L^{-J(d-2)} ≤ 2^{d-2}ν^{(d-2)/2}` and
  `L^J√ν ≤ L²` gives `e^{-δL^{-J}|z|} ≤ e^{-δ√ν|z|/L²}`.
* Root-C still follows, and only constants change. Step B (`BoundsNu.lean`): with `s = √ν|z|`,
  `ν^{(d-2)/2}e^{-c's} = s^{d-2}|z|^{-(d-2)}e^{-c's} ≤ C(d,c')(1+|z|)^{-(d-2)}e^{-c's/2}` for `|z| ≥ 1`, and
  `ν^{(d-2)/2} ≤ 1 ≤ 2^{d-2}(1+|z|)^{-(d-2)}` for `|z| < 1`. So the constant `c` of Root-C increases by
  `cStar · C(d,cPrime)` and `c'` is replaced by `min(cPrime/2, δ_G/(2L²))`; both are fixed before β (cStar, cPrime
  are). The exponent in the frozen Root-C bounds is `d−2` with no `ρ₀`, so the new term fits exactly. Step C
  (`ZeroLimit.lean`): for fixed `x`, `ν^{(d-2)/2} → 0`, so the bound on `rtrZero`, `rlgZero` is still
  `cStar(1+|x|)^{-(d-2+ρ₀)}`; `ρ₀` and the Goldstone constant of the frozen statement are unchanged (the frozen
  Goldstone constant `c` still dominates `cStar` plus the `m₀²/(βγ)` comparison terms already in `Assembly.lean`'s `c`).

Exact Lean change (F-B), in `C1StarF3`, replace the two bounds by

```
|rtr ℓ ν x y| ≤ cStar * ((1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) + ν ^(((d : ℝ) - 2) / 2)) *
    Real.exp (-(cPrime * Real.sqrt ν * ‖x - y‖)) ∧
|rlg ℓ ν x y| ≤ cStar * ((1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) + ν ^(((d : ℝ) - 2) / 2)) *
    Real.exp (-(cPrime * Real.sqrt ν * ‖x - y‖))
```

`abs_rtrLim_le` (limit along tori of the bound at fixed `ν`) is unchanged in form. In `BoundsNu.lean` the lemma `hrem'`
(lines 118–133) gets the extra step above; `c` gets one more summand and `c'` is halved (`hc'`, `Assembly.lean` line 82).
Estimated edit: 100–200 lines, as the document says.

## Findings

### O-01 (MAJOR) F-B is real; `E'` is never zero
Location: §5.2, §5.3 (F3), §5.4. Argument and fix: the F-B verdict above. Additionally, §5.3's sentence "`E'` ... (zero in
the regular reading)" must be deleted; the tail `E` belongs to `F_J` (massive final covariance) or to the unintegrated
field at scale `J` (regular reading), and in both cases to `r`.

### O-02 (MAJOR, new) The `em` bound of `C1StarF2` is false for small tori
Location: `C1Star.lean`, third conjunct of `C1StarF2`; §2 Remark 2.0, §5.3 (F2).
The statement asks `|m_ℓ − m_J(x)| ≤ cStar β^{-2}L^{-2J(d-2)}` for **every** torus with `ML^{J+1} ∣ ℓ`, including
`ℓ = ML^{J+1}`. The derivation in §5.3 uses `M_J(x;h,h) = m_J(x)h`, i.e. that `Σ_{X∋x} M^{(j)}(x,X;h,h) = 0`. By Remark 2.0
this holds only for non-winding `X`; the winding sums are torus-dependent and are discarded as "bounded uniformly",
but they are not bounded by `β^{-2}L^{-2J(d-2)}`. Concretely, the winding term at scale `j = J` contributes
`β_{J-1}^{-1/2}·β^{-1/2+ρ₁}L^{-Jρ₀}e^{-κL} ≈ β^{-1+ρ₁}L^{-J((d-2)/2+ρ₀)}e^{-κL}` at `ℓ = ML^{J+1}`, which exceeds
`β^{-2}L^{-2J(d-2)}` for large `J` (because `(d-2)/2 + ρ₀ < 2(d-2)`). This is not an artefact of the crude per-term
bound: physically `m_ℓ − m_∞ = ((N−1)/(2β))(G_ℓ(0) − G_∞(0)) + … ≈ cβ^{-1}ν^{(d-2)/2}e^{-√νℓ}` (image sum of the massive Green
function), and `√νℓ ≈ ML·L^J√ν ∈ [ML/2, ML³]` is bounded, so this is of size `β^{-1}ν^{(d-2)/2}` times a constant,
while the claimed bound is `β^{-2}ν^{d-2}`. For fixed β and ν ↓ 0 no constant `cStar` works.
Consumer check: `em` enters only through `LemmaThree.lean` (`abs_m_sub_magJ_le`), which applies it for `ℓ` divisible by
`q^{J+1}` through `LimAlong.abs_sub_le`, so only large `ℓ` matter; the two-point clause (F3) is not affected, because
there the winding terms are `≲ β^{-1}ν^{(d-2)/2}e^{-c√νℓ} ≤ cStar ν^{(d-2)/2}e^{-c'√ν|z|}` for `|z| < ℓ/2`, which the F-B
term absorbs.
Fix: in `C1StarF2` replace the last conjunct by
```
∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ x, ∃ ℓ₀ : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ], ℓ₀ ≤ ℓ → M * L ^ (J ν + 1) ∣ ℓ →
  blockM d N ℓ hN β ν = magJ L d (ξ ν) (fun j => μ j ν) β (J ν) x + em ℓ ν x ∧
  |em ℓ ν x| ≤ cStar * (β ^ 2)⁻¹ * ((L : ℝ) ^ (2 * J ν * (d - 2)))⁻¹
```
and in `LemmaThree.lean` take `n₀ := ℓ₀ + J ν + 1` in `⟨J ν + 1, …⟩` (then `q^{n₀} ∣ ℓ` gives `ℓ ≥ q^{n₀} ≥ ℓ₀` since
`q ≥ 2`). In §5.3 (F2) add: the winding terms of the one-point sums are `O(e^{-κℓ/(ML^J)})` and are dropped by taking
`ℓ ≥ ℓ₀(ν)`.

### O-03 (MINOR) Justification of F-A
Location: Summary, §5.4 F-A. The text says the flow's `J = k_f(β,ν)+1` "depends on β through δ_k" and that `C1Star` therefore
cannot be satisfied. As shown above, the dependence is only a feature of the chosen stopping rule; a β-free rule works
if P4 §6 needs only a fixed positive multiple of `L^{-2}`. Rewrite as "recommended hedge; not forced" and drop the claim that
the alternative "changes P4 §6" until the P4 §6 use of `7/8` is read.

### O-04 (MINOR) Lemma 1.1: `ρ₁ = 3ρ₂` cannot close the row `R_1^{k+1,k+1}` with constant 1
Location: Lemma 1.1 (E1), §2.1 (2.1)–(2.2), §3.6 table. The new term of `R_1^{k+1,k+1}` is `C β^{-1/2+3ρ₂}η^{(d-2)/2−3(d-2)ρ₂}`
with a constant `C ≥ 1` coming from the Cauchy estimates of the background. The hypotheses (2.1), (2.2) carry the
constant 1, so the induction needs `Cβ^{-1/2+3ρ₂} ≤ β^{-1/2+ρ₁}`, which fails for `ρ₁ = 3ρ₂` (the factor `η^{…}` is 1 at
`k = 0` and gives no room). P9 avoids this because its (2.18) carries a constant `K₀` ("global bound `K₀β^{-1/2+ρ₁}ξ^{ρ₀}`");
the document dropped it. Fix: either put a constant `K` before β into (2.1)–(2.2) and C-1*'s `cStar` (new terms need
`K ≥ C_new`, and `C_new` does not depend on `K`), or take `ρ₁ := 4ρ₂` (then `ρ₁ ≤ γ/(d−2) ≤ 1/2 < 1`). The first-order row T1
(`β^{-1/2+2ρ₂}`, slack `β^{-ρ₂}`) is not affected. (P9 (3.17) prints `β^{-1/2+3ρ₂}` for T1; the document's `+2ρ₂` follows from two
Cauchy factors `p₁²`; I agree with the document there.)

### O-05 (MINOR) Lemma 1.1 (E3) and the claim about P9's printed exponents
Location: Lemma 1.1, remark after it, §3.6 table. The row `R_2^{k+1,k+1}` is bounded by `ξ_j^{ρ₀+γ-1}η^{1−2(d−2)ρ₂}` (two
Cauchy factors), and reducing it "as T2" needs `ρ₀ ≤ 1 − 2(d−2)ρ₂`, not (E3) `ρ₀ ≤ 1 − (d−2)ρ₂`. (E4) `γ > 2(d−2)ρ₂` was
already stated with the factor 2, so (E3) is inconsistent with (E4) and with the table. P9 (3.23) itself prints
`1 − ρ₀ − (d−2)ρ₂ ≥ 0, γ − (d−2)ρ₂ > 0` for T2 (this agrees with E3, E4 as T2 alone needs), so the document's assertion that P9 p. 511
"differs from the derived list" is not established; the printed `1 − 3(d−2)ρ₂` probably covers the three-factor row. Harmless for
the explicit choice: `ρ₂ ≤ (1−γ)/(2(d−2))` gives `2(d−2)ρ₂ ≤ 1 − γ`, so `ρ₀ = γ` satisfies the corrected (E3). Restate (E3) as
`ρ₀ ≤ 1 − 2(d−2)ρ₂`, delete the comparison with P9 p. 511 (or mark it unverified; E-O4 should then be dropped or kept as "unconfirmed").

### O-06 (MINOR) Lemma 4.2 lacks the mass factor, and the index range needs one line
Location: §4.3, Lemma 4.2. The sum bound is stated as `Cβ^{-2}(1+|x−y|)^{-(d-2+ρ₀)}` with no factor `e^{-c'√ν|x−y|}`, but `C1StarF3`
needs one. It holds: for `j ≤ k_0` we have `νL^{2j}δ_j·β_j ≤ 1`, hence `L^{jd} ≲ (βν)^{-1}` and `L^j ≲ (βν)^{-1/d} ≤ ν^{-1/2}`,
so `e^{-δ_GL^{-j}|z|} ≤ e^{-δ_G√ν|z|}`. Add this to the statement. The proof of the first bound (Lipschitz of `G_jQ_j^*` and
`C^{(j)}_{tr}` in `ν_j`, `GREEN.md` G-5(b), product of three factors) is correct as far as the statement of G-5(b) goes; G-5(b) is itself
"ready but depending on the plan-level block 4.5" in `GREEN.md`, so Lemma 4.2 is conditional on it. Index: `G^{(j)}` uses `H_{j-1}` from the
background `φ_{j-1}`, which is `ν`-free iff `j−1 ≤ k_0`; the kernels affected are `T_i`, `i ≤ k_0`, which matches the range of Lemma 4.2.

### O-07 (MINOR) Lemma 2.1 (2): the Schur step needs the column `Hh`
Location: §2.2, proof of Lemma 2.1 (2). From `h^T H = 0` and `H = SHS^T` (`S` in the stabilizer of `h`) the proof concludes `H = h_{j-1}(I − h⊗h)`.
It must also show `Hh = 0`: `Hh` is a vector in `h^⊥` fixed by all of `S ≅ O(N−1)`; for `N ≥ 3` the representation on `h^⊥` has no fixed vector,
and for `N = 2` the reflection fixing `h` acts as `−1` on the line `h^⊥`. One sentence. The same applies to `C^{(j-1)}` (block diagonal
needs the cross blocks to vanish by the same argument). The lemma is otherwise correct, including `N = 2`.

### O-08 (MINOR) Small points on constants and requirements
(i) Lemma 1.1 allows `α₁ ∈ (0,γ]`, and (E7) is `ρ₀ ≥ γ − α₁`; Root-F's frozen `δ` must be positive and equals `γ − α₁`, so `α₁ < γ` is needed.
(ii) §4.2 requirement 1 treats the factor `e^{⟨g,φ⟩}` as a bound on moduli only. The upper bound `|e^{⟨g,φ⟩}| ≤ e` is correct
(`|φ| = 1`, `‖g‖_{ℓ¹} < 1`). If any estimate of P7 §§2–3 uses a lower bound or a positivity of the large-field density (partition-function
ratios in the refund route), it needs `Re e^{⟨g,φ⟩} ≥ e^{-1}cos 1` on windows, a constant factor of the same type; state this as part of
requirement 1 and have the LF-4 author confirm that no step uses positivity beyond that. This is the same positivity remark as in
`POLYMER.md` §4.4 (the principal logarithm), which is correct as written.
(iii) Lemma 3.2 states the mixed bound `32B` and proves `24B`; both are fine.

### O-09 (MAJOR as a risk, not as an error) P9 (3.13) on subdomains / PE-M for a non-product measure
Location: Prop 3.3, R-M1, R-M2; Question 5 of §7.6. I tried to refute the reduction and did not succeed, but I cannot close it either.
* The reduction `⟨F₁;F₂⟩^T = ∂_{λ₁}∂_{λ₂} log Ξ(λ₁,λ₂)` and (M1)–(M3) are correct for a measure of the form (H-MY). The step that needs care is that the
  λ-dependence of an activity enters only through polymers containing `X_s`: this uses that `F_s` has a localization expansion in the **composite**
  variable `ψ^{(j)}_k(ψ^{(k)}(θ) + zψ')` with the same ψ' as the Gaussian; since the covariance `C^{(k)} = (Δ_tr^{(k)} + aL^{-2}Q^*Q)^{-1}` is
  non-local, its inverse is a quasi-local operator (exponentially decaying couplings, not finite range), and the product form in
  (H-MY)(i) holds only after the off-diagonal part of `C^{-1}` is expanded into polymer couplings (P6 (4.35)–(4.42)). That expansion adds
  polymers whose activities depend on `ψ'` in the blocks where `F_s` also depends on `ψ'`; (M1) survives only if the expansion is done *before* the
  λ-dependence is introduced and the extra polymers are counted as part of `U` (they carry no λ). The document asserts this; it must be checked in
  P6 (4.35)–(4.42) and in the hole version. Until then Prop 3.3 stays at "reduced" and the O3/O7 packages are high risk (as stated).
* One further point for R-M2: with large-field holes the Gaussian measure is on `Ω^c`, so the covariance is a *restriction* and the
  decay of `C^{(k)}` across the hole has to be quasi-local relative to the hole boundary; this is the "boundary term" role of `B`, and the
  λ-independence argument above has to include it.

### O-10 (MINOR) The last step is the weakest part of Theorem 5.2
Location: §5.1–5.2, Prop 5.1 (marked "sketched"). Nothing in P9 or in the document computes the last Gaussian term; see Q2. Prop 5.1 should be stated with
`G_J^{tr} = Σ_{j<J-1} (βγ_j)^{-1}m_Jm_JT_j + (βγ_{J-1})^{-1}m_Jm_J P_{J-1}A_{J-1}^{-1}P_{J-1}^T` (massive final covariance) so that
the tail appears in the *statement* of the layer rather than in `r`. This would make F-B a statement about `mainTr`'s convention and is the cleaner
route if the Lean interface may be changed again (replace the last summand of `mainTr` by the massive one, then the remainder bound with
`(1+|z|)^{-(d-2+ρ₀)}` is plausible again; the `ν^{(d-2)/2}` term is then needed only for `r_lg`, `E`-corrections at `|z| ≳ L^J`). I do not recommend this now:
F-B as stated is correct and local, and the massive summand would need a new Lean kernel.

## Remaining checks (no finding)

* Lemma 1.1 proof: the explicit `ρ₂ = ½ min{…}` satisfies (E1)–(E8) after O-04/O-05 are applied. (E4): `ρ₂ < γ/(2(d−2))` strict.
  `ρ₁ = 4ρ₂ ≤ γ/(d−2) ≤ 1/2`.
* Lemma 2.3(a),(b): the arithmetic is correct. The mass factor requires `L^k ≤ L²/√ν`, true for `k ≤ J` by `J_bounds`.
* §3.5 T1, T2 and §3.6 rows: the exponents `β^{-1/2+2ρ₂}`, `η^{(d-2)/2−2(d-2)ρ₂}` (T1) and `β^{-1+ρ₁+ρ₂}ξ_j^{ρ₀+γ−1}η^{1−(d−2)ρ₂}` (T2) agree with a
  recomputation from (B1)–(B4), and with P9 (3.23), (3.30). The identification of the Gaussian main term (Lemma 3.5) is exact.
* §5.3 (F2) arithmetic: `2Σ_{n≥1}β_{J-1}^{-n-1} + 2β_{J-1}^{-2} ≤ 6β_{J-1}^{-2}` and `β_{J-1}^{-2} ≤ 4β^{-2}L^{-2(J-1)(d-2)}` are correct, with the exception of
  the winding terms (O-02).
* Lemmas 5.3 and 5.4 (limits along tori and as ν ↓ 0): correct given (CONT) and Root-F's agreement clause. In Lemma 5.4 the terms with `j = J(ν)` are the
  last-step terms, which tend to 0; for fixed `(i,j)` the layer objects are the ordinary-step objects once `J(ν) > j`.
* Dictionary (§1.2), Lemma 2.2: correct. The constant-configuration statement `φ_{j-1}(·;h,h) = h` uses uniqueness of the small solution (`BACKGROUND.md` I-1).
* §6 (β-dependence): the list of the four constants that must be uniform in β (`q`, `c'`, `ρ₀`, the constant in `|γ_∞−1| ≤ c/β`) is right, and the flow
  produces them before β. After F-B and O-02 the constants `cStar`, `cPrime` are still before β (F-B adds a factor `C(d,cPrime)` only). Nothing in §6 changes.
* The five LF-4 requirements (§4.2): requirements 2–5 are the right ones (joint covariance of the coset average, locality in `g`, sup bounds on the
  `g`-polydisc, (CONT) with no definition using `k̂_f`); requirement 1 needs the addition of O-08(ii).

## Answers to §7.6, questions 2 and 3 (from P9 and the P4/P5 conventions; not for seaturtle2)

**Q2. Is the final covariance massive or regular; does `F_{k+1}` contain the tail?**
The covariance of the final Gaussian integral is the **massive** one, `(Δ_tr^{(k_f)})^{-1} = A_{k_f}^{-1}` with no coupling `aL^{-2}Q^*Q` (there is no coarse
variable), and the final function `F_J(h,g)` contains the tail `E = (βγ_{J-1})^{-1}P_J A_J^{-1}P_J^T` in its last Gaussian summand.
Evidence from P9 p. 515: the last integral is over "the fluctuation variable `ψ_k − h`" with "a quadratic form with a massive covariance, the mass `≈ v_k ≈ L^{-1}`",
and after it "we have performed now all the integrations down to 0-momentum, so over all scales". So no integral remains after the last one; the sum
(4.14) then has to produce the complete Gaussian propagator `(βγ)^{-1}(−Δ+ν)^{-1}` at leading order, which by (5.3) of the document is
`Σ_{j<J-1}T_j + P_{J-1}A_{J-1}^{-1}P_{J-1}^T`. P9 prints the regular `C^{(j)}_{tr}` in (4.14) for every `j`, including the last, and never evaluates the last term separately; that is
a misprint of the last term (or the regular `C^{(k)}` standing for the full covariance), and is the content of E-O6. It cannot be that the tail is dropped: it has size `β^{-1}L^{-J(d-2)}`,
larger than any other discarded term (`P^{(J)}` is `β_{J-1}^{-2}e^{-2κd}`). Under the opposite reading the unintegrated variable at scale `J` produces the same tail (O-01).
Action: state Prop 5.1/LF-8 with the massive final term (O-10), or leave it in `r` with the F-B bound; both are consistent.

**Q3. Are the Gaussian kernels massless or massive for `j ≤ k_0`?**
P9's own formulas are massive throughout: (4.12)–(4.14) use `G_j = (−Δ + a_jQ_j^*Q_j + v_j)^{-1}` for all `j`, and the bound on `C_{k,tr}` (p. 518) has `e^{-δ(√v + L^{-j})|x−y|}` in
every term; P9 never mentions the `ν`-free backgrounds of P5 (1.9) and is silent about the switch at `k_0`. In the class (Def-6, `SMALLFIELD.md` §1.6, P5 (1.9)) the backgrounds `φ_{j-1}` for `j−1 ≤ k_0`
are `ν`-free, and `G^{(j)} = H_{j-1}C^{(j-1)}H_{j-1}^*` is defined from the derivative `H_{j-1}` of that background, so the kernels `T_i`, `i = j−1 ≤ k_0`, are **massless**, and the kernels with
`i > k_0` are massive. Both conventions are admissible because the difference is a remainder (Lemma 4.2, with the mass factor of O-06); the layer must state which one it uses. I recommend the
class's (massless for `i ≤ k_0`), since only that convention makes (O4) an identity for the objects of the representation, and Lemma 4.2 then moves the difference into `r` at no cost.

## Summary of required edits (for the orchestrator)

1. `C1StarF3`: add the `ν^{(d-2)/2}` term to the `rtr`, `rlg` bounds (O-01, F-B).
2. `C1StarF2`: restrict the `em` bound to `ℓ ≥ ℓ₀(ν, x)` (O-02); adapt `LemmaThree.lean`.
3. `C1Star`: move `J` and its three fields inside `data` (O-03, F-A, recommended).
4. `OBSERVABLES.md`: Lemma 1.1 (`ρ₁ := 4ρ₂` or constant `K`; (E3) with `2(d−2)ρ₂`; `α₁ < γ`), Lemma 4.2 (mass factor), Lemma 2.1 (`Hh = 0`), §5.3 ("`E'` is zero"),
   §7.6 Q2–Q3 (answers above), and the status of Prop 3.3 (O-09).
