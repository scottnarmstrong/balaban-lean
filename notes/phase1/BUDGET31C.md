# BUDGET31C: the marked budgets in the fluctuation step

13 October 2026. Source and landed-code audit. **PROVED** records a checked source statement, a landed declaration, or the displayed elementary arithmetic. **OPEN** records a missing physical or numerical identification. **REFUTED** records an inference contradicted by the sources. No theorem of the actual RG step is claimed from an abstract Lean consumer.

## 1. What the papers claim

**PROVED (source identification).** There is no “Theorem 3.1(c)–(e)” in P4. That numbering is `notes/phase1/FLUCTUATION.md` §3.1, a synthesis of P4–P6. P4
§2, printed pp. 695–696, (2.55)–(2.60) and Propositions 2.1–2.2, concerns the new energy and generating functional; P4 §3 begins with the scaling
identities (3.1)–(3.2). The boundary and inherited-remainder assertions (c)–(e) are P5 §3, printed pp. 514–518, Propositions 3.1–3.3. These pages and the
formulas below were checked against the PDF images, not the P4 OCR.

| Item | P5 statement, on its own scale and rate | Source and interpretation |
|---|---|---|
| (c) | $|\mathcal B''^{(k+1)}(Y)|<\beta_k^{-1}\exp[-\tfrac32\kappa d_{k+1}(Y\bmod\Omega^c_{k+1})]$. No logarithm or separate $L^{-k}$ factor. | P5 printed p. 515, Proposition 3.1, (3.3)–(3.4), for the interpolation (3.2) on p. 514. The sentence after (3.4) permits an arbitrary power of $\beta_k^{-1}$ after changing the large-$\beta$ threshold. |
| (d) | $|\mathcal R'^{(k+1)}_m(Y)|<\tfrac12\beta_k^{-m-1}\exp[-\tfrac32\kappa d_{k+1}(Y\bmod\Omega^c_{k+1})]$. | P5 printed p. 517, Proposition 3.2, applied to (3.9) on p. 516. This is **$\beta_k$**, not $\beta_{k+1}$, in the printed proposition. |
| (e) | New part of $\mathcal R'^{(k+1)}_{n-1}$: $|\mathcal R'_{n-1}(Y)|<C\beta_k^{-n-1}\exp[-\tfrac32\kappa d_{k+1}(Y\bmod\Omega^c_{k+1})]$; terms with $X\cap\Omega_{k+1}=\varnothing$ pass through unchanged. | P5 printed p. 518, Proposition 3.3, referring to (3.11) on p. 517. The $C$ is unspecified. |

**PROVED (source discrepancy).** P6 printed p. 43, proof of P5 Proposition 3.3 after (4.68), starts with an input $\varepsilon=\beta_k^{-n-1/2}$ and
concludes $C_6\beta_k^{-n-1/2}<\tfrac12\beta_k^{-n}$. This does **not** prove P5's printed $C\beta_k^{-n-1}$ with a $k$-independent $C$. P6 then says it
has proved all of Proposition 3.3. The half-power gap in this source claim is **OPEN-SOURCE-E**; it is not an OCR artifact (both PDF images were checked).

**PROVED (notes differ from P5).** `FLUCTUATION.md` §3.1 chooses $\beta_k^{-1}$ for (c), $\tfrac12\beta_{k+1}^{-m-1}$ for (d), and
$\tfrac12\beta_{k+1}^{-n}$ for (e), with rates $\kappa_a,\kappa_b,\kappa_b$. These are the notes' target bounds, not the literal three P5 bounds. Since
$\beta_{k+1}\le2L^{d-2}\beta_k$, an *extra* $\beta_k^{-1}$ in a (d) precursor, or $\beta_k^{-1/2}$ in an (e) precursor, pays the fixed scale conversion for
large $\beta_k$. P6 printed p. 33, Lemma 4.2, gives $\varepsilon=C\beta_k^{-m-2}$ (or $\beta_k^{-m-3/2}$); P6 p. 43 uses $\beta_k^{-n-1/2}$ for (e). There
is no independent $L^{-k}$ gain here beyond $\beta_k=\beta L^{k(d-2)}$.

## 2. Where the smallness comes from

**PROVED (c).** P5 p. 515, paragraph before Proposition 3.1, takes an old boundary term $\mathcal B''^{(k)}(X)$ with $X\cap Z_k\ne\varnothing$ and
$X\cap\Omega_{k+1}\ne\varnothing$. The domain construction forces $d_k(X\bmod\Omega_k^c)\ge LR_k-(2L-1)>R_k$. Sacrificing part of its old exponential decay
gives $e^{-R_k}<\beta_k^{-K}$ for a chosen fixed $K$ and sufficiently large $\beta_k$. P6 printed p. 34, (4.32)–(4.34), makes this quantitative: use a
$\beta_k^{-2}$ source bound, modular localization, and the old-domain sum to get $\beta_k^{-3/2}e^{-(2\kappa-1)d_{k+1}(Y\bmod\Omega^c)}$. This precursor
meets $\beta_k^{-1}$ after the marked cluster and root sums. The mechanism is the **geometric collar**, not parity of the fluctuation Gaussian.

**PROVED (d).** P5 p. 516, (3.5)–(3.9), separates local and translation covariant expressions. The defect $\delta^{(k)}$ of the local covariance/background
is bounded by $e^{-R_k}$ (the paragraph after (3.9), using (2.19), (2.34)). P6 Lemma 4.2 bounds its localized mark by $C\beta_k^{-m-2}$ before the cluster
sums. For fixed $m$ and $C$, $C\beta_k^{-m-2}\le\tfrac12\beta_{k+1}^{-m-1}$ when $\beta_k\ge2C(2L^{d-2})^{m+1}$. The old $\delta D^{(k)}$ trace must be
included separately as in `FLUCTUATION.md` §3.5(d). No Gaussian oddness is used for this size.

**PROVED (e), subject to OPEN-SOURCE-E for P5's stronger wording.** P5 pp. 517–518, (3.10)–(3.11), inserts the already small old $\mathcal R_n^{(k)}$ as
the marked integrand; the $X$ disjoint from $\Omega_{k+1}$ are unchanged. P6 p. 43 uses a precluster $\beta_k^{-n-1/2}$ and obtains $\tfrac12\beta_k^{-n}$
after resummation. For the notes' $\tfrac12\beta_{k+1}^{-n}$ one must retain the half power: $C\beta_k^{-n-1/2}\le\tfrac12\beta_{k+1}^{-n}$ once
$\sqrt{\beta_k}\ge2C(2L^{d-2})^n$. This does not settle the stronger P5 exponent $-n-1$.

**PROVED (different mechanism).** The *new energy* term in (a), not the boundary term (c), contains $-\beta_k V^{(k)}$ after
$\psi'=\beta_k^{-1/2}C^{(k)1/2}\hat\psi$. The zero, first and second ray jets at the critical point give a cubic Taylor remainder:
$\beta_k(\beta_k^{-1/2})^3=\beta_k^{-1/2}$ times a field-radius cube. `Fluctuation/WoneChartIdentity.lean:vkC_ray_vanish_chart` and `vkC_ray_taylor_chart`
are landed under their chart hypotheses. Gaussian parity can kill the *uncoupled expectation* of a homogeneous odd cubic, but the interpolated measure is
tilted and the source papers do not use that cancellation to obtain (c), (d), or (e). A second-order Cauchy argument would require a separate vanishing
first mark jet and a controlled second jet; neither is an input to the present (c) consumer. **REFUTED:** the cubic estimate alone proves the
$\beta_k^{-1}$ budget of (c).

## 3. The exact Lean consumer

**PROVED.** `Fluctuation/Thm31cde.lean:InterpMarks` requires a label-local, measurable, holomorphic family $G_i(u,\Phi)$, a bound
$\|G_i\|\le F_0(i)e^{-\kappa_G d_\ell(y_0i)}$ for all $u,\Phi$, and the almost-everywhere physical sum identity `hF`. Its numerical record fields say
$F_0(i)>0$, $\kappa_G\ge\kappa_H$, and the activity/rate inequalities. `interpAvg_expansion_of_input` yields the coefficient
$C_{\rm PE}\sum_iF_0(i)e^{-\kappa_0d_\ell(y_0i)}$. `interpAvg_expansion_bound` needs this coefficient $\le B$; it is an abstract conditional theorem, not
an estimate for an actual RG mark.

**PROVED.** `thm31c_of_input` sets $B=\beta_k^{-1}$ and $\kappa'=\kappa_a$. This matches P5 Proposition 3.1's power and `FLUCTUATION.md` §3.1(c), although
the notes choose a rate at least as strong as P5's $3\kappa/2$ under their `(IC)` inequalities. `thm31d_of_input` sets $B=\tfrac12(\beta')^{-m-1}$ and
$\kappa'=\kappa_b$; setting $\beta'=\beta_{k+1}$ matches the notes' strengthened output, while P5 prints $\beta_k$. `thm31e_of_input` sets
$B=\tfrac12(\beta')^{-n}$ and $\kappa'=\kappa_b$; at $\beta'=\beta_{k+1}$ it matches the notes' target and P6's half-power precursor, but it does not
establish P5's stronger printed $C\beta_k^{-n-1}$. These declarations also use abstract `dExt`; a physical modular-support identification remains **OPEN**.

**REFUTED.** There is no reason to change `thm31c_of_input` to a $\beta_k^{-1/2}$ budget because the currently cited cubic rooted marks have only that
size. They are marks for the *energy interpolation* and belong to the (a) channel, not to P5 (3.2). Weakening (c) would make its theorem false to the
stated P5 target even though a weaker contribution might still fit H7's fixed $B_0$ (P5 p. 497, (1.39)). The $\beta_k^{-1}$ c budget is source-faithful and
useful for the paper's arbitrary-power boundary statement.

## 4. What the landed mark constants can certify

Put $b=\beta_k=\beta3^k$ in the landed $d=L=3$ level tower, $p_1=A_1(\log b)^p$, $M=3^{m_0+m_1}$, $a=2\kappa_{\rm dec}-1$, $J=c_1(3,3)M^3n_{\rm Fibre}(3,3)e^{a c_{\rm Br}(3,3)}$, and $t_0=1/32$.

**PROVED (cubic rooted family, conditional on its displayed tower hypotheses).**
`Inhabited/MarkedRootAssemblyFromTower.lean:markedRootAssembly_zero_fromTower` returns the exact per-label constant $$F_{\rm cub}=|\beta|\,{3\|E_*\|\over
r^3t_0}J,\qquad E_*={\tt energyBdScaled}(3,3,2,{\tt compWeight}(3,1),k,V,\delta,\rho),\quad r={\tt lvR}(\kappa,t,b,p_1)/4.$$ The tower's
$V={\tt cK2'}({\tt famConst}\,\cdot t)$, $\delta=t$, and $\rho={\tt rho4}$ are fixed once the tower is chosen; $E_*$ includes the block-volume scaling and
is **not** $O(1)$ uniformly in $k$. `Fluctuation/InteractionEnergyScaled.lean:energyBdScaled_eq` gives $E_*=3^kE_{\rm const}(a_k,V,\delta,\rho)$;
`beta_mul_energyBdScaled` gives $\beta E_*=bE_{\rm const}$. `energyBdScaled_le` bounds $E_{\rm const}$ by a fixed number when $a_k\le2$.
`Inhabited/LevelRayTower.lean:lvR` gives $r=\kappa_1\sqrt b/(8p_1)-1$, hence $F_{\rm cub}\le C J p_1^3/\sqrt b$ when $r\ge\kappa_1\sqrt b/(16p_1)$. The
fixed $J$ includes root, fibre, and bridge costs; no root-count power of $b$ is hidden in it.

**PROVED (comparison).** $C_{\rm PE}K_0F_{\rm cub}=O(b^{-1/2}(\log b)^{3p})$ tends to zero, so for sufficiently large $b$ it can meet the **constant**
energy-mark budget used in `FLUCTUATION.md` §3.5(a). It cannot establish $C_{\rm PE}K_0F_{\rm cub}\le b^{-1}$ from this bound: multiplying by $b$ leaves
$C\sqrt b(\log b)^{3p}$. This is a limitation of the available estimate, not a lower bound on the actual coefficient. The source-free activity and physical
`InterpMarks` assembly remain **OPEN**.

**PROVED (decoupled landed count, conditional on its hypotheses).** `Fluctuation/MarkedTwoMarkLocal.lean:marked_count_scaled_dec_resummed` has per-root
constant $F_{\rm dec}=\|E_*\|J/t_0$, with **no** $r^{-3}$. A candidate mark of $-\beta V$ therefore has $|\beta|F_{\rm dec}=bE_{\rm const}J/t_0$. With
fixed $t_0$ its available upper estimate is $O(b)$, not a small estimate. `Fluctuation/MarkedVBlockDec.lean:markedRad` is
$\sqrt N\,\|cc\|C_{\rm sup}c_\psi$; for $cc=b^{-1/2}$ and $c_\psi=p_1$, a permissibly enlarged $t_0$ is at most of order $\sqrt b/p_1$ under the strict
marked-disc condition. Even using that largest radius, this Cauchy upper estimate is of order $\sqrt b\,p_1$, still insufficient to certify $b^{-1}$. The
count localizes a different decoupled block functional; an equality of its coefficients with the cubic coefficients is **OPEN**.

## 5. Verdict, repair, and leaves

**Verdict C (PROVED source and type distinction; physical theorem OPEN).** The proposed either/or confuses channels. P5 (c) is a boundary-mark estimate
paid for by the collar $e^{-R_k}$, so the Lean consumer's $b^{-1}$ budget is faithful. The cubic rooted mark is for (a), where its $b^{-1/2}$ polylog
estimate is sufficient for a fixed output constant; its first two ray jets already vanish, and no Gaussian parity lemma is needed for (c). The decoupled
count's weaker prefactor does not fix the physical mark budget. Preserve `thm31c_of_input`; construct a separate boundary `InterpMarks` whose $F_0$ comes
from the P6 (4.34) modular old-boundary expansion.

**OPEN-BDRY-MARK.** For every old $X$ crossing $Z_k$ and $\Omega_{k+1}$, localize its H7 analytic composite in the *hat* field with the mixed cover, with
coefficient $\le\beta_k^{-2}e^{-\kappa_0d_k(X\bmod\Omega_k^c)-2\kappa d_{k+1}(Y\bmod\Omega_{k+1}^c)}$ as in P6 p. 34. Resum $X$ to obtain a finite root
family $F_0(Y)\le\beta_k^{-3/2}e^{-(2\kappa-1)d(Y)}$ and prove `InterpMarks.hF`, locality on every block configuration, measurability and parameter
holomorphy. Then prove $C_{\rm PE}\sum_YF_0(Y)e^{-\kappa_0d(Y)}\le\beta_k^{-1}$ once $\sqrt b\ge C_{\rm PE}K_0$ with the precise modular entropy constant.
This uses the still **OPEN** Vmod/cover and physical mark family; the abstract consumer alone does not supply them.

**OPEN-D-INPUT.** Localize P6 Lemma 4.2's defect source and the $\delta D$ trace on the common physical carrier; supply an `InterpMarks` whose total budget
is $\le\tfrac12\beta_{k+1}^{-m-1}$ after fixed cluster costs. Do not identify it with the cubic energy family.

**OPEN-E-INPUT.** Localize the inherited $\mathcal R_n^{(k)}$ marks, preserve unchanged disjoint terms and their support condition, and prove the notes'
$\tfrac12\beta_{k+1}^{-n}$ budget. The stronger P5 $C\beta_k^{-n-1}$ remains **OPEN-SOURCE-E** unless an additional half-power gain is shown.

**Text-ready author question (OPEN-SOURCE-E).** “P5 Proposition 3.3 (printed p. 518) states $C\beta_k^{-n-1}$, whereas P6's proof on printed p. 43 begins
with $\varepsilon=\beta_k^{-n-1/2}$ and ends with $C\beta_k^{-n-1/2}<\tfrac12\beta_k^{-n}$. Is the exponent in P5 Proposition 3.3 intended to be $-n$, or
is an additional factor $\beta_k^{-1/2}$ available in the proof?”

| Lean leaf, in dependency order | Exact target | Size / worker |
|---|---|---|
| `boundaryCollarPower` | Turn P5's $d_k(X\bmod\Omega_k^c)>R_k$ and $R_k\asymp(\log b)^2$ into the $\beta_k^{-2}$ old-term source bound, with the split decay rate. | 120–200 lines, Sonnet. |
| `boundaryMarkModular` | Prove the P6 (4.32)–(4.34) hat-localized boundary family under Vmod and mixed-cover hypotheses, retaining old/new component rules. | 250–300 lines per leaf, strong; split geometry from analytic coefficients. |
| `boundaryMarkInterp` | Assemble labels, physical `hF`, global block `dep`, `meas`, `holG`, and activity `hW` into `InterpMarks`; apply `interpAvg_expansion_bound`. | 250–300 lines per leaf, strong; split the record fields. |
| `boundaryBudget` | Establish the explicit $C_{\rm PE}K_0\beta_k^{-3/2}\le\beta_k^{-1}$ threshold and call `thm31c_of_input`; carry the modular support map. | 100–160 lines, Sonnet after the physical family. |
| `defectBudget`, `inheritedBudget` | Separate (d)/(e) mark families, the $\beta_{k+1}$ conversion, and the P5/P6 exponent discrepancy in the frozen statement audit. | 200–300 lines each, strong. |

**Confidence.** High on the checked P5/P6 exponents, the geometric source of (c), and the Lean constants; medium on the final physical bounds because
mixed-cover localization and mark assembly are still open. The P5/P6 exponent mismatch in (e) is explicit and needs resolution before claiming the stronger
printed proposition.
