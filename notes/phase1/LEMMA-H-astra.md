# Lemma H: audit and current status

**Status: open.** I do not have either a complete proof of Lemma H or a counterexample to its stated conclusion. In particular, none of the arguments below licenses the $R$-rule (Rg) for enclosed points. This file records the exact obstruction and a stronger inductive estimate that may remove it. It is **not** a replacement for the open lemma in LF-ARCHITECTURE.md.

## Source and statement

I used the frozen version 2 of `LF-ARCHITECTURE.md` (SHA-256 `35e5b88ac62a2f2e79a51aa8f1231d9ee16054589dbf00f419f4cc126109bf92`), particularly §§2.7, 3.5, 3.7–3.8, 4 and 4.10. The relevant primary sources are Balaban, *A Low Temperature Expansion for Classical N-Vector Models III. A Complete Inductive Description, Fluctuation Integrals*, *Commun. Math. Phys.* **196** (1998), 485–521 (P5); *Renormalization and Localization Expansions. II. Expectation Values of the “Fluctuation” Measures*, *Commun. Math. Phys.* **198** (1998), 1–45 (P6); and *The Large Field Renormalization Operation for Classical N-Vector Models*, *Commun. Math. Phys.* **198** (1998), 493–534 (P7). The P7 PDF used is `s002200050486.pdf`, SHA-256 `c48e08dd439878a0245cceb6e6aead787a8ce7671865f6360c8464a7e579d2e9`.

The assertion to be established is LF-ARCHITECTURE.md §3.8, Lemma H: for points of a covered window enclosed by the old core $Z_{k_1}\cap Z$, the analogues of P7 (2.48), (2.61)–(2.62), and (3.11) hold with the window constant $\hat W$, **or** those variables can be moved into the core while retaining the analytic and budget estimates. P7 proves these statements for a single-box core, not for the multi-box core permitted by window rule (W3). See P7 pp. 508–509, Lemma 2.3; p. 512, (2.61)–(2.62); and pp. 522–524, (3.11)–(3.19).

## Geometry checked first

The tempting six-face-box example in dimension three is **not** a counterexample. Cubes on different coordinate axes touch at an edge or corner. LF-ARCHITECTURE.md §3.7, Lemma G, uses $*$-adjacency, so these are one component. Its diameter is below $\operatorname{crit}=2\rho+10$, and the canonical hull rule in §3.5 fills the central cube. The central cube is therefore in the core, not an enclosed window point. P6 p. 22 uses the same critical-size hulling rule.

Hollow cores are still geometrically allowed. A shell made from a larger $*$-connected collection of critical boxes can have diameter greater than $\operatorname{crit}$; the canonical hull rule does not fill it. A quiet merge or thickening may create the shell while (W3) retains its running window. This observation alone says nothing about the size of the contribution: the earlier small-field restrictions and actions may strongly suppress a field trapped in the hole.

## Plan H1: open the core

There is a sound scale estimate behind this plan. Suppose a scale-$j$ block is first enclosed at an in-window scale $t$ by a lineage covered by $\nu$ boxes of side at most $\operatorname{crit}_t$, as in Lemma C. Connectedness gives a span at most $\sqrt d\,\nu M\operatorname{crit}_t$ in scale-$t$ lattice units. Since the enclosed block has side $L^{j-t}$ in those units,

$$
 L^{j-t}\le \sqrt d\,\nu M\operatorname{crit}_t
 \le \sqrt d\,\nu_{\max}(k)M\operatorname{crit}_k.
$$

Thus, with $h=\lceil\log_L(\sqrt d\,\nu_{\max}(k)M\operatorname{crit}_k)\rceil+2$, the first enclosure of that block occurs no earlier than $j-h+2$. This is the quantitative reason that reopening only recent layers might suffice. It does **not**, by itself, construct a legal P7 chain: an old spatial exit path must be lifted through the exact layers and cross-layer bonds in P7 (2.22)–(2.26), pp. 503–505. One must show that every bond selected when the path crosses the former gap belongs to the action domain of the corresponding one-step operator. Neither Lemma C nor the proof plan of Lemma CH establishes this for an enclosed point.

The decisive analytic loss in the printed H1 plan is at the norm bound for $\mathbb T_{k_1}$. P7 p. 519, before (3.8)–(3.10), bounds the old operator by its inductive scalar norm. The lower bound P6 p. 17, Proposition 3.1 (3.5), on a bond in a layer below $k_1$ has then been discarded. Consequently a violation on such a bond cannot be converted, by the displayed argument of LF-ARCHITECTURE.md §3.8 alone, into the P7 p. 512 factor (2.62). Repeatedly moving the composition start back does not establish a terminating estimate; the newly exposed core can itself have a hole.

### A possible strengthened norm (not yet proved)

Let $E_i(X)$ be twice the sum of nonnegative spatial and cross-layer bond terms inside the braces on the right of P6 (3.5), restricted to the newly absorbed domain $X=Z_i^c\cap Z_{i+1}$. Thus each spatial bond contributes $\beta_i\lvert\partial\psi_i\rvert^2$ to $E_i$. For real configurations P6 (3.5) says

$$
 \beta_{i+1}A^*_{i+1}(X)\ge \frac{\gamma_0}{2}E_i(X).
$$

For $\eta=\gamma_0/8$ it follows pointwise that

$$
 e^{-\beta_{i+1}A^*_{i+1}(X)+\eta E_i(X)}
 \le e^{-3\gamma_0 E_i(X)/8}\le1. \tag{H.1}
$$

This suggests strengthening P5 p. 494, (1.26), to a norm with $\exp(\eta\sum E_i)$ inserted *inside the explicit history integral*, resetting the stored sum when a kept $R$ produces a new single-box window. On a quiet step, (H.1) appears to leave P6 pp. 18–19, (3.9)–(3.11), with its original volume charge. At a step with a new large-field restriction, the stored energy consumes some of the positivity used in P6 (3.7)–(3.8). Its gain coefficient $A_3$ would have to be reduced by a fixed factor and the constants in LF-ARCHITECTURE.md §§3.4, 4 and 5 retuned; the powers used in §4 would remain the same.

If a valid enclosed-point chain produced a violating historical bond at scale $i<k_1$, with $\lvert\partial\psi_i\rvert\ge c\delta_{i,1}$, then the weighted norm would give the **conditional** inequality

$$
 \mathbf1_{\{\lvert\partial\psi_i\rvert\ge c\delta_{i,1}\}}
 \le e^{-\eta c^2\beta_i\delta_{i,1}^2}
      e^{\eta E_i}
 =e^{-\eta c^2A_1^2\lambda_i^{2p_0}}e^{\eta E_i}.
 \tag{H.2}
$$

For $c=(2\hat W)^{-1}$, $\hat W\le C_{\hat W}\lambda_k^{w_0}$, and $\lambda_i\ge(\alpha/2d)\lambda_k$, the exponent extracted in (H.2) is at least

$$
 \frac{\eta A_1^2}{4C_{\hat W}^2}
 \left(\frac{\alpha}{2d}\right)^{2p_0}
 \lambda_k^{2p_0-2w_0}.
 \tag{H.3}
$$

This has exactly the required power $p_R=2p_0-2w_0$. Equations (H.1)–(H.3) are valid algebraically under their stated hypotheses. They are **not** a proof of Lemma H: the following three statements have not been established from P5–P7.

1. A first-enclosure chain reaching the appropriate exterior exists in the actual generating-set geometry, with every violated spatial or cross-layer bond assigned to a stored $E_i(Z_i^c\cap Z_{i+1})$. This includes bonds at the old core boundary and the collar needed for (3.11).
2. The weighted norm composes through all P5 (1.22)–(1.23) factorizations and P7's kept and removed $R$ branches without double-counting a bond or retaining a weight after a reset. P5 p. 494 explicitly warns that the level factorization (1.23) can be destroyed by $R$.
3. The norm is strong enough for the real bad-event estimate and the operator remaining after the bad-event split still admits P7's complex external-field continuation. P7 pp. 520–524 removes characteristic-function dependence by rotating the old variables before proving the bound; P6 (3.5) is only a real positivity estimate. A weight on a bond touching complex external data cannot simply be carried into that continuation.

Thus (H.3) identifies a plausible way to pay for an older bad bond, but the missing statements are mathematical lemmas, not matters of choosing larger constants.

## Plan H2: generalized core

P7 p. 510, (2.51), supplies the minimization principle invoked in H2, and P7 pp. 521–524 uses real nonnegativity of the fluctuation action in (3.16) together with small complex error estimates (3.17)–(3.19). The first fact does not supply the second. If an enclosed variable is left unshifted, the reference field, boundary terms and rotation used on pp. 520–522 change. I found no bound in P5–P7 proving that the resulting characteristic functions are independent of the complex external spin or that the additional cross terms have the asserted order. The stated H2 paragraph in LF-ARCHITECTURE.md itself names this analyticity step as unverified.

There is also a budget obligation. The refund in LF-ARCHITECTURE.md §3.8 Step 6 cancels the P6 quiet-step volume charges against the inductive $\kappa$ charges *for the same newly absorbed region*. Merely bounding an enclosed region step by step while withholding its refund introduces a cost of order $\lambda_j$ per new cube (P6 pp. 18–20, (3.9)–(3.11)). The existing per-component reserve is $\tau=O(\lambda^{p_2})$, while the cap permits $\nu_{\max}=O(\lambda^{p_2})$ critical-size pieces. The displayed estimates in H2 do not show how an unrefunded cost growing with both $\nu_{\max}$ and the critical-box volume is covered. This is a missing accounting estimate, not a counterexample: the actual enclosed volume and duration need separate bounds.

## Required edits to LF-ARCHITECTURE.md

**No edits are justified by a settled result.** Keep “Lemma H open” and the qualifications on LF-4 and (Rg) in §§2.7, 3.6–3.8, 4, 5 and the status table. In particular, do not replace the conditional LF-4 by an unconditional theorem, do not mark (2.48)′, (2.61)′–(2.62)′ or (3.11)′ as proved for enclosed points, and do not treat (H.1)–(H.3) as an established new inductive hypothesis. A future proof via H1 would require exact edits adding the weighted norm, its one-step induction and reset rule, a reduced positive gain constant, the enclosed-point chain lemma, and corresponding constant changes in §§3.4, 3.8, 4 and 5. The present record does not establish those edits.

## Confidence

High confidence in the rejection of the six-box candidate and in the algebraic estimates (H.1)–(H.3). Moderate confidence that the weighted norm is the right way to close H1. **No confidence claim for Lemma H itself:** the missing geometry and analyticity arguments remain open.
