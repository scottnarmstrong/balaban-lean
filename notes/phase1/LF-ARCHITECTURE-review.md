# Review of `LF-ARCHITECTURE.md` (version 1, 2026-10-11)

Independent refute-first review, 2026-10-11. Reviewer did not write the document. Sources read for
this review: P5 pp. 492–499, 501–503, 511–512 (text layer; p. 499 also as page image); P6 pp. 3–5,
17–22, 27 (text layer); P7 pp. 497–531 (text layer); P9 p. 495; P4 p. 679 (H.6) and pp. 716–717; D3 pp. 29–30
(205)–(207) and D2 p. 31 (text layer); the E10 review (`review/papers/E10-*.md`, §3(F), the proof of
(1.80)–(1.88)); roadmap §§4.3–4.5; `notes/phase1/POLYMER.md` §§1–2. Page numbers are journal pages.

**Verdict: CHANGES-REQUIRED.** The counting proof of LF-2 is correct under its axioms. The P6 Prop
3.2 (ii) finding holds, and on firmer grounds than the document gives. The frozen-threshold repair is
sound. But one axiom of LF-2, the $R$-rule (Rg), does not hold for the ripeness trigger. P7 uses
single-box smallness at every scale of the quiet window, not only at the last $n_2$ scales: (2.59),
(2.60) and (3.17)–(3.19) depend on it, and the document did not check them. For a ripe component
whose window contains many pieces, the loss of $R$ is not $O(\lambda^{2d+2})$, so LF-2 (ii) and LF-4
(d) are unsupported as stated. A repair is available: carry a reserve per merged piece and re-derive
those P7 estimates piece by piece. The document should also stop dismissing the route that keeps
P7's requirement unchanged.

---

## Findings

| ID | Severity | Location | Finding | Evidence | Proposed fix |
|---|---|---|---|---|---|
| LFR-01 | BLOCKER | §3.7 LF-4 (M1)–(M3); §4.1 (Rg); §4.6 (ii); §4.9 "The way out"; §6 item 4 | P7 uses smallness of $Z_j\cap Z$ at **every** scale $j\in[k_1,k]$. It is not used only at $k_2,k_3,k$. The list "P7 §2 uses Prop 3.2 (ii) only through …" in (M1) is incomplete. In a ripe component whose window $[k_1,k-n_2)$ contains many pieces (a dense cluster that merges and then shrinks to one box), the term $\beta_kA^*_{0,k}(Z_{k_1};\phi'_k)$ of (2.59) is of order $A_0^2\lambda_k^{2p_0}$ on real fields. P7's own bound on the analyticity domain is $\beta_k\varepsilon_k^2$, and both exceed $\tau_k$. The perturbation sums (2.60) and (3.17) grow like $\beta_{k_1}^{(d-2)/(2\alpha)-1/2}$. So the axiom "(Rg): $L_R\le C_R\lambda_k^{2d+2}$" fails for ripe components, and LF-2 (ii) and LF-4 (d) rest on a false axiom. | P7 p. 498, standing assumption: "Hence the domains $Z_j$ for $k_1\le j\le k$ are rectangular parallelepipeds with diameters … smaller than the critical sizes". (2.15) p. 501: "$\lvert Z_{j+1}\rvert_\xi<(12LM[R_j])^d$". (2.33) p. 505: "$(15MR_{k_1})^{d-1}$". (2.59) p. 511: "$L^{-n_1d}(12MR_{k_1})^d$ … true even for its analytic extension". (2.60) p. 511: "$\mathrm{diam}_j(\Omega^c_{j+1})<10LMR_j$" for each $j$. (3.9) p. 519 cites "(2.15), (2.59), (2.60)". (3.17) p. 523: "$(10LMR_j)^d$" for each $j$. Computation in §3 below. | Add a piece-count reserve to (H6′): $G_k(Z)\ge\tau_{t^*}+V_k(Z)+\nu(Z)$, where $\nu(Z)$ is the number of components merged into $Z$ since its last gain. $\nu$ is additive at pure merges and is reset to 1 at gains and at kept $R$-events. Case 2 pays the extra $m-1$ out of $(m-1)\tau_{k+1}$. Restate (Rg) as $L_R\le C_R\lambda_k^{2d+2}+\nu(Z)$. List (2.59), (2.60), (3.17)–(3.19) under (M2) and re-derive them piece by piece; each piece contributes $\le\beta_{k_1}^{-c}\,\mathrm{poly}(\lambda)$. |
| LFR-02 | MAJOR | (M2) "(2.15) … already charged in $G$" against (M3) "$P7$'s losses (3.9) are $\le C_R\lambda_k^{2d+2}$" | The two statements use different routes in P7. "Already charged" is true only through the refund in (3.8)–(3.9). $R$ discards $\mathbb T_{k,k_1}$ and re-bounds the operator from $\mathbb T_{k_1}$, so the quiet-window losses (3.9) cancel against the predicted costs in (3.8). This needs the per-site cost coefficient used in $\kappa^{(j)}$ to be at least the coefficient in (3.9). The bound $C_R\lambda^{2d+2}$ is P7's other route, which assumes smallness throughout the window. Mixing the two hides LFR-01. | P7 p. 519 (3.8): "it controls the next $n_1$ renormalization steps"; p. 520: "We can take the constants in the sum (3.8) large enough, so that the sum in (3.9) is cancelled … Even this is unimportant, because the whole expression … can be estimated by const.$(\log\beta_k)^{2d+2}$". | Use the refund route explicitly. Add the constraint $c_1\ge C_{(3.9)}$ to §5 row 12. Define $L_R$ as the residual: $\frac12N\log\beta_k\lvert Z_0\rvert$, $O(1)$, $\lvert E_k\rvert\lvert Z\rvert$, and the volume terms of LFR-01. |
| LFR-03 | MAJOR | Summary lines 32–34; §2.1 item 2; §2.6 reason 1; §4.9 "Why a full restart cannot be paid" and "Fallback" | The claims "no counting argument can close" and "unpayable merge cost" are proved only for invariants whose threshold is indexed by the ripeness time and is polynomial in $\lambda$. The doubling argument shows that a lineage of age $a$ past its latest gain contains $\ge2^{\lfloor a/(n_q+\text{shrink})\rfloor}$ atoms. Pooled reserves then cover the "astronomically many atoms" case, which is the case the document leaves open (§3 below). E10 (1.88) is exactly a restarted quiet window paid by a frozen reserve. Given LFR-01, this route may be cheaper because it keeps P7's analysis as written. | §4.9 (own text: "I have not closed this argument"); E10 review §3(F) item (b): $K\le K_2+n_1+R_{j+1}$, paid by $2(1+\beta_0)^{-1}p_0(g_{j+1})$. | Reword the summary and §2.6. Keep the fallback as a parallel candidate in its pooled-reserve form. Freeze Def-7 and LF-4 only after one of the two routes is written in full. |
| LFR-04 | MINOR | §4.9 counterexample; §2.1 item 1; §6 item 3 | The finding is **confirmed** and is stronger than stated, but the argument has gaps. (a) P7 itself reads (ii) as "single rectangular parallelepipeds", which settles the "UNCERTAIN reading". (b) Under the per-component reading, the clause "$\mathbb A_j\cap Z$ control at least $k-j$ steps" fails one step before the merge: each piece controls 1 step but would need $K(Z')+1\ge2$. (c) Showing $K(Z')<\lambda$ needs an **upper** bound on the merged budget; the text gives only a lower bound, and its notation mixes $\kappa_k$ with $\kappa_{k,n}$. (d) Existence of the configuration is asserted, not shown. | P7 p. 498; P6 p. 21, (ii) as printed; P6 (3.18)–(3.19), p. 20; P5 p. 496 (admissibility does not exclude the configuration). | Add (a)–(d) as in §2 below. Raise the confidence in §6 item 3 to at least 90%. Add the diagnosis: P6's $K$ is defined by budget, E10's $K$ by geometry. |
| LFR-05 | MINOR | §3.4 Lemma B | The new volume charged by P6 is $Z_k^c\cap Z_{k+1}$, which contains $Z_k^\uparrow\setminus Z_k$. Lemma B charges only $Z'\setminus Z_k^\uparrow$, and the old-volume surplus does not cover the difference in general. §4.5 actually uses $c_v\lambda_{k+1}\lvert Z'\rvert_\#$, so the proof of LF-2 is unaffected. | P6 (3.9) p. 18; (3.17) p. 20. | State Lemma B with $-c_v\lambda_{k+1}\lvert Z'\rvert_\#$, or with $\lvert Z'\setminus Z_k\rvert_{k+1}$. |
| LFR-06 | MINOR | §3.5 (U3) | Read literally, the clock $s$ is reset to the current scale whenever the hull rule fires. A point-spine box can be re-hulled at every step, so its ripeness time would recede for ever. §4.3 shows that the reset is meant only for non-point spines. | §4.3 (U3) text. | (U3): reset $s$ only if the spine was not a point. |
| LFR-07 | MINOR | §4.1 (G2); Lemma G | Repeated hulling with merges is not confluent. Hulling $A$ first may swallow $B$, while hulling $B$ first may give a different set. P6 defines the hull of one component only. | P6 p. 22. | Fix a canonical rule (for example, simultaneous hull of all components below critical size, iterated) and prove termination and uniqueness in Lemma G. |
| LFR-08 | MINOR | §4.3, (3.1) | $N_{\rho+3}(x)$ spans up to $2\rho+8$ cubes when $x$ is a general point; it spans $2\rho+7$ only for cube centres. After (U1), $x\in\Gamma/L$ is a general point, so "point spine $\Rightarrow$ diameter $\le\mathrm{crit}$ $\Rightarrow$ box" can fail by one cube. Events can also produce a non-point spine of length $\le1$, which the definitions exclude. | §3.5 definition; §4.3 first paragraph. | Take $\mathrm{crit}_k:=2\rho_k+9$ with $\rho_k$ an integer, or snap spine points to cube centres. Replace spines of length $\le1$ by a point at events. |
| LFR-09 | MINOR | §3.1 $n_2$; (M1); §5 rows 7 and 12 | P7's $k_2$ and $k_3$ are defined by $L^{-(k-k_2)}LM[R_{k_2}]\ge1$, and its constants ($\mathrm{diam}(Z_0)<15$; $c_{11},K_6$ "absolute" in Lemma 2.1) assume critical size $12M[R]$. With $\mathrm{crit}\approx2c_0R$ and $L>2c_0$, the document's $n_2$ can be one step shorter than P7's. If $k_2$ is kept as in P7, $K_6$ depends on $c_0$ (row 12), while $R_0\ge6K_1K_6$ is fixed in row 7: an ordering cycle. | P7 (2.2), (2.5) p. 498; Lemma 2.1 remark p. 507; R_0 condition p. 514. | Redefine $k_2,k_3$ through the document's $n_2$, with $L^{n_2}>L\,\mathrm{crit}\,M$, so that $Z_0$ has diameter $\le3$ and $K_6$ stays absolute. |
| LFR-10 | MINOR | §5 rows 8–14 | The roadmap (§4.4) asks for a check that $B_0$ does not depend on $H_0$, $A_0$ or $p_0$. The document checks only $H_0$. $p_0,p_2,A_0,A_1,A_3,A_3'$ depend only on rows 1, 4, 6 and 7, so they can be moved ahead. | Roadmap §4.4, item 4. | Move rows 13–14 (except $C_R$) before row 8. $C_R$ comes after $B_0$, because (3.9) contains the $\mathcal B^{(j)}$ terms. |
| LFR-11 | NOTE | §5 row 1, UNCERTAIN on $\alpha_1$ versus $L$ | This resolves by monotonicity. Set Root-F's $\delta:=\gamma/2$ and choose $\alpha_1\le\gamma/2$ after $L$ and $M$; a smaller $\alpha_1$ only increases $\gamma-\alpha_1$. Constants that depend on $\alpha_1$ come later in the chain. | Root-F item 3 is monotone in $\delta$. | Record this resolution. |
| LFR-12 | MINOR | LF-8 sketch; §2.2 "What must be added" | The final sum is attributed to D3 Lemmas 14–15. Their mechanism ($N-i\le-\log\lambda_i$) is the one §2.2 shows fails for O(N). In (A′) the losses are already in $G$, and the final sum needs only (H6♭), P7 (4.9)–(4.14) and PE (POLYMER §3.6, "volume weights"). | D3 (205) p. 30; §2.2 of the document. | Drop the D3 Lemma 15 citation, or say that only Lemma 14's geometry is used. |
| LFR-13 | NOTE | §4.1 "$\alpha\in(0,\frac12]$" | Inconsistent with row 1 ($\alpha=\frac{d-2}2-\gamma>\frac12$ for $d\ge4$). The value $\frac12$ is not used anywhere. | §4.1 against §5 row 1. | Write $\alpha\in(0,\frac{d-2}2)$. |
| LFR-14 | NOTE | §3.6 $V_k$, $\sigma_k$; (H6♭) | $\sigma_k$ is an infinite sum over $j>k$, and $t^*$ may exceed $k_f$, but $\lambda_j$ is defined only for $j\le k_f$. | Definitions in §4.2. | Extend by $\lambda_j:=\lambda_{k_f}+(j-k_f)(d-2)\log L$; (F1)–(F5) still hold. |
| LFR-15 | NOTE | §3.2 $R$-record | The final decomposition (3.20) on $Z_0''$ (new regions $S''_k$) is missing from the list, and so is the failure case of the bounds (2.22). | P7 p. 503 (2.22); p. 525 (3.20). | Add both. |
| LFR-16 | NOTE | Various | (a) P6's gain is $A_3(\log\beta_k)^{2p_0}$, not $A_3\lambda_k^{2p_0}$; the difference is a constant factor. (b) LF-3 should start at $k=1$, since $k=0$ is LF-6. (c) P5 Thm 2 applies $R^{(k+1)}$ for $k<k_0$, while P7 Thm 2 (p. 497) applies $R^{(k)}$ for $k<k_0$; the document follows P5, which is consistent with P7's use of $\beta_k\nu_k\le1$. | P6 (3.9) p. 18; P5 p. 499 [page image]; P7 p. 497. | Editorial. |
| LFR-17 | NOTE | §6; §2.5 length | Given LFR-01, the confidence in item 4 (70%) is too high as stated: the document's (M2) is not sufficient. With the ν reserve and the re-derivations, it is reasonable. The 15 pp. for "changes to P7" is an underestimate. | — | Revise. |
| LFR-18 | NOTE (positive) | §4.2–§4.8 | LF-2 (i)–(iv) checked line by line: Lemma V; facts (F1)–(F5); Lemma T; (4.1)–(4.3); Cases 1a, 1b, 2a, 2b; (ii); (iii); the transfer and frozen steps; the §4.7 numbers via P4 (H.6) ($\beta_k=\beta L^{k(d-2)}\gamma_k$, $\nu_k=\nu L^{2k}\delta_k$ with $\gamma_k,\delta_k$ convergent); the §4.8 failure (ratio $(1+\ln2)^8=67.54$) and its repair. The rotation of (M4) was checked numerically. The rejection of (B) was checked against D3 (205)–(207). | §1 below. | — |

---

## 1. Priority 1: the step counter LF-2 (§4)

### 1.1 The axioms of §4.1 against the sources

**(G1) Attribution.** The region calculus is built from complements of rounded neighbourhoods:

- $\Omega'_{k+1}$ = the $\pi'_{k+1}$-cubes at distance $>LMR_k$ from $U_k'^{\sim3}$ (P5 (2.3), p. 502);
- $\Omega_{k+1}$ removes the $\pi'$-cubes meeting $P_{k+1}^{\sim3}$ ((2.8));
- $\Omega''_{k+1}$ removes those meeting $(Q^\sim)^{\approx}\cup(R^{\sim2})^{\approx2}$ ((2.45), p. 512);
- $Z_{k+1}^c$ = the $\pi'$-cubes at distance $>2MR_k+M$ from $(\Omega''^c)^{\sim4}\cup S^\sim$ (P6 (2.3)–(2.5), p. 4).

Each complement is therefore a union of rounded neighbourhoods of the seeds. Rounding and neighbourhoods both distribute over unions. The rounded neighbourhood of a connected seed is connected, since each added cube meets the connected neighbourhood. So (G1) holds with $s_*\approx4$ (P6 (3.14): $S(Z)\subset Z^{\sim4L[R_k]}$), provided $R_0\ge C(L)$ absorbs the additive $O(L^2)$ terms. (G1) is what the sources give. It is not a disguised conclusion.

**(B) Lemma B.** The algebra was rechecked against P6 (3.9)–(3.11), (3.17). The old-volume terms satisfy
$$\lvert Z_k\rvert_k\,(H_k-H_{k+1}L^{-d}-M^{-d})\ge0,$$
by P6 p. 20; this even leaves a surplus of about $\frac12H_0\lambda_k\lvert Z_k\rvert_k$, which the document discards (harmless). The new-volume cost per $\pi_{k+1}$-cube is
$$M^d\Big(c_1\lambda+c_2+\tfrac54(L/M)^d+H_0\lambda_{k+1}\Big)\le c_v\lambda_{k+1}\quad\text{for }\lambda\ge c_2+2 .$$
The gain per new cube is $A_3(\log\beta_k)^{2p_0}$ (LFR-16a). The only inaccuracy is the charged set (LFR-05).

**(G2) Hull rule.** This is P6 p. 22 with a different critical size. The ordering issue is LFR-07; the consequences for P7's constants are LFR-09.

**(Rg) $R$-rule.** "Kept with domain unchanged" is correct: all of $R$'s new regions lie inside $Z$ ($Q''_{k_1}\subset U^c_{k_1}\cap U^{\sim6}_{k_1}$; $S''_k$; $Z_0^c\cap(\Omega_k^c)^{\sim3}$; (2.61); (3.20)). "Non-ripe components unchanged" is P7 p. 516: "In the 'old' components of the first kind nothing has been changed". The gain $g'_k=A_3'\lambda_k^{2p_0-4}$ is the weakest factor, from (2.33) and (2.62).

The loss bound $L_R\le C_R\lambda_k^{2d+2}$ is **not** what P7 delivers under ripeness. This is LFR-01, and §3 gives the details. So (Rg) is the one axiom that carries an unverified analytic conclusion.

**(K) Constants.** $p_2\ge2d+3$ is used in (ii) and (iv); Case 2a needs only $p_2>2d+1$. $2p_0-4>p_2$ is used in (ii). The bound on $c_0$ is used in (U1) and (U2). Consistent.

### 1.2 Lemma V and the cost coefficients (§4.2)

**Lemma V.** Take a maximal $\rho$-separated family $p_1,\dots,p_n$ in $\Gamma$. The open sup-balls of radius $\rho/2$ around the $p_i$ are disjoint. A path in $\Gamma$ from $p_i$ to another $p_j$ must leave its ball, so the part of $\Gamma$ inside the ball has $\mathcal H^1$-measure at least the sup-distance travelled, $\rho/2$. Hence $n\rho/2\le\ell$ when $n\ge2$, and $n\le2\ell/\rho+1$ in general. Each $N_{2\rho+3}(p_i)$ meets at most $(4\rho+8)^d\le(12\rho)^d$ cubes for $\rho\ge1$. This gives
$$\lvert N_{\rho+3}(\Gamma)\rvert_\#\le12^d(2\ell\rho^{d-1}+\rho^d)\le2\cdot12^d\rho^{d-1}(\ell+\rho).\qquad\text{Correct.}$$

**Growth facts.**

- (F2): $\sigma_k=L^{-1}(v_{k+1}+\sigma_{k+1})$ is exact. Also $v_{k+n}\le2^{d-1}n^{2d-1}v_{k+1}$, from $\lambda_{k+n}\le n\lambda_{k+1}$ (when $\lambda_{k+1}\ge\theta_+$) and $r_{k+n}\le2n^2r_{k+1}$.
- (F3) is the mean value theorem.
- (F4): $n_2\le2\log_L\lambda+C$, which is better than stated.
- (F5): $w\asymp\lambda\rho^d\asymp\lambda^{2d+1}$ and $vD\asymp\lambda^{2d+1}$. Also $2\sigma_{k+1}\le2C_\sigma v_{k+2}\le2C_\sigma2^{3d-2}v_{k+1}$, so the $E_k$ of the document dominates both the event term and the spine-reserve term.

### 1.3 Consistency of the bookkeeping (§4.3) and Lemma T

**(U1).** In fact $Z^\uparrow\subset N_{(\rho+3)/L}(\Gamma/L)$, without the $+1$. Then
$$B_{Z^\uparrow}\subset N_{s_*r_k+1+(\rho+3)/L}(\Gamma/L)\subset N_{\rho_{k+1}+2}(\Gamma/L),$$
by $c_0(1-L^{-1})\ge s_*+1$. Correct.

**(U2).** Two touching cubes, each within $\rho+3$ of its own spine, put the two spine points at sup-distance $\le2\rho+8$, hence at Euclidean distance $\le D$. A spanning tree has $m+\nu'-1$ edges, which gives (4.1). Correct.

**(U3).** Correct as meant; it must be restricted to non-point spines (LFR-06).

**Lemma T.** $b'\le k+1$ and $s'\le k+1+\lceil\Lambda'\rceil$. Taking the maximum and bounding it by a sum gives the stated bound, and the absorption of the $\log\lambda$ terms is valid for $\lambda\ge\lambda_*$. Correct.

**Ripeness.** Ripeness cannot be skipped, because after every step $t^*\ge k+1$; the hull only lowers $s$ to the current scale. A ripe component has a point spine, and in a quiet stretch $s$ equals the scale at which the spine became a point. So ripeness does imply "a box for the last $n_2(s)$ scales", subject to LFR-08.

### 1.4 The proofs (i)–(iv)

**Pure shadow.** Directly:
$$G_{k+1}(Z')\ \ge\ \tau_{t^*}+\Big(\tfrac2L\sigma_{k+1}+\tfrac1Lv_{k+1}\Big)\ell+\sum_{j=k+2}^{t^*}w_j\ \ge\ \tau_{t^*(Z')}+V_{k+1}(Z').$$
This uses $t^*(Z')\le t^*(Z)$ and $\ell'\le\ell/L$. The factor 2 regenerates the spine reserve exactly. Correct.

**Event, derivation of (4.2).** Rederived:

- the spine terms on the left are $\frac2L(v+\sigma)\ell_i-\frac1Lv\ell_i=\frac1Lv\ell_i+\frac2L\sigma\ell_i$;
- the $\frac2L\sigma_{k+1}\ell_i$ part cancels against the right side;
- the term $w_{k+1}$ moves to the right;
- the tree terms collect into $(m+\nu'-1)E_{k+1}$.

Correct.

**Cases 1a and 1b.** The left side is $\ge2mA_2\lambda^{p_2}+A_32^{-2p_0}\nu'\lambda^{2p_0}$. In 1a the right side is $O(\lambda^{p_2})+O(\lambda^{2d+2})+(m+\nu'-1)C_E\lambda^{2d+1}$. In 1b, whichever alternative of (4.1) holds, the exponential $L^{\Lambda'}$ beats $\Lambda'^{p_2}$. Correct, also for $m=0$, which is (iii).

**Case 2.** When $t^{*\prime}\le t^*_{i_0}$, the remainder is $(m-1)E\le(m-1)\tau_{k+1}$. Otherwise:

- the bound $\Delta\le\bar\Delta$ holds, using $t^*_{i_0}\ge k+\log_L\ell_{\max}$ and $\Lambda'\le\log_L\ell_{\max}+\log_L(m(1+D))$;
- 2a holds because $\log_Lm\le(m-1)/\ln L$ and $p_2-1\ge2d+1$;
- 2b holds on both branches.

One cosmetic point: when all spines are points, the left side of (4.3) contains $v_{k+1}/L$, which is not available. That branch is never used, since 2a does not use it and 2b then falls into its second branch. Correct.

**(ii).** A ripe component has a point spine. The kept case needs
$$A_3'\lambda^{2p_0-4}\ \ge\ C_R\lambda^{2d+2}+2A_2c_*^{p_2}\lambda^{p_2}+n_q\,w_{\rm top},$$
which is fine for $2p_0-4>\max(p_2,2d+2)$, **given (Rg)**. Correct conditionally.

**(iv).** The numbers were checked against P4 (H.6) on p. 679. Since $\nu_k=\nu L^{2k}\delta_k$ with $\delta_k$ convergent (P4 (5.33), p. 717), the factor $(8/7)^2$ is justified. A one-step bound $\nu_{k+1}>\frac78L^2\nu_k$ would instead give $(8/7)^{k_f-k_0}$. Then
$$k_f-k_0<\lambda_{k_0},\qquad \lambda_{k_f}\le\tfrac d2\lambda_{k_0}+c_d .$$
The transfer inequality needs $p_2>2d+2$. In the frozen regime there are no $\Lambda'$ terms. Correct.

**§4.8.** The failure of the printed chain is confirmed, with ratio $(1+(d-2)\log L)^{p_2}\ge67.54$. The repair, both in P6's terms and for P7 (4.12)–(4.13), is correct.

**Conclusion for priority 1.** The counting is sound. The defects are LFR-05 to LFR-08, LFR-13 and LFR-14, all minor, plus the dependence on (Rg) (LFR-01).

---

## 2. Priority 2: does P6 Prop 3.2 (ii) fail for merged components (§4.9)?

### 2.1 Attempted refutation

**$K$ for the merged component.** The definitions as printed give the following. For a component $Z'$, $\kappa_{k,n}(Z',\mathbb A\cap Z')$ is (3.19) with $Z_k,\mathbb A_k$ replaced by $Z',\mathbb A\cap Z'$ (P6 p. 21). The function $\kappa$ is additive over the old components, by (3.10) and "$\kappa^{(k)}$ is a sum of its values on the components" (p. 18). The factor $C$ is multiplicative, by (3.11). So the merged budget is the sum of the pieces' budgets minus one step's cost, and no definition prevents this.

**Admissibility.** P5 p. 496 requires $K(Z_j\cap Z,\cdot)>0$ for all $j\le k$. The pieces have $K=1$ and the merged component has $K(Z')>0$, so the configuration is admissible.

**Upper bound on the merged budget.** This is the bound the document omits. $K(Z_i)=1$ at scale $k-1$ gives
$$\kappa_{k-1,2}(Z_i)\le2p_2(\beta_{k+1}),\qquad\text{hence}\qquad G_{k-1}(Z_i)\le2p_2(\beta_{k+1})+O(\lambda^{2d+1}).$$
Within one step, $G$ grows only by the old-volume surplus $O(\lambda^{2d+1})$. So
$$G_k(Z')\le4p_2(\beta_{k+1})+O(\lambda^{2d+1}),$$
and therefore $K(Z')\le\frac{\ln2+o(1)}{p_2\theta}\lambda_k+1<\lambda_k-3$, where $\theta=\lambda_{j+1}-\lambda_j\to(d-2)\log L$. Slack in P6's predicted costs only slows the decrease of $K$ by a lower-order amount, so $K(Z')$ still reaches 0 within $(\ln2/p_2\theta+o(1))\lambda$ steps.

**Existence of the configuration.** Take one quiet piece $Z^{(1)}$. Without merges $K$ decreases by at most 1 per step (P6 (3.18)) and must reach 0, so it takes the value 1 at some scale $t_1$. Let $Z^{(2)}$ be its translate by a vector of $ML^{K'}\mathbb Z^d$, with $K'$ large enough that all partitions $\pi_j$, $j\le t_1+1$, are preserved; the two pieces then have identical histories. The merge time is a nondecreasing function of the separation that increases by at most 1 per unit, so the separation can be chosen to make the pieces merge at step $t_1\to t_1+1$, on a large enough torus.

**Readings of (ii).**

- *Connected reading.* P7 itself uses it: p. 498, "Hence the domains $Z_j$ for $k_1\le j\le k$ are rectangular parallelepipeds"; also P6 p. 22. Before the merge, $Z_j\cap Z'$ is two disjoint boxes, each of diameter at least $6M[R]$, so its diameter exceeds the critical size. Hence (ii) fails, as the document says.
- *Per-component reading.* Here the clause "the multi-indices $\mathbb A_j\cap Z$ control at least $k'-j$ steps" fails at $j=t_1$: each piece controls 1 step but would have to control $K(Z')+1\ge2$.
- *Mixed reading* (per-component diameters, union budget): only this one survives, and it is exactly the multi-piece situation that P7 does not treat.

### 2.2 Verdict on priority 2

The counterexample is real, and (ii) is false for the budget-defined $K$. The diagnosis can be stated more sharply than in the document. E10's $K$ is geometric, "the smallest $K$ with $S^K(Z)$ small and quiet", and E10 (1.80) proves budget $\ge$ cost up to that geometric time. P6 redefines $K$ by budget exhaustion and asserts the converse implication, "exhausted $\Rightarrow$ geometrically ripe", which does not follow. Confidence in the finding: at least 90%.

The literal admissibility of (A) is therefore broken, and some change to the trigger or to the counting is necessary.

---

## 3. Priority 3: what $R$ really needs (P7 §§2–3)

### 3.1 What P7 needs, place by place

| P7 place | What it needs about $Z_j\cap Z$ | Under ripeness |
|---|---|---|
| (2.1), (2.23) p. 498, 504 | quietness only: layer inclusions $\Omega_j^c\subset\Omega_{j+1}^c\subset(\Omega_j^c)^{\sim3L[R_j]}$ | yes |
| (2.2)–(2.5) p. 498 | box below critical size at $k_2,k_3$ | yes, given LFR-09 |
| (2.18)–(2.20) p. 501–502 | $Z_0$ and $(\Omega_k^c)^{\sim3}$ are boxes; $\mathrm{diam}(Z_0)<15$ | yes |
| chain (2.21)–(2.30) p. 503–505 | local layer widths; segment $<6MR$ at scale $k$ only | yes (the document is right) |
| (2.15) p. 501 | $\lvert Z_{j+1}\rvert<(12LM[R_j])^d$ for **all** $j$ | only through the refund (LFR-02) |
| (2.33) p. 505 | layer $(15MR_{k_1})^{d-1}$ at $k_1$ | product-form $C$ (document's §3.4) |
| (2.59) p. 511 | $\lvert Z_{k_1}\rvert_\eta\le L^{-n_1d}(12MR_{k_1})^d$, also on the analyticity domain | **no** |
| (2.60) p. 511 | $\mathrm{diam}_j(\Omega^c_{j+1})<10LMR_j$ for **all** $j\in[k_1,k)$ | **no** |
| (3.8)–(3.9) p. 519 | input budget of $\mathbb T_{k_1}$ over $n_1$ steps; cites (2.15), (2.59), (2.60) | budget yes; losses see above |
| (3.17)–(3.19) p. 523–524 | volume $(10LMR_j)^d$ for **all** $j$ in the analytic extension | **no** |
| Lemma 2.1, (3.4) | $\lvert Z_0\rvert\le14^d$ at scale $k$ | yes |
| (3.10) | $\lvert E_k\rvert\lvert Z\rvert\le C\lambda^{2d+1}$ at scale $k$ | yes |

The document checked (2.1)–(2.5), (2.15), (2.18)–(2.33) and (3.4)–(3.10). It missed (2.59), (2.60) and (3.11)–(3.19), although (3.9) names (2.59) and (2.60) as its inputs.

### 3.2 Why the gap is real: the dense cluster

Ripeness allows the following configuration.

1. At a scale $k_1\ge b$, many quiet pieces of critical size are packed with spacing about their own size, inside a region of side about $\mathrm{crit}\cdot L^{s-k_1}$.
2. They merge at $k_1+1$ into one component. Its spine has length about $\nu D$, but its diameter is only about $\mathrm{crit}\cdot L^{s-k_1-1}$.
3. It shrinks by pure shadow steps and is hulled at $s$, which resets the clock by (U3).
4. Choose $s=b+n_q(b)-n_2(s)$. Then it is ripe at $k=b+n_q(b)$, with $k_1\approx b$ and $\nu\asymp L^{d(s-k_1)}$ pieces at $k_1$.

At scale $k$, P7's estimates fail in this configuration as follows.

- **Volume of $Z_{k_1}$.** $\lvert Z_{k_1}\cap Z\rvert_\eta\asymp(\mathrm{crit}\,M)^dL^{-dn_2}\asymp1$, by the definition of $n_2$. P7 has $L^{-n_1d}(12MR)^d$ there.
- **(2.59) on real fields.** Lemma 2.2 (2.41) gives $\lvert\partial\phi'_k\rvert<3K_1K_6\delta_k$, so the factor $\exp\beta_kA^*_{0,k}(Z_{k_1};\phi'_k)$ can be as large as
$$\exp\big(c\,\beta_k\delta_k^2\big)=\exp\big(c\,A_0^2\lambda_k^{2p_0}\big).$$
This exceeds $e^{\tau_k}$, since $2p_0>p_2$.
- **(2.59) on the analyticity domain.** P7's own bound is $\asymp\beta_k\varepsilon_k^2$. Here $\varepsilon_{k+1}=L^{-\alpha}\varepsilon_k$ with $\varepsilon_k$ at most an absolute constant (P9 p. 495; P6 p. 27: "if $3\varepsilon_k\le\delta_2$"). So $\beta_k\varepsilon_k^2=\beta\varepsilon_0^2L^{2\gamma k}(1+o(1))$, which is of order at least $\beta$.
- **(2.60) and (3.17).** The sums acquire the factor $\sum_j\nu_j(10LMR_j)^dL^{-2(k-j)}$ with $\nu_j\asymp L^{d(s-j)}$. Multiplied by $\beta_k^{-1/2}$, this is of order $\beta_{k_1}^{(d-2)/(2\alpha)-1/2}\,\mathrm{poly}(\lambda)\gg1$, because $\alpha<\frac{d-2}2$. So the positivity margin "$<1$" of (2.60) and the bound $e^{O(1)}$ of (3.19) are both lost.

### 3.3 What more is needed, and a sufficient condition

Every one of these quantities is a sum over the pieces present in the window, and each piece contributes very little. The volume of a piece at $k_1$, rescaled to scale $k$, is at most $C\rho^{d-1}L^{(s-k_1)-dn_1}$, so its share of (2.59) is at most
$$\beta_{k_1}\varepsilon_{k_1}^2L^{-(1+2\alpha)n_1}\,C\rho^{d-1}\ \le\ C\rho^{d-1}\varepsilon_0^2\,\beta_{k_1}^{-1-1/\alpha}\ \ll\ 1,$$
using $\beta_j\varepsilon_j^2\le\varepsilon_0^2\beta_j$ and $L^{n_1}>\beta_{k_1}^{1/\alpha}$ from (2.31). Its share of (2.60) and (3.17) is at most $\beta^{-1/2}\,\mathrm{poly}(\lambda)$, by Lemma V applied to the spine of the piece.

A sufficient condition for $R$ is therefore:

1. quiet since $k_1$, with $n_1$ as in (2.31);
2. a single box below the critical size on $[k-n_2,k]$, with $n_2$ dominating P7's $k-k_2$ (LFR-09);
3. a budget reserve of at least $\nu(Z)$, the number of components of $Z_{k_1}\cap Z$;
4. $c_1\ge C_{(3.9)}$, so that the refund absorbs the window losses;
5. product-form $C$-factors for (2.33).

Under conditions 1–5, each of (2.59), (2.60) and (3.17)–(3.19) becomes "$O(1)+\nu\cdot o(1)$". (2.60) and (3.19) are then used as losses rather than as absolute bounds. This works because the $\chi''^c$ terms only need gain minus loss, and the kept or removed budget absorbs the loss through the reserve.

At the level of LF-2, condition 3 is cheap. Add $+\nu(Z)$ to (H6′). Case 2 already frees $(m-1)\tau_{k+1}$ and spends only $(m-1)C\log\lambda\,\lambda^{p_2-1}$ of it. Gains and kept $R$-events reset $\nu$ to 1, which is paid by $g_k$ or $g'_k$.

For boundedly many pieces, which covers the two-piece merge of §4.9, P7's estimates survive with a factor $\nu$, so the motivating case is fine.

### 3.4 Simpler alternatives

- **Require $\nu\le\lambda^C$ at ripeness.** This is not simpler. Components with large $\nu$ would have to wait for a fresh window, which brings back the full-restart cost.
- **Keep P7's requirement** (a single box throughout the window) and pay restarts by pooled frozen reserves (LFR-03). The age bound is a doubling argument. If a merged lineage has age $a$ past its latest gain $b'$, then both merging lineages have age at least the merged one's. So age $a$ requires at least $2^{\lfloor a/(n_q+\text{shrink})\rfloor}$ atoms, which gives
$$\lambda_t\le\lambda_{b'}\,(1+c\log N).$$
$R$'s need, $C\lambda_t^{2d+2}$, is then covered:
  - by the reserve $A\lambda_{b'}^q$ of the latest atom ($2d+2<q<2p_0-4$) when $\log N\le\lambda_{b'}^{c'}$;
  - otherwise by the $N$ pooled reserves, since $N\gg(\lambda_{b'}\log N)^{2d+2}/\lambda_0^q$.

  Each restarted window is paid by the absorbed lineage's pool, which it no longer needs for its own $R$; this is E10 (1.88). This route was not proved here, but nothing in the document refutes it, and it needs none of the re-derivations of §3.3.

---

## 4. Priority 4: Def-7 and LF-1 … LF-8

- **Precision.** Def-7 (D1)–(D9) and the (H6′)/(H6♭) split are precise, apart from LFR-14 ($\lambda_j$ beyond $k_f$) and the ν reserve that LFR-01 requires.
- **Consistency.** The ranges fit: LF-6 gives $k=1$, LF-3 covers $1\le k<k_0$ (LFR-16b), LF-4 covers $1\le k\le k_0$, LF-5 covers $k_0\le k<k_f$, and LF-8 covers $k_f$. LF-3's hypothesis "$\bar\nu\le\beta_k^{-1}\le\frac78L^{-2}$" and the "$\frac32\kappa$" match P5 Thm 1 as printed (checked on the page image of p. 499).
- **Circularity.** None is real. LF-2 (i) uses Lemma B, which is the analytic content of LF-3 and is proved without (D6); LF-3's (D6) then comes from LF-2 (i). LF-2 (ii) uses (Rg), which is the analytic content of LF-4 and is proved from (H6′)$^{\rm pre}$; LF-4 (d) then comes from LF-2 (ii). The link is sound only once (Rg) is corrected (LFR-01).
- **Hidden premises.**
  1. (Rg) (LFR-01).
  2. The refund constraint $c_1\ge C_{(3.9)}$ (LFR-02).
  3. A canonical hull order (LFR-07).
  4. P7's $k_2,k_3$ and Lemma 2.1 constants relative to the new critical size (LFR-09).
- **Sufficiency for Root-F.** Assume LF-DEL (a), (b), PE and its lattice corollary with holes and volume weights (POLYMER §§2.3, 2.6, 3.6), and the small-field interfaces (P4 (H.1)–(H.7) at $\lambda=\infty$). Then (F3)–(F4) give Root-F; the conversion arithmetic of §1.2 was checked. The large-field terms reach Root-F through $\mathcal R''^{(j)}_m$, which satisfies (H.4) and is moved into $\mathcal M^{(j+m)}$ by P5 Prop 3.3, and through $\mathcal P^{(k_f+1)}$. The last step needs only (H6♭) and PE; D3 Lemma 15 is not needed (LFR-12).
- **AGENTS.md hard rule 4.** LF-2 is stated "under the axioms". Its Lean form must be an abstract theorem about an arbitrary process satisfying (G1)–(K). Its instantiation must discharge the axioms through Lemma G, Lemma B and LF-4, and must not carry them as premises of any frozen statement.

## 5. Priority 5: the constant chain (§5)

- **Circularity.** None after two adjustments: the reordering of LFR-10, and the definition of $k_2,k_3$ in LFR-09 (otherwise $R_0$ in row 7 depends on $c_0$ in row 12).
- **Independences.**
  - $\kappa_0$ of $M$: still open. It needs P3 p. 81. If $\kappa_0$ were a decay rate per $M$-cube, it would scale with $M$, and rows 5–6 would form a cycle. If it is a combinatorial constant ($\sum e^{-\kappa_0d}\le1$), it depends on $d$ only.
  - $B_0$ of $H_0$: plausible. The $R$-polymer activities improve as $H_0$ grows, through $e^{-H_k\lvert Z\rvert}$ in (3.10), and the small-field boundary constants come from P1 (3.129). The roadmap also asks about $A_0$ and $p_0$ (LFR-10).
  - $\alpha_1$ of $L$: resolved by monotonicity (LFR-11).
- **$A_2=1$.** This is legitimate. P7's "$A_2$ large" (p. 520) was used only to absorb $C\lambda^{2d+2}$, and $p_2=2d+3$ together with $\beta$ large does that.

## 6. Priority 6: the rejections in §2

- **(B), Dimock.** The rejection is correct. D3 (205) on p. 30 uses "$N-i\le(N-i)\log L-\log\lambda=-\log\lambda_i$", which is checked. For O(N), a quiet region costs $\asymp\lambda_j^{2d+1}$ per step (P6 (3.14)–(3.16)). Over $k_f-i$ steps, which is unbounded as $\nu\downarrow0$, this exceeds the fixed creation gain, and the final smallness required, $\beta_{k_f}^{-2}$, also tends to 0. Some retirement mechanism is necessary. D2 p. 31 says $R$ is unnecessary only for $\phi^4_3$.
- **(A), literal.** The rejection is correct as to the admissibility and counting of P5–P6 (§2 above). The claim that the merge cost is "unpayable" is overstated (LFR-03). The defensible statement is narrower: (A) needs either a modified trigger, (A′), or new counting in the E10 style.

---

## 7. Can (A′) work?

Yes, with changes. The counting core is right: the budget, the spines and clocks, Lemma V, Lemma T and the four cases check out line by line, and the frozen threshold after $k_0$ is sound. The diagnosis that P6 Prop 3.2 (ii) fails for merges is correct, and P7 p. 498 settles its reading. The weak point is the claim that $R$ needs smallness only during the last $n_2=O(\log\log\beta)$ scales. P7's estimates (2.59), (2.60) and (3.17)–(3.19) use single-box volume bounds at every scale of the quiet window. For a ripe component built from a dense cluster of merged pieces, those bounds fail by powers of $\beta$, so the loss bound in (Rg) is false as stated. The repair is cheap at the counting level: add a per-piece reserve $\nu(Z)$ to (H6′) and to (Rg), and use P7's refund route for the window losses. On the analytic side it is real work: per-piece versions of (2.59), (2.60) and (3.17)–(3.19), with (2.60) and (3.19) used as losses. The doubling and pooled-reserve route, which keeps P7 exactly as written, has not been refuted and should be developed in parallel. Def-7 and LF-4 should not be frozen until one of the two routes is written in full.

---

## Re-review of v2

Re-review, 2026-10-11, of `LF-ARCHITECTURE.md` version 2 (about 17,000 words, ending with "Review
dispositions" and the updated list of unproved statements), together with `MERGES-astra.md`. Read
in full: v2 §§1–7 and the dispositions; MERGES-astra.md; and again P7 pp. 498–524 for the chain
places (2.20)–(2.30), Lemma 2.3, (2.61)–(2.62), (3.11)–(3.19). I checked these points hardest:
Proposition M (§4.10); the chain obstruction (§2.7.1, §2.7.3); Lemma C, Lemma CH and the
re-derived estimates of §3.8; Lemma H; the revised LF-2 (§4.3–§4.7); and the constant chain (§5).

**Verdict: APPROVE-WITH-CHANGES.**

- The architecture is now consistent, and the counting closes.
- Proposition M is correct. It refutes the pooled-reserve route, and my doubling sketch in LFR-03
  was wrong.
- The chain obstruction for windows with unboundedly many pieces is real. It is the main thing my
  LFR-01 missed.
- Lemma C, the refund certificate and the re-derived volume estimates check out at the level of
  their displayed inequalities.
- LF-2 under covered windows is correct.
- Two changes are needed before Def-7 and LF-4 are drafted:
  - Lemma CH's enclosure bound must be argued one connected component at a time, using a stated
    lattice separation lemma. As written it uses the span of the whole lineage, which is not bounded.
  - Ripeness should exclude merges of the lineage during the $h$ scales before $k_1$ (R2-01 below).
    The core is then a union of separated boxes, every window point is exposed, and Lemma H is no
    longer needed. The cost is $O(\log\lambda)$ per merge, paid inside Case 2a. If this is not
    adopted, Lemma H stays open, and its documented fallback changes the ripeness rule anyway.

### Findings

| ID | Severity | Location | Finding | Evidence | Proposed fix |
|---|---|---|---|---|---|
| R2-01 | MAJOR | §3.8 Lemma H; §6 item 8; §3.5 ripeness | Lemma H is genuinely open: hollow clusters merged shortly before $k_1$ enclose pockets. Its outcome decides the ripeness rule, so Def-7 depends on it. The case can be removed by bookkeeping. Holes in the core at $k_1$ occur only in lineage clusters merged during $[k_1-h,k_1]$: by Lemma C (c) a cluster has extent at most $\sqrt d\,\nu_{\max}\mathrm{crit}$, so within $h-2$ shadow steps it is $\le\mathrm{crit}$ and is hulled. If ripeness also requires no lineage merge in $[k_1(k)-h,k_1(k)]$, the core is a union of pairwise separated boxes. Then $Z\setminus$core is connected (a box minus separated interior boxes, $d\ge2$), and every window point is exposed. The extra delay is at most $k(\mu+h)-k(\mu)+1=O(h)=O(\log\lambda)$ per merge at scale $\mu$, where $k(x):=x+n_1(x)$. That is the same order as Case 2a's existing shift $\bar\Delta$, and the $(m-1)\tau_{k+1}$ freed by that merge pays it. | v2 §3.8 Lemma H ("the cluster arises only because the window must accept merges"); §6 last paragraph ("I do not have that counting argument"); Lemma C (b)–(c); Case 2a. | Add the merge-free strip to $t^*$, carrying the window's merge scales in the window state. Add $+O(h)$ to $\bar\Delta$ in Case 2a. State the lattice separation lemma of R2-02. Keep plan (H2) as an alternative. |
| R2-02 | MINOR | §3.8 Lemma CH (a) | The enclosure bound says "the enclosing set lies in the lineage at scale $i$, which by (RQ2) spans at most $\sqrt d\,\nu M\mathrm{crit}_i$". (RQ2) bounds the number and size of the cover boxes, not their spread. The lineage at early scales can consist of pieces up to $L^{k-i}$ units apart that merge later, so the claim is false as written. It holds per connected component: a connected cluster covered by $\nu_c$ boxes has extent $\le\sqrt d\,\nu_c M\mathrm{crit}$. It also needs a lattice separation lemma: a block enclosed by a union of pairwise $*$-separated sets is enclosed by one of them (Alexander duality, or Janiszewski in $d=2$, in the $*$/nearest-neighbour adjacency pair). Foreign components (not in the lineage) also need a remark: the path only has to reach $Z$'s own outer shell. | v2 §3.8 Lemma CH (a); Lemma G's $*$-adjacency convention. | Restate (a) component by component; prove the separation lemma in Lemma G (R2-01 needs it too). |
| R2-03 | MINOR | §3.1, §4.3 (U2) | The connector length should be $D_k=\sqrt d\,(2\rho_k+10)$, not $\sqrt d\,(2\rho_k+9)$. A spine point $p$ is within $\rho+4$ of some point $a$ of a cube $Q$; $Q$ shares a point $c$ with $Q'$; $Q'$ has a point $b$ within $\rho+4$ of $p'$. So $\lvert p-p'\rvert_\infty\le(\rho+4)+1+1+(\rho+4)$. Version 1 had $2(\rho+3)+2=2\rho+8$, which is consistent. | v2 §3.1 and §4.3 (U2) text. | Change to $2\rho_k+10$. Only constants change ($C_E$, Lemma C (c), $h$). |
| R2-04 | MINOR | §3.7 (M7); §3.8 Step 2 | The late-scale constants that depend on $\mathrm{diam}_k(Z_0)<15$ include (2.20) ($30(d-1)\cdot3\delta_k$, hence $90d\delta_k$ in (2.28)) and the $7K_6$, $90d$ terms in Lemma 2.5 (p. 515), besides Lemma 2.1. With $D_0=3c_0+4$ these become $C(c_0)\delta_k$. They are absorbed by $L^{-n_1/3}$ and $\beta$ large, so nothing breaks, but (M7) should list them. | P7 (2.20) p. 503; p. 515. | Add them to (M7) and row 4. |
| R2-05 | NOTE | §4.10 Proposition M | **Confirmed.** Checked: $\lambda_{s_i}\ge\kappa_-^i\lambda_b$ with $\kappa_-=1+\frac{d-2}{2\alpha}>2$; per-step loss $\ge c\,c_1\lambda_j(M\mathrm{crit}_j)^d$ (exact $\kappa^{(j)}$, $\log C$ nondecreasing, $H$-terms $\le0$ in steady state); income $\le2^HC_M\lambda_b^{2p_0}$; root window cost $\asymp\kappa_-^{H(2d+2)}\lambda_b^{2d+2}$. Two points to add. (a) The proof keeps only the root's window cost while the merges at all levels give surpluses. It should compare level by level: each level's merge surpluses are at most $2^{H-i}C\lambda_{s_i}^{2d+1}$, which is $1/\lambda$ of that level's window costs. (b) The conclusion holds for any window length $n_1\ge c\lambda$ with $(1+c\theta_-)^{2d+2}>2$. P7's estimates force $n_1\ge c\lambda$ for some $c>0$ (from (2.59) on the analyticity domain, $\beta_{k_1}\varepsilon_{k_1}^2L^{-2(1+\alpha)n_1}<1$ with $\beta_j\varepsilon_j^2=\beta\varepsilon_0^2L^{2\gamma j}$). With $2d+2\ge8$, a shorter window does not rescue (R2) unless $c$ is very small. | v2 §4.10; P7 (2.59) p. 511, p. 522; P9 p. 495. | Add (a) to the proof; add (b) as a remark. |
| R2-06 | NOTE | §2.7.2; dispositions LFR-03 | My LFR-03 sketch, $\lambda_t\le\lambda_{b'}(1+c\log N)$, treated $n_q$ as a constant. Each restart adds $n_q(\text{current})\asymp\lambda_{\text{current}}$ scales, so $\lambda$ grows geometrically per restart. v2's correction to $\lambda_t\ge N^{\log_2\kappa_-}\lambda_{b'}$ on the balanced tree is right. | — | Disposition accepted. |
| R2-07 | NOTE | §2.7.1 shape rows; §2.7.3 | **Confirmed**, and missed by my LFR-01. In a gap-filled layer of a dense cluster, the chain from an interior point to $\Omega_{j+1}$ has length about $L^n\mathrm{crit}$. The constraints allow a drift of about $L^n\mathrm{crit}\,M\,c\,\delta$, which leaves the analyticity domain $\lvert\delta\psi\rvert<c'_6$ of Lemma 2.4 once $L^n\gtrsim\beta^{1/2}\lambda^{-C}$. No new restriction can produce a small factor for it: an $O(1)$ drift over length $\ell$ costs only $\asymp\beta/\ell$ in the action, which is $O(1)$ for $\ell\gtrsim\beta$, and ripeness allows $L^n$ up to $\beta^{1/\alpha}$. So it is not a loss that a reserve can pay. The cap $\nu\le\nu_{\max}$ is the right cure. | P7 p. 504 ($\mathrm{dist}_j(\Omega^c_j,\Omega_{j+1})<3LMR_j$), Lemma 2.3 p. 508, Lemma 2.4 p. 509. | — |
| R2-08 | NOTE | §2.7.3 (R1-ν); MERGES-astra §3 | MERGES-astra's objection (i) is weaker than it reads. A gain on an old large connected region gives $\nu=1$, but Lemma V bounds that piece's volume through its spine. Its share in (2.59) stays at most $C\rho^{d-1}\varepsilon_0^2\beta_{k_1}^{-1-1/\alpha}$, as in my §3.3. The decisive objection to (R1-ν) is the shape one: a large concave piece fills its own gaps (R2-07). The conclusion stands. | Review §3.3; v2 §2.7.3. | None needed. |
| R2-09 | NOTE | §3.8 Steps 1, 4, 6 | **Checked.** Lemma C (b) step: $\mathrm{crit}_j/L+2+2s_*r_j\le\mathrm{crit}_{j+1}$ when $c_0(1-L^{-1})\ge s_*$. Lemma C (c) at (W3). (2.59)′: $\le C'\lambda^{p_2+2d}\varepsilon_0^2\beta_{k_1}^{-1-2/\alpha}$. (2.60)′: $\le CA_0^3\nu_{\max}\hat W^2(LM\mathrm{crit})^d\lambda^{3p_0}\beta_k^{-1/2}$. (3.17)′ and (3.19)′. (2.33)′ with $p_R=2p_0-2w_0>p_2+2d$: from row 8, $p_R\ge5d+4>4d+3$, and $\hat W\le C\lambda^{p_2d/2+3d-2}\le C\lambda^{w_0}$. Step 6: $G_k\le\mathcal K_{k_1}-\sum(c_1\log\beta_j+c_2)\lvert\text{new}\rvert-H_k\lvert Z\rvert_k$ holds exactly, because the quiet-window history is determined by the lineage at $k_1$ and $\log C^{(j)}\ge0$. With $c_1\ge C_{39}$, $c_2\ge C'_{39}$ this gives (Rg) with $L_{\rm res}\le C_R\lambda^{2d+1}$. | P6 (3.9)–(3.11); P7 pp. 501, 505, 511, 519–524. | — |
| R2-10 | NOTE | §4.3–§4.7 (LF-2) | **Checked.** Entry (W1) leaves $t^*$ unchanged ($q=s$). Pure shadow does not increase $t^*$. Case 2a: $\nu$ cancels and $q'+n_q(q')\le t^*_{i_0}$. Case 2b: $\bar\Delta'$ from Lemma T′ and $n_q(a+x)-n_q(a)\le\theta_+x/(\alpha\log L)+1$. Case 2c: $\sum\nu_i-1\ge\nu_{\max}\ge C_r\lambda^{p_2}$ pays $\tau_{t^{*\prime}}+\sum w+1$. Kept $R$: $p_R>p_2+2d$. Transfer at $k_0$. Under (W3) the young part's reserve pays the merged window's continuation, so Proposition M's tree is harmless in (R1-cov). | v2 §4. | — |
| R2-11 | NOTE | §5 | **Checked; no cycle.** $c_0,D_0,K_6$ are fixed in row 4 from $d,L$, with $R_0\ge C(L)$ in row 7. Keeping P7's $k_2$ is correct: my LFR-09 proposal to move $k_2$ would have broken (2.2)'s separation $\mathrm{dist}_k(Z_{k_2},\Omega_{k_2+1})>1$, because $k_2$ is the smallest index at which that separation still holds. $p_0,A_0$ now precede $B_0$, and $c_1,c_2,C_R$ follow it. Still open (as v2 says): $\kappa_0$ independent of $M$, and $B_0$ independent of $H_0$. | P7 (2.1)–(2.4) p. 498. | — |
| R2-12 | NOTE | §3.8 (2.61)′ | "$\lambda_i\ge\lambda_{k_1}-\theta_+h$" is unnecessary, since $i\ge k_1$. | — | Editorial. |
| R2-13 | NOTE | §3.6 Lean types | If R2-01 is adopted, the window state must also carry the window's merge scales (a finite list), not just `Option (ℕ × ℕ)`. Def-7 also needs $\nu_{\max}$, $h$ and the extended $\lambda_j$ as explicit functions. | — | Update the type sketch. |

### Dispositions of LFR-01 … LFR-18

| ID | v2 disposition | Assessment |
|---|---|---|
| LFR-01 | Volume terms handled by the cap (now $O(1)$); (2.15) and (3.9) by the refund; shape terms by Lemma CH and Lemma H; $\nu$ pays overflow restarts; (Rg) becomes $L_R\le C_R\lambda^{2d+1}$ | **Resolved**, apart from Lemma H (R2-01) and Lemma CH (a) (R2-02). The extension beyond my finding (the shape terms) is correct (R2-07). |
| LFR-02 | Refund route explicit; $c_1\ge C_{39}$, $c_2\ge C'_{39}$ | **Resolved** (R2-09). |
| LFR-03 | Pooled reserves refuted by Proposition M; doubling bound corrected | **Resolved.** My sketch was wrong (R2-06); Proposition M is confirmed (R2-05). |
| LFR-04 | Counterexample completed | **Resolved.** The upper bound uses the coefficient $2^{1/p_2}-1$; both readings are treated; existence by translation. The remaining UNCERTAIN (buffers at least two cubes wide) is correctly flagged for Lemma G. |
| LFR-05 | Lemma B charges $c_v\lambda\lvert Z'\rvert_\#$ | Resolved. |
| LFR-06 | (U3) only for non-point spines | Resolved. |
| LFR-07 | Simultaneous, iterated hull; terminates and is deterministic | Resolved. |
| LFR-08 | $\mathrm{crit}=2\rho+10$, radius $\rho+4$, $\rho\in\mathbb N$ | Resolved for crit and Lemma V ($(4\rho+10)^d\le(14\rho)^d$). The connector is off by one (R2-03). |
| LFR-09 | $k_2,k_3$ kept; $D_0=3c_0+4$; $K_6$ fixed in row 4 | Resolved, and better than my proposal (R2-11). Add the (2.20) and Lemma 2.5 constants (R2-04). |
| LFR-10 | Reordered | Resolved. |
| LFR-11 | $\delta=\gamma/2$, $\alpha_1$ in row 10 | Resolved. |
| LFR-12 | LF-8 via (H6♭), P7 (4.9)–(4.14) and PE with volume weights | Resolved. |
| LFR-13 – LFR-16 | Applied | Resolved. |
| LFR-17 | Confidences and length revised | Resolved. |
| LFR-18 | Noted | — |

### Judgement: ready for Lean drafting?

- **LF-2 is ready to draft.** It is a model-independent theorem about an abstract history process
  satisfying (G1), (G2), (B), (Rg), (K). Under AGENTS.md hard rule 4, those axioms may be hypotheses
  of this abstract lemma only; they must not be premises of any frozen statement, and the
  instantiation must discharge them through Lemma G, Lemma C, Lemma B and LF-4. Its proof is
  checked and elementary. The only open choice is whether $t^*$ gets the merge-free strip clause of
  R2-01; settle that first (one short paper revision), then draft.
- **Def-7 and LF-4 should wait for the ripeness rule to be fixed.** Their statements depend on Lemma
  H only through the ripeness rule:
  - If R2-01 is adopted, the statements no longer depend on Lemma H. They can then be drafted for
    the author's approval.
  - If R2-01 is not adopted and Lemma H fails, v2's own fallback changes ripeness, and so changes
    (D6) and LF-2. Drafting before the decision risks rework.
- **LF-4 should stay a draft, not frozen,** until Lemma CH (with R2-02) and the §3.8 re-derivations
  are written at full length in the reconstruction document. They are consistent at the level of
  their displayed inequalities, but they are still proof plans.

In short: draft LF-2 now (with the ripeness clause decided); draft Def-7 and LF-4 after adopting
R2-01 or proving Lemma H; freeze nothing in LF-4 until the reconstruction document is approved.
