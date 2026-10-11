# The large-field part: architecture (phase 1, document D-LF, first part)

Version 4, 2026-10-11. It revises version 3 (commit 9c37838) after three inputs: the third review, `notes/phase1/LF-ARCHITECTURE-review.md`, section
"Third review (v3)" (verdict CHANGES-REQUIRED, findings R3-01 to R3-14); the counting audit
`notes/phase1/LF-V3-COUNTING-astra.md` (findings C-01 to C-05, cited as COUNTING-astra); and the repair
text `notes/phase1/LF-V4-REPAIRS-astra.md` (cited as REPAIRS-astra). Versions 1–3 answered the first
review (LFR-01 to LFR-18), the merger analysis `notes/phase1/MERGES-astra.md` (cited as MERGES-astra.md)
and the re-review of version 2 (R2-01 to R2-13). Written for the orchestrator, Scott Armstrong and
Roland Bauerschmidt. Status: draft for review. Nothing here is approved.

This document fixes the architecture of the large-field analysis from which the reconstruction
document (roadmap §4.5; outline in §9 below) and the Lean interfaces Def-7 and LF-1, …, LF-8 will be
written. It contains no Lean.

**Sources and conventions.** Keys as in `review/SOURCES.md`; page numbers are journal pages (arXiv
pages for D1–D3). Tags: **[checked]** = re-read in the PDF for this document (text layer or page
image); **[review]** = taken from `review/papers/*.md`, `review/QC_LOG.md`, one of the reviews, or
MERGES-astra.md, and not re-read here. Status words: *proved* (a complete proof exists in a
source), *cited* (a source states it and refers elsewhere), *sketched* (a source argues it in
outline), *reconstructed* (no source proves it; this document or the reconstruction document
supplies it). Doubts are marked UNCERTAIN.

Rulings in force (`review/ROLAND_ANSWERS.md`, batch 2, 2026-10-11): large fields are the crux and
are committed; "anything that works is okay" for the large-field mechanism, including the
bookkeeping of P5–P7 and the operation $R$ itself; the repair of P6 Thm 4 (freeze the threshold at
$p_2(\beta_{k_0})$) is agreed; the step counter must be reconstructed; limits along tori suffice;
hard spins only ($\lambda=\infty$).

**What changed from version 3.**

1. *Counting closure* (C-01, C-02, C-04, C-05, R3-12). The window state has three cases, pre-window,
   *pending* (core scale in the future) and *active* (§3.5). The transitions are deterministic and
   listed exhaustively. Lemma C4 proves closure, a pending horizon of $h_k+1$ scales and activation.
   Lemma C (e)–(f) is restated with the last-box-entry exception. §4.5 is replaced by the budget
   calculation of REPAIRS-astra §B.3. The LF-2 theorem carries (H-λ), and the base step starts from
   $Z_0=\varnothing$. I adopted REPAIRS-astra §B after checking it line by line; §3.5 and §4.5 say
   where I changed it.
2. *Adjacency* (R3-01, R3-02, C-03). Components are the classes of the relation "distance $<\omega_k$
   cubes", with $\omega_k:=2[\hat R_{k-1}]+11$. Then the neighbourhoods $U^{\sim4}$ of distinct
   components are disjoint, and the factorization P5 (1.22) holds (Lemma F). The constants $D_k$ and
   $h_k$ change; nothing else does. With the localization Lemma L, P7 (3.11) holds box by box at the
   core scale, with P7's own path of length $<3MR_{k_1}+8M$ (§3.8). REPAIRS-astra's component-wide
   path lemma is kept, checked, as Lemma P for the general case. Lemma L rests on Lemma F, whose
   source is the support property asserted in P6 p. 16; Lemma F is the remaining open item of (3.11)′
   (confidence 85%).
3. *Tori* (R3-05). LF-2 and the region calculus are stated on the cube tori $\mathbb T_k$ with
   $n_k=Ln_{k+1}$ cubes per side. Windows and hulls exist only for $k\le k_0$, where
   $n_k\ge c\,\beta_{k_0}^{1/2}$ and components in a window cannot wind. Winding pre-window components
   are allowed and need no special treatment (§3.1, §4.1).
4. *Causality* (R3-06). The bookkeeping (ripeness, windows, strips, budget thresholds) runs on the a
   priori sequence $\hat\lambda_j:=\log(\beta a)+1+j(d-2)\log L$ and on the a priori horizon $\hat k_f$
   (option B of R3-06). The running constants enter only the analytic objects at scales $\le k$, and
   the switch at $k_0$ is the causal test $\beta_k\nu_k\le1$ (§3.1).
5. *Def-7 and LF-4 design decisions* (R3-07 to R3-11), §8.2–§8.4:
   - Def-7 is a predicate on representations, and LF-4 is stated existentially.
   - (D5) is P5 (1.26)–(1.27) for the localized operator, required at every scale $j\le k$.
   - Kept operators come in two kinds (K1, K2) and share one exponent $\kappa''$ (§3.3–§3.4).
   - A removal overwrites the generating set on the removed component (§3.2).
   - The objects Def-7 needs are listed with their $\exists!$/definition status.
   - The constant chain has an explicit quantifier prefix (§5.1).
6. R3-03, R3-04, R3-13 and R3-14 are fixed or recorded (§3.7, §3.8, §5).
7. New §9: the outline of the reconstruction document. §6, §7 and §8 are updated, and the
   dispositions R3-xx and C-xx are appended. The duplicate list of unproved statements at the end of
   version 3 is replaced by §6.

**Earlier versions, in one paragraph each.** *Version 3* added the merge-free strip before the core
(R2-01) with a bank of $\frac12\tau_\mu$ per merge after the core, Lemma S (lattice separation),
Lemma CH argued one component at a time, $D_k=\sqrt d(2\rho_k+10)$, the late-scale constants of P7, a
level-by-level Proposition M and the three §8 interfaces. *Version 2* answered the first review:
- P7 uses the single-box shape of the window through volumes and through chains; uncapped windows
  break the chains (§2.7.3).
- Route (R2), P7 unchanged with a restart at every merge, is refuted by Proposition M (§4.10).
- Route (R1) is adopted as covered windows with a cap $\nu\le\nu_{\max}$ (§2.7).
- The counterexample to P6 Prop 3.2 (ii) is completed (§4.9).
- The constants are reordered so that the chain has no cycle (§5).

**Summary of the recommendation.** Keep Balaban's analytic machinery and replace its bookkeeping.
The machinery is the step $S^{(k)}T^{(k)}$ of P5 §2–P6 §3, with large-field regions left
unintegrated, the operation $R^{(k)}$ of P7 §§2–3, and the last step of P7 §4.
- *Histories* become data generated by explicit, deterministic rules. Components are classes of
  the relation "distance $<\omega_k$ cubes", so that their operators factorize.
- *The budget.* The functions $\kappa_k$ and $C$, the counter $K$ and hypothesis H6 are replaced by a
  single budget $G_k(Z)$ with an explicit invariant (H6′). The bookkeeping runs on the a priori
  sequence $\hat\lambda_j$.
- *The trigger for $R$ is geometric.* A component is *ripe* when it is in an *active* window that
  has reached its ripeness time. Then:
  - it has had no new large fields since the window's core scale $q$, which is P7's $k_1$, at least
    $n_q\asymp\lambda$ scales back;
  - it has been covered at every scale of the window by at most $\nu\le\nu_{\max}\asymp\lambda^{p_2}$
    boxes of critical size;
  - it has been one small box for the last $n_2=O(\log\lambda)$ scales;
  - at the core scale its lineage is a union of single boxes, pairwise $\omega$-separated.
- *Merges.* A merge of window-bearing pieces keeps the window running. It may push the core forward
  across the $O(\log\lambda)$-scale strips that follow recent merges. When the new core lies in the
  future the component waits in a *pending* state; it cannot be ripe there.
- *After $k_0$* the threshold is frozen at $p_2(\beta_{k_0})$.

§4 proves the invariant (the reconstructed step counter LF-2) from listed axioms, on tori. $R$ is
generalized to covered windows (§3.8). P7's volume estimates acquire polynomial factors and remain
$O(1)$. The losses (2.15) and (3.9) go through P7's refund route. The chain argument becomes a
chain lemma with a polynomial constant. P7's estimate (3.11) holds box by box at the core scale.

Four facts force this design:
- P6 Prop 3.2 (ii) is false for merged components (§4.9).
- The repair that keeps P7 unchanged fails (§4.10).
- Without a cap on the number of pieces, P7's chain argument fails (§2.7.3).
- Without the separation $\omega_k$, the operators of nearby components do not factorize (R3-01).

---

## 1. What the large-field part must deliver

### 1.1 The target

Root-F (`Balaban/Frozen/Roots/LogPartitionMultiscale.lean`) asserts: there is $\delta>0$ such that
for all $\kappa,c_9>0$ there are integers $L\ge2$, $M\ge1$ and $\beta_0$ with the following
property for all $\beta\ge\beta_0$, $\nu\in(0,1]$ and unit vectors $h\in\mathbb R^N$. There is
$k_f\in\mathbb N$ with $L^{k_f}\sqrt\nu\le L$, $\tfrac12\le L^{k_f+1}\sqrt\nu$, and there are functions
$T_\ell(j,x,X;g)\in\mathbb C^N$, defined for every torus $\mathbb T_\ell=(\mathbb Z/\ell\mathbb Z)^d$ with
$ML^{k_f+1}\mid\ell$, such that

1. $T_\ell(j,x,X;\cdot)=0$ unless $1\le j\le k_f+1$, $x\in X$ and $X$ is a scale-$j$ polymer (a
   nearest-neighbour connected union of blocks of side $ML^j$);
2. $T_\ell(j,x,X;g)$ depends only on $g|_X$, and is analytic on $\{\sum_y\sum_i|g_i(y)|<1\}$;
3. on $\{\sum_y\sum_i|g_i(y)|\le\frac12\}$: $|T_\ell(j,x,X;g)|\le c_9L^{-j(\frac{d-2}2+\delta)}\exp(-\kappa|X|/(ML^j)^d)$;
4. on $\{\sum\sum|g_i(y)|<1\}$:
   $\log\frac{Z(g)}{Z(0)}=\langle g,h\rangle+\sum_{j=1}^{k_f+1}\sum_x\sum_X\langle g(x),T_\ell(j,x,X;g)\rangle$;
5. the terms of two admissible tori agree on images of finite $A\subset\mathbb Z^d$ in the box
   $4|y_\mu|<\min(\ell,\ell')$.

Here $Z(g)=\int\exp(-\beta H(\varphi)+\langle g,\varphi\rangle)\prod_x d\sigma(\varphi_x)$ with
$H=\frac12\|\partial\varphi\|^2+\frac\nu2\|\varphi-h\|^2$ and $\varphi_x\in S^{N-1}$.

### 1.2 How Root-F decomposes

Write $\rho_0(\varphi;g)=\exp(-\beta H(\varphi)+\langle g,\varphi\rangle)$ and let $k_f$ be the first
$k$ with $\nu_k>\frac78L^{-2}$ (P4 §6, P7 p. 529 [checked]); $k_0$ is the last $k$ with
$\nu_k\beta_k\le1$ (P5 p. 490 [checked]). Root-F follows from four ingredients.

* **(F1) The flow (LF-7).** Densities $\rho_k$, $0\le k\le k_f$, with $\rho_{k+1}=R^{(k+1)}S^{(k)}T^{(k)}\rho_k$
  ($R^{(k+1)}=\mathrm{id}$ for $k\ge k_0$), each in the inductive class of §3.6, and
  $\int\rho_k\,d\psi_k=c_k\,Z(g)$ with $c_k>0$ independent of $g$. The normalizations are
  $\int T\rho=\int\rho$ (P1 (1.11)) and $\int R^{(k)}\rho=\int\rho$ (P7 (1.7) [checked]). (Index
  convention: this follows P5 Thm 2, which applies $R^{(k+1)}$ for $k<k_0$; P7 Thm 2, p. 497, writes
  $R^{(k)}$ for $k<k_0$. Both are consistent with P7's use of $\beta_k\nu_k\le1$; LFR-16c.)
* **(F2) The last step (LF-8).** For $\rho_{k_f}$ in the class,
  $\int\rho_{k_f}d\psi_{k_f}=\exp\big[-E|\mathbb T|+\mathcal F_{k_f+1}(h,g)+\mathcal R^{(k_f+1)}(h,g)+\mathcal P^{(k_f+1)}(g)\big]$
  with $\mathcal F_{k_f+1}=\langle g,h\rangle+\sum_{j\le k_f}\langle g,\mathcal M^{(j)}(h,g)\rangle+\sum_{n=0}^m\langle g,\mathcal M_n^{(k_f+1)}(h,g)\rangle$
  (P7 (4.15)–(4.17) [checked]) and $\mathcal P^{(k_f+1)}(g)=\sum_{Y\in\mathcal D_{k_f+1}}\mathcal P(Y;g)$,
  $|\mathcal P(Y;g)|\le\beta_{k_f}^{-2}e^{-2\kappa d_{k_f+1}(Y)}$ (P9 (4.4)–(4.6) [checked]).
* **(F3) Conversion.** $\log Z(g)/Z(0)$ is the difference of the exponents at $g$ and at $0$. Every
  term is a sum of localized analytic functions $f(X;g)$; write $f(X;g)-f(X;0)=\sum_{x\in X}\langle g(x),\int_0^1\partial_{g(x)}f(X;tg)\,dt\rangle$
  (the device of P7 (4.15)). A one-variable Cauchy estimate on the disc of radius $\frac12$ gives
  $|\partial_{g_i(x)}f(X;tg)|\le2\sup|f|$ on $\sum\sum|g_i|\le\frac12$. Tree length converts to block
  count by $d_j(X)\ge|X|_\#/C_d-1$ (surface audit C.4), so the flow is run with decay rate
  $\kappa_{\rm flow}:=C_d(\kappa+1)$ and amplitude $c_9e^{-\kappa_{\rm flow}}$ (P4 Thm 1 allows any small
  $c_9$). The large-field terms $\mathcal P(Y;g)$ fit item 3 because
  $\beta_{k_f}^{-2}\le\beta^{-2}L^{-2k_f(d-2)}(1+o(1))\le c_9L^{-(k_f+1)(\frac{d-2}2+\delta)}$ for
  $\beta\ge\beta_0(c_9)$.
* **(F4) Torus independence.** Every localized term is a function of local data and is defined on
  finite subsets of $\mathbb Z^d$ before being pushed to the torus (roadmap §3.5).

Two regimes are not covered by P5–P7 as written. **$k_f=0$** ($\nu>\frac78L^{-2}$): the last step is
taken on $\rho_0$ directly, which is not of the form H1 (surface record, m4). **$k_0\le0$**
($\nu\beta\ge1$): there is no $R$ at all and the frozen regime starts at $k=0$. Both are folded into
LF-6 and LF-8 below.

### 1.3 The deliverable, stated once

**LF-DEL.** Fix $d\ge3$, $N\ge2$. There is $\delta>0$ (depending on $d$ only; $\delta:=\gamma/2$, §5
row 1) such that for all $\kappa,c_9>0$ there are $L,M=L^m,\beta_0$ and the constants of §5 such that
for $\beta\ge\beta_0$, $\nu\in(0,1]$, unit $h$, the following hold on every torus with $ML^{k_f+1}\mid\ell$.

(a) (F1) holds: the densities exist, lie in the classes $\mathcal R_k$ ($k\le k_0$) and
$\mathcal R^\flat_k$ ($k_0<k\le k_f$) of §3.6, and $\int\rho_k=c_kZ(g)$.

(b) (F2) holds with all localized terms analytic in $g$ on $\|g\|_{\ell^1}<1$, depending only on $g$
on their domains, torus independent for domains that do not wind, and with the bounds of P4
(H.7) for $\mathcal M^{(j)}$, of P7 (4.17) for $\mathcal M_n^{(k_f+1)}$, and of P9 (4.6) for $\mathcal P$.

Root-F follows from LF-DEL by (F3)–(F4). The large-field contributions enter Root-F in two
places only: through the terms $\mathcal R''^{(j)}_m$ that $R^{(j)}$ adds to the effective action
at scales $j\le k_0$ (they reach $\mathcal E^{(j+m)},\mathcal M^{(j+m)}$ after $m$ steps, P5 Prop 3.3
and p. 518 [review]), and through $\mathcal P^{(k_f+1)}$.

### 1.4 Which properties of $\rho_k$ are used where

The class of §3.6 has components (P1)–(P9). The table says which operation consumes which.

| Property of $\rho_k$ | Step $S^{(k)}T^{(k)}$ (P5 §§2–3, P6 §§2–4) | $R^{(k)}$ (P7 §§2–3) | Last step (P7 §4, P9 §4) |
|---|---|---|---|
| (P1) form H1: $\sum_{Z_k,\mathbb A}\mathbb T_k\,e^{\mathcal B^{(k)}}\chi_k(Z_k^c)e^{\mathcal A_k+\mathcal F_k+\mathcal R^{(k)}}$ | yes (P5 (2.1)) | yes (P7 (1.3)) | yes (P7 (4.1)) |
| (P2) small-field data on the whole lattice: P4 (H.1)–(H.7) at $\lambda=\infty$, P5 H2–H4 incl. (1.8) | yes (fluctuation integral, renormalization) | yes (main-action cancellation (2.53)–(2.58); P1 (3.127)) | yes (massive fluctuation integral; restriction $\lvert\psi_k-h\rvert<(5L+3)\delta_k$, P4 (6.2)) |
| (P3) kernel structure H5: non-negative, support in $U_k^\sim$, $O(N)$- and $\pi_k$-invariant, factorization (1.22), domain (1.24)–(1.25) | support and domain only | explicit structure over the quiet window (P7 (2.6)–(2.7)); invariance (coset change of variables, pp. 520–521) | support and factorization (Mayer expansion (4.11)) |
| (P4) operator bound $\int\lvert\mathbb T_kF\rvert\le e^{-\kappa_k}\sup\chi\lvert F\rvert$, $\sum C^{-1}\le1$ | no (only the recursion for the new $\kappa$) | yes (P7 (3.8), refund route) | yes (P7 (4.10)) |
| (P5) budget invariant (replaces H6) | input of LF-2 | ripeness $\Rightarrow$ budget $\ge2p_2(\beta_k)+\nu$ | frozen threshold $\ge p_2(\beta_{k_0})$ |
| (P6) boundary terms H7: locality in $\mathcal D_k(\mathrm{mod}\,\Omega_k^c)$, analyticity on (1.36)–(1.37) and $\lVert g\rVert<1$, bound $B_0e^{-\kappa d_k(X\,\mathrm{mod}\,\Omega_k^c)}$ | yes ($\mathcal B''$ in the fluctuation integral, P5 (3.2), Prop 3.1) | yes (Mayer expansion (3.26)–(3.28)) | yes ((4.11)–(4.13)) |
| (P7) region data: P2 (1.1)–(1.3) separations, inclusions P5 (1.20) | yes | yes (P7 (2.1)) | yes |
| (P8) families over tori with local data | for Root-F item 5 | idem | idem |
| (P9) $\int\rho_k=c_kZ(g)$ | preserved | preserved (P7 (1.7)) | used |

At the last step the additional facts used are $\nu_{k_f}>\frac78L^{-2}$ (massive variational
problem, P2 Prop 4.1; P7 (4.3)–(4.6) [checked]) and no further renormalization. The
large-field operator bound needed there is (P7 (4.10)) $\sum_{\mathbb A}|\mathbb T'F|\le e^{-p_2-H_k|Z|}\sup|F|$;
it is used with $p_2$ replaced by $p_2(\beta_{k_0})$ (the repair), which suffices because
$e^{-p_2(\beta_{k_0})}$ is smaller than any fixed power of $\beta_{k_f}^{-1}$ (§4.8).

---

## 2. Architectures compared

### 2.1 (A) Balaban P5–P7, reconstructed literally

*Objects.* Large-field regions $Z_k$, nested domains $\Omega_j\supset\Omega''_j\supset Z_j^c$ (P5
(1.20)), new large-field cubes $P,Q,R,S$ per step (P5 (2.5)–(2.14), (2.43); P6 (2.1)), multi-indices
$\mathbb A_k$ (P6 (3.1)), operators $\mathbb T_{k+1}=\mathbb T^{(k)}\mathbb T_ke^{\mathcal B^{(k)}}$ (P6
(3.2)–(3.3) [checked]), exponents $\kappa_k$ (P6 (3.9)–(3.10) [checked]), combinatorial factors $C$
(P6 (3.11) [checked]), predicted exponents $\kappa_{k,n}$ (P6 (3.19) [checked]), the counter
$K=\max\{n:\kappa_{k,n}>2p_2(\beta_{k+n})\}$ (P6 pp. 20–21 [checked]), $R^{(k)}$ (P7 (1.6) [checked]).

*Inductive hypothesis.* P5 H1–H7 (pp. 488–497 [checked]); H6: $K(Z,\mathbb A_k\cap Z)>0$ for $k\le k_0$.

*Hardest step.* $R^{(k)}$ (P7 §§2–3): cancellation of main actions, Lemma 2.5, the coset average
of Lemma 3.1, the polymer expansion with non-small boundary terms. Next hardest: P6 Prop 3.2.

*What the sources prove.* P6 Prop 3.2 is cited to E10 pp. 383–387. E10 proves (1.80) for a
*geometric* stopping time (E9 p. 177: the component lies in a cube of size $100MR_k$, and no new
large fields appeared in it during the preceding $N$ steps), and it pays mergers through the tree
induction (1.84)–(1.88), pp. 386–387 [review: MERGES-astra.md §1, read from page images; QC_LOG E10 row].
The logical direction is "given the geometric stopping time, the gain pays until it". P6 needs the
converse, "budget exhaustion implies a geometric quiet window", and no source proves it. P6 Thm
4's last inequality fails as printed (§4.8, re-verified on the page image of P6 p. 22). Two
problems established here:

1. **P6 Prop 3.2 (ii) is false for merged components** (§4.9; confidence 92%). Two quiet components
   with $K=1$ that merge produce a component whose counter, and whose actual lifetime before $R$,
   is at most $\big(\frac{2^{1/p_2}-1}{(d-2)\log L}+o(1)\big)\lambda$ ($\lambda=\log\beta a$), while (ii) asserts a
   window of more than $\lambda$ scales in which the component's domains are rectangular
   parallelepipeds below critical size (the reading P7 p. 498 uses). Before the merge the domain is
   two disjoint pieces.
2. **Restarting the quiet window at every merge cannot be paid in the O(N) flow** (Proposition M,
   §4.10). Over one quiet window $\lambda$ grows by the factor $\kappa_-=1+\frac{d-2}{2\alpha}>2$. A balanced
   binary merge tree of height $H$ whose merges each happen one step before ripeness has income
   $2^HA_3\lambda_b^{2p_0}$ and window costs at its root of order $\kappa_-^{H(2d+2)}\lambda_b^{2d+2}$; for
   $H\gtrsim\log\lambda_b$ the budget, computed with P6's own one-step costs, is negative. This is the
   point at which E10's mechanism does not transfer: there the coupling runs logarithmically, so the
   threshold barely changes over a window (UNCERTAIN as to E10's exact gain schedule, which I have
   not re-read; the O(N) statement does not depend on it).

*Written length.* Sources P5 37 pp., P6 §§2–3 22 pp., P7 42 pp. A literal reconstruction does not
exist: item 1 breaks admissibility and item 2 excludes the minimal fix.

*Verdict.* Not viable literally; viable after the modifications of (A′).

### 2.2 (B) Dimock D2–D3: carry all large-field regions to the end

*Objects.* Nested regions $\Lambda_0\supset\Omega_1\supset\Lambda_1\supset\cdots$ with buffers
$r_k=(-\log\lambda_k)^r$; per step three families $P,Q,R$; the large-field integrals are left
explicit as Gaussian measures and weights $K_{k,\Pi}\mathcal C_{k,\Pi}$ (D2 Thm 3.1, (201)–(220)).
No counter, no admissibility, no $R$: "This difficult step is not necessary for this model" (D2
p. 31 [checked, text layer]). All large-field configurations are summed in one pass after the
last step (D3 §3).

*Inductive hypothesis.* The representation D2 (201) with properties 1–9; no bound on the
large-field part during the flow.

*Hardest step.* The final sum (D3 Lemmas 14–15). Lemma 14: $\mathrm{Vol}(\Lambda_k^c)\le O(1)(Mr_k)^3\sum_{i\le k}|\mathcal C_i|$
(D3 (195)). Lemma 15 bounds the accumulated losses (D3 (205) [checked]):
$$\sum_{j=0}^{N+1}(-\log\lambda_j)|(\Lambda_j^c)^{(j)}|\le O(1)\sum_iM^3|\mathcal C_i|\sum_{j\ge i}(-\log\lambda_j)r_j^3\le O(1)\sum_iM^3(-\log\lambda_i)^{3r+2}|\mathcal C_i|,$$
using "$N-i\le(N-i)\log L-\log\lambda=-\log\lambda_i$": **the number of steps remaining after scale
$i$ is at most the logarithm of the coupling at scale $i$.** The creation factor
$\exp(-c(-\log\lambda_i)^{2p_0})$ then beats the losses since $3r+2<2p_0$ (D3 (206)–(207)).

*Why it fails for O(N).* In $\phi^4_3$ the coupling grows along the flow ($\lambda_j=L^{j-N}\lambda$),
so early scales have the strongest smallness and the fewest remaining steps relative to it. In the
O(N) flow the coupling weakens ($\beta_j\approx\beta L^{j(d-2)}$). The analogue of D3 (205) reads
$$\sum_{j\ge i}^{k_f}\lambda_j\,r_j^d\ \ge\ (k_f-i)\,R_0^d\lambda_i^{2d+1},\qquad\lambda_j=\log\beta_ja,$$
and $k_f-i\approx\frac12\log_L\nu^{-1}-i$ is unbounded as $\nu\downarrow0$ for fixed $i$ and $\beta$, while
the creation factor $\exp(-A_3\lambda_i^{2p_0})$ is fixed. Two facts make this unavoidable: a quiet
large-field region converges to the critical size $\asymp MR_k$ and then costs
$\asymp\lambda_k^{2d+1}$ per step for ever (the buffers are re-added each step, P6 (3.14)–(3.16)
[checked]); and the smallness required at the end is a power of $\beta_{k_f}^{-1}$ (P9 (4.6); (F3)),
which also tends to $0$ as $\nu\downarrow0$. The same estimate fails if the per-site loss is $O(1)$
instead of $O(\lambda)$. (The review checked this against D3 (205)–(207); LFR-18.)

*What must be added.* A mechanism that retires a large-field region once it has been quiet for a
while: Balaban's $R$. With $R$ added, (B) becomes (A′) below, with Dimock as the template for the
representation (D2 (201)), the base case (D2 §3.4), the cluster expansion with holes (D2 Thm F.1)
and, for the final sum, the geometry of D3 Lemma 14 only. The loss bookkeeping of D3 Lemma 15 is
not used: it rests on (205), and in (A′) the accumulated losses are already in the budget (LFR-12).

*Length.* D2 §3 (52 pp.) and D3 (30 pp.) as templates; the O(N) adaptation without $R$ is not
possible, so no estimate.

### 2.3 (C1) E10's collapsed representation (1.104)

E10 pp. 391–392 [review] rewrites each surviving large-field operator as
$(\mathbf T'_k(Y)1)\cdot[(\mathbf T'_k(Y)1)^{-1}\mathbf T'_k(Y)\,\cdot\,]$ and expands the normalized
expectation in a polymer gas in which every polymer either contains a surviving region or is
disjoint from it. Afterwards a large-field region carries only the scalar weight
$\mathbf T'_k(Y)1$, a function of the current field; the integral-operator structure disappears.

*Gain.* Depth-one operators; no multi-indices in the class.
*Cost.* A polymer expansion at every step with non-small boundary terms; $R$ needs the explicit
composition of the quiet-window transformations (P7 (2.6)–(2.9), (2.53)–(2.58), Lemma 2.5), which
the collapse destroys, so $R$ would have to be re-derived for collapsed weights. No source does
this for O(N); Balaban does not use (1.104) in P7.
*Verdict.* Not recommended. It may be useful locally (e.g. to state the last step), not as the
inductive form.

### 2.4 (C2) Regulator-based approaches

Large-field regulators in the style of Bauerschmidt–Brydges–Slade replace characteristic
functions by weights in norms. No source in the library treats the low-temperature O(N) model
this way; adopting it would be new research. Not considered further.

### 2.5 (A′) Balaban's analysis with reconstructed bookkeeping (recommended)

*Objects.* As (A) for everything analytic: regions, one-step operators, $\mathbb T_k$, boundary terms,
$R^{(k)}$. Changed:
- (i) Histories $\mathbb A_k$ are data generated by explicit, deterministic rules (§3.2). Admissibility
  means "generated by the rules"; it is not a restriction on the sum. Components are the classes of
  "distance $<\omega_k$ cubes" (§3.1).
- (ii) $\kappa_k$, $C$ and $H_k|Z|$ are combined into a budget $G_k(Z)$ with a one-line recursion (§3.4).
- (iii) Each component carries bookkeeping data (§3.5): a *spine* (a connected union of segments
  controlling its size), a *gain clock*, a *smallness clock*, and a *window state* (pre-window,
  pending or active, with core scale $q$, piece count $\nu$ and merge record $\mathcal M$). The
  bookkeeping runs on the a priori sequence $\hat\lambda$.
- (iv) $R$ is triggered by *ripeness of an active covered window*, not by $K=0$.
- (v) The counter and H6 are replaced by the budget invariant
  $G_k(Z)\ge\tau_{t^*(Z)}+V_k(Z)+\nu(Z)+U(Z)$ (§3.6, (H6′)), whose proof is LF-2 (§4).
- (vi) After $k_0$ the threshold is frozen at $p_2(\beta_{k_0})$.
- (vii) P7's $R$ is generalized to covered windows (§3.8).

*Inductive hypothesis.* Def-7 (§3.6, §8.2): P5 H1–H5 and H7 unchanged in substance, H6 replaced by
(H6′), stated as a predicate on representations.

*Hardest step.* $R$ on covered windows (LF-4, §3.8): P7 §§2–3 with polynomially many merged pieces,
and a chain lemma in place of P7's layer-width argument. With the merge strips of §3.5 no hole lemma
is needed, and with $\omega$-separated components P7 (3.11) holds box by box. LF-2 is elementary (§4:
about 10 pages of inequalities).

*What the sources prove and what is reconstructed.* The step, the fluctuation integrals and the
renormalization on $Z_{k+1}^c$ are P5–P6 (sketched there, in full in the small-field case in
P3–P4); $R$ on single-box windows is P7 (sketched); the generalization to covered windows, LF-1,
LF-2, LF-6, the $k_f=0$ case and the constant chain are reconstructed. List in §6.

*Length (revised in version 4).* The reconstruction document is about 130 pp (range 110–140). The
outline is in §9: geometry and counting 30 pp; analytic objects, operators and Def-7 35 pp; $R$ on
covered windows 50 pp; the flow and the end 15 pp. Version 3's estimate (70–95 pp) did not count the
closed definitions that R3-09 requires.

### 2.6 Recommendation

(A′), with $R$ generalized to covered windows. Reasons:

1. It is the only option for which a closed counting argument exists (§4). (A) literal rests on a
   false proposition (§4.9); the repair that keeps P7 unchanged is refuted (§4.10); (B) cannot
   control the regime $k<k_0$; (C1) requires re-deriving $R$ without a source.
2. It changes the bookkeeping and generalizes one operation, $R$, in a stated way: every estimate
   of P7 §§2–3 that uses the single-box window is listed in §2.7.1 and re-derived in §3.8 with an
   explicit polynomial factor, so the dependency graph still points at Balaban's pages.
3. The budget invariant is linear in the budget and needs no case distinction on "first/second
   kind", so the Lean interface for LF-2 is a statement about numbers, finite sets of cubes and
   segments, independent of the model (P6 p. 21: "completely model-independent").
4. Admissibility becomes a theorem about all generated histories rather than a restriction on
   the sum, which removes the circularity noted in roadmap §4.3 ("(1.30) is both an admissibility
   condition and a consequence").
5. Roland's ruling 7 permits all of this.

### 2.7 Mergers: the repair routes compared

This section answers the revision request: route (R1) (a per-piece reserve, with P7 re-derived on
windows containing several pieces) and route (R2) (P7 unchanged, restarts paid by pooled frozen
reserves and a doubling bound on lineage age), developed far enough to choose.

#### 2.7.1 What P7's $R$ uses about the quiet window

Notation: $Z$ is the ripe component at scale $k$, $[k_1,k]$ its window, $\Lambda_j=(\Omega_j\setminus\Omega_{j+1})\cap T^{(j)}$
the layer of scale $j$, $U_{k_1}=Z_{k_1}^{\approx}$. "Shape" means a property other than a volume
bound.

| P7 place | What it uses about $Z_j\cap Z$ for $j\in[k_1,k]$ | Kind |
|---|---|---|
| (2.1) p. 498, (2.23) p. 504 | layer inclusions $\Omega^c_j\subset\Omega^c_{j+1}\subset(\Omega^c_j)^{\sim3L[R_j]}$ | quietness only |
| (2.2)–(2.5) p. 498 | one box below critical size at $k_2,k_3$; $\mathrm{diam}_k(Z_0)<15$ | late scales |
| (2.11)–(2.15) pp. 500–501 | first inequality of (2.15): $\lvert C_{k_1,k}\rvert<\mathrm{const}\sum_j\lvert Z_j^c\cap Z_{j+1}\rvert_\xi$ (local); second: $\lvert Z_{j+1}\rvert_\xi<(12LM[R_j])^d$ for every $j$ | volume |
| (2.18)–(2.20), (2.27)–(2.28) pp. 501–504 | $Z_0$ and $(\Omega^c_k)^{\sim3}$ boxes at scale $k$ | late scales |
| (2.22)–(2.26), (2.29)–(2.30) pp. 503–505 | **every point of $\Lambda_j$ lies within $3LMR_j$ of $\Omega_{j+1}$**: "$\mathrm{dist}_j(\Omega^c_j,\Omega_{j+1})<3LMR_j$" and "the points $y,y'_{k_1}$ are connected by a segment of a length $<3LMR_{k_1}$" (p. 504) | **shape** |
| (2.33) p. 505 | ring $(Z^c_{k_1})^{\sim3}\cap Z^{\sim3}_{k_1}$ of size $(15MR_{k_1})^{d-1}$ | volume |
| Lemma 2.3, (2.48) pp. 508–509 | the chain of (2.22)–(2.26) from every $x\in B_{k_1,k}\cap\Omega^c_k$ | **shape** |
| Lemma 2.4, (2.49) p. 509 | (2.48) and P3 Prop 2.1 | shape |
| (2.59) p. 511 | $\lvert Z_{k_1}\rvert_\eta\le L^{-n_1d}(12MR_{k_1})^d$, also on the analyticity domain | volume |
| (2.60) p. 511 | $\mathrm{diam}_j(\Omega^c_{j+1})<10LMR_j$ for every $j$; (2.41), (2.49) | volume and shape |
| (2.61)–(2.62) p. 512 | the chain of (2.22)–(2.26) for $\delta\psi$ with $c=(16LMR_j)^{-1}$ | **shape** |
| (3.8)–(3.10) pp. 519–520 | input budget of $\mathbb T_{k_1}$; refund of (3.9) by (3.8) | refund |
| (3.11) p. 522 | a path of length $<3MR_{k_1}+8M$ inside $U^{\sim3}_{k_1}$ from each $x\in B_{k_1}(W_{k_1})\cap U^{\sim3}_{k_1}$ to its exterior | **shape** |
| (3.12)–(3.19) pp. 522–524 | (3.11), (2.49), and $(10LMR_j)^d$ per layer | volume and shape |

The review (its §3.1) lists the volume rows and the late-scale rows. The rows marked **shape** are
new here. For nested boxes every point of a layer of width $w$ lies within $w$ of the outer
boundary, which is what p. 504 uses. For general shapes this fails in two ways. (a) *Gap filling*:
when many pieces of $\Omega^c_j$ lie closer than $2\cdot3LMR_j$ to each other, $\Omega^c_{j+1}$ fills the
gaps, and a point in the middle is far from $\Omega_{j+1}$. (b) *Enclosure*: a point of a layer can
be enclosed by older parts of the region, so that every path to $\Omega_k$ passes through older
layers or through the core $U_{k_1}$, where $\psi$ is not controlled.

#### 2.7.2 Route (R2): P7 unchanged, restarts paid by pooled reserves

*The rule.* $R$ acts only on a component whose domains $Z_j\cap Z$, $k_1\le j\le k$, are single boxes
below critical size, with $k-k_1\ge n_q(k_1)$. A merge produces two pieces in the past, so the
window restarts after every merge. Following E10 (1.88), the restarts are to be paid by reserves
frozen at the atoms' creation and pooled at merges, with a doubling bound on the age of a lineage:
a lineage that has restarted $i$ times contains at least $2^i$ atoms.

*The counting argument, and where it fails.* Let a lineage restart at scales $s_1<s_2<\dots$, each
restart one step before the previous window would end, so $s_{i+1}\ge s_i+n_q(s_i)$. By §3.1,
$n_q(s)\ge\lambda_s/(\alpha\log L)$ and $\lambda_{s+n}\ge\lambda_s+n\theta_-$ with $\theta_-=\frac12(d-2)\log L$, so
$$\lambda_{s_{i+1}}\ \ge\ \kappa_-\lambda_{s_i},\qquad\kappa_-:=1+\frac{\theta_-}{\alpha\log L}=1+\frac{d-2}{2\alpha}>2\quad(\text{since }\alpha<\tfrac{d-2}2).$$
The doubling bound gives $N\ge2^i$ atoms after $i$ restarts, hence only
$\lambda_t\le\kappa_-^{\log_2N}\lambda_{b'}=N^{\log_2\kappa_-}\lambda_{b'}$. The review's sketch (its §3.4) states
$\lambda_t\le\lambda_{b'}(1+c\log N)$; that bound treats $n_q$ as a constant, which it is not ($n_q\asymp\lambda$). With
the correct bound, $R$'s need at the end, of order $\lambda_t^{2d+2}$ for the last window alone, is
$N^{(2d+2)\log_2\kappa_-}\lambda_{b'}^{2d+2}$, while $N$ pooled reserves of size $\lambda_{b'}^{q}$ (any fixed $q$) give
$N\lambda_{b'}^q$. Since $(2d+2)\log_2\kappa_->2d+2>1$, the pool loses for large $N$. Proposition M (§4.10)
turns this into a statement about P6's budget itself: on the balanced tree the total income of
all atoms is smaller than the window costs, so no allocation of reserves can work. MERGES-astra.md
rates route (b) "open, 45%"; Proposition M settles it negatively for the O(N) flow.

*Verdict.* (R2) is refuted. $R$ must accept windows that contain merges.

#### 2.7.3 Route (R1): $R$ on windows that contain several pieces

Three versions were examined.

*(R1-ν), the review's proposal (LFR-01).* Keep version 1's ripeness (window from the last gain
$b$, smallness only for the last $n_2$ scales), add $\nu(Z)$ = number of components merged since
the last gain to (H6′), reset $\nu$ to $1$ at gains and kept $R$-events, and state (Rg) as
$L_R\le C_R\lambda^{2d+2}+\nu(Z)$. Two defects. (i) MERGES-astra.md §3: a gain on an old, large,
connected region resets $\nu$ to $1$, but the window starting at $b$ still contains all the old
region's sites, so the reserve is not proportional to what (2.59) sees. (The re-review, R2-08,
points out that this objection is weaker than it reads: Lemma V bounds the volume of such a piece
through its spine, so its share of (2.59) stays small.) (ii) The decisive defect is the shape one
below: a large concave piece, or a dense cluster, fills its own gaps.

*(R1-atom), MERGES-astra.md's proposal.* An atom tally $N_k(Z)$ (each gained cube one atom, kept $R$
output one atom, additive at merges, never reset at gains), invariant $G_k\ge\tau_{t^*}+V_k+a_NN_k$,
a per-atom cover of the window (MERGES-astra.md (3.5)), per-atom versions of (2.15), (2.33), (2.59),
(2.60), (3.17)–(3.19), and the window certificate (MERGES-astra.md (3.6)) with P7's refund
route. Adopted from it: the atom attribution of covers (it is the argument of Lemma C, §3.5), the
refund route with $c_1\ge C_{(3.9)}$, the observation that a merge needs no tax proportional to the
tally, the frozen transfer, and the volume table. Not adopted: the absence of a bound on $N$.
MERGES-astra.md (§3, "What has to change in P7") counts (2.18)–(2.30) among the late-scale
estimates that keep their single-box proofs; but the chain (2.23)–(2.26) runs over every
$j\in[k_1,k]$ (p. 504), so these estimates also see the whole window. With
$N$ unbounded a window can contain a dense cluster: $N\asymp L^{dn}$ critical boxes at mutual
distance comparable to their size at scale $k_1+1$, merging at $k_1+2$ into one component whose layer
$\Lambda_{k_1+1}$ fills the gaps. A point in the middle of the cluster is then at distance $\asymp L^n\mathrm{crit}$
(scale-$(k_1+1)$ units) from $\Omega_{k_1+2}$. The small-field constraints on that layer
($|\partial\psi_{k_1+1}|<c\delta_{k_1+1}$) allow $\psi_{k_1+1}$ to drift by $\asymp L^n\,\mathrm{crit}\,\delta_{k_1+1}$ across the
cluster, which exceeds $1$ once $L^n\gg\beta_{k_1}^{1/2}$; ripeness allows $L^n$ up to $L^{n_q}\ge\beta_{k_1}^{1/\alpha}$.
On such configurations $\delta\psi=\tilde\psi-\psi^0_{k_1,k}$ is of order one on part of the layer, Lemma 2.3 is
false there, Lemma 2.4 and the expansions (3.12)–(3.15) are outside their analyticity domain
($|\delta\psi|<c'_6$), and the factor (2.62) for $\chi''^c$ has no chain to produce it. This is not a loss
that a reserve can pay: P7's $R$ cannot remove such a component at all. So a version of (R1) that
does not bound the window's geometry needs a new analytic idea (confidence in this finding 80%;
the risk is an argument that controls the drift through the structure of the cluster's own
history, which I do not see).

*(R1-cov), adopted: covered windows with a cap.* Five rules (precise form in §3.5):

1. A component *enters a window* when it is a single box below critical size (point spine); its
   window start $q$ is that scale and its piece count is $\nu=1$. A gain, a kept $R$-event or a
   restart puts it back to "before the window" until it is again a single small box. Resetting
   $\nu$ at a gain is legitimate here, unlike in (R1-ν), because the new window starts only when the
   whole component is one small box.
2. A merge of components that are all in their windows keeps the window running: $\nu'=\sum_i\nu_i$,
   and the core is at least $\max_iq_i$. This is what (R2) lacks.
3. If $\nu'$ would exceed $\nu_{\max}(k+1):=\lceil C_\nu\hat\lambda_{k+1}^{p_2}\rceil$, or a part is not in its
   window, the window restarts. The restart is paid by the $\nu'\ge\nu_{\max}$ units of reserve (one per
   piece) carried in the invariant, resp. as in version 1's Case 2.
4. Lemma C (§3.5): the history of a component in an active window is covered at every scale of the
   window by $\nu$ boxes of side $\le\mathrm{crit}_j$.
5. (Versions 3–4, R2-01, C-01, C-02.) A merge at scale $\mu$ blocks the core scales $[\mu,\mu+h_\mu]$,
   $h=O(\log\lambda)$; the core is pushed to the first unblocked scale. Then every lineage component at
   the core scale is a single box (a merged cluster collapses to one box within $h$ shadow steps), the
   core is a union of pairwise $\omega$-separated boxes, and no window point is enclosed by it. When the
   pushed core lies in the future, the component is *pending* until the core scale is reached
   (version 4). The delay is paid by the merges themselves (§4.5).

With the cap, everything $R$ sees is polynomial in $\lambda$: the window's volume is at most
$\nu_{\max}(M\mathrm{crit})^d$ per scale, its extent at most $\nu_{\max}(\mathrm{crit}+\omega)$ cubes. The volume
estimates (2.59), (2.60), (3.17)–(3.19) stay $O(1)$ (they carry negative powers of $\beta$), so no
per-piece analytic accounting is needed at all; (2.15) and (3.9) go through the refund. The
chain argument becomes Lemma CH with a constant $\hat W\le C\lambda^{w_0}$, at the price of a larger
$p_0$. Version 2 left open Lemma H (window points enclosed by a hollow cluster in the core); rule 5,
added in version 3 and made closed in version 4 (pending state), removes that case.

#### 2.7.4 Comparison

| | (R2) | (R1-ν) | (R1-atom) | (R1-cov) |
|---|---|---|---|---|
| counting | fails (Prop. M) | closes for the volume terms; the gain reset is unsound for windows from $b$ | closes (MERGES-astra.md (3.1)–(3.4); I agree) | closes (§4) |
| P7 volume terms | unchanged | per piece | per atom | $O(1)$ with a factor $\nu_{\max}$; (2.15), (3.9) by refund |
| P7 shape terms (chains) | unchanged | not addressed | not addressed; false for dense clusters | Lemma CH, constant $\lambda^{w_0}$; merge-free strip (no hole lemma) |
| new constants | — | — | $a_N$ | $C_\nu$, $w_0$; $p_0$ larger |
| status | refuted | insufficient | insufficient as stated | adopted |

#### 2.7.5 Choice

(R1-cov). (R2) is false by Proposition M. Among the (R1) versions it is the only one in which the
window geometry is controlled, and that control is what P7's chain argument needs; the cap costs
one unit of reserve per piece and is paid at overflow. The merge strips cost $O(h)$ scales per merge
and are paid by the merges. The remaining analytic risk is concentrated in Lemma CH (78%) and Lemma
F (85%), both local to LF-4.

---
## 3. The recommended architecture (A′) in full

Definitions are in dependency order. Objects that are unchanged from P5–P7 are cited, not
repeated. Everything is per torus $\mathbb T=(\mathbb Z/\ell\mathbb Z)^d$ with $ML^{k_f+1}\mid\ell$. Local analytic
objects are defined on finite subsets of $\mathbb Z^d$ and pushed to the torus (roadmap §3.5). The
region calculus and the bookkeeping are defined directly on the cube tori (R3-05).

### 3.1 Tori, lattices, scales, cubes, components, constants

* **Tori** (R3-05). The fine torus is $\mathbb T=(\mathbb Z/\ell\mathbb Z)^d$ with $ML^{k_f+1}\mid\ell$. The
  scale-$k$ lattice is $T^{(k)}:=L^k\mathbb Z^d/\ell\mathbb Z^d$, written in scale-$k$ units as
  $(\mathbb Z/\ell L^{-k}\mathbb Z)^d$ (P5 p. 488, $T_1^{(k)}$). The block of $y\in T^{(k)}$ is
  $B_k(y)=y+\{0,\dots,L^k-1\}^d\subset\mathbb T$.
* **Cubes.** $\pi_k$ is the partition of $\mathbb T$ into cubes of side $ML^k$ aligned with $ML^k\mathbb Z^d$
  (these are the blocks of Def-2 `IsPolymer` with $s=ML^k$). Its cubes are indexed by the *cube torus*
  $\mathbb T_k:=(\mathbb Z/n_k\mathbb Z)^d$, $n_k:=\ell/(ML^k)$, for $0\le k\le k_f+1$. Then $n_k=Ln_{k+1}$, and
  coarsening is $x\mapsto\lfloor x/L\rfloor$ coordinatewise (Lean `blockMap`, `jBlock`).
  - A *domain at scale $k$* is a union of $\pi_k$-cubes; $|X|_\#$ is its number of cubes, and
    $|X|_k=M^d|X|_\#$ its volume in scale-$k$ unit cubes.
  - $\mathcal D_k$ is the set of nearest-neighbour connected domains, and $d_k(X)$ the tree length in
    units of $M$ (P1 (2.27)). $\mathcal D_k(\mathrm{mod}\,\Omega^c)$ and $d_k(X\,\mathrm{mod}\,\Omega^c)$ are
    as in P5 (1.33)–(1.34).
  - For $k\le k_0$ the cube tori are large. From $\nu_{k_f}>\frac78L^{-2}$, $\nu_{k_0}\beta_{k_0}\le1$ and
    $\nu_k=\nu L^{2k}\delta_k$ with $|\log\delta_k|\le\epsilon$ (below), $L^{2(k_f+1-k_0)}\ge\frac78e^{-2\epsilon}\beta_{k_0}$. Hence
    $$n_k\ \ge\ n_{k_0}\ \ge\ L^{k_f+1-k_0}\ \ge\ \tfrac12\beta_{k_0}^{1/2}\qquad(k\le k_0).\tag{3.0}$$
* **Distances and neighbourhoods.** For sets $X,Y$ of $\pi_k$-cubes, $d(X,Y):=\min|x-y|_\infty$ over
  their indices in $\mathbb T_k$ (torus distance). Two cubes are $*$-adjacent if $d\le1$, and
  nearest-neighbour adjacent if they share a face. $X^{\sim n}$ is the set of cubes with
  $d(\cdot,X)\le n$, so that P5 (1.2) reads $X^\approx=X^{\sim([R_{k-1}]+1)}$. For a subset $X$ of the
  continuous torus $(\mathbb R/n_k\mathbb Z)^d$ and real $r\ge0$, $N_r(X)$ is the union of the cubes at
  sup-distance $\le r$ from $X$. Coarsening of domains is $X^\uparrow$ (the $\pi_{k+1}$-cubes meeting
  $X$); for points it is $x\mapsto x/L$.
* **Small sets, diameter, hull.** A set $X$ of cubes is *small* if it lies in a sup-ball of radius
  $n_k/4$. A small set has lifts to $\mathbb Z^d$ inside a ball of radius $n_k/4$, unique up to
  translation by $n_k\mathbb Z^d$. Its diameter and its hull (the smallest box of cubes containing it)
  are those of such a lift, projected (P6 p. 22 [checked]: components below critical size are
  replaced by the smallest rectangular parallelepiped). Hulls are used only at scales $k\le k_0$,
  where every set of diameter $\le\mathrm{crit}_k$ is small by (3.0) (§3.5).
* **Components** (R3-01). Put $\omega_k:=2[\hat R_{k-1}]+11$ for $k\ge1$. The *components* of a domain at
  scale $k$ are the classes of the equivalence relation generated by "$d(\square,\square')<\omega_k$".
  Distinct components $Y,Y'$ satisfy $d(Y,Y')\ge\omega_k$. Since $Y^\approx=Y^{\sim([R_{k-1}]+1)}$ and
  $R_{k-1}\le\hat R_{k-1}$, this gives $d\big((Y^\approx)^{\sim4},(Y'^\approx)^{\sim4}\big)\ge\omega_k-2([R_{k-1}]+5)\ge1$. In particular
  $U^\sim\cap U'^\sim=\varnothing$ for $U=Y^\approx$, $U'=Y'^\approx$, which is the hypothesis of the
  factorization P5 (1.22) (p. 493 [checked]; Lemma F, §3.7).
  - A component need not be connected. Components are $*$-separated, so Lemma S applies to them.
  - Paths, enclosure, chains and $\mathcal D_k$ use nearest-neighbour adjacency.
  - Merges, the hull rule, (U2), Lemma C and the abstract LF-2 all use this component relation.
* **Running constants** (actual). $\beta_k,a_k,\nu_k$ come from the RG equations (P4 Thm 2 with P5 (1.40):
  $c_j=0$, $d_j=b_j$), and $\lambda_k:=\log(\beta_ka)$. By P4 (H.6) and the landed Lean
  (`betaSeq_eq`, `nuSeq_eq`, `norm_gammaSeq_le` in `Flow/RunningCoefficients.lean`),
  $\beta_k=\beta L^{k(d-2)}\gamma_k$ and $\nu_k=\nu L^{2k}\delta_k$ with
  $|\log\gamma_k|,|\log\delta_k|\le\epsilon:=c_8q/(1-q)$; $c_8$ is taken so small that $\epsilon\le\frac1{20}$.
  - $k_0$ is the last $k$ with $\beta_k\nu_k\le1$ (P5 p. 490 [checked]: $\beta_k\nu_k$ is increasing). So
    "$k\le k_0$" is the test $\beta_k\nu_k\le1$, which uses the sequence only up to $k$.
  - $k_f$ is the first $k$ with $\nu_k>\frac78L^{-2}$ (P4 §6; P7 p. 529 [checked]), again a test at
    scale $k$.
  - The region rules of P5–P6 (P5 (1.2), (2.2)–(2.9), (2.45); P6 (2.3)) keep their actual radii
    $R_j=R_0\lambda_j^2$.
* **A priori sequence** (R3-06, option B). Put
  $$\hat\lambda_j:=\log(\beta a)+1+j(d-2)\log L\quad(j\ge0),\qquad\hat R_j:=R_0\hat\lambda_j^2,\qquad\hat k_f:=\min\{k\ge0:\nu L^{2k+2}\ge1\}.$$
  - The increments $\hat\lambda_{j+1}-\hat\lambda_j=\theta:=(d-2)\log L$ are exact. Since
    $\lambda_j=\hat\lambda_j-1+\log\gamma_j$, we have $\lambda_j\le\hat\lambda_j\le\lambda_j+2$ and $R_j\le\hat R_j$.
  - $k_f\le\hat k_f\le k_f+1$. At $\hat k_f$, $\nu_{\hat k_f}\ge e^{-\epsilon}L^{-2}>\frac78L^{-2}$. At $k_f$,
    $\nu L^{2k_f+2}e^{\epsilon}>\frac78$, so $\nu L^{2(k_f+1)+2}\ge1$.
  - **Every bookkeeping quantity below is a function of $\hat\lambda$ (and of $\beta,\nu$ through
    $\hat\lambda_0$, $\hat k_f$) only.** The running constants enter only the analytic objects, at
    scales $\le k$.
  - Version 3's extension of $\lambda_j$ beyond $k_f$ (LFR-14) is no longer needed.
* **Bookkeeping constants.** $r_k:=\lceil\hat R_k\rceil$, $\rho_k:=c_0r_k$ with $c_0\in\mathbb N$, and
  $$\mathrm{crit}_k:=2\rho_k+10,\qquad\omega_k:=2[\hat R_{k-1}]+11,\qquad D_k:=\sqrt d\,(2\rho_k+10+\omega_k)\quad(\pi_k\text{-cubes}).$$
  - Spine radius $\rho_k+4$ (LFR-08). A point-spine component lies in $N_{\rho_k+4}$ of the point, so
    it has diameter $\le\mathrm{crit}_k$. A box of side $\le\mathrm{crit}_k$ lies in $N_{\rho_k+4}$ of its centre.
  - Connector length $D_k$ (R2-03, R3-01). Let two seed sets be at index distance $<\omega$, with cubes
    $Q,Q'$ realizing it, each within $\rho+4$ of its own spine point. The points are then at
    sup-distance $\le(\rho+4)+\omega+(\rho+4)\le2\rho+10+\omega$.
* **Window lengths.** $n_q(j):=\min\{n\ge1:n\log L>\alpha^{-1}\hat\lambda_j\}$ with
  $\alpha=\frac{d-2}2-\gamma\in(0,\frac{d-2}2)$ (LFR-13), and $n_2(j):=\min\{n:L^n>LM\,\mathrm{crit}_j\}$ (LFR-09).
  - $n_q(j)$ satisfies the lower inequality of P7 (2.31) [checked] for the core $j$, since
    $\hat\lambda_j\ge\lambda_j$.
  - Its upper inequality holds up to an additive $2/\alpha$:
    $n_q(j)\log L\le\alpha^{-1}\lambda_j+2\alpha^{-1}+\log L$. P7 uses that inequality only in (2.32) and
    in $\lambda_k\le c_*\lambda_{k_1}$, and both survive (R3-14 (d)).
  - $n_q(j)\le\hat\lambda_j/(\alpha\log L)+1$ and $n_2(j)\le2\log_L\hat\lambda_j+C_2$.
* **Piece cap and exponents.** $\nu_{\max}(j):=\lceil C_\nu\hat\lambda_j^{p_2}\rceil$; $w_0:=\frac{p_2d}2+3d$ (the
  exponent of the chain constant $\hat W$, §3.8); $p_R:=2p_0-2w_0$ (the exponent of the gain of a kept
  component).
* **Window core and strips.** $k_1(t):=\max\{c\ge0:\ c+n_q(c)\le t\}$, with the convention $k_1(t):=0$
  when the set is empty (Lean `Nat.findGreatest`).
  - $k_1$ is evaluated only at times $t\ge t_0\ge n_q(0)$, where the set is non-empty (R3-12).
  - Since $c\mapsto c+n_q(c)$ is strictly increasing, $k_1$ is nondecreasing and
    $k_1(t+1)\le k_1(t)+1$. Moreover $k_1(t)=c$ exactly for $c+n_q(c)\le t<(c+1)+n_q(c+1)$.
  - The strip length is $h_j:=\lceil\log_L(2\sqrt d\,\nu_{\max}(j)M(\mathrm{crit}_j+\omega_j))\rceil+2=O(\log\hat\lambda_j)$,
    nondecreasing in $j$.
  - For a finite set $E$ of merge scales, $B(E):=\bigcup_{\xi\in E}[\xi,\xi+h_\xi]$ is the set of
    *blocked* scales.
* **Fields.** $\psi_k:T^{(k)}\to\mathbb R^N$ ($\mathbb C^N$ in analyticity statements). The multiscale
  field $\psi$ lives on a generating set $\mathbb B_k\subset\bigsqcup_{j\le k}T^{(j)}$, with $\psi=\psi_j$ on
  $\Lambda_j=(\Omega_j\setminus\Omega_{j+1})\cap T^{(j)}$ (P5 p. 492 [checked]). The unintegrated
  fluctuation variables $\psi'_j$ live on $(\Omega_j\setminus\Omega''_j)\cap T^{(j)}$. The generating set is
  a Lean `GeneratingSet d L N₀ k ϱ` with $\varrho\ge R_0$ (BACKGROUND.md, I-1).

### 3.2 Histories (replacing the multi-indices $\mathbb A_k$)

* **Step record** $\varsigma_{k+1}$ (step $k\to k+1$, given $Z_k$). It is the tuple
  $(\Omega'_{k+1},P_{k+1},\Omega_{k+1},Q_{k+1},R_{k+1},\Omega''_{k+1},S_{k+1},Z_{k+1})$ of domains at scale $k+1$:
  - $\Omega'_{k+1}$ is determined by $Z_k$ (P5 (2.2)–(2.3) [checked]);
  - $P_{k+1}\subset\Omega'_{k+1}$ is arbitrary (decomposition (2.6)), and $\Omega_{k+1}$ is then determined
    (P5 (2.8));
  - $Q_{k+1}\subset\Omega^{\sim3}_{k+1}$ is arbitrary ((2.14));
  - $R_{k+1}\subset\Omega_{k+1}$ is arbitrary ((2.43)), and $\Omega''_{k+1}$ is then determined ((2.45));
  - $S_{k+1}$ is arbitrary (P6 (2.1)), and $Z_{k+1}^c$ is then determined (P6 (2.3));
  - finally, for $k+1\le k_0$, the canonical hull rule of §3.5 is applied.

  The *new large-field cubes* are $\mathcal N_{k+1}:=P_{k+1}\cup Q_{k+1}\cup R_{k+1}\cup S_{k+1}$.
* **$R$-record** at scale $k\le k_0$. For every ripe component $Z$ of $Z_k$ (§3.5) it records one of
  two outcomes.
  - *Removed*: P7's case with all new small-field characteristic functions, ending in (3.26)–(3.28).
  - *Kept*: the index $i_*$ of the first decomposition of R taken in its large-field branch, and that
    branch's support (§3.3). The supports are: the failure set of (2.18) or of the bounds (2.22)
    [p. 503]; the $S''_k$ of the second decomposition (p. 502); the $Q''_{k_1}$ of (2.21)–(2.33); the
    $\chi''^c$ regions of (2.61); the $S''_k$ of the final decomposition (3.20) on $Z'''_0$ [p. 525]
    (LFR-15). $\mathcal N^R(Z)$ denotes the support.
* **History** $\mathbb A_k=(\varsigma_1,\mathfrak r_1,\varsigma_2,\dots,\varsigma_k,\mathfrak r_k)$, where $\mathfrak r_j$ is the
  $R$-record of scale $j$, empty for $j>k_0$.
  - **Admissible** means generated by these rules from the base rule (LF-6, $Z_0=\varnothing$), with
    every ripe component appearing in the $R$-record of its scale.
  - Localization $\mathbb A_k\cap Z$ to a union of components is as in P6 p. 15 [checked]: all
    elements created at step $k+1$ lie in, or have their boundaries in, $Z_k^c\cap Z_{k+1}$. By P5
    p. 493, a history is determined by its restrictions to the components.
  - The *localized histories* of a component $Z$ form the set $\mathfrak H_k(Z)$ of all localized
    histories, generated by the rules, whose final region is $Z$ with $Z$ a component. This is the
    "maximal set" of P5 (1.27) (p. 494 [checked]).
* **Removal** (R3-08). If $R^{(k)}$ removes a component $Z$, the history is overwritten on $Z$. For
  $1\le j\le k$, $\Omega_j$ and $\Omega''_j$ become $\Omega_j\cup Z$ and $\Omega''_j\cup Z$, and $Z_j$ becomes
  $Z_j\setminus Z$ (as fine-scale sets; $Z$ is a union of $\pi_k$-cubes, hence of $\pi_j$-cubes).
  - This is what P7 (3.6), (3.21) [checked] produce. On a removed component the density becomes the
    small-field expression with $\chi_k(Z)$ and the background $\phi_k(\mathbb B_k(Z^\approx);\tilde\psi_k)$;
    the generating set on $Z$ is $T^{(k)}$.
  - The nesting P5 (1.20) is preserved, since the same set is added to every $\Omega_j$, $\Omega''_j$
    and removed from every $Z_j$.
  - *Separation.* Regions only grow, so $\Omega^c_j\subset Z_j\subset Z_k$ as fine-scale sets. The new
    $\Omega^c_j=\Omega^c_j\setminus Z$ therefore lies in the other components of $Z_k$. These are at fine
    distance $\ge\omega_kML^k\ge2[R_{k-1}]ML^k$ from $Z$. This exceeds the separation $LM R_jL^j$ that
    P5 (2.4) and P7 (2.1) require between $\Omega^c_j$ and $\Omega_{j+1}$ for $j<k$, so the generating-set
    condition P2 (1.1)–(1.3) (Lean `GeneratingSet.separation`) survives.
  - UNCERTAIN: the exact separation constant of P2 (1.3) and P5 (2.4) is to be matched in Lemma G; the
    margin is a factor $\ge2$.
  - Lemma CH's obstacles $O_i$ and the layers of later windows are computed in the overwritten
    generating set (R3-03 (iii)).
* **Deterministic bookkeeping** (R3-12). Spines, clocks and window states are functions of the
  region history, given fixed tie-breaks. Cubes are ordered lexicographically by their index in the
  fundamental domain $\{0,\dots,n_k-1\}^d$. The spanning tree of the contact graph in (U2) is the
  breadth-first tree from the least seed, neighbours visited in increasing order. A connecting
  segment joins the points of the two spines nearest to the centres of the lexicographically least
  pair of cubes realizing the contact; spines are compact, and among nearest points the
  lexicographically least is taken. Hence (D1) counts each region history once. The abstract LF-2
  (§8.1) allows arbitrary choices, which makes it stronger.

There is no admissibility condition involving bounds. Balaban's condition "$K(Z_j\cap Z,\cdot)>0$
for all $j\le k$" (P5 p. 496 [checked]) becomes the theorem LF-2.

### 3.3 Operators

* **One-step operator** $\mathbb T^{(k)}(Z_{k+1},\mathbb A_{k+1}\cap(Z_k^c\cap Z_{k+1}))$: P6 (3.2) [checked]. This is the
  operator $\mathbb T'^{(k)}$ of P5 (2.47): the transformation $T^{(k)}$ restricted to $\Omega_{k+1}^c$, the
  unintegrated Gaussian on $\Omega_{k+1}\setminus\Omega''_{k+1}$, and the characteristic functions of the
  decompositions. It is multiplied by the characteristic functions of $S_{k+1}$, by
  $\exp\big(-\beta_{k+1}A^*_{k+1}(Z_k^c\cap Z_{k+1},\mathbb B_{k+1};\psi,\phi_{k+1}(\mathbb B_{k+1}(\partial\Omega_{k+1});\tilde\psi))\big)$, and by the
  vacuum constants. Here $\mathbb B_{k+1}(\partial\Omega_{k+1})=(\mathbb B_k(W_k)\cap\Omega^c_{k+1})\cup(\mathbb B_{k+1}(U_{k+1})\cap\Omega_{k+1})$ (P6
  (2.15) [checked]).
* **Large-field operator.** $\mathbb T_{k+1}(Z_{k+1},\mathbb A_{k+1})=\mathbb T^{(k)}(\cdots)\,\mathbb T_k(Z_k,\mathbb A_k)\,\exp\mathcal B^{(k)}(Z_k^c\cap Z_{k+1})$
  (P6 (3.3) [checked]).
* **Localized operator** (R3-07). For a component $Z$ of $Z_k$ and $\mathfrak a\in\mathfrak H_k(Z)$,
  $\mathbb T_k(Z,\mathfrak a)$ is defined by the same recursion, run on the lineage of $Z$ (P5 p. 493, P6
  p. 15). By Lemma F (§3.7), $\mathbb T_k(Z_k,\mathbb A_k)=\prod_Z\mathbb T_k(Z,\mathbb A_k\cap Z)$ over the components;
  the factors commute.
* **Kept operators** (R3-08). There are two kinds, according to whether the large-field branch was
  taken before or after the normalization of $R$.
  - (K1) *Before the normalization*: one of the decompositions (2.18), the second decomposition with
    $S''_k$ (p. 502), the decomposition with $Q''_{k_1}$ ((2.21)), or $\chi''$ ((2.61)). The large-field
    branch of (2.61) joins $U^c_{k_1}\cap U^{\sim6}_{k_1}$ and $(U^{\sim3}_{k_1})^c\cap\Omega^c_k\cap\mathbb B_k$ to $\mathbb A_k$
    (p. 516 [checked]). The kept operator is
    $$\mathbb T''_k(Z,\mathfrak a''):=\mathbb T_k(Z,\mathfrak a)\cdot\textstyle\prod_{i<i_*}\chi_i\cdot\chi^c_{i_*},$$
    where $\chi_i$ are the small-field factors of the decompositions taken before $i_*$. All of them are
    multiplication operators by indicator functions of $(\psi_k,\psi,\psi')$, after the shift of
    variables of (2.74), which is a translation of integration variables. This makes precise P7
    p. 516, "It is also clear what form has the corresponding operators $\mathbb T''_k(Z,\mathbb A_k\cap Z)$"
    [checked].
  - (K2) *After the normalization*: the decomposition (3.20) on $Z'''_0$. The kept operator is
    $$\mathbb T''_k(Z,\mathfrak a''):=(3.7)\cdot\chi_k(Z'''_0\cap S''^c_k)\chi^c_k(S''_k)\cdot\exp\big(-\beta_kA^*_k(Z;\psi_k,\phi_k(\mathbb B_k(Z^\approx);\tilde\psi_k))\big)$$
    (P7 p. 525 [checked]: "defined by (3.7) multiplied by a corresponding term on the right-hand side
    of (3.20), and the exponential with the corresponding main action").
  - The exponent of both kinds is $\kappa''_k$ of §3.4.
* **Removed components.** The all-small-field branch of (3.7) enters the polymer expansion
  (3.26)–(3.28) and leaves the history (overwrite, §3.2).
* **Type.** For fixed torus, $Z$ and history, $\mathbb T_k(Z,\mathfrak a)$ is a non-negative measurable
  kernel $K(\psi_k|_{U^\sim};\psi,\psi')$, $U=Z^\approx$. It acts by $F\mapsto\int K\,F\,d\psi\,d\psi'$ on
  bounded measurable functions $F$ of the internal variables ($\psi$ on $\mathbb B_k\cap U^\sim$, $\psi'$ on
  the fluctuation sets). Properties H5 (P5 pp. 493–494 [checked]) are lemmas: support, invariance
  under $O(N)$ acting on $(\psi,\psi',h,g)$ and under the Euclidean group of $\pi_k$, factorization
  (1.22), level factorization (1.23) away from kept components, and domain (1.24)–(1.25).

### 3.4 The budget (replacing $\kappa_k$, $C$ and H6)

* $\kappa_k$: P6 (3.10) [checked], $\kappa_{k+1}(Z')=\sum_{Z\subset Z'}\kappa_k(Z)+\kappa^{(k)}(\mathbb A_{k+1}\cap(Z_k^c\cap Z'))$,
  where $\kappa^{(k)}$ is *defined* as minus the exponent of P6 (3.9) [checked]:
  $\kappa^{(k)}=A_3(\log\beta_k)^{2p_0}M^{-d}(|P_{k+1}|+|Q_{k+1}|+|R_{k+1}|+|S_{k+1}|)-(c_1\log\beta_k+c_2)|Z_k^c\cap Z'|$
  (volumes in the scale-$(k+1)$ units of P6; $c_1,c_2$ are P6's "$O(1)$" and "const.", which may be
  enlarged; $A_3=\min\{8\gamma_0A_0^2/(6^d(9K_1)^2),A_1^2/8\}$, $p_1=p_0$; the gain is stated with $\log\beta_k$
  as in P6, LFR-16a), the boundary factor $\exp\mathcal B^{(k)}$ of (3.3) being included through (2.33)
  by a change of constant (P6 p. 18 [checked]). It is an exact expression, so it gives upper as
  well as lower bounds on $\kappa$ (used in §3.8 Step 6 and §4.10). We write $g_k:=\frac12A_3\hat\lambda_k^{2p_0}\le A_3(\log\beta_k)^{2p_0}$
  for $\hat\lambda_k\ge\lambda_*$; this uses $\log\beta_k=\lambda_k-\log a\ge\hat\lambda_k-3$ (§3.1).
* $C$: P6 (3.11) [checked]. The *product form* (for a family of possible sets $Y\subset W$ chosen
  independently per cube with weight $\eta$, $C^{-1}(Y):=\prod_{\square\in Y}\eta\prod_{\square\in W\setminus Y}(1-\eta)$,
  so that $\sum_YC^{-1}=1$ and $\log C(Y)\le|Y|_\#\log\eta^{-1}+2\eta|W|_\#$) remains available; with the
  piece cap of §3.5 it is no longer needed for P7 (2.33) (§3.8).
* **Budget.** $G_k(Z,\mathbb A\cap Z):=\kappa_k(Z,\mathbb A\cap Z)-\log C(\mathbb A\cap Z)-H_k|Z|_k$, $H_k=H_0\lambda_k$.
  Then (P5 (1.29)–(1.31) [checked]): $\sum_{\mathbb A\cap Z}\int d\psi_k|_Z|\mathbb T_kF|\le\sup_{\mathbb A}e^{-G_k}\,e^{-H_k|Z|_k}\sup\chi|F|$.
* **Lemma B (budget recursion).** For a component $Z'$ of $Z_{k+1}$ (before $R^{(k+1)}$),
  $$G_{k+1}(Z')\ \ge\ \sum_{Z\subset Z'}G_k(Z)+g_k|\mathcal N_{k+1}\cap Z'|_\#-c_v\hat\lambda_{k+1}|Z'|_\#,$$
  where the sum is over the components $Z$ of $Z_k$ (after $R^{(k)}$) with $Z^\uparrow\subset Z'$, and
  $c_v:=M^d(H_0+c_1+3)$, for $\hat\lambda_0\ge\lambda_*(c_2)$. The proof gives the bound with the actual
  $\lambda_{k+1}\le\hat\lambda_{k+1}$ (R3-06). *Proof:* P6 (3.17)–(3.18) [checked]: the old volume costs
  $M^{-d}|Z_k|+H_{k+1}L^{-d}|Z_k|\le H_k|Z_k|$ (P6 p. 20; this leaves a surplus of about
  $\frac12H_0\lambda_k|Z_k|_k$, discarded), and the new volume $Z_k^c\cap Z'$, which contains
  $Z_k^\uparrow\setminus Z_k$, costs at most $(c_1\lambda_{k+1}+c_2+\frac54(L/M)^d+H_{k+1})|Z_k^c\cap Z'|_{k+1}\le c_v\lambda_{k+1}|Z'|_\#$.
  (LFR-05: version 1 charged only $Z'\setminus Z_k^\uparrow$; the bound with $|Z'|_\#$ is the one §4.5 uses.)
  Status: proved in P6 for (3.11); reconstructed (one line) for the product form.
* **Kept exponent** (R3-08). Let $Z$ be kept at scale $k$, with core $k_1$, old localized history $\mathfrak a$,
  and kept record $\mathfrak a''$ of kind K1 or K2. Define
  $$\kappa''_k(Z,\mathfrak a''):=\kappa_k(Z,\mathfrak a)-C_R\hat\lambda_k^{2d+1}+\gamma(\mathfrak a''),\qquad C''(\mathfrak a''):=C(\mathfrak a)\,C_{\rm dec}(\mathfrak a''),$$
  - $\gamma(\mathfrak a'')$ is the explicit small-factor exponent of the branch taken: $\frac29\gamma_0p_0^2(\beta_k)$ for (2.18);
    $\frac{\gamma_0}{2\cdot6^dK_1^2}p_0^2(\beta_k)M^{-d}|S''_k|$ for the second decomposition and for (3.20); the
    exponent of (2.33)′ for $Q''_{k_1}$; and that of (2.62)′ for $\chi''$ (§3.8).
  - $C_{\rm dec}$ is the combinatoric factor of that decomposition ($e^{O(1)|\cdot|}$ on its domain).
  - Then $\gamma-\log C_{\rm dec}\ge A'_3\hat\lambda_k^{p_R}$ (§3.8 Step 6).
  - In the quiet window, $\kappa_k(Z,\mathfrak a)=\kappa_{k_1}(Z_{k_1}\cap Z)-\sum_{j=k_1}^{k-1}(c_1\log\beta_j+c_2)|Z^c_j\cap Z_{j+1}\cap Z|_{j+1}$
    exactly: no gains, and $\kappa^{(j)}$ is the exact expression above. So $\kappa''$ is the refund form of
    §3.8 Step 6 ("$\kappa_{k_1}$ minus the window costs minus the residual plus the gain").
  - The bound $\int|\mathbb T''_kF|\le e^{-\kappa''_k}\sup\chi|F|$ is proved for both kinds by P7's refund
    route (3.8)–(3.10), together with the additional small factor of p. 520 [checked]: "We estimate in
    the same way the operators constructed in the last section and involving some large field
    restrictions, but then with an additional small factor". This needs $c_1\ge C_{39}$, $c_2\ge C'_{39}$
    (§5 row 14).
  - One route serves both kinds. P7 p. 502's alternative (the old bound times the small factor, minus
    the (2.15) loss) also closes, but is not used.
  - $G''_k:=\kappa''_k-\log C''-H_k|Z|_k=G_k-C_R\hat\lambda_k^{2d+1}+\gamma-\log C_{\rm dec}$, which is (Rg) of §4.1 as
    an identity.

### 3.5 Bookkeeping data, window states and ripeness

Each component $Z$ of $Z_k$ carries the following data, as deterministic functions of the history
(§3.2).

* A **spine** $\Gamma(Z)$, a subset of the continuous torus $(\mathbb R/n_k\mathbb Z)^d$ in scale-$k$ cube units.
  It is a point, or a compact connected union of finitely many segments of total Euclidean length
  $\ell(Z)>1$, with
  $$Z\subset N_{\rho_k+4}(\Gamma(Z)).\tag{3.1}$$
  A spine may wind around the torus; a winding spine has length $\ge n_k$.
* A **gain clock** $b(Z)$: the last scale at which new large-field cubes ($\mathcal N_j$ or $\mathcal N^R$)
  appeared in the history of $Z$, including the histories of all components merged into it.
* A **smallness clock** $s(Z)$. If $\Gamma(Z)$ is a point, it is the scale since which it has been a
  point. Otherwise it is the projected epoch $s(Z):=k+\lceil\log_L\ell(Z)\rceil$.
* For $k\le k_0$, a **window state** (C-02; REPAIRS-astra (B.1)). It is one of
  $$\mathsf{Pre}\quad|\quad\mathsf{Pending}(q,\nu)\quad|\quad\mathsf{Active}(q,\nu,\mathcal M),$$
  where $q\in\mathbb N$ is the *core scale*, $\nu\in\mathbb N_{\ge1}$ the *piece count*, and $\mathcal M$ a finite set
  of scales, the *merge record*. The admissibility conditions at scale $k$ are:
  $$\begin{array}{ll}
  \mathsf{Pre}: & \Gamma(Z)\text{ not a point};\quad q:=s>k,\ \nu:=1,\ \mathcal M:=\varnothing;\\
  \mathsf{Pending}(q,\nu): & k<q\le k+h_k+1,\quad1\le\nu\le\nu_{\max}(k),\quad\mathcal M:=\varnothing;\\
  \mathsf{Active}(q,\nu,\mathcal M): & q\le k,\quad1\le\nu\le\nu_{\max}(k),\quad\mathcal M\subset(q,k].
  \end{array}\tag{B.1}$$
  - In every state put $t^*(Z):=\max\{q+n_q(q),\ s+n_2(s)\}$ (the *ripeness time*) and
    $U(Z):=\frac12\sum_{\xi\in\mathcal M}\tau_\xi$ (the *bank*).
  - A pre-window component has $t^*=s+n_q(s)>k$, since $n_2\le n_q$ (F4). Pre and Pending components
    have $U=0$. A pending component cannot be ripe: $t^*\ge q+n_q(q)>q>k$.
  - Pending replaces version 3's in-window state with a core in the future. That state was not closed
    under (W3) (C-02).
  - The Lean type is the tagged sum `Pre | Pending (q ν : ℕ) | Active (q ν : ℕ) (M : Finset ℕ)`, replacing
    `Option (ℕ × ℕ × Finset ℕ)` (R2-13). Window states exist only for $k\le k_0$ (T7).

**Canonical hull rule** (LFR-07; only at scales $k+1\le k_0$, R3-05). At step $k\to k+1$, after the
domains of §3.2 are formed, repeat the following: replace simultaneously every component of
diameter $\le\mathrm{crit}_{k+1}$ by its hull, and stop when nothing changes.
- Such components are small by (3.0), so the hull is defined.
- Each round either stops or strictly enlarges the domain, so the rule terminates on the finite
  torus, and its result is a function of its input.
- Contacts created by hulls are merges and are recorded by (U2).
- For $k+1>k_0$ no hull is taken. The frozen regime does not need hulls (§4.7), and on small tori
  ($n_k$ as small as $L<\mathrm{crit}_k$) the hull would be undefined.

**Spine and clock updates** (consistency with (3.1) in §4.3).
- (U1) *Pure shadow* (one old part $Z$, no new cubes, no contact). $\Gamma'=\Gamma/L$, replaced by one of
  its points if $\ell(\Gamma)/L\le1$; $b'=b$.
- (U2) *Event* ($m$ old parts, $r$ new cubes, $(m,r)\ne(1,0)$, including contacts caused by hulls).
  $\Gamma'$ is the union of the contracted spines, the centres of the new cubes, and connecting
  segments of length $\le D_{k+1}$ along the spanning tree (§3.2) of the contact graph of the seed sets
  and hull boxes. Two of them are in contact if their index distance is $<\omega_{k+1}$. If
  $\ell(\Gamma')\le1$, $\Gamma'$ is replaced by one of its points (LFR-08). $b'=k+1$ if $r\ge1$, else
  $b'=\max_ib_i$.
- (U3) *Hull.* The spine becomes the centre of the box. $s$ is reset to the current scale only if the
  spine was not a point (LFR-06).
- (U4) *Kept component* at scale $k$: domain and spine unchanged, $b'=k$.

**Transitions** (REPAIRS-astra §B.1, checked; changes listed below). Write $\mu:=k+1$. A *merge* is an
event with $r=0$ and $m\ge2$, including contacts caused by hulls. A *certified one-box entry* at
scale $e$ is one of: a (T1) entry, a point restart in (T2), (T3) or (T5), or a kept component (T6).
The transitions are classified after the spine update and the hull rule. The list is exhaustive:
every component of $Z_{k+1}$ before $R$ arises either from one old part with no new cube and no contact
(T1), or from an event (T2)–(T5).

- (T1) *Pure shadow*, with or without hull.
  - Pre stays Pre unless its spine becomes a point; then it becomes $\mathsf{Active}(\mu,1,\varnothing)$
    (certified entry).
  - Active keeps $(q,\nu,\mathcal M)$.
  - $\mathsf{Pending}(q,\nu)$ keeps its data if $\mu<q$, and becomes $\mathsf{Active}(q,\nu,\varnothing)$ if $\mu=q$
    (*activation*).
- (T2) *New cubes* ($r\ge1$, any $m\ge0$, any states). This is a restart: $b'=\mu$, all merge records
  and banks are discarded, and the output is $\mathsf{Active}(\mu,1,\varnothing)$ (certified entry) if
  $\Gamma'$ is a point, otherwise Pre.
- (T3) *Merge with a Pre part.* Restart as in (T2), with $b'=\max_ib_i$.
- (T4) *Merge, all parts Active or Pending, $\nu':=\sum_i\nu_i\le\nu_{\max}(\mu)$.* Put $\mathcal M_i:=\varnothing$ for
  Pending parts and
  $$\tilde q:=\max_iq_i,\quad E:=\textstyle\bigcup_i\mathcal M_i\cup\{\mu\},\quad t_0:=\max\{\tilde q+n_q(\tilde q),\,s'+n_2(s')\},$$
  $$T:=\min\{t\ge t_0:\ k_1(t)\notin B(E)\},\qquad q':=k_1(T),\qquad\mathcal M':=E\cap(q',\infty).\tag{B.3}$$
  - $T$ exists because $B(E)$ is finite.
  - The output is $\mathsf{Pending}(q',\nu')$ if $q'>\mu$ (then $\mathcal M'=\varnothing$), and
    $\mathsf{Active}(q',\nu',\mathcal M')$ if $q'\le\mu$.
  - The merges in $E\cap[0,q')$ are *released*. A merge behind a pending target is released at once
    and makes no deposit.
- (T5) *Overflow*: a merge with all parts Active or Pending and $\sum_i\nu_i>\nu_{\max}(\mu)$. Restart as in
  (T3).
- (T6) *$R$ at scale $k\le k_0$.* $R^{(k)}$ acts exactly on the Active components with $t^*=k$.
  - A removed component has no successor, and the history is overwritten on it (§3.2).
  - A kept component keeps its domain and spine, has $b'=k$, and becomes $\mathsf{Active}(k,1,\varnothing)$
    (certified entry: a ripe component is one box, Lemma C (g)). Its bank is discarded.
  - Every other component (all Pre, all Pending, the non-ripe Active ones) is unchanged, together
    with its budget.
- (T7) *End of the window regime.* After $R^{(k_0)}$, the transfer of §4.7 is applied, and then the
  window states, $t^*$, $\nu$ and $U$ are discarded; a pending target beyond $k_0$ needs no activation. For
  $k_0<k\le k_f$ there are no window states, no hulls and no $R$.
- *Base* (C-05). $Z_0=\varnothing$, and every component of $Z_1$ is a (T2) event with $m=0$, charged by (B)
  at $k=0$.

A component is **ripe** at scale $k\le k_0$ if it is Active and $t^*(Z)=k$.

*Where this differs from REPAIRS-astra §B.1.* The differences are:
- components and contacts are those of the relation $d<\omega$ (R3-01);
- hulls and window states exist only for $k\le k_0$, on small sets (R3-05);
- all thresholds use $\hat\lambda$ (R3-06);
- the empty-set convention for $k_1$ is fixed (R3-12);
- (T6) states explicitly that Pre and Pending components are untouched by $R$;
- diameters of merged clusters are bounded by $\nu(\mathrm{crit}+\omega)$ in place of $\sqrt d\,\nu\,\mathrm{crit}$, which
  is why $h_j$ carries $\mathrm{crit}_j+\omega_j$.

The rules themselves are REPAIRS-astra's.

**Lemma C4 (closure, horizon, activation).** Assume (G1), (G2), (K) of §4.1 and $\hat\lambda_0\ge\lambda_*$.
(a) After every transition, (B.1) holds. Moreover every Active or Pending component $Z$ of $Z_k$ is
covered by at most $\nu(Z)$ boxes of side $\le\mathrm{crit}_k$, and has $\ell(Z)\le(\nu(Z)-1)D_k$ (B.2).
(b) If (T4) is used at scale $\mu$, then
$$\tilde q\le\mu+h_\mu,\qquad k_1(s'+n_2(s'))\le\mu-1,\qquad\max_iq_i\le q'\le\mu+h_\mu+1,\qquad t^*(Z')=T.\tag{B.4}$$
(c) Under (T1), $t^*$ does not increase, and $\nu$, $\mathcal M$ and $U$ do not change.

*Proof.* (a), cover:
- *Shadow.* A box $B$ of side $\le\mathrm{crit}_k$ gives $B^\uparrow$ of side $\le\mathrm{crit}_k/L+2$. By (G1) its seed
  set lies in $N_{s_*r_k}(B^\uparrow)$, a box of side $\le\mathrm{crit}_k/L+2+2s_*r_k\le\mathrm{crit}_{k+1}$, because
  $c_0(1-L^{-1})\ge s_*+1$, $r_k\le r_{k+1}$ and $10/L+2\le10$.
- A hull is one box of side $\le\mathrm{crit}$. A (T4) merge takes the union of the covers, and $\nu'$ is
  their sum. Restarts and entries are point spines, hence one box (§4.3).

(a), spine: a point at entry; contraction divides lengths by $L$; at (T4), by (4.1),
$\ell'\le\sum_i(\nu_i-1)D_k/L+(m-1)D_\mu\le(\nu'-1)D_\mu$; a hull makes the spine a point.

(b). By (a) and the cap, $\ell'\le\nu_{\max}(\mu)D_\mu$, so
$s'\le\mu+\lceil\log_L\max(\ell',1)\rceil\le\mu+C\log\hat\lambda_\mu$ and $s'+n_2(s')\le\mu+C'\log\hat\lambda_\mu$. Since
$\mu+n_q(\mu)>\mu+\hat\lambda_\mu/(\alpha\log L)$, for $\hat\lambda_0\ge\lambda_*$ we get $s'+n_2(s')<\mu+n_q(\mu)$, hence
$k_1(s'+n_2(s'))\le\mu-1$.
- Each Active input has $q_i\le\mu-1$. Each Pending input has $q_i\le(\mu-1)+h_{\mu-1}+1\le\mu+h_\mu$.
- Since $k_1$ is nondecreasing and $k_1(c+n_q(c))=c$, we have
  $c:=k_1(t_0)=\max\{\tilde q,\,k_1(s'+n_2(s'))\}\le\mu+h_\mu$.
- Every $\xi\in E$ has $\xi\le\mu$ and $h_\xi\le h_\mu$, so $\mu+h_\mu+1\notin B(E)$.
- As $t$ increases from $t_0$, $k_1(t)$ takes every integer value $\ge c$ in order. So $q'$ is the least
  integer $\ge c$ outside $B(E)$, and $\tilde q\le c\le q'\le\max(c,\mu+h_\mu+1)=\mu+h_\mu+1$.
- By the definition of $k_1$, $q'+n_q(q')\le T<(q'+1)+n_q(q'+1)$.
  - If $T>t_0$, then $k_1(T-1)\in B(E)$ and $k_1(T-1)<q'$, so $T=q'+n_q(q')$, and $t^*(Z')=T$ because
    $T>s'+n_2(s')$.
  - If $T=t_0$, then either $t_0=s'+n_2(s')\ge q'+n_q(q')$, or $t_0=\tilde q+n_q(\tilde q)$ and $q'=\tilde q$. In
    both cases $t^*(Z')=T$.

(c). $q$ is fixed and $s$ is nonincreasing: $k+1+\lceil\log_L(\ell/L)\rceil\le k+\lceil\log_L\ell\rceil$, and a spine
that becomes a point at $k+1$ gets $s=k+1$, at most its old projected epoch. At (T1) entries,
$q=s=\mu$ is at most the old $s$. Activation changes no number. $\square$

The pending horizon is therefore at most $h_k+1=O(\log\hat\lambda_k)$ scales ahead of the current scale,
and cores never move backward.

**Lemma C (covered windows).** Let $Z$ be Active at scale $k\le k_0$ with data $(q,\nu,\mathcal M)$. For
$j\le k$ let $Z_j\cap Z$ denote its *lineage* at scale $j$: the union of the components of $Z_j$ whose
descendants lie in $Z$, in the history overwritten by removals. Then:
- (a) No new large-field cubes appear in the lineage at the steps $j\to j+1$, $q\le j<k$, and $b(Z)\le q$.
  Every lineage component at a scale $j\in[q,k]$ is Active or Pending.
- (b) For every $j\in[q,k]$, $Z_j\cap Z$ is covered by $\nu$ boxes of side $\le\mathrm{crit}_j$.
- (c) $\ell(Z)\le(\nu-1)D_k$.
- (d) Trace each branch of the lineage back to its most recent certified one-box entry (the *leaves*
  of the window). At that entry the branch was one box of side $\le\mathrm{crit}$.
- (e4) (C-01 repaired.) Every merge of the lineage at a scale $\xi\le q$ that occurs after the most
  recent certified entry of its branch satisfies $\xi+h_\xi<q$. Merges at or before such an entry
  are exempt; a point restart at $q$ is allowed. Every merge after $q$ lies in $\mathcal M\subset(q,k]$. At
  scale $q$, every lineage component is one box of side $\le\mathrm{crit}_q$, and distinct ones are
  $\omega_q$-separated.
- (f4) $q+n_q(q)\le t^*(Z)<(q+1)+n_q(q+1)$, so $k_1(t^*(Z))=q$.
- (g) If $Z$ is ripe ($t^*=k$), then $s+n_2(s)\le k$. $Z$ has been one box of side $\le\mathrm{crit}$ at every
  scale of $[s,k]$, and is one box of side $\le\mathrm{crit}_k$ at $k$.

*Proof.*

(a) A gain, a merge with a Pre part, and an overflow are restarts (T2), (T3), (T5), after which every
later core is $\ge$ the restart scale, by (B.4) and (T1). Such a restart at the step $j\to j+1$ with
$j\ge q$ would force the core to be $\ge j+1>q$. A Pre lineage component at a scale $j\ge q$ must
enter before it joins $Z$, either at a (T1) entry at some $e>j$ or by a restart. Then the core of $Z$
is $\ge e>q$, a contradiction.

(b) By (a), the lineage components at scale $j\in[q,k]$ are Active or Pending. By Lemma C4 (a) each is
covered by $\nu_i$ boxes, and the $\nu_i$ add up to at most $\nu$, since $\nu$ is additive at (T4) and
constant under (T1).

(c) is Lemma C4 (a). (d) holds because each certified entry is a point spine, hence one hulled box.

(e4) is REPAIRS-astra's argument.
- Let $Y$ be a lineage component at scale $q$. If $Y$ has no merge after its last certified entry, its
  shadows stay covered by one box of side $\le\mathrm{crit}$ (Lemma C4 (a)), and the hull keeps it one
  box.
- Otherwise let $\xi\le q$ be its last post-entry merge, necessarily a (T4) merge. Since $\xi\le q$,
  $\xi\notin\mathcal M(Z)$, so $\xi$ was released at some (T4) transition with core $q''\le q$, and
  $q''\notin[\xi,\xi+h_\xi]$, $q''>\xi$. Hence $\xi+h_\xi<q''\le q$, because cores never decrease (B.4).
- At scale $\xi$ the merged component is one class of the relation $d<\omega_\xi$ covered by at most
  $\nu_{\max}(\xi)$ boxes of side $\le\mathrm{crit}_\xi$, so its sup-diameter is
  $e_\xi\le\nu_{\max}(\xi)(\mathrm{crit}_\xi+\omega_\xi)$.
- There is no merge in $(\xi,q]$. A pure shadow step maps a diameter $e$ to at most $e/L+2s_*r+2$ (by
  (G1)), and $r_j\le r_q$. With $n:=q-\xi\ge h_\xi+1$,
  $$e_q\le L^{-n}\nu_{\max}(\xi)(\mathrm{crit}_\xi+\omega_\xi)+\frac{2s_*r_q+2}{1-L^{-1}}<1+\frac{2s_*r_q+2}{1-L^{-1}}\le\mathrm{crit}_q.\tag{B.5}$$
  The middle step uses $L^{h_\xi}\ge L^2\cdot2\sqrt d\,\nu_{\max}(\xi)M(\mathrm{crit}_\xi+\omega_\xi)$. The last step uses
  $c_0(1-L^{-1})\ge s_*+1$: then $(1-L^{-1})\mathrm{crit}_q\ge2(s_*+1)r_q+5>(1-L^{-1})+2s_*r_q+2$.
- So $Y$ is hulled into one box no later than at $q$, and since $\xi$ was its last merge, no later hull
  makes a contact. Distinct components are $\omega_q$-separated by definition.
- If an event occurs at $q$ itself: a point restart is a new certified entry, and a (T4) merge at $q$
  cannot produce core $q$, which lies in its own newly blocked strip.

(f4) At entries, $t^*=\mu+n_q(\mu)$: the spine is a point since $\mu$, and $n_2\le n_q$. At (T6) kept,
$s+n_2(s)\le k$ by ripeness. After (T4) the claim is (B.4) and the definition of $k_1$. Under (T1)
and activation, $t^*$ does not increase and stays $\ge q+n_q(q)$.

(g) $t^*=k$ gives $s+n_2(s)\le k$, so the spine has been a point on $[s,k]$. A point-spine component
lies in $N_{\rho+4}$ of the point, has diameter $\le\mathrm{crit}$, is small by (3.0), and is hulled. $\square$

*Status:* reconstructed. (a)–(d) follow version 3 and MERGES-astra.md's per-atom cover (its (3.5)),
with pieces in place of atoms. Lemma C4, (e4) and (f4) are REPAIRS-astra §B.2, proved there; checked
here and adapted to $\omega$-components and to tori. The counting audit's C-01 history (a restart
whose merge lies at its own core) is the exempt case of (e4). Its C-02 history (a core pushed to
$4+h_3>3$) is a Pending output of (T4).

A ripe component therefore has the following properties, which are the hypotheses (RQ) of LF-4
(§3.8):
- no new large fields in its window $[q,k]$;
- a cover by $\nu\le\nu_{\max}(k)$ boxes of critical size at every scale of the window;
- it has been one box of side $\le\mathrm{crit}$ for the last $n_2(s)$ scales;
- a core $q=k_1(k)$ at which its lineage is a union of pairwise $\omega_q$-separated boxes.

### 3.6 Def-7: the inductive classes

Let $\tau_t:=2A_2\hat\lambda_t^{p_2}$; note $\tau_t\ge2p_2(\beta_t)$, since $\hat\lambda_t\ge\lambda_t\ge\log\beta_t$. Let $v_j,w_j,\sigma_k$
be the explicit cost coefficients of §4.2: $v_j=c_vC_V\hat\lambda_j\rho_j^{d-1}$, $w_j=v_j\rho_j$,
$\sigma_k=\sum_{j>k}v_jL^{-(j-k)}$. Put
$$V_k(Z):=2\sigma_k\ell(Z)+\sum_{j=k+1}^{t^*(Z)}w_j .$$

**Def-7** (summary; the exact form, as a predicate on representations, is §8.2). For $1\le k\le k_0$,
$\mathcal R_k$ is the set of families $\rho_k(\psi_k;h,g)$ over admissible tori which have a representation
$\mathrm{rep}$ with $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep},\rho_k)$. The representation consists of small-field data, a
finite set of admissible histories with deterministic bookkeeping, and boundary terms.
$\mathrm{IsRep}_k$ consists of:
- (D1) **form** (P5 H1 [checked]): $\rho_k=\sum_{\mathbb A}\mathbb T_k(Z_k(\mathbb A),\mathbb A)\big[e^{\mathcal B^{(k)}(\mathbb A)}\chi_k(Z_k^c)\exp(\mathcal A_k+\mathcal F_k+\mathcal R^{(k)})(Z_k^c)\big]$,
  with $\mathbb T_k$ *defined* from the history and the small-field data (§3.3);
- (D2) **small-field data**: P4 (H.1)–(H.7) at $\lambda=\infty$ and P5 H2–H4 (the class Def-6), with the
  backgrounds without the $\nu$-term (P5 (1.9));
- (D3) $\chi_k(Z_k^c)$ as P5 (1.18)–(1.19) [checked];
- (D5) **operator bound, at every scale $j\le k$** (R3-07): for every component $Z$ of $Z_j$ and every
  $\mathfrak a\in\mathfrak H_j(Z)$, P5 (1.26) holds for the localized operator, with the domain (1.24)–(1.25)
  localized to $Z$; and P5 (1.27) holds over $\mathfrak H_j(Z)$;
- (D6) **(H6′) budget invariant**: for every component $Z$ of $Z_k$ and admissible $\mathbb A$,
  $$t^*(Z)>k\qquad\text{and}\qquad G_k(Z,\mathbb A\cap Z)\ \ge\ \tau_{t^*(Z)}+V_k(Z)+\nu(Z)+U(Z);$$
- (D7) **boundary terms** H7 (P5 (1.36)–(1.39) [checked]) with constant $B_0$;
- (D8) local data and torus independence (roadmap §3.5);
- (D9) $\beta_k>BL^{k(d-2)}$, $0<\nu_k\le\bar\nu$, $\beta_k\nu_k\le1$ (P5 (1.42)).

The H5 properties of the operators (D4 of version 3) are lemmas about the defined operators, not
conditions: "their properties are not really a part of the inductive assumptions, but they are
statements which are consequences of the definition" (P5 p. 494 [checked]).

The variants are as follows.
- $\mathcal R^{\rm pre}_k$ is the same with $t^*(Z)\ge k$ in (D6) (ripe components allowed): the image
  of $S^{(k-1)}T^{(k-1)}$ before $R^{(k)}$.
- $\mathcal R^\flat_k$ ($k_0\le k\le k_f$) is the same without window data, with complete backgrounds for
  $k>k_0$, without the condition $\beta_k\nu_k\le1$ in (D9), and with (D6) replaced by
  $$\text{(H6}^\flat)\qquad G_k(Z,\mathbb A\cap Z)\ \ge\ A_2\hat\lambda_{k_0}^{p_2}+2\sigma_k\ell(Z)+\sum_{j=k+1}^{\hat k_f}w_j.$$
  If $k_0\le0$, read $k_0$ as $0$ here and in LF-5, so that the threshold is $A_2\hat\lambda_0^{p_2}\ge p_2(\beta)$.
  The a priori horizon $\hat k_f\ge k_f$ makes (H6♭) causal (R3-06).
- (H6′) implies P5 (1.30) with $\ell=2$, since $\tau_{t^*}\ge\tau_{k+1}>2A_2\lambda_k^{p_2}\ge2p_2(\beta_k)$, using
  $\hat\lambda_{k+1}=\hat\lambda_k+\theta>\lambda_k$. (H6♭) implies (1.30) with $\ell=1$ and the frozen threshold
  $A_2\hat\lambda_{k_0}^{p_2}\ge p_2(\beta_{k_0})$.

*Lean types.*
- Tori and scale lattices are `Torus d n` (Def-1); domains are `Finset`s of cubes.
- The history is an inductive list of records whose fields are domains satisfying the stated
  equalities, generated by the deterministic rules of §3.2.
- Spines are finite lists of segments in the continuous torus, clocks are natural numbers, and the
  window state is the tagged sum of §3.5. All bookkeeping data are functions of the region history.
- Kernels are non-negative measurable functions with an explicit Lebesgue reference measure on the
  internal variables.
- The functions $\hat\lambda_j$, $\hat k_f$, $n_q$, $n_2$, $k_1$, $h_j$, $\omega_k$, $\nu_{\max}$, $v_j$, $w_j$, $\sigma_k$, $\tau_t$ are explicit
  definitions from $\beta,\nu$ and the constants.

Def-7 is frozen only after the reconstruction document is approved (roadmap §3.1; §8.4).

### 3.7 The statements LF-1 … LF-8

Throughout, the constants are bound by the prefix of §5.1, and $\beta\ge\beta_0$.

**LF-1 (action lower bounds; P6 Prop 3.1 for hard spins).** There is $\gamma_0=\gamma_0(d)>0$ such that
for every $k$, every generating set $\mathbb B_{k+1}$ satisfying P2 (1.1)–(1.3), every domain $X$ with
$X\cap(\Omega_j\setminus\Omega_{j+1})$ a union of scale-$j$ unit cubes, every $\psi$ on $\mathbb B_{k+1}\cap X$
and every $\varphi:X\cap T_\eta\to S^{N-1}$:
$$\beta_{k+1}A^*_{k+1}(X,\mathbb B_{k+1};\psi,\varphi)\ge\gamma_0\Big\{\sum_{j=0}^{k+1}\tfrac{\beta_j}2\sum_{b\subset\Lambda_j\cap X}|\partial^1\psi_j(b)|^2+\sum_{j=0}^{k}\tfrac{\beta_{j+1}}2\sum_{b\in\mathrm{st}(\Omega^c_{j+1}\cap T^{(j+1)})\cap X}|\psi_{j+1}(b_+)-(Q\psi_j)(b_-)|^2\Big\},$$
and, if $||\psi|-1|<c_5$ and $\nu_j(1-h\cdot(\psi)_0)<c_5$ on $\Lambda_j\cap X$,
$\beta_{k+1}A^*_{k+1}\ge\gamma_0\sum_j\beta_j\sum_{y\in\Lambda_j\cap X}[\frac12(|\psi_j(y)|-1)^2+\nu_j(1-h\cdot(\psi_j(y))_0)]$,
where $\beta_j,\nu_j$ are related to $\beta_{k+1},\nu_{k+1}$ by canonical scaling (P6 (3.5)–(3.6), p. 17
[checked]). *Sketch.* Per bond of $\Lambda_j$: $|\partial^1\psi_j(b)|^2\le3|\psi_j(y)-Q_j\varphi(y)|^2+3|Q_j\varphi(y)-Q_j\varphi(y')|^2+3|\psi_j(y')-Q_j\varphi(y')|^2$;
the middle term is bounded by $C_d$ times the Dirichlet energy of $\varphi$ on the two blocks (a
two-block Poincaré inequality: D3 Lemma 20, App. C, proved [review]; E3 §4 [review]); the canonical
scaling $\beta_j\propto(L^j\eta)^{d-2}$ compensates the factor $(L^j\eta)^{2-d}$ of that inequality, and each fine bond lies in
$O(1)$ layers, so the sum is $\le C\beta_{k+1}(\langle\psi-Q\varphi,a(\psi-Q\varphi)\rangle+\|\partial^\eta\varphi\|^2)$;
the cross-layer bonds use the averaging structure of $\mathbb B_{k+1}$ (P2 (1.4)–(1.6), (4.21)). For the
second bound, hard spins give it directly: $|Q_j\varphi|\le1$ and
$1-|Q_j\varphi(y)|^2=\frac1{2|B|^2}\sum_{x,x'\in B(y)}|\varphi_x-\varphi_{x'}|^2$, so $(1-|Q_j\varphi|)^2\le1-|Q_j\varphi|^2$ is
controlled by the block Dirichlet energy, and $1-h\cdot u\le\frac12|u-h|^2$ for unit $u$; P6's hypothesis
on $\alpha$ is not needed. *Status:* reconstructed (P6 says "very simple", no proof; P2 Prop 2.2 has
no proof; ER-030, ER-094). LF-1 holds for arbitrary generating sets, so it applies unchanged to
covered windows (§3.8).

**LF-2 (step counter; reconstructed).** Assume the axioms (G1), (G2), (B), (Rg), (K), (H-λ), (H-T) of
§4.1, with $Z_0=\varnothing$ and $\hat\lambda_0\ge\lambda_*$. Then:
- (i) (H6′) for all components of $Z_k$ implies (H6′)$^{\rm pre}$ for all components of $Z_{k+1}$
  ($k+1\le k_0$);
- (ii) (H6′)$^{\rm pre}$ at scale $k\le k_0$ and the $R$-rule imply (H6′) after $R^{(k)}$;
- (iii) the base rule gives (H6′) at $k=1$;
- (iv) (H6′) at $k_0$ implies (H6♭) at $k_0$, and (H6♭) is preserved by the steps $k\to k+1$ for
  $k_0\le k<k_f$.

Consequences:
- P5 (1.30) with $\ell=2$ at every $k\le k_0$;
- $G_k\ge2p_2(\beta_k)+\nu$ for every ripe component (the input of LF-4, §3.8 Step 6);
- every ripe component is Active with core $k_1(k)$ and a box core (Lemma C);
- P5 (1.31) with $\ell=1$ and threshold $p_2(\beta_{k_0})$ for $k_0\le k\le k_f$ (the repaired P6 Thm 4).

Proof: §4. LF-2 is an internal lemma (§8.1); it is never frozen, and its axioms are discharged by
Lemma G, Lemma B and LF-4's internal lemma (Rg).

**LF-3 (one step, $1\le k<k_0$; P5 Thm 1, P6 Thm 1).** If $1\le k<k_0$ (LFR-16b), $\rho_k\in\mathcal R_k$ with
$\bar\nu\le\beta_k^{-1}\le\frac78L^{-2}$, then $S^{(k)}T^{(k)}\rho_k\in\mathcal R^{\rm pre}_{k+1}$ with
$BL^{d-2},\bar\nu L^2$ in place of $B,\bar\nu$ and the same remaining constants, except that the new
functions with superscript $k+1$ satisfy (H.2)–(H.4), (H.7) with $\frac32\kappa$ in place of $\kappa$
(P5 p. 499 [checked]); the induced map on effective actions satisfies the conclusions of P4 Thm 2
with $c_{k+1}=0$, $d_{k+1}=b_{k+1}$. *Sketch:* P5 §§2–3 and P6 §§2–4 unchanged, with the analytic
inputs I-1, I-2, I-4, I-5, I-8 and PE; (D6) for the output is LF-2 (i), which replaces the sentence
"Instead we have a weaker condition $K\ge0$" (P6 p. 21 [checked]). *Status:* sketched in P5–P6;
known gaps: P5 Lemma 2.1 (proved as P7 Lemma 2.5), the choice $c=0$, $d=b$ (P4 p. 717; I-7).
*Representation form* (R3-10): for every $\mathrm{rep}_k$ with $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep}_k,\rho_k)$, the
representation $\mathrm{rep}$ of $S^{(k)}T^{(k)}\rho_k$ is constructed explicitly. Its histories are those of
$\mathrm{rep}_k$ extended by a step record, and $\mathrm{IsRep}^{\rm pre}_{k+1}(\mathsf c',\mathrm{rep},S^{(k)}T^{(k)}\rho_k)$ holds. LF-4
consumes exactly this $\mathrm{rep}$.

**LF-4 ($R$ on covered windows; P5 Thm 2 = P7 Thm 2, modified; existential form, R3-10).** The
statement is about representations. Let $1\le k\le k_0$, let $\mathrm{rep}$ be a representation of $\rho$ with
$\mathrm{IsRep}^{\rm pre}_k(\mathsf c,\mathrm{rep},\rho)$, and suppose $\rho=S^{(k-1)}T^{(k-1)}\rho_{k-1}$ with
$\mathrm{IsRep}_{k-1}(\mathsf c,\mathrm{rep}_{k-1},\rho_{k-1})$ and $\mathrm{rep}$ produced from $\mathrm{rep}_{k-1}$ by LF-3 (by LF-6 if
$k=1$). Then
there are a family $\rho'$ and a representation $\mathrm{rep}'$ such that:
- (a) $\int\rho'\,d\psi_k=\int\rho\,d\psi_k$ identically in $(h,g)$;
- (b) $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep}',\rho')$;
- (c) the small-field data of $\mathrm{rep}'$ equal those of $\mathrm{rep}$, except that $\mathcal R^{(k)}_m$ is replaced by
  $\mathcal R^{(k)}_m+\mathcal R''^{(k)}_m$, where $\mathcal R''^{(k)}_m$ has the properties and bounds of P5 H4;
- (e) the boundary terms of $\mathrm{rep}'$ created at scale $k$ satisfy (D7) with a constant $B^\sharp$ that
  depends only on the constants chosen before $B_0$ (§5.1; P7 p. 529 [checked]).

The precise statement is §8.3. The construction inside the proof is P7's $R^{(k)}$ (P7 (1.3)–(1.6)
[checked]), applied to the ripe components of $\mathrm{rep}$ in place of the components with $K=0$. The
statement "every ripe component is removed or kept with $G''\ge G-C_R\hat\lambda^{2d+1}+A'_3\hat\lambda^{p_R}$" is
the internal lemma LF-4R, which is (Rg) of §4.1. LF-2 (ii) then gives (D6) for $\mathrm{rep}'$.
*Modifications of P7, each to be written in the reconstruction document; details in §3.8:*
- (M1) *Trigger.* Ripeness (§3.5) replaces $K=0$; it supplies the hypotheses (RQ).
- (M2) *Covered windows.* P7 §§2–3 on windows whose lineage is covered by $\nu\le\nu_{\max}(k)$ boxes of
  critical size. The re-derived estimates of §3.8 are (2.15)′, (2.26)′–(2.30)′, (2.33)′,
  (2.48)′–(2.49)′, (2.59)′, (2.60)′, (2.61)′–(2.62)′, (3.15)′ and (3.17)′–(3.19)′. They use the chain lemma
  (Lemma CH) and the lattice separation lemma (Lemma S). P7 (3.11) holds box by box at the core scale
  (Lemma L, resting on Lemma F). With the merge-free strip of §3.5 every window point is exposed, so the
  hole lemma of version 2 is not needed.
- (M3) *Input bound by the refund route.* P7 (3.8)–(3.10) in the form of the window certificate of
  §3.8 (MERGES-astra.md (3.6)), with $c_1\ge C_{(3.9)}$ (LFR-02). The kept operators and exponents are
  those of §3.3–§3.4.
- (M4) *Lemma 3.1 (coset average) written out.*
  - For unit $u$ with $u\cdot e_1\neq-1$, the rotation in the plane of $e_1,u$,
    $R(u)=I+(ue_1^\top-e_1u^\top)+\frac1{1+e_1\cdot u}(ue_1^\top-e_1u^\top)^2$, satisfies $R(u)e_1=u$, is
    orthogonal for real unit $u$, and is analytic in $u$ (also for complex $u$ near the real sphere).
  - On $u\cdot e_1\neq1$ use $R_-(u)D$, where $R_-$ is the same formula with $-e_1$ in place of $e_1$, and
    $D\in SO(N)$ is fixed with $De_1=-e_1$.
  - The coset average over $\{R\in O(N):Re_1=\psi_0\}$ of the transformed integrand is independent of
    the section, by invariance of Haar measure on the stabilizer $O_{e_1}(N)$ and of the characteristic
    functions. Hence it equals the expression with $R(\psi_0)$ for either section, and is analytic in
    $\psi_0$ on the union of the two chart domains, i.e. on a complex neighbourhood of the whole
    sphere.
  - This replaces P7's verbal argument (pp. 520–521 [checked]). The review checked the rotation
    numerically (LFR-18).
- (M5) *Lemma 2.5 in full* (the new characteristic functions imply the old ones), modelled on E9
  (1.29), (1.89) [review] and D2 Lemma 3.13 [review]. Its proof (pp. 512–516) uses no chains: only
  $\chi''$ (2.61), Lemma 2.2, P3 Prop 2.1, and a scale-$k$ segment to $\partial(Z_0^c\cap T_1^{(k)})$. Its one
  shape input, "$\square^{\sim3}\cap U^{\sim3}_{k_1}\ne\varnothing$ implies $j=k_1$", follows from P7 (2.1) for any core
  (R3-14 (a)).
- (M6) *Polymer expansion* (3.26)–(3.28), via PE with connectivity modulo $\Omega_k^c\cap Y_k$ and the
  activity lemma for non-small boundary terms (roadmap §5.2). The abstract expansion is landed in Lean,
  with no `sorry`:
  - `pe_xi_eq_exp` (`Balaban/Polymer/PE.lean`): $\Xi=\exp(\text{log series})$ under the KP condition;
  - `pe_PY_bound` (`Local.lean`): $\sum_{Y\ni b}|P(Y)|e^{g(Y)}\le\sum_x\kappa_xe^{a_x}$ for subadditive weights $g$;
  - `pe_lattice` and `pe_blockTorus` (`Lattice.lean`, `BlockTorus.lean`): the lattice corollary with
    $\|K(X)\|\le\varepsilon e^{-\kappa|X|}$, local terms with $\sum_{Y\ni b}|P(Y)|e^{\kappa'|Y|}\le\alpha$, and
    $e^{-|B|\alpha}\le|\Xi|\le e^{|B|\alpha}$, block degree $\Delta=2d$;
  - analyticity of the log series and of each $P(Y)$ in parameters: `pe_analyticOnNhd`,
    `pe_PY_analyticOnNhd` (`Holomorphic.lean`);
  - `pe_hole` (`Hole.lean`, commit d665e8d; R3-14 (b)), the version with a hole $S_0$ and decay in the
    Steiner size outside it, which (3.26)–(3.28) need.
- (M7) *Late scales.* P7's $k_2,k_3$, $Z_0$ and $Z'''_0$ are taken as printed, with
  $\mathrm{diam}_k(Z_0)<D_0:=3c_0+4$ instead of 15. Lemma 2.1's constants $c_{11},K_6$ are those for size
  $D_0$ (LFR-09; §5 rows 4 and 7). The other constants of P7 that come from the single-box size become
  $C(c_0)$ times the printed ones (R2-04, R3-04):
  - $30(d-1)\cdot3\delta_k$ in (2.20) (p. 503), hence $90d\delta_k$ in (2.28);
  - $7K_6$ and $90d$ in the proof of Lemma 2.5 (p. 515);
  - the segment of length $<6M[R_{k-1}]$ after (2.18) (p. 502), now $<\frac12M\mathrm{crit}_k+3M$;
  - the segment $<6MR_{k+1}$ before (2.27) (p. 504), now $<\frac12M\mathrm{crit}_k+3M$;
  - $|z-z_0|\le7$ in (3.11) (p. 522), now $\le D_0$, so that $21K_6$ becomes $3D_0K_6$.

  All of them are $O(c_0MR_k)$ or $O(D_0)$. They are absorbed by the factors $L^{-n_1/3}$ in
  (2.27)–(2.30), where the conditions on $n_1$ now read $L^{n_1/3}\ge C(c_0)K_1MR_{k_1}$, and by $\beta$
  large.

*Status:* sketched in P7 for single-box windows; (M1)–(M7) reconstructed.

**LF-5 (regime $k_0\le k<k_f$; P5/P6 Thm 4 repaired).** $\mathcal R_{k_0}\subset\mathcal R^\flat_{k_0}$, and for
$k_0\le k<k_f$, $S^{(k)}T^{(k)}$ maps $\mathcal R^\flat_k$ into $\mathcal R^\flat_{k+1}$ (with $BL^{d-2}$). Consequently
$\sum_{\mathbb A\cap Z}\int|\mathbb T_kF|\le e^{-p_2(\beta_{k_0})-H_k|Z|_k}\sup\chi|F|$ for $k_0\le k\le k_f$.
- The step $k=k_0$ includes the switch from incomplete to complete backgrounds (P5 p. 490 [checked];
  P6 p. 11 suggests two sub-steps, to be written).
- In the frozen regime there are no window states and no hulls. Components may wind on small tori;
  the spine bookkeeping of §4.2–§4.3 holds on tori.

*Sketch:* the analytic part is P6's proof of Thm 4 (p. 21 [checked]). The bound is LF-2 (iv), which
replaces the failing chain of P6 p. 22 (§4.8).

**LF-6 (base case, hard spins; reconstructed).** If $k_f\ge1$, then $\rho_1:=S^{(0)}T^{(0)}\rho_0$ has a
representation (D1) with histories generated by the *base rule* below, and $\rho_1\in\mathcal R_1$ if
$k_0\ge1$, $\rho_1\in\mathcal R^\flat_1$ with threshold $p_2(\beta)$ if $k_0\le0$. The small-field data at $k=1$
satisfy P4 (H.1)–(H.7) with constants independent of $\beta$.
*Base rule and sketch.*
(i) Decomposition of unity on the unit lattice (structure of E8 §1 (1.1)–(1.30), details of D2 §3.4
(228)–(231) [review]): per cube of $\pi_1$, the small-field conditions $|\psi(y)-Q\varphi(y)|<(\beta a)^{-1/2}p_0(\beta)$
on blocks and $|\partial\varphi(b)|<\beta^{-1/2}p_0(\beta)$ on bonds (P5 p. 487 [checked]); if $k_0\le0$ also
$|\varphi_x-h|<(\beta\nu)^{-1/2}p_0(\beta)$. No condition on $|\varphi|$ (hard spins; D2's $|\Phi_0|$ condition
is dropped).
(ii) Each large-field cube gains $\exp(-cp_0(\beta)^2)$ from the Gaussian kernel of $T^{(0)}$ or from the
Gibbs factor, using half of each exponent for the gain and half for integrability (D3 Lemmas 11,
13 [review]); so $A_3\le cA_0^2$ works at $k=0$.
(iii) Regions $\Omega'_1,\Omega_1,\Omega''_1,Z_1$ by the step rules with $Z_0=\emptyset$; $\kappa_0=0$,
$C=1$, $\mathcal B^{(0)}=0$; $\mathbb T_1$, $\kappa_1$, $C(\mathbb A_1)$, $\mathcal B^{(1)}$ are the first instance of
§3.3–3.4.
(iv) Small-field part: P4 (2.42)–(2.50) at $\lambda_0=\infty$ written in a chart of the sphere. The
background $\phi_1(\psi)$ is the constrained minimizer (P2 Prop 1.1 at $\lambda=\infty$, I-1). The fluctuation
is written in the tangent chart $\varphi_x=(1-|\xi_x|^2)^{1/2}\phi_1(x)+\xi_x$, $\xi_x\perp\phi_1(x)$,
$d\sigma(\varphi_x)=(1-|\xi_x|^2)^{-1/2}d^{N-1}\xi_x$. To avoid a basis of $\phi_1(x)^\perp$ (and hence local
sections), use, for unit $\phi$, $\int_{\phi^\perp}f(\xi)\,d^{N-1}\xi=(2\pi)^{-1/2}\int_{\mathbb R^N}f(P^\perp_\phi u)e^{-\frac12(\phi\cdot u)^2}du$
with $P^\perp_\phi=I-\phi\phi^\top/(\phi\cdot\phi)$, which is analytic in $\phi$ near the real sphere. Then the
lower bound on the fluctuation form (P4 (2.48)–(2.50): $G_1^{-1}(\alpha_1)\ge\gamma_0$; at $\lambda=\infty$
the form $P^\perp G_1^{-1}P^\perp+P$, roadmap C8) and I-8 at $k=0$ give $\mathcal E^{(1)},\mathcal M^{(1)}$.
(v) Budgets and windows: $Z_0=\varnothing$, and each component of $Z_1$ is a (T2) event with no old
parts. It is Pre, or $\mathsf{Active}(1,1,\varnothing)$ if its spine is a point; LF-2 (iii).
*Status:* reconstructed (ER-062, ER-063).

**LF-7 (the flow; P7 Thm 5, method form).** For $\beta\ge\beta_0$, $\nu\in(0,1]$ with $k_f\ge1$, unit $h$: the
densities $\rho_1$ (LF-6), $\rho_{k+1}=R^{(k+1)}S^{(k)}T^{(k)}\rho_k$ ($1\le k<k_0$, LF-3, LF-4) and
$\rho_{k+1}=S^{(k)}T^{(k)}\rho_k$ ($k_0\le k<k_f$, LF-5) are well defined, $\rho_k\in\mathcal R_k$ for $k\le k_0$,
$\rho_k\in\mathcal R^\flat_k$ for $k_0\le k\le k_f$, with $\beta_k>BL^{k(d-2)}$, and $\int\rho_k\,d\psi_k=c_kZ(g)$ with
$c_k>0$ independent of $g$. *Sketch:* induction on $k$; the running constants are those of one
global solution of the RG equations (I-7, P4 Prop 5.1) with the bounds of P4 (H.6); normalization
from $\int T\rho=\int\rho$ and LF-4 (a).

**LF-8 (last step; P7 §4, P9 §4).** (a) If $k:=k_f\ge1$ and $\rho_k\in\mathcal R^\flat_k$, then
$$\int\rho_k\,d\psi_k=\exp\Big[-E_{k+1,0}|T^{(k+1)}|+\mathcal F_{k+1,0}(h,g)+\mathcal R^{(k+1)}(h,g)\Big],$$
with $\mathcal F_{k+1,0}$ as in P7 (4.17) [checked] and
$\mathcal R^{(k+1)}=\sum_{n\le m}\mathcal R^{(k+1)}_n+\mathcal P^{(k+1)}$, $\mathcal P^{(k+1)}=\sum_{X\in\mathcal D_{k+1}}\mathcal P^{(k+1)}(X;h,g)$,
$|\mathcal P^{(k+1)}(X)|\le\frac12\beta_k^{-m-1}e^{-\kappa d_{k+1}(X)}$ (P7 (4.14) [checked]; P9 (4.6) [checked]
gives $\beta_k^{-2}e^{-2\kappa d}$), all terms localized, analytic on $\|g\|_{\ell^1}<1$, torus independent.
(b) ($k_f=0$.) If $\nu>\frac78L^{-2}$ the same representation holds for $\int\rho_0$ with scale-1
polymers.
*Sketch of (a)* (LFR-12). P7 (4.1)–(4.8) and P4 §6 unchanged. The large-field operators enter
through P7 (4.9)–(4.10), used with $e^{-p_2(\beta_{k_0})-H_k|Z|}$, which is (H6♭) via LF-5. The Mayer
expansion (4.11) and the bounds (4.12)–(4.13) need $\varepsilon^{-2}e^{-p_2(\beta_{k_0})}\le\frac12\beta_{k_f}^{-m-1}$,
true for $\beta\ge\beta_0$ because $\lambda_{k_f}\le\frac d2\lambda_{k_0}+c_d$ (§4.7–4.8). The sum over large-field
configurations and the exponentiation (4.14) are one application of PE with volume weights
(POLYMER §3.6): activities bounded by $e^{-p_2(\beta_{k_0})-H_k|Z|}\times$ (the boundary factors), and the
volume weight $e^{H_k|Z|}$ absorbs $E_{k+1,0}|Z|+\varepsilon^{-2}B_0K_0M^{-d}|Z|$ ((4.12), §5 row 13). In Lean this is
`pe_lattice` / `pe_blockTorus` for the weighted local bound, `pe_PY_bound` for the volume weights,
and `pe_PY_analyticOnNhd` for analyticity in $(h,g)$; the version with holes (`pe_hole`) is needed if
the expansion is done modulo $\Omega^c$. No loss bookkeeping of D3 Lemma 15 is needed: the losses are
already in $G$, and only the geometry of D3 Lemma 14 (volume of large-field regions in terms of
their creation sets) may be used. Status: sketched in P7 (details "postponed" to P9, p. 533
[checked]); PE proved in Lean.
*Sketch of (b):* decomposition of unity on $\rho_0$ with $|\partial\varphi|<\beta^{-1/2}p_0$,
$|\varphi-h|<(\beta\nu)^{-1/2}p_0$; since $\beta\nu\ge\frac78L^{-2}\beta$ the small-field part is a massive
perturbation of the product measure around $h$ (sphere chart of LF-6 (iv)), and one application of
PE (`pe_blockTorus`) with activities $e^{-cp_0^2}$ per large-field cube concludes. *Status:* (b)
reconstructed.

**Lemma G (region calculus; reconstructed).** The axioms (G1)–(G2) of §4.1 hold for the domains of
§3.2, on the torus. The radii $s_*r_k$ and $s'r_k$ are computed from P5 (2.2)–(2.9), (2.45) and P6 (2.3),
(3.14) [checked (3.14): $S(Z)\subset Z^{\sim4L[R_k]}$]; since $R_k\le\hat R_k$ they hold with $r_k=\lceil\hat R_k\rceil$.
Moreover:
- the canonical hull rule terminates and is deterministic (§3.5), and Lemma C4 and Lemma C hold;
- the removal overwrite of §3.2 keeps $\mathbb B_k$ a generating set with separation $\varrho$;
- (R3-14 (e)) P7's generating set $\mathbb B_{k_1,k}$ of (2.13) [checked] satisfies P2 (1.1)–(1.3) for a
  multi-box core, as P3 Prop 2.1 needs in (2.49)′. The pieces $\mathbb B_{k_1}(W_{k_1})\cap Z_{k_1}$ live on
  disjoint core boxes whose $U^{\sim4}$ are disjoint (§3.1), so the check is the single-box one, made
  box by box.

Lemma G is a list of inclusions between neighbourhoods. The care needed is that each of these sets is
a union of neighbourhoods of *seeds* (old regions and new large-field cubes), rounded to
$\pi'_{k+1}$-cubes, so that every cube of a new component lies in the neighbourhood of a seed in the
same component. The review rechecked this structure (its §1.1, with $s_*\approx4$ and $R_0\ge C(L)$
absorbing the additive $O(L^2)$ terms). Components are the classes of the relation $d<\omega_k$ (§3.1).
Paths, enclosure and the chains of Lemma CH use nearest-neighbour adjacency, and Lemma S uses
$*$-adjacency, which $\omega$-separated sets satisfy.

*Lemma S (lattice separation; R2-02).* Let $d\ge2$ and let $A_1,\dots,A_n\subset\mathbb Z^d$ be finite and
pairwise $*$-separated: there are no $a\in A_i$, $a'\in A_j$, $i\ne j$, with $|a-a'|_\infty\le1$. Say that
$x\notin A:=\bigcup_iA_i$ is *enclosed* by $A$ if every nearest-neighbour path from $x$ to infinity meets
$A$. If $x$ is enclosed by $A$, then it is enclosed by a single $A_{i_0}$. In particular, a union of
pairwise $*$-separated boxes encloses no point outside it.

*Proof.* Let $C$ be the nearest-neighbour component of $\mathbb Z^d\setminus A$ containing $x$; it is finite.
Let $\partial^{\rm ext}C$ be the set of $y\notin C$ that are nearest-neighbour adjacent to $C$ and joined
to infinity by a nearest-neighbour path avoiding $C$.
- For a finite nearest-neighbour connected set in $\mathbb Z^d$, $d\ge2$, this exterior boundary is
  $*$-connected. This is Timár, Proc. AMS 141 (2013) 475–480, Lemma 2; Deuschel–Pisztora 1996,
  Lemma 2.1 has a stronger form. It is external and standard, and not in the source library;
  COUNTING-astra verified Timár's text.
- Every neighbour of $C$ outside $C$ lies in $A$, by maximality of $C$, so $\partial^{\rm ext}C\subset A$. Being
  $*$-connected, and the $A_i$ being pairwise $*$-separated, it lies in one $A_{i_0}$.
- A nearest-neighbour path from $x$ to infinity, after its last visit to $C$, steps into
  $\partial^{\rm ext}C\subset A_{i_0}$.
- For a box: its complement is nearest-neighbour connected and unbounded, so it encloses nothing.
  $\square$

On the torus the lemma is applied to sets contained in a small set (§3.1), lifted to $\mathbb Z^d$. For
$k\le k_0$ every set to which it is applied lies in one component of a window. Such a component has
diameter $\le\nu_{\max}(k)(\mathrm{crit}_k+\omega_k)=O(\hat\lambda_k^{p_2+2})$, which is far below $n_k/4$ by (3.0)
(R3-03 (v), R3-05).

**Lemma F (support and factorization; R3-01).** For every admissible history, every component $Z$ of
$Z_k$ and every $\mathfrak a\in\mathfrak H_k(Z)$:
- the kernel of $\mathbb T_k(Z,\mathfrak a)$ depends only on the variables on $U^\sim$, $U=Z^\approx$;
- if $Z',Z''$ are distinct components, then $\mathbb T_k(Z'\cup Z'',\cdot)=\mathbb T_k(Z',\cdot)\mathbb T_k(Z'',\cdot)$, and the
  two factors commute.

*Source and proof.* The support property is asserted for the one-step operator in P6 p. 16 [checked]:
"its kernel depends on $\psi_{k+1},\psi_k,\psi'_k$ restricted to $U^\sim_{k+1}$". It propagates through the
recursion (3.3), and through $R$, whose new characteristic functions live on $U^{\sim9}_{k_1}$ of the core.
That set lies in $\Omega_{k_1}\cap\Omega^c_{k_1+1}$ near the core (P7 p. 503 [checked]; P7 (2.1)), hence in the lineage, hence in $Z$.
The factorization then follows as in P5 p. 493 [checked], since $U'^\sim\cap U''^\sim=\varnothing$ for
$\omega$-separated components (§3.1).

UNCERTAIN: whether the backgrounds $\phi_{k+1}(\mathbb B_{k+1}(\partial\Omega_{k+1});\tilde\psi)$ in the main actions of
P5 (2.47) and P6 (3.2) are functions of the variables on $U^\sim$ only, as P6 p. 16 asserts, or only up
to exponentially small terms. P6 (2.15)–(2.17) move terms of that second kind into the boundary terms.
If only the second holds, the reconstruction document defines the operators with the backgrounds of
the variational problem localized to $U^\sim$ (a definition choice) and moves the difference into
$\mathcal B$ as P6 (2.15)–(2.17) do. Confidence in Lemma F, in one of these two forms: 85%.

### 3.8 LF-4 in detail: $R$ on covered windows

**Hypotheses (RQ).** $Z$ is a ripe component at scale $k\le k_0$: it is $\mathsf{Active}(q,\nu,\mathcal M)$ with
$t^*(Z)=k$. P7's $k_1$ is fixed by (2.31) as the largest index with $(k-k_1)\log L>\alpha^{-1}\lambda_{k_1}$. Here it
is replaced by $k_1=k_1(k)$ of §3.1, built on $\hat\lambda\ge\lambda$, which satisfies (2.31)'s inequality; by
Lemma C (f4), $k_1=q$. Lemma C then gives:
- (RQ1) there are no new large fields in the lineage on $[k_1,k]$;
- (RQ2) for $j\in[k_1,k]$ the lineage $Z_j\cap Z$ is covered by $\nu\le\nu_{\max}(k)$ boxes of side $\le\mathrm{crit}_j$;
- (RQ3) $Z_j\cap Z$ is one box of side $\le\mathrm{crit}_j$ for $j\in[s,k]$, and $k-s\ge n_2(s)$. Since
  $L^{n_2(s)}>LM\,\mathrm{crit}_s>LM[R_s]$, P7's $k_2$ (the smallest $j$ with $L^{-(k-j)}LM[R_j]\ge1$) exceeds $s$, so
  $[k_2,k]\subset[s,k]$;
- (RQ4) $\lambda_k\le c_*\lambda_{k_1}+C$ with $c_*=1+\theta/(\alpha\log L)$;
- (RQ5) at scale $k_1$ the lineage, i.e. the *core* $Z_{k_1}\cap Z$, is a union of single boxes of side
  $\le\mathrm{crit}_{k_1}$, pairwise $\omega_{k_1}$-separated (Lemma C (e4)). Hence their neighbourhoods $U^{\sim4}$ are
  pairwise disjoint (§3.1).

Write $h:=h_k$ (§3.1); $\hat W\le C_{\hat W}\hat\lambda_k^{w_0}$ is defined in Lemma CH (Step 3). All constants
$C,C',\dots$ below depend only on constants fixed before $\beta$ (§5).

**Step 0: composition and core.** P7 (2.6)–(2.9) hold as printed for any lineage. The operator is
$\mathbb T_k(Z)=\mathbb T_{k,k_1}(Z,Z_{k_1}\cap Z)\,\mathbb T_{k_1}(Z_{k_1}\cap Z)\exp\sum\mathcal B^{(j)}$.
- $\mathbb T_{k_1}(Z_{k_1}\cap Z)$ is the product over the core boxes, by Lemma F: the core boxes are distinct
  components at scale $k_1$, $\omega_{k_1}$-separated (R3-01).
- The composition of the renormalization transformations is P2 Lemma 4.1 for the generating sets
  $(\mathbb B_k\cap Z^c_{k_1})\cup(T^{(k_1)}\cap Z_{k_1})$ and $T^{(k)}_1$, which needs no shape assumption.
- The *core* is $Z_{k_1}\cap Z$, with $U_{k_1}=(Z_{k_1}\cap Z)^\approx$ (P7's convention $Z_k=Z$, p. 498 [checked]; Lemma L).

**Step 1: renormalization of the actions, (2.10)–(2.15).** The bounds (2.11) are per unit of new
volume, so the first inequality of (2.15) holds as printed:
$$|C_{k_1,k}(Z^c_{k_1}\cap Z_k,\mathbb B_k;\psi)|<C_{15}\sum_{j=k_1}^{k-1}|Z^c_j\cap Z_{j+1}\cap Z|_\xi .\tag{2.15′}$$
P7's second inequality, $<\mathrm{const}\,M^dR_0^d\lambda_{k-1}^{2d+1}$, uses $|Z_{j+1}|_\xi<(12LM[R_j])^d$ and is
not used; (2.15′) is paid by the refund (Step 6).

**Step 2: late scales.** (2.2)–(2.5), (2.17)–(2.20), (2.27)–(2.28), Lemma 2.1, Lemma 2.2 and (3.1)–(3.6)
use only scales in $[k_2,k]$ and hold by (RQ3), with $\mathrm{diam}_k(Z_0)<D_0$, the constants $C(c_0)$ of (M7)
(R2-04, R3-04), and $|Z_0|\le D_0^d$ in (3.4)–(3.5).

**Step 3: chains, exposure and the core.** Call a point $y$ of a window layer $\Lambda_j\cap Z$
($k_1\le j<k$) *exposed* if it is joined to $\Omega_k\cap Z$ by a nearest-neighbour path avoiding the core
$Z_{k_1}\cap Z$ (as fine-scale sets), and *enclosed* otherwise.

*All window points are exposed* (version 3).
- By (RQ5) and Lemma S, the core encloses no point outside it.
- A window point $y$ lies in $Z$ (a box at scale $k$) outside the core. A path from $y$ to infinity
  that avoids the core leaves $Z$ through its outer shell.
- The outer shell of $Z$ lies in $\Omega_k$, because $Z_k$ contains the neighbourhood of width
  $2MR_{k-1}+M$ of $\Omega''^c_k\supset\Omega^c_k$ (P6 (2.3)).
- The part of the path before it leaves $Z$ joins $y$ to $\Omega_k\cap Z$.

Version 3 also claimed a per-box path for (3.11)′ from this. That argument was wrong for close
boxes (C-03, R3-02). It is replaced by Lemma L below.

*Lemma CH (chain lemma).* For every window point $y\in\Lambda_j\cap Z$ there are points
$y=x_0,x_1,\dots,x_p=y_k\in\partial\Lambda_k$ with the following property: consecutive points are joined either
by a lattice segment inside one layer $\Lambda_i$ with $i\ge\max(k_1,j-h)$, or by a cross-layer bond. On
every configuration satisfying the bounds (2.22) with a constant $c$,
$$|\tilde\psi(y)-\psi_k(y_k)|\ <\ \hat W\,c\,\delta_j .\tag{2.26′}$$

*Proof plan.*
- (a) *Enclosure bound, one component at a time* (R2-02).
  - For $i\in[k_1,j]$, let the *obstacle at scale $i$* be $O_i:=(\Omega^c_i\cup Z_{k_1})\cap Z$: the
    fine-scale points of $Z$ not available to layers of scale $\ge i$, in the generating set
    overwritten by removals (§3.2).
  - Since $\Omega^c_i\subset Z_i$ and $Z_{k_1}\subset Z_i$, $O_i$ lies in the lineage at scale $i$, and each
    $*$-component of $O_i$ lies in one component of the lineage at scale $i$.
  - By Lemma C (b), such a lineage component is covered by at most $\nu$ boxes of side $\le\mathrm{crit}_i$
    that are chained at gaps $<\omega_i$. Its diameter is therefore at most $\nu(\mathrm{crit}_i+\omega_i)$
    cubes of $\pi_i$, i.e. at most $\nu M(\mathrm{crit}_i+\omega_i)$ units of scale $i$.
  - Suppose the block of $y$ (side $L^{j-i}$ units of scale $i$) is enclosed by $O_i$. By Lemma S it is
    then enclosed by one $*$-component of $O_i$, whose diameter must exceed $L^{j-i}$. (The exterior
    boundary of a finite set containing a block of side $s$ has sup-diameter $\ge s+1$, by its extreme
    points in each coordinate; R3-03 (iv).) Hence $L^{j-i}<\nu M(\mathrm{crit}_i+\omega_i)$, i.e.
    $j-i\le h-2$.
  - Points outside $Z$ play no role: the path only has to reach the outer shell of $Z$, and other
    components are disjoint from $Z$.
  - At $i=k_1$ the obstacle is the core, which encloses nothing (exposure). So with
    $i_0:=\max(k_1,j-h+1)$, $y$ is joined to $\Omega_k\cap Z$ by a path avoiding $O_{i_0}$, i.e. inside
    $\bigcup_{i'\ge i_0}\Lambda_{i'}\cup(\Omega_k\cap Z)$.
- (b) *Length.* Take such a path, converted into a chain in the multiscale graph of $\mathbb B_k$ and made
  self-avoiding in that graph (R3-03 (i)). Its part in $\Lambda_{i'}$ lies in $\Omega^c_{i'+1}\subset Z_{i'+1}\cap Z$,
  which by (RQ2) has at most $\nu(LM\mathrm{crit}_{i'+1})^d$ lattice points of scale $i'$.
- (c) *Cost.* Each bond in $\Lambda_{i'}$ costs $c\delta_{i'}$, and each cross-layer bond $dLc\delta_{i'}$ ((2.22)).
  - The separation of the generating set (P2 (1.1)–(1.3); Lean `GeneratingSet.separation`) lets only
    adjacent layers meet. Where the block $B(b_-)$ required by (2.22) is not contained in $\Lambda_j$ (at
    corners of a non-convex layer), a detour of at most one block inside $\Lambda_j$ costs at most $2dLc\delta_j$
    (R3-03 (ii)).
  - By P7 (2.25), $\sum_{i'\ge i_0}\delta_{i'}\le4\delta_{i_0}$, and
    $\delta_{i_0}\le L^{\frac{d-2}2(j-i_0)}\delta_j\le L^{\frac{d-2}2h}\delta_j$, with $L^h\le L^3\cdot2\sqrt d\,\nu_{\max}(k)M(\mathrm{crit}_k+\omega_k)$.
  - Summing gives (2.26′) with
    $$\hat W:=C_{\rm ch}\,\nu_{\max}(k)\,(LM\mathrm{crit}_k)^d\,\big(2\sqrt d\,\nu_{\max}(k)M(\mathrm{crit}_k+\omega_k)\big)^{\frac{d-2}2}L^{\frac{3(d-2)}2}\ \le\ C_{\hat W}\hat\lambda_k^{w_0},$$
    since the exponent is $p_2+2d+\frac{(p_2+2)(d-2)}2=\frac{p_2d}2+3d-2\le w_0$.
  - For boxes ($\nu=1$) this reduces to P7's chain with $16LMR_{k_1}$ replaced by $\hat W$. $\square$

The proof plan still has to be written out in the reconstruction document. Its outline items are
R3-03 (i)–(v): the conversion to a chain, the corner detour, the overwritten generating set, the
exterior-boundary diameter, and the lift (the last by §3.7, Lemma S).

*Lemma P (component-wide path; REPAIRS-astra §C.1, checked).* Let $A=\bigcup_{i=1}^{N}B_i$ be a union of
pairwise $*$-separated boxes of side $\le b$ ($\pi_q$-cube units) in a small region of $\mathbb T_q$. Put
$a=[R_{q-1}]+1$, $U=A^{\sim a}$, $W=(A^c)^{\sim2a}$, $D=U^{\sim3}$. For $x\in\mathbb B_q(W)\cap D$, let $\mathcal C$ be
the nearest-neighbour component of $D$ containing $x$, and $N_{\mathcal C}$ the number of boxes whose
$(a+3)$-neighbourhood lies in $\mathcal C$. Then there is a nearest-neighbour path from $x$ to $D^c$ with all
sites and bonds in $W^{\sim1}\cap U^{\sim4}$ and length $\le C_dN_{\mathcal C}M(b+a+5)$.

*Proof* (REPAIRS-astra's, checked).
- First go from $x$ along a shortest path to $A^c$ (distance $\le M(2a+2)$); the distance to $A^c$
  decreases along it, so the path stays in $W$.
- Then, in a two-dimensional coordinate slice, follow a ray, detouring around each box section it
  meets along the one-site outer boundary of that section. The detour avoids the other sections,
  since the sections are $*$-separated by at least $M$ sites.
- Stop at the first exit from $D$. Every site before the exit lies in $A^c\cap D\subset W\cap U^{\sim4}$.
- The horizontal travel is at most the diameter of $\mathcal C$, which is $\le N_{\mathcal C}M(b+2a+6)$, and
  each box costs one detour of $\le2Mb+O(M)$ steps. $\square$

**Lemma L (localization at the core; the open item of C.1, R3-01, R3-02).** Let $Z$ be ripe at scale $k$
with core $k_1=q$. Let $B$ be a core box (a component of $Z_{k_1}$ in the lineage). Write $U^B:=B^\approx$,
$W^B:=(B^c)^{\approx2}$, and $U,W$ for the global sets of P5 (1.4) built from $Z_{k_1}$. Then:
- (a) On $(U^B)^{\sim4}$ the global and local sets agree. Precisely: $U^{\sim n}\cap(U^B)^{\sim4}=(U^B)^{\sim n}\cap(U^B)^{\sim4}$
  for $n\le4$, $W\cap(U^B)^{\sim4}=W^B\cap(U^B)^{\sim4}$, and the sets $(U^{B'})^{\sim4}$ for distinct core boxes and
  for the other components of $Z_{k_1}$ are pairwise disjoint.
- (b) In the localized operator of $Z$, the characteristic functions $\chi_{k_1}(Z^c_{k_1}\cap U_{k_1})$ and
  $\chi'_{k_1,\frac12}(U^c_{k_1}\cap U^{\sim6}_{k_1})$ of (3.7), and the domain (1.24) of $\mathbb T_{k_1}(Z_{k_1}\cap Z)$, restricted
  to $(U^B)^{\sim4}$, are exactly the single-box objects of P7 for the box $B$.
- (c) Consequently P7 (3.11) holds for every $x\in\mathbb B_{k_1}(W_{k_1})\cap U^{\sim3}_{k_1}$ as printed: there is a
  straight path of length $\le3MR_{k_1}+8M$ inside $W^\sim\cap U^{\sim4}$ to a point of $(U^{\sim3}_{k_1})^c$, where the
  rotated $\psi'_{k_1}=e_1$. Hence
  $$|R(\psi_0)\tilde\psi_{k_1}(x)-\psi^0_{k_1,k}(x)|<10MR_{k_1}\delta_{k_1}\quad\text{on }\mathbb B_{k_1}(W_{k_1})\cap U^{\sim3}_{k_1},$$
  with the scale-$k$ terms changed as in (M7).

*Proof.*
- (a) Distinct components of $Z_{k_1}$ are $\omega_{k_1}$-separated (§3.1), and
  $(U^B)^{\sim4}=B^{\sim([R_{k_1-1}]+5)}$. The neighbourhoods $(U^{B'})^{\sim4}$ are then pairwise disjoint,
  since $2([R]+5)<\omega$. A cube of $(U^B)^{\sim4}$ is at distance $\ge\omega-([R]+5)>[R]+5$ from every other
  component, so its distances to $Z_{k_1}$ and to $Z^c_{k_1}$ are its distances to $B$ and to $B^c$. Hence
  the global $U^{\sim n}$ ($n\le4$) and $W$ agree with the local ones there.
- (b), the factor $\chi_{k_1}(Z^c_{k_1}\cap U_{k_1})$. It is the part, inside $U$, of the factor
  $\chi_j(Z^c_j\cap(\Omega^{\sim3}_{j+1})^c)$ of P7 (2.6) at $j=k_1$. This applies because $U_{k_1}$ lies in
  $\Omega^c_{k_1+1}$ with margin $\ge4+[R_{k_1}]$ (P7 (2.1) [checked]).
  - It is a product over cubes (P5 (1.18)), each factor depending on $\psi_{k_1}$ and
    $\phi_{k_1}(\mathbb B_{k_1}(\square^{\sim2});\tilde\psi)$ on $\square^{\sim2}$ (P5 (1.19) [checked]).
  - The cubes in $(U^B)^{\sim4}$ belong to the lineage component of $B$ at scale $k_1+1$, hence to $Z$'s
    localized operator, by Lemma F.
- (b), the factor $\chi'_{k_1,\frac12}$. It is defined by $R$ itself (P7 (2.21) [checked]), so we define it
  with the local $U$. On $(U^B)^{\sim4}$ the two agree by (a). The ring functions of distinct boxes of
  the same $Z$ use the same $\psi_0$ (one per component $Z$ of $Z_k$, P7 (2.19)), so their overlap
  outside $(U^B)^{\sim4}$ is harmless.
- (b), the domain. $\mathbb T_{k_1}(Z_{k_1}\cap Z)=\prod_{B'}\mathbb T_{k_1}(B')$ by Lemma F, so its domain (1.24) is the
  product of the single-box domains.
- (c) $x$ lies in $(U^B)^{\sim3}$ for exactly one core box $B$, by (a). P7's argument on p. 522 [checked]
  uses only the objects in (b) on $(U^B)^{\sim4}$:
  - from $x$, which is within $2a$ cubes of $B^c$, go straight through the nearest face of $B$ and on to
    $((U^B)^{\sim3})^c$;
  - the segment stays in $W^\sim\cap(U^B)^{\sim4}$, and has length $\le M(2a+(a+3)+2)=M(3[R_{k_1-1}]+8)\le3MR_{k_1}+8M$, where $a=[R_{k_1-1}]+1$;
  - its endpoint lies outside every $(U^{B'})^{\sim3}$, hence in $(U^{\sim3}_{k_1})^c$.
  - This is Lemma P with $N_{\mathcal C}=1$. $\square$

*Status of (3.11)′.* Proved, conditional on Lemma F. With Lemma L, the version-3 constant
"$\hat W\delta_{k_1}$" in (3.11)′ is no longer needed; P7's $10MR_{k_1}\delta_{k_1}$ holds. Lemma P is not used
under the $\omega$-separation. It is kept, checked, as the statement needed if $\omega_k$ were ever
reduced below $2[R_{k-1}]+11$: then $N_{\mathcal C}\le\nu$, and the path length
$C\nu M\mathrm{crit}=O(\hat\lambda^{p_2+2})$ is absorbed by $\hat W$, since $w_0-(p_2+2)=\frac12p_2(d-2)+3d-2>0$ (REPAIRS-astra
(C.4)). The open item of REPAIRS-astra §C.1 (localization with the exact characteristic functions) is
thus reduced to Lemma F. Confidence 85%; the risk is the UNCERTAIN in Lemma F.

*Remark (version 2's Lemma H; backup).* Without the merge-free strip, a lineage component at $k_1$
could be a hollow cluster merged shortly before $k_1$, enclosing a region of $Z^c_{k_1}$ that the window
absorbs later. Version 2 stated the needed estimates for such enclosed points as Lemma H and left it
open; versions 3–4 exclude the case by Lemma C (e4).

Plan (H2) is kept as a backup in case the strip should be dropped:
- do not shift the enclosed variables by $\psi^0_{k_1,k}$, keep their original characteristic
  functions, and bound their part of the operator by the step-by-step charges (no refund for their new
  volume);
- the main-action difference is $\ge0$ on real fields, because $\psi^0_{k_1,k}$ is the minimal
  configuration (P7 (2.51));
- on the analyticity domain it is of order $\beta_k\varepsilon_k^2$ times the rescaled volume of the enclosed
  set, $\le C\nu_{\max}^2\mathrm{crit}^{2d}\beta_{k_1}^{-1-2/\alpha}$.

Its unverified step is the analyticity of the composed operator in $\psi_k$ when part of the window is
not shifted.

**Step 4: the re-derived estimates.** Each replaces the printed estimate in P7's argument without
other change.

* (2.29)′–(2.30)′. From (2.26′) with $y$ on the ring $\partial(U^{\sim3}_{k_1}\cap T^{(k_1)})$, together with (2.27) and (2.28)
  with the constants of (M7) (R3-04):
  $$|\psi_{k_1}(y)-\psi_0|<\tfrac12K_1^{-1}\delta_{k_1}\big(2K_1\hat Wc+C(c_0)K_1MR_{k_1}L^{-n_1/3}+C(c_0)K_1L^{-n_1/3}\big)\le\tfrac12K_1^{-1}\delta_{k_1}$$
  if $c=(4K_1\hat W)^{-1}$ and $L^{n_1/3}\ge C(c_0)K_1MR_{k_1}$. This contradicts the third inequality of (2.21).
  The small factor becomes $\exp(-\frac12\gamma_0(4K_1\hat W)^{-2}p_0^2(\beta_{k_1}))$.
* (2.33)′. With (2.32) unchanged ($\lambda_{k_1}/\lambda_k>\alpha/d$, which uses only the window length), the
  factor for a non-empty $Q''_{k_1}$ is at most
  $$\exp\Big(-\frac{\gamma_0\alpha^{2p_0}A_0^2}{32\cdot6^dd^{2p_0}K_1^2C_{\hat W}^2}\lambda_k^{2p_0-2w_0}\,M^{-d}|Q''_{k_1}|_{k_1}+M^{-d}|(Z^c_{k_1})^{\sim3}\cap Z^{\sim3}_{k_1}\cap Z|_{k_1}\Big),$$
  and the ring has $|\cdot|_{k_1}\le C\nu_{\max}(k)(M\mathrm{crit}_{k_1})^{d-1}M\le C'\lambda_k^{p_2+2d-2}$. With $|Q''|_{k_1}\ge M^d$
  and $p_R=2p_0-2w_0>p_2+2d$, this is $\le\exp(-A'_3\lambda_k^{p_R})$. Product-form $C$-factors are not
  needed; MERGES-astra.md needs them because its $N$ is unbounded.
* (2.48)′ (Lemma 2.3). $|\delta\psi|<C_{23}\hat W\delta_j$ on $\mathbb B_{k_1,k}\cap\Lambda_j\cap\Omega^c_{j+1}$, $j=k_1,\dots,k-1$,
  $C_{23}=3dL+1$. Proof as printed (p. 509) with (2.26′) for $c=3dL$ in place of
  $|\tilde\psi(x)-\psi_k(y_k)|<48dL^2MR_j\delta_j$; the other three terms ($4K_1K_6\delta_k$, $45K_6\delta_k$,
  $36dMR_k\delta_k$) are at scale $k$ and unchanged.
* (2.49)′ (Lemma 2.4). The same bounds with $108dK_1K_3K_6L^{\frac{d+2}2}MR_j\delta_j$ replaced by
  $C_{24}L^{\frac{d+2}2}\hat W\delta_j$: P3 Prop 2.1 applies because the numbers $C_{23}\hat W\delta_j$ differ by at most
  $2L^{\frac{d-2}2}$ for consecutive $j$, and $C_{23}\hat W\delta_{k_1}\le C\lambda_k^{w_0+p_0}\beta_{k_1}^{-1/2}<c'_6$.
* (2.59)′.
  $$|\beta_kA^*_{0,k}(Z_{k_1}\cap Z;\phi^0_k)|<(6K_1K_6)^2\beta_k\varepsilon_k^2L^{-n_1d}\,\nu(M\mathrm{crit}_{k_1})^d\le C\nu_{\max}(k)(M\mathrm{crit}_{k_1})^d\beta_{k_1}\varepsilon_{k_1}^2L^{-2(1+\alpha)n_1}\le C'\lambda_{k_1}^{p_2+2d}\varepsilon_0^2\beta_{k_1}^{-1-\frac2\alpha}<1,$$
  using $|Z_{k_1}\cap Z|_{k_1}\le\nu(M\mathrm{crit}_{k_1})^d$ (RQ2), $\beta_k=\beta_{k_1}L^{n_1(d-2)}(1+o(1))$ (P4 (H.6)),
  $\varepsilon_k=\varepsilon_{k_1}L^{-\alpha n_1}$, $\varepsilon_{k_1}\le\varepsilon_0$, $L^{\alpha n_1}>\beta_{k_1}a$ ((2.31)), and (RQ4). The surface term
  on $\mathrm{st}(Z_{k_1})$ is bounded in the same way; the one on $\mathrm{st}(Z_k)$ is unchanged.
* (2.60)′.
  $$\tfrac12\beta_k|\langle\delta\phi_{k_1,k},\alpha^0_k\delta\phi_{k_1,k}\rangle|<\tfrac12\sum_{j=k_1}^k\beta_j\big(C_{24}L^{\frac{d+2}2}\hat W\delta_j\big)^2\,3K_1K_6\delta_k\,L^d\nu(LM\mathrm{crit}_{j+1})^dL^{-2(k-j)}<CA_0^3\nu_{\max}(k)\hat W^2(LM\mathrm{crit}_k)^d\lambda_k^{3p_0}\beta_k^{-1/2}<1,$$
  using $|\Lambda_j\cap Z|_j\le L^d|Z_{j+1}\cap Z|_{j+1}$, $\beta_j\delta_j^2=A_0^2\lambda_j^{2p_0}$, $\delta_k=A_0\beta_k^{-1/2}\lambda_k^{p_0}$ and
  $\sum_jL^{-2(k-j)}\le2$. As in P7, the curly bracket of (2.58) times $\beta_k$ is then bounded below by the
  right side of P6 (3.5) for $X=Z^c_{k_1}\cap Z$ minus 1 (LF-1 holds for arbitrary generating sets).
* (2.61)′–(2.62)′. $\chi''$ as printed. For $\chi''^c$ at a window point $y\in\Lambda_j$, Lemma CH with
  $c=(2\hat W)^{-1}$ gives a bond in some $\Lambda_i$, $i\ge k_1$, with $|\partial\delta\psi|\ge c\delta_{i,1}$; P6 (3.5)
  yields $\exp(-\frac12\gamma_0(2\hat W)^{-2}p_1^2(\beta_i)+1)\le\exp(-A''_3\lambda_k^{p_R})$, using $\lambda_i\ge\lambda_{k_1}\ge\frac\alpha d\lambda_k$ ((2.32)).
* (3.11)′. By Lemma L, $|\delta\psi|<10MR_{k_1}\delta_{k_1}\le\hat W\delta_{k_1}$ on $\mathbb B_{k_1}(W_{k_1})\cap U^{\sim3}_{k_1}$. P7's path of length
  $<3MR_{k_1}+8M$ to $(U^{\sim3}_{k_1})^c$ is used box by box. The terms at scale $k$ are changed as in (M7)
  ($|z-z_0|\le D_0$). $|\delta\psi|<\delta_{j,1}$ on $\Lambda_j$ by $\chi''$. Version 3's per-box length
  $\frac12M\mathrm{crit}_{k_1}+8M$ is deleted (C-03).
* (3.15)′. $|\delta\phi'_{k_1,k}|,L^j\eta|\partial^\eta\delta\phi'|,(L^j\eta)^2|\Delta^\eta\delta\phi'|,(L^j\eta)^2|\delta\alpha'|<C(\hat W\delta_j\varepsilon_k+\varepsilon_j\beta_j^{-1})$ on
  $\Lambda_j\cap\Omega^c_{j+1}\cap Z^c_{k_1}\cap Z$; the real part $\delta\phi_{k_1,k}$ with $C\hat W\delta_j$. Proof as printed (pp. 522–523)
  with (3.11)′ and (2.49)′.
* (3.17)′.
  $$|\beta_k\langle\partial^\eta\delta\phi,\partial^\eta\delta\phi'\rangle|<\sum_{j=k_1}^k\beta_jC^2\hat W\delta_j\big(\hat W\delta_j\varepsilon_k+\varepsilon_j\beta_j^{-1}\big)L^d\nu(LM\mathrm{crit}_{j+1})^d
  \le C'\lambda_k^{a_{17}}\big(n_1\varepsilon_k+\textstyle\sum_j\varepsilon_j\beta_j^{-1/2}\big)\le C''\lambda_{k_1}^{a_{17}+1}\varepsilon_0\beta_{k_1}^{-1/2}\le\beta_{k_1}^{-1/4},$$
  with $a_{17}:=p_2+2w_0+2d+2p_0$, using $\varepsilon_k\le\varepsilon_0(\beta_{k_1}a)^{-1}$ ((2.31)), $\varepsilon_j\beta_j^{-1/2}\le\varepsilon_0\beta_j^{-1/2}$
  (from $\beta_j\varepsilon_j^2=\beta\varepsilon_0^2L^{2\gamma j}$), (RQ4) and $\lambda_{k_1}\ge\lambda_*$.
* (3.18)′. $|\beta_k\delta A'^*_k(Z^c_{k_1}\cap Z,\mathbb B_k)|<6\beta_{k_1}^{-1/4}\le1$: the six quadratic terms are bounded as
  (3.17)′; those quadratic in $\delta\phi'$ are smaller.
* (3.19)′. $|\exp(-\beta_k\delta A^*_k(Z^c_{k_1}\cap Z,\mathbb B_k;\delta\psi,\delta\phi_{k_1,k}))|<e^{3}$ on $\Delta^c_k(U;1,\varepsilon_k)$: the
  real part of the main term is $\ge0$ by (3.16), (3.18)′ bounds the cross terms, and (2.60)′ redone
  with $|(L^j\eta)^2(\alpha^0_k+\nu_k)|\le6K_1K_6\varepsilon_k+(L^j\eta)^2\beta_k^{-1}$ is bounded as in (3.17)′.

So every term of P7 (3.9) other than the window sum is $O(1)$ (at most $4$ in total), as in P7, and
no per-piece accounting of these losses is needed.

**Step 5: Lemma 2.5, Lemma 3.1, the polymer expansion.** As in (M4)–(M6). Lemma 2.5 uses no chains
(R3-14 (a)).

**Step 6: the refund certificate, kept operators and the $R$-rule (M3).** Let
$\mathcal K_{k_1}:=\kappa_{k_1}(Z_{k_1}\cap Z)-\log C(\mathbb A_{k_1}\cap Z)$, summed over the components of the lineage at $k_1$.
By P6 (3.10)–(3.11) over the quiet window, with $\log C^{(j)}\ge0$ for the factors of the quiet steps,
$$G_k(Z)\le\mathcal K_{k_1}-\sum_{j=k_1}^{k-1}(c_1\log\beta_j+c_2)|Z^c_j\cap Z_{j+1}\cap Z|_{j+1}-H_k|Z|_k .$$
P7 obtains the bound of the operator after $R$ from the bound of $\mathbb T_{k_1}$ (p. 519 [checked]: "It is
enough to use the inductive assumption on the operator $\mathbb T_{k_1}$"). This is why (D5) is required at
every scale $j\le k$ (§3.6). Adding the window losses (3.9) gives
$$\text{bound exponent}\ \ge\ \mathcal K_{k_1}-\sum_{j=k_1}^{k-1}(C_{39}\log\beta_j+C'_{39})|Z^c_j\cap Z_{j+1}\cap Z|_{j+1}-L_{\rm res}+\gamma-\log C_{\rm dec}-H_k|Z|_k .$$
- The sum is P7 (3.9) ("$(O(1)\log\beta_j+\mathrm{const.})|Z^c_j\cap Z_{j+1}|_\xi$"), which contains (2.15′).
- $\gamma-\log C_{\rm dec}\ge A'_3\hat\lambda_k^{p_R}$ is the gain of the branch taken in the kept case (§3.4), by
  (2.33)′, (2.62)′, (2.18), (3.20). In the removed case, $\gamma=0$ and $C_{\rm dec}=1$.
- $L_{\rm res}=\frac12N\lambda_k|Z_0|+4+|E_k||Z|\le\frac12ND_0^d\lambda_k+4+(O(1)\lambda_k+C)(M\mathrm{crit}_k)^d\le C_R\hat\lambda_k^{2d+1}$, since $Z$ is a
  single box at scale $k$ (Lemma C (g)).

With $c_1\ge C_{39}$ and $c_2\ge C'_{39}$ (§5 row 14; LFR-02), this proves (D5) for the kept operators of
both kinds with the exponent $\kappa''_k=\kappa_k-C_R\hat\lambda_k^{2d+1}+\gamma$ of §3.4. It also proves the internal
lemma
$$\text{(LF-4R)}\qquad G''_k(Z)\ \ge\ G_k(Z)-C_R\hat\lambda_k^{2d+1}+A'_3\hat\lambda_k^{p_R}\quad\text{(kept)},\tag{Rg}$$
which is the window certificate of MERGES-astra.md (3.6) in budget form. For K1 the operator has not
been normalized, so the $\frac12N\log\beta_k|Z_0|$ term is absent, which only helps; the kept case is P7
p. 520 [checked], "with an additional small factor" (R3-14 (c)).

In the removed case, $G_k\ge\tau_k+1\ge2p_2(\beta_k)+1$ (ripeness, LF-2), and $p_2>2d+1$ gives P7 (3.10):
$\sum\int|\mathbb T''_ke^{E_k|Z|}F|\le e^{-p_2(\beta_k)-H_k|Z|}\sup|F|$, the input of (3.26)–(3.28).

P7's alternative route, bounding all of (3.9) by $C\lambda_k^{2d+2}$, is not available: with $\nu$ pieces the
window sum is of order $\nu_{\max}\lambda^{2d+2}$.

**Status of LF-4.** Steps 0–2 and 5 are as in P7. Lemma C, Lemma C4, Lemma S, Lemma P, Lemma L, Step 4
and Step 6 are reconstructed here at the level of the displayed inequalities. Lemma CH is a proof plan
with the five outline items of R3-03. Lemma F carries the one UNCERTAIN on which (3.11)′ rests. LF-4
stays a draft, not frozen, until Lemma CH, Lemma F and the re-derivations are written at full length
in the reconstruction document (§9).

---
## 4. The step counter (LF-2)

This section proves LF-2 from explicitly listed axioms. The axioms are statements about the region
calculus and the one-step bounds of P5–P7. Their verification from the sources is Lemma G (§3.7),
Lemma C4 and Lemma C (§3.5) and Lemma B (§3.4); the $R$-rule (Rg) is LF-4R (§3.8, Step 6). Everything
else here is elementary. "For $\hat\lambda_0\ge\lambda_*$" means: for $\hat\lambda_0=\log(\beta a)+1$ larger than a
constant depending only on the constants fixed before $\beta$ in §5.

History of the checks:
- The review checked version 1 of this section line by line (its §1; LFR-18), and the re-review
  checked version 2 (R2-10).
- Version 3 added the merge record, the bank and the strip shift. COUNTING-astra checked the bank
  arithmetic and found the transition defects C-01 and C-02.
- Version 4 replaces the window states by the three-way state of §3.5, and §4.5 by REPAIRS-astra
  §B.3. I checked that text and adapted it to the a priori sequence, to $\omega$-components and to tori;
  the changes are listed at the end of §4.5.

### 4.1 Setting and axioms

*Fixed data.*
- Integers $d\ge3$, $L\ge2$, $M\ge1$, and $\alpha\in(0,\frac{d-2}2)$ (LFR-13).
- A sequence $\lambda_k$ ($k\ge0$) with $\theta_-\le\lambda_{k+1}-\lambda_k\le\theta_+$. In the instantiation,
  $\lambda=\hat\lambda$ and $\theta_\pm=\theta=(d-2)\log L$. In this section $\lambda_k$ denotes the bookkeeping
  sequence.
- $r_k=\lceil R_0\lambda_k^2\rceil$, $\rho_k=c_0r_k$, $\mathrm{crit}_k=2\rho_k+10$, $\omega_k=2[R_0\lambda_{k-1}^2]+11$,
  $D_k=\sqrt d(2\rho_k+10+\omega_k)$, and $n_q,n_2,\nu_{\max},k_1,h_j$ as in §3.1.
- Integers $k_0\le\hat k_f$, and cube tori $\mathbb T_k=(\mathbb Z/n_k\mathbb Z)^d$ with $n_k=Ln_{k+1}$
  ($0\le k<\hat k_f$).

Components are taken after $R^{(k)}$ unless said otherwise, and are classes of $d<\omega_k$. The
*seeds* of step $k\to k+1$ are the sets $Z^\uparrow$ ($Z$ a component of $Z_k$) and the cubes
$q\in\mathcal N_{k+1}$. $Z_0=\varnothing$ (C-05).

* **(G1) Attribution.** Before the hull rule, $Z_{k+1}=\bigcup_\sigma B_\sigma$ over the seeds. Each
  $B_\sigma$ is a $*$-connected domain containing $\sigma$, with $B_{Z^\uparrow}\subset N_{s_*r_k}(Z^\uparrow)$ and
  $B_q\subset N_{s'r_k}(q)$; in particular $Z^\uparrow\subset Z_{k+1}$. At $k=0$ there are only the seeds $q\in\mathcal N_1$.
* **(G2) Hull rule.** For $k+1\le k_0$, $Z_{k+1}$ is obtained by the canonical hull rule of §3.5. For
  $k+1>k_0$ there is no hull.
* **(B) Budget recursion.** Lemma B (§3.4), with gain $g_k=\frac12A_3\lambda_k^{2p_0}$ per new cube. It also holds
  at $k=0$, with an empty sum over old components.
* **(Rg) $R$-rule** ($k\le k_0$). $R^{(k)}$ acts exactly on the ripe components (Active, $t^*=k$). Each
  ripe component is either removed, or kept with its domain and spine unchanged, $b=k$, state
  $\mathsf{Active}(k,1,\varnothing)$, and $G_{\rm new}\ge G_k-C_R\lambda_k^{2d+1}+g'_k$ with $g'_k:=A'_3\lambda_k^{p_R}$.
  Non-ripe components and their budgets are not changed by $R^{(k)}$. (LF-4R, §3.8 Step 6; P7 p. 516
  for "nothing has been changed" in the other components [checked].)
* **(K) Constants.** $p_2\ge2d+3$; $p_R=2p_0-2w_0>p_2+2d$; $c_0\in\mathbb N$ with $c_0(1-L^{-1})\ge s_*+1$ and
  $c_0\ge s'+1$; $C_\nu\ge C_r$, where $C_r$ is the constant of (4.4) below.
* **(H-λ) Horizon** (C-04). $\hat k_f-k_0<\lambda_{k_0}$ and $\lambda_{\hat k_f}\le\frac d2\lambda_{k_0}+c_d$.
* **(H-T) Large tori below $k_0$** (R3-05). $n_k\ge4\nu_{\max}(k)(\mathrm{crit}_k+\omega_k)+4$ for $1\le k\le k_0$.

*Instantiation of (H-λ) and (H-T).* P5 p. 490 [checked] gives $\beta_{k_0}\nu_{k_0}>\frac78L^{-d}$, and
$\nu_{k_f-1}\le\frac78L^{-2}$ by minimality of $k_f$. With $\nu_k=\nu L^{2k}\delta_k$ these give
$2(k_f-1-k_0)\log L\le(d-2)\log L+\lambda_{k_0}+2\epsilon$. Since $\hat k_f\le k_f+1$, $\log L>\frac12$ and
$\lambda\le\hat\lambda\le\lambda+2$:
$$\hat k_f-k_0\le\frac{\hat\lambda_{k_0}}{2\log L}+\frac d2+2<\hat\lambda_{k_0},\qquad\hat\lambda_{\hat k_f}=\hat\lambda_{k_0}+(\hat k_f-k_0)\theta\le\tfrac d2\hat\lambda_{k_0}+c_d$$
for $\hat\lambda_0\ge\lambda_*$. (H-T) follows from (3.0), since its right side is $O(\hat\lambda_{k_0}^{p_2+2})$.

### 4.2 Volume lemma and cost coefficients

**Lemma V.** Let $\Gamma$ be a point, or a compact connected union of finitely many segments of total
Euclidean length $\ell$, in $\mathbb R^d$ or in a continuous torus $(\mathbb R/n\mathbb Z)^d$, and let $\rho\ge1$. Then
$|N_{\rho+4}(\Gamma)|_\#\le C_V\rho^{d-1}(\ell+\rho)$ with $C_V=2\cdot14^d$.

*Proof.* In $\mathbb R^d$:
- Take a maximal family $p_1,\dots,p_n\in\Gamma$ with pairwise sup-distances $>\rho$; then
  $\Gamma\subset\bigcup_iB_\infty(p_i,\rho)$.
- If $n\ge2$, the balls $B_\infty(p_i,\rho/2)$ are disjoint. For each $i$, a path in $\Gamma$ from $p_i$ to some
  $p_j$ has an initial piece inside $B_\infty(p_i,\rho/2)$ of Euclidean length $\ge\rho/2$. So $n\rho/2\le\ell$, and
  $n\le2\ell/\rho+1$.
- Each $N_{2\rho+4}(p_i)$ meets at most $(4\rho+10)^d\le(14\rho)^d$ cubes, and
  $N_{\rho+4}(\Gamma)\subset\bigcup_iN_{2\rho+4}(p_i)$.

On a torus, consider the graph whose vertices are the segments of $\Gamma$, adjacent when they meet.
Lift the segments to $\mathbb R^d$ one at a time along a spanning tree of this graph. The lift $\tilde\Gamma$ is
connected, has the same length, and projects onto $\Gamma$. So $N_{\rho+4}(\Gamma)$ is the image of
$N_{\rho+4}(\tilde\Gamma)$, and the count does not increase. $\square$

Define
$$v_j:=c_vC_V\lambda_j\rho_j^{d-1},\qquad w_j:=v_j\rho_j,\qquad\sigma_k:=\sum_{j>k}v_jL^{-(j-k)},\qquad\tau_t:=2A_2\lambda_t^{p_2}.$$
So a component $Z\subset N_{\rho_j+4}(\Gamma)$ at scale $j$ costs at most $c_v\lambda_j|Z|_\#\le v_j\ell(\Gamma)+w_j$.

**Growth facts** (for $\lambda_0\ge\lambda_*$):
- (F1) $\lambda_j\le\lambda_k+(j-k)\theta_+$ for $j\ge k$. The sequences $r,\rho,\omega,D,v,w,\tau,n_q,n_2,\nu_{\max},h$ and the
  maps $j\mapsto j+n_q(j)$, $j\mapsto j+n_2(j)$ are nondecreasing. Also $n_q(a+x)-n_q(a)\le\theta_+x/(\alpha\log L)+1$.
- (F2) $\sigma_k=L^{-1}(v_{k+1}+\sigma_{k+1})$, and $v_{k+n}\le2^{d-1}n^{2d-1}v_{k+1}$ for $n\ge1$. So
  $\sigma_k\le C_\sigma v_{k+1}$ with $C_\sigma=2^{d-1}\sum_{n\ge1}n^{2d-1}L^{-n}$.
- (F3) $\tau_t-\tau_{t-1}\le2A_2p_2\theta_+\lambda_t^{p_2-1}$.
- (F4) $n_q(j)\le\lambda_j/(\alpha\log L)+1$ and $n_2(j)\le2\log_L\lambda_j+C_2\le n_q(j)$.
- (F5) $w_j\le C_w\lambda_j^{2d+1}$ and $E_k:=(1+2C_\sigma2^{3d})v_kD_k\le C_E\lambda_k^{2d+1}$ (now with
  $D_k=\sqrt d(2\rho_k+10+\omega_k)$; only $C_E$ changes).

### 4.3 Consistency of the bookkeeping

Invariant (3.1) is $Z\subset N_{\rho_k+4}(\Gamma(Z))$. A point-spine component meets at most $2\rho_k+10$
cubes per direction, so it has diameter $\le\mathrm{crit}_k$. For $k\le k_0$ it is small by (H-T) and the
hull rule makes it a box. A box of side $\le2\rho_k+10$ lies in $N_{\rho_k+4}$ of its centre.

- (U1) If $Z\subset N_{\rho_k+4}(\Gamma)$, then $Z^\uparrow\subset N_{(\rho_k+4)/L}(\Gamma/L)$. By (G1),
  $B_{Z^\uparrow}\subset N_{s_*r_k+(\rho_k+4)/L}(\Gamma/L)\subset N_{\rho_{k+1}+3}(\Gamma/L)$, because $c_0(1-L^{-1})\ge s_*$,
  $r_k\le r_{k+1}$ and $4/L\le3$. If $\ell(\Gamma/L)\le1$ and $x\in\Gamma/L$, then $N_{\rho+3}(\Gamma/L)\subset N_{\rho+4}(x)$.
  The map $x\mapsto x/L$ is well defined between the continuous tori because $n_k=Ln_{k+1}$.
- (U2) $B_q\subset N_{s'r_k+1/2}(c(q))\subset N_{\rho_{k+1}+3}(c(q))$.
  - The contact graph on the seed sets and hull boxes of a new component has an edge when two of them
    are at index distance $<\omega_{k+1}$. It is connected, because the component is one class of that
    relation.
  - Two sets in contact, each within $\rho+4$ of its own spine point, put the two points at sup-distance
    $\le2\rho+8+\omega$, hence at Euclidean distance $\le D_{k+1}$ (§3.1).
  - So $\Gamma'$ is connected, (3.1) holds (if $\ell(\Gamma')\le1$, by the same remark as in (U1)), and
    $$\ell(\Gamma')\le\sum_i\ell_i/L+(m+r-1)D_{k+1}\tag{4.1}$$
    for $m$ old parts with spine lengths $\ell_i$ and $r$ new cubes.
- (U3) Hulling ($k+1\le k_0$). The box lies in $N_{\rho+4}$ of its centre, which becomes the spine. If the
  component had a non-point spine, its projected epoch was $\ge k+2>k+1$, so $s$ decreases and $t^*$
  does not increase. A hull that comes within $\omega$ of another component merges them; this is an
  event of type (U2) with $r=0$.
- (U4) Kept components: domain and spine unchanged, $b=k$, state $\mathsf{Active}(k,1,\varnothing)$.

*Pure shadow steps do not increase $t^*$ and do not change $\nu$, $\mathcal M$ or the bank $U$.* This is
Lemma C4 (c).

**Lemma T′ (ripeness time after a restart).** Let $Z'$ be created by an event at step $k\to k+1$ that is
a restart ((T2), (T3) or (T5)), so that $Z'$ is Pre or $\mathsf{Active}(k+1,1,\varnothing)$. Put
$\Lambda':=\log_L\max(\ell(\Gamma'),1)$. Then
$$t^*(Z')\le k+2+\Lambda'+n_q(k+2+\Lambda'),\qquad\lambda_{t^*(Z')}\le c_*\lambda_{k+1}+2c_*\theta_+(\Lambda'+2),\qquad c_*:=1+\frac{\theta_+}{\alpha\log L}.$$
*Proof.* In both cases $q'=s'\le k+1+\lceil\Lambda'\rceil$, and $t^*=q'+n_q(q')$ because $n_2\le n_q$ (F4). Then
$\lambda_{t^*}\le\lambda_{q'}+\theta_+n_q(q')\le c_*\lambda_{q'}+\theta_+$, and $\lambda_{q'}\le\lambda_{k+1}+\theta_+(\Lambda'+1)$. $\square$

### 4.4 The invariant

$$\text{(H6′)}\qquad t^*(Z)>k\quad\text{and}\quad G_k(Z)\ \ge\ \tau_{t^*(Z)}+V_k(Z)+\nu(Z)+U(Z),\qquad V_k(Z)=2\sigma_k\ell(Z)+\sum_{j=k+1}^{t^*(Z)}w_j ,$$
with $\nu:=1$ and $U:=0$ for Pre components, and $U=0$ for Pending ones. (H6′)$^{\rm pre}$ is the same
with $t^*(Z)\ge k$.

The terms of the right side have the following meanings:
- The two summands of $V$ are the predicted costs of the future steps: the spine part pays for the
  shrinking phase (cf. E10 (1.81) [review]), and the critical part pays for the window.
- $\tau_{t^*}$ is the threshold that $R$ needs at the ripeness time.
- $\nu$ is one unit of reserve per window piece, spent only at an overflow restart.
- The bank $U$ holds half of the threshold freed by each merge after the core. It is spent only when a
  later merge forces the core across that merge's strip.
- The factor 2 on the spine part creates a reserve proportional to $\ell$, used for events with long
  spines.

**Theorem (LF-2).** Assume (G1), (G2), (B), (Rg), (K), (H-λ), (H-T), $Z_0=\varnothing$ and $\lambda_0\ge\lambda_*$.
- (i) For $k+1\le k_0$: if every component of $Z_k$ satisfies (H6′), then every component of $Z_{k+1}$
  (before $R^{(k+1)}$) satisfies (H6′)$^{\rm pre}$.
- (ii) For $k\le k_0$: if every component of $Z_k$ satisfies (H6′)$^{\rm pre}$, then after $R^{(k)}$ every component
  satisfies (H6′).
- (iii) The components created at step $0\to1$ satisfy (H6′) at $k=1$.
- (iv) (H6′) at $k_0$ implies (H6♭) at $k_0$, and (H6♭) at $k$ implies (H6♭) at $k+1$ for
  $k_0\le k<\hat k_f$; here (H6♭) is $G_k\ge A_2\lambda_{k_0}^{p_2}+2\sigma_k\ell+\sum_{j=k+1}^{\hat k_f}w_j$.

The shape statements of Lemma C4 and Lemma C (e4)–(g) hold along every such history; they follow
from (G1), (G2), (K) and (H-T) alone (Lemma C4, §3.5).

### 4.5 Proof of (i)

Every component $Z'$ of $Z_{k+1}$ arises from a pure shadow step (T1) or from an event (T2)–(T5). Write
$\mu=k+1$, $\lambda=\lambda_\mu$, and
$$A(t):=2A_2p_2\theta_+\lambda_t^{p_2-1}+C_w\lambda_t^{2d+1},\qquad W_\mu(t):=\sum_{j=\mu}^tw_j .\tag{B.6}$$
By (F3) and (F5), each additional scale of ripeness time costs at most $A(t)$. For an event, (B), Lemma
V and (4.1) give
$$G_{k+1}(Z')\ge\sum_iG_k(Z_i)+g_kr-v_{\mu}\Big(\sum_i\ell_i/L+(m+r-1)D_{\mu}\Big)-w_{\mu}.$$
Insert (H6′) for the $Z_i$, use $2\sigma_k\ell_i=\frac2L(v_\mu+\sigma_\mu)\ell_i$, and use the required
$V_\mu(Z')\le2\sigma_\mu(\sum\ell_i/L+(m+r-1)D_\mu)+\sum_{j=\mu+1}^{t^{*\prime}}w_j$. It then suffices that
$$\sum_i\tau_{t^*_i}+\sum_iW_\mu(t^*_i)+g_kr+v_\mu\sum_i\frac{\ell_i}L+\sum_i(\nu_i+U_i)\ \ge\ \tau_{t^{*\prime}}+W_\mu(t^{*\prime})+(m+r-1)E_\mu+\nu'+U'.\tag{B.7}$$
This is (4.2) of version 3, for Active and Pending inputs alike. Every old $t^*_i>k$, so $t^*_i\ge\mu$ and
$\sum_i\tau_{t^*_i}\ge m\tau_\mu$. Constants $C$ depend only on the typing data, not on $k$, $m$, $r$ or the history.
Note $\lambda_k\ge\lambda/2$, and put $c':=c_*(1+6\theta_+)$.

**Pure shadow** (T1), including a hull without contact and Pending activation. By (B),
$G_{k+1}(Z')\ge G_k(Z)-v_\mu\ell/L-w_\mu$, by (U1) (or (U3)) and Lemma V. By (H6′) and (F2),
$$G_{k+1}(Z')\ge\tau_{t^*}+2\sigma_\mu\ell/L+\sum_{j=\mu+1}^{t^*}w_j+v_\mu\ell/L+\nu+U\ \ge\ \tau_{t^{*\prime}}+V_\mu(Z')+\nu'+U',$$
since $t^{*\prime}\le t^*$, $\ell'\le\ell/L$, and $\nu'=\nu$, $U'=U$ (Lemma C4 (c)). Activation changes no number. Moreover
$t^{*\prime}\ge\mu$, with equality only for a ripe Active component, which $R^{(\mu)}$ then processes. This is the
exact telescoping that replaces "$K(Z')\ge K(Z)-1$" (P6 Prop 3.2 (iii)).

**Case 1: new cubes, $r\ge1$** ((T2); restart, $\nu'=1$, $U'=0$; old banks dropped). It suffices that
$$m\tau_\mu+rg_k+v_\mu\sum_i\ell_i/L\ \ge\ \tau_{t^{*\prime}}+W_\mu(t^{*\prime})+(m+r-1)E_\mu+1.\tag{B.8}$$
- (1a) $\Lambda'\le\lambda$. By Lemma T′, $\lambda_{t^{*\prime}}\le c'\lambda$ and $t^{*\prime}-k\le C\lambda$, so
  $\tau_{t^{*\prime}}+W_\mu(t^{*\prime})+1\le2A_2c'^{p_2}\lambda^{p_2}+C\lambda^{2d+2}+1$. Moreover $\tau_\mu\ge E_\mu$, and
  $g_k\ge\frac12A_32^{-2p_0}\lambda^{2p_0}\ge E_\mu+2A_2c'^{p_2}\lambda^{p_2}+C\lambda^{2d+2}+1$ for $\lambda\ge\lambda_*$, since $2p_0>p_2\ge2d+3$.
  So (B.8) holds. This includes the base, $m=0$ (part (iii)).
- (1b) $\Lambda'>\lambda$. Then $\lambda_{t^{*\prime}}\le c'\Lambda'$ and $t^{*\prime}-k\le C\Lambda'$, so the threshold and waiting sum are
  at most $C\Lambda'^{p_2}$. By (4.1), $L^{\Lambda'}\le H+F$ with $H=\sum_i\ell_i/L$ and $F=(m+r-1)D_\mu$.
  - If $H\ge\frac12L^{\Lambda'}$, then $v_\mu H\ge\frac12\lambda L^{\Lambda'}\ge C\Lambda'^{p_2}+1$.
  - If $F\ge\frac12L^{\Lambda'}$, then $m+r-1\ge L^{\Lambda'}/(2D_\mu)\ge C\Lambda'^{p_2}+1$. One unit from each old
    threshold or gain pays this count, and the rest pays $(m+r-1)E_\mu$.

**Case 2a: merge, all parts Active or Pending, within the cap** ((T4)). Then $\nu'=\sum_i\nu_i$, which
cancels. Let $i_0$ maximize $t^*_i$, let $c:=k_1(t_0)$, and put
$$\Delta_1:=(t_0-t^*_{i_0})_+,\qquad\Delta_2:=T-t_0,\qquad X:=\{\xi\in E:\ \xi<q',\ \xi+h_\xi\ge c\}.\tag{B.9}$$
These are the *smallness shift*, the *strip shift* and the *crossed* merges.

- *Banks.* Old records are all $<\mu$, so set subtraction gives, with $D:=[\mu\in\mathcal M']$,
  $$U'-\sum_iU_i\ \le\ \tfrac12D\tau_\mu-\tfrac12\textstyle\sum_{\xi\in X,\ \xi<\mu}\tau_\xi,\qquad D\le[\mu\notin X].\tag{B.10}$$
  - Duplicate scales in different input records only add slack.
  - There is no deposit when the new merge lies behind a pending target and is released at once.
  - No bank is spent twice: a bank leaves $\mathcal M'$ at the one transition that releases it, and cores
    never decrease (B.4).
- *Smallness shift.* Since $t^*_i\ge q_i+n_q(q_i)$, $\tilde q+n_q(\tilde q)\le t^*_{i_0}$, so only $s'+n_2(s')$ can exceed
  $t^*_{i_0}$.
  - The part carrying the longest spine has $t^*\ge s\ge k+\log_L\ell_{\max}$ (its projected epoch; trivial if
    all spines are points). This holds for Pending parts too, by (B.2).
  - So $t^*_{i_0}\ge k+\log_L\ell_{\max}$, while $\Lambda'\le\log_L\ell_{\max}+\log_L(m(1+D_\mu))$ by (4.1). Hence
    $$\Delta_1\le\bar\Delta:=3+\log_Lm+\log_L(1+D_\mu)+n_2(\mu+1+\Lambda').\tag{B.11}$$
- *The cap bounds everything here* (REPAIRS-astra's improvement over version 3). By Lemma C4 (a),
  $\ell'\le(\nu'-1)D_\mu\le\nu_{\max}(\mu)D_\mu$, so $\Lambda'=O(\log\lambda)$, $m\le\nu_{\max}(\mu)$ and $\bar\Delta\le C\log\lambda$. No
  large-$\Lambda'$ branch arises.
- *Strip shift.* The integer core scales $[c,q'-1]$ are all blocked, each by a strip $[\xi,\xi+h_\xi]$ with
  $\xi\in X$. So $q'-c\le\sum_{\xi\in X}(h_\xi+1)$. If $X=\varnothing$ then $\Delta_2=0$. Otherwise $T=q'+n_q(q')$ and
  $t_0\ge c+n_q(c)$, so by (F1)
  $$\Delta_2\le c_*\textstyle\sum_{\xi\in X}(h_\xi+1)+1\le\sum_{\xi\in X}\{c_*(h_\mu+1)+1\}.\tag{B.12}$$
- *Scales involved.* Let $i$ be a part with $q_i=\tilde q$.
  - If it is Active, then Lemma C (f4) and $t^*_i\ge\mu$ give $\mu<(\tilde q+1)+n_q(\tilde q+1)$, so
    $\lambda_\mu\le c_*\lambda_{\tilde q}+2\theta_+$. If it is Pending, then $\tilde q\ge\mu$.
  - With $q'\le\mu+h_\mu+1$ (B.4) and $\tilde q\le q'$, for $\lambda\ge\lambda_*$:
    $$\lambda_T\le2c_*^2\lambda_{\tilde q},\qquad\xi\in X\cup\{\mu\}\ \Longrightarrow\ \xi\ge\tilde q-h_\mu\ \Longrightarrow\ \lambda_\xi\ge\tfrac12\lambda_{\tilde q}\ge\frac{\lambda_T}{4c_*^2}.\tag{B.13}$$
    (For $\xi\in X$, $\xi+h_\xi\ge c\ge\tilde q$. For $\xi=\mu$, $\tilde q\le\mu+h_\mu$.)
  - Since $h_\mu=O(\log\lambda)$, increasing $\lambda_*$ makes the following per-merge inequality true for every
    $\xi\in X\cup\{\mu\}$:
    $$\tfrac12\tau_\xi=A_2\lambda_\xi^{p_2}\ \ge\ \{c_*(h_\mu+1)+1\}A(T).\tag{B.14}$$
- *Payment.*
  - The merge frees at least $(m-1)\tau_\mu$ from the thresholds other than $t^*_{i_0}$. Set aside $\frac12\tau_\mu$
    for the new merge: for its deposit if $D=1$, or for its crossed strip if $\mu\in X$ (otherwise it is
    unused).
  - Every old crossed strip is paid by its released bank in (B.10), using (B.14).
  - After cancelling the $i_0$ threshold and waiting sum, the remaining sufficient inequality is
    $$\tfrac12(m-1)\tau_\mu+v_\mu\ell_{\max}/L\ \ge\ \bar\Delta A(T)+(m-1)E_\mu .\tag{B.15}$$
  - Its right side is $\le C\log\lambda\,\lambda^{\max(p_2-1,2d+1)}+(m-1)C_E\lambda^{2d+1}\le\frac12(m-1)\tau_\mu$ for $m\ge2$,
    $p_2\ge2d+3$ and $\lambda\ge\lambda_*$.
  - This proves (B.7), including repeated pending pushes and chains of nested strips.

*Why the bank is needed.* If only the new merge is crossed, the freed threshold pays, as the
re-review proposes. But when two parts with different cores combine, the merged core $c\ge\tilde q$ can
fall in the strip of an earlier merge of one part. Pushing it forward can then run through strips of
the other part's merges that lay after that part's own core. The freed threshold of the current merge
does not cover such a chain; the banks of the crossed merges do, one merge at a time (COUNTING-astra's
ledger confirms that there is no separate bank deficit).

**Case 2b: merge with a Pre part** ((T3); restart, $\nu'=1\le\sum_i\nu_i-1$, banks dropped). Lemma T′
applies.
- Let $p$ be a Pre part: $t^*_p=s_p+n_q(s_p)\ge\mu+n_q(\mu)$. Let $i_1$ carry the longest spine, and put
  $\Lambda_*:=\log_L\ell_{\max}$.
  - If $i_1$ is Pre, then $t^*_{i_0}\ge t^*_{i_1}\ge k+\Lambda_*+n_q(k+\Lambda_*)$.
  - If $i_1$ is Active or Pending, then $\Lambda_*\le\log_L(\nu_{\max}(k)D_k)\le C_3\log\lambda$ by Lemma C4 (a), and
    $t^*_{i_0}\ge t^*_p$.
- In both cases, with $\Lambda'\le\Lambda_*+\log_L(m(1+D_\mu))$, Lemma T′ and (F1) give
  $$\Delta:=(t^{*\prime}-t^*_{i_0})_+\le\bar\Delta':=c_*\big(2+C_3\log\lambda+\log_L(m(1+D_\mu))\big)+2.\tag{B.16}$$
- The sufficient inequality is
  $$(m-1)\tau_\mu+v_\mu\ell_{\max}/L\ \ge\ \bar\Delta'A(t^{*\prime})+(m-1)E_\mu .\tag{B.17}$$
- If $\Lambda'\le\lambda$: $\lambda_{t^{*\prime}}\le c'\lambda$ and $\bar\Delta'\le C(m-1)(1+\log\lambda)$ (as $\ln m\le m-1$), so the right side is
  $\le\frac12(m-1)\tau_\mu$.
- If $\Lambda'>\lambda$: either $\Lambda_*\ge\Lambda'/2$, or $\log_L(m(1+D_\mu))\ge\Lambda'/2$.
  - If $\Lambda_*\ge\Lambda'/2$, then $\Lambda_*>C_3\log\lambda$ forces $i_1$ to be Pre. Its spine reserve
    $v_\mu\ell_{\max}/L\ge\lambda L^{\Lambda'/2-1}$ dominates $C(\log_Lm+\Lambda')\Lambda'^{p_2-1}$ when $m-1\le L^{\Lambda'/4}$. For
    $m-1>L^{\Lambda'/4}$, $C\log m\,\Lambda'^{p_2-1}\le C(\log m)^{p_2}\le m-1$.
  - If $\log_L(m(1+D_\mu))\ge\Lambda'/2$, then $m\ge L^{\lambda/4}$, and the right side is
    $\le C(\log m)^{p_2}+(m-1)C_E\lambda^{2d+1}\le\frac12(m-1)\tau_\mu$.

**Case 2c: overflow** ((T5); restart, $\nu'=1$, banks discarded). By Lemma C4 (a), $\ell_i\le\nu_iD_k$, so
$\Lambda'\le\log_L(2D_\mu\sum_i\nu_i)$. Cancel the $i_0$ terms, and pay $(m-1)E_\mu$ with $(m-1)\tau_\mu$. It suffices that
$$\sum_i\nu_i-1\ \ge\ \tau_{t^{*\prime}}+W_\mu(t^{*\prime})+1.\tag{B.18}$$
- If $\Lambda'\le\lambda$, the right side is at most
  $$2A_2c'^{p_2}\lambda^{p_2}+C\lambda^{2d+2}+1\ \le\ C_r\lambda^{p_2},\qquad C_r:=2A_2c'^{p_2}+1,\tag{4.4}$$
  for $\lambda\ge\lambda_*$, while $\sum_i\nu_i-1\ge\nu_{\max}(\mu)\ge C_\nu\lambda^{p_2}\ge C_r\lambda^{p_2}$ by (K).
- If $\Lambda'>\lambda$, then $\sum_i\nu_i\ge L^{\Lambda'}/(2D_\mu)\ge C\Lambda'^{p_2}+1$.

This proves (i). $\square$

*Where this differs from REPAIRS-astra §B.3.*
- The sequence is the abstract $\lambda$, with $\theta_\pm$; in the instantiation the increments are exact.
- $D_\mu$ includes $\omega_\mu$, which changes only $C_E$, $C_3$ and the $O(\log\lambda)$ bounds on $\Lambda'$ and $h$.
- In (B.13) I added the Active/Pending case distinction for the part carrying $\tilde q$; REPAIRS-astra
  cites version 3's Lemma C (f), which covers only the Active case.
- Case 1 keeps version 3's numbering. The arithmetic is REPAIRS-astra's.

**Remark (what replaced E10's tree induction).** E10 (1.84)–(1.88) handles merges by an induction over
a spanning tree of the merged domains. It pays a restarted geometric waiting period with a reserve
$2(1+\beta_0)^{-1}p_0(g_{j+1})$ that does not grow along the flow [review: MERGES-astra.md §1]. Here four
things replace that induction: the additivity of $G$, of $\nu$ and of the banks (Lemma B, (T4)); the
union bound for spines (4.1); the pending state; and the quantitative shift of the ripeness time.
- A merge of window-bearing parts shifts the smallness clock by $O(\log\lambda)$ scales, and possibly
  shifts the core across merge strips by $O(h)$ scales per merge crossed. Each shift is paid by the
  freed threshold or by a bank.
- A restart of the whole window ($n_q$ scales) happens only at overflow, where at least
  $\nu_{\max}\asymp\lambda^{p_2}$ units of reserve are available.
- Proposition M (§4.10) shows that a full restart at every merge cannot be paid.

### 4.6 Proof of (ii) and (iii)

(ii) Non-ripe components (all Pre, all Pending, and the Active ones with $t^*>k$) are unchanged by
$R^{(k)}$, and satisfy (H6′) because $t^*>k$. A ripe component (Active, $t^*=k$, a box by Lemma C (g)) is
removed, or kept. If kept, then
$G_{\rm new}\ge G_k-C_R\lambda_k^{2d+1}+g'_k\ge\tau_k+\nu+U-C_R\lambda_k^{2d+1}+A'_3\lambda_k^{p_R}$, and its new state is
$\mathsf{Active}(k,1,\varnothing)$, so the new bank is $0$. Its smallness clock satisfies $s+n_2(s)\le k$, so
$t^{*\prime}=k+n_q(k)$ and $V'=\sum_{j=k+1}^{k+n_q(k)}w_j$. Since $\lambda_{k+n_q(k)}\le c_*\lambda_k+\theta_+$, it suffices that
$$A'_3\lambda_k^{p_R}\ \ge\ C_R\lambda_k^{2d+1}+2A_2(c_*+1)^{p_2}\lambda_k^{p_2}+\Big(\frac{\lambda_k}{\alpha\log L}+1\Big)C_w(c_*+1)^{2d+1}\lambda_k^{2d+1}+1.$$
This is true for $\lambda_k\ge\lambda_*$, because $p_R>p_2+2d>2d+2$ (it is REPAIRS-astra (B.19), in the
stronger form of version 3). After $R^{(k)}$ no component is ripe.

(iii) A component created at step $0\to1$ is a (T2) event with $m=0$, with gain $g_0=\frac12A_3\lambda_0^{2p_0}$ per
cube (LF-6 (ii)). Case 1 of §4.5 with $m=0$ applies verbatim. $\square$

### 4.7 Proof of (iv): transfer at $k_0$ and the frozen regime

*Horizon.* (H-λ) gives $\hat k_f-k_0<\lambda_{k_0}$ and $\lambda_{\hat k_f}\le\frac d2\lambda_{k_0}+c_d$; its instantiation is in
§4.1 (from P5 p. 490 [checked] and the definition of $\hat k_f$). Without (H-λ) the transfer fails:
COUNTING-astra C-04 lets $k_f$ recede while every other premise holds. With it,
$$\sum_{j=k_0+1}^{\hat k_f}w_j\le(\hat k_f-k_0)C_w\lambda_{\hat k_f}^{2d+1}\le\lambda_{k_0}C_w\big(\tfrac d2\lambda_{k_0}+c_d\big)^{2d+1}\le A_2\lambda_{k_0}^{p_2}\tag{B.20}$$
for $\lambda_{k_0}\ge\lambda_*$, since $p_2\ge2d+3$.

*Transfer.* At $k_0$, (H6′) gives $G\ge\tau_{t^*}+2\sigma_{k_0}\ell+\sum_{j=k_0+1}^{t^*}w_j+\nu+U$ with $t^*>k_0$; this
includes Pending components. Discard $\nu+U\ge0$ and the window data. (H6♭) needs
$G\ge A_2\lambda_{k_0}^{p_2}+2\sigma_{k_0}\ell+\sum_{j=k_0+1}^{\hat k_f}w_j$. Since $\tau_{t^*}\ge\tau_{k_0+1}\ge2A_2\lambda_{k_0}^{p_2}$, this follows from
(B.20).

*Frozen steps* ($k_0\le k<\hat k_f$; no $R$, no hull, no window state).
- Pure shadow: the computation of §4.5, with $\tau_{t^*}$ replaced by the constant $A_2\lambda_{k_0}^{p_2}$, $t^*$ by
  $\hat k_f$, and no $\nu$.
- Event: (B.7) becomes
  $$(m-1)_+A_2\lambda_{k_0}^{p_2}+g_kr+[m=0]\,\big(-A_2\lambda_{k_0}^{p_2}-\textstyle\sum_{j=k+1}^{\hat k_f}w_j\big)\ \ge\ (m+r-1)E_{k+1}$$
  (the spine terms are handled as in §4.5). With $\lambda_{k+1}\le\lambda_{\hat k_f}\le d\lambda_{k_0}$,
  $E_{k+1}\le C_E(d\lambda_{k_0})^{2d+1}$ and $g_k\ge\frac12A_3\lambda_{k_0}^{2p_0}$, this holds for $\lambda_{k_0}\ge\lambda_*$.
- There is no ripeness time in (H6♭), so no analogue of Cases 1b, 2a–2c is needed.
- Components may wind on the small tori of this regime. Lemma V and (4.1) hold on tori (§4.2), and no
  hull is taken. $\square$

*Consequences.*
- For $k\le k_0$: $G_k\ge\tau_{t^*}\ge\tau_{k+1}>2p_2(\beta_k)$, which is P5 (1.30) with $\ell=2$.
- At ripeness, $G_k\ge\tau_k+\nu\ge2p_2(\beta_k)+\nu$, the input of LF-4 Step 6.
- For $k_0\le k\le k_f$: $G_k\ge A_2\hat\lambda_{k_0}^{p_2}\ge p_2(\beta_{k_0})$, which is P5 (1.31) with $\ell=1$ and the frozen
  threshold.

### 4.8 P6 Thm 4: the printed inequality fails; the repair works

*The printed chain* (P6 p. 22, page image [checked]):
$$\kappa_{k,n}>\kappa_{k,K}-\mathrm{const}\sum_{p=K+1}^n\log\beta_{k+p}(12MR_{k+p})^d>2p_2(\beta_{k+K})-\mathrm{const}(12MR_0)^d\sum_{p=K+1}^n(\log\beta_{k+p}a)^{2d+1}$$
$$>2p_2(\beta_{k+K})-\mathrm{const}'(\log\beta_{k+K}a)^{2d+2}>p_2(\beta_{k+n}),\qquad\text{"if }n\le K+\log\beta_{k+K}a,\ p_2\ge2d+2,\ A_2\text{ large".}$$
With $p_2(\beta)=A_2(\log\beta)^{p_2}$ (P5 p. 495 [checked]) and $\lambda:=\log\beta_{k+K}a$, take $n-K=\lfloor\lambda\rfloor$.
By P4 (H.6), $\log\beta_{k+n}\ge\lambda+(\lambda-1)(d-2)\log L-Cc_8$. The last inequality requires
$p_2(\beta_{k+n})<2p_2(\beta_{k+K})$, i.e. $\big(\log\beta_{k+n}/\log\beta_{k+K}\big)^{p_2}<2$, but the ratio tends to
$(1+(d-2)\log L)^{p_2}\ge(1+\ln2)^8\approx67.5$ as $\lambda\to\infty$, for every $A_2$ (both sides are
proportional to $A_2$, and the $\mathrm{const}'$ term only makes it worse). The inequality holds only for
$n-K\lesssim(2^{1/p_2}-1)\lambda/((d-2)\log L)$. **Confirmed: the last inequality fails as printed**
(agrees with QC_LOG Phase 4, ER-091, and the review's recomputation, ratio $67.54$).

*The repair in P6's own terms.* Suppose at $k_0$ the component has $K\ge1$ (so $\kappa_{k_0,n}>2p_2(\beta_{k_0+n})$
for $n\le K$) and, from step $K$ on, is below critical size. For $K<n\le k_f-k_0$:
$$\kappa_{k_0,n}>2p_2(\beta_{k_0+K})-c_{12}(n-K)\lambda_{k_f}^{2d+1}\ge2p_2(\beta_{k_0})-c_{12}\lambda_{k_0}\big(\tfrac d2\lambda_{k_0}+c_d\big)^{2d+1}\ge p_2(\beta_{k_0}),$$
with $c_{12}=\mathrm{const}(12MR_0)^d$, using $n-K<k_f-k_0<\lambda_{k_0}$ and the bound on $\lambda_{k_f}$ of §4.7; the last
step holds if $A_2\lambda_{k_0}^{p_2}\ge c_{12}(\frac d2+1)^{2d+1}\lambda_{k_0}^{2d+2}$, i.e. for $p_2>2d+2$ and $\beta$ large, or
$p_2=2d+2$ and $A_2\ge c_{12}(\frac d2+1)^{2d+1}$. For $n\le K$, $\kappa_{k_0,n}>2p_2(\beta_{k_0+n})\ge p_2(\beta_{k_0})$. So
the $\ell=1$ bound holds for all remaining steps with the threshold $p_2(\beta_{k_0})$. The phase in
which the component is still above critical size needs P6 Prop 3.2 (i) in some form; in (A′) both
phases are covered by §4.7.

*Sufficiency for the last step.* P7 (4.12)–(4.13) [checked] need $\varepsilon^{-2}e^{-p_2}\le\frac12\beta_{k_f}^{-m-1}$
with $\varepsilon^{-2}=3^dK_0e^{\frac32dL\kappa}$. With the frozen threshold:
$p_2(\beta_{k_0})=A_2\lambda_{k_0}^{p_2}\ge A_2\big(\tfrac2d(\lambda_{k_f}-c_d)\big)^{p_2}\ge(m+2)\lambda_{k_f}+\log(2\varepsilon^{-2})$
for $\beta\ge\beta_0$, since $p_2>1$. So the repair suffices for LF-8 and Root-F. This confirms the
proposal of roadmap §4.3 (agreed by Roland, ruling 8).

### 4.9 P6 Prop 3.2 (ii) is false for merged components

This completes version 1's counterexample along LFR-04 and MERGES-astra.md §2.

*Definitions used* (P6 (3.19), pp. 20–21 [checked]; MERGES-astra.md §1). With $G_t$ as in §3.4 and
$c_{t,p}(Z)\ge0$ the predicted cost of the $p$-th shadow layer,
$\kappa_{t,n}(Z)=G_t(Z)-\sum_{p=1}^nc_{t,p}(Z)$ and $K(Z)=\max\{n:\kappa_{t,n}(Z)>\tau_{t+n}\}$; for a critical-size shadow
$c_{t,p}\le C\lambda_t^{2d+1}$. P6 Prop 3.2 (ii) (p. 21): if $K=0$ at scale $k'$, there is $k_1<k'$ with
$k'-k_1>\log\beta_{k_1}a$ ((3.20)) such that for $k_1\le j\le k'$ the domains $Z_j\cap Z$ have diameters below the
critical sizes, the multi-indices $\mathbb A_j\cap Z$ control at least $k'-j$ steps, and no new large-field
regions appear.

*The configuration.* Two quiet components $Z^{(1)},Z^{(2)}$, each a box below critical size, with
$K(Z^{(i)})=1$ at scale $t$, whose shadows first touch at step $t\to t+1$; $Z'$ is the merged component.

*Upper bound on the merged budget* (the bound version 1 lacked). $K(Z^{(i)})=1$ gives
$\kappa_{t,2}(Z^{(i)})\le\tau_{t+2}$, hence $G_t(Z^{(i)})\le\tau_{t+2}+C\lambda_t^{2d+1}$. In one step of a pure merge $G$ can grow
at most by the old-volume surplus, $O(\lambda_t^{2d+1})$ for critical-size pieces (P6 (3.10)–(3.11); new
cubes are absent and $\log C\ge0$), so
$$G_{t+1}(Z')\le2\tau_{t+2}+C\lambda_t^{2d+1},\qquad\text{and also}\qquad G_{t+1}(Z')\ge2\tau_{t+1}-C\lambda_t^{2d+1}$$
by Lemma B and $\kappa_{t,1}(Z^{(i)})>\tau_{t+1}$; the latter gives $K(Z')\ge1$. Since $\kappa_{t+1,n}\le G_{t+1}$,
$K(Z')\le\max\{n:\tau_{t+1+n}<2\tau_{t+2}+C\lambda^{2d+1}\}$; with $\lambda_{t+1+n}\ge\lambda_{t+2}+(n-1)\theta$, $\theta\to(d-2)\log L$ by P4
(H.6), this gives
$$K(Z')\ \le\ \Big(\frac{2^{1/p_2}-1}{\theta}+o(1)\Big)\lambda_t+2 .$$
The coefficient is $2^{1/p_2}-1$ (MERGES-astra.md (2.3)); $\ln2/p_2$ in version 1 is its first-order
approximation. The *actual* time $k'$ at which the merged component reaches $K=0$ obeys the same
bound: without new large fields, $G$ grows by at most $C\lambda_s^{2d+1}$ per step (old-volume surplus),
which over $O(\lambda_t)$ steps is $O(\lambda_t^{2d+2})=o(\tau_t)$ for $p_2\ge2d+3$. Since
$(2^{1/9}-1)/\ln2<0.12$, $k'-t<\lambda_t$ for $\lambda_t$ large.

*Contradiction under P7's reading.* P7 p. 498 reads (ii) as "the domains $Z_j$ for $k_1\le j\le k$ are
rectangular parallelepipeds with diameters … smaller than the critical sizes" [checked]. If
$k_1\ge t+1$, then $k'-k_1<\lambda_t\le\log\beta_{k_1}a$, contradicting (3.20). So $k_1\le t$, and at $j=t$ the domain
$Z_t\cap Z'$ consists of the two disjoint components $Z^{(1)},Z^{(2)}$, which is not a parallelepiped.
(Version 1 argued through the separation at $t-3$; that is not needed.)

*The per-component reading* (diameters of each piece) fails at the control clause: at $j=t$ each
piece's multi-index controls $K(Z^{(i)})=1$ step, while (ii) requires $k'-t\ge2$ steps ($k'\ge t+2$
because $K(Z')\ge1$ at $t+1$). Only a *mixed* reading survives (per-piece geometry, pooled budget);
that is a new statement, not used by P7, and it is the multi-piece situation that P7 does not
treat.

*Existence.* Let $Z^{(1)}$ be the component created at some scale $b$ by one new large-field cube and
quiet afterwards. Its counter starts at order $\lambda$ (gain $\asymp\lambda^{2p_0}$), decreases by at most one per
step (P6 Prop 3.2 (iii); P6 (3.21)), and must reach $0$ because $G$ stays bounded by $G_b+O(\lambda^{2d+2})$ over
the relevant range while $\tau$ grows; so $K(Z^{(1)})=1$ at some scale $t$. Let $Z^{(2)}$ be its translate by
$\sigma e_1ML^{t+1}$, $\sigma\in\mathbb N$, on a torus large enough. All partitions $\pi_j$, $j\le t+1$, are invariant
under $ML^{t+1}\mathbb Z^d$ and the step rules are translation covariant, so while the two pieces are
separate, the history of $Z^{(2)}$ is the translate of that of $Z^{(1)}$. Let $m(\sigma)$ be the first scale at
which the two (separately computed) regions are adjacent; $m$ is nondecreasing in $\sigma$ and
unbounded. Let $\sigma^*:=\max\{\sigma:m(\sigma)\le t+1\}$. If $m(\sigma^*)\le t$, then at scale $t+1$ the separately computed
regions overlap by at least the buffer width $2R_t\ge2$ cubes of $\pi_{t+1}$, and moving $Z^{(2)}$ by one more
$\pi_{t+1}$-cube keeps them adjacent, so $m(\sigma^*+1)\le t+1$, a contradiction. Hence $m(\sigma^*)=t+1$: the
pieces are separate through scale $t$ and merge at $t\to t+1$. P5's admissibility paragraph (p. 496)
asks only past positivity of $K$, which holds. UNCERTAIN: the overlap claim uses that the buffers
added in one step are at least two cubes wide in every direction, which Lemma G must confirm for
the exact rounding of P5 (2.3)–(2.4).

*Diagnosis.* E10's $K$ is geometric and E10 (1.80) proves "budget $\ge$ cost up to the geometric
stopping time". P6 redefines $K$ by budget exhaustion and asserts the converse, "exhausted $\Rightarrow$
geometrically ripe", which fails exactly when two nearly exhausted budgets are pooled by a merge
(the review's §2.2 and MERGES-astra.md §1 reach the same diagnosis).

*Confidence:* 92%. The residual risk is an unstated restriction elsewhere in P5–P7 excluding such
merges; none was found in P5 §§1–2, P6 §3, P7 §§1–3 (also MERGES-astra.md, 95% on this point).

### 4.10 Proposition M: a window restart at every merge cannot be paid

**Proposition M.** Let $d\ge3$, $\alpha\in(0,\frac{d-2}2)$, $p_0,p_2$ as in §5, and consider the rule (R2) of §2.7.2:
$R$ acts only on components that have been a single box below critical size, without new large
fields, for a window of $n_q$ scales, and a merge restarts the window. Put $\kappa_-:=1+\frac{d-2}{2\alpha}>2$. There
are constants $c_M,C_M>0$ such that for every $\lambda_b\ge\lambda_*$ and every
$$H\ \ge\ H_0(\lambda_b):=\Big\lceil\frac{(2p_0-2d-2)\log_2\lambda_b+\log_2(4C_M/c_M)}{2d+1}\Big\rceil+1$$
there is a history generated by the step rules (on a large enough torus) in which a component
$Z_H$ formed from $2^H$ atoms, each a single new large-field cube created at scale $b$, has
$G_t(Z_H)<0$ at the end of its window, where $G$ is P6's budget (3.10)–(3.11).

*Construction.* A balanced binary tree of depth $H$. Level $0$: the $2^H$ atoms; each becomes a quiet
box below critical size at scale $s_0:=b+2$. Level $i\ge1$: two level-$(i-1)$ components, each in its
window since $s_{i-1}$, are placed so that they merge at $m_i:=s_{i-1}+n_q(s_{i-1})-1$, one step before
either becomes ripe; the merged pair (two adjacent critical boxes) shrinks and is hulled into one box
by $s_i:=m_i+2$. Positions are chosen recursively by the existence argument of §4.9 (merge time is
nondecreasing in the separation and cannot skip a scale). Under (R2) no component of the tree is
ripe before it merges, so the history is generated by the rules.

*Growth of $\lambda$ along the tree.* $s_i\ge s_{i-1}+n_q(s_{i-1})$ and $n_q(s)\ge\lambda_s/(\alpha\log L)$, so
$\lambda_{s_i}\ge\lambda_{s_{i-1}}+\theta_-n_q(s_{i-1})\ge\kappa_-\lambda_{s_{i-1}}$, hence $\lambda_{s_i}\ge\kappa_-^i\lambda_b$.

*Cost of a quiet critical box.* A quiet box reaches, within $O(1)$ steps, the steady size fixed by
"shadow, then buffer, then hull", which is nondecreasing in $j$ (it grows with $r_j$). At a step
$j\to j+1$ in this steady state the new volume $Z^c_j\cap Z_{j+1}$ has $|\cdot|_{j+1}\ge(1-L^{-d})|Z_j|_j\ge c(M\mathrm{crit}_j)^d$
(the buffer is re-added each step; P6 (3.14)–(3.16)), and the budget changes by
$$G_{j+1}-G_j\ \le\ -(c_1\log\beta_j+c_2)|Z^c_j\cap Z_{j+1}|_{j+1}+\big(H_j|Z_j|_j-H_{j+1}|Z_{j+1}|_{j+1}\big)\ \le\ -c\,c_1\lambda_j(M\mathrm{crit}_j)^d\ \le\ -c_M'\lambda_j^{2d+1},$$
because $\kappa^{(j)}$ is the exact expression of §3.4 with no gain term (no new cubes), $\log C$ does not
decrease (P6 (3.11)), and $|Z_{j+1}|_{j+1}\ge|Z_j|_j$, $H_{j+1}\ge H_j$ make the $H$-terms nonpositive. The $O(1)$
steps around each merge, where the pair shrinks to one box, change $G$ by at most $C\lambda_j^{2d+1}$
(old-volume surplus). Over its window of $n_q(s_i)\ge\lambda_{s_i}/(\alpha\log L)$ steps a level-$i$ component
therefore loses at least $c_M\lambda_{s_i}^{2d+2}\ge c_M\kappa_-^{i(2d+2)}\lambda_b^{2d+2}$ for $\lambda_b\ge\lambda_*$. These losses are not
refunded under (R2): P7's refund (3.8)–(3.9) covers only the last window, from its $k_1$ on; the
earlier windows lie inside $\mathbb T_{k_1}$, and refunding them would mean analysing a window that
contains merges, which is route (R1).

*Income.* The only positive terms in P6's $\kappa$ are the gains of new cubes; here these are the
$2^H$ atoms, each contributing at most $C_M\lambda_b^{2p_0}$.

*Conclusion, level by level* (R2-05 (a)). $G$ is additive at merges up to the one-step terms
(P6 (3.10)–(3.11)). At level $i$ there are $2^{H-i}$ components; their window losses total at least
$2^{H-i}c_M\lambda_{s_i}^{2d+2}$, while the $O(1)$ non-steady steps around their merges (the shrinking of a merged
pair to one box) add at most $2^{H-i}C\lambda_{s_i}^{2d+1}$, a fraction $O(1/\lambda_b)$ of that level's losses.
Summing over the levels and keeping only the root's loss, at the end of the root's window
$$G(Z_H)\ \le\ 2^HC_M\lambda_b^{2p_0}-\tfrac12\sum_{i=1}^H2^{H-i}c_M\lambda_{s_i}^{2d+2}\ \le\ 2^HC_M\lambda_b^{2p_0}-\tfrac12c_M\kappa_-^{H(2d+2)}\lambda_b^{2d+2}\ <\ 0$$
as soon as $(\kappa_-^{2d+2}/2)^H>(2C_M/c_M)\lambda_b^{2p_0-2d-2}$, which holds for $H\ge H_0(\lambda_b)$ since
$\kappa_-^{2d+2}/2>2^{2d+1}$. $\square$

*Remark (shorter windows; R2-05 (b)).* The proof uses the window length only through
$\lambda_{s_{i+1}}\ge\kappa\lambda_{s_i}$ with $\kappa^{2d+2}>2$. If P7's window $n_1(s)$ were only $\ge c\lambda_s/\log L$, the same
construction gives $\kappa=1+c\theta_-/\log L=1+c(d-2)/2$. P7's own estimates force $c$ well above the
threshold $\kappa^{2d+2}=2$: (3.11) needs $\varepsilon_k=\varepsilon_{k_1}L^{-\alpha n_1}$ below $\delta_{k_1}$ up to powers of $\lambda$, i.e.
$\alpha n_1\log L\ge\frac12\lambda_{k_1}(1-o(1))$, so $c\ge\frac1{2\alpha}$ and $\kappa\ge1+\frac{d-2}{4\alpha}>\frac32$, with $(\frac32)^{2d+2}\ge(\frac32)^8>2$
(this reading of (3.11) is mine). (2.59) on the analyticity domain gives a weaker bound of the
same kind (re-review R2-05). So (R2) fails for every window length P7's estimates allow.

*Consequences.* (1) No invariant implying $G\ge0$, and no allocation of pooled reserves, can hold
for (R2): the total income of the lineage is smaller than its costs. (2) The doubling bound is
correct (the lineage has $N=2^H$ atoms after $H$ restarts), but it gives $\lambda_t\ge N^{\log_2\kappa_-}\lambda_b$, not
$\lambda_t\le\lambda_b(1+c\log N)$ as the review's sketch states. (3) The obstruction is the O(N) running
$\lambda_{j+n}\approx\lambda_j+n(d-2)\log L$ together with $n_q\asymp\lambda$; with a coupling that runs only
logarithmically, as in E10, $\kappa_-$ would be $1+o(1)$ and the same tree would be paid. (4) In (R1-cov)
the same tree is harmless: merges of window-bearing parts do not restart the window ((T4)), and the
first overflow happens only after $\nu_{\max}\asymp\lambda^{p_2}$ pieces have accumulated, which pay for it.

*Status:* reconstructed here; confidence 90%. The risk is in the construction's geometry (exact
merge times under the hull rule), not in the counting, which has a large margin.

---
## 5. The constant chain

No source states a global order (roadmap §4.4; ER-024). The order below is chosen so that every
constraint found in P1–P9, D1–D3, E6–E10 and in §§3–4 is a condition on a later constant in terms of
earlier ones. Root-F's binders are $\exists\delta\ \forall\kappa\ \forall c_9\ \exists L,M\ \exists\beta_0$, and the order respects
them. The changes from version 3 are:
- the width $\omega_k$ and the a priori $\hat R_k$ (row 7);
- the late-scale constants of R3-04 (row 4);
- the renaming of R3-13: P3's constant becomes $c^{\rm P3}_1$ in row 6, and the flow amplitude is
  $c_9^{\rm flow}$ in row 10;
- $\epsilon\le\frac1{20}$ (row 10);
- the explicit quantifier prefix of §5.1 (R3-11).

| # | Constant(s) | Chosen depending on | Constraints (source) |
|---|---|---|---|
| 0 | $d\ge3$, $N\ge2$ | — | — |
| 1 | $\gamma\in(0,\min\{\frac{d-2}2,\frac12\})$; $\delta:=\gamma/2$; $\alpha:=\frac{d-2}2-\gamma\in(0,\frac{d-2}2)$ | $d$ | P4 (H.1); $\delta$ is Root-F's (surface S0-Q05). LFR-11: $\alpha_1$ is chosen in row 10 with $\alpha_1\le\gamma/(2(d-2))\le\gamma/2$, so $\gamma-\alpha_1\ge\delta$, and Root-F item 3 is monotone in $\delta$. |
| 2 | $\kappa,c_9$ | given by Root-F | — |
| 3 | $L\ge L_0(d)$; $a:=(1-L^{-2})^{-1}$ | $d$ (and $\kappa$, allowed by Root-F) | $L\ge3$ (P2 (4.26) [review]); $1<a<\frac32$ (P4 (5.22) [review]); $\log L>\frac12$ (P5 p. 500); $(d-2)\log L>1$ (used in §3.6); requirements of G-1, G-2. |
| 4 | Green's function and localization constants $\gamma_0,K_0,\dots,K_5,B_5,B_6,C_3,C_4,c_0^{\rm P2},\dots$; $\theta=(d-2)\log L$; $C_V=2\cdot14^d$; $s_*,s'$ (Lemma G, valid once $R_0\ge C(L)$); $c_0:=$ least integer with $c_0(1-L^{-1})\ge s_*+1$, $c_0\ge s'+1$; $D_0:=3c_0+4$; $c_{11},K_6$ of P7 Lemma 2.1 for $Z_0$ of diameter $<D_0$; the constants $C(c_0)$ of (M7): $90d$ in (2.20), (2.28), $7K_6$ and $90d$ in Lemma 2.5, the segments after (2.18) and before (2.27), $\lvert z-z_0\rvert\le D_0$ in (3.11) (R2-04, R3-04) | $d,L$ | G-1–G-6; P2, P3 (uniform in $M$, roadmap §3.4); P7 p. 507 ("the constants $c_{11},K_6$ depend on its size"). LFR-09: $K_6$ depends only on $d,L$, so row 7 has no cycle. |
| 5 | $\kappa_0$; $\kappa_{\rm flow}:=\max\{C_d(\kappa+1),\,16\kappa_0+16\}$; $m_0:=\lceil\log_L14d\rceil$; $\kappa_1\ge\max\{4d(2L+1)^d\kappa_{\rm flow},\,8dm_0\log(2L+1)\}$ | $d,L,\kappa$ | $\kappa\ge3\kappa_0+3$ and the conditions on $\kappa_1,m_0$ (P3 p. 81 [review]), $\kappa-5-8\kappa_0\ge\frac\kappa2$ (P6 p. 43 [review]); conversion of tree length to block count (§1.2 (F3)). UNCERTAIN: $\kappa_0$ independent of $M$ (roadmap §12). |
| 6 | $M=L^m$ | $d,L,\kappa_1$ | $M\ge2(7L)^d\kappa_1/\gamma_0$ (P3 (2.19) [review]); $8dB_0^{\rm G}c^{\rm P3}_1(2L+1)^dM^{-1/2}\le1$ (P3 p. 68 [review]; $c^{\rm P3}_1$ is P3's constant, R3-13); P7 (2.70) [review]; $M$ a power of $L$ (P5 H4) |
| 7 | $R_0\ge\max\{6K_1K_6,\,C(L)\}$, $r_0\ge5$; then the definitions $\hat R_k=R_0\hat\lambda_k^2$, $\omega_k=2[\hat R_{k-1}]+11$, $\mathrm{crit}_k$, $D_k=\sqrt d(2\rho_k+10+\omega_k)$ | 4 | P7 p. 514 [review]; P3 (2.14); Lemma G; R3-01 (the reviewer rechecked: no cycle) |
| 8 | $p_2:=2d+3$; $w_0:=\frac{p_2d}2+3d$; $p_0=p_1:=$ least even integer $\ge d^2+7d+2$ (so $p_R=2p_0-2w_0>p_2+2d$ and $2p_0-4>p_2$); $A_2:=1$; $C_\nu:=C_r=2A_2c'^{p_2}+1$ with $c'=c_*(1+6\theta)$; the strip lengths $h_j$ (§3.1); $C_{\rm ch},C_{\hat W}$ | $d,\gamma,L,M,c_0,R_0$ | (K) of §4.1; P5 (1.30) ($p_2\ge2d+2$); P7 pp. 502, 505 ($2p_0>2d+1$, $2p_0-4\ge2d-2$); (4.4); Lemma CH |
| 9 | $A_0$; $A_1=A_0/(4K_2B_5)$; $A_3$; $A'_3,A''_3$ | 4, 6–8 | P7 p. 505 (with $64K_1LMR_{k_1}$ replaced by $4K_1\hat W$; the exponent margin $p_R>p_2+2d$ leaves no further condition on $A_0$ beyond P7's relations); $A_3$ by P6 (3.9) [checked]; $A'_3,A''_3$ by (2.33)′, (2.62)′ |
| 10 | $\alpha_1\le\gamma/(2(d-2))$; $c_8$ small, with $\epsilon=c_8q/(1-q)\le\frac1{20}$; $c_9^{\rm flow}:=\min\{c_9e^{-\kappa_{\rm flow}},\,c_9^{\max}(d,\gamma,L,M)\}$ | $d,\gamma,L,M$ | P4 Thm 1 hypotheses ("$\alpha_1,c_8,c_9$ positive and sufficiently small", P5 p. 499 [checked]); $\alpha_1(d-2)\le\gamma$ (P3 p. 76 [review]); $c_9^{\rm flow}$ is the flow amplitude of §1.2 (F3), allowed because Root-F item 3 is monotone in $c_9$ (R3-13) |
| 11 | $\alpha_0,E_0,B,\bar\nu$ | 1–10 | outputs of P4 Thm 1 / P5 Thm 1; $E_0\ge4C_4B_6K_0K_5$ (P4 (5.39)) |
| 12 | $B_0\ge B^\sharp$ | 1–11 | $B^\sharp$ is the constant of the new boundary terms, "independent of $B_0$" (P7 p. 529 [checked]). It may depend on $p_0,A_0$ (rows 8–9 precede it; LFR-10). UNCERTAIN: independence of $H_0$ and of $c_1,c_2$ (ER-117). |
| 13 | $H_0$ | $B_0,K_0,M,L,\kappa_{\rm flow}$, $E$-constants | $H_0>2B_0K_0M^{-d}$ (P7 (1.2) [checked]); $H_k\lvert Z\rvert$ must absorb $E_{k+1,0}\lvert Z\rvert+\varepsilon^{-2}B_0K_0M^{-d}\lvert Z\rvert$, $\varepsilon^{-2}=3^dK_0e^{\frac32dL\kappa}$ (P7 (4.12) [checked]) |
| 14 | $c_1\ge\max\{c_1^{\rm P6},C_{39}\}$, $c_2\ge\max\{c_2^{\rm P6},C'_{39}\}$ (P6's cost coefficients) | 1–13 | P6 (3.9) (a larger cost coefficient keeps the bound true); refund P7 (3.8)–(3.9), "we can take the constants in the sum (3.8) large enough" (p. 520 [checked]); LFR-02. $C'_{39}$ may involve $B_0$ through the boundary terms. |
| 15 | $c_v:=M^d(H_0+c_1+3)$; $C_\sigma,C_E,C_w,C_2,C_3$; $C_R$ | 4–14 | Lemma B, converted to $\hat\lambda$ by $\lambda\le\hat\lambda\le\lambda+2$ (§3.4); §4.2; LF-4 Step 6 ($C_R$ after $B_0$; LFR-10) |
| 16 | $\lambda_*$, then $\beta_0:=\max\{e^{\lambda_*-1}/a,\ B\}$ | everything above | all "for $\hat\lambda_0\ge\lambda_*$" conditions of §§3.8, 4; $e^{-R_k}\le\beta_k^{-K}$ (P5 (2.19)); $\beta_ja>e^{6p_0}$ (P7 (2.25) [checked]); $\beta\ge16B_6K_5/(\alpha_0^2c_8)$ (P4 §5); P6 (4.16)–(4.17), (4.27); $\varepsilon^{-2}e^{-p_2(\beta_{k_0})}\le\frac12\beta_{k_f}^{-m-1}$ (§4.8); $\beta_{k_f}^{-2}\le c_9^{\rm flow}L^{-(k_f+1)(\frac{d-2}2+\delta)}$ (§1.2) |
| 17 | Root-C only: $\rho_2$, then $\rho_1,\rho_0$; enlarge $\beta_0$ | P9 p. 511 | $\rho_1\ge3\rho_2$, $\rho_0\le\gamma$, $\gamma>2(d-2)\rho_2$ (BIG §4) |

### 5.1 The quantifier prefix (R3-11)

"Chosen in the order of the table" becomes the following prefix. Three conventions apply:
- A constant that P5–P7 require to be "large enough" (or "small enough") is bound as
  $\exists X'\ \forall X\ge X'$ (resp. $\forall X\le X'$). Every condition on it is then a lower (resp. upper)
  bound in terms of earlier constants. The reconstruction document checks this monotonicity for each
  row, so that LF-3, LF-4, LF-5 and LF-7 can be combined at one choice.
- An output of a lemma is bound by $\exists$, directly after the constants it depends on.
- A derived quantity is a definition, not a binder: $a$, $\theta$, $c_0$, $D_0$, $\kappa_{\rm flow}$, $m_0$, $\hat R_k$,
  $\omega_k$, $\mathrm{crit}_k$, $D_k$, $p_2$, $w_0$, $p_0$, $p_R$, $A_2$, $C_\nu$, $h_j$, $A_1$, $c_9^{\rm flow}$, $c_v$, $C_\sigma$, $C_E$, $C_w$, $C_2$, $C_3$ and
  $\beta_0$.

$$\begin{aligned}
&\forall d\ge3,\ N\ge2.\ \ [\gamma:=\gamma(d),\ \delta:=\gamma/2,\ \alpha:=\tfrac{d-2}2-\gamma]\\
&\forall\kappa>0,\ c_9>0.\ \ \exists L_0\ \forall L\ge L_0.\ \ \exists(\gamma_0,K_0,\dots,K_6,c_{11},B_5,B_6,\dots,s_*,s',\kappa_0)\ \text{(rows 4–5: outputs of G-1–G-6, P2, P3, P7 Lemma 2.1, Lemma G)}.\\
&\exists m_0'\ \forall m\ge m_0'\ [M:=L^m].\ \ \exists R_0'\ \forall R_0\ge R_0'.\ \ \exists(C_{\rm ch},C_{\hat W}).\ \ \exists A_0'\ \forall A_0\ge A_0'\ [A_3,A'_3,A''_3].\\
&\exists\alpha_1',c_8',c_9^{\max}\ \forall\alpha_1\in(0,\alpha_1'],\ c_8\in(0,c_8'].\ \ \exists(\alpha_0,E_0,B,\bar\nu)\ \text{(P4 Thm 1, P5 Thm 1)}.\\
&\exists B^\sharp\ \forall B_0\ge B^\sharp.\ \ \exists H_0'\ \forall H_0\ge H_0'.\ \ \exists c_1',c_2'\ \forall c_1\ge c_1',\ c_2\ge c_2'.\ \ \exists C_R.\\
&\exists\lambda_*\ \forall\beta\ge\beta_0:=\max\{e^{\lambda_*-1}/a,B\}\ \ \forall\nu\in(0,1]\ \forall h\in S^{N-1}\ \forall\text{ admissible tori}:\ \ \text{LF-3, LF-4, LF-5, LF-6, LF-7, LF-8 hold.}
\end{aligned}$$

Remarks on the prefix:
- LF-4 (e) states that the new boundary terms are bounded by $B^\sharp$, where $B^\sharp$ is bound before $B_0$.
  This is the precise form of "a constant independent of $B_0$" (P7 p. 529). If $B^\sharp$ turned out to
  depend on $H_0$ or on $c_1,c_2$ (row 12, UNCERTAIN), the prefix would have a cycle there, and the
  boundary-term constant would need a separate bootstrap.
- $\kappa_0$ independent of $M$ is the other open independence (row 5). If it fails, $m_0'$ must be bound
  after $\kappa_0(M)$, which is a cycle only if $\kappa_0$ grows with $M$.
- Root-F's prefix $\exists\delta\,\forall\kappa\,\forall c_9\,\exists L,M\,\exists\beta_0$ is an instance: take $L:=L_0$, $m:=m_0'$, and
  the least admissible values of the later constants.

**Circularity check.**

1. *$\kappa$ versus $M$.* $\kappa_{\rm flow}$ (row 5) precedes $M$ (row 6). P1 p. 118 / P4 (H.4) ("$\kappa$
   arbitrarily large, depending on $M$") is read as the upper constraint $\kappa_1\le\gamma_0M/(2(7L)^d)$, which
   row 6 satisfies (roadmap §4.4, ER-025). There is no cycle, provided $\kappa_0$ does not grow with $M$
   (still open: it needs P3 p. 81).
2. *$c_0$, $K_6$, $R_0$* (LFR-09). P7's $k_2,k_3$ are kept, so $\mathrm{diam}_k(Z_0)<D_0=3c_0+4$ and $K_6$ depends
   on $c_0$. Since $c_0$ depends only on $s_*,s'$, which depend only on $d,L$ once $R_0\ge C(L)$, both are
   fixed in row 4, and $R_0\ge6K_1K_6$ in row 7 closes. $\omega_k$ is a function of $R_0$ and $\hat\lambda$.
3. *$p_0,A_0$ before $B_0$* (LFR-10). Rows 8–9 depend only on rows 1, 3, 4, 6, 7, so $B_0$ may depend on
   them.
4. *$B_0$, $H_0$, $c_1,c_2$, $c_v$, $C_R$, $\lambda_*$.* Rows 12 → 13 → 14 → 15 → 16. A cycle would arise only if
   $B^\sharp$ depended on $H_0$ or on $c_1,c_2$. P7 p. 529 fixes it from bounds on new boundary terms that
   come from small-field expansions (rows 4–11) and from the $R$ polymer expansion (size
   $\beta_k^{-m-1}$). To be confirmed when LF-4 is written (§9, part III).
5. *$A_2=1$.* P7's "$A_2$ large, which means $A_0$ large" (p. 520 [checked]) was used only to absorb
   $C\lambda^{2d+2}$ in (3.9). Here (3.9) goes through the refund, and the margins of LF-2 come from
   $p_R>p_2+2d$, $p_2\ge2d+3$ and $\beta$ large.
6. *Small-field outputs.* $\alpha_0,E_0,B$ (row 11) do not depend on the large-field constants of rows
   12–15: P4 Thm 1 is a small-field statement, and P5 Thm 1 adds only $B_0$.
7. *LF-2 and LF-4.* $\lambda_*$ depends on $A_2,A_3,A'_3,C_R,C_\nu,c_v,C_V,c_0,R_0,M,L,d,p_0,p_2,w_0,\alpha$, all fixed before
   $\beta$. No bookkeeping quantity depends on the running constants (R3-06); $\beta$ enters only through
   $\hat\lambda_0=\log(\beta a)+1$ and $\nu$ only through $\hat k_f$.
8. *Root-F binders.* $\delta=\gamma/2$ (row 1) depends on $d$ only. $L,M$ (rows 3, 6) may depend on
   $\kappa$, $c_9$ (allowed). $\beta_0$ comes last.

---

## 6. What is new or unproved

This is the single list of the statements of §§3–4 that no source proves. Each entry gives my
confidence that it is true as stated (or after a routine adjustment of constants), and the main
risk. Rows marked * are new or changed in version 4.

| # | Statement | Status | Confidence | Main risk |
|---|---|---|---|---|
| 1* | LF-2: the budget invariant with spines, clocks, three-way window states, unit reserves, the cap, merge strips and banks, on tori, under (G1), (G2), (B), (Rg), (K), (H-λ), (H-T) (§4) | reconstructed; proof given (§4.5 = REPAIRS-astra §B.3, checked) | 92% | the instantiation of the axioms, not the counting; the counting was checked by COUNTING-astra (bank ledger) and REPAIRS-astra |
| 2* | Lemma C4 (closure, horizon $h+1$, activation) and Lemma C (a)–(d), (e4), (f4), (g) | reconstructed (REPAIRS-astra §B.2, checked, adapted) | 90% | collapse time of a merged cluster under the exact region rules (the shadow map $e\mapsto e/L+2s_*r+2$) |
| 3 | Lemma G (seeds, radii $s_*,s'$, canonical hull rule) | reconstructed | 85% | P5 (2.4), (2.9), (2.45), P6 (2.3) rounding to $\pi'_{k+1}$-cubes; hull-induced merges |
| 4* | Lemma F: support of the kernels in $U^\sim$ and factorization (1.22) for $\omega$-separated components | asserted in P6 p. 16 for the one-step operator; propagation reconstructed | 85% | backgrounds in the main actions local only up to exponentially small terms (then: localized backgrounds by definition, difference into $\mathcal B$) |
| 5* | Removal overwrite of the generating set (§3.2) keeps the separation of P2 (1.1)–(1.3) | reconstructed | 88% | the exact separation constant of P2 (1.3), P5 (2.4) |
| 6 | Lemma S (lattice separation) | standard (Timár 2013 Lemma 2; Deuschel–Pisztora 1996), external to the library | 97% | none of substance |
| 7* | Lemma L (localization at the core) and (3.11)′ box by box with P7's path | reconstructed, conditional on Lemma F | 85% | as row 4 |
| 8* | Lemma P (component-wide path; not used under $\omega$-separation) | proved (REPAIRS-astra §C.1, checked) | 95% | none |
| 9 | LF-4 volume estimates and refund: (2.15)′, (2.33)′, (2.59)′, (2.60)′, (3.15)′, (3.17)′–(3.19)′ and (Rg) with $L_{\rm res}\le C_R\hat\lambda^{2d+1}$ (§3.8 Steps 1, 4, 6) | reconstructed (checked by the third review) | 87% | the analytic extension (3.11)–(3.19) with polynomial factors; dependence of $C_{39},C'_{39}$ on $B_0$ |
| 10 | Lemma CH (per component, all window points exposed) and the chain estimates (2.26)′–(2.30)′, (2.48)′–(2.49)′, (2.61)′–(2.62)′ | reconstructed (proof plan; outline items R3-03 (i)–(v)) | 78% | the conversion of a fine path into a self-avoiding chain in the multiscale graph; corner detours |
| 11* | Kept operators K1, K2 and the exponent $\kappa''$ (§3.3–§3.4); (D5) for them by the refund route | reconstructed (P7 p. 516 "it is also clear", p. 520 "in the same way") | 85% | that the volume bound "$\le1$" of p. 520 holds for K1 branches taken before $\chi''$ (only (1.24) restricts the window variables there) |
| 12* | Bookkeeping on the a priori sequence $\hat\lambda$ (R3-06, option B) is compatible with P7's estimates ((2.31), (2.32), $k_2$) and with Lemma B | reconstructed | 92% | none beyond constants |
| 13 | LF-4 (M1), (M7): ripeness trigger; late-scale constants with $D_0$ (R2-04, R3-04) | reconstructed | 90% | none beyond rows 9–10 |
| 14 | LF-4 (M4): coset average with an explicit two-chart section | reconstructed (P7 verbal) | 90% | measure bookkeeping for the complexified, non-orthogonal $R(\psi_0+\psi'_0)$ |
| 15 | LF-4 (M5): P7 Lemma 2.5 in full (no chains needed, R3-14 (a)) | sketched in P7 | 77% | the constant chase (2.64)–(2.72) |
| 16 | LF-4 (M6): the $R$ polymer expansion with non-small boundary terms | "almost completely standard" (P7 p. 528); PE and `pe_hole` proved in Lean | 87% | the activity lemma (roadmap §5.2) with connectivity modulo $\Omega_k^c\cap Y_k$ |
| 17 | P6 Prop 3.2 (ii) is false for merged components (§4.9) | finding | 92% | an unstated restriction elsewhere in P5–P7 |
| 18 | Proposition M: restarting the window at every merge (route R2) cannot be paid, for any window length P7 allows (§4.10) | finding (confirmed by the re-review) | 93% | exact merge times in the construction |
| 19 | Without a bound on the window's geometry, P7's chain argument fails (dense clusters); (R1-ν), (R1-atom) are insufficient (§2.7.3) | finding (confirmed by the re-review) | 85% | a drift bound coming from the cluster's own history |
| 20 | Frozen-threshold repair of P6 Thm 4 (LF-5 bound), with the a priori horizon $\hat k_f$ | reconstructed (agreed by Roland) | 95% | none for the bound; the analytic part of Thm 4 is P6's |
| 21 | The step $k=k_0$ (switch to complete backgrounds) | P6 p. 11 suggestion only | 85% | P4 §5 analysis with the $\nu_{k+1}$-term (ER-098, ER-099) |
| 22 | LF-1 for hard spins | reconstructed (P6: "very simple") | 90% | uniformity of $\gamma_0$ on generating sets with cross-layer bonds |
| 23 | LF-6: base case with large fields, hard spins, sphere chart via $P^\perp_\phi$ | reconstructed | 80% | P4 (2.48)–(2.50) analogue at $\lambda=\infty$; analyticity domains of the first step |
| 24 | LF-8 (b): $k_f=0$ | reconstructed | 90% | none of substance (one massive expansion) |
| 25 | $k_0\le0$ (no $R$ at all) | reconstructed | 95% | none |
| 26 | LF-8 (a) with the frozen threshold; final sum by (H6♭), P7 (4.9)–(4.14) and PE with volume weights | sketched in P7 §4 (details to P9); PE in Lean | 90% | the volume weights in the activity bound |
| 27 | Torus independence of large-field polymer terms | asserted (P4 (H.4)) | 90% | windings of large-field histories (only for $k>k_0$ and for pre-window components, §3.1) |
| 28* | Global constant chain of §5 with the prefix of §5.1 | reconstructed | 85% | $\kappa_0$ independent of $M$; $B^\sharp$ independent of $H_0$, $c_1$, $c_2$ |
| 29 | Admissibility after $R$ ("every surviving component has $K>0$", P7 p. 528) | in (A′) a corollary of LF-2 (ii) | 95% | none |

Some statements of §3 *are* in the sources (sketched): the step (LF-3) apart from (D6); LF-4 on
single-box windows apart from (M4)–(M6); LF-5 apart from the bound; LF-7's induction; LF-8 (a) apart
from the frozen bound.

The weakest links of the chosen route are now row 10 (Lemma CH, inside LF-4), row 15 (Lemma 2.5's
constant chase) and the shared risk of rows 4 and 7 (Lemma F). The counting (rows 1–2) is no longer
among them: its two blockers are repaired, and the repaired text was checked twice (REPAIRS-astra and
here).

---

## 7. Questions

**For Scott (rulings needed before the reconstruction document is approved):**

1. *Bookkeeping change.* (A′) changes P5–P7 in four ways:
   - it replaces P5's H6, the counter $K$, the functions $\kappa_{k,n}$ and the admissibility conditions
     by the budget invariant (H6′), with spines, clocks and three-way window states (pre-window,
     pending, active);
   - it replaces the trigger $K=0$ of $R$ by ripeness of an active covered window, with merge strips of
     $O(\log\lambda)$ scales before the core;
   - it generalizes P7's $R$ to windows containing up to $\nu_{\max}\asymp\lambda^{p_2}$ merged pieces;
   - it defines components as classes of "distance $<\omega_k$ cubes" (needed for factorization).

   Roadmap §3.5 asks for an explicit ruling for each reconstructed interface. Approve this for Def-7,
   LF-2 and LF-4?
2. *Def-7 form* (§8.2). Version 4 makes four design choices:
   - Def-7 is a predicate $\mathrm{IsRep}_k$ on representations, with $\mathcal R_k$ the set of densities that have
     one;
   - the bookkeeping is deterministic and runs on the a priori sequence $\hat\lambda$;
   - (D5) is required at every scale $j\le k$ (P7 uses (1.26) at the core scale);
   - LF-4 is existential.

   Recommendation: approve these. (Version 3's question 2, carrying bookkeeping in the history, is
   settled by R3-12: it is a function of the region history.)

**For Roland:**

3. *Merges.* §4.9 shows that P6 Prop 3.2 (ii) fails for merged components. §4.10 shows that keeping
   P7's single-box window and restarting it at every merge cannot be paid in the O(N) flow: the window
   length $n_q\asymp\lambda$ multiplies $\lambda$ by $\kappa_->2$ per restart. So $R$ must accept windows in which
   pieces merged. Do you know how Balaban intended merges to be handled in P5–P7, beyond E10's geometric
   clock? Or do you see an obstruction to $R$ on covered windows?
4. *Merge strips.* To keep the core of a window a union of separated boxes, a merge pushes the core at
   least $h=O(\log\lambda)$ scales past it. When this puts the core in the future, the component waits in
   a pending state and cannot be removed. Do you see an objection to this rule, or a standard way in
   Balaban's framework to treat small-field pockets enclosed by a hollow cluster directly?
5. *Locality of the large-field kernels* (new). P6 p. 16 asserts that the one-step operator's kernel
   depends only on the variables on $U^\sim$. The main action there contains the background
   $\phi_{k+1}(\mathbb B_{k+1}(\partial\Omega_{k+1});\tilde\psi)$, which is a minimizer on the whole torus. Is the locality meant
   exactly, through a localized variational problem, or up to exponentially small terms that P6
   (2.15)–(2.17) move into the boundary terms? Version 4 works with either (Lemma F), but the
   definition of the operators in the reconstruction document depends on the answer.

No other decision is blocked: the frozen-threshold repair is agreed, and the remaining choices are
covered by ruling 7.

---

## 8. Lean interfaces and design decisions

Three interfaces are stated here in mathematics: LF-2 (abstract, on tori), Def-7 (as a predicate on
representations), and LF-4 (existential). §8.4 says what becomes freezable when. Following the third
review: LF-2 is an internal lemma and is never frozen. Def-7 and LF-4 are designed here and defined in
full in the reconstruction document (§9). Nothing is frozen now.

### 8.1 LF-2 as an abstract, model-independent theorem on tori (internal lemma)

*Typing data.*
- Integers $d\ge2$, $L\ge2$, $M\ge1$ and $0\le k_0\le\hat k_f$.
- Reals $\theta_+\ge\theta_->0$, $\alpha>0$, $R_0\ge1$, $s_*,s'\ge0$, and $c_v,A_2,A_3,A'_3,C_R,C_\nu,c_d>0$.
- Naturals $c_0,p_0,p_2$, and a function $\lambda:\mathbb N\to\mathbb R$.
- Naturals $n_0,\dots,n_{\hat k_f}$ with $n_k=Ln_{k+1}$; the cube tori are $\mathbb T_k=$ `Torus d` $n_k$, with
  coarsening `blockMap`.

*Derived functions* (definitions):
- $r_k=\lceil R_0\lambda_k^2\rceil$, $\rho_k=c_0r_k$, $\mathrm{crit}_k=2\rho_k+10$, $\omega_k=2[R_0\lambda_{k-1}^2]+11$,
  $D_k=\sqrt d(2\rho_k+10+\omega_k)$;
- $n_q(j)=\min\{n\ge1:n\log L>\alpha^{-1}\lambda_j\}$, $n_2(j)=\min\{n:L^n>LM\mathrm{crit}_j\}$, and
  $k_1(t)=$ `Nat.findGreatest` $(\lambda c.\ c+n_q(c)\le t)\ t$;
- $\nu_{\max}(j)=\lceil C_\nu\lambda_j^{p_2}\rceil$, $h_j=\lceil\log_L(2\sqrt d\,\nu_{\max}(j)M(\mathrm{crit}_j+\omega_j))\rceil+2$;
- $w_0=\frac{p_2d}2+3d$, $p_R=2p_0-2w_0$, $g_k=\frac12A_3\lambda_k^{2p_0}$;
- $C_V=2\cdot14^d$, $v_j=c_vC_V\lambda_j\rho_j^{d-1}$, $w_j=v_j\rho_j$, $\sigma_k=\sum_{j>k}v_jL^{-(j-k)}$, $\tau_t=2A_2\lambda_t^{p_2}$;
- from the bookkeeping: $t^*$, $V_k$, $\nu$, $U$ (§3.5, §4.4).

*Abstract history.*
- Finsets $Z^{\rm pre}_k\supseteq Z_k\subset\mathbb T_k$ for $0\le k\le\hat k_f$, with $Z_0=\varnothing$ and $Z^{\rm pre}_k=Z_k$ for $k>k_0$.
- New-cube sets $\mathcal N_k$ and seed sets $B_\sigma$.
- Components are taken for the relation $d<\omega_k$. For each component $Z$ of $Z^{\rm pre}_k$ and of $Z_k$ there
  are numbers $G^{\rm pre}_k(Z)$, $G_k(Z)$, and bookkeeping data: spine (a finite list of segments in
  $(\mathbb R/n_k\mathbb Z)^d$), clocks $b,s$, and, for $k\le k_0$, a window state in
  `Pre | Pending q ν | Active q ν M`. The data are generated by (U1)–(U4) and (T1)–(T7). The choices of
  spine points and spanning trees are arbitrary data (which makes the lemma stronger; R3-12).
- For $k\le k_0$, an $R$-record marking each ripe component of $Z^{\rm pre}_k$ removed or kept.

*Hypotheses* (premises of this internal lemma only):
- (H-λ) $\theta_-\le\lambda_{k+1}-\lambda_k\le\theta_+$ for all $k$; $\hat k_f-k_0<\lambda_{k_0}$; $\lambda_{\hat k_f}\le\frac d2\lambda_{k_0}+c_d$.
- (H-T) $n_k\ge4\nu_{\max}(k)(\mathrm{crit}_k+\omega_k)+4$ for $1\le k\le k_0$.
- (G1) $Z^{(0)}_{k+1}=\bigcup_ZB_Z\cup\bigcup_{q\in\mathcal N_{k+1}}B_q$ over the components $Z$ of $Z_k$. Here $B_Z$ is $*$-connected
  with $Z^\uparrow\subset B_Z\subset N_{s_*r_k}(Z^\uparrow)$, and $B_q$ is $*$-connected with $q\in B_q\subset N_{s'r_k}(\{q\})$.
- (G2) For $k+1\le k_0$, $Z^{\rm pre}_{k+1}$ is the canonical hull closure of $Z^{(0)}_{k+1}$ at size $\mathrm{crit}_{k+1}$ (§3.5). For
  $k+1>k_0$, $Z^{\rm pre}_{k+1}=Z^{(0)}_{k+1}$.
- (B) For every component $Z'$ of $Z^{\rm pre}_{k+1}$ ($0\le k<\hat k_f$):
  $G^{\rm pre}_{k+1}(Z')\ge\sum_{Z\subset Z'}G_k(Z)+g_k|\mathcal N_{k+1}\cap Z'|-c_v\lambda_{k+1}|Z'|$. The sum is over the components $Z$ of
  $Z_k$ with $Z^\uparrow\subset Z'$, and is empty for $k=0$.
- (Rg) For $k\le k_0$: the components of $Z_k$ are those of $Z^{\rm pre}_k$ minus the removed ones. Every ripe
  component is removed or kept. A kept one has the same set, bookkeeping (U4), (T6), and
  $G_k\ge G^{\rm pre}_k-C_R\lambda_k^{2d+1}+A'_3\lambda_k^{p_R}$. A non-ripe one has $G_k=G^{\rm pre}_k$. For $k>k_0$, $G_k=G^{\rm pre}_k$.
- (K) $p_2\ge2d+3$; $p_R>p_2+2d$; $2p_0>p_2$; $c_0(1-L^{-1})\ge s_*+1$; $c_0\ge s'+1$; $C_\nu\ge2A_2c'^{p_2}+1$ with
  $c'=(1+\frac{\theta_+}{\alpha\log L})(1+6\theta_+)$.

*Conclusion.* For all typing constants satisfying (K) there is $\lambda_*$, depending only on them, with the
following property. For every $\lambda$ with $\lambda_0\ge\lambda_*$ satisfying (H-λ), every family of tori satisfying
(H-T), and every history satisfying (G1), (G2), (B), (Rg):
- (i) for $1\le k\le k_0$ and every component $Z$ of $Z_k$: $t^*(Z)>k$ and $G_k(Z)\ge\tau_{t^*(Z)}+V_k(Z)+\nu(Z)+U(Z)$;
  for every component of $Z^{\rm pre}_k$ the same holds with $t^*(Z)\ge k$;
- (ii) for $k_0\le k\le\hat k_f$ and every component $Z$ of $Z_k$: $G_k(Z)\ge A_2\lambda_{k_0}^{p_2}+2\sigma_k\ell(Z)+\sum_{j=k+1}^{\hat k_f}w_j$;
- (iii) every ripe component of $Z^{\rm pre}_k$ is Active, has core $q=k_1(k)$, and at scale $q$ its lineage is a
  union of pairwise $\omega_q$-separated boxes (Lemma C (e4)–(g));
- (iv) consequently $G_k(Z)\ge2A_2\lambda_k^{p_2}$ for $k\le k_0$, $G^{\rm pre}_k(Z)\ge2A_2\lambda_k^{p_2}+1$ for every ripe $Z$, and
  $G_k(Z)\ge A_2\lambda_{k_0}^{p_2}$ for $k_0\le k\le\hat k_f$.

*Instantiation plan.*
- The flow's region history (§3.2) with its deterministic bookkeeping (§3.5) is an abstract history
  with $\lambda=\hat\lambda$ and $\theta_\pm=(d-2)\log L$.
- (H-λ) and (H-T) are §4.1 (from P4 (H.6), P5 p. 490 and (3.0)).
- (G1)–(G2) are Lemma G.
- (B) is Lemma B (P6 (3.9)–(3.11)) converted to $\hat\lambda$, and LF-6 (ii) at $k=0$.
- (Rg) is LF-4R. (K) is §5.

By AGENTS.md hard rule 4, (G1)–(H-T) are hypotheses of this internal lemma only. No frozen statement
carries them; LF-3, LF-4 and LF-5 discharge them in their proofs.

*Drafting status.* The third review listed the conditions for drafting this lemma in Lean: C-01,
C-02, C-04, C-05, R3-01, R3-05 and R3-12. All of them are in version 4. LF-2 can be drafted now, as an
internal lemma, after the author's ruling 1 (§7).

### 8.2 Def-7: design decisions (R3-06 … R3-10)

One line per decision; the full definitions belong to the reconstruction document.

| # | Decision | Where |
|---|---|---|
| R3-06 | **Causality: option B.** All bookkeeping (ripeness, windows, strips, budget thresholds, region radii of the bookkeeping, horizon) runs on the a priori $\hat\lambda_j=\log(\beta a)+1+j(d-2)\log L$ and $\hat k_f$. Running constants enter only the analytic objects, at scales $\le k$; "$k\le k_0$" is the test $\beta_k\nu_k\le1$. No separate causality lemma is needed: Def-7 at scale $k$ mentions the running constants only up to $k$. | §3.1 |
| R3-07 | **(D5)** is P5 (1.26)–(1.27) for the localized operator $\mathbb T_j(Z,\mathfrak a)$, $\mathfrak a\in\mathfrak H_j(Z)$, with $\chi$ the indicator of the domain (1.24)–(1.25) localized to $Z$. The index set of (1.27) is $\mathfrak H_j(Z)$, all localized histories generated by the rules with final component $Z$ (P5's "maximal set"). It is required **at every scale $j\le k$**, because P7 bounds the operator after $R$ through (1.26) at the core scale (p. 519). | §3.3, §3.6 |
| R3-08 | **Kept operators**: (K1) the old localized operator times the characteristic functions of the branch, up to the first large-field branch among (2.18), $S''_k$, $Q''_{k_1}$, $\chi''$; (K2) the operator (3.7) times the (3.20) term and the main-action exponential. **Exponent** for both: $\kappa''=\kappa_k-C_R\hat\lambda_k^{2d+1}+\gamma$, with $C''=C\cdot C_{\rm dec}$ (refund form; one route). **Removal** overwrites $\Omega_j,\Omega''_j$ by $\cup Z$ and $Z_j$ by $\setminus Z$ for $j\le k$; the $\omega_k$-separation keeps the generating-set separation. | §3.2–§3.4 |
| R3-09 | **Objects Def-7 needs**: the table below, in the order in which they must be defined. | below |
| R3-10 | **Def-7 is a predicate** $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep},\rho)$ on a representation structure, over families indexed by admissible tori; $\mathcal R_k:=\{\rho:\exists\,\mathrm{rep},\ \mathrm{IsRep}_k(\mathsf c,\mathrm{rep},\rho)\}$. **LF-4 is existential** (§8.3), and (Rg) is the internal lemma LF-4R. P7's $R$ is the construction inside the proof. | §3.6, §8.3 |
| R3-11 | **Constant prefix**: §5.1. | §5.1 |

**The representation structure.** $\mathrm{rep}=(\mathfrak s,\mathfrak A,\mathcal B)$, a family over admissible tori:
- $\mathfrak s$: the small-field data up to $k$: $(\beta_j,a_j,\nu_j)_{0\le j\le k}$, $E_k$, $(\mathcal E^{(j)},\mathcal M^{(j)})_{j\le k}$ and
  $(\mathcal R^{(k)}_n)_{n\le m}$;
- $\mathfrak A$: a finite set of admissible region histories up to scale $k$ (§3.2). The bookkeeping, the
  operators $\mathbb T_k(\mathbb A)$, $\kappa_k$, $C$ and $G_k$ are *functions* of $(\mathfrak s,\mathbb A)$, not data;
- $\mathcal B$: the boundary terms $\mathcal B^{(k)}(\mathbb A)$, which are data constrained by (D7).

$\mathrm{IsRep}_k$ is (D1), (D2), (D3), (D5) at every $j\le k$, (D6), (D7), (D8), (D9) of §3.6. The torus
coherence (D8) is a condition on the family; it is what makes the existential LF-4 compatible with
Root-F item 5.

**Objects that Def-7 needs (R3-09), with their status.** "Definition" means an explicit formula or
set function. "$\exists!$ first" means the object is "the unique …" and is defined only after its
existence-and-uniqueness theorem, landing with a characterization theorem (hard rule 4).

| # | Object | Source | Status |
|---|---|---|---|
| 1 | Tori, cube tori, blocks, `blockMap`, `jBlock`, $\mathcal D_k$, $d_k$ | Def-1, Def-2; `Lattice/Blocks.lean`, `Multiscale/GeneratingSet.lean` | landed / frozen (Def-1, Def-2) |
| 2 | $\mathcal D_k(\mathrm{mod}\,\Omega^c)$, $d_k(X\,\mathrm{mod}\,\Omega^c)$ | P5 (1.33)–(1.34) | definition (not covered by `IsPolymer`) |
| 3 | Generating sets $\mathbb B_k$ and $\mathbb B_k(X)$ (minimal generating sets), $\mathbb B_{k+1}(\partial\Omega_{k+1})$, $\mathbb B_{k_1,k}$ | P2 (1.1)–(1.3); P6 (2.15); P7 (2.13) | `GeneratingSet` landed; the minimal sets are definitions |
| 4 | Region calculus: $\sim$, $\approx$, $\pi'_{k+1}$, P5 (2.2)–(2.9), (2.45), P6 (2.3)–(2.5), components (relation $d<\omega$), hull rule, removal overwrite | P5, P6; §3.1–§3.2 | definitions |
| 5 | Histories, $R$-records, localized histories $\mathfrak H_k(Z)$, bookkeeping (spines, clocks, states, tie-breaks) | §3.2, §3.5 | definitions (by recursion) |
| 6 | Running constants and small-field data $\mathrm{SF}_k$ (Def-6) | P4 (H.1)–(H.7), P5 H2–H4; `Flow/*` | Def-6 (phase 3); the RG recursion is landed |
| 7 | Background fields $\phi_k(\mathbb B;\tilde\psi)$, $\psi^{(j)}_k$, $\psi(\mathbb B_j,\mathbb B'_k;\psi')$ (Def-5) | P2 Props 1.1, 3.1, 4.1; BACKGROUND.md (I-1, I-2) | **$\exists!$ first** (Def-5; BACKGROUND.md v2) |
| 8 | P7's $\psi^0_k$ (2.34), $\phi^0_k$, $\psi^0_{k_1,k}$, $\phi^0_{k_1,k}$ | P7 §2 | **$\exists!$ first** (instances of item 7 with constraints on $Z_0$; P7 Lemma 2.1) |
| 9 | Multiscale action $A^*_{k}(X,\mathbb B;\psi,\phi)$, $\delta A^*$, the fluctuation forms | P2, P5 (1.5)–(1.6), (1.27) | definitions (given item 7) |
| 10 | Analyticity spaces (1.36)–(1.37), $\Delta^c_k(U;1,\varepsilon_k)$, $\tilde\Psi_j(X;\delta)$, $\Xi$ | P5 p. 497 ("no point in formulating this … awkward definition"), P1 (2.15), (2.20), P3 §4 | definitions, to be written (Def-4) |
| 11 | Characteristic functions $\chi_k$ (P5 (1.18)–(1.19)), $\chi'_{k+1}$ (P5 (2.11)–(2.13)), $\chi'^{(k)}$ (P5 (2.5)), P6 (2.1) | P5, P6 | definitions (given items 7, 10) |
| 12 | $R$'s characteristic functions $\tilde\chi_k$ (2.18), $\chi'_{k_1,\frac12}$ (2.21), $\chi''$ (2.61), $\chi_{Z_0}$ (3.2); $\psi_0$ (2.19); $Z_0$, $Z'''_0$, $k_2$, $k_3$ | P7 §§2–3 | definitions (given items 7–8) |
| 13 | One-step operator $\mathbb T^{(k)}$, reference measures on history-dependent index sets, $\mathbb T_k$ by recursion, localized $\mathbb T_k(Z,\mathfrak a)$ | P5 (2.47), P6 (3.2)–(3.3) | definitions (given items 3–11) |
| 14 | $R$'s transformed operator (3.7), the coset average (M4), $\tilde E^{(k)}_0$ (log of (3.4)), kept operators K1, K2 | P7 (3.4)–(3.7), (3.20); §3.3 | definitions; the coset average needs the section-independence lemma first |
| 15 | $\kappa_k$ (P6 (3.9)–(3.10)), $C$ (P6 (3.11)), $\kappa''$, $G_k$ | P6; §3.4 | definitions |
| 16 | Boundary terms $\mathcal B^{(k)}$ | P5 H7 | data in $\mathrm{rep}$, constrained by (D7) |

The order of definition is 1–5 (model-free) → 6–8 (small field, $\exists!$ theorems) → 9–12 → 13–15 →
Def-7. Items 7–8 are the only "unique minimizer" objects; everything else is explicit.

### 8.3 LF-4: $R$ on covered windows (existential form)

Fix $d\ge3$, $N\ge2$ and the constants bound by the prefix of §5.1 up to $C_R$. There is $\lambda_*$,
depending only on these constants, with the following property. Let $\beta\ge\beta_0:=\max\{e^{\lambda_*-1}/a,B\}$,
$\nu\in(0,1]$, $h\in S^{N-1}$, and $k\ge1$. Let $\mathrm{rep}_{k-1}$ with $\mathrm{IsRep}_{k-1}(\mathsf c,\mathrm{rep}_{k-1},\rho_{k-1})$, let
$(\rho,\mathrm{rep})$ be the output of LF-3 for it, with $\mathrm{IsRep}^{\rm pre}_k(\mathsf c,\mathrm{rep},\rho)$, and suppose $\beta_k\nu_k\le1$ for the
data of $\mathrm{rep}$. Then there exist $\rho'$ and $\mathrm{rep}'$, families over the same admissible tori, such that:
- (a) $\int\rho'\,d\psi_k=\int\rho\,d\psi_k$ on every admissible torus, identically in $(h,g)$;
- (b) $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep}',\rho')$;
- (c) the small-field data of $\mathrm{rep}'$ equal those of $\mathrm{rep}$, except that $\mathcal R^{(k)}_m$ is replaced by
  $\mathcal R^{(k)}_m+\mathcal R''^{(k)}_m$, and $\mathcal R''^{(k)}_m$ satisfies the bounds of P5 H4;
- (e) the boundary terms of $\mathrm{rep}'$ created at scale $k$ are bounded as in (D7) with $B^\sharp$ in place of
  $B_0$.

Remarks:
- The hypotheses are source premises: the inductive class at $k-1$, and $\beta_k\nu_k\le1$. (RQ1)–(RQ5) are
  consequences of (D6) and Lemma C, not premises.
- (Rg) is the internal lemma LF-4R, used in the proof together with LF-2 (ii).
- LF-7 composes LF-3 and LF-4 by choice at each scale. The torus coherence (D8) is part of
  $\mathrm{IsRep}_k$, so the choice is coherent across tori.

*Status:* design. The proof is §3.8 (Steps 0–6) together with P7 §§2–3. The statement is not to be
frozen until Def-7 is frozen, $B^\sharp$ is settled (§5 row 12), and Lemma CH, Lemma F and the §3.8
re-derivations are written at full length in the reconstruction document.

### 8.4 What becomes freezable when

| Interface | Freezable after | Draftable in Lean |
|---|---|---|
| LF-2 (abstract, §8.1) | never frozen (internal lemma; its hypotheses are proof steps of the flow, hard rule 4) | now, after ruling 1 (§7): model-independent, on `Torus d n` |
| Lemma S, Lemma V, Lemma P, region calculus (Lemma G as set functions), bookkeeping (§3.5), Lemma C4, Lemma C | not frozen (internal) | now; Lemma G after RD part I (§9) |
| LF-1 (action lower bounds) | Def-5 and generating sets frozen; RD §II.4 approved | after Def-5 |
| Def-7 | RD parts I–II approved; Def-5 (with I-1, I-2), Def-4 and Def-6 frozen; rulings 1–2 (§7); Lemma F settled (question 5) | after RD part II |
| LF-3 (one step), LF-5 (frozen regime) | Def-7 frozen | after Def-7 |
| LF-4 (existential, §8.3) | Def-7 frozen; §5 row 12 ($B^\sharp$) settled; RD part III approved (Lemma CH, Lemma F, the re-derived estimates, Lemma 2.5, Lemma 3.1, (M6)) | after Def-7 |
| LF-6 (base case) | Def-7 frozen; RD §II.7 approved | after Def-7 |
| LF-7 (flow), LF-8 (last step) | LF-3–LF-6 frozen; PE frozen; the P9 interface for $\mathcal P$ | last |

None of these can enter a surface now.

---

## 9. Outline of the reconstruction document (next deliverable)

The reconstruction document ("RD", roadmap §4.5) contains the closed definitions and full proofs from
which Def-7 and LF-1, …, LF-8 are drafted. It follows the architecture of this document and cites P5–P7
page by page wherever their argument is used unchanged. It has four parts. Each part is reviewed
independently before the interfaces it feeds are drafted for approval. Sizes are estimates in journal
pages.

| § | Content | Objects defined | Statements proved | Sources | Size |
|---|---|---|---|---|---|
| **I** | **Geometry and counting (model-free)** | | | | **30** |
| I.1 | Conventions; the constants and the prefix of §5.1, with a monotonicity check per row | constants, prefix | monotonicity of each "large/small enough" condition | §5 | 4 |
| I.2 | Tori, cube tori, neighbourhoods, small sets, hulls, components (relation $d<\omega_k$), $\mathcal D_k(\mathrm{mod}\,\Omega^c)$ | R3-09 items 1–2, 4 (part) | disjointness of $U^{\sim4}$ for distinct components; (3.0) | P5 (1.2), (1.33)–(1.34); Def-1, Def-2 | 4 |
| I.3 | Region calculus as set functions: P5 (2.2)–(2.9), (2.45), P6 (2.3)–(2.5), seeds; minimal generating sets; removal overwrite | items 3–4 | Lemma G (radii $s_*,s'$; separation of $\mathbb B_k$ incl. removals and $\mathbb B_{k_1,k}$); Lemma S; Lemma P | P5 §2, P6 §2, P7 (2.1), (2.13); Timár 2013 | 8 |
| I.4 | Histories, $R$-records, localized histories $\mathfrak H_k(Z)$; deterministic bookkeeping; window states, (T1)–(T7) | item 5 | Lemma C4, Lemma C | §3.2, §3.5; REPAIRS-astra §B | 6 |
| I.5 | LF-2 on tori, with the instantiation of (H-λ), (H-T) | — | LF-2 (§4), Lemma V, Lemma T′ | §4 | 8 |
| **II** | **Analytic objects, operators, Def-7** | | | | **35** |
| II.1 | Small-field data and running constants; comparison with $\hat\lambda$, $\hat k_f$ | item 6 (recap of Def-6) | $\lambda\le\hat\lambda\le\lambda+2$, $k_f\le\hat k_f\le k_f+1$ | P4 (H.6); `Flow/*` | 2 |
| II.2 | Background fields | items 7–8 | $\exists!$ and characterization (cited from the Def-5 work, I-1, I-2); P7 Lemma 2.1 for $\psi^0_k$ | P2 Props 1.1, 3.1, 4.1; BACKGROUND.md; P7 §2 | 4 |
| II.3 | Analyticity spaces; characteristic functions of the step and of $R$ | items 10–12 | measurability; the Lemma 3.1 [P1] comparison used in P7 p. 502 | P5 (1.18)–(1.19), (1.36)–(1.37), (2.5), (2.11)–(2.13); P6 (2.1); P7 (2.18), (2.21), (2.61), (3.2) | 6 |
| II.4 | LF-1, action lower bounds for hard spins | — | LF-1 | P6 Prop 3.1, P2 Prop 2.2, D3 Lemma 20 | 4 |
| II.5 | Operators: multiscale action, one-step operator, reference measures, recursion, localization; $\kappa_k$, $C$; budget | items 9, 13, 15 | Lemma F; H5 properties; (1.27) for $\mathfrak H_k(Z)$; Lemma B with the $\hat\lambda$ conversion; (D5) for a step (P6 (3.4)–(3.10)) | P5 (2.47), H5; P6 §3 | 10 |
| II.6 | Def-7: the representation structure, $\mathrm{IsRep}_k$, $\mathcal R^{\rm pre}_k$, $\mathcal R^\flat_k$ | Def-7 | — | §3.6, §8.2 | 3 |
| II.7 | LF-6, the base case (decomposition at $k=0$, sphere chart via $P^\perp_\phi$) | base rule | LF-6 | E8 §1, D2 §3.4, D3 Lemmas 11, 13; P4 (2.42)–(2.50) | 6 |
| **III** | **$R$ on covered windows (LF-4)** | | | | **50** |
| III.1 | Ripe components, (RQ1)–(RQ5); composition and core (P7 (2.6)–(2.9)) | — | Step 0 with Lemma F | P7 pp. 498–500 | 3 |
| III.2 | Renormalization of the window actions | $C_{k_1,k}$ | (2.15)′ | P7 (2.10)–(2.16) | 3 |
| III.3 | Late scales: $k_2,k_3$, $Z_0$, $Z'''_0$; P7 Lemmas 2.1, 2.2 with size $D_0$ | — | (M7) constants (R2-04, R3-04) | P7 pp. 498, 502–507 | 4 |
| III.4 | Chains | — | Lemma CH in full (R3-03 (i)–(v)); (2.26)′–(2.30)′; Lemmas 2.3′, 2.4′ ((2.48)′–(2.49)′) | P7 pp. 503–509 | 8 |
| III.5 | The decompositions (2.18), $S''_k$, $Q''_{k_1}$, $\chi''$ and the kept operators K1 | K1 | small factors; (2.33)′, (2.62)′; (D5) for K1 | P7 pp. 501–505, 512, 516 | 5 |
| III.6 | Cancellation of main actions | $\psi^0_{k_1,k}$, $\delta\psi$ | (2.59)′, (2.60)′, P7 (2.51)–(2.58) | P7 pp. 509–512 | 5 |
| III.7 | P7 Lemma 2.5 in full | — | Lemma 2.5 | P7 pp. 512–516; E9 (1.29), (1.89); D2 Lemma 3.13 | 5 |
| III.8 | The normalization of $R$, the operator (3.7), the refund certificate; the kept operators K2; $\kappa''$ | (3.7), $\tilde E^{(k)}_0$, K2, $\kappa''$ | (3.10) with the refund; LF-4R (Rg) | P7 pp. 517–520 | 4 |
| III.9 | The core: Lemma L and (3.11)′; the analytic extension; the coset average | coset average | Lemma L; (3.11)–(3.19)′; Lemma 3.1 (M4) | P7 pp. 520–525 | 6 |
| III.10 | Polymer expansion and exponentiation; new boundary terms; $\mathcal R''_m$ | activities | (M6) with `pe_hole` and the activity lemma; LF-4 (a)–(e) assembled; $B^\sharp$ | P7 pp. 525–529; E10 (1.90)–(1.97); POLYMER.md | 7 |
| **IV** | **The flow and the end** | | | | **15** |
| IV.1 | LF-3, one step $1\le k<k_0$: statement; the (D6) part from LF-2 (i); the analytic part cited to P5–P6 | — | LF-3 (D6) | P5 §§2–3, P6 §§2–4 | 3 |
| IV.2 | LF-5, the frozen regime and the step $k_0$ | — | LF-5 | P6 Thm 4, p. 11, p. 21; §4.7 | 4 |
| IV.3 | LF-7, the flow; torus coherence | — | LF-7 | P7 Thm 5; P4 Prop 5.1 | 2 |
| IV.4 | LF-8, the last step and $k_f=0$ | — | LF-8 | P7 §4; P9 §4; PE | 6 |
| | **Total** | | | | **130** (range 110–140) |

*Order of writing.*
1. Part I first. It is model-free, enables the Lean drafting of LF-2 and of the region calculus, and
   settles the bookkeeping for the author's ruling.
2. Then II.1–II.6, which give Def-7 its prerequisites. Item 7 waits for the Def-5 work (BACKGROUND.md v2,
   I-1, I-2).
3. Then Part III, the largest part and the analytic risk, and with it §5 row 12 ($B^\sharp$).
4. Then II.7 and Part IV.

*Size.* Version 3 estimated 70–95 pp. The increase comes from two sources. The objects of R3-09 must be
written as closed definitions (Part II, about 20 pp that version 3 assumed could be cited). Part III
also gets more detail: Lemma CH in full, Lemma L, and the kept operators.

---

## Review dispositions (v1 → v2)

* **LFR-01** (BLOCKER) — Accepted and extended: the volume terms are handled by the cap $\nu\le\nu_{\max}$ (they stay $O(1)$) and by the refund for (2.15)/(3.9) (§3.8 Steps 1, 4, 6); the shape terms (P7's chain argument), which the review did not list, are handled by Lemma CH and Lemma H (in version 3 the merge-free strip makes Lemma H unnecessary, R2-01); $\nu$ enters (H6′) as one unit of reserve per window piece paying overflow restarts, and (Rg) becomes $L_R\le C_R\lambda^{2d+1}$ after the refund.
* **LFR-02** — Accepted: the refund route is explicit (§3.8 Step 6, window certificate), with $c_1\ge C_{39}$, $c_2\ge C'_{39}$ in §5 row 14; P7's alternative $C\lambda^{2d+2}$ bound is not used.
* **LFR-03** — Accepted and resolved: the pooled-reserve route (R2) was developed (§2.7.2) and is refuted by Proposition M (§4.10); the summary and §2.6 are reworded; the review's doubling bound $\lambda_t\le\lambda_{b'}(1+c\log N)$ is corrected to $\lambda_t\ge N^{\log_2\kappa_-}\lambda_{b'}$ on the merge tree.
* **LFR-04** — Accepted: §4.9 now uses P7 p. 498's reading, gives the upper budget bound and $K(Z')\le((2^{1/p_2}-1)/\theta+o(1))\lambda+2$, treats the per-component reading, proves existence by a translation argument, adds the diagnosis; confidence 92%.
* **LFR-05** — Accepted: Lemma B is stated with $-c_v\lambda_{k+1}|Z'|_\#$ (§3.4).
* **LFR-06** — Accepted: (U3) resets $s$ only for non-point spines (§3.5).
* **LFR-07** — Accepted: canonical simultaneous, iterated hull rule with termination and determinism (§3.5); hull-induced contacts are merges in (U2).
* **LFR-08** — Accepted in the form $\mathrm{crit}_k=2\rho_k+10$, spine radius $\rho_k+4$, $\rho_k\in\mathbb N$, and short event spines replaced by a point (§3.1, §3.5, §4.3).
* **LFR-09** — Accepted in modified form: P7's $k_2,k_3$ are kept (moving $k_2$ would break P7 (2.2), (2.4)); $n_2:=\min\{n:L^n>LM\mathrm{crit}\}$ puts $[k_2,k]$ in the single-box phase; $\mathrm{diam}(Z_0)<D_0=3c_0+4$; $c_0,D_0,K_6$ are fixed in row 4 from $d,L$, so $R_0\ge6K_1K_6$ in row 7 has no cycle.
* **LFR-10** — Accepted: $p_2,w_0,p_0,A_2,C_\nu,A_0,A_1,A_3,A'_3$ precede $B_0$ (rows 8–9); $c_1,c_2,C_R$ follow it (rows 14–15).
* **LFR-11** — Accepted: $\delta:=\gamma/2$, $\alpha_1\le\gamma/(2(d-2))$ chosen in row 10 after $L,M$.
* **LFR-12** — Accepted: LF-8 rests on (H6♭), P7 (4.9)–(4.14) and PE with volume weights; D3 Lemma 15 is not used (only Lemma 14's geometry may be); the Lean PE theorems are cited.
* **LFR-13** — Accepted: $\alpha\in(0,\frac{d-2}2)$.
* **LFR-14** — Accepted: $\lambda_j:=\lambda_{k_f}+(j-k_f)(d-2)\log L$ for $j>k_f$ (§3.1).
* **LFR-15** — Accepted: the final decomposition (3.20) ($S''_k$ on $Z'''_0$) and the failure case of (2.22) are in the $R$-record (§3.2).
* **LFR-16** — Accepted: (a) gain $A_3(\log\beta_k)^{2p_0}$, with $g_k:=\frac12A_3\lambda_k^{2p_0}$; (b) LF-3 for $1\le k<k_0$; (c) P5/P7 index conventions noted in §1.2.
* **LFR-17** — Accepted: confidences revised (§6), length revised to 70–95 pp (§2.5).
* **LFR-18** — Noted: the parts of §4 the review verified are kept; the head of §4 lists what changed.

*MERGES-astra.md.* Adopted: the reading of E10 (geometric $K$, (1.80), (1.84)–(1.88)); the counterexample's upper bound and the coefficient $2^{1/p_2}-1$; the atom attribution of covers (Lemma C); the window certificate with the refund (Step 6); the critique of resetting $\nu$ at a gain when the window starts at the gain; the frozen transfer. Not adopted: an unbounded atom tally (P7's chain argument then fails, §2.7.3) and the per-atom treatment of (2.60), (3.19) as losses (unnecessary under the cap). Its "option (b), open, 45%" is settled negatively by Proposition M.

## Re-review dispositions (v2 → v3)

* **R2-01** — Adopted: ripeness forbids the window core within $h_\mu$ scales after a lineage merge (§3.5 (W3), Lemma C (e)–(f)); the core is a union of separated boxes and every window point is exposed, so Lemma H is not needed (its plan (H2) is kept as a backup, §3.8). The counting closes (§4.5 Case 2a): the new merge's $O(h)$ strip is paid by the freed threshold, and strips of earlier merges crossed when parts with different cores combine are paid by banks of $\frac12\tau_\mu$ per merge after the core (an addition to the re-review's proposal; the freed threshold alone does not cover that case).
* **R2-02** — Adopted: Lemma CH (a) is argued per $*$-component of the obstacle, and Lemma S (lattice separation) is proved in Lemma G.
* **R2-03** — Adopted: $D_k=\sqrt d(2\rho_k+10)$ (§3.1, §4.3).
* **R2-04** — Adopted: (M7) and §5 row 4 list the constants of (2.20)/(2.28) and of Lemma 2.5 that depend on $\mathrm{diam}_k(Z_0)$.
* **R2-05** — Adopted: Proposition M is compared level by level; a remark shows that (R2) fails for every window length P7's estimates allow (via (3.11): $n_1\ge\lambda/(2\alpha\log L)$, so $\kappa>\frac32$).
* **R2-06** — Noted: the reviewer withdraws the LFR-03 doubling sketch; no change.
* **R2-07** — Noted: the chain obstruction is confirmed; no change.
* **R2-08** — Adopted as a qualification in §2.7.3: MERGES-astra.md's objection (i) is weaker than stated, and the shape defect is the decisive one.
* **R2-09** — Noted: Lemma C, the refund and the re-derived volume estimates checked; no change.
* **R2-10** — Noted: version 2's LF-2 checked; version 3's additions (strip shift, banks) are listed at the head of §4 for the next review.
* **R2-11** — Noted: the constant chain checked; the two open independences ($\kappa_0$ of $M$, $B_0$ of $H_0$) remain in §5.
* **R2-12** — Adopted: (2.62)′ uses $\lambda_i\ge\lambda_{k_1}$ directly.
* **R2-13** — Adopted: the window state carries the merge record (`Option (ℕ × ℕ × Finset ℕ)`), and Def-7 uses $\nu_{\max}$, $h_j$, $k_1$ and the extended $\lambda_j$ as explicit functions (§3.6, §8.2).


## Third-review dispositions (v3 → v4)

*Third review* (`LF-ARCHITECTURE-review.md`, "Third review (v3)").

* **R3-01** (MAJOR, adjacency) — Accepted.
  - Components are classes of "$d<\omega_k$", $\omega_k=2[\hat R_{k-1}]+11$ (§3.1). Distinct components have
    disjoint $U^{\sim4}$, and the factorization (1.22) is Lemma F.
  - Constants changed: $D_k=\sqrt d(2\rho_k+10+\omega_k)$, and $h_j$ with $\mathrm{crit}_j+\omega_j$; $C_E$, $C_3$, $\hat W$'s
    constant and Lemma C (c) follow. $\nu_{\max}$, the exponents and $p_R$ are unchanged.
  - The core boxes are $\omega$-separated, so P7 (3.11) holds box by box (Lemma L), and (2.33)'s ring count
    is per box.
  - Added: the removal overwrite also relies on the $\omega$-separation (§3.2). Lemma F carries an
    UNCERTAIN on the locality of the backgrounds (question 5).
* **R3-02** (MAJOR, (3.11)′) — Accepted. The per-box path of version 3 is deleted. Under R3-01, Lemma L
  gives P7's own path box by box. The component-wide path (REPAIRS-astra §C.1) is kept as Lemma P,
  checked, for the general case. The localization obligation is reduced to Lemma F (85%).
* **R3-03** (MINOR, Lemma CH outline) — Accepted and recorded.
  - (iv), the exterior-boundary diameter, is written into the proof plan.
  - (ii) is answered by a one-block detour costing $\le2dLc\delta_j$.
  - (iii) is settled by the removal overwrite.
  - (v) is settled by (3.0) and (H-T).
  - (i), the conversion to a self-avoiding chain in the multiscale graph, is listed for RD III.4.
  - Confidence in Lemma CH rises from 75% to 78%.
* **R3-04** (MINOR, late-scale constants) — Accepted. (M7) and §5 row 4 list the segments after (2.18)
  and before (2.27) and $\lvert z-z_0\rvert\le D_0$ in (3.11). (2.29)′ is rewritten with $C(c_0)$, with
  $L^{n_1/3}\ge C(c_0)K_1MR_{k_1}$.
* **R3-05** (MAJOR, tori) — Accepted.
  - LF-2 and the region calculus are stated on cube tori with $n_k=Ln_{k+1}$ (§3.1, §4.1, §8.1), and
    spines live in continuous tori. Lemma V holds on tori by lifting along a spanning tree.
  - Hulls and window states exist only for $k\le k_0$. There (H-T) holds by (3.0), so window-bearing
    components never wind.
  - Winding pre-window components and the frozen regime on small tori need no hull, and the counting
    is unchanged.
* **R3-06** (MAJOR, causality) — Accepted, option B. The bookkeeping runs on $\hat\lambda_j$ and $\hat k_f$
  (§3.1). "$k\le k_0$" is the causal test $\beta_k\nu_k\le1$. No separate causality lemma is needed.
  Option A was declined: under it, (D6) at scale $k$ would refer to $\lambda_j$, $j>k$, which the flow
  itself determines later.
* **R3-07** (MAJOR, (D5)) — Accepted. (D5) is (1.26)–(1.27) for the localized operator, with the
  localized domain (1.24)–(1.25) and the index set $\mathfrak H_j(Z)$. It is required at every scale $j\le k$,
  because P7 p. 519 uses (1.26) at the core scale; this is an addition to the review's proposal.
* **R3-08** (MAJOR, kept operators) — Accepted.
  - The citation is corrected.
  - Kept operators come in two kinds, K1 (before the normalization) and K2 ((3.20), after it).
  - One exponent $\kappa''=\kappa_k-C_R\hat\lambda^{2d+1}+\gamma$ serves both, by the refund route; the review's
    "choose one route" is answered by choosing the refund route.
  - The removal overwrite of §3.2 has its separation check.
* **R3-09** (MAJOR, missing objects) — Accepted. §8.2 lists 16 objects with source, status
  ("definition" or "$\exists!$ first") and order of definition. RD part II writes them.
* **R3-10** (MAJOR, LF-4 on representations) — Accepted. Def-7 is $\mathrm{IsRep}_k$ on representations,
  and LF-4 is existential (§8.3). (Rg) is the internal lemma LF-4R. Torus coherence is part of
  $\mathrm{IsRep}_k$, so that the existential choice is coherent across tori.
* **R3-11** (MAJOR, quantifier prefix) — Accepted. The explicit prefix is in §5.1, with
  $\exists X'\,\forall X\ge X'$ for "large enough", outputs bound by $\exists$, and derived quantities as
  definitions. LF-4 (e) uses $B^\sharp$, bound before $B_0$. The cycle risk (row 12) is recorded.
* **R3-12** (MINOR, tie-breaks; empty $k_1$) — Accepted. The tie-break rules are in §3.2, and the
  bookkeeping is a function of the region history. The abstract LF-2 keeps arbitrary choices. $k_1$ uses
  the `Nat.findGreatest` convention and is evaluated only where the set is non-empty.
* **R3-13** (MINOR, notation) — Accepted. The flow amplitude is $c_9^{\rm flow}$ (row 10), and P3's
  constant is $c^{\rm P3}_1$ (row 6).
* **R3-14** (NOTE) — Accepted. (a) "with the chains of Lemma CH" is dropped from (M5) and Step 5.
  (b) `pe_hole` is cited as landed (d665e8d). (c) The kept case cites P7 p. 520. (d) is recorded in §3.1
  (window lengths). (e) is added to Lemma G.

*Counting audit* (COUNTING-astra) and repair text (REPAIRS-astra).

* **C-01** (BLOCKER; the review rates it MAJOR) — Accepted. Lemma C (e4) carries the last-box-entry
  exception, and the literal sentence "no lineage merge in $[q-h_q,q]$" is withdrawn. The repair text
  (REPAIRS-astra §B.2) was checked and adopted, with diameters $\nu(\mathrm{crit}+\omega)$.
* **C-02** (BLOCKER) — Accepted. There is a pending state and transitions (T1)–(T7). Lemma C4 proves
  closure, the horizon $q'\le\mu+h_\mu+1$, $t^{*\prime}=T$ and activation (REPAIRS-astra §B.1–§B.2,
  checked). The audit's two-merge history is a Pending output.
* **C-03** (MAJOR) — Accepted. The version-3 per-box path is deleted. Under R3-01 the issue disappears
  (Lemma L), and Lemma P is the general component-wide path.
* **C-04** (MAJOR) — Accepted. (H-λ) is an axiom of §4.1 and a hypothesis of the theorem, with the
  horizon $\hat k_f$; (B.20) is the transfer step.
* **C-05** (MINOR) — Accepted. $Z_0=\varnothing$, (B) applies at $k=0$, and the base is a (T2) event with $m=0$.
* *REPAIRS-astra §B.3* (budget) — Adopted after checking.
  - Changes: the abstract $\lambda$ with $\theta_\pm$; $D$ with $\omega$; and in (B.13) the case distinction
    Active/Pending for the part carrying $\tilde q$, which the text covered only for Active parts.
  - Its observation that the cap gives $\Lambda'=O(\log\lambda)$ in Case 2a, removing version 3's
    large-$\Lambda'$ branch there, is adopted.
* *REPAIRS-astra §C* (path lemma) — Adopted as Lemma P (checked). Its "outstanding localization
  obligation" is answered by R3-01 and Lemma L, conditional on Lemma F.
* *REPAIRS-astra §D* (restated LF-2) — Adopted, with tori (H-T) and the a priori sequence (§4.4, §8.1).
