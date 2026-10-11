# Large-field reconstruction document, Part I: geometry and counting (model-free)

Version 1.1 of Part I (version 1 + the repairs of the independent audit `LFR-PART1-AUDIT-astra.md`, findings
P1-01–P1-08, listed in §I.0 item 16 and marked "(audit P1-xx)" where they occur), 2026-10-11; Part II is appended
after §I.7. Brief: `orchestration/briefs/D-LFR-partI.md`. Input:
`notes/phase1/LF-ARCHITECTURE.md` version 4 (commit 44141ef; cited as **ARCH**), its reviews
`LF-ARCHITECTURE-review.md` (cited as **REV1**, **REV3**), `LF-V3-COUNTING-astra.md` (**COUNT**) and
`LF-V4-REPAIRS-astra.md` (**REPAIRS**); received during the writing and taken into account:
`LF-V4-AUDIT-astra.md` (V4-01–V4-03), `LOCALIZATION-review.md` (L-04, order of constants) and the
orchestrator's note on `SMALLFIELD.md` (the choice $c=0$). Status: draft for independent review. Nothing here is approved
or frozen. Parts II–IV (analytic objects and Def-7; $R$ on covered windows; the flow and the end) are not
written yet; Part I refers to them only through the abstract hypotheses (G1), (G2), (B), (Rg), (K),
(H-λ), (H-T) of the internal lemma LF-2 (§I.5), which are never frozen.

**Purpose.** Part I gives closed definitions and complete proofs, at a level a Lean worker can follow
line by line, for everything in the large-field analysis that does not involve fields or measures:
the constants and their quantifier prefix (§I.1); tori, cubes, neighbourhoods, hulls and components
(§I.2); the region calculus of P5 §2 and P6 §2 as explicit set functions on cube tori, with Lemma G
(attribution, inclusions, locality, separation), Lemma S, Lemma P and the geometric part of Lemma F
(§I.3); histories, spines, clocks and window states with the transitions (T1)–(T7) and Lemmas C4 and C
(§I.4); and the step counter LF-2 on tori with its proof (§I.5). §I.6 lists the Lean declarations that
Part I asks for. §I.7 collects the status of every statement, the changes made to ARCH, and the open items.

**Sources and conventions.** Keys as in `review/SOURCES.md`; page numbers are journal pages. Tags:
**[checked]** = re-read for this document in the PDF (text layer of P5–P7, page image for P2, P3 and
for displays of P5, P6, P7 whose text layer drops symbols); **[review]** = taken from `review/papers/*.md`
or from ARCH and not re-read. Status words: *proved here* (complete proof in this document); *cited*
(an external result, not reproved); *sketched* (outline only); *definition*. Doubts are marked
**UNCERTAIN**. Equation numbers (G1), (3.1), (B.7) etc. are those of ARCH where they exist, so that the
two documents can be read side by side; new displays are numbered (I.x).

**Notation used throughout.**
- $[x]:=\lfloor x\rfloor$ for real $x\ge0$ (P5's $[R_j]$).
- $\mathbb T_k:=(\mathbb Z/n_k\mathbb Z)^d$ is the *cube torus* of scale $k$ (Lean `Torus d (n k)`), whose
  points index the cubes of the partition $\pi_k$ (side $ML^k$ fine units).
- $\mathrm d(x,y)$ is the cyclic sup-distance on $\mathbb T_k$ (§I.2.1); "distance" without qualification
  always means this index distance.
- $X^{\sim m}$ is the closed $m$-neighbourhood of a set of cubes; $X^{\approx}$ is P5 (1.2).
- The four sets of new large-field cubes of a step, which Balaban calls $P_{k+1},Q_{k+1},R_{k+1},S_{k+1}$,
  are written $\mathsf P_{k+1},\mathsf Q_{k+1},\mathsf R_{k+1},\mathsf S_{k+1}$ (sans-serif). Plain $R_k$ is
  always the *running radius* $R_k=R^{\rm run}_k:=R_{\rm base}\lambda_k^2$ with the running $\lambda_k=\log(\beta_ka)$; the fixed
  coefficient, which P5 (1.2) calls $R_0$, is written $R_{\rm base}$ throughout (audit P1-07), so that $R_0$ always means
  $R^{\rm run}_0=R_{\rm base}\lambda_0^2$.
- Distances between sets take values in $\mathbb N\cup\{+\infty\}$ (Lean `ℕ∞`), with $\mathrm d(X,\varnothing)=+\infty$ (audit P1-07).

---

## I.0 What changed relative to ARCH (summary)

Each change is explained where it occurs. None changes the architecture; all are local repairs found
while writing the definitions out.

1. **Component width.** $\omega_k:=2[\hat R_{k-1}]+L+11$ (ARCH: $2[\hat R_{k-1}]+11$). The additional $L$ is
   needed for the attribution property (G1) of the actual region rules: a cube of $Z_{k+1}$ is joined
   to its seed through intermediate cubes of $Z_{k+1}$ at mutual distance up to $2[R_k]+L+3$
   (Lemma I.3.8). As a by-product, the neighbourhoods $U^{\sim n}$ of distinct components are disjoint
   for every $n\le(L+8)/2$, which covers P7's ring $U^{\sim6}$ once $L\ge4$ (Lemma I.2.13). Only
   $D_k$, $h_k$ and the constants $C_E,C_3$ change.
2. **(G1) restated.** ARCH (G1) asked for $*$-connected seed sets $B_\sigma\ni\sigma$. The rules of P5–P6
   produce unions of overlapping $L$-blocks of cubes, whose "pockets" need not be $*$-connected to
   anything. What the rules give, and what LF-2 uses, is: every cube of $Z^{(0)}_{k+1}$ lies within
   $s_\sigma r_k$ of a seed $\sigma$ *in its own component* (Lemma I.3.8). (G1) is restated in this form.
3. **Explicit radii.** $s_*=4$, $s'=5$, valid under the radius hypotheses (RH) of §I.3.1 ($R_{\rm base}\ge4L+20$, $\lambda_j\ge1$; Lemma I.3.8), computed from P5 (2.3),
   (2.8), (2.45) and P6 (2.3) [checked] converted to index distances (Lemma I.2.2). Hence
   $c_0:=\min\{c\in\mathbb N:\ c(1-L^{-1})\ge5,\ c\ge6\}$.
4. **Hull trigger.** A component is hulled when it is small and its hull has side $\le\mathrm{crit}_k$
   (ARCH: "diameter $\le\mathrm{crit}_k$"). With ARCH's wording a hull box can have side
   $\mathrm{crit}_k+1$ and then does not lie in $N_{\rho_k+4}$ of its centre; with the side test it does
   (Lemma I.2.8 (d)).
5. **Spines** are represented by lifts to $\mathbb R^d$ (finite connected unions of segments), and Lemma V is
   proved without Hausdorff measure (Lemma I.5.1). The event bound (4.1) is proved through the rounds of
   the hull rule (Lemma I.4.8); ARCH did not treat hull boxes that are later merged.
6. **Lemma C (a)** is proved through an explicit "floor" invariant (Lemma I.4.12). ARCH's proof was a
   one-paragraph argument.
7. **Constants of the counting.** $c':=c_*(1+3\theta_+)$ (ARCH $1+6\theta_+$; either works), the horizon
   constant $c_H:=\frac{(d+3)(d-2)}2\log L$ (ARCH's $c_d$ depends on $L$), and an explicit finite list of
   the conditions defining $\lambda_*$ (§I.5.3). The large-$\Lambda'$ branch of Case 2b is replaced by a
   direct estimate that does not need the Pre/Active case distinction.
8. **Instantiation of (H-λ).** Derived from $\beta_k=\beta L^{k(d-2)}\gamma_k$, $\nu_k=\nu L^{2k}\delta_k$,
   $|\log\gamma_k|,|\log\delta_k|\le\epsilon\le\frac1{20}$ alone (Lean `betaSeq_eq`, `nuSeq_eq`,
   `norm_gammaSeq_le`), without P5 p. 490's approximate ratio $L^d$. The case $k_0=0$ is included.
9. **LF-2 has a final scale** $K$ with $k_0\le K\le\hat k_f$, so that it applies to the flow, which stops
   at $k_f\le\hat k_f$.
10. **Minimal generating sets** $\mathbb B_k(X)$ of P3 (4.4)–(4.6) are built from $M_1$-cubes, which are not
    cubes of the cube tori; they are moved to Part II (item 3 of ARCH §8.2). Part I gives the
    geometric reduction of P7 (2.13) to single core boxes (Lemma I.3.16).
11. **Locality** of the region rules (each component is computed from its own seeds) is stated and
    proved (Lemma I.3.9). It is the precise form of P5 p. 493 and P6 p. 15 and is what makes localized
    histories well defined.
12. **Short spines.** The projected epoch is $s:=k+\max\{1,\lceil\log_L\max(\ell,1)\rceil\}$, and short spines are replaced by
    a point only under pure shadows (Definition I.4.7). ARCH also replaced short *event* spines, which can
    place a merged component with hull parts outside $N_{\rho+4}$ of the chosen point.
13. **Constant order** (LOCALIZATION-review L-04, received during the writing): $\kappa_1$, then $M_1$ and $M$, then
    the localization constants $K_3,K_4,B_4,B_5,c_7$ (new row 6b); no upper bound on $M$ is needed anywhere in
    Part I (§I.1.3–§I.1.4).
14. **Scope of Lemma L** (LF-V4-AUDIT V4-01, received during the writing): the identification of global and
    local sets holds only near the ripe lineage (Lemma I.2.14); ARCH's Lemma L (c) with the global sets is
    false, and Part III must state (3.11)′ on the localized support (remark after Lemma I.3.16).
15. **Interface details** (V4-03): LF-2 is stated for $d\ge3$; $\omega_0$ and $h_0$ are defined by convention
    (§I.1.2); the window part of LF-2 assumes $k_0\ge1$, and $k_0=0$ is treated in the frozen part.
16. **Repairs after the audit `LFR-PART1-AUDIT-astra.md` (version 1.1).** Each is marked "(audit P1-xx)" in the text.
    - *P1-01 (blocker; constant prefix).* The ratio $M/M_1=L^{m_0}$ is now fixed by a definition, $m_0=m_0(d,L)$ (§I.1.3
      row 5a), as P3 p. 81 and LOCALIZATION §5.3 do; the prefix quantifies over $M_1$ only, and every row-6 condition is
      re-checked to be a lower bound on $M_1$ (§I.1.4). Version 1 quantified "$\forall m\ge m_0'$", which is incompatible
      with $\kappa_1\ge4d\log((2L+1)M/M_1)+2$.
    - *P1-02.* (I.3) and Lemma I.2.13 now assume $\lambda_{k-1}\ge0$ (i.e. $R_{k-1}\le\hat R_{k-1}$) in the flow specialization.
    - *P1-03.* Lemmas I.3.8 and I.3.9 now assume the bookkeeping sequence is nondecreasing with $\lambda_k\ge1$ (so
      $r_k\ge R_{\rm base}$) and $0\le R_j\le R_{\rm base}\lambda_j^2$.
    - *P1-04.* Lemma I.3.10 (c) now assumes $R_j\ge R_{\rm base}$ (running $\lambda_j\ge1$); the Lean `GeneratingSet` has its terminal
      field $\Omega_{k+2}:=\varnothing$.
    - *P1-05.* Lemma I.5.6 (c) is restricted to a genuine $k_0$ ($\beta_{k_0}\nu_{k_0}\le1$); for the conventional $k_0=0$ and for
      $k_0=0$ in general (H-T) is vacuous; $k_f=0$ is excluded from LF-2 and treated by LF-8 (b).
    - *P1-06.* The fixed-point hull closure is labelled an architectural extension of P6 p. 22 (which describes one
      replacement), and the properties used downstream are checked for the closure (remark after Lemma I.3.4).
    - *P1-07.* $R_{\rm base}$ versus $R^{\rm run}_k$; the $k=0$ step by cases; $x\in\mathbb N$ in (F1); distances in $\mathbb N\cup\{\infty\}$; seed
      containment, nonempty seed families and the indexing of component data are fields of `LF2Hyp`.
    - *P1-08.* (Λ12′) is added to the condition list, and the list is split into the conditions of the abstract LF-2
      ((Λ0)–(Λ11)) and those of the flow instantiation ((Λ12), (Λ12′), (Λ13)).

---

## I.1 Constants and the quantifier prefix

### I.1.1 The a priori sequence and the horizon

Fix $\beta>0$, $\nu\in(0,1]$, $L\ge2$ and the constant $a\in(1,\frac32)$ of P4 (5.22) [review] (ARCH §5 row
3: $a=(1-L^{-2})^{-1}$). Put $\theta:=(d-2)\log L$ and

$$\hat\lambda_j:=\log(\beta a)+1+j\theta,\qquad \hat R_j:=R_{\rm base}\hat\lambda_j^2\qquad(j\in\mathbb N),\qquad
\hat k_f:=\min\{k\in\mathbb N:\ \nu L^{2k+2}\ge1\}.\tag{I.1}$$

The running coefficients of the flow satisfy (P4 (H.6) [review]; Lean `betaSeq_eq`, `nuSeq_eq`,
`norm_gammaSeq_le` in `Balaban/Flow/RunningCoefficients.lean`, which are generic in the
perturbations $\xi$ of the RG equations)

$$\beta_k=\beta L^{k(d-2)}\gamma_k,\qquad \nu_k=\nu L^{2k}\delta_k,\qquad |\log\gamma_k|,|\log\delta_k|\le\epsilon:=\tfrac{c_8q}{1-q}\le\tfrac1{20}.\tag{I.2}$$

With $\lambda_k:=\log(\beta_ka)$ this gives $\hat\lambda_k-\lambda_k=1-\log\gamma_k\in[1-\epsilon,1+\epsilon]$, so

$$\lambda_k\le\hat\lambda_k\le\lambda_k+2,\qquad\text{and, if }\lambda_k\ge0,\qquad R_k:=R^{\rm run}_k:=R_{\rm base}\lambda_k^2\le\hat R_k .\tag{I.3}$$

The second inequality needs $\lambda_k\ge0$ (audit P1-02: for $\beta a<1$ the running radius can exceed $\hat R_k$). In
the flow $\hat\lambda_0\ge\lambda_*\ge3$, so $\lambda_k\ge\hat\lambda_k-2\ge1$ for all $k$, hence $R_k\ge R_{\rm base}$ and $R_k\le\hat R_k$; every
statement below that is specialized "to the flow" uses this.

$k_0$ is the last $k$ with $\beta_k\nu_k\le1$, read as $0$ if there is none (ARCH §3.6), and $k_f$ the first
$k$ with $\nu_k>\frac78L^{-2}$ (P4 §6, P7 p. 529 [review]). Lemma I.5.6 shows $k_f\le\hat k_f\le k_f+1$.
**All bookkeeping of Parts I–IV is a function of $\hat\lambda$ and $\hat k_f$**; the running constants
enter only the analytic objects (ARCH R3-06, option B), and only Lemma I.5.6 (the instantiation)
uses (I.2).

### I.1.2 The model-free constants

The bookkeeping of Part I is built on an abstract real sequence $\lambda=(\lambda_j)_{j\in\mathbb N}$; in the
flow, $\lambda=\hat\lambda$. The *typing constants* are

$$d\ge2\ (d\ge3\text{ in LF-2}),\ L\ge2,\ M\ge1,\ R_{\rm base}\ge1\ (\text{integers except }R_{\rm base});\quad \theta_+\ge\theta_->0,\ \alpha>0;\quad p_0,p_2,p_R\in\mathbb N;$$
$$A_2,A_3,A'_3,C_R,C_\nu>0,\quad c_v\ge1,\quad c_H\ge0,\quad s_*,s',c_0\in\mathbb N .$$

In the flow: $d\ge3$, $\theta_\pm=\theta$, $\alpha=\frac{d-2}2-\gamma$, $s_*=4$, $s'=5$, and the other values are those
of §I.1.3. The *derived quantities* are definitions (no binders), for $j,k,t\in\mathbb N$:

| Symbol | Definition | Source / role |
|---|---|---|
| $r_j$ | $\lceil R_{\rm base}\lambda_j^2\rceil$ | radius unit; $r_j\ge\hat R_j\ge R_j$ in the flow |
| $\rho_j$ | $c_0r_j$ | spine radius is $\rho_j+4$ (ARCH LFR-08) |
| $\mathrm{crit}_j$ | $2\rho_j+10$ | critical side (cubes) |
| $\omega_j$ | $2[R_{\rm base}\lambda_{j-1}^2]+L+11$ for $j\ge1$; $\omega_0:=L+11$ | component width (**changed**, §I.0 item 1) |
| $D_j$ | $\sqrt d\,(2\rho_j+10+\omega_j)$ | connector length |
| $n_q(j)$ | $\min\{n\ge1:\ n\log L>\alpha^{-1}\lambda_j\}$ | window length |
| $n_2(j)$ | $\min\{n\in\mathbb N:\ L^n>LM\,\mathrm{crit}_j\}$ | smallness length |
| $k_1(t)$ | $\max\{c\le t:\ c+n_q(c)\le t\}$, and $0$ if the set is empty (Lean `Nat.findGreatest`) | core of a window ending at $t$ |
| $\nu_{\max}(j)$ | $\lceil C_\nu\lambda_j^{p_2}\rceil$ | piece cap |
| $h_j$ | $\lceil\log_L\big(2\sqrt d\,\nu_{\max}(j)M(\mathrm{crit}_j+\omega_j)\big)\rceil+2$ | strip length |
| $B(E)$ | $\bigcup_{\xi\in E}[\xi,\xi+h_\xi]\cap\mathbb N$ for finite $E\subset\mathbb N$ | blocked core scales |
| $g_k$ | $\frac12A_3\lambda_k^{2p_0}$ | gain per new cube |
| $C_V$ | $2\cdot14^d$ | Lemma V |
| $v_j,\ w_j$ | $c_vC_V\lambda_j\rho_j^{d-1}$, $\ v_j\rho_j$ | volume cost coefficients |
| $\sigma_k$ | $\sum_{j>k}v_jL^{-(j-k)}$ | spine reserve coefficient |
| $\tau_t$ | $2A_2\lambda_t^{p_2}$ | ripeness threshold |
| $C_\sigma$ | $2^{d-1}\sum_{n\ge1}n^{2d-1}L^{-n}$ | (F2) |
| $E_k$ | $(1+2^{3d+1}C_\sigma)\,v_kD_k$ | cost of one contact edge |
| $C_w,\ C_E$ | $c_vC_Vc_0^d(R_{\rm base}+1)^d$, $\ (1+2^{3d+1}C_\sigma)c_vC_V\sqrt d\,(c_0(R_{\rm base}+1))^{d-1}(2c_0(R_{\rm base}+1)+2R_{\rm base}+L+21)$ | (F5) |
| $c_*,\ c',\ c''$ | $1+\frac{\theta_+}{\alpha\log L}$, $\ c_*(1+3\theta_+)$, $\ c_*+\theta_+$ | growth of ripeness times |
| $C_t$ | $4+\frac{1+2\theta_+}{\alpha\log L}$ | length of a restarted window (Lemma I.5.3) |
| $C_r$ | $2A_2c'^{p_2}+1$ | overflow payment (4.4) |

In the flow, $w_0:=\frac{p_2d}2+3d$ (chain exponent of Part III) and $p_R:=2p_0-2w_0=2p_0-(p_2+6)d$, an
integer.

### I.1.3 The constant chain

This is ARCH §5 with the changes of §I.0 (rows 4, 7). "Lower" means the condition is a lower bound on
the constant of that row in terms of earlier ones, so that the row can be bound as
$\exists X'\,\forall X\ge X'$; "upper" means $\exists X'\,\forall X\in(0,X']$. Status refers to the
statement that the condition has that form.

| # | Constant(s) | Conditions (source) | Direction | Status of the monotonicity |
|---|---|---|---|---|
| 0 | $d\ge3$, $N\ge2$ | — | — | — |
| 1 | $\gamma\in(0,\min\{\frac{d-2}2,\frac12\})$, $\delta:=\gamma/2$, $\alpha:=\frac{d-2}2-\gamma$ | P4 (H.1) | definition | — |
| 2 | $\kappa,c_9$ | given (Root-F) | — | — |
| 3 | $L$; $a$, $\theta$ derived | $L\ge3$ (P2 (4.26)); $\log L>\frac12$, $(d-2)\log L>1$; G-1–G-6 | lower | the explicit ones checked; G-1–G-6 **UNCERTAIN** (Part II must state each as $L\ge L_i(d)$) |
| 4 | constants depending on $(d,L)$ (and $N$) only: $\gamma_0$, $K_0,K_1,K_2$, $C_3,C_4$, Green constants of G-1–G-3, $R_0(d,L)$ of BACKGROUND §2; $s_*:=4$, $s':=5$ (Lemma I.3.8); $c_0$ (I.0 item 3); $D_0:=3c_0+4$; $K_6,c_{11}$ of P7 Lemma 2.1 for boxes of size $<D_0$ | outputs of G-1–G-3, P2, P7 Lemma 2.1 | outputs ($\exists$) / definitions | the constants of I-4 depend on $\kappa_1$ and are in row 5$'$ |
| 5 | $\kappa_0$; $\kappa_{\rm flow}:=\max\{C_d(\kappa+1),16\kappa_0+16\}$ | $\kappa_0$ an output of row 4 (LOCALIZATION-review L-04: it enters only through $K_0$) | output / definition | $\kappa_0$ independent of $M$ and $M_1$ |
| 5a | $m_0$ (**definition**, audit P1-01) | $m_0:=\min\{m\ge1:\ L^m\ge\max\{14d,\ L+9\}\}$, so $M/M_1:=L^{m_0}$ is a function of $(d,L)$; $L^{m_0}\ge14d$ is P3 p. 81 (LOCALIZATION §1.1, §5.3), $L^{m_0}\ge L+9$ is the range bound of the minimal generating sets (Part II, Lemma II.2.3) | definition | since $L^{m_0}\ge42\ge6$ and $\ge4+8/L$, also $6M_1\le M$ (P3 (4.8)) and $(4L+r_0)M_1\le LM$ with $r_0=8$ (LOCALIZATION §4.0) hold by definition |
| 5b | $\kappa_1$ | $\kappa_1\ge\max\{4d(2L+1)^d\kappa_{\rm flow},\ 4d\log((2L+1)L^{m_0})+2\}$ (the second is the walk-expansion condition of I-4, LOCALIZATION §5.3 (3); with $M/M_1=L^{m_0}$ it depends on $(d,L)$ only) | lower | checked: both are lower bounds on $\kappa_1$ in terms of earlier rows (audit P1-01 resolved) |
| 5$'$ | localization constants $c_*,B_G,c_6,\delta_*,K_3,K_4,c_7,B_4,B_5$ | outputs of I-4 (walk expansion), depending on $(d,L,N,\kappa_1)$ and not on $M_1$, $M$ (LOCALIZATION §5.3 (4)) | outputs ($\exists$) | moved after $\kappa_1$ (L-04) |
| 6 | $M_1=L^{m_1}$; then $M:=L^{m_0}M_1$ (definition) | $M_1\ge M_*(\kappa_1):=\max\{4L^2,c_Me^{N_0\kappa_1}\}$ ($c_M,N_0$ of LOCALIZATION §1.2); P3 (4.38) first part $e^{\gamma_wM_1}\ge4(d+2)(K_2+1)K_4/\eta_\varepsilon$; $M\ge2(7L)^d\kappa_1/\gamma_0$; $M\ge M(\kappa)$ (P4, ER-025); P7 (2.70) $3(d+1)K_1K_3K_6e^{-\gamma_0M/5}\le\frac18$; $5LM_1\ge R_0(d,L)$ (minimal generating sets are generating sets for I-1, Lemma II.2.3 (a)) | lower bounds on $M_1$ | every condition is $M_1\ge$ (function of rows 0–5b and of the $(d,L)$-constants $K_1,K_6$ of row 4, $K_3,K_4$ of row 5$'$): the conditions on $M$ become conditions on $M_1$ because $M=L^{m_0}M_1$ is increasing in $M_1$; no upper bound on $M$ or $M_1$ anywhere in Part I or ARCH §5 |
| 6b | $K_5$ (P4 (5.24), contains $M$), $B_6=NL^dB_4+2$ | outputs depending on $M$ | outputs ($\exists$) | after $M$; $E_0\ge4C_4B_6K_0K_5$ stays after them (row 11) |
| 7 | $R_{\rm base}$ | $R_{\rm base}\ge\max\{6K_1K_6,\ C(L),\ 4L+20,\ R_0(d,L)/(LM)\}$ (P7 p. 514; P3 (2.14); Lemma I.3.8; the separation $\varrho=LMR_{\rm base}\ge R_0(d,L)$ of BACKGROUND §2) | lower | checked; $K_6=K_6(d,L,D_0)$ is the "absolute" constant of P7 Lemma 2.1 for boxes of size $<D_0$ (P7 p. 507 [checked]: "with the size smaller than 15 we obtain absolute constants"), so row 4 |
| 8 | $p_2:=2d+3$, $p_0:=$ least even integer $\ge d^2+7d+2$, $A_2:=1$, $C_\nu:=C_r$ | (K) of §I.5.2 | definitions | (K) holds: $p_R\ge5d+4>p_2+2d$, $2p_0>p_2$ |
| 9 | $A_0$; $A_1,A_3,A'_3,A''_3$ derived | P7 p. 505; P6 (3.9) | lower | $A_3,A'_3$ are increasing in $A_0$ [review] |
| 10 | $\alpha_1$, $c_8$; $c_9^{\rm flow}$ | P4 Thm 1 "sufficiently small" | upper | as stated in P5 p. 499 [review] |
| 11 | $\alpha_0,E_0,B,\bar\nu$; $C_b$, $C_{\psi'}$ | outputs of P4 Thm 1, P5 Thm 1; the constants of P6 (2.33) and P5 (1.25) (Part II, (S0) and Definition II.3.4) | outputs | $C_b$, $C_{\psi'}$: open item O-II-4 |
| 12 | $B_0$ | $B_0\ge B^\sharp$ (P7 p. 529) | lower | $B^\sharp$ independent of $H_0,c_1,c_2$: **UNCERTAIN** (ARCH row 12) |
| 13 | $H_0$ | $H_0>2B_0K_0M^{-d}$; P7 (4.12) | lower | checked [review] |
| 14 | $c_1,c_2$ | $\ge$ P6's coefficients and $C_{39},C'_{39}$; $c_1\ge C_b$, $c_2\ge C_bB_0+2(L^d+1)$ (Lemma II.5.14) | lower | checked (a larger cost coefficient keeps P6 (3.9) true) |
| 15 | $c_v:=M^d(H_0+c_1+3)$; $C_R$ | Lemma B; LF-4R | definition / output | $c_v\ge1$ |
| 16 | $\lambda_*$, then $\beta_0:=\max\{e^{\lambda_*-1}/a,B\}$ | §I.5.3: abstract (Λ0)–(Λ11), flow (Λ12), (Λ12′), (Λ13), (Λ14); Part II (Λ15)–(Λ17); the analytic "$\beta$ large" conditions of Parts III–IV | lower | the Part I conditions are listed in §I.5.3 and each is eventually true; the analytic ones are Part II–IV's |
| 17 | Root-C only: $\rho_2,\rho_1,\rho_0$ | P9 p. 511 | — | — |

The Part I constants $s_*,s',c_0,\omega_j,D_j,h_j,C_\nu$ are fixed in rows 4, 7 and 8; $\lambda_*$ depends on
all of rows 0–15 and on nothing else.

### I.1.4 The quantifier prefix

ARCH §5.1 with the Part I changes:

$$\begin{aligned}
&\forall d\ge3,\ N\ge2.\ [\gamma,\delta,\alpha]\ \ \forall\kappa>0,\ c_9>0.\ \exists L_0\ \forall L\ge L_0.\ [a,\theta,\ s_*:=4,\ s':=5,\ c_0,\ D_0,\ m_0]\ \exists(\gamma_0,K_0,K_1,K_2,K_6,c_{11},R_0(d,L),\dots)_{(d,L,N)}.\\
&\exists\kappa_0.\ [\kappa_{\rm flow}]\ \exists\kappa_1'\ \forall\kappa_1\ge\kappa_1'.\ \exists(c_*,B_G,c_6,\delta_*,K_3,K_4,c_7,B_4,B_5)_{(d,L,N,\kappa_1)}.\ \exists M_1'\ \forall m_1\ \text{with}\ M_1:=L^{m_1}\ge M_1'.\ [M:=L^{m_0}M_1].\\
&\exists(K_5,B_6,\dots).\ \exists R_{\rm base}'\ \forall R_{\rm base}\ge\max\{R_{\rm base}',4L+20\}.\ [\hat R_j,\omega_j,\mathrm{crit}_j,D_j,p_2,p_0,w_0,p_R,A_2,C_\nu,h_j]\ \exists(C_{\rm ch},C_{\hat W}).\\
&\exists A_0'\ \forall A_0\ge A_0'\ [A_1,A_3,A'_3,A''_3].\ \exists\alpha_1',c_8',c_9^{\max}\ \forall\alpha_1\in(0,\alpha_1'],\ c_8\in(0,c_8'].\ \exists(\alpha_0,E_0,B,\bar\nu).\\
&\exists B^\sharp\ \forall B_0\ge B^\sharp.\ \exists H_0'\ \forall H_0\ge H_0'.\ \exists c_1',c_2'\ \forall c_1\ge c_1',c_2\ge c_2'.\ [c_v]\ \exists C_R.\\
&\exists\lambda_*\ \forall\beta\ge\beta_0:=\max\{e^{\lambda_*-1}/a,B\}\ \forall\nu\in(0,1]\ \forall h\in S^{N-1}\ \forall\text{admissible tori}:\ \text{LF-2 (instantiated), LF-3, \dots, LF-8 hold.}
\end{aligned}$$

**The ratio $M/M_1$ (audit P1-01).** Version 1 of this prefix read "$\exists M_1'\,\forall M_1\ge M_1'.\ \exists m_0'\,\forall m\ge m_0'\,[M:=L^m]$",
which together with $\kappa_1\ge4d\log((2L+1)M/M_1)+2$ (fixed before $M$) is contradictory: the right side tends to
$\infty$ with $m$. The repair is P3's own choice (p. 81) and LOCALIZATION §5.3: $M/M_1:=L^{m_0}$ with $m_0=m_0(d,L)$ fixed
by the definition of row 5a. Then the walk-expansion condition on $\kappa_1$ depends on $(d,L)$ only, and the binder
on the RG cube size is the one on $M_1=L^{m_1}$. *Re-check of every row-6 condition for this choice.* Each one is
$M_1\ge F$ with $F$ built from earlier rows: (i) $M_1\ge4L^2$; (ii) $M_1\ge c_Me^{N_0\kappa_1}$; (iii) P3 (4.38), first part:
$e^{\gamma_wM_1}\ge4(d+2)(K_2+1)K_4/\eta_\varepsilon$ ($K_4$ from row 5$'$); (iv) $M=L^{m_0}M_1\ge2(7L)^d\kappa_1/\gamma_0$, implied by
$M_1\ge2(7L)^d\kappa_1/\gamma_0$; (v) $M\ge M(\kappa)$ of P4/ER-025, implied by $M_1\ge M(\kappa)$; (vi) P7 (2.70),
$3(d+1)K_1K_3K_6\exp(-\frac15\gamma_0M)\le\frac18$ [checked, P7 p. 514: "one of the strongest conditions on $M$"], implied by a lower
bound on $M_1$ since $K_1,K_6$ are $(d,L)$-constants (row 4) and $K_3$ is in row 5$'$; (vii) $6M_1\le M$ and
$(4L+8)M_1\le LM$ hold by the definition of $m_0$. Constants chosen after $M$ (row 6b: $K_5$ of P4 (5.24), which
contains $M$, and $B_6$) appear only on the larger side of later conditions (rows 7–16). The open item O-7 of version 1 is
closed.

Square brackets are definitions, not binders. **Monotonicity check of the Part I conditions.** Every
Part I condition is of one of three kinds:

1. a lower bound on $R_{\rm base}$ ($R_{\rm base}\ge4L+20$, row 7);
2. a definition ($s_*,s',c_0,m_0$ and the table of §I.1.2);
3. "$\lambda\ge\lambda_*$" for one real variable $\lambda$ (§I.5.3), where $\lambda_*$ is chosen after all of
   rows 0–15. Since $\hat\lambda_0=\log(\beta a)+1$ is increasing in $\beta$, each such condition is a lower
   bound on $\beta$.

So the Part I conditions are monotone in the sense of ARCH §5.1. The analytic rows (3, 5, 6, 6b, 9–14) are
monotone as far as ARCH and the reviews checked them; Parts II–III must re-check each when the
corresponding estimate is written out (the column "Status").

**No upper bound on $M$ (LOCALIZATION-review L-04).** $M$ enters Part I in $n_2(j)$ ($L^{n_2}>LM\mathrm{crit}_j$),
in $h_j$ (through $\log_LM$), in $c_v=M^d(H_0+c_1+3)$ and in the fine-unit conversions of Lemmas I.3.5 (f),
I.3.10 and I.3.12. Each of these is either a definition or a quantity absorbed by $\lambda\ge\lambda_*$, and
$\lambda_*$ is chosen after $M$. The cube-unit quantities $\mathrm{crit}_j$, $\omega_j$, $r_j$, $s_*$, $s'$, $c_0$ and the
hypothesis (H-T) do not involve $M$. So nothing in Part I bounds $M$ (or $M_1$) above. In the large-field
chain of ARCH §5 the conditions after row 6 that involve $M$ ($R_{\rm base}\ge6K_1K_6$ through $K_6$;
$L^{n_1/3}\ge C(c_0)K_1MR_{k_1}$ in (M7), absorbed by $\beta$ large; $H_0>2B_0K_0M^{-d}$; $c_v$) are lower bounds
or definitions, so an exponentially large $M_1$ (and $M\ge6M_1$) is compatible with them.

---
## I.2 Tori, cubes, neighbourhoods, hulls, components

### I.2.1 Cube tori and the index distance

**Definition I.2.0 (cube tori, distance, neighbourhoods).**
- *Cube tori.* In the flow the fine torus is $(\mathbb Z/\ell\mathbb Z)^d$ with $ML^{k_f+1}\mid\ell$, and
  $n_k:=\ell/(ML^k)$ for $0\le k\le k_f+1$. Abstractly (§I.5) we are given positive integers $n_0,\dots,n_K$
  with $n_k=Ln_{k+1}$. $\mathbb T_k:=(\mathbb Z/n_k\mathbb Z)^d$ (Lean `Torus d (n k)`, i.e. `Fin d → ZMod (n k)`).
  The point $x\in\mathbb T_k$ indexes the cube of $\pi_k$ whose fine sites are the fibre of $x$ under
  `blockMap (M * L^k)` (Lean `blockFibre`); "as fine sets" refers to these fibres.
- *Cyclic norm.* For $a\in\mathbb Z/n\mathbb Z$, $|a|_n:=\min\{a.\mathrm{val},\ n-a.\mathrm{val}\}$ (with $|0|_n=0$).
- *Index distance.* $\mathrm d(x,y):=\max_{1\le i\le d}|x_i-y_i|_{n_k}$, and for sets
  $\mathrm d(X,Y):=\min\{\mathrm d(x,y):x\in X,y\in Y\}$ ($+\infty$ if $X$ or $Y$ is empty).
- *Neighbourhoods.* For $m\in\mathbb N$, $X^{\sim m}:=\{y:\mathrm d(y,X)\le m\}$; $X^{\sim}:=X^{\sim1}$;
  $X^{\sim-m}:=((X^c)^{\sim m})^c$ (P6 p. 4 [checked]: $\Omega''^{\sim-3}=((\Omega''^c)^{\sim3})^c$).
- *Thick neighbourhood* (P5 (1.2) [checked]). At scale $j\ge1$, $X^{\approx}:=X^{\sim([R_{j-1}]+1)}$ and
  $X^{\approx2}:=(X^{\approx})^{\approx}$.
- *Adjacency.* $x\ne y$ are $*$-adjacent if $\mathrm d(x,y)=1$, and nearest-neighbour (nn) adjacent if
  $x-y=\pm e_i$ for some $i$. Paths, enclosure and $\mathcal D_k$ use nn adjacency; Lemma S uses $*$-adjacency.

**Lemma I.2.1 (metric facts).** (a) $\mathrm d$ is a metric on $\mathbb T_k$. (b) If $\mathrm d(x,z)\le a+b$
($a,b\in\mathbb N$), there is $y$ with $\mathrm d(x,y)\le a$ and $\mathrm d(y,z)\le b$. Hence
$(X^{\sim a})^{\sim b}=X^{\sim(a+b)}$, $X^{\approx2}=X^{\sim2([R_{j-1}]+1)}$, and
$\mathrm d(X^{\sim a},Y)\ge\mathrm d(X,Y)-a$. (c) If $\mathrm d(x,z)=t$, there is a sequence
$x=z_0,z_1,\dots,z_t=z$ with $\mathrm d(z_{i-1},z_i)=1$ and $\mathrm d(x,z_i)=i$.

*Proof.* (a) $|\cdot|_n$ is the path metric of the cycle $\mathbb Z/n\mathbb Z$; the maximum of metrics is a
metric. (b) Coordinatewise: let $t_i:=|z_i-x_i|_n$ and move from $x_i$ by $\min\{a,t_i\}$ steps along a
shortest arc towards $z_i$; then $|y_i-x_i|_n\le a$ and $|z_i-y_i|_n=t_i-\min\{a,t_i\}\le b$. (c) Apply (b)
repeatedly with $a=1$. $\square$

**Lemma I.2.2 (Balaban's distances as index distances).** Let the cubes of $\mathbb T_k$ have side $s$ in
some unit (the continuous torus then has side $n_ks$). For $x,y\in\mathbb T_k$ the sup-distance of the
closed cubes is $\operatorname{dist}_\infty(\square_x,\square_y)=s\max\{\mathrm d(x,y)-1,0\}$. Hence, for real
$r\ge0$,
$$\operatorname{dist}_\infty(\square_x,\square_y)>sr\iff\mathrm d(x,y)\ge[r]+2,\qquad
\operatorname{dist}_\infty(\square_x,\square_y)\le sr\iff\mathrm d(x,y)\le[r]+1 .$$
The same holds for sets of cubes.

*Proof.* In coordinate $i$ the two intervals $[x_is,x_is+s]$, $[y_is,y_is+s]$ on the circle of length
$n_ks$ are at distance $s\max\{|x_i-y_i|_{n_k}-1,0\}$; take the maximum over $i$. For an integer $t\ge0$,
$\max\{t-1,0\}>r\iff t\ge[r]+2$. $\square$

*Applications* [checked against the page images]:
- P5 (1.2): "$\mathrm{dist}_j(\square,X)\le MR_{j-1}$" with $\pi_j$-cubes of side $M$ is
  $\mathrm d(\square,X)\le[R_{j-1}]+1$, which is P5's own second expression $X^{\sim([R_{j-1}]+1)}$.
- P5 (2.3): "$\mathrm{dist}_k(\square'',U'^{\sim3}_k)>LMR_k$" with $\pi_{k+1}$-cubes of side $LM$ in scale-$k$
  units is $\mathrm d(\square'',U'^{\sim3}_k)\ge[R_k]+2$.
- P6 (2.3): "$\mathrm{dist}_{k+1}(\square'',\cdot)>2MR_k+M$" with $\pi_{k+1}$-cubes of side $M$ in scale-$(k+1)$
  units is $\mathrm d(\square'',\cdot)\ge[2R_k+1]+2=[2R_k]+3$.

### I.2.2 Coarsening

**Definition I.2.3.** For $x\in\mathbb T_k$, $x^\uparrow\in\mathbb T_{k+1}$ has coordinates
$\lfloor x_i.\mathrm{val}/L\rfloor$ (Lean `blockMap L (n (k+1))`; `Balaban.Multiscale.jBlock`). For a set,
$X^\uparrow:=\{x^\uparrow:x\in X\}$ (P5 (2.2): $U'_k$ is the union of the $\pi_{k+1}$-cubes meeting $U_k$). As
fine sets $X\subset X^\uparrow$.

**Lemma I.2.4.** For $x,y\in\mathbb T_k$:
(a) $\mathrm d(x^\uparrow,y^\uparrow)\le\lceil\mathrm d(x,y)/L\rceil$; hence $(X^{\sim m})^\uparrow\subset(X^\uparrow)^{\sim\lceil m/L\rceil}$;
(b) $\mathrm d(x,y)\le L\,\mathrm d(x^\uparrow,y^\uparrow)+L-1$; in particular $x^\uparrow=y^\uparrow$ implies $\mathrm d(x,y)\le L-1$.

*Proof.* Work in one coordinate; $n_k=Ln_{k+1}$. (a) Choose integer lifts $\tilde x,\tilde y$ with
$|\tilde x-\tilde y|=|x_i-y_i|_{n_k}=:t$; reduction of $\lfloor\cdot/L\rfloor$ modulo $n_{k+1}$ is compatible with
adding $n_k$, so the coarsened coordinates are $\lfloor\tilde x/L\rfloor,\lfloor\tilde y/L\rfloor$ mod $n_{k+1}$, and
$|\lfloor\tilde x/L\rfloor-\lfloor\tilde y/L\rfloor|\le\lceil t/L\rceil$. (b) Choose lifts $u,v$ of the coarse
coordinates with $|u-v|=|x_i^\uparrow-y_i^\uparrow|_{n_{k+1}}$; then $x_i,y_i$ have lifts in $[Lu,Lu+L-1]$ and
$[Lv,Lv+L-1]$. $\square$

### I.2.3 The cover $\pi'$ by $L$-blocks; block openings

**Definition I.2.5.** For $c\in\mathbb T_{k+1}$, $\mathrm{Bl}(c):=\{c+v:\ v\in\{0,\dots,L-1\}^d\}$. The cover
$\pi'_{k+1}$ is $\{\mathrm{Bl}(c):c\in\mathbb T_{k+1}\}$: "a cover of the torus by $L^2M$-cubes $\square''$, which are
unions of $L^d$ cubes from the partition $\pi_{k+1}$" (P5 p. 502 [checked]); the cover is overlapping (P1
(2.26) [review]). For $F,\Omega\subset\mathbb T_{k+1}$ and $m\in\mathbb N$ define the *block openings*
$$\mathrm{Op}_m(F):=\bigcup\{\mathrm{Bl}(c):\mathrm d(\mathrm{Bl}(c),F)\ge m\},\qquad
\mathrm{Op}_m(F;\Omega):=\bigcup\{\mathrm{Bl}(c):\mathrm{Bl}(c)\subset\Omega,\ \mathrm d(\mathrm{Bl}(c),F)\ge m\}.$$

UNCERTAIN (minor): P1 is not explicit whether $\pi'_j$ contains the $L$-blocks at *every* offset. P5 (2.4)
(the shifts by $\frac{L-1}2$) is consistent with every offset and $L$ odd. The family of all $L$-blocks
does not depend on whether blocks are indexed by a corner or by a centre, so the definition above
agrees with P5 whenever P5's cover is the full family. Nothing in Part I uses $L$ odd.

**Lemma I.2.6 (openings).** Let $m\ge1$.
(a) Every point of $\mathrm{Bl}(c)$ is within $L-1$ of every other; $x\in\mathrm{Bl}(x)$.
(b) $\mathrm{Op}_m(F)\cap F^{\sim(m-1)}=\varnothing$ and $\mathrm{Op}_m(F)^c\subset F^{\sim(m+L-2)}$.
(c) If $\Omega$ is a union of $L$-blocks, then $\mathrm{Op}_m(F;\Omega)\subset\Omega\setminus F^{\sim(m-1)}$ and
$\Omega\setminus\mathrm{Op}_m(F;\Omega)\subset F^{\sim(m+L-2)}$.
(d) $\mathrm{Op}_m(F)$ and $\mathrm{Op}_m(F;\Omega)$ are decreasing in $F$, and $\mathrm{Op}_m(F;\Omega)$ is increasing in $\Omega$.

*Proof.* (a) Coordinates of points of $\mathrm{Bl}(c)$ lie in $\{c_i,\dots,c_i+L-1\}$. (b) A point of a block at
distance $\ge m$ from $F$ is at distance $\ge m$ from $F$. If $\mathrm d(x,F)\ge m+L-1$, then by (a)
$\mathrm d(\mathrm{Bl}(x),F)\ge m$, so $x\in\mathrm{Op}_m(F)$. (c) The first inclusion as in (b). If $x\in\Omega$, some
$\mathrm{Bl}(c_0)\ni x$ is contained in $\Omega$; if moreover $\mathrm d(x,F)\ge m+L-1$ then $\mathrm d(\mathrm{Bl}(c_0),F)\ge m$
and $x\in\mathrm{Op}_m(F;\Omega)$. (d) Immediate. $\square$

### I.2.4 The continuous torus, centres and $N_r$

**Definition I.2.7.** $\mathbb T^c_k:=(\mathbb R/n_k\mathbb Z)^d$ in scale-$k$ cube units, with the cyclic sup-distance
$\operatorname{dist}_\infty$. The cube of $x\in\mathbb T_k$ is $\square_x:=x+[0,1]^d$ and its centre
$\mathrm c(x):=x+\frac12\mathbb 1$. For a box $B=\prod_i\{a_i,\dots,a_i+s_i-1\}$ (cyclic intervals) its centre is
$\mathrm c(B):=(a_i+\frac{s_i}2)_i$. For $\Gamma\subset\mathbb T^c_k$ and real $r\ge0$,
$$N_r(\Gamma):=\{x\in\mathbb T_k:\ \operatorname{dist}_\infty(\Gamma,\square_x)\le r\}.$$
The map $p\mapsto p/L$ is well defined $\mathbb T^c_k\to\mathbb T^c_{k+1}$ because $n_k=Ln_{k+1}$.

**Lemma I.2.8.** Let $p\in\mathbb T^c_k$ and $\rho\in\mathbb N$.
(a) $\operatorname{dist}_\infty(p,\square_y)\le\operatorname{dist}_\infty(p,\square_x)+\mathrm d(x,y)$, and
$\operatorname{dist}_\infty(\mathrm c(x),\square_y)\le\max\{\mathrm d(x,y)-\frac12,0\}$. Hence
$N_r(\Gamma)^{\sim m}\subset N_{r+m}(\Gamma)$.
(b) $\operatorname{dist}_\infty(p/L,\square_{x^\uparrow})\le\operatorname{dist}_\infty(p,\square_x)/L$; hence $X\subset N_r(\Gamma)$
implies $X^\uparrow\subset N_{r/L}(\Gamma/L)$.
(c) In every coordinate, the cubes of $N_{\rho+4}(p)$ have their $i$-th index in a cyclic interval of at
most $2\rho+10$ points.
(d) A box of side $\le2\rho+10$ lies in $N_{\rho+4}$ of its centre.

*Proof.* (a) Per coordinate, a point of $[x_i,x_i+1]$ is within $|x_i-y_i|_n$ of $[y_i,y_i+1]$; from the
centre the bound improves by $\frac12$. (b) $\square_x/L\subset\square_{x^\uparrow}$ in scale-$(k+1)$ units, and
$p\mapsto p/L$ divides distances by $L$. (c) $\operatorname{dist}(p_i,[x_i,x_i+1])\le\rho+4$ forces a lift of $x_i$
into $[p_i-\rho-5,\ p_i+\rho+4]$, an interval of length $2\rho+9$, which contains at most $2\rho+10$
integers. (d) For a cube $x$ of the box, $|x_i+\frac12-a_i-\frac{s_i}2|\le\frac{s_i-1}2$, so its distance to the
centre is $\le\max\{\frac{s_i-2}2,0\}\le\rho+4$. $\square$

### I.2.5 Small sets, hulls and boxes

**Definition I.2.9.** A *cyclic interval* of $\mathbb Z/n\mathbb Z$ is $\{a,a+1,\dots,a+s-1\}$, $1\le s\le n$; a *box* is a
product of cyclic intervals, and its *side* is the largest of their lengths $s_i$. A set
$X\subset\mathbb T_k$ is *small* if each coordinate projection $X_i:=\{x_i:x\in X\}$ lies in a cyclic interval
of length $s$ with $2s<n_k$. For small nonempty $X$, $J_i$ is the shortest cyclic interval containing
$X_i$, $\mathrm{Hull}(X):=\prod_iJ_i$, and $\mathrm{side}(X):=\max_i|J_i|$ (P6 p. 22 [review]: "the smallest
rectangular parallelepiped").

**Lemma I.2.10.** Let $X$ be small and nonempty.
(a) $J_i$ is unique: it is the complement of the unique longest gap (maximal cyclic interval disjoint
from $X_i$).
(b) $X\subset\mathrm{Hull}(X)$, $\mathrm{Hull}(X)$ is small, and $\mathrm{Hull}(\mathrm{Hull}(X))=\mathrm{Hull}(X)$.
(c) If $X$ has sup-diameter $e$ with $4e+2<n_k$, then $X$ is small and $\mathrm{side}(X)\le e+1$.
(d) If $X\subset N_{\rho+4}(p)$ for a point $p$ and $n_k\ge4\rho+21$, then $X$ is small and
$\mathrm{side}(X)\le2\rho+10$.
(e) A small set has an injective lift to $\mathbb Z^d$ (choose in each coordinate the lifts in the integer
interval lifting $J_i$), which preserves $\mathrm d$ between points of $\mathrm{Hull}(X)$ and maps $\mathrm{Hull}(X)$ onto
the integer hull of the lift.

*Proof.* (a) If $X_i$ lies in an interval $I$ with $2|I|<n$, the gap containing $I^c$ has more than $n/2$
points and every other gap lies in $I$ and has fewer than $n/2$; shortest covering intervals are
complements of longest gaps. (b) Clear from (a). (c) For $x_0\in X$, $X_i$ lies in the interval of $2e+1$
points centred at $x_{0,i}$, and $2(2e+1)<n$; two points of that interval at cyclic distance $\le e$ are at
integer distance $\le e$ in the lift, so $|J_i|\le e+1$. (d) Lemma I.2.8 (c) and $2(2\rho+10)<n_k$. (e)
Points of an interval with fewer than $n/2$ points have cyclic distance equal to the integer distance of
their lifts. $\square$

### I.2.6 Components

**Definition I.2.11 (components; ARCH R3-01).** Let $\omega\ge2$ be an integer and $X\subset\mathbb T_k$ finite.
$x,y\in X$ are *linked in $X$* if there is a chain $x=z_0,\dots,z_m=y$ in $X$ with $\mathrm d(z_{i-1},z_i)<\omega$.
The *components* of $X$ are the classes of this equivalence relation (Lean: classes of
`Relation.ReflTransGen` of the relation `fun a b => a ∈ X ∧ b ∈ X ∧ d a b < ω`; a `Finset (Finset _)`).
At scale $k$ the width is $\omega=\omega_k$ (§I.1.2).

**Lemma I.2.12.** Let $Y\neq Y'$ be components of $X$.
(a) $\mathrm d(Y,Y')\ge\omega$.
(b) If $S\subset X$ and any two points of $S$ are linked by a chain in $X$ (e.g. $S$ is $*$-connected), then $S$
lies in one component. If $X\subset X'$, each component of $X$ lies in one component of $X'$.
(c) If $Y\subset\bigcup_{i=1}^\nu B_i$ with boxes $B_i$ of side $\le b$, then $Y$ has sup-diameter
$\le\nu(b-1)+(\nu-1)(\omega-1)\le\nu(b+\omega)$.
(d) If $x\in X$ and $\mathrm d(x,y)<\omega$ with $y\in X$, then $x,y$ lie in the same component.

*Proof.* (a), (b), (d) are the definition. (c) Keep the boxes meeting $Y$ and join $i,j$ when
$\mathrm d(B_i\cap Y,B_j\cap Y)<\omega$; this graph is connected because $Y$ is a class. Between two points of $Y$
take a path of $p\le\nu-1$ edges: the distance is at most the sum of the $p+1$ box diameters ($\le b-1$
each) and of the $p$ gaps ($\le\omega-1$ each). $\square$

### I.2.7 Disjoint neighbourhoods; local and global sets near a component

This is the geometric part of Lemma F (ARCH §3.7) and Lemma L (a) (ARCH §3.8).

**Lemma I.2.13 (disjoint neighbourhoods).** Let $Y\neq Y'$ be components of $X$ for the width $\omega$, and
$a,m\in\mathbb N$. Then $\mathrm d\big(Y^{\sim(a+m)},Y'^{\sim(a+m)}\big)\ge\omega-2(a+m)$. In the flow at scale
$k\ge1$, assuming $\lambda_{k-1}\ge0$ (so that $R_{k-1}\le\hat R_{k-1}$ by (I.3); audit P1-02), with $U=Y^{\approx}=Y^{\sim([R_{k-1}]+1)}$,
$U'=Y'^{\approx}$ and $\omega=\omega_k=2[\hat R_{k-1}]+L+11$:
$$\mathrm d(U^{\sim m},U'^{\sim m})\ge L+9-2m,\qquad\text{so }U^{\sim m}\cap U'^{\sim m}=\varnothing\ \text{for }m\le\tfrac{L+8}2 .\tag{I.4}$$
In particular $U^{\sim}\cap U'^{\sim}=\varnothing$ (the hypothesis of the factorization P5 (1.22), p. 493
[checked]), the sets $U^{\sim4}$ are pairwise disjoint, and so are the sets $U^{\sim6}$ if $L\ge4$.

*Proof.* Lemma I.2.1 (b) and Lemma I.2.12 (a); in the flow $[R_{k-1}]\le[\hat R_{k-1}]$ by (I.3), which uses $\lambda_{k-1}\ge0$. (Without it
the statement fails: for $\beta a<1$ the running radius exceeds $\hat R_{k-1}$, audit P1-02.) $\square$

**Lemma I.2.14 (local equals global near a component).** Let $Y$ be a component of $X$ (width $\omega$), and
$t\in\mathbb N$ with $2t<\omega$. For every $x\in Y^{\sim t}$:
(a) $\mathrm d(x,X)=\mathrm d(x,Y)$; hence $X^{\sim n}\cap Y^{\sim t}=Y^{\sim n}\cap Y^{\sim t}$ for every $n\le t$;
(b) $\mathrm d(x,X^c)=\mathrm d(x,Y^c)$; hence $(X^c)^{\sim n}\cap Y^{\sim t}=(Y^c)^{\sim n}\cap Y^{\sim t}$ for every $n$.

In the flow at scale $k_1$ (a core scale, Part III) with $a=[R_{k_1-1}]+1$, $U=X^{\approx}$,
$W=(X^c)^{\approx2}$ and the local sets $U^Y=Y^{\approx}$, $W^Y=(Y^c)^{\approx2}$: on $(U^Y)^{\sim m}$ with
$m\le\frac{L+8}2$ the global sets $U^{\sim n}$ ($n\le m$) and $W$ agree with the local ones.

*Proof.* (a) Every other component $Y'$ has $\mathrm d(x,Y')\ge\omega-t>t\ge\mathrm d(x,Y)$. (b) $X^c\subset Y^c$ gives
$\ge$. If $x\notin Y$ then $x\notin X$ (by (a), $\mathrm d(x,Y')>0$ for $Y'\ne Y$), so both sides vanish. If
$x\in Y$, let $\delta:=\mathrm d(x,Y^c)$, take $y\in Y^c$ at distance $\delta$ and a chain $x=z_0,\dots,z_\delta=y$
as in Lemma I.2.1 (c). The points $z_0,\dots,z_{\delta-1}$ are at distance $<\delta$ from $x$, hence in $Y$, so
$\mathrm d(y,Y)\le1$ and $\mathrm d(y,Y')\ge\omega-1>0$; thus $y\in X^c$. The flow statement is (a), (b) with
$t=a+m$ and $2(a+m)<\omega_{k_1}$, which is $m\le\frac{L+8}2$. $\square$

### I.2.8 Localization domains modulo $\Omega^c$

**Definition I.2.15** (P5 (1.33)–(1.34) [checked]). $\mathcal D_k$ is the set of nonempty nn-connected
$X\subset\mathbb T_k$; this is Def-2 `IsPolymer` with block side $ML^k$ (frozen), which contains P1's class
of connected unions of $\pi'_k$-blocks (P1 (2.26) [review]). For $\Omega\subset\mathbb T_k$:
$$\mathcal D_k(\mathrm{mod}\,\Omega^c):=\{X\in\mathcal D_k:\ \text{every $*$-component of }\Omega^c\text{ is contained in $X$ or disjoint from $X$}\},$$
$$d_k(X\,\mathrm{mod}\,\Omega^c):=\inf\{|\Gamma|:\ \Gamma\subset\textstyle\bigcup_{x\in X}\square_x\ \text{a connected finite union of segments meeting every }\mathrm{Bl}\in\pi'_k\text{ with }\mathrm{Bl}\cap X\cap\Omega\ne\varnothing\},$$
with $|\Gamma|$ the length in scale-$k$ cube units (P5 writes $\frac1M|\Gamma|_\eta$ in the scale where cubes have
side $M$). UNCERTAIN: P5 does not say which adjacency defines the components of $\Omega^c$. We take
$*$-components (the connected components of the closed set $\bigcup_{x\notin\Omega}\square_x$, which is how P5
treats domains, "in the continuous torus", p. 488). The summability (1.35) and the bounds (1.39) that use
these objects are Part II's; Part I only fixes the definitions.

---
## I.3 The region calculus

The region rules of P5 §2 and P6 §2 are written below as explicit set functions on the cube tori,
with Balaban's distance conditions converted to index distances by Lemma I.2.2. The analytic content of
the decompositions (which characteristic function is attached to which cube) is Part II's; here only
the sets matter. The step $k\to k+1$ takes the region $Z_k$ *after* $R^{(k)}$ and after the removal
overwrite (§I.3.4).

### I.3.1 One step as set functions

**Data.** Reals $R_{k-1},R_k\ge0$ (the running radii $R_j=R^{\rm run}_j=R_{\rm base}\lambda_j^2$ of P5 (1.2)) and the bookkeeping
sequence $\lambda$ of §I.1.2 (in the flow $\lambda=\hat\lambda$). The *radius hypotheses* (audit P1-03), used by Lemmas I.3.8, I.3.9 and
everything after them, are
$$(\mathrm{RH})\qquad\lambda\ \text{nondecreasing},\quad\lambda_j\ge1,\quad0\le R_j\le R_{\rm base}\lambda_j^2\ \ (j\ge0),\quad R_{\rm base}\ge4L+20 ;$$
they give $r_j=\lceil R_{\rm base}\lambda_j^2\rceil\ge R_{\rm base}$, $R_j\le r_j$, $R_{k-1}\le r_{k-1}\le r_k$. In the flow they hold by (I.3) and the
remark after it ($\lambda_k\ge\hat\lambda_k-2\ge1$ when $\hat\lambda_0\ge3$). A finite set $Z_k\subset\mathbb T_k$ with $Z_0=\varnothing$.
*The case $k=0$* (audit P1-07) is defined separately: $Z_0=\varnothing$, $U_0:=\varnothing$, $U'_0:=\varnothing$, and $R_{-1}$ is never used
(rows (R1), (R2) below are read with these values; every other row is the same formula).

**Definition I.3.1 (one step).** All neighbourhoods of sets in $\mathbb T_{k+1}$ are taken in $\mathbb T_{k+1}$
("from now on the operations $\sim$ and $\approx$ are taken in the $k+1$st scale", P5 p. 502 [checked]).

| | Set | Definition | Source [checked] |
|---|---|---|---|
| (R1) | $U_k\subset\mathbb T_k$ | $Z_k^{\approx}=Z_k^{\sim([R_{k-1}]+1)}$ ($U_0=\varnothing$) | P5 (2.1), (1.2) |
| (R2) | $U'_k\subset\mathbb T_{k+1}$ | $(U_k)^\uparrow$ | P5 (2.2) |
| (R3) | $\Omega'_{k+1}$ | $\mathrm{Op}_{[R_k]+2}(U'^{\sim3}_k)$ | P5 (2.3) |
| (R4) | $\mathsf P_{k+1}$; $\Omega_{k+1}$ | any $\mathsf P_{k+1}\subset\Omega'_{k+1}$; $\ \Omega_{k+1}:=\mathrm{Op}_1(\mathsf P^{\sim3}_{k+1};\Omega'_{k+1})$ | P5 (2.6), (2.8) |
| (R5) | $\mathsf Q_{k+1},\mathsf R_{k+1}$; $\Omega''_{k+1}$ | any $\mathsf Q_{k+1}\subset\Omega^{\sim3}_{k+1}$, $\mathsf R_{k+1}\subset\Omega_{k+1}$; $\ F''_{k+1}:=\mathsf Q^{\sim([R_k]+2)}_{k+1}\cup\mathsf R^{\sim(2[R_k]+4)}_{k+1}$; $\ \Omega''_{k+1}:=\mathrm{Op}_1(F''_{k+1};\Omega_{k+1})$ | P5 (2.14), (2.43), (2.45) |
| (R6) | $\mathsf S_{k+1}$; $Z^{(0)}_{k+1}$ | any $\mathsf S_{k+1}\subset\Omega''^{\sim-3}_{k+1}$; $\ F^Z_{k+1}:=(\Omega''^c_{k+1})^{\sim4}\cup\mathsf S^{\sim}_{k+1}$; $\ Z^{(0)}_{k+1}:=\mathrm{Op}_{[2R_k]+3}(F^Z_{k+1})^c$ | P6 (2.1), (2.3) |
| (R7) | $\mathcal N_{k+1}$ | $\mathsf P_{k+1}\cup\mathsf Q_{k+1}\cup\mathsf R_{k+1}\cup\mathsf S_{k+1}$ (new large-field cubes) | ARCH §3.2 |
| (R8) | $Z^{\rm pre}_{k+1}$ | $\mathrm{Hull}_{\mathrm{crit}_{k+1}}(Z^{(0)}_{k+1})$ (Definition I.3.3) if $k+1\le k_0$; $Z^{(0)}_{k+1}$ if $k+1>k_0$ | P6 p. 22 [review]; ARCH §3.5 |
| (R9) | $Z_{k+1}$ | $Z^{\rm pre}_{k+1}$ minus the components removed by $R^{(k+1)}$ ($k+1\le k_0$); $Z^{\rm pre}_{k+1}$ otherwise | §I.4 |

The translations: (R3) is Lemma I.2.2 applied to P5 (2.3). In (R4), "$\square''\subset\Omega'_{k+1}$,
$\square''\cap\mathsf P^{\sim3}=\varnothing$" is "$\mathrm d(\square'',\mathsf P^{\sim3})\ge1$". In (R5),
$(\mathsf Q^\sim)^{\approx}=\mathsf Q^{\sim([R_k]+2)}$ and $(\mathsf R^{\sim2})^{\approx2}=\mathsf R^{\sim(2[R_k]+4)}$ by Lemma I.2.1 (b),
since $\approx$ at scale $k+1$ adds $[R_k]+1$. In (R6), P6 (2.3) is Lemma I.2.2 with
$\mathrm d\ge[2R_k]+3$; $\Omega''^{\sim-3}:=((\Omega''^c)^{\sim3})^c$ (P6 p. 4). $\Omega'_{k+1}$ and $\Omega_{k+1}$ are unions of
$L$-blocks, so the constrained openings in (R4)–(R5) are those of Lemma I.2.6 (c).

**Remark (P5 (2.46)).** P5 (2.46) states $\Omega_{k+1}\cap\Omega''^c_{k+1}\subset[(\mathsf Q^\sim)^{\approx}\cup(\mathsf R^{\sim2})^{\approx2}]^{\sim\frac{L-1}2}$. From
(2.45) as printed one gets the neighbourhood of radius $L-1$ (Lemma I.3.5 (c)), not $\frac{L-1}2$: a cube of $\Omega$
can lie in a block $\square''\subset\Omega$ that meets $F''$ only at its far corner. Part I uses only the radius
$L-1$; nothing depends on P5's sharper constant.

### I.3.2 The hull closure

**Definition I.3.2 (hull round).** Fix the scale $j$, the width $\omega=\omega_j$ and the critical side $b$.
For finite $X\subset\mathbb T_j$,
$$H_b(X):=X\cup\bigcup\{\mathrm{Hull}(C):\ C\text{ a component of }X,\ C\text{ small},\ \mathrm{side}(C)\le b\}.$$

**Definition I.3.3 (canonical hull closure; ARCH LFR-07, §I.0 item 4).** $X_0:=X$, $X_{t+1}:=H_b(X_t)$,
$\mathrm{Hull}_b(X):=X_{N}$ with $N:=n_j^d=|\mathbb T_j|$. A component $C$ of $X_t$ that is small with
$\mathrm{side}(C)\le b$ is said to be *hulled in round $t$*, and $\mathrm{Hull}(C)$ is its *hull box*.

**Lemma I.3.4 (hull closure).**
(a) $X_t\subset X_{t+1}$; if $X_{t+1}=X_t$ then $X_s=X_t$ for all $s\ge t$; and $X_{N+1}=X_N$.
(b) Every component $C$ of $\mathrm{Hull}_b(X)$ that is small with $\mathrm{side}(C)\le b$ is a box: $C=\mathrm{Hull}(C)$.
(c) Every component of $X_t$ lies in one component of $X_{t+1}$. Every component $C'$ of $X_{t+1}$ is the union
of the components of $X_t$ contained in it and of the hull boxes of those among them that are hulled in round
$t$. Every component of $\mathrm{Hull}_b(X)$ contains a component of $X$.
(d) $\mathrm{Hull}_b(X)$ is a function of $X$ (determinism), and $X\subset\mathrm{Hull}_b(X)$.

*Proof.* (a) $H_b(X)\supset X$. As long as $X_{t+1}\ne X_t$ the cardinality grows by at least one, and it is
bounded by $N$, so $X_N=X_{N+1}$. (b) $\mathrm{Hull}(C)\subset H_b(X_N)=X_N$; a box is $*$-connected, so
$\mathrm{Hull}(C)$ lies in one component of $X_N$, which meets $C$ and hence is $C$; thus $\mathrm{Hull}(C)\subset C$.
(c) Components of $X_t$ are linked sets in $X_{t+1}\supset X_t$ (Lemma I.2.12 (b)). A point of $X_{t+1}$ lies in
$X_t$, hence in a component of $X_t$, or in a hull box $\mathrm{Hull}(C)$, which is $*$-connected and contains $C$; so it
lies in the component of $X_{t+1}$ containing that component of $X_t$. The last claim follows by induction
on $t$. (d) Clear. $\square$

Hull boxes of one round may grow into other components; the components so touched merge in the next
round (by (c)). This is the "contact caused by a hull" of ARCH (U2), and it is counted as a merge (§I.4.3).

**Remark (the closure is an architectural extension of P6 p. 22; audit P1-06).** P6 p. 22 [review; the sentence is quoted
in the audit] says that a component of diameter below the critical size is replaced "by a smallest rectangular
parallelepiped containing it"; it describes one replacement and does not say what happens when the new box touches
another component. The one-pass rule $H_b$ and the closure $\mathrm{Hull}_b$ are different set functions: in $d=2$ with
$\omega=5$, $b=40$, the L-shaped component $\{(0,y):0\le y\le20\}\cup\{(x,20):0\le x\le20\}$ and the point $(24,0)$ give after one
round a single $\omega$-component that is not a box, and a second round adds e.g. $(22,10)$ (audit P1-06). This document uses
the closure; it is therefore a **definition of the architecture (an extension of P6), not a transcription**. What is used
downstream, and for which version it is proved:
- Lemma I.3.4 (b) (every small component of side $\le b$ of the output is a box) holds for the closure and fails for the
  one-pass rule (the example above); it is used by Lemma I.4.8 (point spines are boxes), Lemma C4 and Lemma C. So the
  bookkeeping needs the closure.
- The inclusions of Lemma I.3.5, the generating-set statements Lemmas I.3.10, I.3.12 and the attribution of Lemma I.3.8 use
  only $Z^{(0)}_{k+1}\subset Z^{\rm pre}_{k+1}$ and $Z^{\rm pre}_{k+1}\setminus Z^{(0)}_{k+1}\subset(Z^{(0)}_{k+1})^c\subset\Omega''_{k+1}$ (Lemma I.3.5 (e)); they hold for both.
- The budget recursion (B) (Lemma B, Part II §II.5.6) charges every cube of $Z^c_k\cap Z'$ at the volume rate, whether it is a
  hull cube or not, and the one-step operator of Part II is defined on the region $Z^{\rm pre}_{k+1}$ produced by the closure;
  hull cubes lie in $\Omega''_{k+1}$, where the operator bound of P6 (3.4)–(3.9) covers them (§II.5.6). So (B) is proved for the closure.

### I.3.3 Lemma G: inclusions, attribution, locality, separation

**Lemma I.3.5 (inclusions).** For the step of Definition I.3.1:
(a) $U'^{\sim([R_k]+4)}_k\subset\Omega'^c_{k+1}\subset U'^{\sim([R_k]+L+3)}_k$.
(b) $\Omega_{k+1}\subset\Omega'_{k+1}$, $\ \Omega_{k+1}\cap\mathsf P^{\sim3}_{k+1}=\varnothing$, $\ \Omega'_{k+1}\setminus\Omega_{k+1}\subset\mathsf P^{\sim(L+2)}_{k+1}$.
(c) $\Omega''_{k+1}\subset\Omega_{k+1}$, $\ \Omega''_{k+1}\cap F''_{k+1}=\varnothing$, $\ \Omega_{k+1}\setminus\Omega''_{k+1}\subset\mathsf Q^{\sim([R_k]+L+1)}_{k+1}\cup\mathsf R^{\sim(2[R_k]+L+3)}_{k+1}$.
(d) $(F^Z_{k+1})^{\sim([2R_k]+2)}\subset Z^{(0)}_{k+1}\subset(F^Z_{k+1})^{\sim([2R_k]+L+1)}$.
(e) $U'_k\subset\Omega'^c_{k+1}\subset\Omega^c_{k+1}\subset\Omega''^c_{k+1}\subset F^Z_{k+1}\subset Z^{(0)}_{k+1}\subset Z^{\rm pre}_{k+1}$, and
$\mathcal N_{k+1}\subset Z^{(0)}_{k+1}$; precisely $\mathsf P\subset\Omega'\setminus\Omega$, $\mathsf Q\cup\mathsf R\subset\Omega''^c$, $\mathsf S\subset F^Z$.
(f) (P5 (1.20) [checked]) $\Omega_{k+1}\supset\Omega''_{k+1}\supset(Z^{\rm pre}_{k+1})^c$, and, as fine sets,
$Z_k^c\supset\Omega_{k+1}$. More precisely, in scale-$k$ units, $\operatorname{dist}_\infty(Z_k,\Omega_{k+1})\ge([R_k]+4)LM+([R_{k-1}]+1)M$,
which implies P7 (2.1) [checked: "$\mathrm{dist}_j(Z_j,\Omega_{j+1})>2(L+1)M+M[R_{j-1}]+LM[R_j]$"].
(g) (P6 (2.6) [checked]) $\big((Z^{\rm pre c}_{k+1})^{\approx2}\big)^{\sim}\cap\big((\Omega''^c_{k+1})^{\sim3}\cup\mathsf S_{k+1}\big)=\varnothing$.
(h) If $\mathsf P_{k+1}=\mathsf Q_{k+1}=\mathsf R_{k+1}=\mathsf S_{k+1}=\varnothing$, then $\Omega'_{k+1}=\Omega_{k+1}=\Omega''_{k+1}$ (P7 p. 498).
(i) (P7 p. 503 [checked]) For $m\in\mathbb N$ with $\lceil m/L\rceil\le[R_k]+4$, as fine sets
$U_k^{\sim m}\subset U'^{\sim\lceil m/L\rceil}_k\subset\Omega'^c_{k+1}\subset\Omega^c_{k+1}$, and $U^c_k\cap U^{\sim m}_k\subset Z^c_k$. In particular, for
$L\ge2$, the ring $U^c_k\cap U^{\sim9}_k$ lies in $Z^c_k\cap\Omega^c_{k+1}\subset\Omega''_k\cap\Omega^c_{k+1}$.

*Proof.* (a) Lemma I.2.6 (b) with $F=U'^{\sim3}$, $m=[R_k]+2$, and Lemma I.2.1 (b). (b), (c) Lemma I.2.6 (c) with
$m=1$ and $F=\mathsf P^{\sim3}$, resp. $F=F''$; for (c), $(F'')^{\sim(L-1)}=\mathsf Q^{\sim([R_k]+L+1)}\cup\mathsf R^{\sim(2[R_k]+L+3)}$.
(d) Lemma I.2.6 (b) with $m=[2R_k]+3$. (e) $U'\subset U'^{\sim([R_k]+4)}\subset\Omega'^c$ by (a); $\Omega\subset\Omega'$;
$\Omega''\subset\Omega$; $\Omega''^c\subset(\Omega''^c)^{\sim4}\subset F^Z\subset(F^Z)^{\sim([2R_k]+2)}\subset Z^{(0)}$ by (d);
$Z^{(0)}\subset Z^{\rm pre}$ by Lemma I.3.4 (d). $\mathsf P\subset\Omega'$ and $\mathsf P\cap\Omega=\varnothing$ by (b); $\mathsf Q\cup\mathsf R\subset F''$ and
$\Omega''\cap F''=\varnothing$ by (c); $\mathsf S\subset\mathsf S^\sim\subset F^Z$. (f) The first chain is (e). Fine sets: $Z_k\subset U_k\subset U'_k$, and
by (a) and (b) every cube of $\Omega_{k+1}$ is at index distance $\ge[R_k]+5$ from $U'_k$, i.e. at distance
$\ge([R_k]+4)LM$ (scale-$k$ units, Lemma I.2.2) from $U'_k$; every point of $Z_k$ has the sup-ball of radius
$([R_{k-1}]+1)M$ inside $U_k\subset U'_k$, so the distances add. The bound exceeds P7's since
$4LM+M\ge2(L+1)M+M$. (g) By Lemma I.2.6 (b), $\mathrm d(\mathrm{Op}_{[2R_k]+3}(F^Z),F^Z)\ge[2R_k]+3$, hence
$\mathrm d(Z^{(0)c},(\Omega''^c)^{\sim3}\cup\mathsf S)\ge[2R_k]+4$; $(Z^{\rm pre c})\subset Z^{(0)c}$, and
$((\cdot)^{\approx2})^\sim=(\cdot)^{\sim(2[R_k]+3)}$ with $2[R_k]+3<[2R_k]+4$. (h) $\mathrm{Op}_1(\varnothing;\Omega)=\Omega$ for a union
of blocks $\Omega$. (i) Lemma I.2.4 (a) gives $(U_k^{\sim m})^\uparrow\subset U'^{\sim\lceil m/L\rceil}_k$, and a cube lies in its parent;
then (a). The ring avoids $Z_k$ because $U_k\supset Z_k$, and $Z^c_k\subset\Omega''_k$ by (f) at scale $k$; $\lceil9/L\rceil\le5\le[R_k]+4$. $\square$

**Definition I.3.6 (seeds).** The *seeds* of the step $k\to k+1$ are the sets $Z^\uparrow$, $Z$ a component of
$Z_k$ (*old seeds*), and the singletons $\{q\}$, $q\in\mathcal N_{k+1}$ (*new seeds*). For a seed $\sigma$ put
$s_\sigma:=s_*=4$ if $\sigma$ is old and $s_\sigma:=s'=5$ if it is new.

**Lemma I.3.7 (seeds).** (a) Every seed lies in $Z^{(0)}_{k+1}$ and in one component of $Z^{(0)}_{k+1}$ (hence of
$Z^{\rm pre}_{k+1}$). (b) Seeds are pairwise disjoint.

*Proof.* (a) Lemma I.3.5 (e). For an old seed $Z^\uparrow$: two points of $Z$ linked by steps $<\omega_k$ have
coarsenings linked by steps $\le\lceil(\omega_k-1)/L\rceil\le[\hat R_k]+8<\omega_{k+1}$ (Lemma I.2.4 (a),
$L\ge2$, $\hat R_{k-1}\le\hat R_k$), and $Z^\uparrow\subset Z^{(0)}_{k+1}$. (b) If $x^\uparrow=y^\uparrow$ with $x\in Z$, $y\in Z'$,
$Z\ne Z'$, then $\mathrm d(x,y)\le L-1<\omega_k$ (Lemma I.2.4 (b)), contradicting Lemma I.2.12 (a). New cubes
are not in $U'_k$: $\mathsf P\subset\Omega'$ and $\mathsf Q\subset\Omega^{\sim3}$, $\mathsf R,\mathsf S\subset\Omega$ are at distance $\ge[R_k]+2$ from
$U'_k$ by (a), (b) of Lemma I.3.5. $\square$

**Lemma I.3.8 (attribution; this is (G1) of §I.5.2).** Assume (RH) (audit P1-03: version 1 assumed only $R_k\le r_k$,
$R_{k-1}\le r_k$, and the statement is false for $\lambda_k=0$, where $r_k=0$). For every $x\in Z^{(0)}_{k+1}$ there is a seed $\sigma$ such that $x$ and $\sigma$ lie in the same
component of $Z^{(0)}_{k+1}$ and $\mathrm d(x,\sigma)\le s_\sigma r_k$.

*Proof.* We build a chain from $x$ to a seed through points of $Z^{(0)}:=Z^{(0)}_{k+1}$, each step of length
$<\omega_{k+1}$; then $x$ and the seed are in the same component (Lemma I.2.12 (d)), and the length of the
chain bounds $\mathrm d(x,\sigma)$. Write $\rho:=[R_k]$.

1. By Lemma I.3.5 (d) there is $f\in F^Z$ with $\mathrm d(x,f)\le[2R_k]+L+1$. On a geodesic from $x$ to $f$ (Lemma
   I.2.1 (c)) let $x'$ be the point at distance $[2R_k]+2$ from $f$ (or $x'=x$). Then $x'\in(F^Z)^{\sim([2R_k]+2)}\subset Z^{(0)}$,
   $\mathrm d(x,x')\le L-1$ and $\mathrm d(x',f)\le[2R_k]+2$; and $f\in Z^{(0)}$.
2. $f\in\mathsf S^\sim$: there is $q\in\mathsf S$ with $\mathrm d(f,q)\le1$. Stop (new seed).
   Otherwise $f\in(\Omega''^c)^{\sim4}$: there is $g\in\Omega''^c\subset Z^{(0)}$ with $\mathrm d(f,g)\le4$.
3. If $g\in\Omega\setminus\Omega''$, then by Lemma I.3.5 (c) there is $q\in\mathsf Q$ with $\mathrm d(g,q)\le\rho+L+1$ or $q\in\mathsf R$ with
   $\mathrm d(g,q)\le2\rho+L+3$. Stop.
4. If $g\in\Omega'\setminus\Omega$, there is $q\in\mathsf P$ with $\mathrm d(g,q)\le L+2$ (Lemma I.3.5 (b)). Stop.
5. If $g\in\Omega'^c$, there is $u\in U'_k\subset Z^{(0)}$ with $\mathrm d(g,u)\le\rho+L+3$ (Lemma I.3.5 (a)). Then
   $u=v^\uparrow$ with $v\in U_k$, and some $z\in Z_k$ has $\mathrm d(v,z)\le[R_{k-1}]+1$, so
   $\mathrm d(u,z^\uparrow)\le\lceil([R_{k-1}]+1)/L\rceil$ (Lemma I.2.4 (a)). Stop at the old seed $Z^\uparrow$, $Z\ni z$.

*Steps are short.* The steps are $\le L-1$, $[2R_k]+2$, $1$, $4$, $\rho+L+1$, $2\rho+L+3$, $L+2$, $\rho+L+3$ and
$\lceil([R_{k-1}]+1)/L\rceil\le\frac{r_k+1}L+1$. Since $[2R_k]+2\le2\rho+3$, all are $\le2\rho+L+3<\omega_{k+1}$, because
$\omega_{k+1}=2[R_{\rm base}\lambda_k^2]+L+11$ and $\rho=[R_k]\le[R_{\rm base}\lambda_k^2]$ by (RH) (this is where the enlarged width of §I.0 item 1 is
needed).
All chain points lie in $Z^{(0)}$ (seeds by Lemma I.3.7).

*Lengths.* With $r:=r_k\ge R_k$ and $[2R_k]\le2r$:
- new seed $\mathsf S$: $\le2r+L+1+1\le5r$;
- $\mathsf Q$: $\le2r+L+1+4+r+L+1=3r+2L+6\le5r$;
- $\mathsf R$: $\le2r+L+1+4+2r+L+3=4r+2L+8\le5r$;
- $\mathsf P$: $\le2r+L+1+4+L+2=2r+2L+7\le5r$;
- old seed: $\le2r+L+1+4+r+L+3+\frac{r+1}L+1\le3r+\frac rL+2L+10\le4r$, using $r(1-\frac1L)\ge2L+10$.

Each of the last inequalities holds because $r\ge R_{\rm base}\ge4L+20$ (by (RH)) and $L\ge2$. $\square$

**Lemma I.3.9 (locality; P5 p. 493, P6 p. 15).** Assume (RH). Let $Z'$ be a component of $Z^{\rm pre}_{k+1}$. Let $\Sigma'$ be the
seed data *inside $Z'$*: the components $Z$ of $Z_k$ with $Z^\uparrow\subset Z'$, and $\mathsf P':=\mathsf P\cap Z'$, $\mathsf Q':=\mathsf Q\cap Z'$,
$\mathsf R':=\mathsf R\cap Z'$, $\mathsf S':=\mathsf S\cap Z'$. Denote by $(\cdot)(\Sigma')$ the sets of Definition I.3.1 computed from
$Z_k':=\bigcup_{Z\in\Sigma'}Z$ and $\mathsf P',\dots,\mathsf S'$. Then:
(a) the constraints of (R4)–(R6) hold for $\Sigma'$;
(b) $\Omega'^c_{k+1}\cap Z'=\Omega'^c(\Sigma')$, $\Omega^c_{k+1}\cap Z'=\Omega^c(\Sigma')$, $\Omega''^c_{k+1}\cap Z'=\Omega''^c(\Sigma')$ and
$Z^{(0)}_{k+1}\cap Z'=Z^{(0)}(\Sigma')$;
(c) $Z'=\mathrm{Hull}_{\mathrm{crit}_{k+1}}(Z^{(0)}(\Sigma'))$ if $k+1\le k_0$, and $Z'=Z^{(0)}(\Sigma')$ otherwise; the local result is
one component;
(d) consequently $\Omega^c_{k+1}=\bigsqcup_{Z'}\Omega^c(\Sigma'(Z'))$ over the components of $Z^{\rm pre}_{k+1}$, and likewise for
$\Omega'^c$, $\Omega''^c$, $Z^{(0)}$; the localized region history of $Z'$ (Definition I.4.4) is generated by the rules
from its own seed data.

*Proof.* *Monotonicity.* $U'$ is increasing in $Z_k$; $\Omega'=\mathrm{Op}(U'^{\sim3})$ is decreasing in $U'$;
$\Omega=\mathrm{Op}_1(\mathsf P^{\sim3};\Omega')$ is decreasing in $\mathsf P$ and increasing in $\Omega'$; $\Omega''$ likewise in $(\mathsf Q,\mathsf R)$ and
$\Omega$; $Z^{(0)}=\mathrm{Op}(F^Z)^c$ is increasing in $F^Z$, which is increasing in $\Omega''^c$ and $\mathsf S$ (Lemma I.2.6 (d)).
Hence $\Omega'(\Sigma')\supset\Omega'$, $\Omega(\Sigma')\supset\Omega$, $\Omega''(\Sigma')\supset\Omega''$ and $Z^{(0)}(\Sigma')\subset Z^{(0)}$. (a) follows:
$\mathsf P'\subset\mathsf P\subset\Omega'\subset\Omega'(\Sigma')$, $\mathsf Q'\subset\Omega^{\sim3}\subset\Omega(\Sigma')^{\sim3}$, $\mathsf R'\subset\Omega(\Sigma')$,
$\mathsf S'\subset\Omega''^{\sim-3}\subset\Omega''(\Sigma')^{\sim-3}$.

*Local sets lie in $Z'$.* By Lemma I.3.8 applied to $\Sigma'$, every point of $Z^{(0)}(\Sigma')$ is joined to a seed of
$\Sigma'$ by a chain in $Z^{(0)}(\Sigma')\subset Z^{(0)}_{k+1}$ with steps $<\omega_{k+1}$; the seed lies in $Z'$, so the point
does. The local complements $\Omega'^c(\Sigma')\subset\Omega^c(\Sigma')\subset\Omega''^c(\Sigma')$ lie in $Z^{(0)}(\Sigma')$ (Lemma I.3.5 (e)).
Hence each local set is contained in the corresponding global set intersected with $Z'$.

*Global sets intersected with $Z'$ are local.* We use: (W) if $y\in Z^{(0)}_{k+1}$ and $\mathrm d(y,x)<\omega_{k+1}$ for
some $x\in Z'\cap Z^{(0)}_{k+1}$, then $y\in Z'$. We go level by level.
- $\Omega'^c$: let $x\in Z'\cap\Omega'^c$ and $\mathrm{Bl}\ni x$. Then $\mathrm d(\mathrm{Bl},U'^{\sim3})\le\rho+1$ ($\rho:=[R_k]$), so some
  $u\in U'_k$ has $\mathrm d(x,u)\le\rho+L+3$; by (W), $u\in Z'$. As in step 5 of Lemma I.3.8, $u$ is within
  $\lceil([R_{k-1}]+1)/L\rceil$ of $z^\uparrow$ for some $z$ in a component $Z$ of $Z_k$; by (W) $z^\uparrow\in Z'$, so
  $Z^\uparrow\subset Z'$, $Z\in\Sigma'$ and $u\in U'(\Sigma')$. Hence $\mathrm d(\mathrm{Bl},U'(\Sigma')^{\sim3})\le\rho+1$ for every $\mathrm{Bl}\ni x$,
  i.e. $x\in\Omega'^c(\Sigma')$.
- $\Omega^c$: let $x\in Z'\cap\Omega^c$; if $x\in\Omega'^c$ use the previous item. Otherwise let $\mathrm{Bl}\ni x$ with
  $\mathrm{Bl}\subset\Omega'(\Sigma')$. If $\mathrm{Bl}$ had a point $y\in\Omega'^c$, then $\mathrm d(x,y)\le L-1$, $y\in Z'$ by (W), so
  $y\in\Omega'^c(\Sigma')$, which contradicts $\mathrm{Bl}\subset\Omega'(\Sigma')$. So $\mathrm{Bl}\subset\Omega'$, and since $x\notin\Omega$, $\mathrm{Bl}$
  meets $\mathsf P^{\sim3}$: some $p\in\mathsf P$ has $\mathrm d(x,p)\le L+2$, $p\in Z'$ by (W), $p\in\mathsf P'$. So $\mathrm{Bl}$ meets
  $\mathsf P'^{\sim3}$ and $x\notin\Omega(\Sigma')$.
- $\Omega''^c$: the same argument with $\Omega$ in place of $\Omega'$ and the witnesses $q\in\mathsf Q$ ($\mathrm d\le\rho+L+1$) or
  $q\in\mathsf R$ ($\mathrm d\le2\rho+L+3$).
- $Z^{(0)}$: let $x\in Z'\cap Z^{(0)}$ and $\mathrm{Bl}\ni x$. Some $f\in F^Z$ has $\mathrm d(f,\mathrm{Bl})\le[2R_k]+2$, so
  $\mathrm d(x,f)\le[2R_k]+L+1$ and $f\in Z'$ by (W). If $f\in\mathsf S^\sim$, the $\mathsf S$-cube is within $1$ of $f$, in $Z'$, in $\mathsf S'$;
  if $f\in(\Omega''^c)^{\sim4}$, the witness $g\in\Omega''^c$ is within $4$ of $f$, in $Z'$, hence in $\Omega''^c(\Sigma')$. Either way
  $f\in F^Z(\Sigma')$, so $\mathrm{Bl}\not\subset\mathrm{Op}_{[2R_k]+3}(F^Z(\Sigma'))$, and $x\in Z^{(0)}(\Sigma')$.

All witness distances are $\le2\rho+L+3<\omega_{k+1}$.

(c) $Z^{(0)}_{k+1}\cap Z'=Z^{(0)}(\Sigma')$ is a union of components of $Z^{(0)}_{k+1}$ (a component meeting $Z'$ lies in $Z'$),
and the relation "linked" on it is the same in both sets. By induction on the rounds, $X_t\cap Z'=X_t(\Sigma')$
with the same components: a round-$t$ component lies in one final component, and its hull box lies in the
same one; hull boxes of components outside $Z'$ lie outside $Z'$. At $t=N$, $X_N\cap Z'=Z'$. (d) follows from
(b), since every complement set lies in $Z^{(0)}_{k+1}\subset Z^{\rm pre}_{k+1}=\bigsqcup Z'$. $\square$

**Lemma I.3.10 (separation of the generating set; P2 (1.1)–(1.3)).** Consider the domains $\Omega_1,\dots,\Omega_{k+1}$
produced by $k+1$ steps of Definition I.3.1 (with the overwrite of §I.3.4 for removals), as fine sets. Then:
(a) $\Omega_1\supset\Omega''_1\supset Z_1^c\supset\Omega_2\supset\cdots\supset\Omega_{k+1}\supset\Omega''_{k+1}\supset Z^c_{k+1}$ (P5 (1.20));
(b) each $\Omega_j$ is a union of $\pi'_j$-blocks of $\pi_j$-cubes, hence of $L^j$-blocks of fine sites;
(c) for $1\le j\le k$, $\operatorname{dist}_\infty(\Omega^c_j,\Omega_{j+1})>LMR_j$ in scale-$j$ units (P2 (1.1) with "$RM$" $=LMR_j$).
Consequently, if moreover $R_j\ge R_{\rm base}$ for $1\le j\le k$ (running $\lambda_j\ge1$; audit P1-04: without it the separation
$>LMR_j$ does not give a fixed parameter), then with $\varrho:=LMR_{\rm base}$ and the terminal field $\Omega_{k+2}:=\varnothing$, the family
$(\Omega_1,\dots,\Omega_{k+1},\Omega_{k+2})$ is a Lean `GeneratingSet d L (M * n (k+1)) (k+1) ϱ` (`Balaban/Multiscale/GeneratingSet.lean`;
fields `top` ($\Omega_{k+2}=\varnothing$), `subset`, `blockUnion` (by (b)), `separation` (by (c): fine distance $>LMR_jL^j\ge\varrho L^j$; its
distance is the $\ell^1$ torus distance, which dominates the sup-distance)).
(d) (a)–(c) hold for every region rule with $Z^{(0)}_j\subset Z^{\rm pre}_j$, in particular for the one-pass hull and for the hull closure
of Definition I.3.3 (remark after Lemma I.3.4, audit P1-06): the proof uses only $\Omega''^c_j\subset Z^{(0)}_j\subset Z^{\rm pre}_j$.

*Proof.* Without removals: (a) is Lemma I.3.5 (f) at each step, together with $\Omega^c_j\subset\Omega''^c_j\subset Z_j$. (b)
$\Omega_j=\mathrm{Op}_1(\cdot;\Omega'_j)$ is a union of $L$-blocks, and a $\pi_j$-cube is a union of $L^j$-blocks of fine sites
($ML^j$ is a multiple of $L^j$). (c) $\Omega^c_j\subset Z_j$ and Lemma I.3.5 (f):
$\operatorname{dist}\ge([R_j]+4)LM>LMR_j$. Removals: Lemma I.3.12. $\square$

### I.3.4 The removal overwrite

**Definition I.3.11 (removal overwrite; ARCH R3-08, §3.2).** If $R^{(k)}$ ($k\le k_0$) removes a component $Z$ of
$Z^{\rm pre}_k$, then, as fine sets, for every $1\le j\le k$:
$$\Omega_j\mapsto\Omega_j\cup Z,\quad\Omega''_j\mapsto\Omega''_j\cup Z,\quad\Omega'_j\mapsto\Omega'_j\cup Z,\quad Z_j\mapsto Z_j\setminus Z,\quad
\mathsf X_j\mapsto\mathsf X_j\setminus Z\ (\mathsf X=\mathsf P,\mathsf Q,\mathsf R,\mathsf S),$$
and $Z_k:=Z^{\rm pre}_k\setminus Z$. Several removed components at the same scale are treated one after the other
(the order is irrelevant, as they are disjoint). By Lemma I.4.3 below, for $j<k$ the overwrite deletes
exactly the lineage of $Z$ at scale $j$.

**Lemma I.3.12 (the overwrite preserves the generating set).** After the overwrite at scale $k$:
(a) the nesting of Lemma I.3.10 (a) holds;
(b) each $\Omega_j\cup Z$ ($j\le k$) is a union of $\pi'_j$-blocks;
(c) for $1\le j<k$, $\operatorname{dist}_\infty\big((\Omega_j\cup Z)^c,\ \Omega_{j+1}\cup Z\big)>LMR_j$ in scale-$j$ units.

*Proof.* (a) The same fine set is added to $\Omega_j$ and $\Omega''_j$ and removed from $Z_j$, so
$\Omega_j\cup Z\supset\Omega''_j\cup Z\supset(Z_j\setminus Z)^c=Z^c_j\cup Z\supset\Omega_{j+1}\cup Z$.
(b) For $j<k$, a $\pi_k$-cube is a box of $L^{k-j}\ge L$ $\pi_j$-cubes per side, hence a union of $L$-blocks.
For $j=k$ and $x\in Z$: the cubes within $L-1$ of $x$ are not in another component of $Z^{\rm pre}_k$ (distance
$\ge\omega_k>L$), so they lie in $Z\cup(Z^{\rm pre}_k)^c\subset Z\cup\Omega''_k\subset Z\cup\Omega_k$; thus $\mathrm{Bl}(x)\subset\Omega_k\cup Z$.
(c) $(\Omega_j\cup Z)^c=\Omega^c_j\setminus Z$. Its distance to $\Omega_{j+1}$ is at least the old one. As fine sets
$\Omega^c_j\subset Z_j\subset Z^{\rm pre}_k$ (regions grow, Lemma I.4.3), so $\Omega^c_j\setminus Z$ lies in the other components of
$Z^{\rm pre}_k$, at index distance $\ge\omega_k$ from $Z$ in $\mathbb T_k$, i.e. at fine distance
$\ge(\omega_k-1)ML^k\ge(2[\hat R_{k-1}]+L+10)ML^k$, which exceeds $LMR_jL^j\le MR_{k-1}L^k$ (fine units) for
$j\le k-1$. $\square$

### I.3.5 Lemma S (lattice separation) and the enclosing diameter

**Lemma I.3.13 (Lemma S; ARCH R2-02, R3-03 (iv)).** Let $d\ge2$ and let $A_1,\dots,A_n\subset\mathbb Z^d$ be finite and pairwise
$*$-separated (no $a\in A_i$, $a'\in A_j$, $i\ne j$, with $|a-a'|_\infty\le1$). Put $A:=\bigcup_iA_i$. Say that
$x\notin A$ is *enclosed* by $A$ if every infinite nn path from $x$ that leaves every finite set meets $A$.
(a) If $x$ is enclosed by $A$, it is enclosed by a single $A_{i_0}$, and indeed by a single $*$-component of
$A_{i_0}$.
(b) If moreover $Q\subset\mathbb Z^d\setminus A$ is a box containing $x$, then that $*$-component has sup-diameter
$\ge\mathrm{side}(Q)+1$.
(c) A union of pairwise $*$-separated boxes encloses no point.

*Cited input* (external, not in the source library): for a finite nn-connected $C\subset\mathbb Z^d$, $d\ge2$, the
exterior boundary $\partial^{\rm ext}C:=\{y\notin C:\ y\text{ nn-adjacent to }C,\ y\text{ joined to infinity by a nn path avoiding }C\}$
is $*$-connected (Timár, Proc. AMS 141 (2013) 475–480, Lemma 2; Deuschel–Pisztora, PTRF 104 (1996)
467–482, Lemma 2.1, stronger form). COUNT verified Timár's text.

*Proof.* Let $C$ be the nn-component of $\mathbb Z^d\setminus A$ containing $x$. If $C$ were infinite, it would contain
an infinite simple nn path from $x$ (König's lemma for the locally finite infinite connected graph $C$),
which leaves every finite set and avoids $A$; so $C$ is finite. Every point $y\notin C$ nn-adjacent to $C$
lies in $A$ (otherwise $y\in C$). Hence $\partial^{\rm ext}C\subset A$. It is nonempty (take $c\in C$ with maximal first
coordinate; $c+e_1$ is joined to infinity along $+e_1$ avoiding $C$) and $*$-connected, so it lies in one
$*$-component $K$ of $A$, and $K\subset A_{i_0}$ for one $i_0$ (pairwise $*$-separation). A nn path from $x$ to infinity
leaves the finite set $C$ for the last time at some step $c\to y$; then $y\in\partial^{\rm ext}C\subset K$. This proves
(a). (b) $Q$ is nn-connected and disjoint from $A$, so $Q\subset C$. For each coordinate $i$, if $c\in C$ minimizes
the $i$-th coordinate then $c-e_i\in\partial^{\rm ext}C$ (the ray $c-te_i$ avoids $C$), and similarly at the maximum.
So $\partial^{\rm ext}C$, hence $K$, has extent $\ge(\max_Cx_i-\min_Cx_i)+2\ge(\mathrm{side}(Q)-1)+2$ in the coordinate where
$Q$ has its side. (c) By (a) an enclosed point would be enclosed by a single box; the complement of a box is
nn-connected and infinite. $\square$

*On the torus* (ARCH R3-03 (v)). If $A\cup\{x\}$ lies in the interior $Q^{\sim-1}$ of a small box $Q\subset\mathbb T_k$, lift $Q$
injectively (Lemma I.2.10 (e)); $x$ is joined to $\partial Q:=Q\setminus Q^{\sim-1}$ by a nn path in $Q$ avoiding $A$ iff the lift
of $x$ is not enclosed by the lift of $A$ (outside the lifted box one can go to infinity freely, and a path
to infinity must cross the lifted $\partial Q$). For $k\le k_0$ every set to which Part III applies the lemma
lies in one window component, of sup-diameter $\le\nu_{\max}(k)(\mathrm{crit}_k+\omega_k)$ (Lemma I.2.12 (c)), and
(H-T) of §I.5.2 makes the box $Q$ (that set's $1$-neighbourhood hull) small.

### I.3.6 Lemma P (path out of a thickened union of separated boxes)

ARCH keeps Lemma P (REPAIRS §C.1) for the case that $\omega_k$ is ever reduced; under the present width it is
not used (Lemma I.2.14 gives P7's own path box by box). It is stated in site units.

**Lemma I.3.14 (Lemma P).** Let $d\ge2$, $\beta\ge1$, $\delta\ge1$ be integers, $B_1,\dots,B_N\subset\mathbb Z^d$ boxes of sides $\le\beta$,
pairwise $*$-separated, and $\hat B_i\supset B_i^{(1)}:=\{z:\operatorname{dist}_\infty(z,B_i)\le1\}$ boxes of sides $\le\beta+2\delta$. Put
$A:=\bigcup_iB_i$ and $D:=\bigcup_i\hat B_i$. For $x\in D$ let $C$ be the nn-component of $D$ containing $x$ and
$N_C:=\#\{i:B_i\subset C\}$. Then there is a nn path $x=x_0,\dots,x_n$ with $x_n\notin D$ and
$$n\le\beta+N_C(3\beta+2\delta),$$
whose first at most $\beta$ steps run inside one box $B_i$ (only if $x\in A$) and whose later points, except $x_n$,
lie in $D\setminus A$. If $x\notin A$, the first term $\beta$ is absent.

*Proof.* If $x\in B_i$, walk along a coordinate direction to the nearest face of $B_i$ and one step beyond:
at most $\beta$ steps, ending at a point at sup-distance $1$ from $B_i$, which lies in $\hat B_i\setminus A$ (other boxes
are at distance $\ge2$ from $B_i$). So assume $x\notin A$. Walk along $+e_1$. Whenever the next point lies in a box
$B_i$, let $I_1\times I_2$ be the section of $B_i$ in the coordinate plane of $e_1,e_2$ through the current point
$x'$ (so $x'_1=\min I_1-1$, $x'_2\in I_2$), and detour: along $+e_2$ to second coordinate $\max I_2+1$, along $+e_1$
to first coordinate $\max I_1+1$, along $-e_2$ back to $x'_2$. Every detour point is at sup-distance exactly $1$
from $B_i$, hence not in $B_i$, and not in any other box (those are at distance $\ge2$ from $B_i$). The first
coordinate never decreases, so $B_i$ is not met again. Stop at the first point outside $D$ ($D$ is finite, so
this happens). All points before the stop lie in $D\setminus A$ and in $C$; every box met is nn-adjacent to a
point of $C$ and lies in $D$, so it lies in $C$: at most $N_C$ detours, each with at most $2\beta$ steps in the
$e_2$ direction. The $e_1$-steps number at most (extent of $C$ in coordinate $1$) $+1$. Every $z\in C$ lies in some
$\hat B_i$, which is nn-connected and contained in $D$, hence in $C$, together with $B_i$; so $C=\bigcup_{B_i\subset C}\hat B_i$, and
its projection to coordinate $1$, an interval, is covered by $N_C$ intervals of at most $\beta+2\delta$ points:
the extent is $\le N_C(\beta+2\delta)-1$. Total: $\le N_C(\beta+2\delta)+2\beta N_C$. $\square$

*Translation to ARCH's form.* Cubes of side $M$ sites, boxes of side $\le b$ cubes ($\beta=Mb$), $a=[R_{q-1}]+1$,
$U=A^{\sim a}$, $D=U^{\sim3}=\bigcup_iB_i^{\sim(a+3)}$ (cube neighbourhoods, boxes of side $\le M(b+2a+6)$ sites, so
$\delta=M(a+3)$), $W=(A^c)^{\sim2a}$: points of $D\setminus A$ lie in $A^c\subset W$ and in $U^{\sim3}$; the exit point is
nn-adjacent to $D$, so it lies in $U^{\sim4}\cap W$; for $x\in A\cap W$ the initial straight segment has at most $M(2a+1)$
steps (the sup-distance from a point of a box to its complement is attained along a coordinate) and stays
in $W$. The length is $\le M(2a+1)+N_C(3Mb+2M(a+3))\le3N_CM(b+a+5)$.

### I.3.7 The geometric part of Lemma F and of Lemma L

The analytic statements of Lemma F (support of kernels in $U^\sim$, factorization P5 (1.22)) are Part II's.
They rest on the following geometric facts.

**Lemma I.3.15 (neighbourhoods along lineages).** Let $Y$ be a component of $Z_j$ ($j\ge1$) and $Y'$ the component of
$Z^{\rm pre}_{j+1}$ containing $Y^\uparrow$ (Lemma I.3.7). Then, as fine sets, for every $m\in\mathbb N$,
$$(Y^{\approx})^{\sim m}\subset(Y'^{\approx})^{\sim\lceil m/L\rceil}.$$
Consequently, if $Y$ is a component of the lineage at scale $j$ of a component $Z$ of $Z_k$ (Definition I.4.2),
then $(Y^{\approx})^{\sim m}\subset(Z^{\approx})^{\sim m}$ as fine sets, and $(Y^\approx)^{\sim m}\subset(Z^\approx)^{\sim1}$ if $m\le L^{k-j}$.

*Proof.* A $\pi_j$-cube at index distance $\le[R_{j-1}]+1+m$ from $Y$ has its parent at distance
$\le\lceil([R_{j-1}]+1)/L\rceil+\lceil m/L\rceil\le[R_j]+1+\lceil m/L\rceil$ from $Y^\uparrow\subset Y'$ (Lemma I.2.4 (a); $[R_{j-1}]\le[R_j]$),
and a cube lies in its parent as fine sets. Iterate along the successor chain (Definition I.4.2), using
$\lceil\lceil m/L\rceil/L\rceil=\lceil m/L^2\rceil$. $\square$

**Lemma I.3.16 (box-by-box reduction at the core; ARCH R3-14 (e), Lemma L (a)).** Let $C$ be a component of $Z_{k_1}$
(a core box in Part III), $U^C:=C^\approx$, $W^C:=(C^c)^{\approx2}$, and $U:=Z_{k_1}^\approx$, $W:=(Z^c_{k_1})^{\approx2}$. Let $\Phi$ be a
set function of *range* $\varpi$ (i.e. $\Phi(X)\cap E$ depends only on $X\cap E^{\sim\varpi}$ for all $E$). If
$m+\varpi\le\frac{L+8}2$, then on $(U^C)^{\sim m}$ the sets $\Phi(U)$, $\Phi(W)$, $\Phi(U^{\sim n})$ ($n\le m$) coincide with $\Phi(U^C)$,
$\Phi(W^C)$, $\Phi((U^C)^{\sim n})$, and the sets $(U^{C'})^{\sim(m+\varpi)}$ of distinct components $C'$ are pairwise disjoint.

*Proof.* Lemma I.2.14 with $t=[R_{k_1-1}]+1+m+\varpi$, and Lemma I.2.13. $\square$

This applies to P7's generating set $\mathbb B_{k_1,k}$ of (2.13) [checked]:
$\mathbb B_{k_1,k}=(\mathbb B_{k_1}(W_{k_1})\cap Z_{k_1})\cup(\mathbb B_k\cap Z^c_{k_1}\cap Z_k)\cup(\mathbb B_k(U_k)\cap Z^c_k\cap U^\sim_k)$. On each core box its
first piece is the single-box one, so the check that $\mathbb B_{k_1,k}$ satisfies P2 (1.1)–(1.3) for a multi-box core
reduces to the single-box check of P7, box by box, *provided the minimal generating sets $\mathbb B_{k_1}(\cdot)$ of P3
(4.4)–(4.6) have range $\varpi\le\frac{L+8}2-m$ in $\pi_{k_1}$-cubes*. UNCERTAIN: P3 (4.7)–(4.8) [page image] give
$\Omega_1(X)\subset X_0=X'^{\sim4L}$ in $M_1$-cubes with $4LM_1+r_0M_1\le LM$, which suggests $\varpi\le1$; this is to be
confirmed in Part II, where $\mathbb B_k(X)$ is defined.

**Remark (scope of Lemmas I.2.14 and I.3.16; LF-V4-AUDIT V4-01).** These lemmas identify global and local
sets only on the neighbourhoods $(U^C)^{\sim m}$ of the components $C$ of the ripe lineage. Elsewhere the
global $U_{k_1}=Z_{k_1}^\approx$ may contain far components of any shape: a Pre component of single cubes on a grid
of spacing $<\omega_{k_1}$ has diameter $>\mathrm{crit}_{k_1}$, is not hulled, and its $U^{\sim3}$ contains points whose
distance to $(U^{\sim3}_{k_1})^c$ exceeds $3MR_{k_1}+8M$ (V4-01). So ARCH's Lemma L (c), stated for every
$x\in\mathbb B_{k_1}(W_{k_1})\cap U^{\sim3}_{k_1}$ with the global sets, is false as printed. Part III must state (3.11)′ for
$x$ in the localized support $\bigcup_C(U^C)^{\sim3}$ of the ripe lineage, with the local $U^C,W^C$, and must show
that the characteristic-function and gradient bounds of P7 (3.7) restrict to that domain; Part I supplies
only the geometric identification above (open item O-3, §I.7).

---
## I.4 Histories, bookkeeping, window states

### I.4.1 Region histories, successors and lineages

**Definition I.4.1 (region history).** Fix integers $0\le k_0\le K$ and cube tori $\mathbb T_0,\dots,\mathbb T_K$ with
$n_k=Ln_{k+1}$. A *region history* up to scale $K$ consists of, by recursion on $k$:
- $Z_0:=\varnothing$;
- for each step $k\to k+1$ ($0\le k<K$), a *step record* $\varsigma_{k+1}=(\mathsf P_{k+1},\mathsf Q_{k+1},\mathsf R_{k+1},\mathsf S_{k+1})$ satisfying
  the constraints of Definition I.3.1 relative to $Z_k$; the derived sets $U_k,U'_k,\Omega'_{k+1},\Omega_{k+1},\Omega''_{k+1},Z^{(0)}_{k+1}$,
  $\mathcal N_{k+1}$ and $Z^{\rm pre}_{k+1}$ are the set functions of Definition I.3.1;
- for each $1\le k\le k_0$, an *$R$-record*: a set $\mathrm{Rem}_k$ of components of $Z^{\rm pre}_k$, each of them ripe
  (Definition I.4.6 below); the ripe components not in $\mathrm{Rem}_k$ are *kept*. Then
  $Z_k:=Z^{\rm pre}_k\setminus\bigcup\mathrm{Rem}_k$, and the overwrite of Definition I.3.11 is applied for each removed component.
  For $k>k_0$, $Z_k:=Z^{\rm pre}_k$.

Ripeness at scale $k$ depends on the bookkeeping of §I.4.3, which is computed from the history up to the
pre-$R$ region of scale $k$; so the history and its bookkeeping are defined by one simultaneous recursion,
which is causal. A history is *admissible* iff it is generated by these rules; there is no condition
involving bounds (ARCH §3.2). The analytic part of the history (indices of the decompositions, the
kept-branch data of $R$) is Part II's and Part III's; it does not affect the region history except through
$\mathrm{Rem}_k$. *Lean*: a structure with one field per scale and a predicate `Admissible` expressing that each
field is the value of the set functions; the bookkeeping is a function of the structure.

**Definition I.4.2 (successor, lineage).** For a component $Y$ of $Z_j$ ($j<K$), $\mathrm{succ}(Y)$ is the
component of $Z^{\rm pre}_{j+1}$ containing $Y^\uparrow$ (Lemma I.3.7). For a component $Z$ of $Z^{\rm pre}_k$ (or of $Z_k$) and
$j\le k$, the *ancestors at scale $j$* are: $\mathrm{Anc}_k(Z):=\{Z\}$, and for $j<k$, $\mathrm{Anc}_j(Z)$ is the set of components
$Y$ of $Z_j$ with $\mathrm{succ}(Y)\in\mathrm{Anc}_{j+1}(Z)$. The *lineage* is $\mathrm{Lin}_j(Z):=\bigcup\mathrm{Anc}_j(Z)$ (ARCH writes
$Z_j\cap Z$).

**Lemma I.4.3 (regions grow; lineages).** In the overwritten history:
(a) the overwrite of a removed component $Z^\star$ of $Z^{\rm pre}_{j+1}$ deletes from $Z_j$ exactly the components $Y$ with
$\mathrm{succ}(Y)=Z^\star$, and recursively their ancestors at lower scales; consequently, for every component $Y$ of $Z_j$,
$\mathrm{succ}(Y)$ is a component of $Z_{j+1}$ (it survived $R^{(j+1)}$);
(b) as fine sets, $Z_j\subset Z^{\rm pre}_{j+1}$ and $Z_j\subset Z_{j+1}\subset\dots\subset Z_k$;
(c) for a component $Z$ of $Z_k$ (or $Z^{\rm pre}_k$) and $j\le k$: $\mathrm{Lin}_j(Z)=\{y\in Z_j:\ y\subset Z\text{ as fine sets}\}$, i.e. the
lineage is "$Z_j\cap Z$";
(d) $Z_j=\bigsqcup_Z\mathrm{Lin}_j(Z)$ over the components $Z$ of $Z_k$, and lineages of distinct components are disjoint.

*Proof.* (a) As fine sets $Y\subset Y^\uparrow\subset\mathrm{succ}(Y)$, and distinct components of $Z^{\rm pre}_{j+1}$ are disjoint; so
$Y\subset Z^\star$ iff $\mathrm{succ}(Y)=Z^\star$, and otherwise $Y\cap Z^\star=\varnothing$. The overwrite removes the fine set $Z^\star$
from $Z_j$, hence removes exactly these $Y$; by induction the same holds at lower scales. (b) $Y\subset\mathrm{succ}(Y)$ and,
after (a), $\mathrm{succ}(Y)$ survives. (c) "$\subset$": $Y\subset\mathrm{succ}^{(k-j)}(Y)=Z$ as fine sets. "$\supset$": a cube $y$ of $Z_j$
lying in $Z$ belongs to a component $Y$ whose descendant at scale $k$ is a component of $Z_k$ (by (a)) containing $y$,
hence equal to $Z$. A $\pi_j$-cube is contained in or disjoint from a $\pi_k$-cube. (d) From (c). $\square$

**Definition I.4.4 (localized histories; $\mathfrak H_k(Z)$).** The *localized history* of a component $Z$ of $Z^{\rm pre}_k$
consists of the lineages $\mathrm{Lin}_j(Z)$, the step records and derived sets intersected with $Z$ as fine sets
($\mathsf P_j\cap Z$, \dots, $\Omega'^c_j\cap Z$, $\Omega^c_j\cap Z$, $\Omega''^c_j\cap Z$), and the $R$-records of the lineage components. By
Lemma I.3.9 applied at every step, it is itself a region history (on the same tori) whose region at scale
$k$ is $Z$; and the global history is determined by the localized histories of the components (P5 p. 493 [checked]:
"all its elements are determined completely by their restrictions to the large field region $Z_k$"; P6 p. 15).
$\mathfrak H_k(Z)$ is the set of all admissible region histories whose pre-$R$ region at scale $k$ is $Z$ and has $Z$
as its only component (the "maximal set" of P5 (1.27), p. 494 [checked]; ARCH R3-07). The summability (1.27)
over $\mathfrak H_k(Z)$ is Part II's.

### I.4.2 Spines

**Definition I.4.5 (spine).** A *spine at scale $k$* is either a *point* $p\in\mathbb T^c_k$, or the projection
$\Gamma=\pi_k(\tilde\Gamma)$ of a lift $\tilde\Gamma=\bigcup_{i=1}^n[a_i,b_i]\subset\mathbb R^d$, a finite union of segments which is
connected. Its *length* is $\ell(\Gamma):=\sum_i|b_i-a_i|_2$ ($0$ for a point). *Lean*: a structure with a list of pairs
in `EuclideanSpace ℝ (Fin d)` and a connectedness field (e.g. the intersection graph of the segments is
connected); the projection is coordinatewise reduction mod $n_k$. Operations:
- *contraction* $\Gamma/L$ (lift divided by $L$), a spine at scale $k+1$ with $\ell(\Gamma/L)=\ell(\Gamma)/L$;
- *join*: for spines $\Gamma_1,\Gamma_2$ and points $p\in\Gamma_1$, $p'\in\Gamma_2$, choose a lift $\tilde p\in\tilde\Gamma_1$ and the lift $\tilde p'$ of $p'$ nearest
  to $\tilde p$; translate $\tilde\Gamma_2$ by the lattice vector that moves its lift of $p'$ to $\tilde p'$, and add the segment
  $[\tilde p,\tilde p']$. The result is a spine, of length $\ell(\Gamma_1)+\ell(\Gamma_2)+|\tilde p-\tilde p'|_2$;
- $N_r(\Gamma)$ as in Definition I.2.7.

Choices (lifts, nearest points, spanning trees, attributions) are made by a fixed choice function; any
such function makes the bookkeeping a function of the region history, which is all (D1) needs (ARCH R3-12).
In Lean, `Classical.choose` suffices; ARCH's lexicographic tie-breaks are one admissible choice. LF-2 holds
for every choice (§I.5).

### I.4.3 Bookkeeping data and their updates

**Definition I.4.6 (bookkeeping).** Each component $Z$ of $Z^{\rm pre}_k$ and of $Z_k$ carries a spine $\Gamma(Z)$ at scale $k$,
a *gain clock* $b(Z)\in\mathbb N$, a *smallness clock* $s(Z)\in\mathbb N$, and, for $k\le k_0$, a *window state*
$$w(Z)\in\{\mathsf{Pre}\}\cup\{\mathsf{Pending}(q,\nu):q,\nu\in\mathbb N\}\cup\{\mathsf{Active}(q,\nu,\mathcal M):q,\nu\in\mathbb N,\ \mathcal M\subset\mathbb N\text{ finite}\}$$
(Lean `inductive WState | pre | pending (q ν : ℕ) | active (q ν : ℕ) (M : Finset ℕ)`). If $\Gamma(Z)$ is not a point,
$s(Z)$ is the *projected epoch* $s(Z):=k+\max\{1,\lceil\log_L\max\{\ell(\Gamma(Z)),1\}\rceil\}$ (so $s(Z)=k+1$ if $\ell\le L$). The *derived data*: for $\mathsf{Pre}$,
$q:=s$, $\nu:=1$, $\mathcal M:=\varnothing$; for $\mathsf{Pending}(q,\nu)$, $\mathcal M:=\varnothing$; and in every state
$$t^*(Z):=\max\{q+n_q(q),\ s+n_2(s)\},\qquad U(Z):=\tfrac12\textstyle\sum_{\xi\in\mathcal M}\tau_\xi .$$
For $\mathsf{Pre}$, $t^*=s+n_q(s)$ because $n_2\le n_q$ ((F4), §I.5.2). The state is *admissible at scale $k$* (ARCH (B.1)) if
$$\begin{array}{ll}
\mathsf{Pre}: & \Gamma(Z)\text{ is not a point (so }s>k);\\
\mathsf{Pending}(q,\nu): & k<q\le k+h_k+1,\quad1\le\nu\le\nu_{\max}(k);\\
\mathsf{Active}(q,\nu,\mathcal M): & q\le k,\quad1\le\nu\le\nu_{\max}(k),\quad\mathcal M\subset(q,k].
\end{array}\tag{B.1}$$
A component of $Z^{\rm pre}_k$ ($k\le k_0$) is **ripe** if it is Active and $t^*(Z)=k$.

*Change from ARCH.* The projected epoch uses $\max\{1,\cdot\}$, so non-point spines of length $\le1$ are allowed
after events; short spines are replaced by a point only under pure shadows (U1). ARCH (LFR-08) replaced
short event spines by a point too, which can push a merged component with hull parts outside
$N_{\rho+4}$ of that point.

**Definition I.4.7 (spine and clock update at the step $k\to k+1$).** Let $\mu:=k+1$, $\rho:=\rho_\mu$. Fix for every
$x\in Z^{(0)}_\mu$ a seed $\sigma(x)$ as in Lemma I.3.8 (attribution), with $\sigma(x)=\sigma$ for $x\in\sigma$; the
*attribution set* of a seed is $B_\sigma:=\{x:\sigma(x)=\sigma\}$. The *spine piece* of a seed is $\Gamma_\sigma:=\Gamma(Z)/L$ for
$\sigma=Z^\uparrow$ and $\Gamma_\sigma:=\{\mathrm c(q)\}$ for $\sigma=\{q\}$.

1. *Round $0$.* For a component $C$ of $X_0:=Z^{(0)}_\mu$ with seeds $\sigma_1,\dots,\sigma_p$ (all seeds lying in $C$): the
   *contact graph* has vertices $\sigma_i$ and an edge when $\mathrm d(B_{\sigma_i},B_{\sigma_j})<\omega_\mu$. For each edge of a chosen
   spanning tree, choose cubes $a\in B_{\sigma_i}$, $a'\in B_{\sigma_j}$ with $\mathrm d(a,a')<\omega_\mu$ and points $p\in\Gamma_{\sigma_i}$, $p'\in\Gamma_{\sigma_j}$
   with $\operatorname{dist}_\infty(p,\square_a),\operatorname{dist}_\infty(p',\square_{a'})\le\rho+4$, and join $p$ to $p'$. $\Gamma_0(C)$ is the union of the
   pieces $\Gamma_{\sigma_i}$ and these segments.
2. *Round $t+1$* ($\mu\le k_0$ only; hull rounds of Definition I.3.3 with $b=\mathrm{crit}_\mu$). A component $C'$ of $X_{t+1}$ is
   the union of the components $C_1,\dots,C_p$ of $X_t$ in it and of the hull boxes of the hulled ones (Lemma I.3.4
   (c)). Its *parts* are $V_i:=\mathrm{Hull}(C_i)$ with spine $\{\mathrm c(\mathrm{Hull}(C_i))\}$ if $C_i$ is hulled in round $t$, and $V_i:=C_i$
   with spine $\Gamma_t(C_i)$ otherwise. $\Gamma_{t+1}(C')$ is the union of the parts' spines and the segments of a spanning
   tree of the contact graph of the parts (edge iff $\mathrm d(V_i,V_j)<\omega_\mu$), chosen as in round $0$.
3. *Final spine* of a component $Z'$ of $Z^{\rm pre}_\mu$: if $\mu\le k_0$ and $Z'$ is small with $\mathrm{side}(Z')\le\mathrm{crit}_\mu$ (then
   $Z'$ is a box, Lemma I.3.4 (b)), $\Gamma':=\{\mathrm c(Z')\}$; otherwise $\Gamma':=\Gamma_N(Z')$ ($\Gamma_0(Z')$ if $\mu>k_0$).
4. *Pure shadow* ($Z'$ contains exactly one seed, which is old, $\sigma=Z^\uparrow$): then $\Gamma_0=\Gamma(Z)/L$; if this is not a point
   and $\ell(\Gamma(Z))/L\le1$, it is replaced by one of its points. (Only here are short spines replaced.)
5. *Clocks.* $b':=\mu$ if $\mathcal N_\mu\cap Z'\ne\varnothing$, otherwise $b':=\max_ib(Z_i)$ over the old parts. If $\Gamma'$ is a point:
   $s':=s(Z)$ in a pure shadow whose old spine $\Gamma(Z)$ was a point, and $s':=\mu$ otherwise. If $\Gamma'$ is not a point,
   $s'$ is its projected epoch.

ARCH's (U1) is item 4 (with the hull: item 3), (U2) is items 1–2, (U3) is item 3 with item 5, and (U4) is the
kept case of (T6) below.

**Lemma I.4.8 (consistency of the spines; ARCH (3.1), (4.1)).** Assume the conclusion of Lemma I.3.8 with
$s_*,s'$, and $c_0(1-L^{-1})\ge s_*+1$, $c_0\ge s'+1$, $r_k\ge2$. Suppose every component $Z$ of $Z_k$ satisfies
$Z\subset N_{\rho_k+4}(\Gamma(Z))$. Then every component $Z'$ of $Z^{\rm pre}_{k+1}$, with $m$ old parts $Z_1,\dots,Z_m$ (components of
$Z_k$ with $Z_i^\uparrow\subset Z'$) and $r:=|\mathcal N_{k+1}\cap Z'|$ new cubes, satisfies:
$$Z'\subset N_{\rho_{k+1}+4}(\Gamma'),\tag{3.1}$$
$$\ell(\Gamma')\le\sum_{i=1}^m\frac{\ell(\Gamma(Z_i))}L+(m+r-1)D_{k+1}\quad\text{in general, and}\quad\ell(\Gamma')\le\frac{\ell(\Gamma(Z_1))}L\ \text{ if }(m,r)=(1,0).\tag{4.1}$$
Moreover, if $k+1\le k_0$ and (H-T) holds, then $\Gamma'$ is a point iff $Z'$ is small with $\mathrm{side}(Z')\le\mathrm{crit}_{k+1}$, and then $Z'$
is a box with $\Gamma'=\{\mathrm c(Z')\}$.

*Proof.* *Seeds.* For an old seed $\sigma=Z^\uparrow$, $Z^\uparrow\subset N_{(\rho_k+4)/L}(\Gamma(Z)/L)$ (Lemma I.2.8 (b)); for
$x\in B_\sigma$, $\mathrm d(x,Z^\uparrow)\le s_*r_k$, so (Lemma I.2.8 (a)) $\operatorname{dist}_\infty(\Gamma_\sigma,\square_x)\le\frac{c_0r_k+4}L+s_*r_k\le c_0r_k-r_k+2\le\rho_{k+1}$,
using $\frac{c_0}L\le c_0-s_*-1$, $r_k\le r_{k+1}$ and $r_k\ge2$. For a new seed, $\operatorname{dist}_\infty(\mathrm c(q),\square_x)\le s'r_k\le\rho_{k+1}-r_k$.
So $B_\sigma\subset N_{\rho_{k+1}}(\Gamma_\sigma)$. *Parts.* A hull box of side $\le\mathrm{crit}_{k+1}=2\rho_{k+1}+10$ lies in $N_{\rho_{k+1}+4}$ of its
centre (Lemma I.2.8 (d)). *Rounds.* By induction on $t$, every component $C$ of $X_t$ lies in $N_{\rho_{k+1}+4}(\Gamma_t(C))$:
it is the union of its parts, each within $\rho_{k+1}+4$ of its own spine. *Segments.* If two parts $V,V'$ have
cubes $a,a'$ with $\mathrm d(a,a')\le\omega-1$, and $p,p'$ are within $\rho+4$ of $\square_a,\square_{a'}$, then
$|p-p'|_\infty\le(\rho+4+\frac12)+(\omega-1)+(\rho+4+\frac12)=2\rho+8+\omega$, so the segment has Euclidean length
$\le\sqrt d(2\rho+8+\omega)\le D_{k+1}$. The contact graphs are connected: a chain of cubes of $C$ with steps $<\omega$
between two parts passes through parts, and consecutive cubes in different parts give an edge (the parts
cover $C$ by Lemma I.3.4 (c) and by the definition of $B_\sigma$). *Length.* By induction on $t$:
$\ell(\Gamma_t(C))\le\sum_{\text{old }\sigma\subset C}\ell(\Gamma_\sigma)+(\#\{\text{seeds in }C\}-1)D_{k+1}$. Round $0$: $p$ seeds, a tree with $p-1$
edges. Round $t+1$: parts $C_1,\dots,C_p$, each containing at least one seed (Lemma I.3.4 (c)); hulled parts
have length $0$; so $\ell\le\sum_i[\sum_{\sigma\subset C_i}\ell(\Gamma_\sigma)+(\#\mathrm{seeds}(C_i)-1)D]+(p-1)D$, which is the claim. Seeds are
disjoint and each lies in one component, so $\#\mathrm{seeds}(Z')=m+r$. The final spine is either this one, or a
centre, or (pure shadow) a point of $\Gamma(Z)/L$: (4.1) holds in all cases. (3.1) for the final spine: centres and
$\Gamma_N$ are covered above. In the pure-shadow replacement, $Z'\subset N_{\rho_{k+1}}(\Gamma(Z)/L)$ if no hull occurred, and every
point of $\Gamma(Z)/L$ is within Euclidean distance $\ell(\Gamma(Z)/L)\le1$ of the chosen point, so $Z'\subset N_{\rho_{k+1}+1}(p)$.
*Point spines.* If $\Gamma'$ is a point and $k+1\le k_0$: either it is the centre of the box $Z'$, or $Z'$ is a single new cube's
attribution set ($Z'\subset N_{\rho_{k+1}}(\mathrm c(q))$) or a pure shadow with replaced spine ($Z'\subset N_{\rho_{k+1}+1}(p)$); in the
last two cases $Z'$ is small with $\mathrm{side}\le2\rho_{k+1}+10$ by Lemma I.2.10 (d) and (H-T) (which gives
$n_{k+1}\ge4\rho_{k+1}+21$), so it is hulled in the last round and is a box, and by item 3 its spine is its centre.
Conversely item 3. $\square$

### I.4.4 Window states and the transitions (T1)–(T7)

For $k+1\le k_0$, the state of each component $Z'$ of $Z^{\rm pre}_{k+1}$ is defined from its old parts $Z_1,\dots,Z_m$ (with states
$w_i$, data $q_i,\nu_i,\mathcal M_i$, clocks $s_i$, ripeness times $t^*_i$) and from $r:=|\mathcal N_{k+1}\cap Z'|$. Write $\mu:=k+1$,
$s':=s(Z')$, $\Gamma':=\Gamma(Z')$. A *merge* is a step with $r=0$, $m\ge2$ (it includes contacts caused by hulls). The
list is exhaustive: $r\ge1$, or $r=0$ and $m\ge1$ (every component contains a seed).

- **(T1) Pure shadow** ($m=1$, $r=0$; with or without hull).
  - $\mathsf{Pre}$ stays $\mathsf{Pre}$ if $\Gamma'$ is not a point; otherwise it becomes $\mathsf{Active}(\mu,1,\varnothing)$ (*certified entry*).
  - $\mathsf{Active}(q,\nu,\mathcal M)$ keeps its data.
  - $\mathsf{Pending}(q,\nu)$ keeps its data if $\mu<q$, and becomes $\mathsf{Active}(q,\nu,\varnothing)$ if $\mu=q$ (*activation*).
- **(T2) New cubes** ($r\ge1$; any $m\ge0$, any states). *Restart*: the output is $\mathsf{Active}(\mu,1,\varnothing)$ (certified
  entry) if $\Gamma'$ is a point, otherwise $\mathsf{Pre}$. (Clocks: $b'=\mu$.)
- **(T3) Merge with a Pre part** ($r=0$, $m\ge2$, some $w_i=\mathsf{Pre}$). Restart as in (T2).
- **(T4) Merge within the cap** ($r=0$, $m\ge2$, all parts Active or Pending, $\nu':=\sum_i\nu_i\le\nu_{\max}(\mu)$). With $\mathcal M_i:=\varnothing$
  for Pending parts,
  $$\tilde q:=\max_iq_i,\quad E:=\textstyle\bigcup_i\mathcal M_i\cup\{\mu\},\quad t_0:=\max\{\tilde q+n_q(\tilde q),\ s'+n_2(s')\},$$
  $$T:=\min\{t\ge t_0:\ k_1(t)\notin B(E)\},\qquad q':=k_1(T),\qquad\mathcal M':=E\cap(q',\infty).\tag{B.3}$$
  The output is $\mathsf{Pending}(q',\nu')$ if $q'>\mu$ (then $\mathcal M'=\varnothing$) and $\mathsf{Active}(q',\nu',\mathcal M')$ if $q'\le\mu$. The scales in
  $E\cap[0,q']$ are *released*.
- **(T5) Overflow** ($r=0$, $m\ge2$, all parts Active or Pending, $\sum_i\nu_i>\nu_{\max}(\mu)$). Restart as in (T2).
- **(T6) $R$ at scale $k\le k_0$.** $R^{(k)}$ acts exactly on the ripe components. A removed component has no successor
  (overwrite, Definition I.3.11). A *kept* component keeps its set and spine, gets $b:=k$, keeps $s$, and becomes
  $\mathsf{Active}(k,1,\varnothing)$ (certified entry). Every other component (all Pre, all Pending, the non-ripe Active ones) is
  unchanged.
- **(T7) End of the window regime.** After $R^{(k_0)}$, the transfer of §I.5.6 is applied and the window states are
  discarded. For $k_0<k\le K$ there are no window states, no hulls and no $R$.
- **Base.** $Z_0=\varnothing$; if $k_0\ge1$, every component of $Z^{\rm pre}_1$ has $m=0$, $r\ge1$, and is a (T2) output.

$T$ in (B.3) exists because $B(E)$ is finite and $k_1$ is unbounded (Lemma I.4.9 (a)). These are the rules of
REPAIRS §B.1 as adopted in ARCH §3.5; the only change is the clock convention of Definition I.4.6.

### I.4.5 Lemma C4 (closure, horizon, activation)

**Lemma I.4.9 (properties of $k_1$).** Assume $n_q$ is nondecreasing (true when $\lambda$ is). Then:
(a) $c\mapsto c+n_q(c)$ is strictly increasing; $k_1$ is nondecreasing and unbounded; $k_1(t+1)\le k_1(t)+1$;
(b) for $t\ge n_q(0)$ and $c\in\mathbb N$: $k_1(t)=c\iff c+n_q(c)\le t<(c+1)+n_q(c+1)$; in particular $k_1(c+n_q(c))=c$;
(c) if $t<\mu+n_q(\mu)$ then $k_1(t)\le\mu-1$ (for $\mu\ge1$, $t\ge n_q(0)$);
(d) as $t$ runs through $t_0,t_0+1,\dots$ ($t_0\ge n_q(0)$), $k_1(t)$ takes every integer value $\ge k_1(t_0)$, in increasing order.

*Proof.* (a) $c+1+n_q(c+1)>c+n_q(c)$. Monotonicity of `Nat.findGreatest` in $t$; unbounded since $k_1(c+n_q(c))\ge c$.
If $c:=k_1(t+1)\ge1$ then $(c-1)+n_q(c-1)\le c+n_q(c)-1\le t$, so $k_1(t)\ge c-1$. (b) The set
$\{c:c+n_q(c)\le t\}$ is an initial segment of $\mathbb N$ by (a), nonempty for $t\ge n_q(0)$. (c) From (b). (d) From (a). $\square$

**Lemma I.4.10 (Lemma C4).** Assume the hypotheses of LF-2 (§I.5.2: (G1), (G2), (K), (H-T)) and
$\lambda_0\ge\lambda_*$. For every $1\le k\le k_0$ and every component $Z$ of $Z^{\rm pre}_k$ and of $Z_k$:
(a) $w(Z)$ satisfies (B.1). If $Z$ is Active or Pending, it is covered by at most $\nu(Z)$ boxes of side $\le\mathrm{crit}_k$, and
$\ell(\Gamma(Z))\le(\nu(Z)-1)D_k$.
(b) If (T4) is used at scale $\mu$, then
$$\tilde q\le\mu+h_\mu,\qquad k_1(s'+n_2(s'))\le\mu-1,\qquad\max_iq_i\le q'\le\mu+h_\mu+1,\qquad t^*(Z')=T.\tag{B.4}$$
(c) Under (T1), $t^*$ does not increase, $\nu$, $\mathcal M$ and $U$ do not change, and $t^*(Z')\ge\mu$.

*Proof.* By induction over the transitions in their order (step $k\to k+1$, then $R^{(k+1)}$).

(a), cover. *(T1) with an Active or Pending input* covered by boxes $B_1,\dots,B_\nu$ of side $\le\mathrm{crit}_k$: the only seed
of $Z'$ is $Z^\uparrow$, so by (G1) every cube of the round-$0$ component lies in $N_{s_*r_k}(Z^\uparrow)\subset\bigcup_iN_{s_*r_k}(B_i^\uparrow)$.
$B_i^\uparrow$ is a box of side $\le\mathrm{crit}_k/L+2$, and its $s_*r_k$-neighbourhood is a box of side
$\le\mathrm{crit}_k/L+2+2s_*r_k\le\mathrm{crit}_{k+1}$, because $(2c_0r_k+10)/L+2+2s_*r_k\le2c_0r_k+10$ follows from
$c_0(1-L^{-1})\ge s_*$ and $10/L+2\le10$. A hull (Lemma I.3.4) replaces the boxes covering a component by one box. So $\nu$
boxes suffice; $\nu\le\nu_{\max}(k)\le\nu_{\max}(k+1)$. *Entries and restarts* to $\mathsf{Active}(\mu,1,\varnothing)$ have point spines, hence
are boxes of side $\le\mathrm{crit}_\mu$ (Lemma I.4.8). *(T4)*: let every part $Z_i$ be covered by $\nu_i$ boxes of side
$\le\mathrm{crit}_k$. By induction over the hull rounds, every component $C$ of $X_t$ inside $Z'$ is covered by
$\sum_{Z_i^\uparrow\subset C}\nu_i$ boxes of side $\le\mathrm{crit}_\mu$: at round $0$ by (G1) as in (T1) (all seeds of $Z'$ are old); at round
$t+1$, $C'$ is the union of round-$t$ components (covered by induction) and the hull boxes of the hulled ones, each of
which replaces the cover of its component by one box (each component contains a seed, so its count is $\ge1$).
So $Z'$ is covered by $\nu'$ boxes. *(T6) kept*: $Z$ is ripe, hence a box (Lemma I.4.13 (g) at scale $k$, which uses only
the induction hypothesis at earlier transitions), covered by one box.

(a), spine. Entries and restarts with point spines: $\ell=0$. (T1): $\ell'\le\ell/L\le(\nu-1)D_k/L\le(\nu-1)D_{k+1}$ by (4.1).
(T4): by (4.1) with $r=0$, $\ell'\le\sum_i(\nu_i-1)D_k/L+(m-1)D_\mu\le(\nu'-m)D_\mu+(m-1)D_\mu=(\nu'-1)D_\mu$. Hulls give points.

(a), (B.1). Pre outputs have non-point spines by construction. Active outputs of entries, restarts and kept: $q=\mu$ or
$q=k$, $\mathcal M=\varnothing$, $\nu=1$. (T1) keeps Active data, and $\mathcal M\subset(q,k]\subset(q,k+1]$; Pending with $\mu<q$ keeps
$\mu<q\le k+h_k+1\le\mu+h_\mu+1$ ($h$ nondecreasing); activation gives $q=\mu$, $\mathcal M=\varnothing$. (T4): the cap gives
$\nu'\le\nu_{\max}(\mu)$; $\mathcal M'\subset E\subset[0,\mu]$ and $\mathcal M'\subset(q',\infty)$, so $\mathcal M'\subset(q',\mu]$ in the Active case and
$\mathcal M'=\varnothing$ in the Pending case; the horizon $q'\le\mu+h_\mu+1$ is (b). (T6): non-ripe components are unchanged
and their constraints at scale $k$ are those of $Z^{\rm pre}_k$.

(b). By (a), $\ell'\le\nu_{\max}(\mu)D_\mu$, so $s'\le\mu+\max\{1,\lceil\log_L\max(\ell',1)\rceil\}\le\mu+1+\log_L(\nu_{\max}(\mu)D_\mu)$ and $\lambda_{s'}\le2\lambda_\mu$, and
by condition (Λ1) of §I.5.3, $s'+n_2(s')<\mu+n_q(\mu)$; Lemma I.4.9 (c) gives $k_1(s'+n_2(s'))\le\mu-1$.
- Active inputs have $q_i\le k=\mu-1$; Pending inputs have $q_i\le k+h_k+1\le\mu+h_\mu$. So $\tilde q\le\mu+h_\mu$.
- $k_1$ is nondecreasing and $k_1(\tilde q+n_q(\tilde q))=\tilde q$, so $c:=k_1(t_0)=\max\{\tilde q,k_1(s'+n_2(s'))\}\le\mu+h_\mu$.
- Every $\xi\in E$ has $\xi\le\mu$ and $h_\xi\le h_\mu$, so $\mu+h_\mu+1\notin B(E)$.
- By Lemma I.4.9 (d), $q'$ is the least integer $\ge c$ outside $B(E)$; hence $\tilde q\le c\le q'\le\mu+h_\mu+1$.
- $t^*(Z')=\max\{q'+n_q(q'),s'+n_2(s')\}$. Since $k_1(T)=q'$, $q'+n_q(q')\le T$, and $T\ge t_0\ge s'+n_2(s')$; so $t^*\le T$. If
  $T>t_0$, then $k_1(T-1)\in B(E)$ by minimality, so $k_1(T-1)\ne q'$, $k_1(T-1)\le q'-1$, and $T-1<q'+n_q(q')$, i.e.
  $T\le q'+n_q(q')\le t^*$. If $T=t_0$: either $t_0=s'+n_2(s')\le t^*$, or $t_0=\tilde q+n_q(\tilde q)$, in which case $c=\tilde q=q'$ and
  $t_0=q'+n_q(q')\le t^*$.

(c). $q$ is fixed (for Pre, $q=s$). $s$ does not increase: a point spine keeps $s$ (item 5); a non-point spine $\Gamma$ with
$\ell(\Gamma)/L>1$ has $s'=\mu+\max\{1,\lceil\log_L\ell-1\rceil\}=k+\lceil\log_L\ell\rceil=s$ (as $\lceil\log_L\ell\rceil\ge2$); a non-point spine
that becomes a point (by item 4 or by a hull) gets $s'=\mu\le s$. Hence $t^*$ does not increase. A Pre entry has new
$t^*=\mu+n_q(\mu)\le s+n_q(s)$ (old, as $s\ge\mu$), $\nu=1$, $U=0$, unchanged. Activation changes no number. Finally
$t^*(Z')\ge\mu$: if $s$ changed then $s'=\mu$ and $t^*\ge s'$; if not, $t^*$ is unchanged and was $>k$ for components of
$Z_k$ (this is part of the invariant (H6′) of §I.5, proved in the same induction; for Pending, $t^*>q\ge\mu$). $\square$

The pending horizon is at most $h_k+1=O(\log\lambda_k)$ scales, and cores never move backward ((B.4): $q'\ge\max_iq_i$).

### I.4.6 The floor invariant and Lemma C

**Definition I.4.11 (resets).** A component $Y$ (of $Z^{\rm pre}_j$ or $Z_j$) *has a reset at scale $i\le j$* if some ancestor
of $Y$ (Definition I.4.2, including $Y$) at scale $i$ is (i) Pre, or (ii) the output of a restart (T2), (T3), (T5) at
the step $(i-1)\to i$, or (iii) kept by $R^{(i)}$.

**Lemma I.4.12 (floor).** For $j\le k_0$: if $Y$ has a reset at scale $i$, then $Y$ is Pre, or $Y$ is Active or Pending with
core $q(Y)\ge i$, and $q(Y)\ge i+1$ in case (i).

*Proof.* Induction on $j$ along the transitions. If the reset is at $i=j$: in case (i) $Y$ is Pre; in cases (ii), (iii) $Y$ is
Pre or has $q=j$. Otherwise the reset is in the history of some ancestor $Y_0$ at scale $j-1$ with the claim for $Y_0$,
and $Y$ arises from $Y_0$ by (T1), (T2)–(T5), or by $R^{(j)}$ (non-ripe: unchanged; kept: $q=j$).
- (T2), (T3), (T5): $Y$ is Pre or has $q(Y)=j\ge i+1$.
- (T1): if $Y_0$ is Pre, $Y$ is Pre or has $q(Y)=j\ge i+1$ (since $i\le j-1$); if $Y_0$ is Active/Pending, $q(Y)=q(Y_0)$.
- (T4): $Y_0$ is Active or Pending, and $q(Y)=q'\ge\max_iq_i\ge q(Y_0)$ by (B.4).
In each case the bound passes from $Y_0$ to $Y$. $\square$

**Lemma I.4.13 (Lemma C, covered windows).** Assume the hypotheses of Lemma I.4.10. Let $Z$ be Active$(q,\nu,\mathcal M)$ at
scale $k\le k_0$ (a component of $Z^{\rm pre}_k$ or $Z_k$), with lineage $\mathrm{Lin}_j(Z)$, $j\le k$.
- (a) No new large-field cubes appear in the lineage at the steps $j\to j+1$, $q\le j<k$; $b(Z)\le q$; no restart and no
  kept $R$-event occurs in the lineage at scales in $(q,k]$; every ancestor at a scale $j\in[q,k]$ is Active or Pending, and
  its transitions on $[q,k]$ are (T1) and (T4) only.
- (b) For $j\in[q,k]$, $\mathrm{Lin}_j(Z)$ is covered by $\nu$ boxes of side $\le\mathrm{crit}_j$; more precisely $\nu=\sum_{Y\in\mathrm{Anc}_j(Z)}\nu(Y)$ for the
  post-$R$ ancestors at $j\in[q,k)$.
- (c) $\ell(\Gamma(Z))\le(\nu-1)D_k$.
- (d) Each branch of the lineage, followed backwards from $Z$ through (T1) and (T4), ends at a certified entry
  (a (T1) entry, a point output of (T2), (T3), (T5), or a kept component), where it is one box of side $\le\mathrm{crit}$.
- (e4) Every (T4) merge of the lineage at a scale $\xi\le q$ that occurs after the last certified entry of its branch
  satisfies $\xi+h_\xi<q$; every (T4) merge at a scale in $(q,k]$ lies in $\mathcal M$. At scale $q$, every ancestor is one box of
  side $\le\mathrm{crit}_q$, and distinct ancestors are at distance $\ge\omega_q$.
- (f4) $q+n_q(q)\le t^*(Z)<(q+1)+n_q(q+1)$; hence $k_1(t^*(Z))=q$.
- (g) If $Z$ is ripe ($t^*=k$), then $\Gamma(Z)$ is a point, $s+n_2(s)\le k$, no event occurs in the lineage at scales in
  $(s,k]$, and $\mathrm{Lin}_j(Z)$ is one box of side $\le\mathrm{crit}_j$ for every $j\in[s,k]$.

*Proof.* (a) A new cube at the step $j\to j+1$ ($q\le j<k$) produces a (T2) ancestor at scale $j+1>q$, a reset; by
Lemma I.4.12, $q\ge j+1$, a contradiction. The same for (T3), (T5) outputs and kept components at scales in $(q,k]$. A
Pre ancestor at a scale $j\ge q$ would give $q\ge j+1$. So ancestors on $[q,k]$ are Active or Pending and their
transitions are (T1), (T4) and non-ripe $R$. $b(Z)$ is the last scale of a (T2) output or of a kept event in the
history of $Z$, and both are resets, so $b(Z)\le q$.

(b) By (a) and Lemma I.4.10 (a), each ancestor $Y$ at $j\in[q,k]$ is covered by $\nu(Y)$ boxes of side $\le\mathrm{crit}_j$. On $[j,k]$ only
(T1) (which keeps $\nu$) and (T4) (which adds the $\nu_i$) occur, every ancestor at scale $j$ has exactly one successor
in the lineage, and removed components are not in the lineage; so $\sum_{Y\in\mathrm{Anc}_j(Z)}\nu(Y)=\nu(Z)$.

(c) Lemma I.4.10 (a). (d) Backwards along (T1) and (T4), Active/Pending states persist; Pending is created only by
(T4) and Active only by entries, restarts, kept events, activation or (T4); since $Z_0=\varnothing$ each branch ends at an
entry. Entries have point spines and are boxes (Lemma I.4.8).

(e4) Let $Y\in\mathrm{Anc}_q(Z)$. $Y$ is not Pending with core $>q$ (else $q(Z)\ge q(Y)>q$ by monotonicity of cores along (T1),
(T4)), so it is Active. *Case 1: no merge on $Y$'s branch after its last entry*, at scale $e\le q$: at $e$ it is one box of side
$\le\mathrm{crit}_e$; under a pure shadow a box $B$ of side $\le\mathrm{crit}_j$ goes to a set inside the box $N_{s_*r_j}(B^\uparrow)$ of side
$\le\mathrm{crit}_{j+1}$ (as in Lemma I.4.10 (a)), which is small by (H-T) and is hulled; so $Y$ is one box of side $\le\mathrm{crit}_q$.
*Case 2*: let $\xi\le q$ be the scale of the last (T4) merge on $Y$'s branch (after its last entry; post-entry merges are
(T4), since a (T3)/(T5) output is an entry or Pre). Between $\xi$ and $q$ the branch has only (T1) steps. Since $\xi\le q$ and
$\mathcal M(Z)\subset(q,k]$, $\xi\notin\mathcal M(Z)$. Merge records persist under (T1) and are removed only when released at a (T4)
transition (restarts and kept events do not occur on $[\xi,k]$ in the lineage, by (a) and the choice of $\xi$). So $\xi$ was
released at some (T4) transition at a scale $\mu''\in[\xi,k]$ whose new core $q''$ satisfies $q''\notin[\xi,\xi+h_\xi]$ and $\xi\le q''$,
hence $q''>\xi+h_\xi$; cores are nondecreasing along the lineage on $[\mu'',k]$, so $q\ge q''>\xi+h_\xi$. In particular $\xi<q$, and
a (T4) merge at scale $q$ itself is impossible (it would need $q>q+h_q$).
At scale $\xi$ the merged component is one class of the relation $\mathrm d<\omega_\xi$, covered by $\le\nu_{\max}(\xi)$ boxes of side
$\le\mathrm{crit}_\xi$, so its sup-diameter is $e_\xi\le\nu_{\max}(\xi)(\mathrm{crit}_\xi+\omega_\xi)$ (Lemma I.2.12 (c)). A pure shadow step maps
the diameter $e$ to at most $e/L+1+2s_*r_j$ (Lemma I.2.4 (a), the attribution radius, and the fact that a hull does not
increase the diameter). With $n:=q-\xi\ge h_\xi+1$ and $r_j\le r_q$,
$$e_q\le L^{-n}\nu_{\max}(\xi)(\mathrm{crit}_\xi+\omega_\xi)+\frac{2s_*r_q+1}{1-L^{-1}}<1+\frac{2s_*r_q+1}{1-L^{-1}},\tag{B.5}$$
because $L^{h_\xi+1}\ge L^3\cdot2\sqrt d\,\nu_{\max}(\xi)M(\mathrm{crit}_\xi+\omega_\xi)$. The hull side is $\le e_q+1<2+\frac{2s_*r_q+1}{1-L^{-1}}\le\mathrm{crit}_q$: indeed
$(1-L^{-1})(2c_0r_q+8)\ge2(s_*+1)r_q+4\ge2s_*r_q+1$ by $c_0(1-L^{-1})\ge s_*+1$. So $Y$ is small (H-T) with side $\le\mathrm{crit}_q$ and is
one box. Distinct ancestors at scale $q$ are distinct components of $Z_q$, at distance $\ge\omega_q$.

(f4) At entries, restarts and kept events, $q=\mu$ (or $k$) and $t^*=q+n_q(q)$: the spine is a point with $s=q$ and
$n_2\le n_q$, resp. $s+n_2(s)\le k$ for kept components (ripeness). After (T4), (B.4) and Lemma I.4.9 (b). Under (T1) and
activation, $q$ is fixed, $t^*$ does not increase, and $t^*\ge q+n_q(q)$ by definition. So the two-sided bound holds
after every transition, and Lemma I.4.9 (b) gives $k_1(t^*)=q$.

(g) $t^*=k$ gives $s+n_2(s)\le k$, so $s<k$; a non-point spine has $s>k$, hence $\Gamma(Z)$ is a point. An event at a scale
$\mu\in(s,k]$ in the lineage ((T2)–(T5)) would set the clock to $\mu$ (item 5 of Definition I.4.7) or produce a non-point spine whose
later contraction to a point sets $s$ to a later scale; in both cases $s\ge\mu$, a contradiction. So on $(s,k]$ only pure
shadows occur, starting from a point-spine component at scale $s$, which is a box of side $\le\mathrm{crit}_s$ (Lemma I.4.8); as in
(e4) Case 1, it stays one box of side $\le\mathrm{crit}_j$. $\square$

*Status:* Lemmas I.4.10, I.4.12, I.4.13 are proved here, under the abstract hypotheses of LF-2. (a)–(d) follow ARCH's
version 3 and MERGES-astra's per-atom cover; (e4), (f4) and Lemma I.4.10 are REPAIRS §B.2, checked and written out. The
hypotheses (RQ1)–(RQ5) of LF-4 (ARCH §3.8) are (a), (b), (g), the growth bound $\lambda_k\le c_*\lambda_{q+1}+\theta_+$ (from (f4) and (F1)
of Lemma I.5.2), and (e4) with Lemma I.2.13.

---
## I.5 LF-2: the step counter on tori

### I.5.1 Lemma V

**Lemma I.5.1 (Lemma V).** Let $\Gamma$ be a spine at scale $k$ (Definition I.4.5) of length $\ell$, and $\rho\ge1$. Then
$$|N_{\rho+4}(\Gamma)|\le C_V\rho^{d-1}(\ell+\rho),\qquad C_V=2\cdot14^d .$$

*Proof.* *Lift.* If $\operatorname{dist}_\infty(p,\square_x)\le\rho+4$ for $p\in\Gamma$, choose a lift $\tilde p\in\tilde\Gamma$ and the lift $\tilde x$ of $x$ nearest
to $\tilde p$; then $\operatorname{dist}_\infty(\tilde p,\tilde x+[0,1]^d)\le\rho+4$. So $N_{\rho+4}(\Gamma)$ is the image of
$\tilde N:=\{\tilde x\in\mathbb Z^d:\operatorname{dist}_\infty(\tilde\Gamma,\tilde x+[0,1]^d)\le\rho+4\}$ and $|N_{\rho+4}(\Gamma)|\le|\tilde N|$.
*Separated points.* Let $p_1,\dots,p_n\in\tilde\Gamma$ have pairwise sup-distances $>\rho$, $n\ge2$. The closed balls
$\bar B_i:=\{y:|y-p_i|_\infty\le\rho/2\}$ are pairwise disjoint. Fix $i$ and $f(y):=|y-p_i|_\infty$, continuous on the connected set
$\tilde\Gamma$, with $f(p_i)=0$ and $f(p_j)>\rho$; so $f(\tilde\Gamma)\supset[0,\rho/2]$. Every $t\in[0,\rho/2]$ is $f(y)$ for some $y\in\tilde\Gamma\cap\bar B_i$, so
$[0,\rho/2]\subset\bigcup_sf(s\cap\bar B_i)$ over the segments $s$ of $\tilde\Gamma$. Each $s\cap\bar B_i$ is a segment (a convex set meets a
segment in a segment), and $f$ is $1$-Lipschitz for the Euclidean metric, so the length of the interval $f(s\cap\bar B_i)$
is at most $|s\cap\bar B_i|_2$. Hence $\rho/2\le\sum_s|s\cap\bar B_i|_2$. Summing over $i$ and using disjointness,
$n\rho/2\le\sum_s|s|_2=\ell$. So any such family has $n\le2\ell/\rho+1$ (also for $n=1$), and a maximal family exists.
*Count.* For a maximal family every $y\in\tilde\Gamma$ is within $\rho$ of some $p_i$, so every cube of $\tilde N$ is within $2\rho+4$ of some
$p_i$; per coordinate its index lies in an interval of length $4\rho+9$, which contains at most $4\rho+10\le14\rho$ integers.
Thus $|\tilde N|\le(2\ell/\rho+1)(14\rho)^d\le2\cdot14^d\rho^{d-1}(\ell+\rho)$. For a point spine $|\tilde N|\le(2\rho+10)^d\le C_V\rho^d$. $\square$

For a component $Z\subset N_{\rho_j+4}(\Gamma)$ at scale $j$ this gives the cost bound
$$c_v\lambda_j|Z|_\#\le v_j\,\ell(\Gamma)+w_j .\tag{I.5}$$

### I.5.2 The abstract setting, the hypotheses and the growth facts

**Typing data.** The constants of §I.1.2 with $d\ge3$ (LF-V4-AUDIT V4-03: this is what the flow needs; the proof
below uses only $\alpha>0$ and $\theta_->0$, never $d\ge3$ itself, so it applies verbatim for $d\ge2$, but the statement is
made for $d\ge3$). Integers $0\le k_0\le K\le\hat k_f$. Positive integers $n_0,\dots,n_K$ with $n_k=Ln_{k+1}$. A function
$\lambda:\mathbb N\to\mathbb R$.

**Abstract history.** Sets $Z_0=\varnothing$, $Z^{(0)}_{k+1},Z^{\rm pre}_{k+1},Z_{k+1}\subset\mathbb T_{k+1}$ and $\mathcal N_{k+1}\subset\mathbb T_{k+1}$ ($0\le k<K$);
components for the width $\omega_k$; the bookkeeping of Definitions I.4.6–I.4.7 and the transitions (T1)–(T7), with
arbitrary choices (attribution, spanning trees, segment end points, the point replacing a short spine);
for $1\le k\le k_0$ a set $\mathrm{Rem}_k$ of ripe components of $Z^{\rm pre}_k$; reals $G^{\rm pre}_k(Z)$ for the components $Z$ of
$Z^{\rm pre}_k$ and $G_k(Z)$ for those of $Z_k$ ($1\le k\le K$).

**Hypotheses** (premises of this internal lemma only; never frozen; AGENTS.md hard rule 4):
- **(G1) Attribution.** For $0\le k<K$: $Z^\uparrow\subset Z^{(0)}_{k+1}$ for every component $Z$ of $Z_k$; $\mathcal N_{k+1}\subset Z^{(0)}_{k+1}$; the seeds
  (Definition I.3.6) are pairwise disjoint; **every seed lies in a single component of $Z^{(0)}_{k+1}$** (seed containment); and every
  $x\in Z^{(0)}_{k+1}$ lies in the same component of $Z^{(0)}_{k+1}$ as a seed $\sigma$ with $\mathrm d(x,\sigma)\le s_\sigma r_k$ ($s_\sigma=s_*$ for old, $s'$ for
  new seeds); in particular every component of $Z^{(0)}_{k+1}$ contains at least one seed (nonempty seed family).
  *Lean form* (audit P1-07): `LF2Hyp` carries, as data with these properties, the seed map `seedComp : seeds → comps (Z⁽⁰⁾ (k+1))`
  (seed containment), the attribution map `σ : Z⁽⁰⁾ (k+1) → seeds` with `seedComp (σ x) = comp x` and the distance bound, and all
  component-indexed data ($G$, $G^{\rm pre}$, spines, clocks, states) as functions on the `Finset` of components of the relevant set, so
  that no typing obligation is implicit. The flow supplies these by Lemmas I.3.7 and I.3.8.
- **(G2) Hull rule.** $Z^{\rm pre}_{k+1}=\mathrm{Hull}_{\mathrm{crit}_{k+1}}(Z^{(0)}_{k+1})$ if $k+1\le k_0$, and $Z^{\rm pre}_{k+1}=Z^{(0)}_{k+1}$ if $k+1>k_0$.
  $Z_k=Z^{\rm pre}_k\setminus\bigcup\mathrm{Rem}_k$ for $k\le k_0$ and $Z_k=Z^{\rm pre}_k$ for $k>k_0$.
- **(B) Budget recursion.** For $0\le k<K$ and every component $Z'$ of $Z^{\rm pre}_{k+1}$,
  $G^{\rm pre}_{k+1}(Z')\ge\sum_{Z^\uparrow\subset Z'}G_k(Z)+g_k|\mathcal N_{k+1}\cap Z'|_\#-c_v\lambda_{k+1}|Z'|_\#$ (empty sum for $k=0$).
- **(Rg) $R$-rule.** For $1\le k\le k_0$: a kept ripe $Z$ has $G_k(Z)\ge G^{\rm pre}_k(Z)-C_R\lambda_k^{2d+1}+A'_3\lambda_k^{p_R}$; a non-ripe
  component has $G_k=G^{\rm pre}_k$. For $k>k_0$, $G_k=G^{\rm pre}_k$.
- **(K) Constants.** $p_2\ge2d+3$; $p_R>p_2+2d$; $2p_0>p_2$; $c_0(1-L^{-1})\ge s_*+1$; $c_0\ge s'+1$; $C_\nu\ge C_r$; $R_{\rm base}\ge2$; $c_v\ge1$.
- **(H-λ) Horizon.** $\theta_-\le\lambda_{j+1}-\lambda_j\le\theta_+$ for all $j$; $\hat k_f-k_0<\lambda_{k_0}$; $\lambda_{\hat k_f}\le\frac d2\lambda_{k_0}+c_H$.
- **(H-T) Large tori.** $n_k\ge4\nu_{\max}(k)(\mathrm{crit}_k+\omega_k)+4$ for $1\le k\le k_0$.

**Auxiliary functions** ($x\ge1$): $\overline{\mathrm{crit}}(x):=2c_0(R_{\rm base}x^2+1)+10$; $\bar\omega(x):=2R_{\rm base}x^2+L+11$;
$\bar D(x):=\sqrt d(\overline{\mathrm{crit}}(x)+\bar\omega(x))$; $\bar\nu(x):=C_\nu x^{p_2}+1$;
$\bar h(x):=\log_L\big(2\sqrt d\,\bar\nu(x)M(\overline{\mathrm{crit}}(x)+\bar\omega(x))\big)+3$; $\bar n_2(x):=\log_L(LM\,\overline{\mathrm{crit}}(x))+1$;
$\bar A(y):=2A_2p_2\theta_+y^{p_2-1}+C_wy^{2d+1}$; $\Phi(y):=2A_2(c'y)^{p_2}+C_tC_wc'^{2d+1}y^{2d+2}$;
$\bar\Delta(x):=2+\log_L\bar\nu(x)+\log_L(1+\bar D(x))+\bar n_2(2x)$; $\bar G(x):=c_*\big(2+\log_L(\bar\nu(x)\bar D(x))+\log_L(1+\bar D(x))\big)+1$.
Each is nondecreasing; $\bar h,\bar n_2,\bar\Delta,\bar G$ are $O(\log x)$, $\bar\nu,\bar D,\bar A,\Phi$ are polynomial.

**Lemma I.5.2 (growth facts).** Assume (H-λ), (K) and $\lambda_0\ge\max\{1,\theta_+\}$. Then:
- (F1) $\lambda$ is increasing and $\lambda_j\le\lambda_k+(j-k)\theta_+$ ($j\ge k$). The sequences $r,\rho,\mathrm{crit},\omega,D,v,w,\tau,n_q,n_2,\nu_{\max},h$ are
  nondecreasing. $n_q(j)=\lfloor\lambda_j/(\alpha\log L)\rfloor+1$, so $\frac{\lambda_j}{\alpha\log L}<n_q(j)\le\frac{\lambda_j}{\alpha\log L}+1$,
  $n_q(a+x)-n_q(a)\le\frac{\theta_+x}{\alpha\log L}+1$ ($a,x\in\mathbb N$; audit P1-07), and $\lambda_{j+n_q(j)}\le c_*\lambda_j+\theta_+$.
- (F2) $\sigma_k=L^{-1}(v_{k+1}+\sigma_{k+1})$; $v_{k+n}\le2^{d-1}n^{2d-1}v_{k+1}$ ($n\ge1$); $\sigma_k\le C_\sigma v_{k+1}$; $v_{k+1}\le2^{3d}v_k$; hence
  $(v_k+2\sigma_k)D_k\le E_k$.
- (F3) $\tau_t-\tau_{t-1}\le2A_2p_2\theta_+\lambda_t^{p_2-1}$; so $A(t):=\tau_t-\tau_{t-1}+w_t\le\bar A(\lambda_t)$.
- (F4) $n_2(j)\le\bar n_2(\lambda_j)$.
- (F5) $w_j\le C_w\lambda_j^{2d+1}$, $E_j\le C_E\lambda_j^{2d+1}$, $\mathrm{crit}_j\le\overline{\mathrm{crit}}(\lambda_j)$, $\omega_j\le\bar\omega(\lambda_j)$, $D_j\le\bar D(\lambda_j)$,
  $\nu_{\max}(j)\le\bar\nu(\lambda_j)$, $h_j\le\bar h(\lambda_j)$.

*Proof.* (F1) $\theta_->0$. $\min\{n\ge1:n>y\}=\lfloor y\rfloor+1$ for $y\ge0$. $\lambda_{j+n_q(j)}\le\lambda_j+\theta_+(\frac{\lambda_j}{\alpha\log L}+1)$. (F2) The
recursion is the definition. $\lambda_{k+n}\le\lambda_{k+1}+(n-1)\theta_+\le n\lambda_{k+1}$ and
$r_{k+n}\le R_{\rm base}n^2\lambda_{k+1}^2+1\le2n^2r_{k+1}$ give the ratio $n(2n^2)^{d-1}$. $\lambda_{k+1}\le2\lambda_k$ and $r_{k+1}\le4R_{\rm base}\lambda_k^2+1\le5r_k$ give
$v_{k+1}/v_k\le2\cdot5^{d-1}\le2^{3d}$; then $2\sigma_k\le2^{3d+1}C_\sigma v_k$. (F3) Mean value theorem. (F4), (F5)
$\rho_j=c_0\lceil R_{\rm base}\lambda_j^2\rceil\le c_0(R_{\rm base}+1)\lambda_j^2$ and $\omega_j\le2R_{\rm base}\lambda_{j-1}^2+L+11\le(2R_{\rm base}+L+11)\lambda_j^2$; insert. $\square$

**Lemma I.5.3 (ripeness time after a restart; ARCH Lemma T′).** Let $Z'$ be the output at scale $\mu$ of a restart
((T2), (T3) or (T5)), $\Lambda':=\log_L\max\{\ell(\Gamma(Z')),1\}$ and $X:=\max\{\lambda_\mu,\Lambda'\}$. Then
$$\lambda_{t^*(Z')}\le c'X,\qquad t^*(Z')-\mu+1\le C_tX,\qquad\tau_{t^*(Z')}+W_\mu(t^*(Z'))\le\Phi(X),$$
where $W_a(t):=\sum_{j=a}^tw_j$ ($0$ if $t<a$).

*Proof.* The output is $\mathsf{Active}(\mu,1,\varnothing)$ with $s=\mu$, or $\mathsf{Pre}$ with $s=\mu+\max\{1,\lceil\Lambda'\rceil\}$; in both cases
$q=s\le\mu+1+\Lambda'$ and $t^*=s+n_q(s)$. So $\lambda_s\le\lambda_\mu+\theta_+(1+\Lambda')\le(1+2\theta_+)X$ and
$\lambda_{t^*}\le c_*\lambda_s+\theta_+\le c'X$ by (F1). The number of terms is $\le1+\Lambda'+n_q(s)+1\le3+X+\frac{(1+2\theta_+)X}{\alpha\log L}\le C_tX$, and
each $w_j\le C_w(c'X)^{2d+1}$. $\square$

### I.5.3 The statement and the conditions defining $\lambda_*$

**The invariants.** For a component $Z$ at scale $k\le k_0$, with $V_k(Z):=2\sigma_k\ell(\Gamma(Z))+W_{k+1}(t^*(Z))$:
$$\text{(H6′)}\qquad t^*(Z)>k\quad\text{and}\quad G_k(Z)\ge\tau_{t^*(Z)}+V_k(Z)+\nu(Z)+U(Z);$$
(H6′)$^{\rm pre}$ is the same with $t^*(Z)\ge k$ and $G^{\rm pre}_k$. For a component at scale $k_0\le k\le K$:
$$\text{(H6}^\flat)\qquad G_k(Z)\ge A_2\lambda_{k_0}^{p_2}+2\sigma_k\ell(\Gamma(Z))+W_{k+1}(\hat k_f).$$

**The conditions on $\lambda_*$.** $\lambda_*\ge1$ is any number such that the following hold for every real $x\ge\lambda_*$
(each compares a function with a faster-growing one, so such $\lambda_*$ exists; in Lean each is
`∀ᶠ x in atTop` and they are combined):

| | Condition (for all $x\ge\lambda_*$) | Used in |
|---|---|---|
| (Λ0) | $x\ge4c_*\theta_+$; $\ \theta_+(\bar h(x)+2)\le\frac x{4c_*}$; $\ \bar n_2(x)\le\frac x{\alpha\log L}$; $\ 2A_2x^{p_2}\ge C_Ex^{2d+1}+1$; $\ \frac12A_3(x/2)^{2p_0}\ge C_Ex^{2d+1}+1$ | throughout |
| (Λ1) | $\theta_+\big(2+\log_L(\bar\nu(x)\bar D(x))\big)\le x$ and $1+\log_L(\bar\nu(x)\bar D(x))+\bar n_2(2x)\le\frac x{\alpha\log L}$ | Lemma I.4.10 (b) |
| (Λ2) | $\frac12A_3(x/2)^{2p_0}\ge C_Ex^{2d+1}+\Phi(x)+1$ | Case 1a |
| (Λ3) | $\frac12L^x\ge\Phi(x)+1$ | Case 1b |
| (Λ4) | $L^x/(2\bar D(x))\ge\Phi(x)+1$ | Cases 1b, 2c |
| (Λ5) | $\frac12A_2x^{p_2}\ge\bar\Delta(x)\bar A(3c_*x)$ and $\frac12A_2x^{p_2}\ge C_Ex^{2d+1}$ | Case 2a (B.15) |
| (Λ6) | $A_2\big(\frac x{4c_*}\big)^{p_2}\ge\big(c_*(\bar h(x)+1)+1\big)\bar A(3c_*x)$ | Case 2a (B.14) |
| (Λ7) | $2A_2x^{p_2}\ge(\bar G(x)+2c_*)\bar A(c'x)+C_Ex^{2d+1}$ | Case 2b, $\Lambda'\le\lambda$ |
| (Λ8) | $L^{x/2-1}\ge\Phi(x)$ and $L^{x/2}/(2(1+\bar D(x)))\ge\Phi(x)$ | Case 2b, $\Lambda'>\lambda$ |
| (Λ9) | $C_\nu x^{p_2}\ge\Phi(x)$ | Case 2c |
| (Λ10) | $A'_3x^{p_R}\ge C_Rx^{2d+1}+2A_2(c''x)^{p_2}+\big(\frac x{\alpha\log L}+1\big)C_w(c''x)^{2d+1}+1$ | (ii), kept |
| (Λ11) | $c_H\le\frac d2x$; $\ xC_w(dx)^{2d+1}\le A_2x^{p_2}$; $\ A_2x^{p_2}\ge C_E(dx)^{2d+1}$; $\ \frac12A_3x^{2p_0}\ge A_2x^{p_2}+xC_w(dx)^{2d+1}+C_E(dx)^{2d+1}$ | (iv) |

(Λ9) holds for large $x$ because $C_\nu\ge C_r=2A_2c'^{p_2}+1$ and $p_2>2d+2$. (Λ10) uses $p_R>p_2+2d\ge\max\{p_2,2d+2\}+1$;
(Λ11) uses $p_2\ge2d+3$ and $2p_0>p_2$. Since $\lambda$ is increasing, $\lambda_0\ge\lambda_*$ implies $\lambda_j\ge\lambda_*$ for all $j$.

**Abstract and flow conditions (audit P1-08).** (Λ0)–(Λ11) are the conditions of the **abstract** LF-2; they define
$\lambda_*^{\rm LF2}$, the binder of Theorem I.5.4. The **flow instantiation** (§I.5.7) adds, for all real $x\ge\lambda_*^{\rm flow}$:

| | Condition (for all $x\ge\lambda_*^{\rm flow}$) | Used in |
|---|---|---|
| (Λ12) | $x(1-\frac1{2\log L})\ge\frac{d+3}2$ | Lemma I.5.6 (b), (H-λ) |
| (Λ12′) | $\frac23e^{x-2}\ge2L^2$ | Lemma I.5.6 (a): $\beta_{k_0}\ge2L^2$, hence $k_0<k_f$ |
| (Λ13) | $e^{x/2-1}/\sqrt2\ge4\bar\nu(x)(\overline{\mathrm{crit}}(x)+\bar\omega(x))+4$ | Lemma I.5.6 (c), (H-T) |
| (Λ14) | $x\ge3$ | running $\lambda_k\ge\hat\lambda_k-2\ge1$: (I.3), (RH), Lemma I.3.10 (c) |

(Λ12′) is not implied by the others in general (it involves $L^2$ against $e^x$ with no $\lambda$-polynomial on the other side), so it
is listed. Part II adds the analytic conditions (Λ15)–(Λ17) of §II.1.3. The constant of the quantifier prefix is
$\lambda_*:=\max\{\lambda_*^{\rm LF2},\lambda_*^{\rm flow},\lambda_*^{\rm II}\}$, and in Lean the three lists are separate structures
(`LamStarConditions`, `FlowLamConditions`, `AnalyticLamConditions`).

**Theorem I.5.4 (LF-2; ARCH §4.4, §8.1).** Assume the typing data, the abstract history and (G1), (G2), (B), (Rg),
(K), (H-λ), (H-T), and $\lambda_0\ge\lambda_*$. Then:
- (i) if $k_0\ge1$: for $1\le k\le k_0$, every component of $Z^{\rm pre}_k$ satisfies (H6′)$^{\rm pre}$ and every component of $Z_k$
  satisfies (H6′);
- (ii) for $k_0\le k\le K$ (for $1\le k\le K$ if $k_0=0$), every component of $Z_k$ satisfies (H6♭);
- (iii) the shape statements of Lemmas I.4.10 and I.4.13 hold; every ripe component of $Z^{\rm pre}_k$ is Active, has core
  $q=k_1(k)$, and its lineage at scale $q$ is a union of pairwise $\omega_q$-separated boxes of side $\le\mathrm{crit}_q$;
- (iv) consequently $G_k(Z)\ge2A_2\lambda_k^{p_2}$ for $1\le k\le k_0$; $G^{\rm pre}_k(Z)\ge2A_2\lambda_k^{p_2}+1$ for every ripe $Z$; and
  $G_k(Z)\ge A_2\lambda_{k_0}^{p_2}$ for $k_0\le k\le K$.

*What LF-2 replaces in the sources.* P5's hypothesis H6 ($K(Z,\mathbb A_k\cap Z)>0$, P5 (1.32), p. 496 [checked]), P6's counter
$K$ and Prop 3.2 (pp. 20–21 [checked]; cited there to E10 pp. 383–387 [review]), and P6 Thm 4's last inequality (p. 22,
false as printed, ARCH §4.8). E10 (1.84)–(1.88) pays merges by an induction over a spanning tree of the merged
domains with a reserve that does not grow along the flow [review: MERGES-astra §1]; here that induction is replaced by
the additivity of $G$, $\nu$ and the banks, the spine union bound (4.1), the Pending state, and the bounded shifts
(B.11)–(B.12) of the ripeness time. ARCH §4.9–§4.10 explain why P6 Prop 3.2 (ii) and a restart at every merge fail.

*Structure of the proof.* The shape statements (iii) and the facts "$t^*\ge k$ before $R^{(k)}$, $t^*>k$ after" do not
involve budgets: they are Lemmas I.4.10, I.4.13 (whose (c) uses only that after $R^{(k)}$ no component is ripe, which holds
because ripe components are removed or become $\mathsf{Active}(k,1,\varnothing)$ with $t^*=k+n_q(k)>k$). The budget statements are
proved by induction on $k$: §I.5.4 gives the step $k\to k+1$ in the window regime, §I.5.5 the $R$-step and the base, §I.5.6
the transfer and the frozen regime. In the window regime, $t^*(Z')\ge\mu$ for every component $Z'$ of $Z^{\rm pre}_\mu$: under (T1)
by Lemma I.4.10 (c); for restarts, $t^*\ge s+n_q(s)>\mu$; for (T4), $t^*=T\ge s'\ge\mu$.

### I.5.4 Proof of (i): the step $k\to k+1$, $k+1\le k_0$

Write $\mu:=k+1$, $\lambda:=\lambda_\mu$. All parts satisfy (H6′) at scale $k$ (induction).

**Lemma I.5.5 (sufficient inequality).** Let $Z'$ be a component of $Z^{\rm pre}_\mu$ with old parts $Z_1,\dots,Z_m$ (data $t^*_i,\nu_i,U_i$,
$\ell_i:=\ell(\Gamma(Z_i))$) and $r$ new cubes, and $t^{*\prime}:=t^*(Z')\ge\mu$. If
$$\sum_{i=1}^m\big[\tau_{t^*_i}+W_\mu(t^*_i)+\nu_i+U_i\big]+g_kr+\frac{v_\mu}L\sum_i\ell_i\ \ge\ \tau_{t^{*\prime}}+W_\mu(t^{*\prime})+(m+r-1)E_\mu+\nu'+U',\tag{B.7}$$
then $Z'$ satisfies (H6′)$^{\rm pre}$. For $(m,r)=(1,0)$ the term $(m+r-1)E_\mu$ is $0$.

*Proof.* By (B), (3.1) and (I.5), $G^{\rm pre}_\mu(Z')\ge\sum_iG_k(Z_i)+g_kr-v_\mu\ell'-w_\mu$ with $\ell':=\ell(\Gamma(Z'))$. Insert (H6′) for $Z_i$,
$2\sigma_k=\frac2L(v_\mu+\sigma_\mu)$ (F2) and $W_{k+1}=W_\mu$. The target is $\tau_{t^{*\prime}}+2\sigma_\mu\ell'+W_\mu(t^{*\prime})-w_\mu+\nu'+U'$. By (4.1),
$(v_\mu+2\sigma_\mu)\ell'\le(v_\mu+2\sigma_\mu)\sum_i\ell_i/L+(m+r-1)E_\mu$ (F2), and for $(m,r)=(1,0)$, $\ell'\le\ell_1/L$. The difference of the
two sides is at least the difference of the sides of (B.7). $\square$

Every old $t^*_i>k$, so $t^*_i\ge\mu$ and $\tau_{t^*_i}\ge\tau_\mu$. By (Λ0), $\tau_\mu\ge E_\mu+1$ and $g_k\ge E_\mu+1$ (as $\lambda_k\ge\lambda-\theta_+\ge\lambda/2$).

**Pure shadow (T1)**, with or without hull, including Pending activation and Pre entry. By Lemma I.4.10 (c),
$t^{*\prime}\le t^*_1$, $\nu'=\nu_1$, $U'=U_1$, and $W_\mu$ is nondecreasing, so (B.7) holds. This is the exact telescoping that
replaces "$K(Z')\ge K(Z)-1$" (P6 Prop 3.2 (iii)).

**Case 1: new cubes ($r\ge1$, (T2)).** $\nu'=1$, $U'=0$; drop $W_\mu(t^*_i),U_i\ge0$ and use $\nu_i\ge0$. Sufficient:
$$m\tau_\mu+rg_k+\frac{v_\mu}L\sum_i\ell_i\ge\tau_{t^{*\prime}}+W_\mu(t^{*\prime})+(m+r-1)E_\mu+1.\tag{B.8}$$
By Lemma I.5.3 the right side is $\le\Phi(X)+(m+r-1)E_\mu+1$, $X=\max\{\lambda,\Lambda'\}$.
- (1a) $\Lambda'\le\lambda$: $m\tau_\mu\ge mE_\mu$ and $rg_k\ge(r-1)E_\mu+g_k\ge(r-1)E_\mu+\Phi(\lambda)+1$ by (Λ2). This includes $m=0$.
- (1b) $\Lambda'>\lambda$: by (4.1), $L^{\Lambda'}=\ell'\le H+F$ with $H:=\sum_i\ell_i/L$,
  $F:=(m+r-1)D_\mu$. If $H\ge\frac12L^{\Lambda'}$: $m\tau_\mu+rg_k\ge(m+r-1)E_\mu$ as in (1a), and $v_\mu H\ge\frac12L^{\Lambda'}\ge\Phi(\Lambda')+1$ by (Λ3) ($v_\mu\ge1$). If $F\ge\frac12L^{\Lambda'}$: $m+r-1\ge L^{\Lambda'}/(2\bar D(\Lambda'))$,
  and $m\tau_\mu+rg_k\ge(m+r)(E_\mu+1)\ge(m+r-1)E_\mu+(m+r-1)+1$, with $m+r-1\ge\Phi(\Lambda')$ by (Λ4).

**Case 2a: merge within the cap ((T4)).** $\nu'=\sum_i\nu_i$ cancels. Let $i_0$ maximize $t^*_i$, $c:=k_1(t_0)$, and
$$\Delta_1:=(t_0-t^*_{i_0})_+,\qquad\Delta_2:=T-t_0,\qquad X:=\{\xi\in E:\ \xi<q',\ \xi+h_\xi\ge c\}.\tag{B.9}$$
- *Banks.* $U'-\sum_iU_i\le\frac12D\tau_\mu-\frac12\sum_{\xi\in X,\,\xi<\mu}\tau_\xi$ with $D:=[\mu\in\mathcal M']\le[\mu\notin X]$ (B.10). Indeed
  $\sum_iU_i\ge\frac12\sum_{\xi\in\bigcup\mathcal M_i}\tau_\xi$ (duplicates only help), $\mathcal M'\setminus\{\mu\}\subset\bigcup_i\mathcal M_i$, and the elements of $X$ other than $\mu$ are
  old records released at this transition ($\xi<q'$). If $\mu\in X$ then $\mu<q'$, so $\mu\notin\mathcal M'$. No bank is spent twice: a
  record leaves $\mathcal M$ only at the transition that releases it, and cores never decrease (B.4).
- *Smallness shift.* $\tilde q+n_q(\tilde q)\le t^*_i\le t^*_{i_0}$ for a part with $q_i=\tilde q$, so $\Delta_1\le(s'+n_2(s')-t^*_{i_0})_+$. With
  $\Lambda_*:=\log_L\max\{\max_i\ell_i,1\}$: the part with the longest spine has $t^*\ge s\ge k+\Lambda_*$ (projected epoch; trivial if
  all spines are points, as $t^*\ge\mu$), and $\Lambda'\le\Lambda_*+\log_L(m(1+D_\mu))$ by (4.1), while $s'\le\mu+1+\Lambda'$. By the cap and
  Lemma I.4.10 (a), $m\le\nu'\le\nu_{\max}(\mu)\le\bar\nu(\lambda)$ and $\Lambda'\le\log_L(\bar\nu(\lambda)\bar D(\lambda))$, so $\lambda_{s'}\le2\lambda$ by (Λ1). Hence
  $$\Delta_1\le\bar\Delta(\lambda)=2+\log_L\bar\nu(\lambda)+\log_L(1+\bar D(\lambda))+\bar n_2(2\lambda).\tag{B.11}$$
- *Strip shift.* The integers of $[c,q'-1]$ are all in $B(E)$; each lies in $[\xi,\xi+h_\xi]$ for some $\xi\in X$. So
  $q'-c\le\sum_{\xi\in X}(h_\xi+1)$. If $X=\varnothing$, $q'=c=k_1(t_0)$ and $T=t_0$. Otherwise $T>t_0$, so $T=q'+n_q(q')$ (proof of (B.4)), and
  $t_0\ge c+n_q(c)$; by (F1),
  $$\Delta_2\le c_*\sum_{\xi\in X}(h_\xi+1)+1\le\sum_{\xi\in X}\{c_*(h_\mu+1)+1\}.\tag{B.12}$$
- *Scales.* Let $i$ be a part with $q_i=\tilde q$. If it is Active, Lemma I.4.13 (f4) and $t^*_i\ge\mu$ give $\mu\le\tilde q+n_q(\tilde q+1)$, hence
  $\lambda\le c_*\lambda_{\tilde q+1}\le c_*(\lambda_{\tilde q}+\theta_+)$; if it is Pending, $\tilde q\ge\mu$. Either way $\lambda_{\tilde q}\ge\lambda/(2c_*)$ by (Λ0). Every
  $\xi\in X\cup\{\mu\}$ has $\xi\ge\tilde q-h_\mu$ (for $\xi\in X$: $\xi+h_\xi\ge c\ge\tilde q$, $h_\xi\le h_\mu$; for $\mu$: (B.4)), so
  $\lambda_\xi\ge\lambda_{\tilde q}-\theta_+\bar h(\lambda)\ge\lambda/(4c_*)$ (Λ0). And $T<(q'+1)+n_q(q'+1)$ with $q'+1\le\mu+h_\mu+2$, so
  $\lambda_{q'+1}\le\lambda+\theta_+(\bar h(\lambda)+2)\le2\lambda$ and $\lambda_T\le c_*\lambda_{q'+1}+\theta_+\le3c_*\lambda$. Together with (Λ6):
  $$\xi\in X\cup\{\mu\}\ \Longrightarrow\ \tfrac12\tau_\xi\ge A_2\big(\tfrac\lambda{4c_*}\big)^{p_2}\ge\{c_*(h_\mu+1)+1\}\bar A(\lambda_T).\tag{B.14}$$
- *Payment.* Keep the $i_0$ terms; the other parts give $\sum_{i\ne i_0}\tau_{t^*_i}\ge(m-1)\tau_\mu$. Since $T\le t^*_{i_0}+\Delta_1+\Delta_2$ and each
  additional scale up to $T$ costs at most $\bar A(\lambda_T)$ (F3), $\tau_T+W_\mu(T)-\tau_{t^*_{i_0}}-W_\mu(t^*_{i_0})\le(\Delta_1+\Delta_2)\bar A(\lambda_T)$. By (B.12) and
  (B.14), $\Delta_2\bar A(\lambda_T)\le\frac12\sum_{\xi\in X}\tau_\xi$. With (B.10), it suffices that
  $(m-1)\tau_\mu\ge\Delta_1\bar A(\lambda_T)+(m-1)E_\mu+\frac12(D+[\mu\in X])\tau_\mu$; as $D+[\mu\in X]\le1$ and $m\ge2$, it suffices that
  $$\tfrac12(m-1)\tau_\mu\ge\bar\Delta(\lambda)\bar A(3c_*\lambda)+(m-1)E_\mu,\tag{B.15}$$
  which is (Λ5). This covers repeated pending pushes and chains of nested strips.

**Case 2b: merge with a Pre part ((T3)).** Restart: $\nu'=1\le m\le\sum_i\nu_i$, $U'=0$, banks dropped.
- *$\Lambda'\le\lambda$.* Keep the $i_0$ terms; it suffices that $(m-1)\tau_\mu\ge\Delta\bar A(c'\lambda)+(m-1)E_\mu$ with $\Delta:=(t^{*\prime}-t^*_{i_0})_+$,
  since $\lambda_{t^{*\prime}}\le c'\lambda$ (Lemma I.5.3). Bound $\Delta$: $t^{*\prime}=s'+n_q(s')$ with $s'\le\mu+\max\{1,\lceil\Lambda'\rceil\}$. If the part $i_1$ with the
  longest spine is Pre, $t^*_{i_0}\ge s_{i_1}+n_q(s_{i_1})$ with $s_{i_1}\ge k+\lceil\Lambda_*\rceil$, and (F1) gives
  $\Delta\le c_*(2+\Lambda'-\Lambda_*)+1\le c_*(2+\log_L(m(1+D_\mu)))+1$. If $i_1$ is Active or Pending, $\Lambda_*\le\log_L(\bar\nu(\lambda)\bar D(\lambda))$
  (Lemma I.4.10 (a)) and $t^*_{i_0}\ge t^*_p\ge\mu+n_q(\mu)$ for a Pre part $p$, so $\Delta\le c_*(\Lambda'+1)+1$ with
  $\Lambda'\le\Lambda_*+\log_L(m(1+D_\mu))$. In both cases, with $\log_Lm\le2(m-1)$, $\Delta\le\bar G(\lambda)+2c_*(m-1)\le(m-1)(\bar G(\lambda)+2c_*)$. (Λ7)
  concludes.
- *$\Lambda'>\lambda$.* Pay directly: the left side of (B.7) is $\ge m\tau_\mu+v_\mu\ell_{\max}/L+m$ and the right side $\le\Phi(\Lambda')+(m-1)E_\mu+1$
  (Lemma I.5.3). Since $\Lambda'\le\Lambda_*+\log_L(m(1+D_\mu))$, either $\Lambda_*\ge\Lambda'/2$, so $v_\mu\ell_{\max}/L\ge L^{\Lambda'/2-1}\ge\Phi(\Lambda')$ (Λ8); or
  $m(1+D_\mu)\ge L^{\Lambda'/2}$, so $m-1\ge m/2\ge L^{\Lambda'/2}/(2(1+\bar D(\Lambda')))\ge\Phi(\Lambda')$ (Λ8), and $(m-1)\tau_\mu\ge(m-1)E_\mu+(m-1)$. In both
  cases $m\tau_\mu\ge(m-1)E_\mu$ covers the rest.

**Case 2c: overflow ((T5)).** Restart: $\nu'=1$, $U'=0$. $\ell_i\le(\nu_i-1)D_k$ (Lemma I.4.10 (a)), so by (4.1)
$\ell'\le2D_\mu\sum_i\nu_i$. Drop the $i_0$ terms and the banks, pay $(m-1)E_\mu$ with $(m-1)\tau_\mu$. It suffices that
$$\sum_i\nu_i\ge\tau_{t^{*\prime}}+W_\mu(t^{*\prime})+1 .\tag{B.18}$$
If $\Lambda'\le\lambda$: the right side is $\le\Phi(\lambda)+1\le C_\nu\lambda^{p_2}+1\le\nu_{\max}(\mu)+1\le\sum_i\nu_i$ by (Λ9). If $\Lambda'>\lambda$:
$\sum_i\nu_i\ge L^{\Lambda'}/(2D_\mu)\ge L^{\Lambda'}/(2\bar D(\Lambda'))\ge\Phi(\Lambda')+1$ by (Λ4).

The cases are exhaustive (§I.4.4). This proves (H6′)$^{\rm pre}$ at $\mu$. $\square$

### I.5.5 The $R$-step and the base

**(ii) of the window regime: after $R^{(k)}$.** Non-ripe components are unchanged, with $G_k=G^{\rm pre}_k$ (Rg), and have
$t^*>k$ (Active with $t^*\ne k$, Pending with $t^*>q>k$, Pre with $t^*>s>k$). A removed component has no obligation.
A kept component $Z$ (ripe: Active, $t^*=k$, point spine and one box by Lemma I.4.13 (g)) has
$G^{\rm pre}_k(Z)\ge\tau_k+\nu+U\ge0$ and new data $\mathsf{Active}(k,1,\varnothing)$, $t^{*\prime}=k+n_q(k)$, $\ell=0$, $U'=0$, $\nu'=1$. Since
$\lambda_{k+n_q(k)}\le c''\lambda_k$ and $n_q(k)\le\frac{\lambda_k}{\alpha\log L}+1$ (F1), (Rg) and (Λ10) give
$G_k(Z)\ge A'_3\lambda_k^{p_R}-C_R\lambda_k^{2d+1}\ge\tau_{k+n_q(k)}+W_{k+1}(k+n_q(k))+1$. After $R^{(k)}$ no component is ripe.

**Base ($k_0\ge1$).** Every component of $Z^{\rm pre}_1$ is a (T2) output with $m=0$; (B) at $k=0$ and Case 1 with $m=0$ give
(H6′)$^{\rm pre}$ at $1$. No component of $Z^{\rm pre}_1$ is ripe ($t^*\ge1+n_q(1)>1$), so $Z_1=Z^{\rm pre}_1$ satisfies (H6′). $\square$

### I.5.6 Proof of (ii): transfer at $k_0$ and the frozen regime

*Horizon sum.* By (H-λ), $\hat k_f-k_0<\lambda_{k_0}$ and $\lambda_j\le\lambda_{\hat k_f}\le\frac d2\lambda_{k_0}+c_H\le d\lambda_{k_0}$ for $j\le\hat k_f$ ((Λ11)); so
$$W_{k_0+1}(\hat k_f)\le\lambda_{k_0}C_w(d\lambda_{k_0})^{2d+1}\le A_2\lambda_{k_0}^{p_2}\qquad\text{(B.20), by (Λ11).}$$

*Transfer ($k_0\ge1$).* For a component $Z$ of $Z_{k_0}$, (H6′) gives $t^*\ge k_0+1$ and
$G\ge\tau_{t^*}+2\sigma_{k_0}\ell+W_{k_0+1}(t^*)$ (drop $\nu+U\ge0$). If $t^*\ge\hat k_f$, $W_{k_0+1}(t^*)\ge W_{k_0+1}(\hat k_f)$ and $\tau_{t^*}\ge A_2\lambda_{k_0}^{p_2}$.
Otherwise $\tau_{t^*}\ge\tau_{k_0+1}\ge2A_2\lambda_{k_0}^{p_2}\ge A_2\lambda_{k_0}^{p_2}+W_{k_0+1}(\hat k_f)$ by (B.20). Either way (H6♭) holds at $k_0$; this
includes Pending components (their $t^*>k_0$). The window data are then discarded (T7).

*Frozen steps* ($k_0\le k<K$; no $R$, no hull, no window state; $\mu:=k+1\le\hat k_f$). The computation of Lemma I.5.5 with
$\tau_{t^*}$ replaced by the constant $A_2\lambda_{k_0}^{p_2}$, $t^*$ by $\hat k_f$, and no $\nu$, $U$, gives the sufficient inequality
$$(m-1)A_2\lambda_{k_0}^{p_2}+(m-1)W_\mu(\hat k_f)+g_kr+\frac{v_\mu}L\sum_i\ell_i\ \ge\ (m+r-1)E_\mu\tag{I.6}$$
(for a pure shadow both sides vanish). For $m\ge1$: $A_2\lambda_{k_0}^{p_2}\ge C_E(d\lambda_{k_0})^{2d+1}\ge E_\mu$ and $g_k\ge\frac12A_3\lambda_{k_0}^{2p_0}\ge E_\mu$ by
(Λ11), since $\lambda_\mu\le d\lambda_{k_0}$ and $\lambda_k\ge\lambda_{k_0}$. For $m=0$ ($r\ge1$; this includes the base step when $k_0=0$):
$g_kr\ge g_k+(r-1)E_\mu$ and $g_k\ge A_2\lambda_{k_0}^{p_2}+W_\mu(\hat k_f)+E_\mu$ by (Λ11). Components may wind on small tori; Lemma V
and (4.1) hold on tori, and no hull is taken. $\square$

*Consequences (iv).* For $1\le k\le k_0$: $G_k\ge\tau_{t^*}\ge\tau_{k+1}\ge2A_2\lambda_k^{p_2}$. For ripe $Z$: $G^{\rm pre}_k\ge\tau_k+\nu\ge2A_2\lambda_k^{p_2}+1$.
For $k_0\le k\le K$: $G_k\ge A_2\lambda_{k_0}^{p_2}$. $\square$

In the flow, (iv) gives P5 (1.30) with $\ell=2$ for $k\le k_0$ ($2A_2\hat\lambda_k^{p_2}\ge2p_2(\beta_k)$, since $\hat\lambda_k\ge\lambda_k\ge\log\beta_k$ and
$p_2(\beta)=A_2(\log\beta)^{p_2}$, P5 p. 495 [checked]); the input $G\ge2p_2(\beta_k)+\nu$ of LF-4 at ripeness; and P5 (1.31) with $\ell=1$ and
the frozen threshold $p_2(\beta_{k_0})$ for $k_0\le k\le k_f$ (the repaired P6 Thm 4; ARCH §4.8).

### I.5.7 Instantiation: the flow satisfies the hypotheses of LF-2

**Lemma I.5.6 (horizon and tori).** Assume (I.2) with $\epsilon\le\frac1{20}$, $a\in(1,\frac32)$, $L\ge2$, $k_f\ge1$, and let $k_0$ be the flow's
$k_0$ (read as $0$ if $\beta\nu>1$). Then:
(a) $k_f\le\hat k_f\le k_f+1$, and $k_0<k_f$ if $\beta_{k_0}\ge2L^2$;
(b) $\hat k_f-k_0<\frac{d+3}2+\frac{\hat\lambda_{k_0}}{2\log L}$; hence (H-λ) holds for $\lambda=\hat\lambda$ with $\theta_\pm=\theta$ and $c_H=\frac{(d+3)(d-2)}2\log L$,
provided $\hat\lambda_{k_0}(1-\frac1{2\log L})\ge\frac{d+3}2$;
(c) if $k_0$ is *genuine* ($\beta_{k_0}\nu_{k_0}\le1$), then for $k\le k_0$ and every admissible torus, $n_k\ge L^{k_f+1-k_0}\ge e^{\hat\lambda_{k_0}/2-1}/\sqrt2$
(ARCH (3.0)), and (H-T) holds if $e^{x/2-1}/\sqrt2\ge4\bar\nu(x)(\overline{\mathrm{crit}}(x)+\bar\omega(x))+4$ for $x=\hat\lambda_{k_0}$ (condition (Λ13));
if $k_0=0$ (genuine, or by the convention for $\beta\nu>1$), (H-T), which is indexed by $1\le k\le k_0$, is vacuous.
(Audit P1-05: version 1 stated (c) for every $k_0$; for the conventional $k_0=0$ the bound $n_0\ge e^{\hat\lambda_0/2-1}/\sqrt2$ is false,
e.g. $d=L=3$, $\nu=1/81$, $\beta=10^8$, $n_0=9$; it is not needed there.)
The case $k_f=0$ ($\nu>\frac78L^{-2}$) is outside this lemma and outside LF-2: there is no RG step, and the last step is taken
on $\rho_0$ directly (ARCH LF-8 (b)).

*Proof.* (a) At $\hat k_f$: $\nu_{\hat k_f}=\nu L^{2\hat k_f}\delta_{\hat k_f}\ge L^{-2}e^{-\epsilon}>\frac78L^{-2}$, so $k_f\le\hat k_f$. At $k_f$: $\nu L^{2k_f}>\frac78L^{-2}e^{-\epsilon}$, so
$\nu L^{2(k_f+1)+2}>\frac78e^{-\epsilon}L^2\ge1$, so $\hat k_f\le k_f+1$. $\nu_k$ is increasing ($\nu_{k+1}/\nu_k=L^2\delta_{k+1}/\delta_k\ge L^2e^{-2\epsilon}>1$); if
$\beta_{k_0}\ge2L^2$ then $\nu_{k_0}\le\beta_{k_0}^{-1}<\frac78L^{-2}$, so $k_0<k_f$.
(b) If $k_0$ is the last $k$ with $\beta_k\nu_k\le1$: $\beta_{k+1}\nu_{k+1}=\beta_k\nu_kL^d\frac{\gamma_{k+1}\delta_{k+1}}{\gamma_k\delta_k}\le\beta_k\nu_kL^de^{4\epsilon}$, so
$\nu_{k_0}>L^{-d}e^{-4\epsilon}\beta_{k_0}^{-1}$; and $\nu_{k_f-1}\le\frac78L^{-2}$. Then
$L^{2(k_f-1-k_0)}\le e^{2\epsilon}\nu_{k_f-1}/\nu_{k_0}<\frac78e^{6\epsilon}L^{d-2}\beta_{k_0}\le2L^{d-2}\beta_{k_0}$, so
$k_f-k_0<\frac d2+\frac{\log2+\log\beta_{k_0}}{2\log L}\le\frac{d+1}2+\frac{\hat\lambda_{k_0}}{2\log L}$ (as $\log\beta_{k_0}<\lambda_{k_0}\le\hat\lambda_{k_0}$), and $\hat k_f\le k_f+1$.
Then $\hat\lambda_{\hat k_f}=\hat\lambda_{k_0}+(\hat k_f-k_0)\theta<\hat\lambda_{k_0}(1+\frac{d-2}2)+\frac{d+3}2\theta=\frac d2\hat\lambda_{k_0}+c_H$. If $\beta\nu>1$ ($k_0:=0$):
$\hat k_f=0$ or $\nu L^{2\hat k_f}<1$, so $L^{2\hat k_f}<\beta$ and $\hat k_f<\frac{\hat\lambda_0}{2\log L}$; the same conclusions follow.
(c) $ML^{k_f+1}\mid\ell$, so $L^{k_f+1-k}\mid n_k$. From $\nu_{k_f}>\frac78L^{-2}$, $\nu_{k_0}\le\beta_{k_0}^{-1}$ (this is where genuineness is used) and $\delta_{k_f}/\delta_{k_0}\le e^{2\epsilon}$:
$L^{2(k_f+1-k_0)}\ge\frac78e^{-2\epsilon}\beta_{k_0}\ge\frac34\beta_{k_0}$, and $\beta_{k_0}=e^{\lambda_{k_0}}/a\ge\frac23e^{\hat\lambda_{k_0}-2}$. For $k\le k_0$, $\nu_{\max}(k)$, $\mathrm{crit}_k$,
$\omega_k$ are at most their values at $\hat\lambda_{k_0}$ (F5). $\square$

**The instantiation** (ARCH §8.1 "Instantiation plan"), for $k_f\ge1$, with $K:=k_f$:
- $\lambda:=\hat\lambda$, $\theta_\pm:=\theta$; the tori $n_k=\ell/(ML^k)$; (H-λ), (H-T) by Lemma I.5.6 under the flow conditions (Λ12),
  (Λ12′), (Λ13) of §I.5.3 ($\lambda_*\ge\lambda_*^{\rm flow}$); $k_0<k_f$ by Lemma I.5.6 (a) and (Λ12′);
- the region history of the flow (§I.3, §I.4) with its bookkeeping; (RH) holds by (Λ14) and (I.3); (G1) is Lemmas I.3.7–I.3.8
  ($R_{\rm base}\ge4L+20$, $s_*=4$, $s'=5$), with seed containment by Lemma I.3.7 (a); (G2) is (R8)–(R9) of Definition I.3.1 (the hull
  closure, remark after Lemma I.3.4);
- (B) is Lemma B (Part II, Lemma II.5.12; P6 (3.9)–(3.11) [checked]), converted to $\hat\lambda$ by (I.3); with the base
  gain of LF-6 (ii) at $k=0$ (Part II §II.7, not yet written);
- (Rg) is LF-4R (Part III);
- (K) holds by §I.1.3 rows 4 and 8.

---
## I.6 Lean declarations asked for by Part I

Namespace `Balaban.LargeField`; all files are Lean modules (AGENTS.md rule 1). Order = dependency order. Sizes are
estimates of Lean lines including docstrings. "Model-free" files import only `Mathlib`, `Balaban.Frozen.Model.Torus`
and `Balaban.Lattice.Blocks`; the abstract LF-2 (block D) does not import the region calculus (block B), which is
needed only for the instantiation (block E).

| # | Declaration(s) | Kind | Content | Est. lines |
|---|---|---|---|---|
| **A** | **Geometry** (`LargeField/Geometry/*`) | | | **≈2 600** |
| A1 | `cycNorm`, `supDist`, `setDist`, `nbhd` ($X^{\sim m}$), `thick` ($X^{\approx}$) | def | Def. I.2.0 | 60 |
| A2 | `supDist_triangle`, `exists_geodesic`, `nbhd_nbhd`, `setDist_nbhd_ge` | thm | Lemma I.2.1 | 150 |
| A3 | `cubeDist_gt_iff` | thm | Lemma I.2.2 (documentation of the translation) | 40 |
| A4 | `coarsen` (= `blockMap L`), `supDist_coarsen_le`, `supDist_le_coarsen`, `nbhd_coarsen_subset` | def/thm | Def. I.2.3, Lemma I.2.4 | 150 |
| A5 | `lblock`, `opening`, `openingIn`, `opening_compl_subset`, `openingIn_diff_subset`, monotonicity | def/thm | Def. I.2.5, Lemma I.2.6 | 160 |
| A6 | continuous torus cubes: `cubeCentre`, `boxCentre`, `NR` ($N_r$ of a set of points), Lemma I.2.8 (a)–(d) | def/thm | Def. I.2.7, Lemma I.2.8 | 250 |
| A7 | `IsSmall`, `hull`, `side`, `IsBox`; `hull_unique`, `subset_hull`, `hull_hull`, `side_le_diam_succ`, `small_of_subset_NR`, `lift_small` | def/thm | Def. I.2.9, Lemma I.2.10 | 400 |
| A8 | `Linked ω X`, `comps ω X : Finset (Finset _)`; `comps_sep`, `comp_of_linked`, `comp_diam_le` | def/thm | Def. I.2.11, Lemma I.2.12 | 300 |
| A9 | `nbhd_disjoint_of_comps`, `local_eq_global` | thm | Lemmas I.2.13, I.2.14 | 200 |
| A10 | `DmodOmega`, `treeLengthMod` | def | Def. I.2.15 (consumers in Part II) | 120 |
| A11 | `exteriorBoundary`, `exteriorBoundary_starConnected` (Timár 2013 Lemma 2) | def/thm | cited input of Lemma S; to be formalized | 800 |
| A12 | `encloses`, `lemmaS`, `lemmaS_diam`, `boxes_enclose_nothing`, `lemmaS_torus` | def/thm | Lemma I.3.13 | 350 |
| A13 | `lemmaP` | thm | Lemma I.3.14 (not used under the present $\omega$; low priority) | 300 |
| **B** | **Region calculus** (`LargeField/Region/*`) | | | **≈2 300** |
| B1 | `RegionStep` (data: $Z_k$, radii, $\mathsf P,\mathsf Q,\mathsf R,\mathsf S$ with constraints); `U`, `Uprime`, `OmegaPrime`, `Omega`, `OmegaDD`, `FZ`, `Z0`, `newCubes` | def | Def. I.3.1 | 250 |
| B2 | `hullRound`, `hullClosure`, `hulledIn`; `hullClosure_fixed`, `hullClosure_box`, `hullClosure_comps` | def/thm | Defs. I.3.2–I.3.3, Lemma I.3.4 | 350 |
| B3 | `inclusions` (a)–(i) | thm | Lemma I.3.5 | 350 |
| B4 | `seeds`, `seeds_subset`, `seeds_disjoint`, `seed_in_comp` | def/thm | Def. I.3.6, Lemma I.3.7 | 150 |
| B5 | `attribution` (G1) | thm | Lemma I.3.8 | 300 |
| B6 | `locality` | thm | Lemma I.3.9 | 500 |
| B7 | `flowGeneratingSet` (to `Multiscale.GeneratingSet`), `removeOverwrite`, `overwrite_generatingSet` | def/thm | Lemma I.3.10, Def. I.3.11, Lemma I.3.12 | 350 |
| B8 | `thick_lineage_subset`, `coreReduction` | thm | Lemmas I.3.15, I.3.16 | 150 |
| **C** | **Histories and bookkeeping** (`LargeField/History/*`) | | | **≈3 200** |
| C1 | `RegionHistory` (structure, field per scale) and `RegionHistory.Admissible`; `succ`, `anc`, `lineage`; `lineage_eq_inter`, `regions_grow` | def/thm | Defs. I.4.1–I.4.2, Lemma I.4.3 | 450 |
| C2 | `localHistory`, `historiesWithFinal` ($\mathfrak H_k(Z)$) | def | Def. I.4.4 | 150 |
| C3 | `Spine` (lifted segments + connectedness), `Spine.length`, `Spine.contract`, `Spine.join`, `Spine.NR` | def/thm | Def. I.4.5 | 400 |
| C4 | `WState`, `Book`, `tStar`, `bank`, `WState.Admissible` (B.1), `IsRipe` | def | Def. I.4.6 | 150 |
| C5 | `stepSpine` (rounds), `stepClocks`, `stepState` ((T1)–(T5)), `rStep` ((T6)), `base` | def | Def. I.4.7, §I.4.4 | 550 |
| C6 | `spine_consistency` ((3.1), (4.1), point spines are boxes) | thm | Lemma I.4.8 | 400 |
| C7 | `k1` (`Nat.findGreatest`), `blocked`; `k1_mono`, `k1_succ_le`, `k1_eq_iff`, `k1_surj` | def/thm | Lemma I.4.9 | 150 |
| C8 | `lemmaC4` (a)–(c) | thm | Lemma I.4.10 | 500 |
| C9 | `HasReset`, `floor`; `lemmaC` (a)–(g) | def/thm | Def. I.4.11, Lemmas I.4.12–I.4.13 | 600 |
| **D** | **Abstract LF-2** (`LargeField/Counter/*`) | | | **≈2 700** |
| D1 | `lemmaV` | thm | Lemma I.5.1 | 350 |
| D2 | the constants of §I.1.2 as functions of the typing data and $\lambda$ (`r`, `ρ`, `crit`, `ω`, `D`, `nq`, `n2`, `νmax`, `h`, `g`, `v`, `w`, `σ` (as `tsum`), `τ`, `E`, …) and the auxiliary functions of §I.5.2 | def | §I.1.2, §I.5.2 | 200 |
| D3 | `growth` (F1)–(F5), `restart_tStar` | thm | Lemmas I.5.2–I.5.3 | 400 |
| D4 | `LamStarConditions` ((Λ0)–(Λ11)), `FlowLamConditions` ((Λ12), (Λ12′), (Λ13), (Λ14)), `exists_lamStar` | def/thm | §I.5.3 | 300 |
| D5 | `LF2Hyp` (structure: (G1) with the seed map and attribution map as data, (G2), (B), (Rg), (K), (H-λ), (H-T) for an abstract history; component data indexed by the `Finset` of components) | def | §I.5.2 | 200 |
| D6 | `sufficient_B7`, `pureShadow`, `case1`, `case2a`, `case2b`, `case2c` | thm | Lemma I.5.5, §I.5.4 | 900 |
| D7 | `rStep_budget`, `base_budget` | thm | §I.5.5 | 150 |
| D8 | `transfer`, `frozenStep` | thm | §I.5.6 | 250 |
| D9 | `LF2` | thm | Theorem I.5.4 (internal; never frozen) | 100 |
| **E** | **Instantiation** (`LargeField/Counter/Instantiation.lean`) | | | **≈350** |
| E1 | `kfhat`, `kfhat_bounds`, `hLambda_of_flow`, `hT_of_flow` | def/thm | Lemma I.5.6 (uses `Flow/RunningCoefficients.lean`) | 250 |
| E2 | `flowHistory_LF2Hyp_geom` ((G1), (G2), (H-λ), (H-T), (K) for the flow's region history; (B), (Rg) remain as hypotheses until Parts II–III) | thm | §I.5.7 | 100 |
| | **Total** | | | **≈11 000** |

No file need exceed 1 000 lines. Blocks A, C, D can be drafted now (after ruling 1 of ARCH §7); block B after
this Part is reviewed; block E needs only landed flow lemmas. A11 (Timár) is the one external input; it is used
only by Lemma S, whose consumers are in Part III.

---

## I.7 Status, changes, open items

### I.7.1 Status of the statements of Part I

| Statement | Status |
|---|---|
| Defs. I.2.0, I.2.3, I.2.5, I.2.7, I.2.9, I.2.11, I.2.15; Defs. I.3.1–I.3.3, I.3.6, I.3.11; Defs. I.4.1, I.4.2, I.4.4–I.4.7, I.4.11; (T1)–(T7) | definitions (sources [checked] as marked) |
| Lemmas I.2.1, I.2.2, I.2.4, I.2.6, I.2.8, I.2.10, I.2.12, I.2.13, I.2.14 | proved here |
| Lemma I.3.4 (hull closure), I.3.5 (inclusions), I.3.7 (seeds), I.3.8 (attribution, (G1)), I.3.9 (locality) | proved here |
| Lemma I.3.10, I.3.12 (generating set and overwrite) | proved here |
| Lemma I.3.13 (Lemma S) | proved here from a cited external lemma (Timár 2013, Lemma 2) |
| Lemma I.3.14 (Lemma P) | proved here (site form) |
| Lemma I.3.15 | proved here; Lemma I.3.16 proved here for set functions of range $\varpi$; the value of $\varpi$ for P3's $\mathbb B_k(X)$ is UNCERTAIN (Part II) |
| Lemmas I.4.3, I.4.8, I.4.9, I.4.10 (C4), I.4.12, I.4.13 (C) | proved here |
| Lemma I.5.1 (V), I.5.2, I.5.3, I.5.5; Theorem I.5.4 (LF-2) | proved here, under the abstract hypotheses |
| Lemma I.5.6 (instantiation of (H-λ), (H-T)) | proved here from (I.2) (P4 (H.6) [review]; Lean `betaSeq_eq`, `nuSeq_eq`, `norm_gammaSeq_le`) |
| (B) for the flow (Lemma B) | cited to P6 (3.9)–(3.11) [checked in ARCH]; proof in Part II |
| (Rg) for the flow (LF-4R) | Part III |

### I.7.2 Changes relative to ARCH v4

The list of §I.0 (items 1–15). In short: $\omega_k$ gains $+L$; (G1) is restated as attribution within components
with explicit $s_*=4$, $s'=5$ and $R_{\rm base}\ge4L+20$; the hull trigger is "hull side $\le\mathrm{crit}$"; spines are lifted and
Lemma V avoids Hausdorff measure; short spines are replaced by a point only under pure shadows, with the projected
epoch $k+\max\{1,\lceil\log_L\max(\ell,1)\rceil\}$; the event bound (4.1) and the cover of Lemma C4 are proved through the hull
rounds; Lemma C (a) has a floor invariant; $c'=c_*(1+3\theta_+)$, $c_H=\frac{(d+3)(d-2)}2\log L$; $\lambda_*$ is an explicit
list (Λ0)–(Λ13); Case 2b's large-$\Lambda'$ branch is direct; (H-λ) is derived from (I.2) only; LF-2 has a final scale
$K\le\hat k_f$, is stated for $d\ge3$, and covers $k_0=0$; locality (Lemma I.3.9) is new; the minimal generating sets
move to Part II; the constant order follows LOCALIZATION-review L-04; Lemma L (c) is restricted to the ripe lineage
(V4-01). P5 (2.46)'s radius $\frac{L-1}2$ is replaced by $L-1$ (remark after Definition I.3.1). Version 1.1 (§I.0 item 16) fixes
$M/M_1=L^{m_0}$ in the prefix, adds the radius hypotheses (RH) and $R_j\ge R_{\rm base}$, restricts Lemma I.5.6 (c) to a genuine
$k_0$, labels the hull closure as an extension of P6 p. 22, renames the coefficient $R_{\rm base}$, and splits the $\lambda_*$ list.

### I.7.3 Open items

(Status after Part II: see §II.O.4, which supersedes O-2, O-4, O-6, O-7 and O-8 below.)

- **O-1 (Timár's lemma, Lean).** Lemma S rests on the $*$-connectedness of exterior boundaries (Timár 2013, Lemma 2;
  Deuschel–Pisztora 1996). It is external and not in Mathlib; formalizing it is item A11 (≈800 lines). Its only
  consumers are Lemma CH and the exposure argument of Part III.
- **O-2 (Lemma F, analytic; V4-02).** Part I proves the geometric premises (Lemmas I.2.13, I.2.14, I.3.15). The exact
  support of the recursively defined and kept operators, and the locality of the backgrounds in P5 (2.47) and P6
  (3.2), remain Part II obligations (ARCH question 5 to Roland).
- **O-3 (Lemma L (c), (3.11)′; V4-01).** Part III must state (3.11)′ on the localized support $\bigcup_C(U^C)^{\sim3}$ of the
  ripe lineage and prove that P7 (3.7)'s characteristic-function and gradient bounds restrict to it. Part I gives
  the identification of global and local sets there (Lemma I.2.14), valid for $m\le\frac{L+8}2$.
- **O-4 (range of P3's minimal generating sets).** Lemma I.3.16 reduces the multi-box check of P7 (2.13) to single
  boxes if $\mathbb B_k(\cdot)$ has range $\varpi\le\frac{L+8}2-m$ (UNCERTAIN; P3 (4.7)–(4.8) suggest $\varpi\le1$). Part II.
- **O-5 ($\pi'$ offsets; components of $\Omega^c$).** Minor UNCERTAINs: whether P1's $\pi'_j$ contains all $L$-block offsets
  (Definition I.2.5), and which adjacency defines the components of $\Omega^c$ in P5 (1.33) (Definition I.2.15; we take
  $*$-adjacency). Both to be settled with the summability (1.35) in Part II.
- **O-6 (Lemma B at hulls and at $k=0$).** (B) must hold for components of $Z^{\rm pre}$, i.e. after the hull rule: the
  hull-added cubes are new volume charged at P6's rate (P6 p. 22 [review]). The base rule (LF-6) must produce sets
  $\mathsf P_1,\dots,\mathsf S_1$ satisfying the constraints of Definition I.3.1 with $Z_0=\varnothing$. Part II.
- **O-7 (constant order; L-04). Closed in version 1.1** (audit P1-01): $M/M_1:=L^{m_0}$ with $m_0=m_0(d,L)$ by definition (row 5a),
  rows 4–6b as in LOCALIZATION §5.3, and the prefix binds $M_1$ (§I.1.4). Part I needs no upper bound on $M$ or $M_1$.
- **O-8 (the choice $c=0$ versus $c=a_{k+1}b$; SMALLFIELD.md).** Part I uses only (I.2), the bounds
  $|\log\gamma_k|,|\log\delta_k|\le\epsilon$, which the landed Lean lemmas prove for any perturbations $\xi$ with
  $\|\xi_k\|\le\frac{c_8}4q^{k+1}$; it does not use $c=0$. Where $c=0$ enters Parts II–IV: ARCH's Def-7 (D2) and LF-3 cite
  P4 Thm 2 "with $c_{k+1}=0$, $d_{k+1}=b_{k+1}$" and P5 (1.40); P7's main-action cancellation (2.53)–(2.58) and the
  renormalization of the window actions (2.10)–(2.12) use P5's normalization of the actions. Whether these need $c=0$
  beyond $\frac12<a_k<\frac32$ is a Part II/III check; I found no place in Part I.
- **O-9 (deterministic choices).** Part I implements the tie-breaks of ARCH R3-12 by a fixed choice function
  (`Classical.choose`), so the bookkeeping is a function of the region history and (D1) counts each history once. If
  the author prefers the lexicographic rules of ARCH §3.2 for readability, they are one admissible instance.
- **O-10 (Parts III–IV must use the changed constants).** $\omega_k$, $D_k$, $h_k$ change by $O(L)$ and $O(1)$; Lemma CH's
  $\hat W$, (2.33)′'s ring count and the late-scale constants of (M7) are unaffected in their exponents.


---
---

# Large-field reconstruction document, Part II: analytic objects, operators, Def-7

Version 1 (Part II, sections II.1–II.6), 2026-10-11. Brief: `orchestration/briefs/D-LFR-partII.md`. Input: Part I above
(version 1.1), ARCH v4 (§§3, 5, 8, 9), `LEMMA-F-astra.md` (cited as **LF-astra**), `BACKGROUND.md` v2 (**BG**),
`LOCALIZATION.md` v2 (**LOC**), `SMALLFIELD.md` v2 (**SF**), `GREEN.md`, `POLYMER.md` and their reviews; the landed Lean of
`Balaban/Background`, `Balaban/Localization`, `Balaban/Flow`, `Balaban/Multiscale`, `Balaban/Green`, `Balaban/Polymer`.
Status: draft for independent review; nothing here is approved or frozen. Tags and status words as in Part I
([checked] = re-read for this Part in the PDF text layer of P5–P7, or the page image where stated; [review] = taken from
a review or project document). §II.7 (LF-6, the base case) is written after Part III (ARCH §9).

**Purpose.** Part II supplies the objects that Def-7 needs and Def-7 itself: the running constants and their relation to
the a priori sequence $\hat\lambda$ (§II.1); the background fields as instances of the landed and proposed Def-5 objects,
P3's minimal generating sets, and the component-local boundary generating set that makes the operators factorize exactly
(§II.2); the characteristic functions, the operator domain and the analyticity spaces (§II.3); LF-1 with a complete proof
for hard spins (§II.4); the variables, kernels and operators, Lemma F, the exponents $\kappa$, the combinatoric factors $C$,
the budget $G$, the summability (1.27) and Lemma B (§II.5); and Def-7 as a predicate $\mathrm{IsRep}_k$ on representations
(§II.6). §II.L lists the Lean declarations and §II.O the status, the changes and the open items.

## II.0 Design decisions and summary of changes

Each decision is explained where it is used. D-II.1 and D-II.2 change ARCH v4; the others make ARCH precise.

**D-II.1 (Lemma F: a localized representation with a genuine minimizer).** The main action of the new large-field region
in P6 (3.2) uses the background $\phi_{k+1}(\mathbb B_{k+1}(\partial\Omega_{k+1});\tilde\psi)$ of P6 (2.15), whose generating set spans all
components; its value on one component depends on data near the others (LF-astra, "the raw factor is not exactly local";
P5 p. 505 [checked] makes the same remark for (2.17)). Following LF-astra's choice (b), the representation is changed so
that the factorization P5 (1.22) is exact, and the difference is carried by the boundary terms. **Change to LF-astra:** the
local background is not the decoupled-family field $\Phi_q(s^Z)$ of LF-astra (F.6)–(F.7), but the genuine minimizer
$\phi_{k+1}(\mathbb B^{\rm loc}_{k+1}(\partial\Omega_{k+1});\tilde\psi)$ for the generating set $\mathbb B^{\rm loc}$ obtained from P6 (2.15) by intersecting with the
neighbourhoods $U_{Z'}$ of the components (Definition II.2.4 (v)). Its $\Omega_1$ splits into mutually non-adjacent pieces, one per
component, so the Euler–Lagrange system decouples and the minimizer factorizes exactly (Lemma II.2.6). The change from P6's
background to this one is the same operation that P6 (2.16)–(2.17) performs to pass from $\mathbb B'_{k+1}$ to $\mathbb B_{k+1}(\partial\Omega_{k+1})$,
and its correction terms go to the boundary terms in the same way. Reasons: (i) the background stays a minimizer, so P7's
variational identities (2.50)–(2.58), the expansion P5 (2.23) and P6 (2.14) apply verbatim to the window actions (with
LF-astra's field they hold only up to the Euler–Lagrange residual); (ii) exact factorization is a property of a variational
problem with disconnected domain, with no parameter family; (iii) the analytic input for the correction terms is the
localization expansion already needed by P6 (2.16), not a new full-parameter version of I-4. LF-astra's construction is kept
as an alternative (remark after Lemma II.5.9).

**D-II.2 (which operators are defined and which are data).** The large-field operator of a localized history is defined by
a recursion along its lineage (ARCH §3.3, P6 (3.3)). In Def-7:
- the **quiet step operator** (a step with no new large-field cube in the component) is an explicit kernel built from
  Def-5 backgrounds, the Gaussian kernel of $T^{(k)}$, the characteristic functions and the main action (Definition II.5.6);
- the **non-quiet step kernels**, the **step boundary factors** $\exp b_k$ (P6 (3.3), (2.33)) and the **kept kernels** of $R$
  are *data* of the representation, required to have the properties that every consumer uses: positivity, measurability,
  support in $V_Z$, invariance, the operator domain, and the bound (1.26) with the explicit exponent (Definition II.5.7).

ARCH v4 (R3-08, §8.2) made all operators functions of the history and the small-field data. The change is needed because
the non-quiet step operator of P5 (2.47) contains the substitution $\psi_k=\psi^{(k)}(\square',\theta)+\beta_k^{-1/2}C^{(k)1/2}_{\rm loc}\psi$ of P5
(2.20), (2.39), whose ingredients are I-4 objects at $s=0$ (LOC I-4b(v), I-4c) whose very definition needs the convergence
of the walk expansion (LOC Theorem DG), and the kept operators of P7 are the output of $R$ itself. With D-II.2, Def-7 uses
only Def-5 backgrounds and explicit formulas; the constructions of the non-quiet step kernels and of the kept kernels are
the proofs of LF-3 and LF-4. Nothing is lost: every consumer uses only the listed properties, except LF-4 (P7 §2), which
uses the explicit form of the operator on the quiet window of a ripe component, and that form is explicit here
(Definition II.5.6; Lemma C (a): all steps of the window are quiet). As a consequence **LF-4's hypothesis becomes
$\mathrm{IsRep}^{\rm pre}_k(\mathrm{rep},\rho)$ alone**; ARCH §8.3 also required "rep is the output of LF-3", which referred to a
construction (§II.6.4).

**D-II.3 (one flow).** Def-7 (D2) uses the free flow $c_{k+1}=a_{k+1}b_{k+1}$ (SF §3.1 ruling). The uses of P5's $c=0$ in P5–P7 are
listed in §II.1.6; one of them (the exact composition of the window transformations, P7 p. 499) needs a perturbative
replacement in Part III (O-8′).

**D-II.4 (Def-7 is a predicate with existential data).** $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep},\rho)$ (ARCH R3-10). The data of rep are:
the small-field data, a finite set of admissible histories, and, per localized history prefix, the step data and kept
data of D-II.2, and the boundary terms. All bookkeeping, the quiet step operators, the localized operators, $\kappa$, $C$, $G$
are functions of these data.

**D-II.5 (the minimal generating sets; O-4 closed).** P3's minimal generating sets $\mathbb B_q(X)$ are written as explicit set
functions (Definition II.2.2). Their range is at most $(L+9)M_1$ fine units per scale unit, hence at most one $\pi_q$-cube once
$M\ge(L+9)M_1$, which the definition of $m_0$ guarantees (Part I §I.1.3 row 5a). This closes Part I's O-4: the reduction of P7
(2.13) to single core boxes (Lemma I.3.16) applies with $\varpi=2$ and $m\le\frac{L+4}2$.

**Summary of results.** Proved here: the comparison lemma for the running constants (II.1.3); the generating-set and range
properties of the minimal generating sets and of $\mathbb B^{\rm loc}$, and the exact factorization of its minimizer (II.2.3,
II.2.6); measurability and stencils of the characteristic functions (II.3.3); LF-1 with explicit $\gamma_0=\frac1{28d}$ (II.4.1);
the support and factorization statements of Lemma F for the representation (II.5.9); invariance (II.5.10); Lemma B with the
$\hat\lambda$ conversion, hull cubes included (II.5.12); the composition of operator bounds, (D5) for a step from a one-step bound
(II.5.13); the one-step bound for quiet steps (II.5.14); the summability (1.27) for the localized histories, including hull and
kept data (II.5.15). Cited: I-1, I-2 (BG), the existence of P6's background change expansion (P6 (2.16)–(2.17),
LOC I-5) and the one-step bound for non-quiet steps (P6 (3.4)–(3.9)), both of which are LF-3's to construct. Defined:
Def-7 and its variants (§II.6).

**Conventions of Part II.**
- *Units.* The fine torus is $\mathbb T=(\mathbb Z/\ell\mathbb Z)^d$, sites $x$, spacing $1$ (the units of BG and of the landed
  `GeneratingSet`, `dirichletOperator`, `BgData`). The scale-$j$ lattice $T^{(j)}\subset\mathbb T$ is the set of block corners
  $y\in L^j\mathbb Z^d$, the $j$-block of $y$ is $B_j(y)=y+\{0,\dots,L^j-1\}^d$ (Lean `jBlock`), $\ell_j:=L^j$, and $\pi_j$-cubes have side
  $ML^j$ and are indexed by the cube torus $\mathbb T_j$ of Part I. P5–P7 write everything at step $k$ in *scale-$k$ units*
  ($T^{(k)}$ has spacing $1$, $T_\eta$ has spacing $\eta=L^{-k}$); a length $r$ in scale-$k$ units is $rL^k$ fine units, P5's
  $|\partial^\eta\phi|<\delta$ is $\ell_k|\partial\phi|<\delta$ and $|\Delta^\eta\phi|,|\alpha|<\delta$ are $\ell_k^2|\Delta\phi|,\ell_k^2|\alpha|<\delta$ in fine units (BG §1.1:
  these are BG's scaled norms $|\cdot|_1,|\cdot|_2$ on the layer of spacing $\ell_k$). Volumes: $|X|_j:=L^{-jd}|X|_{\rm sites}$ (scale-$j$
  units), so a $\pi_j$-cube has $|\cdot|_j=M^d$, and $|X|_\#$ (Part I) counts $\pi_j$-cubes.
- *Spins and fields.* $N\ge2$; real fields take values in $\mathbb R^N$, complex ones in $\mathbb C^N$ with the bilinear product
  $u\cdot v=\sum_iu^iv^i$ (BG). $h\in S^{N-1}$; $g:\mathbb T\to\mathbb C^N$ with $\|g\|_{\ell^1}<1$ (the polydisc of Root-F).
- *Histories.* Region histories, localized histories $\mathfrak H_k(Z)$, lineages, the bookkeeping and ripeness are those of
  Part I §I.4 (with the overwrite of Definition I.3.11); "the step $k\to k+1$" produces $\Omega'_{k+1},\Omega_{k+1},\Omega''_{k+1},Z^{(0)}_{k+1},Z^{\rm pre}_{k+1}$
  from $Z_k$ and the record $(\mathsf P,\mathsf Q,\mathsf R,\mathsf S)_{k+1}$ (Definition I.3.1). All of these are finite sets of cubes, read as sets of
  fine sites when fields are involved.

---

## II.1 Running constants and the a priori sequence

### II.1.1 The running constants

**Definition II.1.1 (running constants and derived thresholds).** The small-field data of a representation at scale $k$
(Def-6 = SF §1.6, the small-field part of Def-7 (D2); §II.6) contain, for $0\le j\le k$, the running coefficients
$\beta_j>0$, $0<\nu_j$, and for $1\le j\le k$ the field renormalizations $z_j=1+\zeta_j$ and the vacuum constants $E_j$ (P4 (4.1),
(H.1); SF §3.1). The RG kernel constant $a$ is fixed in $[\frac9{10}(1-L^{-2})^{-1},\frac32)$ (SF §1.1, review S-08). Under the
free flow (D-II.3; SF §3.1 ruling)
$$a_j:=a\,\frac{1-L^{-2}}{1-L^{-2j}}\quad(j\ge1),\qquad\text{so }a_j=\texttt{compWeight}\ L\ a\ j\ \ (\text{Lean, }\texttt{Background/Composition.lean}).\tag{II.1}$$
The derived quantities (definitions, P5 p. 498 [checked]: "we define $p_0(\beta_j)=A_0(\log\beta_ja)^{p_0}$, $\delta_j=(\beta_ja)^{-1/2}p_0(\beta_j)$, etc. In the
future we will always use these definitions"):

| Symbol | Definition | Source |
|---|---|---|
| $\lambda_j$ | $\log(\beta_ja)$ (running) | Part I (I.2)–(I.3) |
| $R_j$ | $R^{\rm run}_j=R_{\rm base}\lambda_j^2$ | P5 (1.2) |
| $p_0(\beta_j),\ p_1(\beta_j)$ | $A_0\lambda_j^{p_0}$, $A_1\lambda_j^{p_1}$ with $p_1:=p_0$ | P5 p. 487, (2.42); P6 (3.9) ("we have taken $p_1=p_0$") |
| $\delta_j$ | $(\beta_ja)^{-1/2}p_0(\beta_j)=e^{-\lambda_j/2}A_0\lambda_j^{p_0}$ | P5 p. 498 |
| $p_2(\beta_j)$, $H_j$ | $A_2(\log\beta_j)^{p_2}$, $H_0\log\beta_j$ | P5 (1.30) |
| $\varepsilon_j$, $\varepsilon_{1,j}$ | $\alpha_0(1+\sum_{n\ge j}n^{-2})L^{-j\alpha}$, $\frac{A_1}{A_0}\varepsilon_j$ | SF §1.7 (P4 (H.1)); P5 (1.37) |
| $\mu_j$ | the fine-unit mass of the backgrounds at scale $j$: $\mu_j:=0$ if $\beta_j\nu_j\le1$, $\mu_j:=\nu_jL^{-2j}$ otherwise | P5 (1.9) [checked]; BG §1.1 |
| $\beta^{(q)}_n,\ a^{(q)}_n$ | for a multiscale action at level $q$ and $n\le q$: $\beta_qL^{-(q-n)(d-2)}$ and $a_q\frac{1-L^{-2q}}{1-L^{-2n}}$ | P5 (1.41), P6 p. 17, P7 (2.10) |
| $k_0$ | the last $k$ with $\beta_k\nu_k\le1$; *genuine* if it exists, and $k_0:=0$ (*conventional*) if $\beta\nu>1$ | P5 p. 490; Part I §I.1.1 |
| $k_f$ | the first $k$ with $\nu_k>\frac78L^{-2}$ | P4 §6; P7 p. 529 |

Under the free flow $a^{(q)}_n=a_n$ for all $q\ge n$ (insert (II.1)): the coefficients "renormalized to step $q$" of P7 (2.10) coincide
with the actual ones. Under P5's choice $c=0$ they differ by factors $1+O(\beta^{-1})$ (SF §3.1).

### II.1.2 Comparison with the a priori sequence

**Lemma II.1.2.** Assume the bounds (I.2) of Part I with $\epsilon\le\frac1{20}$ (Def-6 (H.6) through the landed `betaSeq_eq`,
`nuSeq_eq`, `norm_gammaSeq_le`), $a\in(1,\frac32)$, and $\hat\lambda_0\ge3$ (condition (Λ14) of §I.5.3). Then for all $j$:
(a) $\lambda_j\le\hat\lambda_j\le\lambda_j+2$, $\lambda_j\ge1$, and $R_{\rm base}\le R_j\le\hat R_j$; in particular the radius hypotheses (RH) of §I.3.1
hold for the flow and $R_j\ge R_{\rm base}$ (Lemma I.3.10 (c));
(b) $\hat\lambda_j-3\le\log\beta_j\le\hat\lambda_j$; hence $p_2(\beta_j)\le A_2\hat\lambda_j^{p_2}$, $\tau_j=2A_2\hat\lambda_j^{p_2}\ge2p_2(\beta_j)$, and
$H_0(\hat\lambda_j-3)\le H_j\le H_0\hat\lambda_j$;
(c) $\delta_j\le\bar\delta(\hat\lambda_j)$ with $\bar\delta(x):=eA_0x^{p_0}e^{-x/2}$, a decreasing function for $x\ge2p_0$;
(d) if $\hat\lambda_k\ge3/(1-2^{-1/(2p_0)})$ (condition (Λ15)), then $A_3(\log\beta_k)^{2p_0}\ge g_k=\frac12A_3\hat\lambda_k^{2p_0}$;
(e) $\log\beta_{k+1}-\log\beta_k\le(d-2)\log L+2\epsilon$;
(f) $k_f\le\hat k_f\le k_f+1$ if $k_f\ge1$ (Lemma I.5.6 (a)).

*Proof.* (a) $\lambda_j=\log(\beta a)+j(d-2)\log L+\log\gamma_j=\hat\lambda_j-1+\log\gamma_j$ and $|\log\gamma_j|\le\epsilon$; so $\lambda_j\ge\hat\lambda_j-2\ge1$
and $R_{\rm base}\le R_j=R_{\rm base}\lambda_j^2\le R_{\rm base}\hat\lambda_j^2$. (b) $\log\beta_j=\lambda_j-\log a$ with $0<\log a<\log\frac32<\frac12$. (c)
$\delta_j=A_0\lambda_j^{p_0}e^{-\lambda_j/2}$, $\lambda_j\le\hat\lambda_j$ and $\lambda_j\ge\hat\lambda_j-2$. (d) $(\log\beta_k)^{2p_0}\ge(\hat\lambda_k-3)^{2p_0}=\hat\lambda_k^{2p_0}(1-3/\hat\lambda_k)^{2p_0}$,
and $(1-3/x)^{2p_0}\ge\frac12$ iff $x\ge3/(1-2^{-1/(2p_0)})$. (e) $\beta_{k+1}/\beta_k=L^{d-2}\gamma_{k+1}/\gamma_k$. (f) Part I. $\square$

### II.1.3 The analytic conditions on $\lambda_*$ added by Part II

For all real $x\ge\lambda^{\rm II}_*$ (combined with Part I's lists into $\lambda_*$, §I.5.3):

| | Condition (for all $x\ge\lambda_*^{\rm II}$) | Used in |
|---|---|---|
| (Λ15) | $x\ge3/(1-2^{-1/(2p_0)})$ | Lemma II.1.2 (d), Lemma B |
| (Λ16) | $H_0\big[(1-L^{-d})(x-3)-L^{-d}((d-2)\log L+1)\big]\ge1$ and $x\ge c_2+2$ | Lemma B (old volume, new volume) |
| (Λ17) | $3dL\,\bar\delta(x)\le\min\{c_1^{\rm BG},\,c_{11}\}/C_4$ and $\bar\delta(x)\le\min\{\delta_{**},\delta_*\}/(C_3C_4)$ | Remark II.2.8 (the backgrounds of the step exist on the support of the kernels), Lemma II.3.3 (faithfulness) |

$c_1^{\rm BG},C_3,C_4,\delta_{**}$ are the constants of BG Theorem 5.2, Lemma 5.3 and Theorem 6.1 ($(d,L,N)$-constants, row 4), $\delta_*$ that of
BG Prop 5.1, $c_{11}$ that of P7 Lemma 2.1 (row 4). Each condition compares a fixed constant with a function tending to $\infty$
(or $0$), so $\lambda^{\rm II}_*$ exists; (Λ16) is the place where $c_2$ (row 14) enters, so $\lambda_*$ is chosen after row 14, as in §I.1.3.

### II.1.4 Causality

Def-7 at scale $k$ (§II.6) reads the running constants $(\beta_j,\nu_j,z_j,E_j)_{j\le k}$ only, and the test "$j\le k_0$" only through
$\beta_j\nu_j\le1$ for $j\le k$ (P5 p. 490: $\beta_j\nu_j$ is increasing, so "$j\le k_0$" is decided at scale $j$). All bookkeeping
(radii $r_j$, widths, windows, ripeness, budget thresholds) uses $\hat\lambda$ (ARCH R3-06, option B), i.e. $\beta$ and $j$ only. The
horizon $\hat k_f(\nu)$ enters Def-7 only through the threshold $W_{k+1}(\hat k_f)$ of the frozen invariant (H6♭), i.e. only in the
class $\mathcal R^\flat_k$ for $k\ge k_0$ (§II.6.3); no object (background, characteristic function, operator, exponent, combinatoric
factor) at any scale uses it (OBSERVABLES §4.2 (5), received during the writing; see §II.6.5).

### II.1.5 Free flow versus $c=0$ (open item O-8 of Part I)

Def-7 uses the free flow $c_{k+1}=a_{k+1}b_{k+1}$ (D-II.3), so $a_j$ is the deterministic sequence (II.1) and $\beta_j=\beta L^{j(d-2)}\gamma_j$ with
$\gamma_{j+1}=\gamma_j/(1+\xi^{(j)}_3)$ (SF §3.1, P4 (5.28)). The places where P5–P7 use P5's choice $c_{k+1}=0$, $d_{k+1}=b_{k+1}$
[checked in the text layers]:
1. **P5 (1.40)–(1.41), p. 498.** $c=0$ makes $\beta_ja_j$ follow the free flow, and with the $j$-dependent kernel constant
   $a=\frac{1-L^{-2j}}{1-L^{-2}}a_j$ of $T^{(j)}$ it gives $\beta_ja=\beta_ka(L^j\eta)^{d-2}$ *exactly*: "This way we have written all the
   renormalization transformations $T^{(j)}$ in terms of the common constants $\beta_k,a$ … we can apply all the composition formulas
   proved in Sect. 4 [2]. They will be used in Sect. 2 of the third paper."
2. **P6 p. 3.** "Now it is convenient to choose the one discussed … in Sect. 1 of [5], see in particular (1.40), (1.41) [5]" — the
   choice for the renormalization of P6 §2; it is used there only through item 1.
3. **P7 p. 499, before (2.7).** "Let us recall now the discussion of the renormalization conditions (1.36) [4], and the choice of the
   constants $a$ … leading to the equalities (1.37) [4]. These are exactly the equalities we need to use the composition formulas in
   Sect. 4 [2]." P4 has no equations (1.36)–(1.37) (its §1 ends at (1.10) [checked, text layer pp. 681–683]); the citation is read as
   P5 (1.40)–(1.41) (a citation misprint, probably preprint numbering; new erratum candidate N-II-2). Consumers: the composed window
   transformation $T(T^{(k)}_1,(\mathbb B_k\cap Z^c_{k_1})\cup(T^{(k_1)}\cap Z_{k_1}))$ in (2.7), its kernel (2.9) with the weights $a(\Delta_k(z),\mathbb B_k)$ of
   P2 (4.6)–(4.7), the identity P2 (4.18) used after (2.55), and the composition formula P2 (4.11) used for (2.57).
4. **Not used:** P7 (2.10)–(2.12) (the renormalization of the window actions: it replaces the actual coefficients of each step by
   those renormalized to step $k$, in $k-j-1$ steps through P6 (2.31), and bounds the change by (2.11); this works for any flow with
   (H.6)); P7 (2.53)–(2.54) (they use the minimality of $\psi'_{k_1,k}$ and P2 (4.21)); Part I and the rest of Part II (they use only
   (I.2) and $a_j\in(\frac12,\frac32)$).

Under the free flow the $T^{(j)}$ have the common constant $a$ and $\beta_ja=\beta_ka\,L^{-(k-j)(d-2)}\cdot\gamma_j/\gamma_k$, where
$|\log(\gamma_j/\gamma_k)|\le\sum_{i=j}^{k-1}|\log(1+\xi^{(i)}_3)|\le2C_\xi\beta^{-1}L^{-2\gamma(j+1)}/(1-L^{-2\gamma})$ by SF's bound $|\xi^{(i)}|\le C_\xi\beta^{-1}L^{-2\gamma(i+1)}$.
So the composition of item 3 is exact up to relative errors $O(\beta^{-1}L^{-2\gamma k_1})$ in the coefficients. **Carried to Part III
(O-8′):** the Gaussian algebra of P2 §4 holds for arbitrary positive coefficients (landed `integral_blockSpin_comp`,
`Gaussian/BlockSpin.lean`), with composed weights $a^{(b)}(\Delta,\mathbb B)$ given by the actual coefficients; what fails is the identity
P2 (4.18), equivalently (C1) of BG §6.1, for these weights. Part III §III.2 must either (i) carry the weights $a^{(b)}$ through
(2.9)–(2.58) and put the difference $a^{(b)}-a^{(6.1)}=O(\beta^{-1}L^{-2\gamma k_1})a$ into $C_{k_1,k}$ of (2.15) (the cancellation (2.55)/(2.57) then
leaves a quadratic remainder bounded by $O(\beta^{-1})\times$ the window volume, which (2.15)'s budget absorbs), or (ii) use $c=0$ for
the whole flow, which would require the perturbation statement for the Gaussian kernels that SF §3.1 says no source provides.
Route (i) is recommended. Def-7 itself does not depend on the choice beyond the values of the running constants.

---

## II.2 Background fields

### II.2.1 The Def-5 objects (cited)

All backgrounds of Def-7 are instances of the Def-5 objects of BG §7 at $\lambda=\infty$. Status of each:

| Object (BG) | Lean | Status |
|---|---|---|
| `BgData G` (layer-constant data $\Psi$, block-constant $\tilde h$), `source` (1.1), `action` (1.2) | `Background/Data.lean`: `BgData`, `source`, `action` | landed |
| `IsEL`, `IsSmallSolution c₀`, `IsMinimizer` | `Background/Data.lean` | landed |
| data domains $\tilde\Psi(\mathbb B;\delta)$ (R1)–(R4), $\tilde\Psi^c(\mathbb B;\delta,\varepsilon)$ (C1)–(C3), their unions $\mathcal D_{\mathbb R}$, $\mathcal D$ | `InPsiTilde`, `InPsiTildeC`, `InDomainR`, `InDomainC`, `InUnionDomainR`, `InUnionDomainC` | landed |
| Prop 5.1 (perturbed system: $\exists!$, analytic, $\le K_2\delta_1$) | `prop51_exists_unique`, `prop51_analytic`; abstract family `GreenFamily`, `prop51_core`, `exists_analytic_core` | landed |
| Lemma 5.3 (approximate solution) | `lemma53`, `approxField_analytic`, `residualRaw_analytic` | landed |
| Theorem 5.2 = I-1(a)–(d), (f) ($\exists!$ small solution, analyticity, bounds, real minimiser) | — | proved on paper (BG §5.4) from the two landed results; assembly not landed |
| Def-5(a),(b): `bgField G a μ h Ψ` (dite on $\exists!$ `IsMinimizer`), `bgFieldC c₀ G a μ D` (dite on $\exists!$ `IsSmallSolution c₀`), multipliers; Theorems 7.1–7.2 | — | proposed (BG §7), not landed |
| Def-5(c) `composeField` (6.2), weights (6.1), Theorem 6.1 (ii)–(iii), Prop 6.4 | `composeField`, `compWeight`, `compWeight_C1`, `isEL_compose`, `composedSystem_unique_lt`, `prop64` | landed; Lemmas 6.2/6.3 (domain) open (W28) |
| linear response, $G-\Pi\succeq0$ | `linearResponse`, `green_sub_constrainedOp_posSemidef` | landed |

Notation: for a generating set $G$ at level $q$, weights $a$, fine mass $\mu$ and data $D$, $\mathrm{bg}(G;D):=$ `bgFieldC c₀ G a μ D` with
$c_0$ the constant of BG Theorem 5.2 (it equals `bgField` on real data in $\mathcal D_{\mathbb R}$, BG Theorem 7.2), and $\alpha(G;D)$ the
multiplier. Unless said otherwise the weights are $a^{(q)}_n=a_n$ (II.1) and the mass is $\mu_q$ (Definition II.1.1). Generating
sets are Lean `GeneratingSet d L N₀ q ϱ` on the fine torus ($N_0L^q=\ell$), with $\Omega_{q+1}=\varnothing$.

### II.2.2 Lifts and P3's minimal generating sets

**Definition II.2.1 (lifted data).** Let $G$ be a generating set at level $q$ and $D=(\Psi,\tilde h)$ with $\tilde h\equiv h$.
(a) *Single-scale lift* (P5 (1.4): $\tilde\psi_k=Q^*(T^{(k)}_1,\mathbb B_k(W_k))\psi_k$): for a field $\psi_k:T^{(k)}\to\mathbb C^N$ and $q=k$,
$\mathrm{lift}_k\psi_k(x):=\psi_k(y_k(x))$, $y_k(x)$ the corner of the $k$-block containing $x$.
(b) *Mixed lift* (P5 (2.11)–(2.12)): for $q=k+1$, a set $\Omega$ that is a union of $(k+1)$-blocks with $\Omega_{k+1}(G)\subset\Omega$, and fields
$\psi_k$ on $T^{(k)}$, $\vartheta$ on $T^{(k+1)}$: $\mathrm{lift}_{k,k+1}(\psi_k,\vartheta)(x):=\vartheta(y_{k+1}(x))$ if $x\in\Omega$, $:=\psi_k(y_k(x))$ otherwise.
Both are layer-constant for $G$ (every $n$-block with $n\le k$ lies in a $k$-block, and the $(k+1)$-blocks of the top layer lie in $\Omega$),
so they are `BgData G`; values on the one-site collar $C(\Omega_1(G))$ are given by the same formula.

**Definition II.2.2 (minimal generating set; P3 (4.4)–(4.6), p. 68 text layer, p. 69 page image [checked]).** Let $q\ge1$ and
let $X\subset\mathbb T$ be a union of $\pi_q$-cubes. For $1\le n\le q$ let $\mathcal C_n$ be the partition of $\mathbb T$ into cubes of side $s_n:=M_1L^n$
aligned with $s_n\mathbb Z^d$. Define recursively
$$\Omega_q(X):=X,\qquad\Omega_n(X):=\bigcup\big\{C\in\mathcal C_n:\ \mathrm d_{\mathcal C_n}(C,\{C'\in\mathcal C_n:C'\subset\Omega_{n+1}(X)\})\le5L\big\}\quad(n=q-1,\dots,1),\qquad\Omega_{q+1}(X):=\varnothing,$$
with $\mathrm d_{\mathcal C_n}$ the cyclic sup-distance of cube indices. $\mathbb B_q(X)$ is the family $(\Omega_n(X))_{1\le n\le q+1}$. (P3 (4.4) defines $\Omega_q(X)$
as the union of the $LM_1$-cubes of the cover that contain an $LM_1$-cube of the cover contained in $X$; for $X$ a union of $\pi_q$-cubes,
which are unions of aligned cubes of side $LM_1L^q$ because $M=L^{m_0}M_1$ with $m_0\ge1$, this union is $X$. (4.5)–(4.6): "add $5L$ layers
of $M_1L^n\eta$-cubes".)

**Lemma II.2.3 (minimal generating sets).** Let $X\subset X'$ be unions of $\pi_q$-cubes, and $\varrho_3:=5LM_1$.
(a) $\mathbb B_q(X)$ is a generating set with separation $\varrho_3$ (P2 (1.1)–(1.3)); with $\Omega_{q+1}:=\varnothing$ it is a Lean
`GeneratingSet d L N₀ q ϱ₃`, and $\varrho_3\ge R_0(d,L)$ (BG §2) once $M_1\ge R_0(d,L)/(5L)$ (a row-6 lower bound on $M_1$).
(b) (Monotonicity) $\Omega_n(X)\subset\Omega_n(X')$ for all $n$; in particular $\mathbb B_q(X)\prec\mathbb B_q(X')$ in the sense of BG §6.1 (Lean `Precedes`).
(c) (Range) $\Omega_1(X)\cup C(\Omega_1(X))\subset\{x:\operatorname{dist}_\infty(x,X)\le r_q\}$ with $r_q:=(5L+1)M_1L^q/(L-1)$, and for every site $x$ the
statement "$x\in\Omega_n(X)$" depends only on $X\cap\{y:\operatorname{dist}_\infty(x,y)\le r_q\}$. Since $r_q+1<ML^q$ (because $\frac{5L+1}{L-1}\le11$ for $L\ge2$
and $M/M_1=L^{m_0}\ge14d\ge42$), $\Omega_1(X)\cup C(\Omega_1(X))\subset X^{\sim1}$ and $\mathbb B_q(\cdot)$ has *range* $\varpi=1$ in $\pi_q$-cubes in the sense of
Lemma I.3.16: $\Omega_n(X)\cap E$ depends only on $X\cap E^{\sim1}$.
(d) (Disjoint unions) If $X=X_1\sqcup X_2$ with $\mathrm d(X_1,X_2)\ge3$ ($\pi_q$-cubes), then $\Omega_n(X)=\Omega_n(X_1)\sqcup\Omega_n(X_2)$ with
$\operatorname{dist}_\infty(\Omega_1(X_1)\cup C(\Omega_1(X_1)),\Omega_1(X_2)\cup C(\Omega_1(X_2)))\ge2$.

*Proof.* (a) Nested by construction; each $\Omega_n(X)$ is a union of cubes of side $M_1L^n$, hence of $n$-blocks (side $L^n$), so
`blockUnion` holds. Separation: if $x\notin\Omega_n(X)$ and $y\in\Omega_{n+1}(X)$, the $\mathcal C_n$-cube of $y$ is contained in $\Omega_{n+1}(X)$ (which is a union
of $\mathcal C_{n+1}$-cubes, each a union of $\mathcal C_n$-cubes), and the $\mathcal C_n$-cube of $x$ is at index distance $>5L$ from it, so
$\operatorname{dist}_\infty(x,y)\ge5Ls_n+1>\varrho_3L^n$; the $\ell^1$ distance of the Lean field dominates the sup-distance. (b) Induction on $n$
downward; the defining condition is monotone in $\Omega_{n+1}$. (c) A point of a $\mathcal C_n$-cube at index distance $\le5L$ from a cube $C'$ is
within sup-distance $(5L+1)s_n$ of $C'$; summing over $n<q$, $\sum_{n=1}^{q-1}(5L+1)M_1L^n\le(5L+1)M_1L^q/(L-1)$; the collar adds one site,
absorbed since the sum has strict room. The locality statement follows by the same induction. $r_q<ML^q$ because
$M/M_1=L^{m_0}\ge42$ (Part I row 5a) and $\frac{5L+1}{L-1}+1\le12$. (d) By (c) the two families are built from disjoint, far apart seeds,
and $2r_q+2<3ML^q$. $\square$

With (c), Lemma I.3.16 applies to P7's generating set $\mathbb B_{k_1,k}$ (2.13) with $\varpi=1$ for each minimal piece; counting one more
cube for the collar-level dependence of the backgrounds, $\varpi=2$ and $m\le\frac{L+4}2$ suffice (Part I O-4; D-II.5).

### II.2.3 The generating sets of a step

Fix the step $k\to k+1$ of a region history (Definition I.3.1), with $W_k:=(Z^c_k)^{\approx2}$ (scale $k$, P5 (1.4)), $U_{k+1}:=(Z^{\rm pre}_{k+1})^{\approx}$
(scale $k+1$), and for a component $Z'$ of $Z^{\rm pre}_{k+1}$ put $U_{Z'}:=Z'^{\approx}$, $V_{Z'}:=U_{Z'}^{\sim}$ (scale $k+1$). By Lemma I.2.13 the sets
$V_{Z'}$ of distinct components are at mutual index distance $\ge L+7$.

**Definition II.2.4 (generating sets of the step).**
(i) $G_k(\square):=\mathbb B_k(\square^{\sim2})$ for $\square\in\pi_k$ (P5 (1.19)).
(ii) $G_{k+1}(\square'):=\big(\Omega_1(\square'^{\sim2}),\dots,\Omega_k(\square'^{\sim2}),\ \Omega_{k+1}\cap\square'^{\sim2},\ \varnothing\big)$ for $\square'\in\pi_{k+1}$, where $\Omega_n(\square'^{\sim2})$
are the layers of $\mathbb B_{k+1}(\square'^{\sim2})$ (P5 (2.11) [checked]).
(iii) $G^{\rm sf}_k:=\mathbb B_k(W_k)$ (P5 (1.4)); and, for $j\le k$, $\mathbb B_j(W_k)$, so that $\mathbb B_j(W_k)\prec\mathbb B_k(W_k)$ (Lemma II.2.3 (b) applied to the
layers: $\Omega_n(\mathbb B_j(W_k))\subset\Omega_n(\mathbb B_k(W_k))$ for $n\le j$).
(iv) (P6 (2.15) [checked]) $G^\partial_{k+1}:=\mathbb B_{k+1}(\partial\Omega_{k+1})$, the family with
$\Omega_n:=(\Omega_n(W_k)\cap\Omega^c_{k+1})\cup(\Omega_n(U_{k+1})\cap\Omega_{k+1})$ for $n\le k$, $\Omega_{k+1}:=U_{k+1}\cap\Omega_{k+1}$, $\Omega_{k+2}:=\varnothing$, where $\Omega_n(W_k)$ are
the layers of $\mathbb B_k(W_k)$ and $\Omega_n(U_{k+1})$ those of $\mathbb B_{k+1}(U_{k+1})$.
(v) (**local version**, D-II.1) for each component $Z'$: $G^{Z'}_{k+1}$ is defined as in (iv) with $W_k$ replaced by $W_k\cap U_{Z'}$ and
$U_{k+1}$ by $U_{Z'}$; and $\mathbb B^{\rm loc}_{k+1}(\partial\Omega_{k+1}):=\bigcup_{Z'}G^{Z'}_{k+1}$ (layerwise union).

**Lemma II.2.5 (the step generating sets).** Assume (RH) of §I.3.1 and $M_1\ge R_0(d,L)/(5L)$.
(a) Each of (i)–(v) is a generating set with separation $\ge\varrho_3$ (Lean `GeneratingSet d L N₀ q ϱ₃` with $q=k$ or $k+1$).
(b) $\Omega_1(G^{Z'}_{k+1})\cup C(\Omega_1(G^{Z'}_{k+1}))\subset V_{Z'}$, and the pieces of $\mathbb B^{\rm loc}$ for distinct components are at fine distance $\ge2$.
(c) On the set $E_{Z'}:=Z'^{\sim[R_k]}$ (scale $k+1$) the layers of $G^{Z'}_{k+1}$ and of $G^\partial_{k+1}$ coincide: $\Omega_n(G^{Z'})\cap E_{Z'}=\Omega_n(G^\partial)\cap E_{Z'}$.

*Proof.* (a) For (i)–(iii), Lemma II.2.3 (a); for (ii) the extra top layer $\Omega_{k+1}\cap\square'^{\sim2}$ lies in $\Omega_{k+1}(\square'^{\sim2})=\square'^{\sim2}$ and the
separation from $\Omega_k(\square'^{\sim2})^c$ is that of $\mathbb B_{k+1}(\square'^{\sim2})$. For (iv): nested since both families are; block unions since
$\Omega_{k+1}$ is a union of $(k+1)$-blocks. Separation between $x\notin\Omega_n$ and $y\in\Omega_{n+1}$: if both lie on the same side of $\Omega_{k+1}$ it is
that of $\mathbb B_k(W_k)$ or of $\mathbb B_{k+1}(U_{k+1})$. If $y\in\Omega_{k+1}$ and $x\in\Omega^c_{k+1}\setminus\Omega_n(W_k)$, then $x\notin W_k$ while
$\Omega_{k+1}\subset Z^c_k$ is at distance $\ge2([R_{k-1}]+1)ML^k$ from $W_k^c$ (definition of $W_k$, Lemma I.3.5 (f)); if $y\in\Omega^c_{k+1}$ and
$x\in\Omega_{k+1}\setminus\Omega_n(U_{k+1})$, then $x\notin U_{k+1}\supset(\Omega^c_{k+1})^{\sim([R_k]+1)}$ (since $\Omega^c_{k+1}\subset Z^{(0)}_{k+1}\subset Z^{\rm pre}_{k+1}$, Lemma I.3.5 (e)), so
$\operatorname{dist}_\infty(x,y)\ge([R_k]+1)ML^{k+1}$. Both exceed $\varrho_3L^n$ under (RH). (v): each $G^{Z'}$ as in (iv) (intersections with $U_{Z'}$
preserve the argument because $U_{Z'}$ is a union of $\pi_{k+1}$-cubes); the union by (b). (b) Lemma II.2.3 (c): the layers lie within one
$\pi_k$-cube of $W_k\cap U_{Z'}$, resp. one $\pi_{k+1}$-cube of $U_{Z'}$, hence in $U_{Z'}^{\sim1}=V_{Z'}$; distinct $V$'s are $\ge L+7$ cubes apart.
(c) By the range statement of Lemma II.2.3 (c): on $E_{Z'}$, $W_k\cap U_{Z'}$ agrees with $W_k$ and $U_{Z'}$ with $U_{k+1}$ within one cube of every
point, because $U_{Z'}\supset Z'^{\sim([R_k]+1)}$ and the other components' sets are outside $V_{Z'}$. $\square$

**Lemma II.2.6 (exact factorization of the local background).** Let $D$ be data for $\mathbb B^{\rm loc}:=\mathbb B^{\rm loc}_{k+1}(\partial\Omega_{k+1})$ and $D_{Z'}$ its
restriction to $\Omega_1(G^{Z'})\cup C(\Omega_1(G^{Z'}))$. Then: (a) $D\in\tilde\Psi(\mathbb B^{\rm loc};\delta)$ iff $D_{Z'}\in\tilde\Psi(G^{Z'};\delta)$ for every $Z'$, and the same for
$\tilde\Psi^c$; (b) $(\phi,\alpha)$ solves (EL) for $\mathbb B^{\rm loc}$ with $|\alpha|_2<c_0$ iff every restriction $(\phi,\alpha)|_{\Omega_1(G^{Z'})}$ solves (EL) for $G^{Z'}$ with
data $D_{Z'}$ and $|\alpha|_2<c_0$; hence $\mathrm{bg}(\mathbb B^{\rm loc};D)|_{\Omega_1(G^{Z'})}=\mathrm{bg}(G^{Z'};D_{Z'})$ whenever the left side is defined by the $\exists!$
branch; (c) the minimiser of (1.2) for $\mathbb B^{\rm loc}$ is the product of the minimisers of the pieces.

*Proof.* By Lemma II.2.5 (b) no bond of $\mathbb T$ joins two pieces, no collar site of one piece lies in another piece, and every block of
every layer lies in one piece. The operator $H_D(\alpha)=-\Delta^D_{\Omega_1}+Q^*aQ+\mu+\alpha$ (BG §1.1) is therefore block diagonal, the source
$S(\Psi,\tilde h)(x)$ of BG (1.1) at $x$ in a piece involves only data of that piece and its collar, the constraint is pointwise, and the
uniqueness class $\ell(x)^2|\alpha(x)|<c_0$ is pointwise. (a) Each of (R1)–(R4), (C1)–(C3) is a conjunction of conditions on single blocks,
on pairs of adjacent blocks (which lie in one piece) or on $h$ alone. (b) and (c) follow, and (c) also from the additivity of the action
(1.2) over the pieces. $\square$

**Definition II.2.7 (the backgrounds of Def-7).** At the step $k\to k+1$ (weights $a_n$, masses as stated):
(i) $\phi_k(\square;\psi_k):=\mathrm{bg}(G_k(\square);\mathrm{lift}_k\psi_k)$, $\alpha_k(\square;\psi_k)$ its multiplier, mass $\mu_k$ (P5 (1.19));
(ii) $\phi'_{k+1}(\square';\psi_k,\theta):=\mathrm{bg}(G_{k+1}(\square');\mathrm{lift}_{k,k+1}(\psi_k,\theta))$ with $\Omega=\Omega_{k+1}$, mass $\mu_k$ (P5 (2.12); the
unrenormalized coefficients of the step, $a_{k+1,u}=a_{k+1}$ under the free flow, $\nu_{k+1,u}L^{-2(k+1)}=\nu_kL^{-2k}$); $\theta$ is the block variable of $T^{(k)}$;
(iii) $\phi_k:=\mathrm{bg}(\mathbb B_k(W_k);\mathrm{lift}_k\psi_k)$ and $\psi^{(j)}_k:=$ `composeField` $(\mathbb B_j(W_k),\mathbb B_k(W_k),a;\phi_k,\mathrm{lift}_k\psi_k)$, $j\le k$ (P5 (1.4);
BG (6.2)): the small-field backgrounds, used only in (D2);
(iv) $\phi^{\rm loc}_{k+1}(\psi_k,\psi_{k+1})$, the field on $\bigsqcup_{Z'}\Omega_1(G^{Z'})$ equal on each piece to $\mathrm{bg}(G^{Z'}_{k+1};\mathrm{lift}_{k,k+1}(\psi_k,\psi_{k+1}))$ with
$\Omega=\Omega_{k+1}$ and mass $\mu_{k+1}$ (the background of the main action of the new large-field region; it replaces
$\phi_{k+1}(\mathbb B_{k+1}(\partial\Omega_{k+1});\tilde\psi)$ of P6 (3.2), D-II.1). By Lemma II.2.6 it equals $\mathrm{bg}(\mathbb B^{\rm loc};\cdot)$ on the $\exists!$ domain, and by
construction it is a product of functions of the data in the single $V_{Z'}$.

(The literal P6 (3.2) uses the renormalized variable: $\tilde\psi$ is built from $\psi_{k+1}$ on $\Omega_{k+1}$, while P5 (2.12) is built from
$\theta=z_{k+1}\psi_{k+1}$; we follow each source literally. UNCERTAIN (minor): P6 does not say whether the background of (3.2) is
evaluated at $\psi_{k+1}$ or at $\theta$; since $z_{k+1}=1+O(\varepsilon_{k+1})$ either choice gives the same estimates.)

**Remark II.2.8 (where the backgrounds are evaluated).** Every background enters a kernel only multiplied by the indicator that
its data lie in the open real domain $\mathcal D_{\mathbb R}$ of BG Theorem 7.1 (Definitions II.3.1, II.5.6). On that domain $\mathrm{bg}$ is the unique
minimiser and is real analytic in the data (BG Theorems 5.2, 7.1–7.2), so all kernels below are Borel functions, and the junk
value of the `dite` is never observable. That the indicator equals $1$ on the support of the remaining factors of the kernel is the
regularity statement of P5 (2.7), (2.10) and P6 (2.6) [checked] ("on the domain $W_{k+1}$ there are only the small field functions
$\chi_{k+1}(\square')$"): the characteristic functions imply data in $\tilde\Psi(\cdot;3dL\delta_k)$, which lies in $\mathcal D_{\mathbb R}$ by (Λ17). It is used only
to identify our operators with P5–P6's (LF-3); Def-7 does not need it.

**Remark II.2.9 (P7's backgrounds).** $\psi^0_k$ of P7 (2.34), $\phi^0_k=\phi_k(\mathbb B_k(U_k);\tilde\psi^0_k)$ and $\psi^0_{k_1,k}$ of (2.40) are $\exists!$ objects (P7
Lemma 2.1 [checked]: unique solution in $\tilde\Psi(U^\sim_k;K_6\delta)$ for data in $\tilde\Psi(U^\sim_k\cap Z^c_0;\delta)$, $\delta\le c_{11}$, constants absolute for boxes of
size $<15$, our $D_0$). They are used only inside $R$ (P7 §§2–3), whose output enters Def-7 only through the kept data (D-II.2);
they are defined in Part III (§III.3, §III.6).

---

## II.3 Characteristic functions, the operator domain, analyticity spaces

### II.3.1 Characteristic functions

**Definition II.3.1 (regularity predicate).** Let $G$ be a generating set at level $q$, $D=(\Psi,h)$ real data for $G$, $\delta>0$, $T$ a set of
$q$-blocks of the top layer of $G$, and $S$ a set of sites of $\Omega_1(G)$. With $\phi=\mathrm{bg}(G;D)$, $\alpha$ its multiplier, $\bar\phi$ the extension of $\phi$ by
$\Psi$ to the collar, and $\nu:=\mu L^{2q}$ the dimensionless mass,
$$\mathrm{Reg}_q(G,D,\delta;T,S):\iff D\in\mathcal D_{\mathbb R}(G)\ \wedge\ \max_{y\in T}|\Psi_q(y)-(Q_q\phi)(y)|<\delta\ \wedge\ \max_{x\in S}\max\{\ell_q|\partial_e\bar\phi(x)|,\ \ell_q^2|\Delta\bar\phi(x)|,\ \ell_q^2|\alpha(x)|\}<\delta$$
$$\wedge\ \big[\nu>0\Rightarrow\max_{x\in S}|\phi(x)-h|<\delta/\sqrt\nu\ \wedge\ |h\cdot h-1|<\delta^2/\nu\big],$$
where $\partial_e$ runs over the $2d$ unit vectors and $(Q_q\phi)(y)$ is the average of $\phi$ over the $q$-block $y$. ($\mathcal D_{\mathbb R}(G)$ is the open real domain of BG
Theorem 7.1, `InUnionDomainR c₁ μ`; the conjunct is explained in Remark II.2.8.)

**Definition II.3.2 (the characteristic functions; P5 (1.18)–(1.19), (2.5), (2.13), (2.42), P6 (2.1) [checked]).** For a cube $\square\in\pi_k$,
$\square'\in\pi_{k+1}$, write $\square^{\sim}$ etc. for neighbourhoods in the cube torus of the scale of the cube, and $T_k(\cdot)$, $S(\cdot)$ for the $k$-blocks and the
sites of a set.
1. $\chi_k(\square):=\mathbf 1\big[\mathrm{Reg}_k(G_k(\square),\mathrm{lift}_k\psi_k,\delta_k;\ T_k(\square^\sim),\ S(\square^\sim))\big]$; $\chi_k(X):=\prod_{\square\subset X}\chi_k(\square)$ (P5 (1.18)–(1.19), mass $\mu_k$:
   the $h$-conditions are present only for $k>k_0$).
2. $\chi'^{(k)}(\square'):=\mathbf 1\big[|\theta(y)-(Q\psi_k)(y)|<2\delta_k\ \forall y\in T_{k+1}(\square')\big]$, $(Q\psi_k)(y):=L^{-d}\sum_{y'\in T_k(B_{k+1}(y))}\psi_k(y')$ (P5 (2.5)); $\theta$ the
   block variable of $T^{(k)}$, after renormalization $\theta=z_{k+1}\psi_{k+1}$.
3. $\chi'_{k+1}(\square')$ (P5 (2.13)): with $G=G_{k+1}(\square')$, $D=\mathrm{lift}_{k,k+1}(\psi_k,\theta)$ ($\Omega=\Omega_{k+1}$), $\phi'=\phi'_{k+1}(\square';\psi_k,\theta)$, $\alpha'$ its
   multiplier: $\chi'_{k+1}(\square'):=\mathbf 1$ iff $D\in\mathcal D_{\mathbb R}(G)$, $|\psi_k(y)-(Q_k\phi')(y)|<\frac34\delta_k$ for $y\in T_k(\square'^\sim\setminus\Omega_{k+1})$,
   $|\theta(y)-(Q_{k+1}\phi')(y)|<\frac54\delta_k$ for $y\in T_{k+1}(\square'^\sim\cap\Omega_{k+1})$, $\ell_k|\partial_e\bar\phi'|,\ \ell_k^2|\Delta\bar\phi'|,\ \ell_k^2|\alpha'|<\frac34\delta_k$ on $S(\square'^\sim)$, and,
   for $k>k_0$, $|\phi'-h|<\frac34\delta_k/\sqrt{\nu_k}$ on $S(\square'^\sim)$ and $|h\cdot h-1|<\frac9{16}\delta_k^2/\nu_k$.
4. $\chi^{(k)}(\square'):=\mathbf 1\big[|\psi'_k(x)|<p_1(\beta_k)\ \forall x\in T_k(\square')\big]$ (P5 (2.42)), $\psi'_k$ the fluctuation variable of the step (§II.5.1).
5. $\chi_{k+1}(\square'):=\mathbf 1\big[\mathrm{Reg}_{k+1}(\mathbb B_{k+1}(\square'^{\sim2}),\mathrm{lift}_{k+1}\psi_{k+1},\delta_{k+1};\ T_{k+1}(\square'^\sim),S(\square'^\sim))\big]$ (P6 (2.1) = P5 (1.19) at $k+1$).
For each kind, $\chi(X)$ is the product over the cubes of $X$ and $\chi^c(\square):=1-\chi(\square)$, $\chi^c(X):=\prod_{\square\subset X}\chi^c(\square)$ (P5 (2.6)).

The units: P5's $|\partial^\eta\phi|,|\Delta^\eta\phi|,|\alpha|<\delta$ with $\eta=L^{-k}$ are the conditions $\ell_k|\partial\phi|,\ell_k^2|\Delta\phi|,\ell_k^2|\alpha|<\delta$ in fine units (II.0
conventions); P5 (2.13) uses $\partial^\eta$ with the same $\eta$ on both layers, which we keep. P5 (1.19) prints the field condition as
$|h^2-1|<\delta_k^2/\sqrt{\nu_k}$ and (2.13) as $|h^2-1|<\frac9{16}\delta_k^2/\nu_k$; for real $h\in S^{N-1}$ both are void, and they matter only for the
complexified versions (Definition II.3.5), where we use $\delta^2/\nu$ (UNCERTAIN, minor; it enters only for $k>k_0$).

**Lemma II.3.3 (measurability and stencils).** Assume $L^{m_0}\ge42$ (row 5a). Each function of Definition II.3.2 is the indicator of a
Borel (indeed relatively open in the space of the variables it reads) set, and:
$\chi_k(\square)$ depends only on $\psi_k$ on the $k$-blocks of $\square^{\sim3}$; $\chi'^{(k)}(\square')$ only on $\theta$ on $T_{k+1}(\square')$ and $\psi_k$ on $T_k(\square')$;
$\chi'_{k+1}(\square')$ only on $(\psi_k,\theta)$ on $\square'^{\sim3}$; $\chi^{(k)}(\square')$ only on $\psi'_k$ on $T_k(\square')$; $\chi_{k+1}(\square')$ only on $\psi_{k+1}$ on $\square'^{\sim3}$.

*Proof.* $\mathcal D_{\mathbb R}(G)$ is open in the finite-dimensional space of real data (BG Theorem 5.2 (2)), and on it $\mathrm{bg}(G;\cdot)$ and the multiplier are
real analytic, hence continuous; every other condition is a strict inequality between continuous functions. So $\{\chi=1\}$ is open in
the data, which are linear functions (lifts) of the variables. Stencils: the data of $G_k(\square)=\mathbb B_k(\square^{\sim2})$ live on
$\Omega_1(\square^{\sim2})\cup C(\Omega_1(\square^{\sim2}))\subset\square^{\sim3}$ by Lemma II.2.3 (c); the same for $G_{k+1}(\square')$ and $\mathbb B_{k+1}(\square'^{\sim2})$. $\square$

*Faithfulness.* P5 (1.19) has no domain conjunct. Where the inequalities of item 1 hold for the true minimiser, the data lie in
$\tilde\Psi(\square^\sim;3\delta_k)$ by P1 Lemma 3.1 (SF §1.2 (D1), [review]), which is inside $\mathcal D_{\mathbb R}$ by (Λ17); so the conjunct changes nothing on the
configurations where P5's function is defined.

### II.3.2 The operator domain

**Definition II.3.4 (the domain (1.24)–(1.25), localized to a component).** Let $Z$ be a component of $Z_k$ with localized history
$\mathfrak a\in\mathfrak H_k(Z)$ (domains $\Omega_j$, $\Omega''_j$, $Z_j$, $j\le k$, of the lineage), let $\psi$ be the multiscale field ($\psi=\psi_j$ on
$\Lambda_j=(\Omega_j\setminus\Omega_{j+1})\cap T^{(j)}$) and $\psi'$ the fluctuation variables. For a set $Y$ of blocks of the generating set $\mathbb B_k$ and $\delta>0$,
$\tilde\Psi(Y;\delta)$ is the set of multiscale fields with $|\psi(y)-\psi(y')|<\delta$ for adjacent blocks $y,y'\in Y$ of layers $n,n'\in\{n,n-1\}$ and
$||\psi(y)|^2-1|<\delta$ for $y\in Y$ (BG (R1)–(R2); for $k\le k_0$ these are P7 p. 501's conditions "$|(\partial^1\psi_k)(b)|<\delta$, $||\psi_k(z)|-1|<\delta$", up to
the equivalent form of the second condition). Then $\chi^{\rm dom}_k(Z,\mathfrak a)(\psi,\psi'):=1$ iff
- (1.24) for $0\le j\le k-1$ and every $\square\in\pi_{j+1}$ with $\square\subset\Omega^\sim_{j+1}\cap Z_{j+1}\cap Z$: $\psi\in\tilde\Psi(\mathbb B_k\cap\square^\sim;3dL\delta_j)$; and for $1\le j\le k$
  and every $\square\in\pi_j$ with $\square\subset Z^c_j\cap(\Omega^\sim_{j+1})^c\cap Z$: $\psi_j\in\tilde\Psi(T_j(\square^\sim);3\delta_j)$ ($\Omega_{k+1}^\sim:=\varnothing$);
- (1.25) for $0\le j\le k-1$: $|\psi'_j(x)|<C_{\psi'}p_0(\beta_j)$ on $(\Omega_{j+1}\setminus\Omega''_{j+1})\cap T^{(j)}\cap Z$.

$C_{\psi'}$ is the constant of P5 (1.25) ("const. is built in a simple way from the constants $K_1$, $B_5$, etc.", p. 494 [checked]); it is an
output of the small-field step, chosen with row 11. *Index convention* (UNCERTAIN, minor; new erratum candidate N-II-3): P5 p. 492
puts the fluctuation variable $\psi'_j$ on $(\Omega_j\setminus\Omega''_j)\cap T^{(j)}$, while P6 p. 5 calls the fluctuation variable created at the step
$k\to k+1$ on the scale-$k$ points of $\Omega_{k+1}\setminus\Omega''_{k+1}$ "$\psi'_k$" (it replaces $\psi_k$ there, P5 (2.20)). We follow P6: $\psi'_j$ lives on
$(\Omega_{j+1}\setminus\Omega''_{j+1})\cap T^{(j)}$, and (1.25), (1.37) are read with this shift.

### II.3.3 Analyticity spaces

**Definition II.3.5 (P5 (1.36)–(1.37) [checked]).** (a) $\Delta^c_j(\square;1,\varepsilon)$, $\square\in\pi_j$: the set of complex fields $\psi_j$ on $T_j(\square^{\sim3})$ whose
lift $D^c$ lies in the open complex domain $\mathcal D(G_j(\square))$ of BG Theorem 5.2 (2) and whose complex small solution
$(\phi^c,\alpha^c)=\mathrm{bg}(G_j(\square);D^c)$ satisfies the inequalities of Definition II.3.1 with $\varepsilon$ in place of $\delta$ and with moduli of complex
numbers (P5 p. 497: "the obvious complexification of the conditions in (1.19), with $\varepsilon_j$ and $j$ instead of $k$ and $\delta_k$").
(b) $\Delta'^c_j(\square;(\frac34,\frac54),\varepsilon_{j-1})$, $\square\in\pi_j$: the complexification of item 3 of Definition II.3.2 at the step $j-1\to j$, with $\varepsilon_{j-1}$ in
place of $\delta_{j-1}$ ("modeled on (2.11)–(2.13)", P5 p. 497).
(c) For $X\in\mathcal D_k(\mathrm{mod}\,\Omega^c_k)$ (Definition I.2.15) and the domains of a history,
$$\Delta^c(X,\mathbb B_k;\{\Omega_j\}):=\bigcap_{j=1}^k\Big[\bigcap_{\square\subset[X\cap(\Omega^{\sim3}_{j+1})^c]\setminus(\Omega^c_j)^{\sim3}}\Delta^c_j(\square;1,\varepsilon_j)\ \cap\bigcap_{\square\subset X\cap\Omega^{\sim3}_j\cap(\Omega^c_j)^{\sim3}}\Delta'^c_j(\square;(\tfrac34,\tfrac54),\varepsilon_{j-1})\Big]\tag{1.36}$$
with $\Omega_{k+1}:=\varnothing$, and
$$\{\psi':\ |\psi'_j|<\varepsilon_{1,j}\ \text{on}\ X\cap(\Omega_{j+1}\setminus\Omega''_{j+1})\cap T^{(j)},\ 0\le j\le k-1\}.\tag{1.37}$$
(d) The **H7 domain** of a history at $X$ is the product of (1.36), (1.37) and $\{g:\|g\|_{\ell^1}<1\}$ (complex $g$).

These spaces are SF's $\Xi^c$-type spaces localized to cubes; by SF's ruling (iv) the small-field analyticity domains of Def-6 are the
data domains $\tilde\Psi^c_j(\mathbb B_j(X);K\varepsilon_j,K\varepsilon_j)$, and the two families are comparable by SF (Ξ1) and (D2) [review]. Def-7 uses (1.36)–(1.37) for
the boundary terms (D7), as P5 H7 does.

---

## II.4 LF-1: lower bounds for the multiscale action (P6 Proposition 3.1 for hard spins)

**Setting.** $G$ is a generating set at level $q$ with separation $\varrho\ge2dL$ (layers $\Lambda_n=\Omega_n\setminus\Omega_{n+1}$, $n\ge1$; layer $0$ is
$\mathbb T\setminus\Omega_1$), $a_n\in[\frac12,2]$ (`IsAdmissibleWeights`), $\mu\ge0$, $h\in\mathbb R^N$. $X\subset\mathbb T$ is a set of sites such that $X\cap\Lambda_n$ is a
union of $n$-blocks for every $n\ge1$. The variables are $\phi:X\to\mathbb R^N$, $\psi_n$ on the $n$-blocks of $\Lambda_n\cap X$ ($n\ge1$), and $\psi_0:=\phi$
on $X\setminus\Omega_1$ (P2's convention $a_0=\infty$). Define
$$A_G(X;\psi,\phi):=\tfrac12\sum_{n=1}^q\sum_{y\in T_n(\Lambda_n\cap X)}a_nL^{n(d-2)}|\psi_n(y)-(Q_n\phi)(y)|^2+\tfrac12\sum_{b\subset X}|\partial\phi(b)|^2+\tfrac\mu2\sum_{x\in X}|\phi(x)-h|^2,$$
the sum over bonds with both end points in $X$. P5 (1.5) is $\beta_qA^*_q(X,G;\psi,\phi)=\beta^{(q)}_0\big(A_G(X;\psi,\phi)+\frac14\sum_{b\in{\rm st}(X)}|\partial\phi(b)|^2\big)$ with
$\beta^{(q)}_0=\beta_qL^{-q(d-2)}$ and $\mu=\nu_qL^{-2q}$ (a site of $T_\eta$ carries $\eta^d$, $\partial^\eta=\eta^{-1}\partial$, $\eta=L^{-q}$; the boundary half-bonds are
$\ge0$). The pairs entering the bound:
- $P_n(X)$ ($n\ge1$): unordered pairs of nearest-neighbour $n$-blocks $y,y'$ of $\Lambda_n$ contained in $X$; $P_0(X)$: nearest-neighbour sites of
  $X\setminus\Omega_1$;
- $P^\times_{n+1}(X)$ ($0\le n<q$): pairs $(b_+,b_-)$ of nearest-neighbour $(n+1)$-blocks contained in $X$ with $b_+\subset\Omega_{n+1}$ and $b_-\cap\Omega_{n+1}=\varnothing$,
  and $(Q\psi_n)(b_-):=L^{-d}\sum_s\psi_n(s)$ over the $L^d$ $n$-blocks $s\subset b_-$ (for $n=0$, the sites of $b_-$).

The separation $\varrho\ge2dL$ gives: $b_+\subset\Lambda_{n+1}$ (a point of $b_+$ in $\Omega_{n+2}$ would be within $\ell^1$-distance $2dL^{n+1}$ of $b_-\subset\Omega^c_{n+1}$), and
for $n\ge1$ every $s\subset b_-$ lies in $\Lambda_n$ (a point of $b_-$ outside $\Omega_n$ would be within $2dL\cdot L^n$ of $b_+\subset\Omega_{n+1}$).

**Theorem II.4.1 (LF-1).** With $\gamma_0:=\frac1{28d}$:
(a) for arbitrary $\psi,\phi$,
$$A_G(X;\psi,\phi)\ge\gamma_0\Big\{\sum_{n=0}^q\frac{L^{n(d-2)}}2\sum_{\{y,y'\}\in P_n(X)}|\psi_n(y)-\psi_n(y')|^2+\sum_{n=0}^{q-1}\frac{L^{(n+1)(d-2)}}2\sum_{(b_+,b_-)\in P^\times_{n+1}(X)}|\psi_{n+1}(b_+)-(Q\psi_n)(b_-)|^2\Big\};$$
(b) if moreover $|\phi(x)|=1$ on $X$, $|h|=1$, $\mu L^{2q}\le1$ and $\psi_n(y)\ne0$,
$$A_G(X;\psi,\phi)\ge\gamma_0\sum_{n=0}^qL^{n(d-2)}\sum_{y\in T_n(\Lambda_n\cap X)}\Big[\tfrac12(|\psi_n(y)|-1)^2+\mu L^{2n}\big(1-h\cdot(\psi_n(y))_0\big)\Big],\qquad(u)_0:=u/|u|.$$
In P6's units, with $\beta_n=\beta^{(q)}_0L^{n(d-2)}$ and $\nu_n=\nu_qL^{-2(q-n)}=\mu L^{2n}$, these are P6 (3.5) and (3.6) for $q=k+1$, for every generating set (in
particular for the covered windows of Part III) and every field $\phi$, with no condition on the multiplier (at $\lambda=\infty$ the condition
"$|\alpha|<c_0(L^{j-1}\eta)^2$" of P6 Prop 3.1 is not needed).

**Lemma II.4.2 (adjacent block averages).** Let $B$ be a block of side $\ell$ in $\mathbb Z^d$ (or in a torus of side $\ge2\ell$), $B':=B+\ell e$, and
$\phi$ any field on $B\cup B'$. Then $|(Q\phi)(B)-(Q\phi)(B')|^2\le\ell^{2-d}\sum_{b\in E_e(B\cup B')}|\partial\phi(b)|^2$, where $E_e(B\cup B')$ is the set of bonds
$\{z,z+e\}$ with both end points in $B\cup B'$.

*Proof.* $(Q\phi)(B)-(Q\phi)(B')=\ell^{-d}\sum_{x\in B}\sum_{t=0}^{\ell-1}(\phi(x+te)-\phi(x+(t+1)e))$, a sum of $\ell^{d+1}$ bond differences. By Cauchy–Schwarz
its square is $\le\ell^{-2d}\ell^{d+1}\sum_{x,t}|\partial\phi(\{x+te,x+(t+1)e\})|^2$. A bond $\{z,z+e\}$ occurs for at most $\ell$ pairs $(x,t)$ (for each $t$ at most
one $x=z-te$). $\square$

**Lemma II.4.3 (hard-spin block bound).** If $|\phi|=1$ on a block $B$ of side $\ell$ (an $n$-block of the fine torus), then
$0\le1-|(Q\phi)(B)|^2=|B|^{-1}\sum_{x\in B}|\phi(x)-(Q\phi)(B)|^2\le\frac12\ell^{2-d}\sum_{b\subset B}|\partial\phi(b)|^2$.

*Proof.* The identity: $|B|^{-1}\sum|\phi-Q\phi|^2=|B|^{-1}\sum|\phi|^2-|Q\phi|^2$. The inequality is the landed sharp block Poincaré inequality
`blockPoincare_sharp` (`Green/BlockPoincareSharp.lean`: $\sum_x(\phi_x-P\phi_x)^2\le\frac12N^2\,$`innerEnergy` for the partition into aligned blocks of side
$N$), applied to each component of the field equal to $\phi$ on $B$ and to $0$ off $B$: the variances and inner energies of the other blocks vanish.
$\square$

*Proof of Theorem II.4.1.* Write $\Delta_n(y):=|\psi_n(y)-(Q_n\phi)(y)|^2$ ($n\ge1$; $\Delta_0:=0$ since $\psi_0=\phi$), $\mathrm{Bk}_n:=\sum_{y\in T_n(\Lambda_n\cap X)}L^{n(d-2)}\Delta_n(y)$,
and $E(S):=\sum|\partial\phi(b)|^2$ over the bonds with both end points in $S$. Since $a_n\ge\frac12$,
$$A_G\ge\tfrac14\textstyle\sum_n\mathrm{Bk}_n+\frac12E(X)+\frac\mu2\sum_X|\phi-h|^2.\tag{II.2}$$
*Intra-layer terms, $n\ge1$.* For $\{y,y'\}\in P_n(X)$ in direction $e$, $|\psi_n(y)-\psi_n(y')|^2\le3\Delta_n(y)+3\Delta_n(y')+3\ell_n^{2-d}\sum_{E_e}|\partial\phi|^2$ (Lemma II.4.2).
Each block is in $\le2d$ pairs, and each bond in direction $e$ lies in $E_e(B\cup B')$ for at most two pairs in direction $e$. With the weight
$\frac12\ell_n^{d-2}$: the intra-layer sum at level $n$ is $\le3d\,\mathrm{Bk}_n+3E(\Lambda_n\cap X)$. For $n=0$ it is $\frac12E(X\setminus\Omega_1)$.
*Cross terms.* For $(b_+,b_-)\in P^\times_{n+1}(X)$, since $(Q_{n+1}\phi)(b_-)=L^{-d}\sum_s(Q_n\phi)(s)$,
$$\psi_{n+1}(b_+)-(Q\psi_n)(b_-)=[\psi_{n+1}-Q_{n+1}\phi](b_+)+[(Q_{n+1}\phi)(b_+)-(Q_{n+1}\phi)(b_-)]+L^{-d}\textstyle\sum_s[(Q_n\phi)(s)-\psi_n(s)],$$
so its square is $\le3\Delta_{n+1}(b_+)+3\ell_{n+1}^{2-d}\sum_{E_e(b_+\cup b_-)}|\partial\phi|^2+3L^{-d}\sum_s\Delta_n(s)$. With the weight $\frac12\ell_{n+1}^{d-2}$ and
$\ell_{n+1}^{d-2}L^{-d}=\ell_n^{d-2}L^{-2}\le\frac14\ell_n^{d-2}$, summing over the cross pairs (each $b_\pm$ in $\le2d$ pairs, each bond in $\le2$ pairs of its
direction): the cross sum at level $n+1$ is $\le3d\,\mathrm{Bk}_{n+1}+\frac34d\,\mathrm{Bk}_n+3E(\cdot)$, the last over bonds of $X$.
*Totals.* $\mathrm{Bk}_n$ receives at most $3d+3d+\frac34d\le7d$; a bond receives at most $3$ (its own layer) $+3$ (cross pairs at its layer's scale)
$+3$ (cross pairs at the next scale) $=9$. Hence the bracket of (a) is $\le7d\sum_n\mathrm{Bk}_n+9E(X)\le28d\,A_G$ by (II.2). (a) follows.
*(b).* Fix $n\ge1$, $y$, $B=B_n(y)$, $u=(\psi_n(y))_0$, $\Delta=\Delta_n(y)$. Since $0\le|Q\phi|\le1$, $(1-|Q\phi|)^2\le1-|Q\phi|^2$, so by Lemma II.4.3
$(|\psi_n|-1)^2\le2\Delta+2(1-|Q\phi|^2)\le2\Delta+\ell_n^{2-d}E(B)$. Next $1-h\cdot u=\frac12|u-h|^2\le|u-Q\phi|^2+|Q\phi-h|^2$, with
$|Q\phi-h|^2\le|B|^{-1}\sum_B|\phi-h|^2$ (convexity) and $|u-Q\phi|^2\le2(|\psi_n|-1)^2+2\Delta\le6\Delta+2\ell_n^{2-d}E(B)$; and $\mu L^{nd}=\mu L^{2n}L^{n(d-2)}\le L^{n(d-2)}$. So
$$L^{n(d-2)}\big[\tfrac12(|\psi_n|-1)^2+\mu L^{2n}(1-h\cdot u)\big]\le7L^{n(d-2)}\Delta+\tfrac52E(B)+\mu\textstyle\sum_B|\phi-h|^2 .$$
For $n=0$ the bracket is $\mu(1-h\cdot\phi(x))=\frac\mu2|\phi(x)-h|^2$. Summing, the right side of (b) without $\gamma_0$ is $\le7\sum\mathrm{Bk}_n+\frac52E(X)+\mu\sum_X|\phi-h|^2\le28A_G$
by (II.2). $\square$

*Status:* proved here (P6 p. 17 calls these inequalities "very simple" and gives no proof; ER-030, ER-094; ARCH LF-1 had a sketch).
P6's remark that $\gamma_0=1/(7d+4)$ is attainable is not needed. LF-1 holds for every field $\phi$, so it applies to the local
backgrounds of D-II.1 as well as to P6's.

---

## II.5 Operators, Lemma F, exponents, combinatoric factors, budget

### II.5.1 Variables and reference measures

**Definition II.5.1 (variables of a localized history).** Let $Z$ be a component of $Z^{\rm pre}_k$ or of $Z_k$, $k\ge1$, and $\mathfrak a\in\mathfrak H_k(Z)$ its localized
history, with domains $\Omega_j,\Omega''_j$ ($1\le j\le k$) of the lineage (overwritten history, Definition I.4.4; all sets are intersected with $Z$ as fine sets).
- *Output variables:* $\psi_k(y)\in\mathbb R^N$ for $y\in T^{(k)}\cap V_Z$, $V_Z:=(Z^{\approx})^{\sim}$ (scale $k$).
- *Internal variables* $I(Z,\mathfrak a)$: for $0\le j\le k-1$, the *large-field variables* $\psi_j(y)$, $y\in T^{(j)}\cap\Omega^c_{j+1}\cap Z$, and the *fluctuation variables*
  $\psi'_j(y)$, $y\in T^{(j)}\cap(\Omega_{j+1}\setminus\Omega''_{j+1})\cap Z$ (index convention of §II.3.2). The large-field variables of scale $0$ are spins,
  $\psi_0(y)\in S^{N-1}$; all others take values in $\mathbb R^N$ (complex values only in analytic extensions).
- *Reference measure* $\mu_{Z,\mathfrak a}$: the product of the a priori measure of `Model/SphereMeasure.lean` (normalized surface measure on $S^{N-1}$, the
  frozen `aprioriMeasure` per site) for the spins, and Lebesgue measure $d^N\psi$ for the other internal variables. (The fluctuation variables of the
  step $0\to1$ are $\mathbb R^N$-valued through the representation $\int_{\phi^\perp}f\,d^{N-1}\xi=(2\pi)^{-1/2}\int_{\mathbb R^N}f(P^\perp_\phi u)e^{-\frac12(\phi\cdot u)^2}du$ of ARCH LF-6
  (iv); this convention is fixed in §II.7.)
- The *multiscale field* $\psi$ of the history ($\psi=\psi_j$ on $\Lambda_j\cap T^{(j)}$, P5 p. 492) is a function of the internal and output variables, since
  $\Lambda_j\subset\Omega^c_{j+1}$ for $j<k$ and $\Lambda_k=\Omega_k\cap T^{(k)}$.

All internal variables are located in $Z$: $\Omega^c_{j+1}\cup(\Omega_{j+1}\setminus\Omega''_{j+1})\subset Z_{j+1}$ (Lemma I.3.5 (e)), and $Z_{j+1}\cap Z$ is the lineage of $Z$
(Lemma I.4.3 (c)). For a component $Z'$ of $Z^{\rm pre}_{k+1}$ with ancestors $\mathrm{Anc}_k(Z')$ (Definition I.4.2),
$$I(Z',\mathfrak a)=I^{\rm new}_k(Z')\ \sqcup\bigsqcup_{Y\in\mathrm{Anc}_k(Z')}I(Y,\mathfrak a|_Y),\qquad I^{\rm new}_k(Z'):=\{\psi_k\text{ on }T^{(k)}\cap\Omega^c_{k+1}\cap Z'\}\sqcup\{\psi'_k\text{ on }T^{(k)}\cap(\Omega_{k+1}\setminus\Omega''_{k+1})\cap Z'\},\tag{II.3}$$
because $Z_k\cap Z'=\bigsqcup_{Y}Y$ and $\Omega^c_{j+1}\subset Z_{j+1}\subset Z_k$ for $j<k$. The output variables of every ancestor are new internal variables:
$V_Y\subset U^{\sim}_k\subset\Omega^c_{k+1}$ as fine sets (Lemma I.3.5 (a), (i)) and $V_Y\subset V_{Z'}$ (Lemma I.3.15), so $T^{(k)}\cap V_Y\subset T^{(k)}\cap\Omega^c_{k+1}\cap Z'$.

### II.5.2 Kernels, operators, and the bound (1.26)

**Definition II.5.2 (large-field operators).** A *large-field kernel* at $(Z,\mathfrak a)$ is a pair $(K,b)$: $K\ge0$ a Borel function of the output and
internal variables, independent of $g$; $b$ a function of the output and internal variables and of $(h,g)$, $\|g\|_{\ell^1}<1$, analytic in $g$ and real for real
arguments. Its operator is
$$\mathbb T F(\psi_k):=\int K(\psi_k,x)\,e^{b(\psi_k,x;h,g)}\,F(\psi_k,x)\,\mu_{Z,\mathfrak a}(dx)$$
on Borel functions $F$ of the output, internal and other (parameter) variables for which the integral converges absolutely. The **bound (1.26)**
with exponent $\kappa$ (P5 (1.26) [checked], in the form with the modulus inside, which is the form that composes) is
$$\int d\psi_k\!\restriction_{T^{(k)}\cap Z}\int\mu_{Z,\mathfrak a}(dx)\,K\,e^{{\rm Re}\,b}\,|F|\ \le\ e^{-\kappa}\ \sup\big\{\chi^{\rm dom}_k(Z,\mathfrak a)|F|\big\}\qquad\text{for all Borel }F\text{ and all }\|g\|_{\ell^1}<1,\tag{1.26}$$
the supremum over all variables. For real $g$ the kernel $Ke^b$ is non-negative, as P5 H5 requires; for complex $g$ the bound is the sup bound on
the whole polydisc (OBSERVABLES §4.2 (4)).

**Lemma II.5.3 (products and compositions).** (a) Operators at distinct components of $Z_k$ act on disjoint sets of internal variables and have
kernels depending on disjoint sets of output variables and of $g$-values (once Lemma II.5.9 (a) is proved); their product is the operator
of the product kernel, and they commute (Fubini–Tonelli). (b) If $\mathbb T_1$ at level $k+1$ has internal variables $I^{\rm new}$ containing the output variables
of operators $\mathbb T_Y$ at level $k$ with disjoint internal variables, then $\mathbb T_1\circ\bigotimes_Y\mathbb T_Y$ is the operator with kernel $K_1e^{b_1}\prod_YK_Ye^{b_Y}$ on $I^{\rm new}\sqcup\bigsqcup_YI_Y$.

*Proof.* Tonelli for the non-negative integrands $K\,e^{{\rm Re}\,b}|F|$, then Fubini. $\square$

### II.5.3 The multiscale action and the quiet step kernel

**Definition II.5.4 (main action of the new large-field region).** At the step $k\to k+1$, for a component $Z'$ of $Z^{\rm pre}_{k+1}$ put
$X_{Z'}:=Z^c_k\cap Z'$ (fine sites). With the history's generating set $\mathbb B_{k+1}$ (layers $\Omega_1\supset\dots\supset\Omega_{k+1}$), the multiscale field $\psi$
(on $X_{Z'}$ it consists of $\psi_k$ on $\Lambda_k$ and $\psi_{k+1}$ on $\Lambda_{k+1}$, since $Z^c_k\subset\Omega_k$), the weights $a_n$ and $\phi=\phi^{\rm loc}_{k+1}$ on the piece of $Z'$
(Definition II.2.7 (iv); it is defined on $X^{+1}_{Z'}$ because $Z^c_k\subset W_k$ and $Z'\subset U_{Z'}$),
$$\mathcal A_{k+1}(Z';\psi):=\beta_{k+1}A^*_{k+1}(X_{Z'},\mathbb B_{k+1};\psi,\phi):=\beta^{(k+1)}_0\Big(A_{\mathbb B_{k+1}}(X_{Z'};\psi,\phi)+\tfrac14\sum_{b\in{\rm st}(X_{Z'})}|\partial\phi(b)|^2\Big),$$
with $A_G$ of §II.4 (mass $\mu=\nu_{k+1}L^{-2(k+1)}$, the $\nu$-term being present for every $k$, P5 p. 490: "we keep it in the main action") and
$\beta^{(k+1)}_0=\beta_{k+1}L^{-(k+1)(d-2)}$. This is P6 (3.2)'s $\beta_{k+1}A^*_{k+1}(Z^c_k\cap Z_{k+1},\mathbb B_{k+1};\psi,\phi_{k+1}(\mathbb B_{k+1}(\partial\Omega_{k+1});\tilde\psi))$ with the
local background (D-II.1).

**Definition II.5.5 (quiet step).** The step $k\to k+1$ is *quiet in* $Z'$ if $\mathcal N_{k+1}\cap Z'=\varnothing$. Then the seed data inside $Z'$ have
$\mathsf P'=\mathsf Q'=\mathsf R'=\mathsf S'=\varnothing$, so by Lemma I.3.9 and Lemma I.3.5 (h) applied to them, $\Omega'_{k+1}\cap Z'=\Omega_{k+1}\cap Z'=\Omega''_{k+1}\cap Z'$.

**Definition II.5.6 (quiet step kernel; P5 (2.47) and P6 (3.2) with $\mathsf P=\mathsf Q=\mathsf R=\mathsf S=\varnothing$).** For a step quiet in $Z'$, with
$\theta:=z_{k+1}\psi_{k+1}$ and the Gaussian kernel of $T^{(k)}$ per $(k+1)$-block (P1 (1.11); normalization as in P5 (2.48) [checked], whose constant
$\frac12NL^{-d}\log(\beta_kaL^{d-2}/2\pi)|\Omega_{k+1}|$ is its logarithm)
$$t_k(\vartheta,w):=\Big(\frac{\beta_kaL^{d-2}}{2\pi}\Big)^{N/2}\exp\Big(-\frac{\beta_kaL^{d-2}}2|\vartheta-w|^2\Big),$$
define
$$\begin{aligned}K^{\rm q}_k(Z')&:=\prod_{y\in T^{(k+1)}\cap\Omega^c_{k+1}\cap Z'}z_{k+1}^N\,t_k\big(\theta(y),(Q\psi_k)(y)\big)\ \cdot\ \chi_k\big(Z^c_k\cap Z'\cap(\Omega^{\sim3}_{k+1})^c\big)\ \chi'_{k+1}\big(\Omega^{\sim3}_{k+1}\cap\Omega^c_{k+1}\cap Z'\big)\\
&\quad\cdot\chi'_{k+1}\big(\Omega_{k+1}\cap(\Omega^c_{k+1})^{\sim3}\cap Z'\big)\ \chi_{k+1}\big(\Omega^{\sim-3}_{k+1}\cap Z'\big)\ \cdot\ \chi^{\rm new}_k(Z')\ \mathbf 1[\phi^{\rm loc}\text{-data}\in\mathcal D_{\mathbb R}]\ \cdot\ e^{-\mathcal A_{k+1}(Z';\psi)},\end{aligned}$$
products over $\pi_k$-cubes (first $\chi_k$) and $\pi_{k+1}$-cubes (the others); $\chi^{\rm new}_k(Z')$ is the indicator of the conditions of Definition II.3.4 that are
new at level $k+1$ (the cubes of scale $k$ and $k+1$ in $Z'$ listed in the proof of Lemma II.5.13); $\Omega^{\sim-3}=((\Omega^c)^{\sim3})^c$ (P6 p. 4). Its internal
variables are $I^{\rm new}_k(Z')$, which here consist of $\psi_k$ on $T^{(k)}\cap\Omega^c_{k+1}\cap Z'$ only (no fluctuation variables, since $\Omega_{k+1}=\Omega''_{k+1}$ on $Z'$).

*Derivation from the sources.* P5 (2.47) [checked] with $\mathsf P=\mathsf Q=\mathsf R=\varnothing$ and $\Omega'=\Omega=\Omega''$ on $Z'$: $T^{(k)}(\Omega^c_{k+1})$ remains; $\chi_k(Z^c_k\cap(\Omega^{\sim3}_{k+1})^c)$
remains; $\chi'^{(k)c}(\mathsf P)=1$ and $\chi'^{(k)}(\mathsf P^c\cap\Omega'\cap\Omega^c)$ is an empty product; $\chi'^c_{k+1}(\mathsf Q)=1$ and $\chi'_{k+1}(\mathsf Q^c\cap\Omega^{\sim3}\cap\Omega''^c)=\chi'_{k+1}(\Omega^{\sim3}\cap\Omega^c)$; the
Gaussian integral over $\Omega\cap\Omega''^c$, the functions $\chi_k(\mathsf Q\cup\dots)$, $\chi'^{(k)}((\mathsf Q\cup\dots)\cap\Omega)$ and $\chi^{(k)}$ are empty. P6 (3.2) [page image p. 16
checked] with $\mathsf S=\varnothing$: $\chi'_{k+1}(\Omega''\cap((\Omega''^c)^{\sim3}\,\square\,\mathsf S))$, $\chi^c_{k+1}(\mathsf S)=1$, $\chi_{k+1}(\Omega''^{\sim-3}\cap\mathsf S^c\cap Z_{k+1})$, the main action and the vacuum
constants. P6 (3.2) prints "$\cap\,\mathsf S_{k+1}$" at the place marked $\square$, while P6 p. 4 says the functions $\chi'_{k+1}(\square')$ left on $\Omega''_{k+1}$ "are the ones with
$\square'\subset(\Omega''^c_{k+1})^{\sim3}\cup\mathsf S_{k+1}$"; we read $\cup$ (new erratum candidate N-II-1; the remark below shows that the literal reading cannot be
intended). The vacuum constants
$-E_kL^d|Z^c_k\setminus\Omega_{k+1}|-E''_kL^d|\Omega_{k+1}\setminus\Omega''_{k+1}|-E'''_kL^d|\Omega''_{k+1}\cap Z_{k+1}|$ of P6 (3.2), and the factor $\exp\mathcal B^{(k)}(Z^c_k\cap Z_{k+1})$ of P6 (3.3),
are put into the step boundary factor $b_k$ (P7 p. 499: "The constants in the exponentials are unimportant, so we separate them … and
combine them with corresponding boundary terms"). The indicators $\chi^{\rm new}_k$ and $\mathbf 1[\cdot\in\mathcal D_{\mathbb R}]$ equal $1$ wherever the other characteristic
functions do (P5 (2.7), (2.10), P1 Lemma 3.1; Remark II.2.8); they make the support property and measurability hold by definition.

*Remark (the reading of P6 (3.2)).* With the literal "$\cap\,\mathsf S$", the cubes of $\Omega''_{k+1}\cap(\Omega''^c_{k+1})^{\sim3}$ would carry no characteristic function in
a quiet step, and $\psi_{k+1}$ there would be unconstrained, so the integration in (1.26) would diverge; the reading "$\cup$" of P6 p. 4 is the
consistent one.

### II.5.4 Step data and kept data

**Definition II.5.7 (data of a representation, per localized history prefix).** Let $Z'$ be a component of $Z^{\rm pre}_{k+1}$ ($0\le k$) with localized
history prefix $\mathfrak a$ (up to and including the step record of the step $k\to k+1$).
- (S0) *Step boundary factor* $b_k(Z',\mathfrak a)$: a function of $\psi_{k+1}$ on $T^{(k+1)}\cap V_{Z'}$, of the internal variables $I(Z',\mathfrak a)$ and of $(h,g|_{V_{Z'}})$; real for
  real arguments; analytic on the H7 domain (Definition II.3.5 (d)) localized to $V_{Z'}$, jointly in $g$; bounded there by
  $|b_k|\le(C_b\log\beta_k+C_bB_0)\,|Z^c_k\cap Z'|_{k+1}$; covariant: $b_k(R\psi,Rx;Rh,Rg)=b_k(\psi,x;h,g)$ for $R\in O(N)$ and invariant under the Euclidean
  symmetries of the torus preserving $\pi_{k+1}$ applied to all variables and the history. ($C_b$: an output constant of the small-field step,
  P6 (2.33) "const."; row 11. It contains the vacuum constants of P6 (3.2), the term $\exp\mathcal B^{(k)}(Z^c_k\cap Z_{k+1})$ of P6 (3.3), and, by D-II.1, the
  correction terms of the background change whose localization domains lie in $Z_{k+1}$.)
- (S1) *Step kernel.* If the step is quiet in $Z'$: $K_k(Z',\mathfrak a):=K^{\rm q}_k(Z')$. Otherwise $K_k(Z',\mathfrak a)$ is a datum: a non-negative Borel function of
  $\psi_{k+1}$ on $T^{(k+1)}\cap V_{Z'}$ and of the variables $I^{\rm new}_k(Z')$ and $\psi_k$ on $T^{(k)}\cap Z_k\cap Z'$, independent of $g$, vanishing unless
  $\chi^{\rm new}_k(Z')=1$, O(N)- and Euclid-invariant as in (S0).
- (S2) *One-step bound.* For all values of $\psi_{k+1}$ on $V_{Z'}\setminus Z'$, of $\psi_k$ on $T^{(k)}\cap Z_k\cap Z'$, of $h$, and all $\|g\|_{\ell^1}<1$:
  $$\int d\psi_{k+1}\!\restriction_{T^{(k+1)}\cap Z'}\int d\psi_k\!\restriction_{T^{(k)}\cap Z^c_k\cap\Omega^c_{k+1}\cap Z'}\int d\psi'_k\ K_k(Z',\mathfrak a)\,e^{{\rm Re}\,b_k(Z',\mathfrak a)}\ \le\ e^{-\kappa^{(k)}(Z',\mathfrak a)},$$
  with $\kappa^{(k)}$ of Definition II.5.10. For quiet steps this is Lemma II.5.14; for the others it is a requirement (P6 (3.4)–(3.9)).
- (S3) *Kept data* (scale $k\le k_0$, $Z$ a ripe component of $Z^{\rm pre}_k$ that is kept): a label $\varkappa$ from a finite set $\mathfrak K(Z,\mathfrak a)$, numbers
  $C_{\rm dec}(\varkappa)\ge1$ with $\sum_{\varkappa\in\mathfrak K}C_{\rm dec}(\varkappa)^{-1}\le1$, a *kept exponent* $\gamma(\varkappa)$ with $\gamma(\varkappa)-\log C_{\rm dec}(\varkappa)\ge A'_3\hat\lambda_k^{p_R}$, and a
  large-field kernel $(K'',b'')$ at $(Z,\mathfrak a)$ (same output and internal variables and reference measure as $\mathbb T^{\rm pre}_k(Z,\mathfrak a)$), with $K''$ vanishing
  unless $\chi^{\rm dom}_k(Z,\mathfrak a)=1$, $b''$ as in (S0) with the bound replaced by a bound uniform on the H7 domain, invariance as in (S0), and the bound
  (1.26) with exponent $\kappa''_k(Z,\mathfrak a,\varkappa):=\kappa_k(Z,\mathfrak a)-C_R\hat\lambda_k^{2d+1}+\gamma(\varkappa)$.
- (S4) *Locality.* All these data depend on the history only through the localized history prefix of $Z'$ (resp. $Z$); in particular they are
  the same for two global histories with the same localized prefix (P5 p. 493: the multi-index "is determined completely by its restrictions";
  P6 p. 15).

(S3) is ARCH's kept exponent (§3.4, R3-08) with the kept operator and its decomposition data left to LF-4 (D-II.2). P7's two kinds K1, K2 are
instances; Part III must show that P7's construction yields kernels of this form, in particular that the $g$-dependence of the kept operator
sits in a factor $e^{b''}$ with $K''\ge0$ independent of $g$ and that the coset average (M4) is taken on the full integrand so that $b''$ is jointly
covariant (OBSERVABLES §4.2 (2); open item O-II-5).

### II.5.5 The localized operators and Lemma F

**Definition II.5.8 (localized operators, by recursion along the lineage; P6 (3.3), P5 (1.23)).** Given the data of Definition II.5.7:
- for a component $Z'$ of $Z^{\rm pre}_{k+1}$ ($k\ge0$) and $\mathfrak a\in\mathfrak H_{k+1}(Z')$ (pre-$R$):
  $$\mathbb T^{\rm pre}_{k+1}(Z',\mathfrak a):=\big(K_k(Z',\mathfrak a),b_k(Z',\mathfrak a)\big)\circ\bigotimes_{Y\in\mathrm{Anc}_k(Z')}\mathbb T_k(Y,\mathfrak a|_Y)$$
  in the sense of Lemma II.5.3 (b) (for $k=0$ there are no ancestors);
- for a component $Z$ of $Z_k$: $\mathbb T_k(Z,\mathfrak a):=\mathbb T^{\rm pre}_k(Z,\mathfrak a)$ if $Z$ is not ripe or $k>k_0$, and $\mathbb T_k(Z,\mathfrak a):=$ the operator of the kept kernel
  $(K'',b'')$ of (S3) if $Z$ is kept with label $\varkappa$ (removed components have no operator; they are not in any lineage, Lemma I.4.3);
- for a global history $\mathbb A$: $\mathbb T_k(Z_k,\mathbb A):=\bigotimes_{Z}\mathbb T_k(Z,\mathbb A\cap Z)$ over the components of $Z_k$ (P5 (1.21)–(1.22)).

By (II.3) and Lemma II.5.3, $\mathbb T^{\rm pre}_{k+1}(Z',\mathfrak a)$ is a large-field kernel at $(Z',\mathfrak a)$ with kernel
$K_k\prod_YK_Y$ and exponent $b_k+\sum_Yb_Y$, where $(K_Y,b_Y)$ are the kernels of the ancestors' operators.

**Lemma II.5.9 (Lemma F for the representation: support, factorization, levels, domain).** Assume (RH) and $L^{m_0}\ge42$. For every
$k\ge1$, every component $Z$ of $Z^{\rm pre}_k$ or $Z_k$ and every $\mathfrak a$:
(a) (support; P5 H5, P6 p. 16) the kernel of $\mathbb T_k(Z,\mathfrak a)$ depends only on $\psi_k$ on $T^{(k)}\cap V_Z$, on the internal variables (all located in $Z$),
and on $g|_{V_Z}$ and $h$;
(b) (factorization; P5 (1.22)) for distinct components $Z^{(1)},Z^{(2)}$ the sets $V_{Z^{(i)}}$ are disjoint, the two operators act on disjoint variables and
commute, and $\mathbb T_k(Z_k,\mathbb A)$ is their product;
(c) (levels; P5 (1.23)) if $Z'$ is not kept at $k+1$, $\mathbb T_{k+1}(Z')=(K_k,b_k)\circ\bigotimes_Y\mathbb T_k(Y)$;
(d) (domain; P5 (1.24)–(1.25)) the kernel vanishes unless $\chi^{\rm dom}_k(Z,\mathfrak a)=1$.

*Proof.* Induction on $k$. *Quiet kernels.* By Lemma II.3.3 each characteristic function of Definition II.5.6 reads its variables within three cubes
of a cube contained in $Z'$ ($\pi_k$-cubes of $Z^c_k\cap Z'$, $\pi_{k+1}$-cubes of $Z'$), hence within $Z'^{\sim3}\subset V_{Z'}=Z'^{\sim([R_k]+2)}$ (scale $k+1$; $[R_k]\ge1$ by (RH)).
The Gaussian factors live on blocks of $\Omega^c_{k+1}\cap Z'$. The main action lives on $X_{Z'}^{+1}$ and its background $\phi^{\rm loc}$ on the piece of $Z'$ reads data
in $V_{Z'}$ only (Lemma II.2.5 (b), Lemma II.2.6). *Data kernels and boundary factors:* (S0), (S1), (S3). *Ancestors:* $V_Y\subset V_{Z'}$ (Lemma I.3.15) and
their internal variables lie in $Y\subset Z'$. This gives (a). (b): $V$'s of distinct components are at index distance $\ge L+7$ (Lemma I.2.13), and
internal variables lie in the components; then Lemma II.5.3 (a). (c) is the definition. (d): $\chi^{\rm dom}_{k+1}(Z')=\chi^{\rm new}_k(Z')\prod_Y\chi^{\rm dom}_k(Y)$
(proof of Lemma II.5.13), and each factor is present in the kernel ((S1), (S3), and the induction hypothesis). $\square$

*What remains of ARCH's Lemma F, and where it is proved (open item O-2′, replacing Part I's O-2).* Lemma II.5.9 is the structural half. The
analytic half is the statement that the density produced by $S^{(k)}T^{(k)}$ from a representation of $\rho_k$ has a representation of the form
(D1) with these operators: the main action of P6 (2.11)–(2.17) on $Z^c_k\cap Z_{k+1}$, with P6's background $\phi_{k+1}(\mathbb B_{k+1}(\partial\Omega_{k+1});\tilde\psi)$, equals
$\sum_{Z'}\mathcal A_{k+1}(Z';\psi)$ plus terms $\Delta(Y)$, $Y\in\mathcal D_{k+1}(\mathrm{mod}\,\Omega^c_{k+1})$, each depending only on the variables in $Y$, analytic on the H7 domain and
bounded by $\varepsilon_Fe^{-\kappa d_{k+1}(Y\,\mathrm{mod}\,\Omega^c_{k+1})}$ with $\varepsilon_F\to0$ as $\hat\lambda_0\to\infty$; terms with $Y\subset Z_{k+1}$ go into $b_k$, the others into $\mathcal B^{(k+1)}$.
*Route.* $\mathbb B^{\rm loc}\prec\mathbb B_{k+1}(\partial\Omega_{k+1})$ (Lemma II.2.3 (b) layer by layer), so by I-2 (BG Theorem 6.1 (ii), landed `isEL_compose`)
$\phi(\mathbb B_{k+1}(\partial\Omega_{k+1});\tilde\psi)=\phi(\mathbb B^{\rm loc};\psi(\mathbb B^{\rm loc},\mathbb B_{k+1}(\partial\Omega_{k+1});\tilde\psi))=\phi^{\rm loc}+\delta\phi$, where the data change
$\psi(\mathbb B^{\rm loc},\mathbb B_{k+1}(\partial\Omega_{k+1});\tilde\psi)-\tilde\psi$ vanishes on the sets $E_{Z'}=Z'^{\sim[R_k]}$ (Lemma II.2.5 (c)), i.e. at distance $\ge[R_k]$ cubes of side
$ML^{k+1}$ from $X_{Z'}$. This is P6 (2.12)–(2.13) and (2.16) verbatim ("the configuration $\delta\psi''$ … is equal to $0$ on the domain …, hence this
function satisfies the bounds (2.13)": $|\delta\phi|<K_3K_4\delta\exp(-\frac14\gamma_0(2MR_k-M-2M_1))<\exp(-R_k)$). The expansion of the action
(P5 (2.23)) and the localization expansion of the remainder with decoupling parameters (LOC I-4b (v), I-5, Lemma AE: landed
`abstract_expansion`) are the same as for P6 (2.16)–(2.17); this is part of LF-3's proof (Part IV.1) and is conditional on LOC's open items
(NC, GM2). LF-astra (F.2)–(F.4) gives the same structure with its own local action.

*Remark (LF-astra's alternative).* Replacing $e^{-\mathcal A_{k+1}(Z';\psi)}$ in Definition II.5.6 by $e^{-\mathcal A^{\rm loc}_q(X_{Z'})}$ of LF-astra (F.7) changes nothing in Part II
except that the background is no longer a minimiser (its Euler–Lagrange residual is bounded by LF-astra (F.8)); LF-1 still applies (it holds for
every field). D-II.1 prefers the minimiser for the reasons given in §II.0.

**Lemma II.5.10 (invariance; P5 H5).** The quiet kernels are invariant under $R\in O(N)$ acting on all spin-valued variables, the data and
$h$ (and $g$ in $b$), and under the Euclidean symmetries $r$ of the torus that preserve $\pi_{k+1}$ (translations by multiples of $ML^{k+1}$, coordinate
permutations and reflections mapping cubes to cubes), applied to the variables and to the history. Hence so are all localized operators.

*Proof.* The region rules of Definition I.3.1 are built from cubes, neighbourhoods and openings that commute with $r$; the backgrounds are
equivariant: for real data the minimiser of the $O(N)$-invariant problem (1.2) at rotated data is the rotated minimiser (uniqueness, BG
Theorem 7.1), and similarly under $r$ (the generating sets are mapped to the generating sets of the image history). The characteristic
functions, the Gaussian $t_k$ and the action are invariant. Data: (S0), (S1), (S3). $\square$

### II.5.6 Exponents, combinatoric factors, budget

**Definition II.5.11 (exponents, combinatoric factors, budget; P6 (3.9)–(3.11) [checked], ARCH §3.4).** For the step $k\to k+1$ and a component $Z'$
of $Z^{\rm pre}_{k+1}$ with localized history $\mathfrak a$:
- $\kappa^{(k)}(Z',\mathfrak a):=A_3(\log\beta_k)^{2p_0}\,|\mathcal N_{k+1}\cap Z'|_\#-(c_1\log\beta_k+c_2)\,|Z^c_k\cap Z'|_{k+1}$, with $|\cdot|_\#$ the number of $\pi_{k+1}$-cubes and $A_3$ of P6 (3.9)
  ($A_3=\min\{\frac{8\gamma_0}{6^d(9K_1)^2}A_0^2,\frac18A_1^2\}$, $p_1=p_0$; row 9). P6 (3.9) has $|\mathsf P|+|\mathsf Q|+|\mathsf R|+|\mathsf S|\ge|\mathcal N_{k+1}|$ in place of $|\mathcal N_{k+1}|$, so P6's bound implies
  (S2) with this $\kappa^{(k)}$; $c_1,c_2$ are P6's "$O(1)$" and "const." enlarged (row 14), and they absorb the bound of (S0).
- $\kappa_{k+1}(Z',\mathfrak a):=\sum_{Y\in\mathrm{Anc}_k(Z')}\kappa_k(Y,\mathfrak a|_Y)+\kappa^{(k)}(Z',\mathfrak a)$ (P6 (3.10)); for a kept component $\kappa_k(Z,\mathfrak a''):=\kappa''_k(Z,\mathfrak a,\varkappa)$ of (S3).
- $\log C_{k+1}(Z',\mathfrak a):=\sum_Y\log C_k(Y,\mathfrak a|_Y)+|Z_k\cap Z'|_{\#k}+\frac54|Z^c_k\cap Z'|_{\#k}$ (P6 (3.11); $|\cdot|_{\#k}$ counts $\pi_k$-cubes, i.e. $M^{-d}|\cdot|_k$);
  for a kept component $\log C_k(Z,\mathfrak a''):=\log C_k(Z,\mathfrak a)+\log C_{\rm dec}(\varkappa)$. Empty sums are $0$ (so at $k=0$ the old terms vanish).
- $G_k(Z,\mathfrak a):=\kappa_k(Z,\mathfrak a)-\log C_k(Z,\mathfrak a)-H_k|Z|_k$, and $G^{\rm pre}_k$ the same for the pre-$R$ components (ARCH §3.4; P5 (1.30)).

All are functions of the localized history and of the running constants up to scale $k+1$ (causal).

**Lemma II.5.12 (Lemma B: the budget recursion; LF-2's hypothesis (B)).** Assume Lemma II.1.2's hypotheses and that $\hat\lambda_k$ satisfies (Λ15) and
(Λ16). For every component $Z'$ of $Z^{\rm pre}_{k+1}$ (the hull closure included) and every $\mathfrak a$,
$$G^{\rm pre}_{k+1}(Z',\mathfrak a)\ \ge\ \sum_{Y\in\mathrm{Anc}_k(Z')}G_k(Y,\mathfrak a|_Y)+g_k\,|\mathcal N_{k+1}\cap Z'|_\#-c_v\,\hat\lambda_{k+1}|Z'|_\#,\qquad c_v:=M^d(H_0+c_1+3).$$

*Proof.* Let $n_1:=|Z_k\cap Z'|_{\#k}$, $n_2:=|Z^c_k\cap Z'|_{\#k}$. Volumes: $\sum_Y|Y|_k=M^dn_1$, $|Z_k\cap Z'|_{k+1}=L^{-d}M^dn_1$, $|Z^c_k\cap Z'|_{k+1}=L^{-d}M^dn_2$. By the
definitions,
$$G^{\rm pre}_{k+1}-\sum_YG_k(Y)=A_3(\log\beta_k)^{2p_0}|\mathcal N_{k+1}\cap Z'|_\#+n_1\big[M^d(H_k-L^{-d}H_{k+1})-1\big]-n_2\big[(c_1\log\beta_k+c_2+H_{k+1})L^{-d}M^d+\tfrac54\big].$$
*Gain:* $A_3(\log\beta_k)^{2p_0}\ge g_k$ by Lemma II.1.2 (d) and (Λ15). *Old volume:* by Lemma II.1.2 (b), (e),
$H_k-L^{-d}H_{k+1}\ge H_0[(1-L^{-d})\log\beta_k-L^{-d}((d-2)\log L+2\epsilon)]\ge H_0[(1-L^{-d})(\hat\lambda_k-3)-L^{-d}((d-2)\log L+1)]\ge1\ge M^{-d}$ by (Λ16), so the
$n_1$-bracket is $\ge0$ (P6 p. 20 [checked]: "$M^{-d}|Z_k|+H_{k+1}L^{-d}|Z_k|\le H_k|Z_k|$"; the surplus is discarded). *New volume:* $\log\beta_k\le\hat\lambda_k\le\hat\lambda_{k+1}$,
$\log\beta_{k+1}\le\hat\lambda_{k+1}$, $\frac54L^dM^{-d}\le2$ (as $M\ge L$) and $c_2+2\le\hat\lambda_{k+1}$ by (Λ16); so the $n_2$-term is at least
$-|Z^c_k\cap Z'|_{k+1}(c_1+H_0+3)\hat\lambda_{k+1}\ge-c_v\hat\lambda_{k+1}|Z'|_\#$, since $|Z^c_k\cap Z'|_{k+1}\le M^d|Z'|_\#$. Every cube of $Z^c_k\cap Z'$ is counted, in particular the cubes
added by the hull closure (they lie in $Z^c_k$ because $Z_k\subset Z^{(0)}_{k+1}$ as fine sets, Lemma I.4.3 (b)). $\square$

*Status:* proved here, from the definitions; the operator bound that makes $\kappa^{(k)}$ meaningful is (S2). This closes the first half of Part I's
O-6 (hull cubes are new volume charged at P6's rate; for quiet steps the bound covers them by Lemma II.5.14, for non-quiet steps P6 (3.4)
integrates over all of $Z^c_k\cap Z_{k+1}$, hull cubes included, since they lie in $\Omega''_{k+1}$). The base $k=0$ (LF-6) must supply (S2) with this
$\kappa^{(0)}$; that is §II.7.

**Lemma II.5.13 (composition of bounds; (D5) for a step).** If every ancestor operator $\mathbb T_k(Y,\mathfrak a|_Y)$ satisfies (1.26) with $\kappa_k(Y,\mathfrak a|_Y)$ and the
step data satisfy (S2), then $\mathbb T^{\rm pre}_{k+1}(Z',\mathfrak a)$ satisfies (1.26) with $\kappa_{k+1}(Z',\mathfrak a)$.

*Proof.* First the domain: $\chi^{\rm dom}_{k+1}(Z')=\chi^{\rm new}_k(Z')\prod_Y\chi^{\rm dom}_k(Y)$, where $\chi^{\rm new}_k(Z')$ is the indicator of the conditions of Definition II.3.4
at level $k+1$ that involve scale $k$ or $k+1$ inside $Z'$: (1.24) for $j=k$ (the $\pi_{k+1}$-cubes of $\Omega^\sim_{k+1}\cap Z'$) and for $\pi_k$-cubes of $Z^c_k\cap(\Omega^\sim_{k+1})^c\cap Z'$,
and (1.25) for $j=k$. Indeed, for $j<k$ the cubes of (1.24) lie in $Z_{j+1}\cap Z'=\bigsqcup_Y(Z_{j+1}\cap Y)$ or in $Z^c_j\cap(\Omega^\sim_{j+1})^c\cap Z'$, and the latter is
contained in $\bigsqcup_Y Y$ because $Z^c_k\subset\Omega_{j+1}$ for $j<k$ (P5 (1.20)); near those cubes $\mathbb B_{k+1}\cap\square^\sim=\mathbb B_k\cap\square^\sim$ because $Z_k$ is at
distance $>LMR_k$ from $\Omega_{k+1}$ (Lemma I.3.5 (f)); and for $j=k+1$ the conditions are void since $Z'\subset Z_{k+1}$. Now, by Lemma II.5.3 (b) and
Tonelli, for fixed new variables put $\Phi:=\prod_Y\int\mu_Y\,K_Ye^{{\rm Re}\,b_Y}|F|$ (each factor integrates only the internal variables of $Y$). The ancestors act on
disjoint variables, so applying (1.26) to them one at a time, $\int d\psi_k\!\restriction_{T^{(k)}\cap Z_k\cap Z'}\Phi\le e^{-\sum_Y\kappa_k(Y)}\sup\prod_Y\chi^{\rm dom}_k(Y)|F|$ for every value of
the new variables at which $\chi^{\rm new}_k=1$ (elsewhere the step kernel vanishes, (S1)). Integrating the new variables with (S2), uniformly in the old
ones, gives the factor $e^{-\kappa^{(k)}}$. $\square$

**Lemma II.5.14 (one-step bound for quiet steps).** If the step is quiet in $Z'$, (S0) holds, $c_1\ge C_b$ and $c_2\ge C_bB_0+2(L^d+1)$, then (S2)
holds with $\kappa^{(k)}(Z',\mathfrak a)=-(c_1\log\beta_k+c_2)|Z^c_k\cap Z'|_{k+1}$ (no gain), for real $z_{k+1}\in[\frac12,2]$ and $\delta_k\le\frac25$.

*Proof.* Fix the old variables. The action is $\ge0$ for real arguments, so $e^{-\mathcal A}\le1$, and $e^{{\rm Re}\,b_k}\le e^{(C_b\log\beta_k+C_bB_0)|Z^c_k\cap Z'|_{k+1}}$. Integrate
$\psi_{k+1}$ on the $(k+1)$-blocks of $\Omega^c_{k+1}\cap Z'$: $\int z^N_{k+1}t_k(z_{k+1}\psi_{k+1}(y),w)\,d^N\psi_{k+1}(y)=1$. Every $(k+1)$-block of $\Omega_{k+1}\cap Z'$ lies in a cube carrying
$\chi'_{k+1}$ (if within $3$ of $\Omega^c_{k+1}$) or $\chi_{k+1}$ (otherwise), which confines $\theta(y)=z_{k+1}\psi_{k+1}(y)$, resp. $\psi_{k+1}(y)$, to a ball of radius $\le\frac54\delta_k$,
so $\psi_{k+1}(y)$ to a ball of radius $\le\frac52\delta_k\le1$; the $\psi_{k+1}(y)$-integral is $\le v_N\le6$ ($v_N=\pi^{N/2}/\Gamma(\frac N2+1)$, the volume of the unit ball).
Every $k$-block of $Z^c_k\cap\Omega^c_{k+1}\cap Z'$ lies in a $\pi_k$-cube carrying $\chi_k$ (outside $\Omega^{\sim3}_{k+1}$) or in a $\pi_{k+1}$-cube carrying $\chi'_{k+1}$ (inside), which
confines $\psi_k(y)$ to a ball of radius $\le\delta_k$; the $\psi_k(y)$-integral is $\le6$. There are at most $(L^d+1)|Z^c_k\cap Z'|_{k+1}$ such blocks, and
$\log6\le2$. $\square$

(P6 (3.4)'s "$(O(1)\log\beta_k+{\rm const.}E_0)|Z^c_k\cap Z_{k+1}|$" is the same estimate; the $\log\beta_k$ there comes from the normalizations of the fluctuation
integrals and from the vacuum constants, which here are in $b_k$.)

**Lemma II.5.15 (the summability (1.27) for localized histories).** Let $L^d\ge8$. For every $k\ge1$ and every component $Z$ (of $Z^{\rm pre}_k$ or $Z_k$),
$$\sum_{\mathfrak a\in\mathfrak H_k(Z)}C_k(Z,\mathfrak a)^{-1}\le1,$$
where $\mathfrak H_k(Z)$ is the set of all admissible localized histories with final component $Z$ (the "maximal set" of P5 (1.27) [checked]: our admissibility
has no condition involving bounds, ARCH §3.2), including the kept labels of the ripe lineage components.

*Proof.* Induction on $k$. A localized history of a component $Z'$ of $Z^{\rm pre}_{k+1}$ is determined injectively by: the set $S:=Z_k\cap Z'$ of $\pi_k$-cubes;
the record $(\mathsf P,\mathsf Q,\mathsf R,\mathsf S)_{k+1}\cap Z'$, four sets of $\pi_{k+1}$-cubes of $Z'$ disjoint from $S$ (new cubes lie outside $U'_k\supset Z_k$, Lemma I.3.7), hence
subsets of a set of at most $n_2/L^d$ cubes, $n_2:=|Z'\setminus S|_{\#k}$; and the localized histories of the components $Y$ of $S$ (with their own kept labels).
The hull closure and the bookkeeping are functions of these (Part I). Enlarging the index set to *all* such tuples,
$$\sum_{\mathfrak a}C^{-1}_{k+1}(Z',\mathfrak a)\le\sum_{S}e^{-n_1(S)-\frac54n_2(S)}\,2^{4n_2(S)/L^d}\prod_{Y}\Big[\sum_{\mathfrak a_Y\in\mathfrak H_k(Y)}C_k(Y,\mathfrak a_Y)^{-1}\Big]\le\prod_{\square\subset Z'}\big(e^{-1}+e^{-(5/4-4L^{-d}\log2)}\big)\le1,$$
by the induction hypothesis, since $e^{-1}+e^{-0.9}<0.78$ for $L^d\ge8$. At $k=0$ there is no old region ($S=\varnothing$). If $Z'$ is ripe at $k+1$ and kept, the label
sum contributes $\sum_\varkappa C_{\rm dec}(\varkappa)^{-1}\le1$ ((S3)); removed components do not occur. $\square$

(P6 (3.11) counted six region families with $2^{6(LM)^{-d}|\cdot|}$; in our histories $\Omega_{k+1}$, $\Omega''_{k+1}$ and $Z_{k+1}$ are functions of the four new sets, so
four suffice. P5 (1.28) then holds with our $C$.)

---

## II.6 Def-7: the predicate $\mathrm{IsRep}_k$

### II.6.1 The representation structure

**Definition II.6.1 (representation at scale $k$).** Fix the constants $\mathsf c$ of the prefix §I.1.4 up to row 15 (in particular $L$, $M_1$, $M=L^{m_0}M_1$,
$R_{\rm base}$, $p_0,p_2,A_0,\dots,A'_3$, $\alpha_0,E_0,B,\bar\nu$, $B_0,H_0,c_1,c_2,c_v,C_R$, $C_b$, $C_{\psi'}$), and $\beta,\nu,h$. For each admissible torus $\mathbb T=(\mathbb Z/\ell\mathbb Z)^d$,
$ML^{k+1}\mid\ell$, a **representation** $\mathrm{rep}=(\mathfrak s,\mathfrak A,\mathfrak D,\mathcal B)$ consists of:
- $\mathfrak s$ (*small-field data at scale $k$*): the running constants $(\beta_j,\nu_j)_{j\le k}$, $(z_j,E_j)_{1\le j\le k}$; the localized functions
  $\mathcal E^{(j)}(y,X;\cdot)$, $\mathcal M^{(j)}(x,X;\cdot)$ ($j\le k$, $X\in\mathcal D_j$) and $\mathcal R^{(k)}_n(X;\cdot)$ ($n\le m$, $L^m=M$, $X\in\mathcal D_k$), given on finite subsets of $\mathbb Z^d$ and
  pushed to the torus (SF §1.3 (H.4), P5 H4);
- $\mathfrak A$: a finite set of admissible global region histories up to scale $k$ (Definition I.4.1, with the overwrite of Definition I.3.11), whose
  $R$-records at each scale $j\le\min(k,k_0)$ mark every ripe component of $Z^{\rm pre}_j$ as removed or as kept with a label;
- $\mathfrak D$: for every localized history prefix occurring in $\mathfrak A$, the step data (S0)–(S1) of every step and the kept data (S3) of every kept
  component (Definition II.5.7), indexed by the localized prefix (so (S4) holds by construction);
- $\mathcal B$: for every $\mathbb A\in\mathfrak A$ the boundary terms $\mathcal B^{(k)}(X,\mathbb A;\psi,\psi',h,g)$, $X\in\mathcal D_k(\mathrm{mod}\,\Omega^c_k(\mathbb A))$ with $X\cap Z_k\ne\varnothing\ne X\cap Z^c_k$ (P5 (1.38)).

*Derived objects* (functions of rep; no further data): the bookkeeping of Part I (spines, clocks, window states, $t^*$, $\nu$, $U$, ripeness); the localized
and global operators $\mathbb T_k(Z,\mathfrak a)$, $\mathbb T_k(Z_k,\mathbb A)$ (Definition II.5.8); $\kappa_k$, $C_k$, $G_k$ (Definition II.5.11); the characteristic function
$\chi_k(Z^c_k)$ (Definition II.3.2); the restricted small-field functions of P5 (1.6)–(1.17) [checked]:
$$\mathcal A_k(Z^c_k;\psi_k,h):=-\beta_kA^*_k(Z^c_k;\psi_k,\phi_k)+\mathcal E_k(Z^c_k;\psi_k,h)-E_k|Z^c_k|_k,\qquad\mathcal E_k(Z^c_k):=\sum_{j=1}^k\mathcal E^{(j)}(Z^c_k;\psi^{(j)}_k,h),\tag{1.6–1.7}$$
$$\mathcal E^{(j)}(Z^c_k;\psi_j,h):=\sum_{y\in Z^c_k\cap T^{(j)}}\ \sum_{X\in\mathcal D_j:\,y\in X\subset(Z^c_k)^{\approx}}\mathcal E^{(j)}(y,X;\psi_j,h)-\sum_{y\in Z^c_k\cap T^{(j)}}\ \sum_{x\in(Z^c_k)^{\approx}\cap T^{(j)}}\Big[\tfrac12v^{(j)}_1(y,x)(\psi_j^2(x)-\psi_j^2(y))+v^{(j)}_2(y,x)\big(\nu_jh\cdot(\psi_j)_0(x)-\nu_jh\cdot(\psi_j)_0(y)\big)\Big],\tag{1.8}$$
with $v^{(j)}_{1,2}$ determined by $\mathcal E^{(j)}$ on the whole lattice through P1 (3.106) [review]; $\phi_k$, $\psi^{(j)}_k$ of Definition II.2.7 (iii) (mass $\mu_k$, so $\nu$-free
when $\beta_k\nu_k\le1$, P5 (1.9)); $A^*_k(Z^c_k;\psi_k,\phi_k)$ the single-scale action (generating set $T^{(k)}_1$, weight $a_k$) with half bonds on ${\rm st}(Z^c_k)$ (P5 (1.5));
$$\mathcal F_k(Z^c_k;\psi_k,h,g):=\langle\chi_{Z^c_k}g,\phi_k\rangle_1+\sum_{j=1}^k\langle\chi_{Z^c_k}g,\mathcal M^{(j)}(Z^c_k;\psi^{(j)}_k,h,g)\rangle_1,\quad\mathcal M^{(j)}(x,Z^c_k):=\sum_{X\in\mathcal D_j:\,x\in X\subset(Z^c_k)^{\approx}}\mathcal M^{(j)}(x,X);\tag{1.10–1.13}$$
$$\mathcal R^{(k)}(Z^c_k;\psi_k,h,g):=\sum_{n=1}^m\ \sum_{X\in\mathcal D_k:\,X\subset Z^c_k}\mathcal R^{(k)}_n(X;\psi_k,h,g).\tag{1.16–1.17}$$

### II.6.2 The predicate

**Definition II.6.2 (Def-7: $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep},\rho)$, $1\le k$).** A family $\rho=(\rho^{(\ell)})$ of functions $\rho^{(\ell)}_k(\psi_k;h,g)$ over admissible tori and a family of
representations satisfy $\mathrm{IsRep}_k$ iff on every admissible torus:
- **(D1) Form** (P5 H1, (1.1), (1.21) [checked]). For all real $\psi_k$ and all complex $g$ with $\|g\|_{\ell^1}<1$,
  $$\rho_k(\psi_k;h,g)=\sum_{\mathbb A\in\mathfrak A}\mathbb T_k(Z_k(\mathbb A),\mathbb A)\Big[e^{\mathcal B^{(k)}(\mathbb A)}\,\chi_k(Z^c_k)\,\exp\big(\mathcal A_k+\mathcal F_k+\mathcal R^{(k)}\big)(Z^c_k)\Big],\qquad\mathcal B^{(k)}(\mathbb A):=\sum_X\mathcal B^{(k)}(X,\mathbb A),$$
  the operator integrating the internal variables (Definition II.5.2), with absolutely convergent integrals.
- **(D2) Small-field data**: $\mathfrak s$ satisfies Def-6 at scale $k$ (SF §1.3, §1.6: (H.1)–(H.7) in P4's numbering, P5's conventions (1.8)–(1.9), the
  free flow (II.1), analyticity domains $\tilde\Psi^c_j(\mathbb B_j(X);K\varepsilon_j,K\varepsilon_j)$), and the $\mathcal R^{(k)}_n$ satisfy P5 H4 ((1.14)–(1.15) symmetries, localization
  expansions with the bounds of (H.4) with $E_0$ replaced by $\beta_k^{-n-1}$, analyticity on $\Xi_k(1,\varepsilon_k)\times\{\|g\|_{\ell^1}<1\}$).
- **(D3) Characteristic functions**: $\chi_k(Z^c_k)$ is the function of Definition II.3.2 item 1 (P5 (1.18)–(1.19)).
- **(D4) Step and kept data**: $\mathfrak D$ satisfies (S0)–(S3) of Definition II.5.7 for every localized history prefix of every $\mathbb A\in\mathfrak A$, at every step
  $j\to j+1$, $0\le j<k$, and at every kept event.
- **(D5) Operator bound at every scale** (P5 (1.26), ARCH R3-07): for every $\mathbb A\in\mathfrak A$, $j\le k$ and component $Y$ of $Z_j(\mathbb A)$ or of $Z^{\rm pre}_j(\mathbb A)$,
  the localized operator satisfies (1.26) with $\kappa_j(Y,\mathbb A\cap Y)$. (Implied by (D4); Lemma II.6.3 (a).)
- **(D6) Budget invariant (H6′)** ($k\le k_0$): every component $Z$ of $Z_k(\mathbb A)$, $\mathbb A\in\mathfrak A$, satisfies $t^*(Z)>k$ and
  $G_k(Z,\mathbb A\cap Z)\ge\tau_{t^*(Z)}+V_k(Z)+\nu(Z)+U(Z)$, with $V_k(Z)=2\sigma_k\ell(\Gamma(Z))+W_{k+1}(t^*(Z))$ (Part I §I.5.3).
- **(D7) Boundary terms** (P5 H7, (1.38)–(1.39) [checked]): each $\mathcal B^{(k)}(X,\mathbb A)$ depends only on $\psi,\psi',g$ restricted to $X$ and on the history through
  $\mathbb A\cap X$ (the domains $\Omega_j\cap X$, $\Omega''_j\cap X$, $Z_j\cap X$ and the localized histories of the components of $Z_k$ meeting $X$); it is real for real
  arguments, analytic on the H7 domain at $X$ (Definition II.3.5 (d)), bounded there by $|\mathcal B^{(k)}(X,\mathbb A)|<B_0e^{-\kappa d_k(X\,\mathrm{mod}\,\Omega^c_k)}$, jointly
  $O(N)$-covariant in $(\psi,\psi',h,g)$ and invariant under the Euclidean symmetries of the torus preserving $\pi_k$ (P5 H5).
- **(D8) Torus coherence** (roadmap §3.5; ARCH (D8)): every localized datum — $\mathcal E^{(j)}(y,X)$, $\mathcal M^{(j)}(x,X)$, $\mathcal R^{(k)}_n(X)$, the step and kept data of
  a localized history, $\mathcal B^{(k)}(X,\mathbb A)$ — whose support (the set $X$, resp. $V_Z$ of the final component together with the lineage) lies in a cube of
  side $<\ell/4$ is the push-forward of a datum attached to the lifted finite subset of $\mathbb Z^d$, the same for all admissible tori containing such
  a cube (lifts are unique up to translation by the small-set lemma, Lemma I.2.10 (e)); the step data of the quiet steps satisfy this
  automatically.
- **(D9) Coefficients** (P5 (1.42), Theorem 1): $\beta_k>BL^{k(d-2)}$, $0<\nu_k\le\bar\nu$, and $\beta_k\nu_k\le1$.

$\mathcal R_k(\mathsf c):=\{\rho:\exists\,\mathrm{rep},\ \mathrm{IsRep}_k(\mathsf c,\mathrm{rep},\rho)\}$ (ARCH R3-10).

### II.6.3 Variants

- $\mathrm{IsRep}^{\rm pre}_k$ (the image of $S^{(k-1)}T^{(k-1)}$ before $R^{(k)}$; ARCH §3.6): as $\mathrm{IsRep}_k$ with $Z^{\rm pre}_k$ in place of $Z_k$ (no $R$-record
  at scale $k$, operators $\mathbb T^{\rm pre}_k$), and (D6) replaced by (H6′)$^{\rm pre}$: $t^*(Z)\ge k$ and $G^{\rm pre}_k(Z)\ge\tau_{t^*(Z)}+V_k(Z)+\nu(Z)+U(Z)$ for every
  component of $Z^{\rm pre}_k$ (ripe components allowed).
- $\mathrm{IsRep}^\flat_k$ ($k_0\le k\le k_f$; ARCH §3.6): as $\mathrm{IsRep}_k$ except that there are no window data and no $R$-records at scales $>k_0$, the
  backgrounds at scales $j>k_0$ carry the mass $\mu_j=\nu_jL^{-2j}$ (complete backgrounds, P5 p. 490, P6 p. 2), the characteristic functions at
  scales $>k_0$ contain the $h$-conditions, (D9) is $\beta_k>BL^{k(d-2)}$, $0<\nu_k$ only, and (D6) is replaced by
  $$\text{(H6}^\flat)\qquad G_k(Z,\mathbb A\cap Z)\ \ge\ A_2\hat\lambda_{k_0}^{p_2}+2\sigma_k\ell(\Gamma(Z))+W_{k+1}(\hat k_f)$$
  for every component (spines and clocks continue in the frozen regime, Part I §I.4.4 (T7)); for the conventional $k_0=0$ the threshold is
  $A_2\hat\lambda_0^{p_2}\ge p_2(\beta)$. This is the only place where $\hat k_f(\nu)$ enters Def-7 (§II.1.4).

**Lemma II.6.3 (consequences).** Assume $\mathrm{IsRep}_k$ (resp. a variant) and the hypotheses of Lemmas II.5.12–II.5.15.
(a) (D4) implies (D5).
(b) (P5 (1.29)–(1.31)) For every component $Z$ of $Z_k$ and Borel $F$: $\sum_{\mathfrak a}\int d\psi_k\!\restriction_Z\int\mu\,|Ke^b||F|\le\sup_{\mathfrak a}e^{-G_k(Z,\mathfrak a)-H_k|Z|_k}\cdot\sup\chi^{\rm dom}|F|$, the
sum over the localized histories of $Z$ occurring in $\mathfrak A$.
(c) Under (D6) (and $\hat\lambda_0\ge\lambda_*$), the right side of (b) is $\le e^{-2p_2(\beta_k)-H_k|Z|_k}$ (P5 (1.31) with $\ell=2$); under (H6♭) it is
$\le e^{-p_2(\beta_{k_0})-H_k|Z|_k}$ (with $\ell=1$ and the frozen threshold, the repaired P6 Theorem 4).
(d) The histories of $\mathfrak A$ satisfy (G1), (G2) of LF-2 (Part I §I.5.7), and their budgets satisfy (B) (Lemma II.5.12); so the hypotheses of
LF-2 not involving $R$ hold for every representation.

*Proof.* (a) Induction on $j$ with Lemma II.5.13 (steps) and (S3) (kept events), starting from (S2) at $j=0$. (b) Write
$\int\cdots\le e^{-\kappa_k}\sup\chi|F|=C_k\,e^{-\kappa_k}\cdot C_k^{-1}\sup\chi|F|$ and sum with Lemma II.5.15; $C_ke^{-\kappa_k}=e^{-G_k-H_k|Z|_k}$ by definition.
(c) (D6) gives $G_k\ge\tau_{t^*}\ge\tau_{k+1}=2A_2\hat\lambda_{k+1}^{p_2}\ge2A_2\lambda_k^{p_2}\ge2p_2(\beta_k)$ (Lemma II.1.2 (b); $\lambda_k\ge\log\beta_k$); (H6♭) gives
$G_k\ge A_2\hat\lambda_{k_0}^{p_2}\ge p_2(\beta_{k_0})$. (d) Part I Lemmas I.3.7–I.3.8 and (R8)–(R9). $\square$

### II.6.4 What Def-7 changes in the interfaces of ARCH §3.7, §8.3

- **LF-3** (one step, $1\le k<k_0$): *for every* $\mathrm{rep}$ with $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep},\rho)$ there is $\mathrm{rep}'$ with $\mathrm{IsRep}^{\rm pre}_{k+1}(\mathsf c',\mathrm{rep}',S^{(k)}T^{(k)}\rho)$, whose
  histories extend those of $\mathrm{rep}$ by a step record, whose step data at the new step are constructed (non-quiet kernels from P5 (2.47),
  P6 (3.2) with the local background; boundary factors from P6 (2.32)–(2.33), (3.3) and the background change of Lemma II.5.9's route), and whose
  small-field data are the image under P4 Theorem 2 with the free flow. (D6) for $\mathrm{rep}'$ is LF-2 (i). The operator bound (S2) for the
  non-quiet steps is P6 (3.4)–(3.9) with the local background (LF-1 applies to it).
- **LF-4** ($R$): the hypothesis is $\mathrm{IsRep}^{\rm pre}_k(\mathsf c,\mathrm{rep},\rho)$ and $\beta_k\nu_k\le1$ **only** (ARCH §8.3 also required $\mathrm{rep}$ to be "the output of LF-3",
  which named a construction; with D-II.2 the window operators are explicit in every representation). The conclusion produces kept data (S3)
  for the kept components and removes the others; (Rg) of LF-2 is then $G''_k=G^{\rm pre}_k-C_R\hat\lambda_k^{2d+1}+\gamma-\log C_{\rm dec}\ge G^{\rm pre}_k-C_R\hat\lambda_k^{2d+1}+A'_3\hat\lambda_k^{p_R}$,
  an identity plus (S3).
- **LF-5, LF-6, LF-7, LF-8**: unchanged in form; they read $\mathcal R_k$, $\mathcal R^{\rm pre}_k$, $\mathcal R^\flat_k$ as defined here.

### II.6.5 The external field $g$ and the limit $\nu\downarrow0$ (OBSERVABLES §4.2, received during the writing)

1. *$g$ is an analytic parameter of every object.* Kernels are $g$-independent and non-negative; $g$ enters only through the step and kept
   boundary factors (S0), (S3), the boundary terms (D7) and the small-field functional $\mathcal F_k$ (D2), all analytic on $\|g\|_{\ell^1}<1$. The hard-spin
   factor $e^{\langle g,\phi\rangle}$ of the large-field sites of scale $0$ enters $b_0$ with $|\langle g,\phi\rangle|\le\|g\|_{\ell^1}\le1$ (§II.7).
2. *Joint covariance of $R''$*: required of the kept data in (S3) and of the new small-field terms by (D2); whether P7's coset average (M4) is
   taken on the full integrand is a Part III item (O-II-5).
3. *Locality in $g$*: (S0), (S3), (D7) require dependence on $g$ restricted to $V_Z$, resp. $X$.
4. *Sup bounds on the complex polydisc*: (1.26) (Definition II.5.2), (S0) and (D7) are stated for all complex $\|g\|_{\ell^1}<1$.
5. *$\nu\downarrow0$ and the horizon*: no object of Def-7 uses $\hat k_f(\nu)$ (§II.1.4); the bookkeeping uses $\hat\lambda$ (a function of $\beta$); for fixed $k$ and
   $\nu<\nu_*(k)$ (any $\nu_*(k)$ with $\beta_k\nu_k\le1$) all scales $j\le k$ are in the regime $j\le k_0$, where the backgrounds are $\nu$-free and $\nu$ enters
   only through the running constants and the $\nu$-term of the actions. $\mathrm{IsRep}_k$ is a predicate at fixed $\nu$, so continuity of the large-field
   data in $\nu$ is a property of the flow (LF-7), to be stated there as a clause analogous to SF's (CONT) (open item O-II-6).
P9's marked polymer expansion PE-M with large-field holes is a Part IV / POLYMER item; nothing in Def-7 obstructs it (the large-field
operators are local and their bounds are of the form used by PE).

---

## II.L Lean declarations asked for by Part II

Namespace `Balaban.LargeField`; all files Lean modules. Order = dependency order; sizes are estimates including docstrings. Prerequisites
not yet landed are listed in the last column of the relevant rows: **Def-5** (`bgField`, `bgFieldC`, BG Theorems 5.2/7.1–7.2 assembled from the landed
`prop51_exists_unique`, `prop51_analytic`, `lemma53`), **Def-6** (SF's small-field class), and Part I blocks A–C.

| # | Declaration(s) | Kind | Content | Needs | Est. lines |
|---|---|---|---|---|---|
| **F** | **Running constants** (`LargeField/Analytic/Constants.lean`) | | | | **≈300** |
| F1 | `runLam`, `runR`, `pZero`, `pOne`, `deltaRun`, `epsRun`, `bgMass`, `betaCanon`, `kZero`, `kZeroGenuine`, `kF` | def | Def. II.1.1 | `Flow/RunningCoefficients` | 120 |
| F2 | `runLam_le_hat`, `hat_le_runLam_add_two`, `runR_ge_base`, `logBeta_ge`, `gain_conv`, `logBeta_succ_le` | thm | Lemma II.1.2 | `betaSeq_eq`, `norm_gammaSeq_le` | 150 |
| F3 | `AnalyticLamConditions` ((Λ15)–(Λ17)) | def | §II.1.3 | — | 30 |
| **G** | **Generating sets and backgrounds** (`LargeField/Background/*`) | | | | **≈2 100** |
| G1 | `minimalGenSet` (as `GeneratingSet d L N₀ q ϱ₃`), `minimalGenSet_mono` (to `Precedes`), `minimalGenSet_range`, `minimalGenSet_disjoint` | def/thm | Def. II.2.2, Lemma II.2.3 | `GeneratingSet` | 600 |
| G2 | `liftSingle`, `liftMixed` (to `BgData`), layer-constancy | def/thm | Def. II.2.1 | `BgData`, `IsLayerConstant` | 200 |
| G3 | `genCube`, `genCubeMixed`, `genSF`, `genBoundary`, `genBoundaryLocal`; generating-set, range and agreement lemmas | def/thm | Def. II.2.4, Lemma II.2.5 | G1, Part I B | 700 |
| G4 | `isEL_local_iff`, `bgFieldC_local_eq` (exact factorization) | thm | Lemma II.2.6 | **Def-5**, `IsEL`, `IsSmallSolution` | 400 |
| G5 | `bgCube`, `bgCubeMixed`, `bgSF`, `psiSF` (via `composeField`), `bgLoc` | def | Def. II.2.7 | **Def-5**, `composeField` | 200 |
| **H** | **Characteristic functions and domains** (`LargeField/Characteristic/*`) | | | | **≈1 400** |
| H1 | `Reg`, `chiK`, `chiPrimeOld` (2.5), `chiPrimeNew` (2.13), `chiFluct` (2.42), `chiNext` (P6 (2.1)), products over cube sets | def | Defs. II.3.1–II.3.2 | G5 | 350 |
| H2 | `measurableSet_chi`, `chi_stencil` | thm | Lemma II.3.3 | H1, BG Thm 5.2 (2) | 350 |
| H3 | `chiDom` ((1.24)–(1.25)), `PsiTildeMulti` | def | Def. II.3.4 | `InPsiTilde` | 300 |
| H4 | `DeltaC`, `DeltaPrimeC`, `H7Domain` | def | Def. II.3.5 | **Def-5** (`bgFieldC`) | 400 |
| **I** | **LF-1** (`LargeField/LF1.lean`) | | | | **≈900** |
| I1 | `adjacent_blockAvg_sq_le`, `hardSpin_one_sub_sq_le` | thm | Lemmas II.4.2–II.4.3 | `blockPoincare_sharp` | 300 |
| I2 | `actionG`, `lf1_gradient`, `lf1_hardSpin` | def/thm | Thm. II.4.1 | `GeneratingSet`, `IsAdmissibleWeights` | 600 |
| **J** | **Operators** (`LargeField/Operators/*`) | | | | **≈3 100** |
| J1 | `InternalVars` (index sets, `Fintype`), `refMeasure` (`aprioriMeasure` × Lebesgue), `multiscaleField` | def | Def. II.5.1, (II.3) | Part I C, `aprioriMeasure` | 400 |
| J2 | `LFKernel` (structure: `K ≥ 0` Borel, `b` analytic in `g`), `LFKernel.op`, `Bound126`, `LFKernel.comp`, `LFKernel.tensor`, `op_comm` | def/thm | Def. II.5.2, Lemma II.5.3 | Mathlib `MeasureTheory` | 800 |
| J3 | `mainActionLoc` | def | Def. II.5.4 | I2, G5 | 200 |
| J4 | `IsQuiet`, `quietKernel` | def | Defs. II.5.5–II.5.6 | H1, H3, J3 | 400 |
| J5 | `StepData`, `KeptData` (structures with fields (S0)–(S3)), indexing by localized prefixes (S4) | def | Def. II.5.7 | J2, H4 | 400 |
| J6 | `locOp` (recursion), `locOp_support`, `locOp_factor`, `locOp_level`, `locOp_domain` | def/thm | Def. II.5.8, Lemma II.5.9 | J1–J5, Part I B6, C1 | 700 |
| J7 | `locOp_rot_invariant`, `locOp_euclid_invariant` | thm | Lemma II.5.10 | G4, `Model/Symmetry` | 200 |
| **K** | **Exponents and budget** (`LargeField/Budget/*`) | | | | **≈1 700** |
| K1 | `kappaStep`, `kappa`, `logC`, `budgetG` | def | Def. II.5.11 | J6, F1 | 200 |
| K2 | `lemmaB` | thm | Lemma II.5.12 | K1, F2 | 300 |
| K3 | `bound126_comp` | thm | Lemma II.5.13 | J2, J6 | 400 |
| K4 | `quietKernel_bound` | thm | Lemma II.5.14 | J4 | 400 |
| K5 | `sum_inv_logC_le_one` | thm | Lemma II.5.15 | K1, Part I C2 | 400 |
| **L** | **Def-7** (`LargeField/Def7.lean`) | | | | **≈1 000** |
| L1 | `Rep` (structure $(\mathfrak s,\mathfrak A,\mathfrak D,\mathcal B)$), `sfRestricted` (P5 (1.6)–(1.17)) | def | Def. II.6.1 | **Def-6**, J5 | 400 |
| L2 | `IsRep`, `IsRepPre`, `IsRepFlat`; `RepClass` | def | Defs. II.6.2–II.6.3 | L1, K1, Part I C | 300 |
| L3 | `isRep_bound126`, `isRep_sum_bound`, `isRep_p2_bound`, `isRep_LF2Hyp_geom` | thm | Lemma II.6.3 | K2–K5, Part I E2 | 300 |
| | **Total** | | | | **≈10 500** |

No file need exceed 1 000 lines. Blocks F, G1–G3, H3, I, J1–J2, K1, K2, K5 can be drafted now (they need only landed Lean and Part I);
G4, G5, H1–H2, H4, J3–J7, K3–K4, L need Def-5 landed; L needs Def-6 frozen. Def-7 (L2) is freezable only after Parts I–II are approved,
Def-5 and Def-6 are frozen, and the open items O-II-1, O-II-2, O-II-5 below are settled (ARCH §8.4).

---

## II.O Status, changes, open items

### II.O.1 Status of the statements of Part II

| Statement | Status |
|---|---|
| Defs. II.1.1, II.2.1, II.2.2, II.2.4, II.2.7, II.3.1–II.3.5, II.5.1, II.5.2, II.5.4–II.5.8, II.5.11, II.6.1–II.6.2 and the variants | definitions (sources [checked] as marked) |
| Lemma II.1.2 | proved here from (I.2) (landed Lean) |
| Lemmas II.2.3, II.2.5, II.2.6 | proved here (II.2.6 uses BG's (EL) and domains; the uniqueness statement is BG Theorem 5.2, proved on paper) |
| Remark II.2.8 (backgrounds evaluated only on the domain; identification with P5–P6) | the identification is cited (P5 (2.7), (2.10), P6 (2.6), P1 Lemma 3.1); not needed by Def-7 |
| Lemma II.3.3 | proved here |
| Theorem II.4.1 (LF-1), Lemmas II.4.2–II.4.3 | proved here ($\gamma_0=1/(28d)$; Lemma II.4.3 from the landed `blockPoincare_sharp`) |
| Lemma II.5.3, II.5.9 (structural Lemma F), II.5.10 | proved here |
| analytic half of Lemma F (background change into $b_k$ and $\mathcal B$) | cited route (P6 (2.12)–(2.17), LOC I-4b, I-5, Lemma AE); LF-3's proof; conditional on LOC's open items (O-2′) |
| Lemma II.5.12 (Lemma B), II.5.13, II.5.14, II.5.15 ((1.27)) | proved here |
| (S2) for non-quiet steps | P6 (3.4)–(3.9) [checked]; to be re-derived in LF-3 with the local background |
| Lemma II.6.3 | proved here from the above |

### II.O.2 Check of LEMMA-F-astra and the changes made

LF-astra was checked against P5 p. 493, p. 505, P6 pp. 6–7, 16, P7 pp. 499–500, 525. Its diagnosis is correct: P6 (3.2)'s background is the
minimiser for $\mathbb B_{k+1}(\partial\Omega_{k+1})$, which spans all components, so the literal kernel is not supported in $U^\sim$ of one component, and P6 p. 16's
sentence is not a proof (P5 p. 505 makes the same point for (2.17)). Its exact identity (F.9) is Lemma AE (landed `abstract_expansion`) and is
correct; (F.10) is conditional on I-4/I-5, as it says; the full-parameter version of I-4 that it uses is plausible (the walk expansion with all
parameter cubes converges under the same $M_1\ge c\,e^{N_0\kappa_1}$). **Adopted:** choice (b) (exact factorization of the representation, corrections in $\mathcal B$),
the treatment of K1/K2 (componentwise, restricted backgrounds as in P7 (3.7), (3.20)), and the constant bookkeeping (new $\mathcal B$-terms independent
of $B_0,H_0,c_1,c_2$; $B_0$ chosen after them). **Changed:** (1) the local action uses the genuine minimiser of the component-local boundary
generating set $\mathbb B^{\rm loc}$ (D-II.1) instead of the normalized decoupled field $\Phi_q(s^Z)$; (2) the correction terms with localization domain inside
$Z_{k+1}$ go into the step boundary factor $b_k$ (they are local to one component), the others into $\mathcal B^{(k+1)}$; (3) LF-astra's "$s_*$" (an interaction-cube
collar) is not Part I's $s_*=4$; the gap used here is $[R_k]$ cubes of side $ML^{k+1}$ (Lemma II.2.5 (c)).

### II.O.3 Changes relative to ARCH v4 and to Part I

1. D-II.1 (Lemma F via $\mathbb B^{\rm loc}$; ARCH §3.7 Lemma F's UNCERTAIN resolved in favour of "a definition choice").
2. D-II.2: non-quiet step kernels, step boundary factors and kept kernels are data with properties (S0)–(S4); ARCH R3-08/§8.2 had all
   operators defined. LF-4's hypothesis is $\mathrm{IsRep}^{\rm pre}_k$ alone (ARCH §8.3).
3. Def-7's (D5) is stated in the composable form (modulus inside) and is implied by (D4) (Lemma II.6.3 (a)); ARCH listed it as a condition.
4. P7's objects ($\psi^0_k$, $R$'s characteristic functions (2.18), (2.21), (2.61), (3.2), the P1 Lemma 3.1 comparison of P7 p. 502) move from II.2/II.3
   to Part III, because Def-7 no longer contains them (ARCH §9 rows II.2, II.3).
5. (1.27) uses four region families (not P6's six); P5 (1.28) holds with our $C$.
6. LF-1 has an explicit $\gamma_0=\frac1{28d}$ and needs no hypothesis on $\alpha$ or $\lambda$.
7. Part I version 1.1 (audit repairs P1-01–P1-08, §I.0 item 16): $M/M_1=L^{m_0}$ fixed, (RH), $R_j\ge R_{\rm base}$, genuine $k_0$ in Lemma I.5.6 (c), hull
   closure labelled as an extension of P6 p. 22, $R_{\rm base}$, split $\lambda_*$ lists. No other change to Part I.

### II.O.4 Open items (Parts I and II together)

- **O-1 (Timár's lemma, Lean).** Unchanged.
- **O-2′ (analytic half of Lemma F; replaces O-2).** The localization expansion of the background change from $\mathbb B_{k+1}(\partial\Omega_{k+1})$ to $\mathbb B^{\rm loc}$ (route
  in §II.5.5) must be written in LF-3 (Part IV.1). It needs LOC I-4b (v), I-5 (with the variation for one-cube anchors) and inherits LOC's open
  items (NC, GM2, the $h'$-conditions of $\Xi^c$).
- **O-3 (Lemma L (c), (3.11)′).** Unchanged (Part III).
- **O-4 (range of P3's minimal generating sets).** **Closed**: range $1$ cube (Lemma II.2.3 (c)).
- **O-5 ($\pi'$ offsets; adjacency of components of $\Omega^c$ in P5 (1.33)).** Open; neither affects the form of Def-7 (both enter only the summability
  (1.35) with a constant $K_0$, to be fixed in Part III/IV).
- **O-6 (Lemma B at hulls; base rule).** Hull half **closed** (Lemma II.5.12). Base rule ($k=0$: sets $\mathsf P_1,\dots,\mathsf S_1$, the step data at $k=0$ with
  spin variables, (S2) with the gain $\kappa^{(0)}$, and $b_0\ni\langle g,\phi\rangle$): §II.7.
- **O-7 (constant order).** **Closed** in Part I v1.1.
- **O-8′ (free flow versus $c=0$; replaces O-8).** The exact composition of the window transformations (P7 p. 499, (2.7), (2.9), (2.55), (2.57)) uses
  P5's $c=0$; under the free flow it holds up to relative errors $O(\beta^{-1}L^{-2\gamma k_1})$. Part III §III.2 must carry the actual composed weights
  (route (i) of §II.1.5).
- **O-9, O-10.** Unchanged.
- **O-II-1 (Def-5 in Lean).** `bgField`, `bgFieldC` and the assembly of BG Theorem 5.2 are not landed; BG Lemmas 6.2/6.3 (W28) are open. Def-7 needs
  the first two.
- **O-II-2 (Def-6).** (D2) is Def-6; SF's open requirement R-ν (the RG equations with $\nu$-free backgrounds) must be settled before Def-7 is frozen.
- **O-II-3 (new errata candidates).** N-II-1: P6 (3.2) prints $(\Omega''^c_{k+1})^{\sim3}\cap\mathsf S_{k+1}$ where p. 4 has $\cup$ (Definition II.5.6). N-II-2: P7 p. 499 cites
  "(1.36), (1.37) [4]", which do not exist in P4; read as P5 (1.40)–(1.41). N-II-3: the index of the fluctuation variables (P5 p. 492 versus P6
  p. 5). Minor: P5 (1.19) prints $|h^2-1|<\delta^2_k/\sqrt{\nu_k}$; whether P6 (3.2)'s background is evaluated at $\psi_{k+1}$ or $\theta=z_{k+1}\psi_{k+1}$.
- **O-II-4 (constants of the small-field step).** $C_b$ (P6 (2.33) "const.") and $C_{\psi'}$ (P5 (1.25) "const.") are outputs of LF-3, chosen with row 11;
  $c_1\ge C_b$, $c_2\ge C_bB_0+2(L^d+1)$ (row 14) must be added to the chain.
- **O-II-5 (kept data from P7).** Part III must show that P7's kept operators K1, K2 have the form (S3): non-negative $g$-independent kernel on
  the lineage's variables, $g$ in an analytic factor, the coset average (M4) taken on the full integrand (joint covariance, OBSERVABLES §4.2 (2)),
  and the bound with $\kappa''$.
- **O-II-6 ($\nu\downarrow0$).** The continuity of the flow's large-field data in $\nu$ is a clause of LF-7, analogous to SF's (CONT) (OBSERVABLES §4.2 (5));
  Def-7 does not obstruct it (§II.6.5).
- **O-II-7 (torus coherence of constructed data).** LF-3 and LF-4 must construct their step and kept data from finite-set objects so that (D8) holds;
  by Lemma II.5.9 they are local, so this is a matter of stating the constructions on $\mathbb Z^d$.
- **O-II-8 (row 3 of the constant chain).** The conditions G-1–G-6 on $L$ are still to be written as $L\ge L_i(d)$ (Part I row 3, UNCERTAIN); Part II added
  no condition on $L$ beyond $L^d\ge8$ (Lemma II.5.15) and $\varrho\ge2dL$ (LF-1, implied by $R_0(d,L)\ge4dL$).
