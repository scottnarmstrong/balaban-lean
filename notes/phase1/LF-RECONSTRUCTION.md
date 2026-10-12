# Large-field reconstruction document, Part I: geometry and counting (model-free)

**Version 1.3 (2026-10-12).** The amendments tagged [v1.3: ...] incorporate the Part III and Part IV audits, FLUCTUATION, and the indicated landed Lean constants. A cited analytic input remains an input until its stated hypotheses are verified; the status ledger at the end records those dependencies.

Version 1.1 of Part I (version 1 + the repairs of the independent audit `LFR-PART1-AUDIT-astra.md`, findings
P1-01–P1-08, listed in §I.0 item 16 and marked "(audit P1-xx)" where they occur), 2026-10-11; Part II is appended
after §I.7. Brief: `orchestration/briefs/D-LFR-partI.md`. Input:
`notes/phase1/LF-ARCHITECTURE.md` version 4 (commit 44141ef; cited as **ARCH**), its reviews
`LF-ARCHITECTURE-review.md` (cited as **REV1**, **REV3**), `LF-V3-COUNTING-astra.md` (**COUNT**) and
`LF-V4-REPAIRS-astra.md` (**REPAIRS**); received during the writing and taken into account:
`LF-V4-AUDIT-astra.md` (V4-01–V4-03), `LOCALIZATION-review.md` (L-04, order of constants) and the
orchestrator's note on `SMALLFIELD.md` (the choice $c=0$). Status: draft for independent review. Nothing here is approved
or frozen. Parts II–IV (analytic objects and Def-7; $R$ on covered windows; the flow and the end) follow Part I (Part IV, with §II.7, was
appended on 2026-10-12; its changes to Part I are marked "version 1.2 (Part IV)" and listed in §IV.O.2); Part I refers to them only through the abstract
hypotheses (G1), (G2), (B), (Rg), (K), (H-λ), (H-T) of the internal lemma LF-2 (§I.5), which are never frozen.

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
  are written $\mathsf P_{k+1},\mathsf Q_{k+1},\mathsf R_{k+1},\mathsf S_{k+1}$ (sans-serif). [v1.3: P4-09] In the operative geometric flow, plain $R_k$ is the chosen separation $\hat R_k$; $R^{\rm run}_k:=R_{\rm base}\lambda_k^2$ is used only for comparison with the source convention. The fixed coefficient, which P5 (1.2) calls $R_0$, is written $R_{\rm base}$ throughout.
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

$$\lambda_k\le\hat\lambda_k\le\lambda_k+2,\qquad\text{and, if }\lambda_k\ge0,\qquad R^{\rm run}_k:=R_{\rm base}\lambda_k^2\le\hat R_k .\tag{I.3}$$

The second inequality needs $\lambda_k\ge0$ (audit P1-02: for $\beta a<1$ the running radius can exceed $\hat R_k$). In
the flow $\hat\lambda_0\ge\lambda_*\ge3$, so $\lambda_k\ge\hat\lambda_k-2\ge1$ for all $k$, hence $R_k^{\rm run}\ge R_{\rm base}$ and $R_k^{\rm run}\le R_k=\hat R_k$ [v1.3: P4-09]; every
statement below that is specialized "to the flow" uses this.

$k_0$ in the operative flow is the last $k$ with $\beta\nu L^{kd}\le1$, read as $0$ if there is none [v1.3: P4-01]; the earlier running definition belongs only to ARCH §3.6. Let $k_f$ be the first
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
| 4 | constants depending on $(d,L)$ (and $N$) only: $\gamma_0$, $K_0,K_1,K_2$, $C_3,C_4$, Green constants of G-1–G-3, $R_0(d,L)$ of BACKGROUND §2; $s_*:=4$, $s':=5$ (Lemma I.3.8); $c_0$ (I.0 item 3); $D_0:=3c_0+4$; $K_6,c_{11}$ of P7 Lemma 2.1 for boxes of size $<D_0$; Part III: $D''_0:=9(2c_0+1)+8$, $c_{D_0}$, $C_{2.20}$, $C_6:=3dD_0(K_6+1)$, $C_{23}$, $C_{24}$ (§§III.3–III.4, III.8) | outputs of G-1–G-3, P2, P7 Lemma 2.1 | outputs ($\exists$) / definitions | the constants of I-4 depend on $\kappa_1$ and are in row 5$'$ |
| 5 | $\kappa_0$; $\kappa_{\rm flow}:=\max\{C_{d,L}(\kappa+1)+C'_{d,L},16\kappa_0+16,\ 2(4+\log(2(2d)^2 2^{2d+1}))\}$ [v1.3: constant b], with $C_{d,L}:=3^{d+1}L^{2d+1}$ and $C'_{d,L}:=C_{\rm loss}+C_{d,L}L^d\log2$ | the multiscale block count has the extra factor $L$ beyond LOCALIZATION's $L^{2d}3^{d+1}$; $\kappa_0$ is an output of row 4 | output / definition | $\kappa_0$ independent of $M$ and $M_1$ |
| 5a | $m_0$ [v1.3: constant a] | $r_0:=4dL^3+L$, $r_1:=(r_0-4dL^3)/L=1$; $m_0:=\min\{m\ge1:\ L^m\ge\max\{14d,\ L+9,\ 4+r_0/L\}\}$, $M/M_1:=L^{m_0}$ | landed $i4a_close_X0$ in DecoupledFieldX0.lean, P3 p. 81, Lemma II.2.3 | $\rho=LMR_{\rm base}\ge4dLM$ is also imposed in row 7; $6M_1\le M$ and $(4L+r_0)M_1\le LM$ follow from the defining maximum |
| 5b | $\kappa_1$ | $\kappa_1\ge\max\{4d(2L+1)^d\kappa_{\rm flow},\ 4d\log((2L+1)L^{m_0})+2\}$ (the second is the walk-expansion condition of I-4, LOCALIZATION §5.3 (3); with $M/M_1=L^{m_0}$ it depends on $(d,L)$ only) | lower | checked: both are lower bounds on $\kappa_1$ in terms of earlier rows (audit P1-01 resolved) |
| 5$'$ | localization constants $c_*,B_G,c_6,\delta_*,K_3,K_4,c_7,B_4,B_5$ | outputs of I-4 (walk expansion), depending on $(d,L,N,\kappa_1)$ and not on $M_1$, $M$ (LOCALIZATION §5.3 (4)) | outputs ($\exists$) | moved after $\kappa_1$ (L-04) |
| 6 | $M_1=L^{m_1}$; then $M:=L^{m_0}M_1$ (definition) | $M_1\ge M_*(\kappa_1):=\max\{4L^2,c_Me^{N_0\kappa_1}\}$ ($c_M,N_0$ of LOCALIZATION §1.2); P3 (4.38) first part $e^{\gamma_wM_1}\ge4(d+2)(K_2+1)K_4/\eta_\varepsilon$; $M\ge2(7L)^d\kappa_1/\gamma_0$; $M\ge M(\kappa)$ (P4, ER-025); P7 (2.70) $3(d+1)K_1K_3K_6e^{-\gamma_0M/5}\le\frac18$; $5LM_1\ge R_0(d,L)$ (minimal generating sets are generating sets for I-1, Lemma II.2.3 (a)) | lower bounds on $M_1$ | every condition is $M_1\ge$ (function of rows 0–5b and of the $(d,L)$-constants $K_1,K_6$ of row 4, $K_3,K_4$ of row 5$'$): the conditions on $M$ become conditions on $M_1$ because $M=L^{m_0}M_1$ is increasing in $M_1$; no upper bound on $M$ or $M_1$ anywhere in Part I or ARCH §5 |
| 6b | $K_5$ (P4 (5.24), contains $M$), $B_6=NL^dB_4+2$ | outputs depending on $M$ | outputs ($\exists$) | after $M$; $E_0\ge4C_4B_6K_0K_5$ stays after them (row 11) |
| 7 | $R_{\rm base}$ | $R_{\rm base}\ge\max\{44K_1K_6,\ C(L),\ 4L+20,\ 4d,\ R_0(d,L)/(LM)\}$ [v1.3: constant b], so $\rho=LMR_{\rm base}\ge4dLM$ | lower | $K_6=K_6(d,L,D_0)$ is fixed in row 4; this adds a lower bound only |
| 8 | $p_2:=2d+3$, $p_0:=$ least even integer $\ge d^2+7d+2$, $A_2:=1$, $C_\nu:=C_r$ | (K) of §I.5.2 | definitions | (K) holds: $p_R\ge5d+4>p_2+2d$, $2p_0>p_2$ |
| 9 | $A_0$; $A_1,A_3,A'_3,A''_3$ derived | P7 p. 505; P6 (3.9); version 1.2 (Part IV): $A_3:=\frac14\min\{\frac{8\gamma_0}{6^d(9K_1)^2}A_0^2,\frac18A_1^2\}$, a quarter of P6's constant (Lemma II.7.8) | lower | $A_3,A'_3$ are increasing in $A_0$ [review] |
| 10 | $\alpha_1$, $c_8$; $c_9^{\rm flow}$ | P4 Thm 1 "sufficiently small"; version 1.2 (Part IV): $\alpha_1\le\gamma/2$ (Root-F's $\delta=\gamma/2$) and $c^{\rm flow}_9:=\min\{c^{\rm P4}_9,\frac12c_9e^{-\kappa_{\rm flow}}\}$ | upper | as stated in P5 p. 499 [review] |
| 11 | $\alpha_0,E_0,B,\bar\nu$; $C_b$, $C_{\psi'}$, $C_{15}$, $B_{\rm st}$ [v1.3: constants c,d] | outputs of P4 Thm 1, P5 Thm 1; the constants of P6 (2.33) and P5 (1.25) (Part II, (S0) and Definition II.3.4); $C_b$ also bounds the base constants of Lemma II.7.7 (b). Put $C_{\Xi1}:=(4d+8)(2d+1)$ and require $3(4d+6)(2d+1)\alpha_0\le1$ and $3C_{\Xi1}\alpha_0\le c^{\rm BG}_1$, since $\varepsilon_j\le(1+\sum_{n\ge1}n^{-2})\alpha_0<3\alpha_0$; these are the landed (Ξ1)/(Ξ4) domain hypotheses | outputs / upper bounds on $\alpha_0$ | the small-field theorem must supply an $\alpha_0$ within these bounds; increasing $\lambda_*$ cannot replace this choice |
| 12 | $B_0$ | $B_0\ge B^\sharp:=B_{\rm st}+1$ (P7 p. 529; Lemma III.10.7) | lower | $B^\sharp$ is independent of $H_0,c_1,c_2$: $B_{\rm st}$ is an output of rows 0–11 (Lemma IV.1.5) |
| 13 | $H_0$ | $H_0>2B_0K_0M^{-d}$; P7 (4.12); version 1.2 (Part IV): $H_0\ge2L^d(C'_E+1)$ (Lemma IV.4.2, Theorem IV.4.1) | lower | checked [review] |
| 14 | $c_1,c_2$ | $\ge$ P6's coefficients; $c_1\ge C_b$, $c_2\ge C_bB_0$ (Lemma II.5.14, version 1.1, audit P2-02); the refund constants $c_1\ge C_W$, $c_2\ge C'_W$ of Part III §III.8.2 (they contain P7's $C_{39},C'_{39}$) | lower | checked (a larger cost coefficient keeps P6 (3.9) true) |
| 15 | $c_v:=M^d(H_0+c_1+3)$; $C_R$ | Lemma B; LF-4R, Definition III.8.6 ((III.8.4); depends on rows 0–11 only) | definition / output | $c_v\ge1$ |
| 16 | $\lambda_*$, then $\beta_0:=\max\{e^{\lambda_*-1}/a,2B\}$ | §I.5.3: (Λ0)–(Λ17′); Part III (Λ18)–(Λ25-op); Part IV (Λ26)–(Λ32), including (Λ28′); [v1.3: constants c,d] the analytic-domain uses take $C_{\Xi1}=(4d+8)(2d+1)$ and $K_\Sigma=\frac B{\theta_h}((C_3+\frac32K_1)C_{\Xi1})+C_HC_{\Xi1}+8$, with row-11 smallness | lower | eventual lower bounds after rows 0–15; the row-11 upper bound on $\alpha_0$ is a separate small-field input |
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
&\exists\lambda_*\ \forall\beta\ge\beta_0:=\max\{e^{\lambda_*-1}/a,2B\}\ \forall\nu\in(0,1]\ \forall h\in S^{N-1}\ \forall\text{admissible tori}:\ \text{LF-2 (instantiated), LF-3, \dots, LF-8 hold.}
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
$(4L+r_0)M_1\le LM$ hold by the [v1.3: constant a] definition of $m_0$, $r_0=4dL^3+L$. Constants chosen after $M$ (row 6b: $K_5$ of P4 (5.24), which
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
- *Cube tori.* In the flow the fine torus is $(\mathbb Z/\ell\mathbb Z)^d$ with $ML^{\hat k_f+1}\mid\ell$ (version 1.2 (Part IV), D-IV.1; version 1.1 had
  $ML^{k_f+1}\mid\ell$, which depends on the running $\nu_k$), and $n_k:=\ell/(ML^k)$ for $0\le k\le\hat k_f+1$. Abstractly (§I.5) we are given positive integers $n_0,\dots,n_K$
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

[v1.3: FLUCTUATION §4.3(iv)] The operative analytic bound uses the modular *covering* size $d_k^{\rm cov}(X\,\mathrm{mod}\,\Omega^c)$ of FLUCTUATION Definition 1.1 and LOC v3: choose $\pi'_k$-cubes contained in $X$ whose union covers $X\cap\Omega$, then minimize the length in scale-$k$ units of a tree in $X$ meeting each chosen cube, divided by $M$. This is at most the preceding P5 size $d_k$. FLUCTUATION Lemma 1.2 (G1)–(G3) proves the volume, entropy and union inequalities for $d_k^{\rm cov}$; those are the analytic estimates used from Part II onward. In particular a bound with $d_k$ cannot be inferred from one with $d_k^{\rm cov}$. The admissible cover and a finite value of $d_k^{\rm cov}$ are hypotheses on each localization domain; the $\hat Y(S)$ domains of FLUCTUATION Theorem 3.1 have them. For a general member of the larger Def-2 class without such a cover, no finite covering-size bound is asserted here.

---
## I.3 The region calculus

The region rules of P5 §2 and P6 §2 are written below as explicit set functions on the cube tori,
with Balaban's distance conditions converted to index distances by Lemma I.2.2. The analytic content of
the decompositions (which characteristic function is attached to which cube) is Part II's; here only
the sets matter. The step $k\to k+1$ takes the region $Z_k$ *after* $R^{(k)}$ and after the removal
overwrite (§I.3.4).

### I.3.1 One step as set functions

**Data.** Reals $R_{k-1},R_k\ge0$ (P5 (1.2)'s radii; in the flow, version 1.2 (Part IV), D-IV.2, the a priori radii $R_j:=\hat R_j=R_{\rm base}\hat\lambda_j^2$, so that
(RH) holds with equality and the histories do not depend on $\nu$; version 1.1 used the running $R^{\rm run}_j=R_{\rm base}\lambda_j^2$) and the bookkeeping
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
- (B) is Lemma B (Part II, Lemma II.5.12; P6 (3.9)–(3.11) [checked]), converted to $\hat\lambda$ by (I.3); at $k=0$ it is Lemma II.7.2 (e), with the base
  one-step bound of Lemma II.7.8 (§II.7). *Version 1.2 (Part IV):* with the a priori regime index $k_0$ (D-IV.11) and the tori $ML^{\hat k_f+1}\mid\ell$, (H-λ) and (H-T) are
  Lemma IV.3.3, which uses only $(\beta,\nu)$;
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
list (Λ0)–(Λ14) (with (Λ15)–(Λ17) of Part II and (Λ18)–(Λ25) of Part III); Case 2b's large-$\Lambda'$ branch is direct; (H-λ) is derived from (I.2) only; LF-2 has a final scale
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

Version 1.1 (Part II, sections II.1–II.6), 2026-10-12: version 1 (2026-10-11) with the repairs of the audit `LFR-PART2-AUDIT-astra.md`
(findings P2-01–P2-06) and the amendments required by Part III, listed in §II.O.5 and marked "(audit P2-xx)" or "(Part III)" where
they occur. Brief: `orchestration/briefs/D-LFR-partII.md`. Input: Part I above
(version 1.1), ARCH v4 (§§3, 5, 8, 9), `LEMMA-F-astra.md` (cited as **LF-astra**), `BACKGROUND.md` v2 (**BG**),
`LOCALIZATION.md` v2 (**LOC**), `SMALLFIELD.md` v2 (**SF**), `GREEN.md`, `POLYMER.md` and their reviews; the landed Lean of
`Balaban/Background`, `Balaban/Localization`, `Balaban/Flow`, `Balaban/Multiscale`, `Balaban/Green`, `Balaban/Polymer`.
Status: draft for independent review; nothing in this Part is approved or frozen (the architecture rulings it implements are, §II.0). Tags and status words as in Part I
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

**Rulings in force.** ARCH v4 §7 rulings 1 and 2 are **approved by the author** (2026-10-11; AGENTS.md "Author rulings",
`frozen/APPROVALS.md`, section "LF rulings 1–2"): the reconstructed bookkeeping (A′) — budget invariant (H6′), spines, clocks, pre-window/pending/active
states, ripeness with merge strips, $R$ on windows of up to $\nu_{\max}$ merged pieces, components by distance $<\omega_k$ — for Def-7, LF-2 and LF-4;
and the Def-7 design — $\mathrm{IsRep}_k$ on representations, deterministic bookkeeping on $\hat\lambda$, (D5) at every scale $j\le k$, LF-4 existential. Part II
implements both. D-II.1 and D-II.2 below refine the approved design without leaving it (Def-7 stays a predicate on representations,
the bookkeeping stays on $\hat\lambda$, (D5) is required at every scale, LF-4 stays existential); they change ARCH v4 in two points of detail
(the background of the new large-field action, and which operators are data rather than functions) and are **for author review**.

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
| $R_j$ [v1.3: P4-09] | operative chosen radius $R_j:=\hat R_j=R_{\rm base}\hat\lambda_j^2$ in every region rule, neighbourhood and late scale; $R^{\rm run}_j=R_{\rm base}\lambda_j^2$ denotes only the P5 (1.2) comparison value | D-IV.2; P5 (1.2) source notation |
| $p_0(\beta_j),\ p_1(\beta_j)$ | $A_0\lambda_j^{p_0}$, $A_1\lambda_j^{p_1}$ with $p_1:=p_0$ | P5 p. 487, (2.42); P6 (3.9) ("we have taken $p_1=p_0$") |
| $\delta_j$ | $(\beta_ja)^{-1/2}p_0(\beta_j)=e^{-\lambda_j/2}A_0\lambda_j^{p_0}$ | P5 p. 498 |
| $p_2(\beta_j)$, $H_j$ | $A_2(\log\beta_j)^{p_2}$, $H_0\log\beta_j$ | P5 (1.30) |
| $\varepsilon_j$, $\varepsilon_{1,j}$ | $\alpha_0(1+\sum_{n\ge j}n^{-2})L^{-j\alpha}$, $\frac{A_1}{A_0}\varepsilon_j$ | SF §1.7 (P4 (H.1)); P5 (1.37) |
| $\mu_j$ | the fine-unit mass of the backgrounds at scale $j$: $\mu_j:=0$ if $j\le k_0$, $\mu_j:=\nu_jL^{-2j}$ otherwise (version 1.2: the test is $j\le k_0$ with the a priori $k_0$, D-IV.11) | P5 (1.9) [checked]; BG §1.1 |
| $\beta^{(q)}_n,\ a^{(q)}_n$ | for a multiscale action at level $q$ and $n\le q$: $\beta_qL^{-(q-n)(d-2)}$ and $a_q\frac{1-L^{-2q}}{1-L^{-2n}}$ | P5 (1.41), P6 p. 17, P7 (2.10) |
| $k_0$ | *version 1.2 (Part IV), D-IV.11:* $\max\{k:\beta\nu L^{kd}\le1\}$ (a priori; then $\beta_k\nu_k\le e^{2\epsilon}$ for $k\le k_0$), *genuine* if $\beta\nu\le1$, and $k_0:=0$ (*conventional*) if $\beta\nu>1$; version 1.1: the last $k$ with $\beta_k\nu_k\le1$ (P5's running index, which differs by at most one) | P5 p. 490; Part I §I.1.1 |
| $k_f$ | the first $k$ with $\nu_k>\frac78L^{-2}$ | P4 §6; P7 p. 529 |

Under the free flow $a^{(q)}_n=a_n$ for all $q\ge n$ (insert (II.1)): the coefficients "renormalized to step $q$" of P7 (2.10) coincide
with the actual ones. Under P5's choice $c=0$ they differ by factors $1+O(\beta^{-1})$ (SF §3.1).

### II.1.2 Comparison with the a priori sequence

**Lemma II.1.2.** Assume the bounds (I.2) of Part I with $\epsilon\le\frac1{20}$ (Def-6 (H.6) through the landed `betaSeq_eq`,
`nuSeq_eq`, `norm_gammaSeq_le`), $a\in(1,\frac32)$, and $\hat\lambda_0\ge3$ (condition (Λ14) of §I.5.3). Then for all $j$:
(a) $\lambda_j\le\hat\lambda_j\le\lambda_j+2$, $\lambda_j\ge1$, and $R_{\rm base}\le R^{\rm run}_j\le R_j=\hat R_j$; in particular the radius hypotheses (RH) of §I.3.1
hold for the flow and $R_j\ge R_{\rm base}$ (Lemma I.3.10 (c));
(b) $\hat\lambda_j-3\le\log\beta_j\le\hat\lambda_j$; hence $p_2(\beta_j)\le A_2\hat\lambda_j^{p_2}$, $\tau_j=2A_2\hat\lambda_j^{p_2}\ge2p_2(\beta_j)$, and
$H_0(\hat\lambda_j-3)\le H_j\le H_0\hat\lambda_j$;
(c) $\delta_j\le\bar\delta(\hat\lambda_j)$ with $\bar\delta(x):=eA_0x^{p_0}e^{-x/2}$, a decreasing function for $x\ge2p_0$;
(d) if $\hat\lambda_k\ge3/(1-2^{-1/(2p_0)})$ (condition (Λ15)), then $A_3(\log\beta_k)^{2p_0}\ge g_k=\frac12A_3\hat\lambda_k^{2p_0}$;
(e) $\log\beta_{k+1}-\log\beta_k\le(d-2)\log L+2\epsilon$;
(f) $k_f\le\hat k_f\le k_f+1$ if $k_f\ge1$ (Lemma I.5.6 (a)).

*Proof.* (a) $\lambda_j=\log(\beta a)+j(d-2)\log L+\log\gamma_j=\hat\lambda_j-1+\log\gamma_j$ and $|\log\gamma_j|\le\epsilon$; so $\lambda_j\ge\hat\lambda_j-2\ge1$
and $R_{\rm base}\le R^{\rm run}_j=R_{\rm base}\lambda_j^2\le R_j=R_{\rm base}\hat\lambda_j^2$. (b) $\log\beta_j=\lambda_j-\log a$ with $0<\log a<\log\frac32<\frac12$. (c)
$\delta_j=A_0\lambda_j^{p_0}e^{-\lambda_j/2}$, $\lambda_j\le\hat\lambda_j$ and $\lambda_j\ge\hat\lambda_j-2$. (d) $(\log\beta_k)^{2p_0}\ge(\hat\lambda_k-3)^{2p_0}=\hat\lambda_k^{2p_0}(1-3/\hat\lambda_k)^{2p_0}$,
and $(1-3/x)^{2p_0}\ge\frac12$ iff $x\ge3/(1-2^{-1/(2p_0)})$. (e) $\beta_{k+1}/\beta_k=L^{d-2}\gamma_{k+1}/\gamma_k$. (f) Part I. $\square$

### II.1.3 The analytic conditions on $\lambda_*$ added by Part II

For all real $x\ge\lambda^{\rm II}_*$ (combined with Part I's lists into $\lambda_*$, §I.5.3):

| | Condition (for all $x\ge\lambda_*^{\rm II}$) | Used in |
|---|---|---|
| (Λ15) | $x\ge3/(1-2^{-1/(2p_0)})$ | Lemma II.1.2 (d), Lemma B |
| (Λ16) | $H_0\big[(1-L^{-d})(x-3)-L^{-d}((d-2)\log L+1)\big]\ge1$ and $x\ge c_2+2$ | Lemma B (old volume, new volume) |
| (Λ17) | $3dL\,\bar\delta(x)\le\min\{c_1^{\rm BG},\,c_{11}\}/C_4$ and $\bar\delta(x)\le\min\{\delta_{**},\delta_*\}/(C_3C_4)$ | Remark II.2.8 (the backgrounds of the step exist on the support of the kernels), Lemma II.3.3 (faithfulness) |
| (Λ17′) | $3dL\,c_N\,\bar\delta(x)\le\frac12$, $c_N=Nv_N(\frac32)^{N/2}$ (version 1.1, audit P2-02) | Lemma II.5.14 (shell volumes $\le1$) |

$c_1^{\rm BG},C_3,C_4,\delta_{**}$ are the constants of BG Theorem 5.2, Lemma 5.3 and Theorem 6.1 ($(d,L,N)$-constants, row 4), $\delta_*$ that of
BG Prop 5.1, $c_{11}$ that of P7 Lemma 2.1 (row 4). Each condition compares a fixed constant with a function tending to $\infty$
(or $0$), so $\lambda^{\rm II}_*$ exists; (Λ16) is the place where $c_2$ (row 14) enters, so $\lambda_*$ is chosen after row 14, as in §I.1.3.

### II.1.4 Causality

Def-7 at scale $k$ (§II.6) reads the running constants $(\beta_j,\nu_j,z_j,E_j)_{j\le k}$ only, and the test "$j\le k_0$" only through
$\beta_j\nu_j\le1$ for $j\le k$ (P5 p. 490: $\beta_j\nu_j$ is increasing, so "$j\le k_0$" is decided at scale $j$). *Version 1.2 (Part IV), D-IV.11:* the test is made with the
a priori product $\beta\nu L^{jd}$, which is known before the flow; the running test is circular at the switching step. All bookkeeping
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
P2 (4.18), equivalently (C1) of BG §6.1, for these weights. Part III must either (i) carry the actual composed transformation through
(2.9)–(2.58), or (ii) use $c=0$ for the whole flow, which would require the perturbation statement for the Gaussian kernels that SF §3.1
says no source provides. Route (i) is adopted. *(Audit P2-05; version 1 claimed here that route (i) "leaves a quadratic remainder bounded by
$O(\beta^{-1})\times$ the window volume". That is not correct: expanding at the ideal stationary point leaves a **linear** first-variation residual,
and every coefficient error is multiplied by $\beta_k$. Moreover the field renormalizations $\theta=z_{j+1}\psi_{j+1}$ of the window Gaussians shift
the mean of the composed Gaussian, an effect that version 1 did not list.)* The repair is Part III: Lemma III.1.6 computes the actual composed
transformation exactly for arbitrary positive coefficients and arbitrary $z_j$ (weights $a^\natural_z=a_z(1+\eta_z)$, mean $\mathcal Q^\natural_z$ with the factors
$\varpi_n=\prod_{i>n}z_i^{-1}$), Lemma III.1.7 bounds the mean shift after weighting by the volume fractions of the deep layers, and Lemma III.6.3 is the
perturbative composition lemma: the cancellation (2.53)–(2.58) is done exactly with the ideal weights and the ideal minimizer, and the complete
difference $C^\natural$ (its linear part, its quadratic part and the normalization constants, with the factor $\beta_k$) splits into a part absorbed by
$\frac38$ of the composed-Gaussian term and a part bounded by $1$ on the real window domain and by $C_\natural\hat\lambda_k^{2d+1}$ on the complex window domain
(paid by $C_R$, (III.8.4)). Def-7 itself does not depend on the choice beyond the values of the running constants.

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

[v1.3: F-1, constants c,d] The author accepted FLUCTUATION Finding F-1: Def-6 and Def-7 (D2) require analyticity of each local $\mathscr E^{(j)}(y,X;\cdot)$ and $\mathscr M^{(j)}(x,X;\cdot)$ on $\Xi^c_j(\mathbb B_j(X);1,\varepsilon_j)$. The data domain $\tilde\Psi^c_j$ is used to construct and estimate the background, not as the output analyticity domain of those local terms. For the inclusion (Ξ1) use $C_{\Xi1}=(4d+8)(2d+1)$, under $(4d+6)(2d+1)\varepsilon_j\le1$ (landed xiC1, xiC_inPsiTildeC); in (Ξ4) use $K_\Sigma=\frac B{\theta_h}((C_3+\frac32K_1)C_{\Xi1})+C_HC_{\Xi1}+8$ (landed xiSigma, xiFour). These constants replace the earlier $3$ and $+4$ in every application of (Ξ1), (Ξ4), including the H7-to-$\tilde\Psi^c$ inclusion in Lemma IV.1.3. Def-7 (D7) retains (1.36)–(1.37), the H7 domain for boundary terms.

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
- *Reference measure* $\mu_{Z,\mathfrak a}$: the product of the surface measures `(volume).toSphere` on $S^{N-1}$ (the factors of the frozen `aprioriMeasure`; total mass
  $Nv_N$ per site, not normalized — version 1.2 (Part IV) correction) for the spins, and Lebesgue measure $d^N\psi$ for the other internal variables. (The fluctuation variables of the
  step $0\to1$ are $\mathbb R^N$-valued through the representation $\int_{\phi^\perp}f\,d^{N-1}\xi=(s/2\pi)^{1/2}\int_{\mathbb R^N}f(P^\perp_\phi u)e^{-\frac s2(\phi\cdot u)^2}du$ ($s=\beta$) of ARCH LF-6
  (iv); this convention is fixed in §II.7, D-IV.4, Lemma II.7.4.)
- The *multiscale field* $\psi$ of the history ($\psi=\psi_j$ on $\Lambda_j\cap T^{(j)}$, P5 p. 492) is a function of the internal and output variables, since
  $\Lambda_j\subset\Omega^c_{j+1}$ for $j<k$ and $\Lambda_k=\Omega_k\cap T^{(k)}$.

All internal variables are located in $Z$: $\Omega^c_{j+1}\cup(\Omega_{j+1}\setminus\Omega''_{j+1})\subset Z_{j+1}$ (Lemma I.3.5 (e)), and $Z_{j+1}\cap Z$ is the lineage of $Z$
(Lemma I.4.3 (c)). For a component $Z'$ of $Z^{\rm pre}_{k+1}$ with ancestors $\mathrm{Anc}_k(Z')$ (Definition I.4.2),
$$I(Z',\mathfrak a)=I^{\rm new}_k(Z')\ \sqcup\bigsqcup_{Y\in\mathrm{Anc}_k(Z')}I(Y,\mathfrak a|_Y),\qquad I^{\rm new}_k(Z'):=\{\psi_k\text{ on }T^{(k)}\cap\Omega^c_{k+1}\cap Z'\}\sqcup\{\psi'_k\text{ on }T^{(k)}\cap(\Omega_{k+1}\setminus\Omega''_{k+1})\cap Z'\},\tag{II.3}$$
because $Z_k\cap Z'=\bigsqcup_{Y}Y$ and $\Omega^c_{j+1}\subset Z_{j+1}\subset Z_k$ for $j<k$. The output variables of every ancestor are new internal variables:
$V_Y\subset U^{\sim}_k\subset\Omega^c_{k+1}$ as fine sets (Lemma I.3.5 (a), (i)) and $V_Y\subset V_{Z'}$ (Lemma I.3.15), so $T^{(k)}\cap V_Y\subset T^{(k)}\cap\Omega^c_{k+1}\cap Z'$.

### II.5.2 Kernels, operators, and the bound (1.26)

**Definition II.5.2 (large-field operators).** A *large-field kernel* at $(Z,\mathfrak a)$ is a pair $(K,b)$: $K\ge0$ a Borel function of the output and
internal variables and of $h$, independent of $g$; $b$ a function of the output and internal variables and of $(h,g)$, $\|g\|_{\ell^1}<1$, analytic in $g$ and real for real
arguments. (Version 1 said "$K$ a function of the output and internal variables"; the quiet kernel of Definition II.5.6 depends on $h$ through the
$\nu$-term of the main action, so $K$ may depend on $h$ (Part III).) **Convention on $g$ (audit P2-04).** The operators of Def-7 depend on $g$, through
the factor $e^{b}$ only; this is P5 H5 [checked, p. 493: the kernel "depends on $\psi_k,\psi,\psi',g$ restricted to $U^\sim_k$"]. The $g$-dependence cannot be moved
out of the operators, because $b$ contains boundary terms that depend on the integrated variables. LF-3 and LF-4 use this convention. Consequently
the assertion (L4) of `OBSERVABLES.md` §4.1 ("the integral operators $\mathbb T_k$ do not depend on $g$") is not available: the observable argument must
differentiate the large-field operators in $g$, which it can do by Cauchy estimates, since (1.26) holds uniformly on the whole polydisc (open item
O-II-9, §II.O.4). Its operator is
$$\mathbb T F(\psi_k):=\int K(\psi_k,x)\,e^{b(\psi_k,x;h,g)}\,F(\psi_k,x)\,\mu_{Z,\mathfrak a}(dx)$$
on Borel functions $F$ of the output, internal and other (parameter) variables for which the integral converges absolutely. The **bound (1.26)**
with exponent $\kappa$ (P5 (1.26) [checked], in the form with the modulus inside, which is the form that composes) is
$$\int d\psi_k\!\restriction_{T^{(k)}\cap Z}\int\mu_{Z,\mathfrak a}(dx)\,K\,e^{{\rm Re}\,b}\,|F|\ \le\ e^{-\kappa}\ \sup\big\{\chi^{\rm dom}_k(Z,\mathfrak a)|F|\big\}\qquad\text{for all Borel }F\text{ and all }\|g\|_{\ell^1}<1,\tag{1.26}$$
the supremum over all variables. For real $g$ the kernel $Ke^b$ is non-negative, as P5 H5 requires; for complex $g$ the bound is the sup bound on
the whole polydisc (OBSERVABLES §4.2 (4)). *Reduction to $F\equiv1$ (audit P2-06).* If the kernel vanishes unless $\chi^{\rm dom}_k(Z,\mathfrak a)=1$ (Lemma II.5.9 (d)),
then $K|F|=K\chi^{\rm dom}|F|\le K\,\sup\{\chi^{\rm dom}|F|\}$ pointwise, so (1.26) for all $F$ is equivalent to (1.26) for $F\equiv1$. This is how (1.26) is used below; it
avoids suprema of Borel functions over a subset of the variables, which need not be Borel.

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
  (Version 1.1: $b_k$ depends on $\psi_{k+1}$ only through the multiscale field, i.e. on $T^{(k+1)}\cap\Omega_{k+1}\cap V_{Z'}$.)
- (S1) *Step kernel.* If the step is quiet in $Z'$: $K_k(Z',\mathfrak a):=K^{\rm q}_k(Z')$. Otherwise $K_k(Z',\mathfrak a)$ is a datum: a non-negative Borel function of
  $\psi_{k+1}$ on $T^{(k+1)}\cap V_{Z'}$, of the variables $I^{\rm new}_k(Z')$ and $\psi_k$ on $T^{(k)}\cap Z_k\cap Z'$ and of $h$, independent of $g$, vanishing unless
  $\chi^{\rm new}_k(Z')=1$, O(N)- and Euclid-invariant as in (S0). *Gaussian structure* (version 1.2 (Part IV), D-IV.3; version 1.1 asked $W$ to be a singleton with $F\equiv1$, which is
  false when $\mathsf P_{k+1}\ne\varnothing$; P5 (2.47): the factor $T^{(k)}(\Omega^c_{k+1})\chi'^{(k)c}(\mathsf P)\chi'^{(k)}(\mathsf P^c\cap\Omega'\cap\Omega^c)$):
  $$K_k(Z',\mathfrak a)=\prod_{y\in T^{(k+1)}\cap\Omega^c_{k+1}\cap Z'}z_{k+1}^N\,t_k\big(z_{k+1}\psi_{k+1}(y),(Q\psi_k)(y)\big)\cdot\sum_{w\in W}F^w_k(u)\,\tilde K^w_k(Z',\mathfrak a),\qquad u_y:=z_{k+1}\psi_{k+1}(y)-(Q\psi_k)(y),$$
  with $W$ finite, $F^w_k:(\mathbb R^N)^{T^{(k+1)}\cap\Omega^c_{k+1}\cap Z'}\to[0,1]$ Borel, and $\tilde K^w_k\ge0$ independent of $\psi_{k+1}\restriction_{\Omega^c_{k+1}}$. For the quiet kernel $W$ is a singleton and $F\equiv1$ (Definition
  II.5.6 and the support argument of Lemma III.1.5, one step); for P5 (2.47) $W$ is a singleton and $F$ is the $\chi'^{(k)}$-factor (Lemma IV.1.4); at $k=0$ see (II.7.4).
- (S2) *One-step bound* (restated in version 1.1, audit P2-06). Call *new* the variables $\psi_{k+1}$ on $T^{(k+1)}\cap Z'$, $\psi_k$ on $T^{(k)}\cap Z^c_k\cap\Omega^c_{k+1}\cap Z'$ and
  $\psi'_k$, *new′* the new variables other than $\psi_{k+1}\restriction_{\Omega^c_{k+1}}$, and *old* the variables $\psi_k$ on $T^{(k)}\cap Z_k\cap Z'$ and the internal variables of the
  ancestors. There is a Borel function $S_k(Z',\mathfrak a)\ge0$ of the new′ variables and of the parameters ($\psi_{k+1}$ on $V_{Z'}\setminus Z'$, $h$, $g$) such that, for
  **all values of the old variables** and all $\|g\|_{\ell^1}<1$,
  $$\tilde K^w_k(Z',\mathfrak a)\,e^{{\rm Re}\,b_k(Z',\mathfrak a)}\le S^w_k(Z',\mathfrak a),\qquad\sum_{w\in W}m^w_k\int d(\text{new}')\,S^w_k(Z',\mathfrak a)\ \le\ e^{-\kappa^{(k)}(Z',\mathfrak a)},\qquad m^w_k:=\int\prod_yg_k(u_y)\,F^w_k(u)\,du,$$
  $g_k$ the centred Gaussian density of $t_k$ (version 1.2; for $W$ a singleton with $F\equiv1$ this is the version-1.1 form), with $\kappa^{(k)}$ of Definition II.5.11. For quiet steps this is Lemma II.5.14; for the others it is a requirement (P6 (3.4)–(3.9), whose bound has
  exactly this form: P6 (3.4) takes the supremum over $\psi'_k$ and the old variables after bounding the new integrals [checked]). Version 1 required only the
  integral of $K_ke^{{\rm Re}\,b_k}$ for fixed old outputs, which is not enough to compose (audit P2-06).
- (S3) *Kept data* (scale $k\le k_0$, $Z$ a ripe component of $Z^{\rm pre}_k$ that is kept): a label $\varkappa$ from the finite set $\mathfrak K$ ($\mathfrak K=\{\varkappa_1,\dots,\varkappa_5\}$ in
  Part III, Definition III.5.2), numbers $C_{\rm dec}(\varkappa)\ge1$ with $\sum_{\varkappa\in\mathfrak K}C_{\rm dec}(\varkappa)^{-1}\le1$, a *kept exponent* $\gamma(\varkappa)$ with
  $\gamma(\varkappa)-\log C_{\rm dec}(\varkappa)\ge A'_3\hat\lambda_k^{p_R}$, and a large-field kernel $(K'',b'')$ at $(Z,\mathfrak a)$ with the output variables of $\mathbb T^{\rm pre}_k(Z,\mathfrak a)$ and
  internal variables $I''\subset I(Z,\mathfrak a)$ that contain all variables of the multiscale field and of the fluctuation fields of the lineage (Part III, D-III.9;
  the reference measure is the restriction of $\mu_{Z,\mathfrak a}$), with $K''$ vanishing unless $\chi^{\rm dom}_k(Z,\mathfrak a)=1$ (a function of the multiscale and fluctuation
  fields, hence of $I''$ and the outputs), $b''$ as in (S0) with the bound replaced by a bound uniform on the H7 domain, invariance as in (S0), and the bound
  (1.26) with exponent $\kappa''_k(Z,\mathfrak a,\varkappa):=\kappa_k(Z,\mathfrak a)-C_R\hat\lambda_k^{2d+1}+\gamma(\varkappa)$. In (II.3) a kept ancestor $Y$ contributes $I''(Y)$.
- (S4) *Locality.* All these data depend on the history only through the localized history prefix of $Z'$ (resp. $Z$); in particular they are
  the same for two global histories with the same localized prefix (P5 p. 493: the multi-index "is determined completely by its restrictions";
  P6 p. 15).
- (S5) *Rotation form* (Part III, D-III.6; needed by the coset average of $R$, P7 p. 521 [checked]). For $k+1\le k_0$ (resp. $k\le k_0$ for kept data) the
  kernel has the form $K=\mathbf 1_A\,e^{-a}$, where (i) $A$ is a Borel set of values of the output and internal variables that is invariant under
  $R\in O(N)$ acting on all spin-valued variables ($h$ not acted on); (ii) $a$ is a real function of the variables and of $h$, jointly invariant,
  $a(Rx;Rh)=a(x;h)$, which extends analytically in $(x,h)$ to the complex neighbourhood of $A\times S^{N-1}$ formed by the displacements of modulus
  $<\varepsilon_j$ of the variables of scale $j$ and $<1$ of $h$; (iii) on that neighbourhood $|a(x;h')-a(x;h)|\le C_{\rm S5}|h'-h|\,|Z|_k$. The quiet kernel has
  this form ($A$ is the support of its characteristic functions, which contain no $h$-condition for $k+1\le k_0$; $a$ is the Gaussian exponent plus the
  main action; (iii) with $C_{\rm S5}=3$ because $h$ enters only through the term $\frac{\nu_{k+1}}2\beta_{k+1}\|\phi-h\|^2$ and $\beta_{k+1}\nu_{k+1}\le e^{2\epsilon}$ for $k+1\le k_0$ (version 1.2, D-IV.11; version 1.1 had $C_{\rm S5}=2$
  from $\beta_{k+1}\nu_{k+1}\le1$)). A kernel that is a finite sum of such forms (the base kernels (II.7.4)) is admitted; Lemma III.9.5 applies term by term.

(S3) is ARCH's kept exponent (§3.4, R3-08) with the kept operator and its decomposition data left to LF-4 (D-II.2). P7's two kinds K1, K2 are
instances; Part III constructs them (§III.5, §III.8) and shows that the $g$-dependence of the kept operators sits in a factor $e^{b''}$ with $K''\ge0$
independent of $g$, and that the coset average (M4) is taken on the full integrand, so that everything is jointly covariant (OBSERVABLES §4.2 (2);
open item O-II-5, closed in Part III).

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
bounded by $\varepsilon_Fe^{-\kappa d_{k+1}^{\rm cov}(Y\,\mathrm{mod}\,\Omega^c_{k+1})}$ with $\varepsilon_F\to0$ as $\hat\lambda_0\to\infty$; terms with $Y\subset Z_{k+1}$ go into $b_k$, the others into $\mathcal B^{(k+1)}$.
*Route.* $\mathbb B^{\rm loc}\prec\mathbb B_{k+1}(\partial\Omega_{k+1})$ (Lemma II.2.3 (b) layer by layer), so by I-2 (BG Theorem 6.1 (ii), landed `isEL_compose`)
$\phi(\mathbb B_{k+1}(\partial\Omega_{k+1});\tilde\psi)=\phi(\mathbb B^{\rm loc};\psi(\mathbb B^{\rm loc},\mathbb B_{k+1}(\partial\Omega_{k+1});\tilde\psi))=\phi^{\rm loc}+\delta\phi$, where the data change
$\psi(\mathbb B^{\rm loc},\mathbb B_{k+1}(\partial\Omega_{k+1});\tilde\psi)-\tilde\psi$ vanishes on the sets $E_{Z'}=Z'^{\sim[R_k]}$ (Lemma II.2.5 (c)), i.e. at distance $\ge[R_k]$ cubes of side
$ML^{k+1}$ from $X_{Z'}$. [v1.3: P4-09, Lambda28'] The zero-data condition is P6 (2.12)–(2.13) and (2.16). On the chosen geometry its usable distance is $D_k=M([\hat R_k]-1)-2M_1$; LOC I-4a/b gives $|\delta\phi|\le C_{\rm BG}\delta e^{-\gamma_wD_k}$. The action and its first variation are bounded and localized as in FLUCTUATION Theorem 4.2; (Λ28′) pays the prefactor. P6's printed $e^{-R_k}$ is not obtained by substituting a larger radius into its old bound. The expansion of the action
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
integrates over all of $Z^c_k\cap Z_{k+1}$, hull cubes included, since they lie in $\Omega''_{k+1}$). The base $k=0$ (LF-6) supplies (S2) with this
$\kappa^{(0)}$: Lemma II.7.8 (§II.7, written with Part IV).

**Lemma II.5.13 (composition of bounds; (D5) for a step).** If every ancestor operator $\mathbb T_k(Y,\mathfrak a|_Y)$ satisfies (1.26) with $\kappa_k(Y,\mathfrak a|_Y)$ and the
step data satisfy (S2), then $\mathbb T^{\rm pre}_{k+1}(Z',\mathfrak a)$ satisfies (1.26) with $\kappa_{k+1}(Z',\mathfrak a)$.

*Proof.* First the domain: $\chi^{\rm dom}_{k+1}(Z')=\chi^{\rm new}_k(Z')\prod_Y\chi^{\rm dom}_k(Y)$, where $\chi^{\rm new}_k(Z')$ is the indicator of the conditions of Definition II.3.4
at level $k+1$ that involve scale $k$ or $k+1$ inside $Z'$: (1.24) for $j=k$ (the $\pi_{k+1}$-cubes of $\Omega^\sim_{k+1}\cap Z'$) and for $\pi_k$-cubes of $Z^c_k\cap(\Omega^\sim_{k+1})^c\cap Z'$,
and (1.25) for $j=k$. Indeed, for $j<k$ the cubes of (1.24) lie in $Z_{j+1}\cap Z'=\bigsqcup_Y(Z_{j+1}\cap Y)$ or in $Z^c_j\cap(\Omega^\sim_{j+1})^c\cap Z'$, and the latter is
contained in $\bigsqcup_Y Y$ because $Z^c_k\subset\Omega_{j+1}$ for $j<k$ (P5 (1.20)); near those cubes $\mathbb B_{k+1}\cap\square^\sim=\mathbb B_k\cap\square^\sim$ because $Z_k$ is at
distance $>LMR_k$ from $\Omega_{k+1}$ (Lemma I.3.5 (f)); and for $j=k+1$ the conditions are void since $Z'\subset Z_{k+1}$. Hence the composed kernel vanishes
unless $\chi^{\rm dom}_{k+1}(Z')=1$ (step kernel by (S1), ancestors by the induction hypothesis), and by the reduction after (1.26) it suffices to prove (1.26)
with $F\equiv1$. *Order of integration (version 1.1, audit P2-06).* The integrand is $K_ke^{{\rm Re}\,b_k}\prod_YK_Ye^{{\rm Re}\,b_Y}\ge0$, so Tonelli allows any order.
(1) Integrate $\psi_{k+1}$ on the $(k+1)$-blocks of $\Omega^c_{k+1}\cap Z'$: by the Gaussian structure (S1) they occur only in the factors
$z^N_{k+1}t_k(z_{k+1}\psi_{k+1}(y),\cdot)$ and $F^w_k(u)$ (the ancestors' kernels are functions of scale-$k$ and older variables); the change of variables $u_y=z_{k+1}\psi_{k+1}(y)-(Q\psi_k)(y)$
(Jacobian $z^N_{k+1}$ per block) turns the integral of the $w$-term into the number $m^w_k$, whatever the values of the other variables (version 1.2; in version 1.1, $F\equiv1$ and $m=1$). (2) Bound
$\tilde K^w_ke^{{\rm Re}\,b_k}\le S^w_k(\text{new}')$ by (S2); $S^w_k$ does not depend on the old variables. (3) For fixed new′ variables, integrate the old variables:
the ancestors act on disjoint sets of old variables, and the remaining variables on which $K_Y$ depends (its outputs on $V_Y\setminus Y$, which are new′
variables, and the parameters) are fixed; applying (1.26) with $F\equiv1$ to one ancestor at a time gives $\int d(\text{old})\prod_YK_Ye^{{\rm Re}\,b_Y}\le e^{-\sum_Y\kappa_k(Y)}$, a
constant. (4) Integrate $S^w_k$ over the new′ variables and sum over $w$ with the weights $m^w_k$: $\le e^{-\kappa^{(k)}}$ by (S2). The product is $e^{-\kappa_{k+1}(Z')}$ by (3.10). No supremum over a part of the
variables is taken, so no measurability question arises. $\square$

**Lemma II.5.14 (one-step bound for quiet steps; version 1.1, audit P2-02).** If the step is quiet in $Z'$, (S0) holds, $c_1\ge C_b$, $c_2\ge C_bB_0$ and
$\hat\lambda_k$ satisfies (Λ17′) of §II.1.3, then (S2) holds with $\kappa^{(k)}(Z',\mathfrak a)=-(c_1\log\beta_k+c_2)|Z^c_k\cap Z'|_{k+1}$ (no gain), for every $z_{k+1}>0$.

*Proof.* *Shell volume.* For $0<t\le\frac12$ the shell $\{u\in\mathbb R^N:\ |u\cdot u-1|<t\}$ has volume $v_N\big((1+t)^{N/2}-(1-t)^{N/2}\big)\le c_Nt$, $c_N:=Nv_N(\frac32)^{N/2}$
($v_N$ the volume of the unit ball; mean value theorem). *The new′ variables are confined to shells.* In the quiet step the new′ variables are
$\psi_{k+1}$ on the $(k+1)$-blocks of $\Omega_{k+1}\cap Z'$ and $\psi_k$ on the $k$-blocks of $Z^c_k\cap\Omega^c_{k+1}\cap Z'$ (no fluctuation variables). Each of these blocks is
a block of the multiscale field $\mathbb B_{k+1}$ inside a cube $\square$ to which $\chi^{\rm new}_k(Z')$ attaches a condition of (1.24): a $(k+1)$-block of $\Omega_{k+1}\cap Z'$ lies in a
$\pi_{k+1}$-cube $\square\subset\Omega^\sim_{k+1}\cap Z'$ (first family, $\psi\in\tilde\Psi(\mathbb B_{k+1}\cap\square^\sim;3dL\delta_k)$); a $k$-block of $Z^c_k\cap\Omega^c_{k+1}\cap Z'$ lies in a $\pi_k$-cube $\square$; if
$\square\cap\Omega^\sim_{k+1}=\varnothing$ the second family applies ($\psi_k\in\tilde\Psi(T_k(\square^\sim);3\delta_k)$), and otherwise the $\pi_{k+1}$-cube $\square'\supset\square$ meets the union of $\pi_{k+1}$-cubes
$\Omega^\sim_{k+1}$, hence lies in it, and the first family applies to $\square'$. Both spaces contain the condition $|\psi(y)\cdot\psi(y)-1|<3dL\delta_k$ for the block $y$ (BG (R2);
Definition II.3.4). So $\chi^{\rm new}_k(Z')\le\prod_{y\in\text{new}'}\mathbf 1[|\psi(y)\cdot\psi(y)-1|<3dL\delta_k]$, a function of the new′ variables only. *The majorant.* The main action is
$\ge0$ for real arguments, so $e^{-\mathcal A}\le1$; all other characteristic functions are $\le1$; $e^{{\rm Re}\,b_k}\le e^{(C_b\log\beta_k+C_bB_0)|Z^c_k\cap Z'|_{k+1}}$ by (S0). Hence
$$\tilde K_k\,e^{{\rm Re}\,b_k}\le S_k:=e^{(C_b\log\beta_k+C_bB_0)|Z^c_k\cap Z'|_{k+1}}\prod_{y\in\text{new}'}\mathbf 1\big[|\psi(y)\cdot\psi(y)-1|<3dL\delta_k\big]$$
for all values of the old variables, and $\int d(\text{new}')S_k\le e^{(C_b\log\beta_k+C_bB_0)|Z^c_k\cap Z'|_{k+1}}(3dLc_N\delta_k)^{\#\text{new}'}\le e^{(C_b\log\beta_k+C_bB_0)|Z^c_k\cap Z'|_{k+1}}$ by
(Λ17′). The Gaussian factorization of (S1) holds because the characteristic functions, the main action and $b_k$ read $\psi_{k+1}$ only on $\Omega_{k+1}$ (Definition
II.3.2, II.5.4, (S0)). Finally $c_1\log\beta_k+c_2\ge C_b\log\beta_k+C_bB_0$. $\square$

*Remark (audit P2-02).* Version 1 asserted that $\chi'_{k+1}$ and $\chi_{k+1}$ confine $\theta(y)$ to a ball of radius $\frac54\delta_k$. They do not: $|\theta-Q\phi'(\theta)|<\frac54\delta_k$ is a
self-consistent condition whose set contains, for every unit vector $v$, the constant configuration $v$ (the audit's example). The shell condition
of (1.24) is a condition on each variable separately and does not suffer from this; it makes the per-block volume $\le1$, so the term $2(L^d+1)$ of
version 1 in $c_2$ disappears. P6 (3.4)'s "$(O(1)\log\beta_k+{\rm const.}E_0)|Z^c_k\cap Z_{k+1}|$" is the corresponding estimate; the $\log\beta_k$ there comes from the
normalizations of the fluctuation integrals and from the vacuum constants, which here are in $b_k$.

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
$R_{\rm base}$, $p_0,p_2,A_0,\dots,A'_3$, $\alpha_0,E_0,B,\bar\nu$, $B_0,H_0,c_1,c_2,c_v,C_R$, $C_b$, $C_{\psi'}$), and $\beta,\nu,h$. For each admissible torus $\mathbb T=(\mathbb Z/\ell\mathbb Z)^d$
(version 1.2 (Part IV): $ML^{\hat k_f+1}\mid\ell$, (A-IV.3); version 1.1 wrote $ML^{k+1}\mid\ell$, on which the hypothesis (H-T) of LF-2 can fail), a **representation** $\mathrm{rep}=(\mathfrak s,\mathfrak A,\mathfrak D,\mathcal B)$ consists of:
- $\mathfrak s$ (*small-field data at scale $k$*): the running constants $(\beta_j,\nu_j)_{j\le k}$, $(z_j,E_j)_{1\le j\le k}$; the localized functions
  $\mathcal E^{(j)}(y,X;\cdot)$, $\mathcal M^{(j)}(x,X;\cdot)$ ($j\le k$, $X\in\mathcal D_j$) and $\mathcal R^{(k)}_n(X;\cdot)$ ($n\le m$, $L^m=M$, $X\in\mathcal D_k$), given on finite subsets of $\mathbb Z^d$ and
  pushed to the torus (SF §1.3 (H.4), P5 H4);
- $\mathfrak A$: **the set of all** admissible global region histories up to scale $k$ (Definition I.4.1, with the overwrite of Definition I.3.11), whose
  $R$-records at each scale $j\le\min(k,k_0)$ mark every ripe component of $Z^{\rm pre}_j$ as removed or as kept with a label from $\mathfrak K$; it is finite.
  (Version 1 said "a finite set"; completeness is P5's "maximal set of the multi-indices" (p. 494 [checked]) and is needed for the polymer
  expansion of $R$, Part III D-III.8, Lemma III.10.4. Histories whose operator vanishes are harmless.)
- $\mathfrak D$: for every localized history prefix occurring in $\mathfrak A$, the step data (S0)–(S1) of every step and the kept data (S3) of every kept
  component (Definition II.5.7), indexed by the localized prefix (so (S4) holds by construction);
- $\mathcal B$: for every $\mathbb A\in\mathfrak A$ the boundary terms $\mathcal B^{(k)}(X,\mathbb A;\psi,\psi',h,g)$, $X\in\mathcal D_k(\mathrm{mod}\,\Omega^c_k(\mathbb A))$ with $X\cap Z_k\ne\varnothing\ne X\cap Z^c_k$ (P5 (1.38)).

*Derived objects* (functions of rep; no further data): the bookkeeping of Part I (spines, clocks, window states, $t^*$, $\nu$, $U$, ripeness); the localized
and global operators $\mathbb T_k(Z,\mathfrak a)$, $\mathbb T_k(Z_k,\mathbb A)$ (Definition II.5.8); $\kappa_k$, $C_k$, $G_k$ (Definition II.5.11); the characteristic function
$\chi_k(Z^c_k)$ (Definition II.3.2); the restricted small-field functions of P5 (1.6)–(1.17) [checked]:
$$\mathcal A_k(Z^c_k;\psi_k,h):=-\beta_kA^*_k(Z^c_k;\psi_k,\phi_k)+\mathcal E_k(Z^c_k;\psi_k,h)-E_k|Z^c_k|_k,\qquad\mathcal E_k(Z^c_k):=\sum_{j=1}^k\mathcal E^{(j)}(Z^c_k;\psi^{(j)}_k,h),\tag{1.6–1.7}$$
$$\mathcal E^{(j)}(Z^c_k;\psi_j,h):=\sum_{y\in Z^c_k\cap T^{(j)}}\ \sum_{X\in\mathcal D_j:\,y\in X\subset(Z^c_k)^{\approx}}\mathcal E^{(j)}(y,X;\psi_j,h)-\sum_{y\in Z^c_k\cap T^{(j)}}\ \sum_{x\in(Z^c_k)^{\approx}\cap T^{(j)}}\Big[\tfrac12v^{(j)}_1(y,x)(\psi_j^2(x)-\psi_j^2(y))+v^{(j)}_2(y,x)\big(\nu_jh\cdot(\psi_j)_0(x)-\nu_jh\cdot(\psi_j)_0(y)\big)\Big],\tag{1.8}$$
with $v^{(j)}_{1,2}$ determined by $\mathcal E^{(j)}$ on the whole lattice through P1 (3.106) [review]; $\phi_k$, $\psi^{(j)}_k$ of Definition II.2.7 (iii) (mass $\mu_k$, so $\nu$-free
when $k\le k_0$ in the operative flow, P5 (1.9)); $A^*_k(Z^c_k;\psi_k,\phi_k)$ the single-scale action (generating set $T^{(k)}_1$, weight $a_k$) with half bonds on ${\rm st}(Z^c_k)$ (P5 (1.5));
$$\mathcal F_k(Z^c_k;\psi_k,h,g):=\langle\chi_{Z^c_k}g,\phi_k\rangle_1+\sum_{j=1}^k\langle\chi_{Z^c_k}g,\mathcal M^{(j)}(Z^c_k;\psi^{(j)}_k,h,g)\rangle_1,\quad\mathcal M^{(j)}(x,Z^c_k):=\sum_{X\in\mathcal D_j:\,x\in X\subset(Z^c_k)^{\approx}}\mathcal M^{(j)}(x,X);\tag{1.10–1.13}$$
$$\mathcal R^{(k)}(Z^c_k;\psi_k,h,g):=\sum_{n=1}^m\ \sum_{X\in\mathcal D_k:\,X\subset Z^c_k}\mathcal R^{(k)}_n(X;\psi_k,h,g).\tag{1.16–1.17}$$

### II.6.2 The predicate

**Definition II.6.2 (Def-7: $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep},\rho)$, $1\le k$).** A family $\rho=(\rho^{(\ell)})$ of functions $\rho^{(\ell)}_k(\psi_k;h,g)$ over admissible tori and a family of
representations satisfy $\mathrm{IsRep}_k$ iff on every admissible torus:
- **(D1) Form** (P5 H1, (1.1), (1.21) [checked]). For all real $\psi_k$ and all complex $g$ with $\|g\|_{\ell^1}<1$,
  $$\rho_k(\psi_k;h,g)=\sum_{\mathbb A\in\mathfrak A}\mathbb T_k(Z_k(\mathbb A),\mathbb A)\Big[e^{\mathcal B^{(k)}(\mathbb A)}\,\chi_k(Z^c_k)\,\exp\big(\mathcal A_k+\mathcal F_k+\mathcal R^{(k)}\big)(Z^c_k)\Big],\qquad\mathcal B^{(k)}(\mathbb A):=\sum_X\mathcal B^{(k)}(X,\mathbb A),$$
  the operator integrating the internal variables (Definition II.5.2), with absolutely convergent integrals.
- **(D2) Small-field data** [v1.3: F-1]: $\mathfrak s$ satisfies Def-6 at scale $k$ (SF §1.3, §1.6 with the author-accepted correction in FLUCTUATION §1.4: (H.1)–(H.7) in P4's numbering, P5's conventions (1.8)–(1.9), the
  free flow (II.1), and analyticity of each local $\mathscr E^{(j)}(y,X)$ and $\mathscr M^{(j)}(x,X)$ on $\Xi^c_j(\mathbb B_j(X);1,\varepsilon_j)$), and the $\mathcal R^{(k)}_n$ satisfy P5 H4 ((1.14)–(1.15) symmetries, localization
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
  arguments, analytic on the H7 domain at $X$ (Definition II.3.5 (d)), bounded there by $|\mathcal B^{(k)}(X,\mathbb A)|<B_0e^{-\kappa d_k^{\rm cov}(X\,\mathrm{mod}\,\Omega^c_k)}$, jointly
  $O(N)$-covariant in $(\psi,\psi',h,g)$ and invariant under the Euclidean symmetries of the torus preserving $\pi_k$ (P5 H5).
- **(D8) Torus coherence** (roadmap §3.5; ARCH (D8)): every localized datum — $\mathcal E^{(j)}(y,X)$, $\mathcal M^{(j)}(x,X)$, $\mathcal R^{(k)}_n(X)$, the step and kept data of
  a localized history, $\mathcal B^{(k)}(X,\mathbb A)$ — whose support (the set $X$, resp. $V_Z$ of the final component together with the lineage) lies in the image of a box
  $\{y\in\mathbb Z^d:|y_\mu-c_\mu|<\ell/4\ \forall\mu\}$ (version 1.2 (Part IV), D-IV.9: side $<\ell/2$, Root-F's agreement box; version 1.1 had "a cube of side $<\ell/4$") is the push-forward of a
  datum attached to the corresponding finite subset of $\mathbb Z^d$, the same for all admissible tori containing such an image (the map of the box to the torus is injective and
  preserves adjacency and the sup-distance); the step data of the quiet steps satisfy this automatically.
- **(D9) Coefficients** (P5 (1.42), Theorem 1): $\beta_k>BL^{k(d-2)}$, $0<\nu_k\le\bar\nu$, and $k\le k_0$ (version 1.2, D-IV.11: so $\beta_k\nu_k\le e^{2\epsilon}$; version 1.1: $\beta_k\nu_k\le1$).

$\mathcal R_k(\mathsf c):=\{\rho:\exists\,\mathrm{rep},\ \mathrm{IsRep}_k(\mathsf c,\mathrm{rep},\rho)\}$ (ARCH R3-10).

### II.6.3 Variants

- $\mathrm{IsRep}^{\rm pre}_k$ (the image of $S^{(k-1)}T^{(k-1)}$ before $R^{(k)}$; ARCH §3.6): as $\mathrm{IsRep}_k$ with $Z^{\rm pre}_k$ in place of $Z_k$ (no $R$-record
  at scale $k$, operators $\mathbb T^{\rm pre}_k$), and (D6) replaced by (H6′)$^{\rm pre}$: $t^*(Z)\ge k$ and $G^{\rm pre}_k(Z)\ge\tau_{t^*(Z)}+V_k(Z)+\nu(Z)+U(Z)$ for every
  component of $Z^{\rm pre}_k$ (ripe components allowed). *(Part III, D-III.4.)* Its (D7) holds with $\kappa_+:=\frac32\kappa$ in place of $\kappa$ and with $B_{\rm st}$ in place
  of $B_0$, where $B_{\rm st}$ is the constant of the boundary terms created by a step, which does not depend on $B_0$ (P5 Theorem 1, p. 499 [checked]:
  "(H.2), (H.3), (H.4), (H.7) are satisfied with the constant $\frac32\kappa$ instead of $\kappa$ for functions with the superscript $j=k+1$"; P6 p. 15 [checked]:
  "contributions to $\mathcal B^{(k+1)}$ ... have bounds independent of $B_0$"). This is an obligation on LF-3; $B_0\ge B_{\rm st}+1$ is row 12 (Lemma III.10.7).
  Its (D2) requires $\mathcal R^{(k)}_m$ to satisfy P5 H4 with the bound $\frac12\beta_k^{-m-1}$ in place of $\beta_k^{-m-1}$ (P5 Proposition 3.2, p. 517 [checked]: "the bounds
  (3.4) with $\frac12\beta_k^{-m-1}$"), so that $R$ can add $\mathcal R''^{(k)}_m$ (P5 p. 491 [checked]: "the sum of the two satisfies all the properties and bounds required
  by Hypothesis (H.4)"); also an obligation on LF-3 (Part III, Theorem III.10.8 (c)).
- $\mathrm{IsRep}^\flat_k$ ($k_0\le k\le k_f$; ARCH §3.6; version 1.1, audit P2-01): as $\mathrm{IsRep}_k$ except that
  (i) there are no window data and no $R$-records at scales $>k_0$;
  (ii) the backgrounds at scales $j>k_0$ carry the mass $\mu_j=\nu_jL^{-2j}$ (complete backgrounds, P5 p. 490, P6 p. 2), and the characteristic functions at
  scales $>k_0$ contain the $h$-conditions;
  (iii) (D2) is replaced by **(D2♭)**: $\mathfrak s$ satisfies the clauses (H.1)–(H.7) of Def-6 at scale $k$ verbatim (SF §1.3), read for scales $j>k_0$ in P4's
  convention with complete backgrounds (SF §1.6 item 1 is applied only to the scales $j\le k_0$), and the mass range of the "Space" clause of SF §1.3,
  $0<\nu_k\le\bar\nu$ with $\bar\nu\le\frac78L^{-2}$, is replaced by $0<\nu_k\le1$; the $\mathcal R^{(k)}_n$ satisfy P5 H4 as in (D2);
  (iv) (D9) is replaced by **(D9♭)**: $\beta_k>BL^{k(d-2)}$ and $0<\nu_k\le1$;
  (v) (D6) is replaced by
  $$\text{(H6}^\flat)\qquad G_k(Z,\mathbb A\cap Z)\ \ge\ A_2\hat\lambda_{k_0}^{p_2}+2\sigma_k\ell(\Gamma(Z))+W_{k+1}(\hat k_f)$$
  for every component (spines and clocks continue in the frozen regime, Part I §I.4.4 (T7)); for the conventional $k_0=0$ the threshold is
  $A_2\hat\lambda_0^{p_2}\ge p_2(\beta)$. This is the only place where $\hat k_f(\nu)$ enters Def-7 (§II.1.4).
  *Which clauses used $\nu\le\bar\nu$ (audit P2-01).* In Def-6 the bound $\nu_k\le\bar\nu\le\frac78L^{-2}$ occurs only in the "Space" clause of SF §1.3; the clauses
  (H.1)–(H.7) are stated for every $\nu_k>0$, and their $\nu$-dependent domain conditions ($|\phi-h|<\sigma\varepsilon/\sqrt\nu$, $\nu||h|^2-1|<\sigma^2\varepsilon^2$, and (R3), (R4),
  (C3) of BG §1.3) are uniform for $\nu\in(0,1]$. The bound $\nu_k\le\frac78L^{-2}$ is a hypothesis of the step $k\to k+1$ (I-9, SF §5.1, P4 Theorem 1, P5
  Theorem 1), not of the class. Version 1 imported it through (D2), which made $\mathrm{IsRep}^\flat_{k_f}$ empty since $\nu_{k_f}>\frac78L^{-2}$.
  *Preservation.* For $k_0\le k<k_f$, $\nu_k\le\frac78L^{-2}$ by the definition of $k_f$, so the step (LF-5, with I-9 at $\bar\nu=\frac78L^{-2}$) applies to $\mathrm{IsRep}^\flat_k$;
  its output has $\nu_{k+1}=\nu_kL^2\frac{1+\xi_3}{1+\xi_2}\le\frac78e^{c_\xi/\beta}<1$ (P4 (5.28), SF Theorem 5.3), so (D9♭) holds at $k+1$, in particular at $k+1=k_f$; at
  $k_f$ no step is applied (LF-8 consumes $\mathrm{IsRep}^\flat_{k_f}$). The switch of convention at $k_0$ is part of LF-5's step at $k_0$ (ARCH §3.7, Part IV),
  and the compatibility of Def-6 with complete backgrounds is SF's requirement R-ν (open item O-II-2); neither is changed here.

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

**Definition II.6.4 (the continuous family class $\mathrm{IsRepFam}_k$; version 1.1, audit P2-03; superseded by Definition IV.3.1 in version 1.2, D-IV.8).** $\mathrm{IsRep}_k$ is a predicate at fixed $\nu$ and puts no relation
between the data at different $\nu$; the audit's example (multiply a kernel by $1+\epsilon\sin(1/\nu)$) satisfies it and has no limit at $\nu=0$. The observable limit
(OBSERVABLES §4.2 (5)) and LF-7 therefore use the following family class. Fix $\beta$, $h$, the constants, $k\ge1$, and $\nu_*(k)>0$ with $\beta_k(\nu)\nu_k(\nu)\le1$
for $\nu\in(0,\nu_*(k)]$ (it exists by (I.2)). A family $(\mathrm{rep}(\nu),\rho(\nu))_{0<\nu\le\nu_*(k)}$ satisfies $\mathrm{IsRepFam}_k$ (resp. $\mathrm{IsRepFam}^{\rm pre}_k$) iff
- (F-i) $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep}(\nu),\rho(\nu))$ (resp. $\mathrm{IsRep}^{\rm pre}_k$) for every $\nu$;
- (F-ii) the history set $\mathfrak A$ does not depend on $\nu$ (it is the set of all admissible histories; the bookkeeping uses $\hat\lambda$, which does not depend
  on $\nu$, and all scales $\le k$ are $\le k_0(\nu)$);
- (F-iii) **(CONT$^{\rm LF}$)** for every localized prefix, each datum — the step kernels and boundary factors $(K_j,b_j)$, $j<k$, the kept kernels $(K'',b'')$,
  the boundary terms $\mathcal B^{(k)}(X,\mathbb A)$, and the small-field data $\mathfrak s$ — depends on $\nu$ through the running constants $(\beta_j,\nu_j,z_j,E_j)_{j\le k}$
  and the variable $b=\nu h$ only; for almost every value of the internal and output variables (for the reference measure) and every value of the
  complex arguments in the analyticity domains (which do not depend on $\nu$ for $k\le k_0$: no $h$-condition occurs), it is a continuous function of
  $\nu\in(0,\nu_*(k)]$ with a limit as $\nu\downarrow0$; and the bounds (S0)–(S3), (S5), (D7) hold uniformly in $\nu\in(0,\nu_*(k)]$ (uniform domination);
  for $\mathfrak s$ this is SF's (CONT) (SF §3.5, Theorem 5.3).
Continuity in $\nu$ is distinct from analyticity in $g$, which holds for each fixed $\nu$. "Almost every" is needed because the thresholds $\delta_j$ of the
characteristic functions depend on $\nu$ through $\beta_j(\nu)$; dominated convergence then gives continuity of all operators and of $\rho(\nu)$. LF-3 and LF-4
must map $\mathrm{IsRepFam}_k$ to $\mathrm{IsRepFam}^{\rm pre}_{k+1}$, resp. $\mathrm{IsRepFam}^{\rm pre}_k$ to $\mathrm{IsRepFam}_k$; their data are explicit formulas in the input data
with uniformly dominated integrals (for LF-4: Theorem III.10.8 (f)). LF-7 and the observable induction use $\mathrm{IsRepFam}$.

### II.6.4 What Def-7 changes in the interfaces of ARCH §3.7, §8.3

- **LF-3** (one step, $1\le k<k_0$): *for every* $\mathrm{rep}$ with $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep},\rho)$ there is $\mathrm{rep}'$ with $\mathrm{IsRep}^{\rm pre}_{k+1}(\mathsf c',\mathrm{rep}',S^{(k)}T^{(k)}\rho)$, whose
  histories extend those of $\mathrm{rep}$ by a step record, whose step data at the new step are constructed (non-quiet kernels from P5 (2.47),
  P6 (3.2) with the local background; boundary factors from P6 (2.32)–(2.33), (3.3) and the background change of Lemma II.5.9's route), and whose
  small-field data are the image under P4 Theorem 2 with the free flow. (D6) for $\mathrm{rep}'$ is LF-2 (i). The operator bound (S2) for the
  non-quiet steps is P6 (3.4)–(3.9) with the local background (LF-1 applies to it).
- **LF-4** ($R$) [v1.3: P4-01]: the operative hypothesis is $\mathrm{IsRep}^{\rm pre}_k(\mathsf c,\mathrm{rep},\rho)$ and $1\le k\le k_0$ for the a priori index, hence $\beta_k\nu_k\le e^{2\epsilon}$ (ARCH §8.3 also required $\mathrm{rep}$ to be "the output of LF-3",
  which named a construction; with D-II.2 the window operators are explicit in every representation). The conclusion produces kept data (S3)
  for the kept components and removes the others; (Rg) of LF-2 is then $G''_k=G^{\rm pre}_k-C_R\hat\lambda_k^{2d+1}+\gamma-\log C_{\rm dec}\ge G^{\rm pre}_k-C_R\hat\lambda_k^{2d+1}+A'_3\hat\lambda_k^{p_R}$,
  an identity plus (S3).
- **LF-5, LF-6, LF-7, LF-8**: unchanged in form; they read $\mathcal R_k$, $\mathcal R^{\rm pre}_k$, $\mathcal R^\flat_k$ as defined here.

### II.6.5 The external field $g$ and the limit $\nu\downarrow0$ (OBSERVABLES §4.2, received during the writing)

1. *$g$ is an analytic parameter of every object.* Kernels are $g$-independent and non-negative; $g$ enters only through the step and kept
   boundary factors (S0), (S3), the boundary terms (D7) and the small-field functional $\mathcal F_k$ (D2), all analytic on $\|g\|_{\ell^1}<1$. The hard-spin
   factor $e^{\langle g,\phi\rangle}$ of the large-field sites of scale $0$ enters $b_0$ with $|\langle g,\phi\rangle|\le\|g\|_{\ell^1}\le1$ (§II.7). **The operators therefore depend on $g$**
   (through $e^b$), as in P5 H5; this is the convention of LF-3 and LF-4 (Definition II.5.2, audit P2-04). The observable argument must differentiate them
   (open item O-II-9).
2. *Joint covariance of $R''$*: required of the kept data in (S3) and of the new small-field terms by (D2); P7's coset average (M4) is taken on the
   full integrand, and joint covariance holds (Part III, Lemma III.9.6; O-II-5 closed).
3. *Locality in $g$*: (S0), (S3), (D7) require dependence on $g$ restricted to $V_Z$, resp. $X$.
4. *Sup bounds on the complex polydisc*: (1.26) (Definition II.5.2), (S0) and (D7) are stated for all complex $\|g\|_{\ell^1}<1$.
5. *$\nu\downarrow0$ and the horizon*: no object of Def-7 uses $\hat k_f(\nu)$ (§II.1.4); the bookkeeping uses $\hat\lambda$ (a function of $\beta$); for fixed $k$ and
   $\nu<\nu_*(k)$ with $\nu_*(k)=\beta^{-1}L^{-kd}$ all scales $j\le k$ are in the regime $j\le k_0$, where the backgrounds are $\nu$-free and $\nu$ enters
   only through the running constants and the $\nu$-term of the actions. $\mathrm{IsRep}_k$ is a predicate at fixed $\nu$; continuity of the large-field
   data in $\nu$ is the family clause (CONT$^{\rm LF}$) of Definition II.6.4 (version 1.1, audit P2-03), which LF-3 and LF-4 must preserve (open item O-II-6).
P9's marked polymer expansion PE-M with large-field holes is a Part IV / POLYMER item; nothing in Def-7 obstructs it (the large-field
operators are local and their bounds are of the form used by PE).

*Pointer (version 1.2).* §II.7 (LF-6, the base case) was written with Part IV and is placed after §IV.0, at the end of this document. Definition II.6.4 is
replaced by Definition IV.3.1 (D-IV.8).

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
| Defs. II.1.1, II.2.1, II.2.2, II.2.4, II.2.7, II.3.1–II.3.5, II.5.1, II.5.2, II.5.4–II.5.8, II.5.11, II.6.1–II.6.2, II.6.4 and the variants | definitions (sources [checked] as marked); II.5.7 (S1)–(S5), II.6.1, II.6.3, II.6.4 amended in version 1.1 (§II.O.5) |
| Lemma II.1.2 | proved here from (I.2) (landed Lean) |
| Lemmas II.2.3, II.2.5, II.2.6 | proved here (II.2.6 uses BG's (EL) and domains; the uniqueness statement is BG Theorem 5.2, proved on paper) |
| Remark II.2.8 (backgrounds evaluated only on the domain; identification with P5–P6) | the identification is cited (P5 (2.7), (2.10), P6 (2.6), P1 Lemma 3.1); not needed by Def-7 |
| Lemma II.3.3 | proved here |
| Theorem II.4.1 (LF-1), Lemmas II.4.2–II.4.3 | proved here ($\gamma_0=1/(28d)$; Lemma II.4.3 from the landed `blockPoincare_sharp`) |
| Lemma II.5.3, II.5.9 (structural Lemma F), II.5.10 | proved here |
| analytic half of Lemma F (background change into $b_k$ and $\mathcal B$) | cited route (P6 (2.12)–(2.17), LOC I-4b, I-5, Lemma AE); LF-3's proof; conditional on LOC's open items (O-2′) |
| Lemma II.5.12 (Lemma B), II.5.15 ((1.27)) | proved here (survived the audit) |
| Lemma II.5.13, II.5.14 | proved here in version 1.1 (proofs rewritten after audit findings P2-06, P2-02: integration order with the uniform majorant of (S2); shell volumes from (1.24)) |
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
- **O-3 (Lemma L (c), (3.11)′).** **Closed in Part III** (D-III.1, Lemma III.9.1: local sets $U,W$ of the ripe lineage).
- **O-4 (range of P3's minimal generating sets).** **Closed**: range $1$ cube (Lemma II.2.3 (c)).
- **O-5 ($\pi'$ offsets; adjacency of components of $\Omega^c$ in P5 (1.33)).** Open; neither affects the form of Def-7 (both enter only the summability
  (1.35) with a constant $K_0$, to be fixed in Part III/IV).
- **O-6 (Lemma B at hulls; base rule).** Hull half **closed** (Lemma II.5.12). Base rule ($k=0$: sets $\mathsf P_1,\dots,\mathsf S_1$, the step data at $k=0$ with
  spin variables, (S2) with the gain $\kappa^{(0)}$, and $b_0\ni\langle g,\phi\rangle$): §II.7.
- **O-7 (constant order).** **Closed** in Part I v1.1.
- **O-8′ (free flow versus $c=0$; replaces O-8).** The exact composition of the window transformations (P7 p. 499, (2.7), (2.9), (2.55), (2.57)) uses
  P5's $c=0$ and ignores the field renormalizations $z_j$. **Closed in Part III** (Lemmas III.1.6, III.1.7, III.6.3; audit P2-05): the actual composed transformation
  is computed exactly and the complete action difference, with its linear part and the factor $\beta_k$, is controlled: $\frac38$ of the composed-Gaussian
  term absorbs the linear part, the rest is $\le1$ on the real domain and $\le C_\natural\hat\lambda_k^{2d+1}$ on the complex domain (part of $L_{\rm res}$).
- **O-9, O-10.** Unchanged.
- **O-II-1 (Def-5 in Lean).** **Closed** since version 1: `bgField`, `bgFieldC`, `theorem71`, `theorem72` (`Background/Def5.lean`), I-2 `theorem73_real`,
  `theorem73_system`, `theorem73_perturb`, BG Lemmas 6.2/6.3 (`lemma62`, `lemma63`, W28) and I-1(e) (W33b) are landed (ledger, 2026-10-11).
- **O-II-2 (Def-6).** (D2) is Def-6; SF's open requirement R-ν (the RG equations with $\nu$-free backgrounds) must be settled before Def-7 is frozen.
- **O-II-3 (new errata candidates).** N-II-1: P6 (3.2) prints $(\Omega''^c_{k+1})^{\sim3}\cap\mathsf S_{k+1}$ where p. 4 has $\cup$ (Definition II.5.6). N-II-2: P7 p. 499 cites
  "(1.36), (1.37) [4]", which do not exist in P4; read as P5 (1.40)–(1.41). N-II-3: the index of the fluctuation variables (P5 p. 492 versus P6
  p. 5). Minor: P5 (1.19) prints $|h^2-1|<\delta^2_k/\sqrt{\nu_k}$; whether P6 (3.2)'s background is evaluated at $\psi_{k+1}$ or $\theta=z_{k+1}\psi_{k+1}$.
- **O-II-4 (constants of the small-field step).** $C_b$ (P6 (2.33) "const.") and $C_{\psi'}$ (P5 (1.25) "const.") are outputs of LF-3, chosen with row 11;
  $c_1\ge C_b$, $c_2\ge C_bB_0$ (row 14, version 1.1) and the refund constants $c_1\ge C_W$, $c_2\ge C'_W$ of §III.8.2 are in the chain.
- **O-II-5 (kept data from P7).** **Closed in Part III** (§III.8, Lemma III.9.6): the kept kernels K1, K2 have the form (S3) with $I''$ (D-III.9), the coset
  average is taken on the full integrand, and joint covariance holds.
- **O-II-6 ($\nu\downarrow0$).** Version 1.1 adds the family class $\mathrm{IsRepFam}_k$ with (CONT$^{\rm LF}$) (Definition II.6.4, audit P2-03). Open: LF-3 must
  preserve it (Part IV); LF-4 does (Theorem III.10.8 (f)).
- **O-II-7 (torus coherence of constructed data).** LF-3 and LF-4 must construct their step and kept data from finite-set objects so that (D8) holds;
  by Lemma II.5.9 they are local, so this is a matter of stating the constructions on $\mathbb Z^d$.
- **O-II-8 (row 3 of the constant chain).** The conditions G-1–G-6 on $L$ are still to be written as $L\ge L_i(d)$ (Part I row 3, UNCERTAIN); Part II added
  no condition on $L$ beyond $L^d\ge8$ (Lemma II.5.15) and $\varrho\ge2dL$ (LF-1, implied by $R_0(d,L)\ge4dL$).
- **O-II-9 ($g$ in the operators; audit P2-04).** The operators of Def-7 depend on $g$ through $e^b$ (Definition II.5.2, P5 H5). `OBSERVABLES.md` §4.1 (L4)
  ("$\mathbb T_k$ does not depend on $g$") must be replaced: the derivatives in $g$ of the large-field part are bounded by Cauchy estimates from the sup bound
  (1.26) on the polydisc, and the observable reduction must include these terms. This is a change to `OBSERVABLES.md`, not to Def-7.
- **O-II-10 (frozen class; audit P2-01).** Closed by (D2♭), (D9♭) of §II.6.3. LF-5 must prove the switch of conventions at $k_0$ (Part IV).

### II.O.5 Version 1.1: fixes after `LFR-PART2-AUDIT-astra.md` and amendments required by Part III

| Finding | Fix | Where |
|---|---|---|
| P2-01 (BLOCKER) $\mathrm{IsRep}^\flat_{k_f}$ empty | (D2♭): Def-6 clauses (H.1)–(H.7) verbatim, complete backgrounds above $k_0$, mass range $0<\nu_k\le1$; (D9♭); list of the clauses that used $\nu\le\bar\nu$ (only the "Space" clause); preservation for $k_0\le k<k_f$ | §II.6.3 |
| P2-02 (MAJOR) volume argument of Lemma II.5.14 | per-block shell condition of (1.24) (in $\chi^{\rm new}$), volume $\le c_N\cdot3dL\delta_k\le1$ by (Λ17′); $c_2\ge C_bB_0$ (the term $2(L^d+1)$ disappears); valid for every $z_{k+1}>0$ | Lemma II.5.14, §II.1.3, row 14 |
| P2-03 (MAJOR) $\nu$-discontinuous data | family class $\mathrm{IsRepFam}_k$ with (CONT$^{\rm LF}$): $\nu$-dependence through the running constants and $b=\nu h$, a.e. continuity with limits at $\nu=0$, uniform domination; LF-3, LF-4 must preserve it | Definition II.6.4, §II.6.5 item 5 |
| P2-04 (MAJOR) $g$ in operators vs OBSERVABLES (L4) | convention stated: operators depend on $g$ through $e^b$ only (P5 H5); (L4) must be replaced in `OBSERVABLES.md` (O-II-9) | Definition II.5.2, §II.6.5 item 1 |
| P2-05 (MAJOR) O-8′ route | the claim of a quadratic $O(\beta^{-1})$ remainder withdrawn; perturbative composition lemma with linear residual, $\beta_k$ factor and field renormalizations: Part III Lemmas III.1.6, III.1.7, III.6.3 | §II.1.5, O-8′ |
| P2-06 (MINOR) integration order in Lemma II.5.13 | (S2) restated with the Gaussian factorization and a majorant uniform in all old variables; proof integrates the Gaussian variables, then the old variables (ancestor bounds with $F\equiv1$), then the new′ variables; reduction of (1.26) to $F\equiv1$ by the support property | (S1), (S2), Definition II.5.2, Lemma II.5.13 |
| §I.7.2 stale "(Λ0)–(Λ13)" | corrected | §I.7.2 |
| Part III D-III.4 | $\mathrm{IsRep}^{\rm pre}_k$'s (D7) with $\kappa_+=\frac32\kappa$ and $B_{\rm st}$; its (D2) with $\frac12\beta_k^{-m-1}$ for $\mathcal R^{(k)}_m$ | §II.6.3 |
| Part III D-III.6 | (S5) rotation form; $K$ may depend on $h$ | Definitions II.5.2, II.5.7 |
| Part III D-III.8, D-III.9 | $\mathfrak A$ = all admissible histories; kept kernels on $I''\subset I$ | Definitions II.6.1, II.5.7 (S3) |

The lemmas that survived the audit (II.1.2, II.2.3, II.3.3, II.4.1–II.4.3, II.5.3, II.5.12, II.5.15) are unchanged. The audit's conditional verdicts on
II.2.5 (v) (the buffer argument for $W_k\cap U_{Z'}$) and II.5.9 (d) are answered as follows. *II.2.5 (v).* $G^{Z'}_{k+1}$ is the family of (iv) with $W_k$, $U_{k+1}$ replaced
by $X':=W_k\cap U_{Z'}$ (a union of $\pi_k$-cubes) and $U_{Z'}$. Let $x\notin\Omega_n(G^{Z'})$, $y\in\Omega_{n+1}(G^{Z'})$. If $x,y$ lie on the same side of $\partial\Omega_{k+1}$, the separation
is that of the generating set $\mathbb B_k(X')$, resp. $\mathbb B_{k+1}(U_{Z'})$ (Lemma II.2.3 (a), valid for every union of cubes). If $y\in\Omega_{k+1}$ and $x\in\Omega^c_{k+1}\setminus\Omega_n(X')$:
either $x\notin W_k$, and the argument of (iv) applies, or $x\in W_k\setminus U_{Z'}$; then $x\in\Omega^c_{k+1}\subset Z^{\rm pre}_{k+1}$ lies in another component, at distance $\ge\omega_{k+1}-([R_k]+2)$
cubes of side $ML^{k+1}$ from $U^{\sim1}_{Z'}\supset\Omega_{n+1}(G^{Z'})$. If $y\in\Omega^c_{k+1}$ and $x\in\Omega_{k+1}\setminus\Omega_n(U_{Z'})$: $y\in X'^{\sim1}\cap\Omega^c_{k+1}$ lies in $Z'$ (other components are
far), and $x\notin U_{Z'}\supset(\Omega^c_{k+1}\cap Z')^{\sim([R_k]+1)}$ (since $\Omega_n(U_{Z'})\supset U_{Z'}$), so the distance is $\ge([R_k]+1)ML^{k+1}$. All these exceed $\varrho_3L^n$ under (RH).
*II.5.9 (d)* follows from the rewritten Lemma II.5.13.


---
---

# Large-field reconstruction document, Part III: $R$ on covered windows (LF-4)

Version 1 (Part III, sections III.0–III.10, III.L, III.O), 2026-10-12. Brief: `orchestration/briefs/D-LFR-partIII.md`. Input: Parts I
(version 1.1) and II above; ARCH v4 §3.8 (Steps 0–6, Lemma CH, Lemma L), §8.3, §9; `LF-V4-AUDIT-astra.md` (V4-01), REV3 (R3-03);
`OBSERVABLES.md` §4.2 (cited as **OBS**), `POLYMER.md` (**PE**), `SMALLFIELD.md` (**SF**), `BACKGROUND.md` (**BG**). P7 was re-read for this
Part in its text layer, pp. 495–529; displays whose symbols the text layer drops ($\Omega$, $\Psi$, $\Delta$, $\Lambda$) were reconstructed from
context and are tagged [checked, text layer]. Status: draft for independent review; nothing here is approved or frozen. Tags, status
words and the UNCERTAIN convention are those of Parts I–II.

**Purpose.** Part III constructs the large-field renormalization operation $R^{(k)}$ on the ripe components of a representation
(Def-7, §II.6), proves the internal lemma LF-4R (the hypothesis (Rg) of LF-2), and states and proves LF-4 in the existential form of
ARCH §8.3 as amended by Part II §II.6.4 and [v1.3: P4-01]: the hypotheses are $\mathrm{IsRep}^{\rm pre}_k$ and $1\le k\le k_0$. It follows the outline of
ARCH §9 (III.1–III.10). P7's argument is cited page by page where it is used unchanged; every estimate that changes because the
window contains up to $\nu_{\max}$ merged pieces, because the flow is the free flow, or because the bookkeeping is that of Part I, is
written out.

## III.0 Setting, design decisions, summary

### III.0.1 Standing assumptions of Part III

Throughout Part III:

- **(A-III.1)** The constants of the prefix §I.1.4 are fixed up to row 15, $\hat\lambda_0\ge\lambda_*$ with $\lambda_*$ satisfying the conditions of
  §I.5.3, §II.1.3 and §III.O.3, and $\beta\ge\beta_0$.
- **(A-III.2)** [v1.3: P4-01] $1\le k\le k_0$ for the a priori $k_0$ of D-IV.11. Then (I.2) gives $\beta_j\nu_j\le e^{2\epsilon}$ for all $j\le k$. The backgrounds at scales $j\le k$ are massless by convention, no characteristic function there contains an $h$-condition, and (H-T) is Lemma IV.3.3(d). The factor $e^{2\epsilon}$ is paid explicitly in Lemmas III.6.4 and III.8.2 and in (Λ25).
- **(A-III.3)** $\mathrm{rep}=(\mathfrak s,\mathfrak A,\mathfrak D,\mathcal B)$ is a representation with $\mathrm{IsRep}^{\rm pre}_k(\mathsf c,\mathrm{rep},\rho)$ (Definition II.6.2 and §II.6.3, with the
  amendments of §III.0.3), on a fixed admissible torus; everything below is done on each admissible torus separately and is local
  (proof of Theorem III.10.8 for (D8)).

All bookkeeping (radii, widths, windows, ripeness, $h_j$, $\nu_{\max}$, $\hat W$) uses $\hat\lambda$ (ARCH R3-06); the running constants
$\beta_j,\nu_j,z_j$ enter only the analytic objects. Constants named $C,C',\dots$ depend only on rows 0–15 of the chain; every condition of
the form "$\beta$ large" is written as a condition on $\lambda_*$ and collected in §III.O.3.

### III.0.2 Notation for one ripe component

Fix a global history $\mathbb A\in\mathfrak A$ and a ripe component $Z$ of $Z^{\rm pre}_k(\mathbb A)$ (Definition I.4.6), with localized history
$\mathfrak a=\mathbb A\cap Z\in\mathfrak H_k(Z)$. As in P7 p. 498 [checked] ("we assume that $Z_k=Z$, so that these intersections are equal to $Z_j$,
$\mathbb A_k$, etc."), **all sets below are intersected with $Z$ as fine sets**, i.e. they are the sets of the localized history (Definition
I.4.4), and are written without the intersection. In particular:

| Symbol | Meaning |
|---|---|
| $q=q(Z)$, $k_1$ | the core scale of the Active state of $Z$; $k_1:=q$ (Lemma III.1.2 (a): $k_1=k_1(k)$ of §I.1.2), $n_1:=k-k_1$ |
| $s=s(Z)$ | the smallness clock (Definition I.4.6) |
| $\mathrm{Lin}_j$, $\mathcal C_*$ | the lineage $\mathrm{Lin}_j(Z)$, $k_1\le j\le k$; the core components $\mathcal C_*:=\mathrm{Anc}_{k_1}(Z)$ (components of $Z_{k_1}$) |
| $Z_j$ | $\mathrm{Lin}_j$ for $k_1\le j<k$, and $Z_k:=Z$ (P7's convention) |
| $X_j$ | the new region of the step $j\to j+1$: $X_j:=Z^c_j\cap Z_{j+1}$, $k_1\le j<k$; the *window region* $X_{\rm win}:=\bigsqcup_jX_j=Z\setminus Z_{k_1}$ |
| $\Omega_j,\Omega''_j$ | the localized domains; on $X_j$ the step is quiet, so $\Omega'_{j+1}=\Omega_{j+1}=\Omega''_{j+1}$ (Lemma III.1.2 (b)) |
| $\Lambda_j$ | the layer $(\Omega_j\setminus\Omega_{j+1})$ of the localized generating set $\mathbb B_k$, $k_1\le j<k$; $\Lambda_k:=\Omega_k$ |
| $U,\ W$ | the **local** core sets $U:=\bigcup_{C\in\mathcal C_*}C^{\approx}$, $W:=(Z^c_{k_1})^{\approx2}$, at scale $k_1$ (ARCH writes $U_{k_1},W_{k_1}$; by V4-01 only the local sets occur) |
| $\delta_j,\ \delta_{j,1},\ \varepsilon_j$ | $\delta_j=(\beta_ja)^{-1/2}p_0(\beta_j)$, $\delta_{j,1}=\frac{A_1}{A_0}\delta_j$ (P7 (2.61)), $\varepsilon_j$ of Definition II.1.1 |
| $\lambda_j$ | the running $\log(\beta_ja)$ (Definition II.1.1); $p_0(\beta_j)=A_0\lambda_j^{p_0}$, so $\beta_j\delta_j^2=A_0^2\lambda_j^{2p_0}/a$ |
| $\mathbb T^{\rm pre}_k(Z,\mathfrak a)$ | the localized operator of Definition II.5.8, kernel $(K^{\rm pre},b^{\rm pre})$ |

Volumes: $|X|_j$ in scale-$j$ units, $|X|_{\#j}$ the number of $\pi_j$-cubes, as in Part II. "$k$-block" is a cube of $T^{(k)}_1$ (side $L^k$
fine units), as in P7.

### III.0.3 Design decisions

Rulings 1–2 (approved, AGENTS.md) are in force: $R$ acts on ripe components, i.e. on Active windows covered by at most $\nu_{\max}$ boxes
with merge strips, and may be redefined wherever P7's construction needs it. The following decisions make P7 precise in that setting.

**D-III.1 (localization; V4-01, O-3).** $R$ is defined on one ripe component at a time, on its localized history, with the local sets
$U,W$ of the core. The global sets $U_{k_1}=Z_{k_1}^\approx$, $W_{k_1}$ of ARCH's Lemma L never occur. Lemma L becomes a statement about
local sets (§III.9.1) and needs no assumption on far components; this closes O-3.

**D-III.2 (binary decompositions).** P7 introduces five decompositions of unity: (2.18) on $Z^c_0\cap(\Omega^c_k)^{\sim3}$, "the second
decomposition" over $S''_k\subset Z''^c_0\cap(\Omega^c_k)^{\sim3}$ (p. 502), the decomposition over $Q''_{k_1}\subset U^c\cap U^{\sim6}$ (p. 503), $\chi''$ (2.61),
and (3.20) over $S''_k\subset Z''_0$. In P7 the large-field terms are indexed by the subsets $S''_k$, $Q''_{k_1}$, because the large-field
region of the multi-index is enlarged by them. Here a kept component keeps its region and spine ((T6) of §I.4.4), so no subset needs to
be recorded: **each decomposition is binary**, $1=\chi+(1-\chi)$ with $\chi$ the product of the small-field functions, and the
large-field branch uses the small factor of a single violation. This removes the entropy of the subset sums (P7's factors
$\exp O(1)|\cdot|$ and the ring term of (2.33)). The kept labels are $\mathfrak K:=\{\varkappa_1,\dots,\varkappa_5\}$ with $C_{\rm dec}\equiv5$
(Definition III.5.2).

**D-III.3 (the actual composed transformation; O-8′).** P7 p. 499 composes the window transformations $T^{(j)}$ exactly, using P5's
choice $c=0$ ("the equalities (1.37) [4]", read as P5 (1.40)–(1.41), Part II §II.1.5 item 3). Under the free flow (D-II.3) two things
differ: the coefficients $\beta_ja$ are not exactly canonical (ratio $\gamma_j/\gamma_k$), and the field renormalizations $\theta=z_{j+1}\psi_{j+1}$
(P4 (4.1), P6 p. 4 [checked]) multiply the large-field Gaussians of the window. **New finding:** the second effect is not mentioned by P7,
and it shifts the mean of the composed Gaussian by $\sum_{i>n}\zeta_i$ for a leaf of layer $n$, which is large compared with the Gaussian width
$\beta_k^{-1/2}$ for deep layers. It is harmless only after weighting by the volume fraction of the deep layers in a $k$-block, which is
$O(L^{-(k-n)d})$ (Lemmas III.1.7, III.1.7′). Route (i) of §II.1.5 is adopted: the actual composed kernel is computed exactly (Lemma III.1.6), the
cancellation (2.53)–(2.58) is done with the ideal weights of P2 (4.6)–(4.7), and the difference is an explicit remainder $C^\natural=C^\natural_0+C^\natural_1$:
$C^\natural_1$ is absorbed by $\frac38$ of the composed-Gaussian term, $|C^\natural_0|\le1$ on the real domain and $\le C_\natural\hat\lambda_k^{2d+1}$ on the complex domain
(Lemma III.6.3; the latter is part of $L_{\rm res}$). No perturbation statement for the Gaussian kernels in the sequence $(a_i)$ is needed (SF §3.1).

**D-III.4 (decay margin of the input).** P5 Theorem 1 (p. 499 [checked]) states that the functions with the new superscript produced by
the step satisfy (H.2)–(H.4), (H.7) "with the constant $\frac32\kappa$ instead of $\kappa$", and P7 p. 528 [checked] uses "the exponential decay
properties obtained after the last fluctuation integral and the scaling operation, and they are better than the properties formulated
in the inductive hypothesis (H.7)". The polymer expansion of §III.10 needs this margin. **$\mathrm{IsRep}^{\rm pre}_k$ is amended**: its (D7)
holds with $\kappa_+:=\frac32\kappa$ in place of $\kappa$ (and with the constant $B_{\rm st}$ of LF-3, Lemma III.10.7), and its (D2) gives $\mathcal R^{(k)}_m$ the bound $\frac12\beta_k^{-m-1}$
(P5 Proposition 3.2), leaving room for $\mathcal R''^{(k)}_m$. This is an obligation on LF-3
(P5 Theorem 1), recorded as a change to §II.6.3 (§III.O.2).

**D-III.5 (the refund route; ARCH Step 6, (M3)).** Every loss of $R$ that is proportional to the window volume $\sum_j|X_j|_{j+1}$ (the
renormalization remainder $C_{k_1,k}$, the step boundary factors, the integration volumes of the window variables) is paid by the slack in
the quiet-step charges $(c_1\log\beta_j+c_2)|X_j|_{j+1}$ of $\kappa^{\rm pre}$ (Definition II.5.11), once $c_1\ge C_W$, $c_2\ge C'_W$ (§III.8.2). Only the
losses that are not proportional to the window volume ($L_{\rm res}$, (III.8.4)) are paid by $C_R\hat\lambda_k^{2d+1}$. This is P7 p. 520 [checked]:
"We can take the constants in the sum (3.8) large enough, so that the sum in (3.9) is cancelled by the sum in (3.8)".

**D-III.6 (rotation form of the kernels; OBS requirement 2).** P7's coset average (p. 521 [checked]) rotates the integration variables of the
core operator and needs that "the integral operators with the characteristic functions ... are invariant with respect to the orthogonal
group", while "some expressions in the exponentials ... depend on the vector variables $h,g$ ... but they depend analytically on
$(\psi,\psi')$". Part II version 1 did not state this structure. It is added as requirement (S5) on all kernels at scales $\le k_0$ (Definition
II.5.7, version 1.1): indicator of an $O(N)$-invariant set times the exponential of a jointly covariant analytic function. It holds for the quiet
kernels and for the kept kernels constructed here; LF-3 and LF-6 must supply it for their kernels.

**D-III.7 (removed clusters in the polymer expansion).** P7 (3.26) sums over sets $\{Z_1,\dots,Z_n\}$ of removed components without saying
which sets occur together with a given kept region. Joint admissibility of components is not a pairwise condition (§III.10.1: gap
filling in the openings can involve three components). The heavy objects of the gas are therefore *removed clusters*, the classes of
removed components under "distance $\le4\omega_k$"; joint admissibility factorizes over them (Lemmas III.10.2, III.10.4). This is new.

**D-III.8 (completeness of $\mathfrak A$).** The history set of a representation is the set of **all** admissible histories (with $R$-records
valued in $\{\text{removed}\}\cup\mathfrak K$), as in P5 (1.27) ("the maximal set of the multi-indices", p. 494 [checked]). Terms with zero operator are
harmless; completeness is needed for the gas identity (Lemma III.10.4). Change to Definition II.6.1 (§III.O.2).

**D-III.9 (variables of kept kernels).** After $R$'s normalization, the kept kernels of the second kind (K2) no longer contain the window
variables that occur only in Gaussians (they are integrated by the composition). (S3) is amended to allow a kept kernel whose internal
variables $I''\subset I(Z,\mathfrak a)$ contain all variables of the multiscale field and of the fluctuation fields ((S3) of Definition II.5.7, version 1.1).

**D-III.10 (LF-1 (b) replaces P7's segment arguments).** P7 uses segments of length $<6M[R_{k-1}]$ (p. 502) to verify the hypothesis
$||\psi|-1|<c_5$ of P6 (3.6). LF-1 (b) (Theorem II.4.1) holds for hard spins without that hypothesis, so these segments are not needed;
the constants $C(c_0)$ of (M7) attached to them disappear.

### III.0.4 Summary of results

Proved here: the structure of the window operator and the exact composition with the actual coefficients (§III.1); the late-scale
geometry with $D_0=3c_0+4$ (§III.3); **Lemma CH** with explicit $\hat W_k\le C_{\hat W}\hat\lambda_k^{w_0}$ (§III.4); the small factors of the five
decompositions (§III.5); the cancellation identity with the remainder $C^\natural$ (§III.6); Lemma 2.5 with the changed constants (§III.7);
the window integral, the kept data K1, K2 and **LF-4R** (§III.8); **Lemma L** for the local sets, the bounds (3.11)′–(3.19)′, the coset
average with joint covariance (§III.9); the clique lemma, the removed-cluster gas, and **LF-4** (§III.10). Cited: the renormalization of
the window actions P7 (2.10)–(2.15) with P6 (2.31) (same inputs as Part II's O-2′), P7 Lemmas 2.1–2.2 (existence and bounds of $\psi^0_k$, with $D_0$), the denominator (3.3)–(3.5),
P2 Proposition 3.1 / P3 Proposition 2.1 (through BG and LOC), the background re-expansion (3.22)–(3.25) (P6 §2), and the abstract
polymer expansion PE with a hole (landed `pe_hole`).

---

## III.1 Ripe components, the window, and the composition (P7 pp. 498–500)

### III.1.1 What ripeness gives

**Lemma III.1.2 ((RQ1)–(RQ5); P7 (2.1)–(2.2), (2.31)–(2.32)).** Under (A-III.1)–(A-III.3), let $Z$ be ripe at scale $k$, Active$(q,\nu,\mathcal M)$ with
$t^*(Z)=k$. Then:

(a) $q=k_1(k)$ (the core of §I.1.2), $n_1=k-k_1$ satisfies $n_1\ge n_q(k_1)$, hence
$$n_1\log L>\alpha^{-1}\hat\lambda_{k_1}\ge\alpha^{-1}\log(\beta_{k_1}a)\qquad(\text{the first inequality of P7 (2.31)}),\tag{III.1.1}$$
and $\hat\lambda_k\le c_*\hat\lambda_{k_1}+(c_*+1)\theta\le2c_*\hat\lambda_{k_1}$ (RQ4), so that $\lambda_j\ge\lambda_{k_1}\ge\hat\lambda_k/(4c_*)$ for $k_1\le j\le k$ (replacing P7 (2.32),
$\log\beta_{k_1}a/\log\beta_ka>\alpha/d$).

(b) (RQ1) For $k_1\le j<k$ no new large-field cube lies in $Z_{j+1}$: the step $j\to j+1$ is quiet in every component of $Z_{j+1}$
(Definition II.5.5), so $\Omega'_{j+1}=\Omega_{j+1}=\Omega''_{j+1}$; no ancestor of $Z$ at a scale in $(k_1,k)$ is ripe, removed or kept.

(c) (RQ2) For $k_1\le j\le k$, $Z_j$ is covered by $\nu\le\nu_{\max}(k)$ boxes of side $\le\mathrm{crit}_j$; it has at most $\nu(M\mathrm{crit}_j)^d$ $j$-blocks
per $\pi_j$-cube count, and $\Lambda_j$ has at most $\nu(LM\mathrm{crit}_{j+1})^d$ $j$-blocks.

(d) (RQ3) $\Gamma(Z)$ is a point, $s+n_2(s)\le k$, and $Z_j$ is one box of side $\le\mathrm{crit}_j$ for $s\le j\le k$; in particular $Z$ is one box.

(e) (RQ5) The core $Z_{k_1}=\bigsqcup_{C\in\mathcal C_*}C$ is a union of boxes of side $\le\mathrm{crit}_{k_1}$, at mutual distance $\ge\omega_{k_1}$; the sets
$(C^{\approx})^{\sim m}$, $C\in\mathcal C_*$, are pairwise disjoint for $m\le\frac{L+8}2$ (Lemma I.2.13).

(f) (P7 (2.1), (2.23) for the lineage) For $k_1\le j<k$: $\Omega^c_j\subset\Omega^c_{j+1}\subset Z_{j+1}$, $Z_j\subset\Omega^c_{j+1}$, and, as fine sets,
$\mathrm{dist}_\infty(Z_j,\Omega_{j+1})\ge(([R_j]+4)LM+([R_{j-1}]+1)M)L^j$ (Lemma I.3.5 (f)). The ring $U^c\cap U^{\sim9}$ (scale $k_1$) lies in
$X_{k_1}\cap\Omega^c_{k_1+1}=Z^c_{k_1}\cap\Omega^c_{k_1+1}$, i.e. in the layer $\Lambda_{k_1}$, and $U^{\sim9}\subset Z_{k_1+1}$ (Lemma I.3.5 (i) for the localized history).

*Proof.* (a) Lemma I.4.13 (f4): $k_1(t^*(Z))=q$ and $t^*=k$. By Lemma I.4.9 (b), $q+n_q(q)\le k$, and $n_q(q)>\hat\lambda_q/(\alpha\log L)$ by (F1);
$\hat\lambda_q\ge\lambda_q=\log(\beta_qa)$ by Lemma II.1.2 (a). By Lemma I.4.9 (b) also $k<(q+1)+n_q(q+1)$, so $\hat\lambda_k\le\hat\lambda_{q+1+n_q(q+1)}\le c_*\hat\lambda_{q+1}+\theta$
by (F1), and $\hat\lambda_{q+1}=\hat\lambda_q+\theta$. The last bound uses $\hat\lambda_{k_1}\ge(c_*+1)\theta/c_*$ ((Λ0)), $\lambda_j\ge\hat\lambda_j-2\ge\hat\lambda_j/2$ ((Λ14) with
$\hat\lambda\ge4$) and monotonicity. (b)–(e) Lemma I.4.13 (a), (b), (g), (e4) and Lemma I.4.10 (a); quietness is (a) of Lemma I.4.13 with
Definition II.5.5. No ancestor in $(k_1,k)$ is ripe: a ripe ancestor would be removed (then it has no successor, Lemma I.4.3 (a)) or kept
(a reset, excluded by Lemma I.4.13 (a)). The block counts in (c): $\Lambda_j\subset\Omega^c_{j+1}\subset Z_{j+1}$, covered by $\nu$ boxes of $\pi_{j+1}$-cubes,
each containing $(LM)^d$ $j$-blocks. (f) Lemma I.3.5 (a), (e), (f), (i) applied to the localized history (Lemma I.3.9 (d)); $Z_j=\mathrm{Lin}_j$
and $Z_{j+1}=\mathrm{Lin}_{j+1}$ by Lemma I.4.3 (c). $\square$

P7's second inequality of (2.31) ($n_1\log L\le\alpha^{-1}\log\beta_{k_1}a+\log L$) is replaced by (RQ4); it was used only for (2.32).

### III.1.2 The window operator (P7 (2.6))

**Lemma III.1.3 (the window operator).** With the notation of §III.0.2,
$$\mathbb T^{\rm pre}_k(Z,\mathfrak a)=\big(K_{\rm win},b_{\rm win}\big)\circ\bigotimes_{C\in\mathcal C_*}\mathbb T_{k_1}(C,\mathfrak a|_C),\qquad
K_{\rm win}:=\prod_{j=k_1}^{k-1}\ \prod_{Y'\in\mathrm{Anc}_{j+1}(Z)}K^{\rm q}_j(Y'),\quad b_{\rm win}:=\sum_{j=k_1}^{k-1}\ \sum_{Y'\in\mathrm{Anc}_{j+1}(Z)}b_j(Y'),\tag{III.1.2}$$
in the sense of Lemma II.5.3, where $K^{\rm q}_j$ is the quiet kernel of Definition II.5.6 and $b_j$ the step boundary factor (S0). The internal
variables of $(K_{\rm win},b_{\rm win})$ are $\psi_j$ on $T^{(j)}\cap\Omega^c_{j+1}$, $k_1\le j\le k-1$ (no fluctuation variables); its output variables are
$\psi_k$ on $T^{(k)}\cap V_Z$. This is P7 (2.6) [checked, text layer], with P6 (3.2)'s background replaced by the local background (D-II.1) and
with the constants $-E_j|Z^c_j\cap\Omega^c_{j+1}|-E'''_j|\Omega_{j+1}\cap Z_{j+1}|$ inside $b_j$ (P7 p. 499: "The constants in the exponentials are
unimportant, so we separate them").

*Proof.* Induction on $j$ from $k_1+1$ to $k$ with Definition II.5.8: by Lemma III.1.2 (b) every step on $[k_1,k)$ is quiet in every lineage
component, so its step kernel is $K^{\rm q}_j$ by (S1), and no ancestor at a scale in $(k_1,k)$ is ripe, so $\mathbb T_j=\mathbb T^{\rm pre}_j$ there. Products
and compositions are those of Lemma II.5.3 (b); the internal variables of the quiet steps are listed in Definition II.5.6. $\square$

By Lemma III.1.2 (b) and Definition II.5.6 the window kernel is explicit:
$$K_{\rm win}=\prod_{j=k_1}^{k-1}\Big[\prod_{y\in T^{(j+1)}\cap\Omega^c_{j+1}}z_{j+1}^Nt_j\big(z_{j+1}\psi_{j+1}(y),(Q\psi_j)(y)\big)\Big]\cdot\mathcal X_{\rm win}\cdot e^{-\sum_j\mathcal A_{j+1}(X_j)},\tag{III.1.3}$$
where $\mathcal X_{\rm win}$ is the product of the characteristic functions of Definition II.5.6 over the window, $\chi_j(X_j\cap(\Omega^{\sim3}_{j+1})^c)$,
$\chi'_{j+1}(\Omega^{\sim3}_{j+1}\cap(\Omega^c_{j+1})^{\sim3}\cap Z_{j+1})$ (both sides of $\partial\Omega_{j+1}$), $\chi_{j+1}(\Omega^{\sim-3}_{j+1}\cap Z_{j+1})$, $\chi^{\rm new}_j$ and
$\mathbf 1[\cdot\in\mathcal D_{\mathbb R}]$, and $\mathcal A_{j+1}(X_j):=\sum_{Y'}\mathcal A_{j+1}(Y';\psi)$ (Definition II.5.4).

### III.1.3 Leaves, Gaussian-only variables, and the composition (P7 (2.7)–(2.9))

**Definition III.1.4 (leaves and Gaussian-only variables).**
- The *Gaussian-only variables* are $\mathcal J:=\{\psi_j(y):\ y\in T^{(j)},\ y\subset\Omega^c_j,\ k_1<j\le k-1\}$.
- The *leaves* are the variables of the generating set $G:=(\mathbb B_k\cap Z^c_{k_1}\cap\Omega^c_k)\cup(T^{(k_1)}\cap Z_{k_1})$ (P7 p. 499: "the one generating
  set equal to $(\mathbb B_k\cap Z^c_{k_1})\cup(T^{(k_1)}\cap Z_{k_1})$"): the multiscale field $\psi_n$ on the blocks of $\Lambda_n\cap Z^c_{k_1}$, $k_1\le n\le k-1$, and $\psi_{k_1}$
  on the $k_1$-blocks of $Z_{k_1}$. For a leaf block $x$ write $n_x$ for its layer and $\psi^G(x)$ for its variable.
- The *top variables* are $\psi_k(z)$, $z$ a $k$-block of $\Omega^c_k$.

**Lemma III.1.5 (support of the Gaussian-only variables).** A Gaussian-only variable $\psi_j(y)$ occurs in $K_{\rm win}e^{b_{\rm win}}\prod_CK_C e^{b_C}$ only
in the two factors $z_j^Nt_{j-1}(z_j\psi_j(y),(Q\psi_{j-1})(y))$ and $z_{j+1}^Nt_j(z_{j+1}\psi_{j+1}(y''),(Q\psi_j)(y''))$, $y''\supset y$ the $(j+1)$-block. A top variable
$\psi_k(z)$, $z\subset\Omega^c_k$, occurs only in $t_{k-1}$. In particular the main actions, the characteristic functions, the boundary factors and the
core kernels do not depend on $\mathcal J$ nor on $\psi_k|_{\Omega^c_k}$.

*Proof.* $y\subset\Omega^c_j\subset Z_j$ is at fine distance $\ge(([R_j]+4)LM)L^j$ from $\Omega_{j+1}$ (Lemma III.1.2 (f)), and at index distance
$\ge[2R_{j-1}]+7$ (scale $j$) from $Z^c_j$ (Lemma I.3.5 (d), (e) at scale $j$: $Z^{(0)}_j\supset(F^Z_j)^{\sim([2R_{j-1}]+2)}\supset(\Omega''^c_j)^{\sim([2R_{j-1}]+6)}$). The
characteristic functions read their variables within three cubes of cubes of $X_j$, of $\Omega^{\sim3}_{j+1}\cap(\Omega^c_{j+1})^{\sim3}$ or of $\Omega_{j+1}$ (Lemma
II.3.3), hence not on $\Omega^c_j$. The main action $\mathcal A_{j+1}(X_j)$ reads the multiscale field on $X_j^{+1}$ (which consists of $\psi_j$ on $\Lambda_j$ and
$\psi_{j+1}$ on $\Omega_{j+1}$) and the local background, whose data live on $\Omega_1(G^{Y'}_{j+1})\cup C(\Omega_1(G^{Y'}_{j+1}))$; its part from $\mathbb B_j(W_j)$ lies within
one cube of $W_j=(Z^c_j)^{\sim2([R_{j-1}]+1)}$ (Lemma II.2.3 (c)), at distance $\ge[2R_{j-1}]+7-2[R_{j-1}]-3>0$ from $\Omega^c_j$, and its part from
$\mathbb B_{j+1}(U_{Y'})\cap\Omega_{j+1}$ reads $\psi_{j+1}$ on $\Omega_{j+1}$ only (the mixed lift, Definition II.2.1 (b)). Boundary factors and core kernels depend on
the multiscale field, the fluctuation fields and the core variables only ((S0), Lemma II.5.9 (a)). For $\psi_k$ on $\Omega^c_k$: the multiscale
field at scale $k$ is $\psi_k$ on $\Omega_k$, and $\chi'_k$ reads $\theta=z_k\psi_k$ only on $\Omega_k$ (Definition II.3.2 item 3). $\square$

**Lemma III.1.6 (the actual composed transformation; O-8′ part 1).** Put $c_j:=\beta_jaL^{d-2}$, $\varpi_n:=\prod_{i=n+1}^kz_i^{-1}$ ($\varpi_k=1$), and for a
$k$-block $z\subset\Omega^c_k$ and a leaf $x\subset z$, $w_x:=L^{(n_x-k)d}$ (its volume fraction). Then, for every value of the leaves and of the other
variables,
$$\int\prod_{j=k_1}^{k-1}\ \prod_{y\subset\Omega^c_{j+1}}z_{j+1}^Nt_j\big(z_{j+1}\psi_{j+1}(y),(Q\psi_j)(y)\big)\ \prod_{\mathcal J}d^N\psi\ =\ \prod_{z\subset\Omega^c_k}g_z\big(\psi_k(z)-\mathcal Q^\natural_z\psi^G\big),\tag{III.1.4}$$
$$\mathcal Q^\natural_z\psi^G:=\sum_{x\subset z}w_x\varpi_{n_x}\psi^G(x),\qquad g_z(u):=\Big(\frac{\beta_ka^\natural_z}{2\pi}\Big)^{N/2}e^{-\frac12\beta_ka^\natural_z|u|^2},\qquad
\frac1{\beta_ka^\natural_z}:=\sum_{j=k_1}^{k-1}\ \sum_{y}\frac{\varpi_j^2\,w_y^2}{c_j},\tag{III.1.5}$$
the last sum over the $(j+1)$-blocks $y\subset z$ that are not leaves, $w_y:=L^{(j+1-k)d}$. Each $g_z$ is a probability density on $\mathbb R^N$. Write
$\mathcal Q_z\psi^G:=\sum_{x\subset z}w_x\psi^G(x)$ (P2 (4.6), the volume average) and $a_z:=a(\Delta_k(z),G)$ for the weight of P2 (4.7) = BG (6.5),
$\frac1{a_z}=\sum_{x\subset z}w_xu_{k-n_x}$, $u_r=1/\texttt{compWeight}\ L\ a\ r$. Then
$$a^\natural_z=a_z(1+\eta_z),\quad|\eta_z|\le\eta_k:=\frac{12c_\xi q^k}{\beta(1-q)};\qquad|\varpi_n-1|\le\varsigma_n:=\frac{6\alpha_0c_\xi}{\beta}L^{-(n+1)(\alpha+2\gamma)}\quad(k_1\le n<k),\tag{III.1.6}$$
with $c_\xi$, $q=L^{-2\gamma}$ of SF Theorem 5.3. With the ideal coefficients ($z_i\equiv1$, $\beta_j=\beta_kL^{-(k-j)(d-2)}$) the right side of (III.1.4) is P7 (2.9):
$\mathrm{const}\cdot\exp(-\frac12\sum_z\beta_ka(\Delta_k(z),\mathbb B_k)|\psi_k(z)-Q(\Delta_k(z),\mathbb B_k)\psi|^2)$, and (III.1.4) restricted to $Z_0$ gives P7 (2.8).

*Proof.* *Change of variables.* Put $Z_j:=\prod_{i=k_1+1}^jz_i$ ($Z_{k_1}=1$; the scalar, not the region) and $\hat\psi_j:=Z_j\psi_j$ for all variables of scale
$j\in[k_1,k]$ (leaves, Gaussian-only, top). Since $z_{j+1}/Z_{j+1}=1/Z_j$ and $Q$ is linear,
$z_{j+1}\psi_{j+1}(y)-(Q\psi_j)(y)=Z_j^{-1}\big(\hat\psi_{j+1}(y)-(Q\hat\psi_j)(y)\big)$. So the factor $z^N_{j+1}t_j(\dots)\,d^N\psi_{j+1}(y)$ is the Gaussian probability measure in
$\hat\psi_{j+1}(y)$ with mean $(Q\hat\psi_j)(y)$ and covariance $(Z_j^2/c_j)I$. *Markov chain.* Integrating the Gaussian-only variables layer by layer
from $j=k_1+1$ upwards, for fixed leaves, is computing the law of the top variables of a Gaussian chain on the tree of blocks of $z$: with
$e(y):=\hat\psi_{j+1}(y)-(Q\hat\psi_j)(y)$, independent centred Gaussians, and $Q$ the plain average over the $L^d$ children,
$\hat\psi_k(z)=\sum_{x\subset z}w_x\hat\psi^G(x)+\sum_{y}w_ye(y)$, the second sum over the non-leaf blocks $y\subset z$ of scales $k_1+1,\dots,k$. (Each non-leaf block
of scale $j+1$ is the average of its children plus $e(y)$; unfold the averages.) Different $k$-blocks involve disjoint variables. Hence the
law of $\hat\psi_k(z)$ is Gaussian with mean $\sum_xw_x\hat\psi^G(x)$ and covariance $\sum_yw_y^2Z_j^2/c_j$; dividing by $Z_k$ gives (III.1.4)–(III.1.5) with
$\varpi_n=Z_n/Z_k$. The Jacobians cancel because every factor is a probability measure. This is the landed `integral_blockSpin_comp`
(`Gaussian/BlockSpin.lean`) iterated, for arbitrary positive coefficients. *Ideal case.* With $Z\equiv1$ and $c_j=c_j^{\rm id}:=\beta_kaL^{d-2}L^{-(k-j)(d-2)}$:
$w_y^2/c^{\rm id}_j=\beta_k^{-1}a^{-1}w_yL^{-2(k-j-1)}$, and $\sum_{y\text{ non-leaf of scale }j+1}w_y=\sum_{x:\,n_x\le j}w_x$; so $\beta_k^{-1}a_z^{-1}=\beta_k^{-1}\sum_xw_x\sum_{j=n_x}^{k-1}a^{-1}L^{-2(k-j-1)}=\beta_k^{-1}\sum_xw_xu_{k-n_x}$,
which is BG (6.5) (P2 (4.7)). *Bounds.* $c_j=c_j^{\rm id}\gamma_j/\gamma_k$ (Part I (I.2)), so each term of (III.1.5) is the ideal term times $\rho_j:=\varpi_j^2\gamma_k/\gamma_j$.
Write $W_j:=\sum_yw_y^2/c^{\rm id}_j=(\beta_ka)^{-1}L^{-2(k-j-1)}f_{\le j}(z)$, $f_{\le j}(z):=\sum_{x:\,n_x\le j}w_x\le1$; then $a_z/a^\natural_z=\sum_j\rho_jW_j/\sum_jW_j$ and $\sum_jW_j\ge W_{k-1}=(\beta_ka)^{-1}$
(every leaf has layer $\le k-1$), so $|a_z/a^\natural_z-1|\le\sum_{j=k_1}^{k-1}L^{-2(k-j-1)}|\rho_j-1|$: **the coefficient error is weighted towards the top scales.** SF Theorem 5.3 gives,
for the constants of the step $i-1\to i$, $|\zeta_i|=\varepsilon_i|\xi_1^{(i-1)}|\le\varepsilon_i\frac{c_\xi}{4\beta}q^i$ and $|\xi^{(i-1)}_3|\le\frac{c_\xi}{4\beta}q^i$; with $\gamma_i=\gamma_{i-1}/(1+\xi_3^{(i-1)})$ (P4 (5.28)) and
$\varepsilon_i\le1$, $x_j:=2|\log\varpi_j|+|\log(\gamma_k/\gamma_j)|\le\sum_{i>j}(4|\zeta_i|+2|\xi^{(i-1)}_3|)\le\frac{3c_\xi q^{j+1}}{2\beta(1-q)}$, and $|\rho_j-1|\le2x_j$. Hence
$|a_z/a^\natural_z-1|\le\frac{3c_\xi q^k}{\beta(1-q)}\sum_{m\ge0}(L^{-2}q^{-1})^m\le\frac{6c_\xi q^k}{\beta(1-q)}$, since $L^{-2}q^{-1}=L^{2\gamma-2}\le L^{-1}\le\frac12$; this gives $\eta_k$ (with $\eta_k\le\frac12$). For
$\varsigma_n$ use $\varepsilon_i\le3\alpha_0L^{-i\alpha}$ (Definition II.1.1): $|\varpi_n-1|\le e^{x}-1\le2x$ with $x=\sum_{i>n}2|\zeta_i|\le\frac{3\alpha_0c_\xi}{2\beta}\sum_{i>n}L^{-i(\alpha+2\gamma)}\le\frac{3\alpha_0c_\xi}\beta L^{-(n+1)(\alpha+2\gamma)}$. $\square$

**Lemma III.1.7 (volume fractions of deep layers).** For a $k$-block $z\subset\Omega^c_k$ and $k_1\le n<k$, the fraction $f_n(z):=\sum_{x\subset z,\,n_x=n}w_x$ of $z$
in the layer $n$ satisfies $f_n(z)\le\nu_{\max}(k)(LM\mathrm{crit}_k)^dL^{-(k-n)d}$. Consequently
$$\bar\varsigma_z:=\sum_{x\subset z}w_x|\varpi_{n_x}-1|\le\sum_{n=k_1}^{k-1}f_n(z)\varsigma_n,\qquad\Sigma^\natural:=\beta_k^{1/2}\max_z\bar\varsigma_z\le C_\varsigma\,\beta^{-1/2}\,\hat\lambda_k^{\,p_2+2d}L^{-k\gamma},\tag{III.1.7}$$
with $C_\varsigma:=6e\,\alpha_0c_\xi(LM)^d\,\sup_{x\ge1}\big[x^{-(p_2+2d)}\bar\nu(x)\overline{\mathrm{crit}}(x)^d\big]\big/\big(L^{\alpha+2\gamma}(1-L^{-(d+2)/2+\gamma})\big)$, a constant of rows 0–10. Since $\hat\lambda_k\le\hat\lambda_0(1+k\theta)$,
for every polynomial $P$ of degree $p$, $\Sigma^\natural P(\hat\lambda_k)\le C_\varsigma C_P\,\beta^{-1/2}\hat\lambda_0^{\,p+p_2+2d}$ with $C_P:=\sup_k(1+k\theta)^{p+p_2+2d}L^{-k\gamma}\sup_{x\ge1}x^{-p}P(x)$; all uses of
$\Sigma^\natural$ below are of this form and are made $\le1$ (or small) by conditions on $\lambda_*$ (§III.O.3; $\beta^{-1/2}\le\sqrt a\,e^{-(\hat\lambda_0-1)/2}$).

*Proof.* The first bound is Lemma III.1.2 (c): $\Lambda_n$ has at most $\nu(LM\mathrm{crit}_{n+1})^d$ blocks of volume $L^{nd}$, and $|z|=L^{kd}$. Then, with
$\beta_k^{1/2}\le e^{\epsilon}\beta^{1/2}L^{k(d-2)/2}$ and $m:=k-n\ge1$,
$$\beta_k^{1/2}f_n(z)\varsigma_n\le6e\,\alpha_0c_\xi\,\beta^{-1/2}\nu_{\max}(k)(LM\mathrm{crit}_k)^dL^{\frac{k(d-2)}2-(k-m+1)(\alpha+2\gamma)-md}
=6e\,\alpha_0c_\xi\beta^{-1/2}\nu_{\max}(k)(LM\mathrm{crit}_k)^dL^{-\alpha-2\gamma}\,L^{-k\gamma}L^{-m(\frac{d+2}2-\gamma)},$$
because $\frac{d-2}2-\alpha-2\gamma=-\gamma$ and $d-\alpha-2\gamma=\frac{d+2}2-\gamma>0$. Sum over $m\ge1$ and use (F5). $\square$

**Lemma III.1.7′ (total shift).** Let $V_n:=\sum_{z\subset Z^c_0\cap\Omega^c_k}f_n(z)$ be the volume of $\Lambda_n\cap Z^c_0$ in $k$-blocks. Then $V_n\le(M\mathrm{crit}_k)^dL^{-(k-n-1)d}$ if $n+1\ge s$, and
$V_n\le\min\{(M\mathrm{crit}_k)^dL^{-(k-s)d},\ \nu_{\max}(k)(M\mathrm{crit}_k)^dL^{-(k-n-1)d}\}$ if $n+1<s$; and
$$\Theta^\natural:=\beta_k\varepsilon_k\sum_{z\subset Z^c_0\cap\Omega^c_k}\bar\varsigma_z\ \le\ C_\vartheta\,\hat\lambda_k^{\,2d+1},\tag{III.1.8}$$
with $C_\vartheta$ a constant of rows 0–10. *Proof.* For $n+1\ge s$ the lineage at scale $n+1$ is one box of side $\le\mathrm{crit}_{n+1}$ $\pi_{n+1}$-cubes (Lemma III.1.2 (d)), of volume
$\le(M\mathrm{crit}_k)^dL^{-(k-n-1)d}$ $k$-blocks, and $\Lambda_n\subset Z_{n+1}$. For $n+1<s$, $\Lambda_n\subset Z_{n+1}\subset Z_s$ as fine sets (regions grow, Lemma I.4.3 (b)), which gives the
first bound without $\nu$; the second is Lemma III.1.2 (c). Next $\sum_z\bar\varsigma_z\le\sum_n\varsigma_nV_n$, and $\beta_k\varepsilon_k\varsigma_n\le18e^{\epsilon}\alpha_0^2c_\xi L^{(k-n-1)(\alpha+2\gamma)}$ (as
$\beta_k\le e^{\epsilon}\beta L^{k(d-2)}$, $\varepsilon_k\le3\alpha_0L^{-k\alpha}$, $d-2-\alpha=\alpha+2\gamma$). Put $t:=k-n-1$. The terms with $t\le k-s$ sum to $\le(M\mathrm{crit}_k)^d\sum_tL^{-t(d-\alpha-2\gamma)}\le2(M\mathrm{crit}_k)^d$.
The terms with $t>k-s$ (they occur only if $s>k_1+1$, and then $\hat\lambda_s\ge\hat\lambda_{k_1}\ge\hat\lambda_k/(2c_*)$) are $\le\sum_t\min\{AL^{t(\alpha+2\gamma)},\nu_{\max}(M\mathrm{crit}_k)^dL^{-t(d-\alpha-2\gamma)}\}$ with
$A=(M\mathrm{crit}_k)^dL^{-(k-s)d}$; summing the two geometric series at the crossover gives $\le4(M\mathrm{crit}_k)^dL^{-(k-s)(d-\alpha-2\gamma)}\nu_{\max}^{(\alpha+2\gamma)/d}$. Since $k-s\ge n_2(s)$,
$L^{k-s}>LM\mathrm{crit}_s\ge LMR_{\rm base}\hat\lambda_k^2/(4c_*^2)$; with $d-\alpha-2\gamma\ge\frac{d+1}2$ and $\frac{\alpha+2\gamma}d<\frac12$ this is $\le C\hat\lambda_k^{2d-(d+1)+p_2/2}=C\hat\lambda_k^{2d+\frac12}$
($p_2=2d+3$). $\square$

*Remark (why this matters).* For a leaf of layer $n$ close to $k_1$, $\beta_k^{1/2}\varsigma_n\approx\beta^{-1/2}L^{n_1(d-2)/2-\gamma k_1}$, which is large since
$L^{n_1}\ge(\beta_{k_1}a)^{1/\alpha}$ and $\frac{d-2}{2\alpha}>1$: the composed Gaussian is shifted by much more than its width for the deep leaves. The
shift enters the cancellation only through the averages $\mathcal Q^\natural_z$, where the deep leaves have weight $O(L^{-(k-n)d})$; that is what
(III.1.7) uses. P7's exact composition holds only for $z_i\equiv1$.

---

## III.2 Renormalization of the window actions (P7 (2.10)–(2.17))

**Definition III.2.1 (the window generating set; P7 (2.13), local).** With the local sets of §III.0.2 and $U_k:=Z^{\approx}$ (scale $k$),
$$\mathbb B_{k_1,k}:=\big(\mathbb B_{k_1}(W)\cap Z_{k_1}\big)\cup\big(\mathbb B_k\cap Z^c_{k_1}\cap Z\big)\cup\big(\mathbb B_k(U_k)\cap Z^c\cap U_k^{\sim}\big),$$
"the set $\mathbb B_k$ on $W_{k_1}\cap U_k$, completed by the minimal generating sets in a neighbourhood of the boundaries" (P7 p. 500 [checked]), and
$\phi_{k_1,k}:=\phi_k(\mathbb B_{k_1,k};\tilde\psi)$ (the Def-5 background $\mathrm{bg}(\mathbb B_{k_1,k};\cdot)$ of Part II §II.2.1, massless by (A-III.2)). By Lemma I.3.16 with the range
$\varpi\le2$ of the minimal generating sets (Lemma II.2.3 (c), D-II.5) and Lemma III.1.2 (e), on each $(C^{\approx})^{\sim m}$, $C\in\mathcal C_*$, $m\le\frac{L+4}2$, the first piece of
$\mathbb B_{k_1,k}$ is the single-box object of P7 for the box $C$; so P2 (1.1)–(1.3) for $\mathbb B_{k_1,k}$ reduce to P7's single-box check made box by box (ARCH Lemma G,
R3-14 (e)), and $\mathbb B_{k_1,k}$ is a `GeneratingSet` with separation $\varrho_3$.

**Lemma III.2.2 (renormalized window action; P7 (2.10)–(2.16), cited).** On the window domain (the configurations with $\mathcal X_{\rm win}=1$, extended to the
complex domain (1.32) [5] with $X=W\cap U_k$),
$$\sum_{j=k_1}^{k-1}\mathcal A_{j+1}(X_j;\psi)=\beta_kA^*_k\big(X_{\rm win},\mathbb B_k;\psi,\phi_{k_1,k}\big)-C_{k_1,k}(\psi),\qquad|C_{k_1,k}(\psi)|\le C_{15}\sum_{j=k_1}^{k-1}|X_j|_{j+1},\tag{2.15′}$$
where $A^*_k(\cdot,\mathbb B_k;\cdot)$ is the multiscale action with the coefficients renormalized to scale $k$ (P7 (2.10); under the free flow the weights are
$a_n$ of (II.1) for every $n$, since $a^{(k)}_n=a_n$, and $\beta^{(k)}_n=\beta_kL^{-(k-n)(d-2)}$, $\nu^{(k)}_n=\nu_kL^{-2(k-n)}$), $C_{k_1,k}$ is analytic, depends on $\psi$ restricted to
$W^\sim\cap U_k^\sim$, and $C_{15}$ is an output of rows 0–11 (it does not depend on $B_0,H_0,c_1,c_2$).

*Source and route.* P7 pp. 500–501 [checked, text layer]: (i) each step action is converted to the coefficients of scale $k$ in $k-j-1$ steps by the
renormalization formula P6 (2.31) (the actions only; "we do not renormalize the spin variables"), each conversion bounded by (2.11),
$\mathrm{const}\cdot\beta_{j+1}\varepsilon_{j+1}^2(\beta_n\varepsilon_n^2)^{-1}|X_j|_{j+1}\le\mathrm{const}\cdot L^{-2\gamma(n-j-1)}|X_j|_{j+1}$, summable in $n$; (ii) the background of each step is replaced by
$\phi_{k_1,k}$ through the composition identity (I-2, landed `theorem73_real`/`theorem73_complex`) and the exponential decay of P3 (2.55)–(2.56),
P6 (2.13)–(2.14), with a remainder $\le C_{\rm win}e^{-\gamma_w(M([\hat R_{j-1}]-1)-2M_1)}|X_j|_{j+1}$ [v1.3: P4-09]. Under the free flow (i) is unchanged (Part II §II.1.5 item 4). In (ii) the step backgrounds
are the local ones $\phi^{\rm loc}_{j+1}$ of D-II.1 instead of $\phi_{j+1}(\mathbb B_{j+1}(\partial\Omega_{j+1});\tilde\psi)$; the data change from $\mathbb B^{\rm loc}_{j+1}$ to $\mathbb B_{k_1,k}$ vanishes on
$Y'^{\sim[R_j]}$ (Lemma II.2.5 (c)) for every lineage component $Y'$, so the same decay estimate applies. *Status:* cited; the inputs are those of Part II's
O-2′ (LOC I-4b, I-5; conditional on LOC's open items). P7's second bound in (2.15), $<\mathrm{const}\,M^dR_0^d(\log\beta_{k-1}a)^{2d+1}$, is false for a window with $\nu$
pieces and is not used (ARCH Step 1): (2.15′) is per unit of new volume and is paid by the refund (§III.8).

**Lemma III.2.3 (the composed Gaussian dominates the single-scale action; P7 (2.17)′).** For every value of the window field and of $\psi_k$, with
$\mathcal G^\natural:=\sum_{z\subset Z^c_0\cap\Omega^c_k}\frac12\beta_ka^\natural_z|\psi_k(z)-\mathcal Q^\natural_z\psi^G|^2$ (the exponent of the composed kernel (III.1.4) outside $Z_0$),
$$\mathcal G^\natural+\beta_kA^*_k\big(Z^c_0\cap Z,\mathbb B_k;\psi,\phi\big)\ \ge\ \tfrac12(1-\eta_k)\,\beta_kA^*_k\big(Z^c_0\cap Z;\psi_k,\phi\big)-8(\Sigma^\natural)^2(M\mathrm{crit}_k)^d\max_x|\psi^G(x)|^2\tag{2.17′}$$
for every field $\phi$, where the right action is the single-scale action (generating set $T^{(k)}_1$). With the ideal composed weights the inequality holds
with $1$ in place of $\frac12(1-\eta_k)$ and without the last term (P7 (2.17)).

*Proof.* *Ideal case.* Fix a $k$-block $z\subset Z^c_0\cap\Omega^c_k$ and write $t_0:=\psi_k(z)-\mathcal Q_z\psi^G$, $t_x:=\psi^G(x)-(Q_{n_x}\phi)(x)$ for the leaves $x\subset z$. Since
$\sum_xw_x(Q_{n_x}\phi)(x)=(Q_k\phi)(z)$ (nested block averages), $\psi_k(z)-(Q_k\phi)(z)=t_0+\sum_xw_xt_x$. In fine units the composed term of $z$ is $\frac12\beta^{(k)}_0a_zL^{k(d-2)}|t_0|^2$ and the
block terms of the leaves are $\frac12\beta^{(k)}_0a_{n_x}L^{n_x(d-2)}|t_x|^2$ (P5 (1.5)). By Cauchy–Schwarz,
$|t_0+\sum_xw_xt_x|^2\le\big(\frac1{a_zL^{k(d-2)}}+\sum_x\frac{w_x^2}{a_{n_x}L^{n_x(d-2)}}\big)\big(a_zL^{k(d-2)}|t_0|^2+\sum_xa_{n_x}L^{n_x(d-2)}|t_x|^2\big)$, and, with $w_x=L^{(n_x-k)d}$ and (C1)
$L^{2(n-k)}u_n=u_k-u_{k-n}$, the first factor is $L^{-k(d-2)}\big(u^{(k)}_z+\sum_xw_x(u_k-u_{k-n_x})\big)=L^{-k(d-2)}u_k$, because $u^{(k)}_z:=1/a_z=\sum_xw_xu_{k-n_x}$ (BG (6.5)). So
the composed term plus the block terms of the leaves of $z$ are $\ge\frac12\beta^{(k)}_0a_kL^{k(d-2)}|\psi_k(z)-Q_k\phi(z)|^2$, the block term of the single-scale action. The
gradient, mass and boundary terms of the two actions coincide. *Actual case.* $a^\natural_z\ge(1-\eta_k)a_z$ and $|u-s|^2\ge\frac12|u|^2-|s|^2$ with $u=\psi_k-\mathcal Q_z\psi^G$,
$s=s_z:=\mathcal Q^\natural_z\psi^G-\mathcal Q_z\psi^G=\sum_xw_x(\varpi_{n_x}-1)\psi^G(x)$, $|s_z|\le\bar\varsigma_z\max|\psi^G|$; then $\frac12\beta_ka^\natural_z|u-s|^2\ge\frac12(1-\eta_k)\cdot\frac12\beta_ka_z|u|^2-\beta_ka_z|s_z|^2$,
$a_z\le2$, and the number of $k$-blocks of $Z$ is $\le(M\mathrm{crit}_k)^d$ (Lemma III.1.2 (d)); the action terms are multiplied by $\frac12(1-\eta_k)\le1$, which is allowed since
they are $\ge0$. $\square$

On the window domain $|\psi^G|\le2$, and by (Λ19) of §III.O.3 the last term of (2.17′) is $\le1$.

---

## III.3 Late scales (P7 pp. 498, 502–508)

**Definition III.3.1 (late scales, $Z_0$, $Z''_0$; P7 (2.2)–(2.5)).** Measure lengths at scale $k$ in $k$-blocks. Put
$$k_2:=\min\{j\le k:\ L^{-(k-j)}LM[R_j]\ge1\},\qquad k_3:=\min\{j\le k:\ L^{-(k-j)}L[R_j]\ge8\},\qquad n_2:=k-k_2,\ n_3:=k-k_3,$$
with the running radii $R_j$ (P5 (1.2)) — *version 1.2 (Part IV), D-IV.2:* with the a priori radii $\hat R_j$, so that $k_2,k_3$ do not depend on $\nu$; the radius estimates of Lemma III.3.2 hold for $\hat R_j$ by (Λ18) at
$x=\hat\lambda_{j-1}$ (with $\hat\lambda_j=\hat\lambda_{j-1}+\theta$ exactly; $\mathrm{crit}_j\le(2c_0+1)[\hat R_j]$ needs only $4c_0+10\le[\hat R_j]$); $Z_0$ := the union of the $k$-blocks that meet $Z_{k_2}$ (P7 (2.3)); $Z''_0$ := the $3$-neighbourhood (in $\pi_k$-cubes) of the
union of the $\pi_k$-cubes that meet $Z_{k_3}$. (P7 (2.5) has the threshold $1$ in $k_3$ and no neighbourhood; the change is needed by the second
decomposition and is explained before Lemma III.5.0.)

**Lemma III.3.2 (geometry of the late scales).** Under (A-III.1)–(A-III.3) and (Λ18) of §III.O.3:
(a) $k_1<k_2\le k_3\le k$ and $s<k_2$; the sequence $j\mapsto L^{-(k-j)}LM[R_j]$ is nondecreasing, and $L^{-n_2}LM[R_{k_2}]<\frac98L$, $L^{-n_3}L[R_{k_3}]<9L$.
(b) For $k_2\le j\le k$, $Z_j$ is one box of side $\le\mathrm{crit}_j$ $\pi_j$-cubes; $\mathrm{diam}_k(Z_{k_2})<\frac98(2c_0+1)$ and $\mathrm{diam}_k(Z_{k_3})<9(2c_0+1)M$.
(c) $Z_0$ is a box of $k$-blocks with $\mathrm{diam}_k(Z_0)<D_0:=3c_0+4$, $|Z_0|\le D_0^d$; $Z_0\subset Z''_0$, and $Z''_0$ is a box of $\pi_k$-cubes with $\mathrm{diam}_k(Z''_0)<D''_0M$,
$D''_0:=9(2c_0+1)+8$.
(d) (P7 (2.4)) $Z_{k_2}\subset Z_0\subset\Omega^c_{k_2+1}\subset\Omega^c_k$; in scale-$k_2$ units $\mathrm{dist}(Z_0,\Omega_{k_2+1})>2(L+1)M+M[R_{k_2-1}]$ and $\mathrm{dist}(Z^c_0,\Omega^c_{k_2})\ge([2R_{k_2-1}]+6)M$;
in scale-$k$ units $\mathrm{dist}(Z_0,\Omega_k)>MR_{k-1}-1\ge M$. In particular $U^{\sim9}\subset Z_{k_1+1}\subset Z_{k_2}\subset Z_0$ as fine sets.

*Proof.* (a) $[R_j]$ is nondecreasing, so the sequence is. At $j=k$ it is $LM[R_k]\ge1$ and $L[R_k]\ge8$, so $k_2,k_3$ exist, and $k_3\ge k_2$ since $M\ge1$. At $j=k_1$:
$n_1\ge n_q(k_1)\ge n_2(k_1)$ (by (F4) and (Λ0), $n_2(j)\le\bar n_2(\hat\lambda_j)\le\hat\lambda_j/(\alpha\log L)<n_q(j)$), and $L^{n_2(k_1)}>LM\mathrm{crit}_{k_1}\ge LM[R_{k_1}]$, so the term is $<1$
and $k_2>k_1$. At $j=s$: $k-s\ge n_2(s)$ (Lemma III.1.2 (d)), so likewise $k_2>s$. Minimality gives $L^{-(n_2+1)}LM[R_{k_2-1}]<1$, hence $L^{-n_2}LM[R_{k_2}]<L[R_{k_2}]/[R_{k_2-1}]\le\frac98L$
by (Λ18) ($[R_j]\le\frac98[R_{j-1}]$); the same for $k_3$ with the threshold $8$. (b) $j\ge k_2>s$ and Lemma III.1.2 (d). In scale-$k$ units a $\pi_{k_2}$-cube has side $ML^{-n_2}$, so
$\mathrm{diam}_k(Z_{k_2})\le\mathrm{crit}_{k_2}ML^{-n_2}<\frac98\mathrm{crit}_{k_2}/[R_{k_2}]$ by (a), and $\mathrm{crit}_{k_2}=2c_0r_{k_2}+10\le(2c_0+1)[R_{k_2}]$ by (Λ18) (which contains
$2c_0(r_j-[R_j])+10\le[R_j]$; $r_j=\lceil R_{\rm base}\hat\lambda_j^2\rceil$ and $R_j=\hat R_j$). The same with $L[R_{k_3}]<9L\,L^{n_3}$ for $k_3$. (c) $Z_{k_2}$ is a box, so $Z_0$ is a box, and its
diameter exceeds that of $Z_{k_2}$ by at most $2$; $\frac98(2c_0+1)+2<3c_0+4$. $Z_{k_2}\subset Z_{k_3}$ as fine sets (regions grow, Lemma I.4.3 (b)) and a $k$-block lies in a
$\pi_k$-cube, so $Z_0\subset Z''_0$; the diameter of $Z''_0$ exceeds that of $Z_{k_3}$ by at most $8M$. (d) Lemma III.1.2 (f) at $j=k_2$ gives the margin
$([R_{k_2}]+4)LM+([R_{k_2-1}]+1)M$ between $Z_{k_2}$ and $\Omega_{k_2+1}$; $Z_0$ lies within one $k$-block $=L^{n_2}$ scale-$k_2$ units of $Z_{k_2}$, and $L^{n_2}\le LM[R_{k_2}]$ by the
definition of $k_2$. The second distance is Lemma I.3.5 (d), (e) at scale $k_2$. The third: $Z_{k-1}\supset Z_{k_2}$ is at distance $>([R_{k-1}]+4)LM$ (scale $k-1$) from
$\Omega_k$. The last chain: Lemma III.1.2 (f) and $k_1+1\le k_2$. $\square$

This is ARCH (M7): P7's $15$ becomes $D_0=3c_0+4$ (P7 p. 507: "for size smaller than 15 we obtain absolute constants"; ours depend on $D_0$, row 4).

**Lemma III.3.3 (P7 Lemma 2.1 with $D_0$; cited).** Let $c_{D_0}:=4(D_0+1)^{-2}$. There are $c_{11},K_6>0$, depending on $d,L,N,D_0$ (row 4), such that if
$\psi_k\restriction_{U^\sim_k\cap Z^c_0}\in\tilde\Psi(U^\sim_k\cap Z^c_0;\delta)$ with $\delta\le c_{11}$, the variational problem
$$\inf_{\psi_k\restriction Z_0}A_k\big(\mathbb B_k(U_k);\tilde\psi_k,\phi_k(\mathbb B_k(U_k);\tilde\psi_k)\big)\qquad(\nu_k\text{-term absent; P7 (2.34)})\tag{2.34}$$
has a unique solution $\psi^0_k$ in $\tilde\Psi(U^\sim_k;K_6\delta)$, equal to $\psi_k$ on $U^\sim_k\cap Z^c_0$, analytic in $\psi_k\restriction_{U^\sim_k\cap Z^c_0}$ with the analytic extension mapping the
complex spaces into each other, and $O(N)$-equivariant: $\psi^0_k(R\psi_k)=R\psi^0_k(\psi_k)$, also for $R\in O(N,\mathbb C)$ near $O(N)$ where defined.

*Source and route.* P7 pp. 506–507 [checked, text layer]: expansion (2.35)–(2.36) around $\psi_{k,0}$ ($=\psi_k$ off $Z_0$, $=\psi_0$ on $Z_0$), the coercivity (2.37)–(2.38),
and a contraction for (2.39). The coercivity with $D_0$: each coordinate line meets the box $Z_0$ in an interval of at most $D_0$ points, on which the
Dirichlet Laplacian has smallest eigenvalue $2-2\cos\frac\pi{D_0+1}\ge4(D_0+1)^{-2}$; so $\langle\delta\psi,(-\Delta_1)\delta\psi\rangle\ge c_{D_0}\|\delta\psi\|^2$ for $\delta\psi$ supported in $Z_0$, replacing
P7's $\frac1{36}$, and $\langle\delta\psi,\Delta^{(k)}\delta\psi\rangle\ge\frac12\gamma_0c_{D_0}\|\delta\psi\|^2$ for $\delta$ small (P7 (2.37), P4 (2.24)). Uniqueness and analyticity: the landed analytic
contraction (`Background/ContractionAnalytic.lean`) with the linear response of BG Prop 5.4 (`theorem72_linearResponse`). Equivariance: the problem
(2.34) has no $h$-term, so it is $O(N)$-invariant, and uniqueness gives equivariance for real $R$; for complex $R$ by analytic continuation. *Status:*
cited from P7 with the changed constant; the contraction is to be written out in Lean (§III.L, item P3).

**Definition III.3.4 (reference vector; P7 (2.19)).** $\tilde\psi:=|\partial(Z^c_0\cap T^{(k)}_1)|^{-1}\sum_{z\in\partial(Z^c_0\cap T^{(k)}_1)}\psi_k(z)$ (the average over the $k$-blocks outside $Z_0$
adjacent to it) and $\psi_0:=\tilde\psi/(\tilde\psi\cdot\tilde\psi)^{1/2}$ (principal branch; $\psi_0:=e_1$ if $\tilde\psi\cdot\tilde\psi\in(-\infty,0]$, which does not occur on the support of
$\tilde\chi_k$ below). For complex $\psi_k$ this is the analytic continuation, with $\psi_0\cdot\psi_0=1$.

**Lemma III.3.5 ((2.20)′).** If $|\partial^1\psi_k(b)|<3\delta_k$ for the bonds of the boundary layer $\partial(Z^c_0\cap T^{(k)}_1)$ and $||\psi_k(z)|-1|<3\delta_k$ there (both implied by
$\tilde\chi_k=1$, Definition III.5.1), then, with $C_{2.20}:=12d(D_0+2)+3$,
$$|\psi_k(z)-\psi_0|<C_{2.20}\,\delta_k\qquad(z\in\partial(Z^c_0\cap T^{(k)}_1)).\tag{2.20′}$$
*Proof.* The boundary layer of the box $Z_0$ is connected, and two of its points are joined inside it by a path of at most $2d(D_0+2)$ bonds, so
$|\psi_k(z)-\tilde\psi|\le C_{20}\delta_k$, $C_{20}:=6d(D_0+2)$. Hence $|\tilde\psi|\ge|\psi_k(z)|-C_{20}\delta_k\ge1-(3+C_{20})\delta_k$ and $|\tilde\psi|\le1+3\delta_k$, so $|\tilde\psi-\psi_0|=||\tilde\psi|-1|\le(3+C_{20})\delta_k$,
and $|\psi_k(z)-\psi_0|\le(2C_{20}+3)\delta_k$. $\square$ (P7 (2.20) has $90d$; the layer lies in $(\Omega^c_k)^{\sim1}$ by Lemma III.3.2 (d).)

---

## III.4 Chains: Lemma CH and its consequences (P7 (2.22)–(2.30), Lemmas 2.3–2.4)

P7's chain (2.22)–(2.26) uses that every point of a layer $\Lambda_j$ lies within $3LMR_j$ of $\Omega_{j+1}$ (p. 504 [checked]: "$\mathrm{dist}_j(\Omega^c_j,\Omega_{j+1})<3LMR_j$").
For a window with several pieces this fails (gap filling; ARCH §2.7.1). Lemma CH replaces it: the chain goes from a window block to $\Omega_k$
through layers of scale $\ge j-h_k+2$, never through the core, and its length is bounded by the number of blocks of the window.

### III.4.1 The chain graph

**Definition III.4.1 (window blocks and the chain graph $\mathcal G$).** The *window blocks* are the $j$-blocks of $\Lambda_j\cap Z^c_{k_1}$, $k_1\le j\le k-1$ (blocks of $\mathbb B_k$ in
$X_{\rm win}$), and the *terminal blocks* are the $k$-blocks of $\Omega_k\cap Z$. $\mathcal G$ has these blocks as vertices and two kinds of edges:
- *intra edges*: two $i$-blocks of the same layer $\Lambda_i$ that are nearest-neighbour translates ($y'=y\pm L^ie_m$);
- *cross edges*: a $(i+1)$-block $b_+\subset\Lambda_{i+1}$ (a window or terminal block) and an $i$-block $y'\subset b_-$, where $b_-$ is a $(i+1)$-block nearest-neighbour
  adjacent to $b_+$ with $b_-\cap\Omega_{i+1}=\varnothing$ (P7 (2.22): "$b\subset T^{(j+1)}$, $b_+\in\Lambda_{j+1}$, $b_-\in\Lambda_j$").
Write $B_i$ for the number of window blocks of layer $i$; by Lemma III.1.2 (c), $B_i\le\nu_{\max}(k)(LM\mathrm{crit}_{i+1})^d$.

**Lemma III.4.2 (cross pairs; R3-03 (ii)).** Assume $\varrho_3\ge2dL$. (a) For a cross edge, $b_-\subset\Lambda_i\cap Z^c_{k_1}$: all $i$-blocks of $b_-$ are window blocks, and any two
of them are joined by at most $d(L-1)$ intra edges inside $b_-$. (b) If $x,x'$ are nearest-neighbour fine sites with $x\in\Lambda_{i'}$, $x'\in\Lambda_{i''}$, then $|i'-i''|\le1$;
if $i'=i+1$, $i''=i$, then the $(i+1)$-block $b_+$ of $x$ and the $i$-block $y'$ of $x'$ form a cross edge (with $b_-$ the $(i+1)$-block of $x'$).

*Proof.* (b) first. A site of $\Omega_{i+2}$ is at $\ell^1$-distance $>\varrho_3L^{i+1}>1$ from $\Omega^c_{i+1}$ (separation of $\mathbb B_k$, Lemma I.3.10, I.3.12), so nearest neighbours lie in
layers differing by at most one. Let $i'=i+1$. $\Omega_{i+1}$ is a union of $(i+1)$-blocks and $\Omega_{i+2}$ of $(i+2)$-blocks; $x\in\Omega_{i+1}\setminus\Omega_{i+2}$ gives $b_+\subset\Lambda_{i+1}$,
and $x'\notin\Omega_{i+1}$ gives $b_-\cap\Omega_{i+1}=\varnothing$; $b_+,b_-$ are nearest-neighbour adjacent since $x,x'$ are. (a) Every site of $b_-$ is within $\ell^1$-distance $2dL^{i+1}<\varrho_3L^i$
of $b_+\subset\Omega_{i+1}$, so it lies in $\Omega_i$ by separation; with $b_-\cap\Omega_{i+1}=\varnothing$, $b_-\subset\Lambda_i$. For $i>k_1$, $\Lambda_i\subset\Omega_{k_1+1}\subset Z^c_{k_1}$; for $i=k_1$, $b_-$ is
within $2dL^{k_1+1}$ of $\Omega_{k_1+1}$, while $Z_{k_1}$ is at fine distance $\ge([R_{k_1}]+4)LML^{k_1}$ from $\Omega_{k_1+1}$ (Lemma III.1.2 (f)). The intra edges: monotone lattice
paths inside the block. $\square$

So P7's requirement that "the whole block $B(b_-)$ lie in $\Lambda_j$" (REV3 R3-03 (ii)) holds automatically; no corner detour is needed.

### III.4.2 Non-enclosure

**Lemma III.4.3 (paths avoid the core and the deep obstacles; ARCH Lemma CH (a)).** Let $y$ be a window block of layer $j$ and
$i_0:=\max\{k_1,\ j-h_k+2\}$. There is a nearest-neighbour path of fine sites from a site of $y$ to a site of $\Omega_k\cap Z$ all of whose sites except the last lie
in $\bigcup_{i=i_0}^{k-1}\Lambda_i\cap Z^c_{k_1}$.

*Proof.* *Lift* (R3-03 (v)). $Z$ is one box of side $\le\mathrm{crit}_k$ (Lemma III.1.2 (d)) and $n_k\ge4\nu_{\max}(k)(\mathrm{crit}_k+\omega_k)+4$ by (H-T); so $Z^{\sim1}$ is small and has an
injective lift to $\mathbb Z^d$ preserving distances (Lemma I.2.10 (e)); all sets below lie in $Z$ and are identified with their lifts. *Obstacles* (R3-03 (iii)).
For $k_1\le i\le j$ put $O_i:=(\Omega^c_i\cup Z_{k_1})\cap Z$, with the overwritten domains (Definition I.3.11; removals at scales $<k$ have already acted on the
localized history, Lemma I.4.3). $O_i\subset Z_i$ (as $\Omega^c_i\subset Z_i$ and $Z_{k_1}\subset Z_i$, Lemma I.4.3 (b)), $O_i$ increases with $i$, and $O_{k_1}=Z_{k_1}$ (as $\Omega^c_{k_1}\subset Z_{k_1}$).
The block $y$ is disjoint from $O_i$ for $i\le j$: $y\subset\Lambda_j\subset\Omega_j\subset\Omega_i$, and $y\cap Z_{k_1}=\varnothing$ ($Z_{k_1}$ is a union of $k_1$-blocks and $y$ a $j$-block with $j\ge k_1$, $y\not\subset Z_{k_1}$).
*Enclosure forces a large component.* Let $x\in y$ and suppose $x$ is enclosed by $O_i$ in $\mathbb Z^d$ (every nearest-neighbour path from $x$ that leaves every finite set
meets $O_i$). Let $\{C'_m\}$ be the components of $Z_i$ in the sense of Definition I.2.11 (width $\omega_i$); as fine sets they are at mutual distance $\ge(\omega_i-1)ML^i\ge2$, so
the sets $A_m:=O_i\cap C'_m$ are pairwise $*$-separated. By Lemma S (Lemma I.3.13 (a), (b), with the box $Q:=y$, disjoint from $O_i$), $x$ is enclosed by a single
$*$-component $K$ of some $A_m$, and $K$ has sup-diameter $\ge L^j+1$ (R3-03 (iv): the exterior boundary of the finite nn-component containing a box of side $s$
has extent $\ge s+1$ in the coordinate of that side). But $C'_m$ is covered by at most $\nu$ boxes of side $\le\mathrm{crit}_i$ (Lemma III.1.2 (c)), so its sup-diameter is
$\le\nu(\mathrm{crit}_i+\omega_i)$ cubes (Lemma I.2.12 (c)), i.e. $\le\nu(\mathrm{crit}_i+\omega_i)ML^i$ fine units. Hence $L^{j-i}<\nu_{\max}(k)M(\mathrm{crit}_k+\omega_k)\le L^{h_k-2}$ (definition of $h_k$,
§I.1.2), i.e. $i>j-h_k+2$. *Conclusion.* If $i_0=j-h_k+2>k_1$, $x$ is not enclosed by $O_{i_0}$. If $i_0=k_1$, $O_{k_1}=Z_{k_1}$ is the core, a union of boxes at mutual
index distance $\ge\omega_{k_1}$ (Lemma III.1.2 (e)), hence pairwise $*$-separated as fine sets; by Lemma I.3.13 (c) it encloses no point. So there is a path from $x$
to infinity avoiding $O_{i_0}$. It leaves the finite set $Z$; before that it meets $\Omega_k\cap Z$, because the sites of $Z$ within $([2R_{k-1}]+6)ML^k$ of $Z^c$ lie in $\Omega_k$
(Lemma I.3.5 (d), (e) at scale $k$: $Z\supset(\Omega''^c_k)^{\sim([2R_{k-1}]+6)}$). Stop at the first site of $\Omega_k$. The earlier sites lie in $Z\cap\Omega^c_k\setminus O_{i_0}=\bigcup_{i=i_0}^{k-1}\Lambda_i\cap Z^c_{k_1}$.
Project back to the torus. $\square$

The landed Lean covers the lattice part: `Balaban.LatticeGeom.enclosed_by_single_component`, `enclosed_component_diam`, `not_enclosed_boxes`
(`LargeField/Geometry/LemmaS.lean`), resting on `exteriorBoundary_starConn` (`Timar.lean`), and its torus version via the box lift (W37).

### III.4.3 Lemma CH

**Lemma III.4.4 (Lemma CH; ARCH §3.8 Step 3, R3-03 (i)–(v)).** Let $y$ be a window block of layer $j$, $i_0$ as in Lemma III.4.3. There is a chain
$y=x_0,x_1,\dots,x_p$ in $\mathcal G$, $x_p$ a terminal block, all of whose vertices except $x_p$ are window blocks of layers $\ge i_0$, which visits every vertex at most once.
Let $(\bar\delta_i)_{k_1\le i\le k}$ be positive with $\bar\delta_{i+1}\le\bar\delta_i$, $\bar\delta_i\le e^{\epsilon}L^{\frac{d-2}2(j-i)}\bar\delta_j$ ($i\le j$), $\sum_{i\ge i_0}\bar\delta_i\le4\bar\delta_{i_0}$, and $\bar c>0$. If a configuration
satisfies, along the chain, $|\psi(x_{m+1})-\psi(x_m)|\le\bar c\,\bar\delta_i$ for every intra edge in layer $i$ and $\le dL\bar c\,\bar\delta_i$ for every cross edge between layers $i+1$ and
$i$, then
$$|\psi_j(y)-\psi_k(x_p)|\ <\ \hat W_k\,\bar c\,\bar\delta_j,\qquad\hat W_k:=4e^{\epsilon}(1+2dL)\,\nu_{\max}(k)\,(LM\mathrm{crit}_k)^d\,L^{\frac{d-2}2(h_k-2)}\ \le\ C_{\hat W}\hat\lambda_k^{\,w_0-2},\tag{2.26′}$$
with $C_{\hat W}:=4e^{\epsilon}(1+2dL)L^{d-2}(2C_\nu)^{d/2}(LM)^d(2\sqrt dM)^{\frac{d-2}2}\big(2c_0(R_{\rm base}+1)+10\big)^d\big(2c_0(R_{\rm base}+1)+2R_{\rm base}+L+21\big)^{\frac{d-2}2}$.

*Proof.* *Chain* (R3-03 (i)). Take the path of Lemma III.4.3 and the sequence of blocks of $\mathbb B_k$ containing its sites. Consecutive sites in the same block
give nothing; in the same layer and different blocks, an intra edge; in different layers, a cross edge by Lemma III.4.2 (b), whose $b_-$ consists of window
blocks of layer $\ge i_0$ (Lemma III.4.2 (a); the site $x'$ is a path site, so its layer is $\ge i_0$). The last site is in $\Omega_k\cap Z$; its $k$-block is terminal. So a chain
exists in the subgraph of $\mathcal G$ spanned by the window blocks of layers $\ge i_0$ and the terminal blocks; take a shortest one. It visits each vertex at most
once. *Count.* Each vertex of layer $i$ has at most two chain edges, so the chain has at most $B_i$ intra edges in layer $i$ and at most $2B_i$ cross edges between
layers $i+1$ and $i$. Hence
$$|\psi_j(y)-\psi_k(x_p)|\le\sum_{i=i_0}^{k-1}B_i(1+2dL)\bar c\,\bar\delta_i\le(1+2dL)\nu_{\max}(k)(LM\mathrm{crit}_k)^d\bar c\cdot4\bar\delta_{i_0}\le\hat W_k\bar c\,\bar\delta_j,$$
using $j-i_0\le h_k-2$. *Constant.* $L^{h_k-2}\le L\cdot2\sqrt d\,\nu_{\max}(k)M(\mathrm{crit}_k+\omega_k)$, $\nu_{\max}(k)\le2C_\nu\hat\lambda_k^{p_2}$, $\mathrm{crit}_k\le(2c_0(R_{\rm base}+1)+10)\hat\lambda_k^2$,
$\mathrm{crit}_k+\omega_k\le(2c_0(R_{\rm base}+1)+2R_{\rm base}+L+21)\hat\lambda_k^2$ ((F5)); the exponent of $\hat\lambda_k$ is $p_2+2d+\frac{(p_2+2)(d-2)}2=\frac{p_2d}2+3d-2=w_0-2$. Strictness: the
first inequality is strict because $\bar\delta_i>0$ and the sum has at least one term. $\square$

**Lemma III.4.5 (the sequences $\delta_j$ and $\delta_{j,1}$ are admissible).** If the running $\lambda_i\ge12p_0$ for all $i$ ((Λ20)), then $\bar\delta=\delta$ and $\bar\delta=(\delta_{i,1})$
satisfy the hypotheses of Lemma III.4.4: $\delta_{i+n}\le e^{\epsilon}L^{-n/3}\delta_i$ (P7 (2.25)), hence $\sum_{n\ge0}\delta_{i+n}\le4\delta_i$ for $L\ge3$, and
$\delta_i\le e^{\epsilon}L^{\frac{d-2}2(j-i)}\delta_j$ for $i\le j$.

*Proof.* $\delta_i=A_0(\beta_ia)^{-1/2}\lambda_i^{p_0}$, $\beta_{i+n}/\beta_i=L^{n(d-2)}\gamma_{i+n}/\gamma_i$ and $\lambda_{i+n}-\lambda_i\le n\theta+2\epsilon$. For $n\ge0$, with $1+x\le e^x$,
$$\frac{\delta_{i+n}}{\delta_i}\le e^{\epsilon}L^{-\frac{n(d-2)}2}\Big(1+\frac{n\theta+2\epsilon}{\lambda_i}\Big)^{p_0}\le e^{\epsilon}L^{-n(d-2)(\frac12-\frac{p_0}{\lambda_i})}e^{2\epsilon np_0/\lambda_i}\le e^{\epsilon}L^{-\frac{5n}{12}}e^{\frac n{120}}\le e^{\epsilon}L^{-n/3},$$
for $\lambda_i\ge12p_0$, $d\ge3$, $\epsilon\le\frac1{20}$, $L\ge3$. The sum: $e^{\epsilon}/(1-L^{-1/3})\le e^{1/20}/(1-3^{-1/3})<3.5$. For $i\le j$: $\lambda_i\le\lambda_j$ gives
$\delta_i/\delta_j\le(\beta_j/\beta_i)^{1/2}\le e^{\epsilon}L^{\frac{d-2}2(j-i)}$. The same for $\delta_{i,1}=\frac{A_1}{A_0}\delta_i$. $\square$

### III.4.4 Consequences: (2.48)′ and (2.49)′ (P7 Lemmas 2.3–2.4)

The window characteristic functions $\mathcal X_{\rm win}$ contain the conditions (1.24) of Definition II.3.4 on every window block (through $\chi^{\rm new}_j$): adjacent blocks
of the multiscale field in layers $\{n,n-1\}$ differ by $<3dL\delta_n$. Hence every intra edge of $\mathcal G$ in layer $i$ costs $<3dL\delta_i$, and every cross edge $(b_+,y')$ costs
$<3dL\delta_i+d(L-1)3dL\delta_i\le dL\cdot3dL\delta_i$ (go from $y'$ inside $b_-$ to an $i$-block adjacent to $b_+$, Lemma III.4.2 (a)). So Lemma CH applies with $\bar c=3dL$, $\bar\delta=\delta$
(P7: "if $c$ is sufficiently large, for example if $c=3dL$ by (1.24) [5]").

Let $\psi^0_k$ be the solution of (2.34) (Lemma III.3.3), $\phi^0_k:=\phi_k(\mathbb B_k(U_k);\tilde\psi^0_k)$, $\psi^0_{k_1,k}:=\psi(\mathbb B_{k_1,k},\mathbb B_k(U_k);\tilde\psi^0_k)$ (P7 (2.40); the composed field
`composeField` of I-2, BG (6.2)), and $\delta\psi:=\tilde\psi-\psi^0_{k_1,k}$ on $\mathbb B_{k_1,k}$ (P7 (2.46)), $\tilde\psi=Q^*(\mathbb B_{k_1,k},\mathbb B_k)\psi$.

**Lemma III.4.6 ((2.48)′; P7 Lemma 2.3).** On the support of $\mathcal X_{\rm win}$ and of the decompositions' small-field functions $\tilde\chi_k$ and $\chi_k(\Omega^{\sim-3}_k\cap Z)$
(Definition III.5.1), $\delta\psi=0$ on $\mathbb B_{k_1,k}\cap\Omega_k$, and
$$|\delta\psi|<C_{23}\hat W_k\,\delta_j\quad\text{on }\mathbb B_{k_1,k}\cap\Lambda_j,\ k_1\le j\le k-1,\qquad C_{23}:=3dL+2.\tag{2.48′}$$
*Proof.* As P7 p. 509 [checked], with Lemma CH in place of the reasoning between (2.22) and (2.26). $\delta\psi=0$ on $\Omega_k$ because $\mathbb B_{k_1,k}\cap\Omega_k=\mathbb B_k(W_k)\cap\Omega_k$
and $\psi^0_k=\psi_k$ off $Z_0$ ((2.44)). For $x\in\mathbb B_{k_1,k}\cap\Lambda_j\cap Z^c_{k_1}$, $\tilde\psi(x)=\psi_j(y)$ for the window block $y\ni x$; Lemma CH gives a terminal block $y_k$ with
$|\psi_j(y)-\psi_k(y_k)|<3dL\hat W_k\delta_j$. Then $|\psi_k(y_k)-\psi^0_k(z(x))|\le3K_6\delta_k\cdot d\,M\mathrm{crit}_k$ ($\psi^0_k\in\tilde\Psi(U^\sim_k;3K_6\delta_k)$ by Lemma III.3.3 and $\psi^0_k(y_k)=\psi_k(y_k)$;
a monotone path inside the box $Z$, Lemma III.1.2 (d)), and $|\psi^0_k(z(x))-\psi^0_{k_1,k}(x)|<4K_1K_6\delta_k$ ((2.43), from BG (6.2) and Theorem 5.2 (3)). For $x$ in the core
part ($j=k_1$, $x\in\mathbb B_{k_1}(W)\cap Z_{k_1}$): $W$ reaches at most $2[R_{k_1-1}]+3$ cubes into $Z_{k_1}$, while $\Omega^c_{k_1}$ is at distance $\ge[2R_{k_1-1}]+6$ cubes from
$Z^c_{k_1}$ (Lemma I.3.5 (d), (e)), so $x\in\Omega_{k_1}\cap Z_{k_1}$, where $\psi_{k_1}$ is regular by the small-field functions of the step $k_1-1\to k_1$ (Definition II.5.6,
$\chi_{k_1}(\Omega^{\sim-3}_{k_1})$, $\chi'_{k_1}$); a path of at most $d(2[R_{k_1-1}]+4)M$ blocks to a window block adds $\le3d(2[R_{k_1-1}]+4)M\delta_{k_1}\le\hat W_k\delta_{k_1}$. Finally
$3dK_6M\mathrm{crit}_k+4K_1K_6\le\hat W_k$ by (Λ21) and $\delta_k\le\delta_j$. $\square$

**Lemma III.4.7 ((2.49)′; P7 Lemma 2.4, cited input P3 Proposition 2.1).** The function $\delta\phi_{k_1,k}:=\phi_k(\mathbb B_{k_1,k};\tilde\psi)-\phi_k(\mathbb B_{k_1,k};\psi^0_{k_1,k})$ and its multiplier satisfy, for
$y\in\Lambda_j\cap\Omega^c_{j+1}\cap(Z^c_{k_1})^\sim$,
$$|\delta\phi_{k_1,k}|,\ L^j|\partial\delta\phi_{k_1,k}|,\ L^{2j}|\Delta\delta\phi_{k_1,k}|,\ L^{2j}|\delta\alpha_{k_1,k}|\ <\ C_{24}L^{\frac{d+2}2}\hat W_k\,\delta_j\,e^{-\frac14\gamma_0d(y,(\Omega^c_k)^\sim)},\qquad C_{24}:=2K_3C_{23},\tag{2.49′}$$
(fine units; P7's $\eta$-scale derivatives). *Proof.* P7 p. 509 [checked]: P3 Proposition 2.1 (in the project: the perturbation theorem BG Prop 5.1 with the
decay of the Green functions G-2, LOC) applied to the data change $\delta\psi$ bounded by (2.48′); the numbers $C_{23}\hat W_k\delta_j$ differ at consecutive $j$ by at most
$e^{\epsilon}L^{\frac{d-2}2}\le2L^{\frac{d-2}2}$ (Lemma III.4.5), which gives the factor $L^{\frac{d+2}2}$. The smallness hypothesis $C_{23}\hat W_k\delta_{k_1}\le c'_6$ is (Λ22). *Status:* cited (P7, with $\hat W_k$
in place of $54dK_1K_6L^2MR_j$). $\square$

All bounds of this section hold for the analytic extensions with $\delta$ replaced by $2\varepsilon$ (P7 Lemma 2.2, last sentence [checked]), on the domain where the
characteristic functions hold for the real part.

---

## III.5 The decompositions and the kept operators of the first kind (P7 pp. 501–505, 512)

### III.5.1 The small-field functions of $R$

**Definition III.5.1 (the five small-field functions of $R$).** With the notation of §III.0.2 and §III.3:
1. *(P7 (2.18))* $\tilde\chi_k:=\mathbf 1\big[\psi_k\in\tilde\Psi_k(Z^c_0\cap(\Omega^c_k)^{\sim3};3\delta_k)\big]$: $|\partial^1\psi_k(b)|<3\delta_k$ for the bonds $b$ of $T^{(k)}_1$ in $Z^c_0\cap(\Omega^c_k)^{\sim3}$ and $||\psi_k(z)|-1|<3\delta_k$
   for its points (P7 p. 501 [checked]: "the space $\tilde\Psi_k(X;\delta)$ ... is defined by the conditions $|(\partial^1\psi_k)(b)|<\delta$ ... and $||\psi_k(z)|-1|<\delta$").
2. *(P7 p. 502, "the second decomposition")* $\chi_S:=\prod\chi_k(\square)$ over the $\pi_k$-cubes $\square\subset Z''^c_0\cap(\Omega^c_k)^{\sim3}\cap Z$, $\chi_k(\square)$ of Definition II.3.2 item 1 at scale $k$.
3. *(P7 p. 503)* $\chi^0:=\prod\chi^0_{k_1,\frac12}(\square)$ over the $\pi_{k_1}$-cubes $\square\subset U^c\cap U^{\sim6}$ (local $U$), where $\chi^0_{k_1,\frac12}(\square)$ is $\chi_{k_1}(\square)$ with $\delta_{k_1}$ replaced by $\frac12\delta_{k_1}$
   and $\psi_{k_1}$ by $\psi'_{k_1}$: $\psi'_{k_1}:=\psi_{k_1}$ on $\Lambda_{k_1}\cap U^{\sim3}$, $:=\psi_0$ on $\Lambda_{k_1}\cap(U^{\sim3})^c$ (P7 [checked]). It reads $\psi'_{k_1}$ on $(U^c)^{\sim3}\cap U^{\sim9}\subset\Lambda_{k_1}\cap Z^c_{k_1}$ and
   $\psi_k$ through $\psi_0$.
4. *(P7 (2.61))* $\chi'':=\mathbf 1\big[|\delta\psi(y)|<\delta_{j,1}\ \text{for all blocks }y\text{ of }D''\text{ of layer }j\big]$, $D'':=(\mathbb B_k\cap Z^c_{k_1}\cap\Omega^c_k)\setminus(\Lambda_{k_1}\cap U^{\sim3})$, with $\delta\psi$ of
   §III.4.4. *Reading* (UNCERTAIN, minor): P7 (2.61) writes "$\psi''=\delta\psi$ on $Z^c_{k_1}\cap\Omega^c_k\cap\mathbb B_k$, $\chi''$ on $\Lambda_j\cap Z^c_{k_1}$", but (3.7) integrates $\psi_{k_1}$ on $U^{\sim3}$ and
   $\psi''$ separately, and p. 516 says $\chi''$ improves (2.48) only on $(U^{\sim3}_{k_1})^c$; we take $D''$ as above.
5. *(P7 (3.20))* $\chi_{Z''}:=\prod\chi_k(\square)$ over the $\pi_k$-cubes $\square\subset Z''_0\cap Z$.

*Change to P7's $Z''_0$ (needed by item 2).* The violation that makes $\chi_k(\square)=0$ may lie anywhere in $\square^{\sim3}$, and inside $Z_0$ no new restriction can be
paid for (P7 p. 506: "the main actions localized on it could have been already used"). P7's $Z''_0$ (cubes meeting $Z_{k_3}$) does not keep $\square^{\sim3}$
away from $Z_0$ (the lineage grows by less than one $\pi_k$-cube between $k_2$ and $k_3$). Definition III.3.1 therefore uses $k_3:=\min\{j:L^{-(k-j)}L[R_j]\ge8\}$ and
$Z''_0:=(\text{the }\pi_k\text{-cubes meeting }Z_{k_3})^{\sim3}$. **Lemma III.5.0.** (a) Every $\pi_k$-cube $\square\subset Z''^c_0$ has $\square^{\sim3}\cap Z_0=\varnothing$. (b) $(Z''_0)^{\sim3}\subset\Omega^c_{k_3+1}\subset Z$ (as
fine sets, $\pi_k$-cube neighbourhoods). (c) $\mathrm{diam}_k(Z''_0)<D''_0M$, $D''_0:=9(2c_0+1)+8$, and $L^{-n_3}<9/[R_{k_3}]$. *Proof.* (a) $Z_0$ lies in the $\pi_k$-cubes meeting
$Z_{k_3}$ ($Z_{k_2}\subset Z_{k_3}$, a $k$-block lies in a $\pi_k$-cube); a cube outside the $3$-neighbourhood is at index distance $\ge4$ from them. (b) By Lemma III.1.2 (f)
at $j=k_3$ the margin of $Z_{k_3}$ to $\Omega_{k_3+1}$ is $\ge([R_{k_3}]+4)LM$ scale-$k_3$ units $=([R_{k_3}]+4)LML^{-n_3}\ge8M$ scale-$k$ units, by the definition of $k_3$;
$(Z''_0)^{\sim3}$ lies within $7M$ of $Z_{k_3}$. (c) Lemma III.3.2 (a)–(c): $L^{-n_3}L[R_{k_3}]<8\cdot\frac98L$. $\square$
The constant $D_0$ of $Z_0$ is unchanged; the late-scale constant attached to $Z''_0$ is $D''_0$ (ARCH (M7): "$15M$").

### III.5.2 Outcomes and labels

**Definition III.5.2 (the outcomes of $R$ on a ripe component; D-III.2).** Insert the binary decompositions $1=\chi+(1-\chi)$ for $\chi=\tilde\chi_k,\chi_S,\chi^0,\chi''$ in this
order into the kernel of $\mathbb T^{\rm pre}_k(Z,\mathfrak a)$ (Lemma III.1.3):
$$K^{\rm pre}=\underbrace{K^{\rm pre}(1-\tilde\chi_k)}_{\varkappa_1}+\underbrace{K^{\rm pre}\tilde\chi_k(1-\chi_S)}_{\varkappa_2}+\underbrace{K^{\rm pre}\tilde\chi_k\chi_S(1-\chi^0)}_{\varkappa_3}+\underbrace{K^{\rm pre}\tilde\chi_k\chi_S\chi^0(1-\chi'')}_{\varkappa_4}+\underbrace{K^{\rm pre}\tilde\chi_k\chi_S\chi^0\chi''}_{\text{to }R}.$$
The terms $\varkappa_1,\dots,\varkappa_4$ are the **kept outcomes of the first kind (K1)**: the kernel $K^{(\varkappa_i)}$ with $b^{(\varkappa_i)}:=b^{\rm pre}$, on the variables of $\mathbb T^{\rm pre}_k(Z,\mathfrak a)$.
The last term is normalized by $R$ (§III.8) and then split by $1=\chi_{Z''}+(1-\chi_{Z''})$ into the **kept outcome of the second kind (K2)**, label $\varkappa_5$, and the
**removed outcome**. The label set is $\mathfrak K=\{\varkappa_1,\dots,\varkappa_5\}$, with $C_{\rm dec}(\varkappa):=5$, so $\sum_{\varkappa}C_{\rm dec}(\varkappa)^{-1}=1$.

All five functions are indicators of Borel sets, $O(N)$-invariant under the simultaneous rotation of all spin-valued variables ($\psi_0$ rotates with $\psi_k$, and
$\psi^0_k$, $\psi^0_{k_1,k}$ are equivariant by Lemma III.3.3 and BG Theorem 6.1), and contain no $h$ and no $g$ ((A-III.2)). So the K1 kernels satisfy (S1)-type
measurability, $g$-independence, invariance and (S5) (§III.9.3), and vanish unless $\chi^{\rm dom}_k(Z,\mathfrak a)=1$ because $K^{\rm pre}$ does.

### III.5.3 The small factors

Write $\mathcal G^\natural$ for the exponent of the composed Gaussian on $Z^c_0\cap\Omega^c_k$ (Lemma III.2.3) and $\mathcal A_{\rm win}:=\sum_j\mathcal A_{j+1}(X_j)$; by Lemma III.2.2,
$\mathcal A_{\rm win}=\beta_kA^*_k(X_{\rm win},\mathbb B_k;\psi,\phi_{k_1,k})-C_{k_1,k}$. By (Λ20), $\lambda_j\ge\lambda_{k_1}\ge\hat\lambda_k/(4c_*)$ for $j\in[k_1,k]$ (Lemma III.1.2 (a)), and $\beta_j\delta_j^2=A_0^2\lambda_j^{2p_0}/a$.
The *canonical* coefficients of $A^*_k(\cdot,\mathbb B_k)$ satisfy $\beta^{(k)}_j\ge e^{-2\epsilon}\beta_j$.

**Lemma III.5.3 (small factors; P7 pp. 501–505, 512, (2.33), (2.62), P6 (3.7)–(3.8)).** On the support of $K^{\rm pre}$ (all window characteristic functions hold):
(a) *($\varkappa_1$)* if $\tilde\chi_k=0$: $\frac12\mathcal G^\natural+\mathcal A_{\rm win}+C_{k_1,k}\ \ge\ \gamma_1:=\frac98(1-\eta_k)\gamma_0A_0^2\lambda_k^{2p_0}/a-\frac12$;
(b) *($\varkappa_2$)* if $\tilde\chi_k=1$, $\chi_S=0$: $\mathcal G^\natural+\mathcal A_{\rm win}+C_{k_1,k}\ \ge\ \gamma_2:=\frac{1-\eta_k}{144K_1^2}\gamma_0A_0^2\lambda_k^{2p_0}/a-1$;
(c) *($\varkappa_3$)* if $\tilde\chi_k=\chi_S=1$, $\chi^0=0$: $\mathcal A_{\rm win}+C_{k_1,k}\ \ge\ \gamma_3:=\frac{e^{-2\epsilon}\gamma_0A_0^2\lambda_{k_1}^{2p_0}}{72aK_1^2\hat W_k^2}$;
(d) *($\varkappa_4$)* if $\tilde\chi_k=\chi_S=\chi^0=1$, $\chi''=0$: the curly bracket of (2.58) (Lemma III.6.3) satisfies $\beta_k\{\cdots\}\ \ge\ \gamma_4:=\frac{e^{-2\epsilon}\gamma_0A_1^2\lambda_{k_1}^{2p_0}}{2a\hat W_k^2}-1$;
(e) *($\varkappa_5$)* if $\chi_{Z''}=0$ and $\chi_{Z_0}=1$: $\beta_kA^*_k\big(Z;\psi_k,\phi_k(\mathbb B_k(Z^\approx);\tilde\psi_k)\big)\ \ge\ \gamma_5:=\frac{1}{72K_1^2}\gamma_0A_0^2\lambda_k^{2p_0}/a$.
Consequently, with $p_R=2p_0-2w_0$ and $A'_3:=\frac{e^{-2\epsilon}\gamma_0}{8a\,C_{\hat W}^2(4c_*)^{2p_0}}\min\{\frac{A_0^2}{72K_1^2},\frac{A_1^2}2\}$, for $\hat\lambda_k\ge\lambda_*$ ((Λ24)):
$$\gamma_i-\log C_{\rm dec}(\varkappa_i)\ \ge\ 2A'_3\hat\lambda_k^{p_R}\qquad(i=1,\dots,5).\tag{III.5.1}$$

*Proof.* Everything uses LF-1 (Theorem II.4.1), which holds for every generating set and every field, with $\gamma_0=\frac1{28d}$, in the scaled form: for a
generating set at level $q$ and $X$, $\beta_qA^*_q(X,\mathbb B;\psi,\phi)\ge\gamma_0\sum_n\frac{\beta^{(q)}_n}2\big[\sum_{P_n(X)}|\psi_n(y)-\psi_n(y')|^2+\sum_{P^\times_n(X)}|\psi_n(b_+)-(Q\psi_{n-1})(b_-)|^2\big]$ and, for $|\phi|=1$,
$\ge\gamma_0\sum_n\beta^{(q)}_n\sum_y\frac12(|\psi_n(y)|-1)^2$. Actions are additive over disjoint domains (the half-bonds of P5 (1.5)) and non-negative, so they may be restricted.

(a) If a bond $b\subset Z^c_0\cap(\Omega^c_k)^{\sim3}$ has $|\partial^1\psi_k(b)|\ge3\delta_k$, or a point has $||\psi_k|-1|\ge3\delta_k$, LF-1 for the single-scale action on $Z^c_0\cap Z$ gives
$\beta_kA^*_k(Z^c_0\cap Z;\psi_k,\phi_{k_1,k})\ge\frac92\gamma_0\beta_k\delta_k^2$. Since $\mathcal A_{\rm win}+C_{k_1,k}=\beta_kA^*_k(X_{\rm win},\mathbb B_k)\ge\beta_kA^*_k(Z^c_0\cap Z,\mathbb B_k)$ (additivity,
$Z_{k_1}\subset Z_0$), (2.17′) gives $\frac12\mathcal G^\natural+\mathcal A_{\rm win}+C_{k_1,k}\ge\frac12\big(\mathcal G^\natural+\beta_kA^*_k(Z^c_0\cap Z,\mathbb B_k)\big)\ge\frac14(1-\eta_k)\frac92\gamma_0\beta_k\delta_k^2-\frac12=\gamma_1$. (P7 p. 502 uses a
segment of length $<6M[R_{k-1}]$ to check the hypothesis of P6 (3.6); LF-1 (b) needs no such hypothesis, D-III.10.)
(b) $\chi_k(\square)=0$ for some $\square\subset Z''^c_0\cap(\Omega^c_k)^{\sim3}\cap Z$. If $\psi_k\in\tilde\Psi(T_k(\square^{\sim3});\delta)$ with $K_1\delta<\delta_k$, then by BG Theorem 5.2 (3) (landed `theorem52_exists`
bounds) the background of $\mathbb B_k(\square^{\sim2})$ satisfies every inequality of Definition II.3.1 with $\delta_k$, and the data lie in $\mathcal D_{\mathbb R}$ by (Λ17), so $\chi_k(\square)=1$. Hence
a bond in $\square^{\sim3}$ has $|\partial^1\psi_k|\ge\delta_k/(2K_1)$ or a point has $|\psi_k\cdot\psi_k-1|\ge\delta_k/(2K_1)$, hence $||\psi_k|-1|\ge\delta_k/(6K_1)$ (as $|\psi_k|\le2$ on $\tilde\chi_k=1$). By Lemma III.5.0 (a)
and $\square^{\sim3}\subset(\Omega^c_k)^{\sim6}\subset Z$, the violation lies in $Z^c_0\cap Z$; LF-1 and (2.17′) give $\ge\frac12(1-\eta_k)\frac{\gamma_0\beta_k\delta_k^2}{72K_1^2}-1$.
(c) $\chi^0(\square)=0$ for some $\square\subset U^c\cap U^{\sim6}$. As in (b) with $\frac12\delta_{k_1}$ and $\delta^0:=\delta_{k_1}/(3K_1)$ ($K_1\delta^0<\frac12\delta_{k_1}$): one of P7 (2.21) [checked] holds,
(i) $|\partial^1\psi_{k_1}(b)|\ge\delta^0$ or (ii) $|\psi_{k_1}\cdot\psi_{k_1}-1|\ge\delta^0$ at a bond or point of $\square^{\sim3}\cap U^{\sim3}\cap\Lambda_{k_1}$, or (iii) $|\psi_{k_1}(y)-\psi_0|\ge\delta^0$ at a block $y$ of
$\square^{\sim3}\cap\partial(U^{\sim3}\cap T^{(k_1)})$. These blocks are window blocks of layer $k_1$ (Lemma III.1.2 (f)). In cases (i), (ii), LF-1 for $A^*_k(X_{\rm win},\mathbb B_k)$ gives
$\ge\gamma_0e^{-2\epsilon}\beta_{k_1}(\delta^0)^2/18=\gamma_0e^{-2\epsilon}A_0^2\lambda_{k_1}^{2p_0}/(162K_1^2a)$. Case (iii) is the chain argument (P7 (2.22)–(2.30)): put $c:=(6K_1\hat W_k)^{-1}$ and suppose every
intra edge of $\mathcal G$ in layer $i$ has $|\psi_i(y)-\psi_i(y')|<c\delta_i$ and every cross pair has $|\psi_{i+1}(b_+)-(Q\psi_i)(b_-)|<c\delta_i$ (then every cross edge costs $<dLc\delta_i$,
Lemma III.4.2 (a)). Lemma CH from $y$ ($j=k_1$, $i_0=k_1$) gives a terminal block $y_k$ with $|\psi_{k_1}(y)-\psi_k(y_k)|<\hat W_kc\,\delta_{k_1}=\delta_{k_1}/(6K_1)$ (Lemma III.4.5). From $y_k$ go
to the point $z_0$ of the boundary layer of $Z_0$ obtained by clamping the coordinates of $y_k$ to the box $Z_0^{+1}$, along a monotone path that first moves a
coordinate in which $y_k$ lies outside $Z_0$; the path stays in the box $Z$ and outside $Z_0$, has at most $dM\mathrm{crit}_k$ bonds, each with $|\partial^1\psi_k|<3dL\delta_k$ (by $\tilde\chi_k$
and the conditions (1.24) at scale $k$), so $|\psi_k(y_k)-\psi_k(z_0)|<3d^2LM\mathrm{crit}_k\delta_k$; and $|\psi_k(z_0)-\psi_0|<C_{2.20}\delta_k$ by (2.20′). With $\delta_k\le e^{\epsilon}L^{-n_1/3}\delta_{k_1}$
(Lemma III.4.5) and (Λ23), $(3d^2LM\mathrm{crit}_k+C_{2.20})\delta_k\le\delta_{k_1}/(6K_1)$, so $|\psi_{k_1}(y)-\psi_0|<\delta_{k_1}/(3K_1)=\delta^0$, contradicting (iii). Hence some intra edge or cross pair
violates the bound with $c$, and LF-1 gives $\ge\gamma_0e^{-2\epsilon}c^2\min_{i\ge k_1}\beta_i\delta_i^2/2\ge\gamma_3$ (and $\gamma_3$ is smaller than the bound of (i), (ii) as $\hat W_k\ge2$).
(d) $|\delta\psi(y)|\ge\delta_{j,1}$ at a block $y$ of $D''$, layer $j$. $\delta\psi=0$ on terminal blocks (Lemma III.4.6). With $c'':=1/\hat W_k$, if every edge of the chain of Lemma CH
from $y$ satisfied the bounds of Lemma III.4.4 for $\delta\psi$ with $\bar c=c''$, $\bar\delta=(\delta_{i,1})$ (admissible by Lemma III.4.5), we would get $|\delta\psi(y)|<\delta_{j,1}$. So some intra edge
or cross pair of $\delta\psi$ has $|\cdot|\ge c''\delta_{i,1}$, $i\ge k_1$. The curly bracket of (2.58) is $\ge$ the LF-1 bracket of $\delta\psi$ on $X_{\rm win}$ (the fluctuation action $\delta A^*_k$ has the
same first two terms as $A^*_k$ in $(\delta\psi,\delta\phi_{k_1,k})$, LF-1 holds for every field; its third term is bounded by (2.60)′, its last terms are $\ge0$, and the composed
Gaussian term is $\ge0$; P7 p. 512 [checked]). So $\beta_k\{\cdots\}\ge\gamma_0e^{-2\epsilon}(c'')^2\beta_i\delta_{i,1}^2/2-1\ge\gamma_4$.
(e) As (b), for $\square\subset Z''_0$, with the single-scale action of $\rho_{k,0}(Z)$ on $Z\supset\square^{\sim3}$ (Lemma III.5.0 (b)), on which $|\psi_k|\le2$ by $\chi_k$ of $Z\cap Z''^c_0$, $\tilde\chi_k$ and $\chi_{Z_0}$.
*(III.5.1).* $\lambda_k\ge\hat\lambda_k/2$, $\lambda_{k_1}\ge\hat\lambda_k/(4c_*)$, $\hat W_k\le C_{\hat W}\hat\lambda_k^{w_0-2}$, $\eta_k\le\frac12$; each $\gamma_i\ge4A'_3\hat\lambda_k^{2p_0-2w_0+4}-3\ge4A'_3\hat\lambda_k^{p_R}-3$ for $i=3,4$, and $\gamma_1,\gamma_2,\gamma_5$ are
larger (exponent $2p_0$); (Λ24) absorbs $3+\log5$. $\square$

*Comparison with P7.* P7's factors are $\exp(-\frac92\gamma_0p_0^2(\beta_k))$ for (2.18), $\exp(-\frac{\gamma_0}{2\cdot6^dK_1^2}p_0^2M^{-d}|S''_k|)$ (P6 (3.8)), $\exp(-\frac12\gamma_0(64K_1LMR_{k_1})^{-2}p_0^2(\beta_{k_1}))$ for (2.21)
(2.30), and $\exp(-\frac12\gamma_0(16LMR_j)^{-2}p_1^2+1)$ for (2.62). Here $64K_1LMR_{k_1}$ and $16LMR_j$ become $6K_1\hat W_k$ and $\hat W_k$: the window has $\nu$ pieces and the chain is
longer. The exponent $2p_0-2w_0=p_R>p_2+2d$ is what LF-2 needs ((K), (Λ10)). The subset entropy of P7 (2.33) ("$+M^{-d}|(Z^c_{k_1})^{\sim3}\cap Z^{\sim3}_{k_1}|$") does not occur
(D-III.2).

---

## III.6 The cancellation of the main actions (P7 pp. 506–512, (2.34)–(2.60))

### III.6.1 Backgrounds of the window

**Definition III.6.1 (P7 (2.40), (2.46), (2.50)).** On the support of $\tilde\chi_k$ (and of the window characteristic functions), with $\psi^0_k$ of Lemma III.3.3 for $\delta=3\delta_k$:
$\phi^0_k:=\phi_k(\mathbb B_k(U_k);\tilde\psi^0_k)$ and $\alpha^0_k$ its multiplier (massless, $U_k=Z^\approx$); $\psi^0_{k_1,k}:=\psi(\mathbb B_{k_1,k},\mathbb B_k(U_k);\tilde\psi^0_k)$, the composed field of BG (6.2)
(landed `composeField`) with the weights $a_n$ of (II.1); $\delta\psi:=\tilde\psi-\psi^0_{k_1,k}$ on $\mathbb B_{k_1,k}$; $\delta\phi_{k_1,k}:=\phi_k(\mathbb B_{k_1,k};\tilde\psi)-\phi^0_k$ (by I-2, landed `theorem73_real`,
$\phi_k(\mathbb B_{k_1,k};\psi^0_{k_1,k})=\phi^0_k$ on $\Omega_1(\mathbb B_{k_1,k})$, so this is P7 (2.50)). Write $r_z:=\psi_k(z)-(Q_k\phi^0_k)(z)$ for the $k$-blocks $z\subset Z^c_0$ (there $\psi^0_k=\psi_k$).

**Lemma III.6.2 (P7 Lemma 2.2, (2.41)–(2.45); cited).** Under the characteristic functions introduced so far, in scale-$k$ units:
$|Q^*_k\psi^0_k-\phi^0_k|,|\partial\phi^0_k|,|\Delta\phi^0_k|,|\alpha^0_k|<3K_1K_6\delta_k$ on $U_k$ (2.41); the same quantities are $<\frac98\delta_k$ on $Z''^c_0\cap U_k$ (2.42); $|\psi^0_k(z)-\psi^0_{k_1,k}(x)|<4K_1K_6\delta_k$
for $x\in\Delta_k(z)\subset\Omega^c_k$ (2.43); $\psi^0_k-\psi^0_{k_1,k}=0$ on $\Omega_k\cap U^\sim_k$ (2.44); and (2.45). In particular $|r_z|<3K_1K_6\delta_k$. The analytic extensions satisfy the same bounds with
$\delta_k$ replaced by $2\varepsilon_k$. *Source.* P7 p. 508 [checked]: (2.41) from BG Theorem 5.2 (3) and Lemma III.3.3; (2.43)–(2.45) from BG (6.2) and (2.41); (2.42) by the
comparison argument of Lemma 2.5 (§III.7); with our larger $Z''_0$ (Lemma III.5.0) the region $Z''^c_0$ is smaller, so (2.42) holds a fortiori.

The pair $(\psi^0_k,\phi^0_k)$ minimizes $A_k(\mathbb B_k(U_k);\tilde\psi_k,\phi)$ jointly over $\psi_k\restriction_{Z_0}$ and $\phi$ (P7 (2.34), (2.51): "$\inf_{\psi_k}\inf_\phi$"); the stationarity in $\psi_k\restriction_{Z_0}$ gives
$$\psi^0_k-Q_k\phi^0_k=0\ \text{on }Z_0,\qquad\text{hence}\qquad\psi^0_{k_1,k}-Q(\mathbb B_{k_1,k})\phi^0_k=0\ \text{on }Z_0\qquad(\text{P7 (2.52)}),\tag{2.52}$$
the second by BG (6.2) ($\psi^0_{k_1,k}=Q_n\phi^0_k+\frac{a_k}{a_n}L^{2(n-k)}(\psi^0_k-Q_k\phi^0_k)$ on the layer $n$).

### III.6.2 The cancellation identity with the actual composed transformation

**Lemma III.6.3 (the fundamental formula; P7 (2.53)–(2.58); perturbative composition lemma for O-8′, audit P2-05).** On the domain of Definition III.6.1, real and
complex, with $\mathcal G^\natural$ the exponent and $\mathrm{const}^\natural:=\prod_z(\beta_ka^\natural_z/2\pi)^{N/2}$ the constant of the composed kernel (III.1.4) on $Z^c_0\cap\Omega^c_k$,
$$\mathcal G^\natural+\beta_kA^*_k\big(X_{\rm win},\mathbb B_k;\psi,\phi_{k_1,k}\big)-\log\mathrm{const}^\natural=\beta_kA^*_k(Z;\psi^0_k,\phi^0_k)-\beta_kA^*_{0,k}(Z_{k_1};\phi^0_k)+\beta_k\{\cdots\}+\beta_kS_{\rm st}-\log\mathrm{const}+C^\natural,\tag{2.58′}$$
where $\mathrm{const}:=\prod_z(\beta_ka_z/2\pi)^{N/2}$ (ideal), $A^*_{0,k}$ is the main action without the block terms of the renormalization transformations (P7 p. 511),
$$\{\cdots\}:=\sum_{z\subset Z^c_0\cap\Omega^c_k}\tfrac12a^\natural_z|\mathcal Q_z\delta\psi|^2+\delta A^*_k\big(X_{\rm win},\mathbb B_k;\delta\psi,\delta\phi_{k_1,k}\big)+\nu_k\langle\delta\phi_{k_1,k},\phi^0_k-h\rangle_{X_{\rm win}},\qquad S_{\rm st}:=\big\langle\tfrac12[(\delta\phi_{k_1,k})_++(\delta\phi_{k_1,k})_-],\partial\phi^0_k\big\rangle_{{\rm st}(X_{\rm win})},$$
$\delta A^*_k$ the fluctuation action of P5 (2.24), and the remainder $C^\natural=C^\natural_0+C^\natural_1$ satisfies
$$|C^\natural_1|\le\tfrac38\sum_z\beta_ka^\natural_z|\mathcal Q_z\delta\psi|^2,\qquad|C^\natural_0|\le\begin{cases}1&\text{on the real domain},\\ C_\natural\,\hat\lambda_k^{2d+1}&\text{on the complex domain},\end{cases}\tag{III.6.1}$$
with $C_\natural$ a constant of rows 0–11 (it is part of $L_{\rm res}$, (III.8.4)). With the ideal composition ($z_i\equiv1$, $\beta_j$ canonical) $C^\natural=0$ and $a^\natural=a$: this is P7 (2.58).

*Proof.* *Expansion of the action* (P7 (2.53) [checked, text layer]). By (2.50) and P5 (2.23) (the expansion of the action at a stationary point; the
background $\phi^0_k$ solves (EL) for $\mathbb B_{k_1,k}$ with the datum $\psi^0_{k_1,k}$ by I-2),
$$A^*_k(X_{\rm win},\mathbb B_k;\psi,\phi_{k_1,k})=A^*_k(X_{\rm win},\mathbb B_k;\psi^0_{k_1,k},\phi^0_k)+\langle\delta\psi,a(\mathbb B_{k_1,k})(\psi^0_{k_1,k}-Q(\mathbb B_{k_1,k})\phi^0_k)\rangle_{X_{\rm win}}+\nu_k\langle\delta\phi,\phi^0_k-h\rangle+\delta A^*_k+S_{\rm st}.$$
The second term vanishes on $X_{\rm win}\cap Z_0$ by (2.52) and on $\Omega_k$ since $\delta\psi=0$ there (Lemma III.4.6); on $Z^c_0\cap\Omega^c_k$, by BG (6.2) and
$a_nL^{-2n}\cdot\frac{a_k}{a_n}L^{2(n-k)}=a_kL^{-2k}$, it equals (P7 (2.54))
$$\sum_{z}a_k\,(\mathcal Q_z\delta\psi)\cdot r_z\qquad(\text{in scale-}k\text{ units; }\mathcal Q_z\text{ the volume average over }z).$$
*Expansion of the composed Gaussian.* On $z\subset Z^c_0\cap\Omega^c_k$ the leaves are window leaves outside $U^{\sim3}$ (Lemma III.3.2 (d)), and
$\psi_k(z)-\mathcal Q^\natural_z\tilde\psi=\varrho_z-\mathcal Q_z\delta\psi-s_z$, with $\varrho_z:=\psi_k(z)-\mathcal Q_z\psi^0_{k_1,k}$ and $s_z:=\sum_xw_x(\varpi_{n_x}-1)\tilde\psi(x)$. By BG (6.2) and (C1),
$\mathcal Q_z\psi^0_{k_1,k}=(Q_k\phi^0_k)(z)+a_k(u_k-u^{(k)}_z)r_z$, so $\varrho_z=a_ku^{(k)}_zr_z=\frac{a_k}{a_z}r_z$ (this is P2 (4.18) in the form used in P7 (2.55)). Hence, with
$a^\natural_z=a_z(1+\eta_z)$,
$$\tfrac12\beta_ka^\natural_z|\varrho_z-\mathcal Q_z\delta\psi-s_z|^2=\tfrac12\beta_k\frac{a_k^2}{a_z}|r_z|^2-\beta_ka_k\,r_z\cdot\mathcal Q_z\delta\psi+\tfrac12\beta_ka^\natural_z|\mathcal Q_z\delta\psi|^2+R_{\eta,z}+R_{s,z},$$
$$R_{\eta,z}:=\beta_k\eta_z\Big(\tfrac{a_k^2}{2a_z}r_z\cdot r_z-a_k\,r_z\cdot\mathcal Q_z\delta\psi\Big),\qquad R_{s,z}:=\beta_ka^\natural_z\Big(-(\varrho_z-\mathcal Q_z\delta\psi)\cdot s_z+\tfrac12s_z\cdot s_z\Big)$$
(bilinear products; for complex arguments the identity is the same polynomial identity). The term $-\beta_ka_kr_z\cdot\mathcal Q_z\delta\psi$ cancels $\beta_k$ times (2.54) exactly (P7 p. 510:
"the second term above is equal to (2.54) with the minus sign, so their sum is equal to 0"). *Minimal value* (P7 (2.56)–(2.57)). The block terms of
$\beta_kA^*_k(X_{\rm win},\mathbb B_k;\psi^0_{k_1,k},\phi^0_k)$ on $Z^c_0\cap\Omega^c_k$ plus $\sum_z\frac12\beta_k\frac{a_k^2}{a_z}|r_z|^2$ equal $\sum_z\frac12\beta_ka_k|r_z|^2$: per $z$, the block term of a leaf of layer $n$ is
$\frac12\beta^{(k)}_0a_nL^{n(d-2)}L^{nd}\cdot L^{-nd}|\frac{a_k}{a_n}L^{2(n-k)}r_z|^2$, and summing with (C1) as in the proof of Lemma III.2.3 gives $\frac12\beta_ka_k^2|r_z|^2(u_k-u^{(k)}_z)$, to which
$\frac12\beta_ka_k^2u^{(k)}_z|r_z|^2$ is added. The block terms on $X_{\rm win}\cap Z_0$ vanish by (2.52), those on $\Omega_k$ coincide with the single-scale ones. So the block terms
together form the single-scale block terms of $\beta_kA^*_k(Z;\psi^0_k,\phi^0_k)$ on $Z\setminus Z_{k_1}$ (on $Z_0$ they vanish, $r=0$), and the gradient, mass and boundary terms of
$A^*_k(X_{\rm win})$ are those of $A^*_k(Z)$ minus those of $Z_{k_1}$, which is $-A^*_{0,k}(Z_{k_1};\phi^0_k)$ (P7: "we can extend the form (2.57) to the whole set $Z_k\cap T^{(k)}_1$ writing $\psi^0_k$
instead of $\psi_k$"). *Constants.* $\log\mathrm{const}^\natural-\log\mathrm{const}=\frac N2\sum_z\log(1+\eta_z)$. Collecting, $C^\natural=\sum_z(R_{\eta,z}+R_{s,z})-\frac N2\sum_z\log(1+\eta_z)$.
*Bounds.* By Cauchy–Schwarz, $|\beta_k\eta_za_kr_z\cdot\mathcal Q_z\delta\psi|\le\frac18\beta_ka^\natural_z|\mathcal Q_z\delta\psi|^2+8\beta_k\eta_k^2a_k^2|r_z|^2/a^\natural_z$ and
$|\beta_ka^\natural_z\mathcal Q_z\delta\psi\cdot s_z|\le\frac14\beta_ka^\natural_z|\mathcal Q_z\delta\psi|^2+\beta_ka^\natural_z|s_z|^2$; these two $\frac18+\frac14=\frac38$ parts form $C^\natural_1$. The rest, $C^\natural_0$, is bounded by
$$\sum_z\Big[3\beta_k\eta_k|r_z|^2+4\beta_k|r_z||s_z|+3\beta_k|s_z|^2\Big]+N\eta_k\#\{z\}\qquad(a_k,a_z,a^\natural_z\in[\tfrac12,2],\ \eta_k\le\tfrac12).$$
On the real domain $|r_z|\le3K_1K_6\delta_k$ and $|s_z|\le2\bar\varsigma_z$, so with $\#\{z\}\le(M\mathrm{crit}_k)^d$: the first term is $\le27K_1^2K_6^2\eta_kA_0^2\lambda_k^{2p_0}a^{-1}(M\mathrm{crit}_k)^d$, the second
$\le24K_1K_6(\delta_k/\varepsilon_k)\Theta^\natural$, the third $\le12(\Sigma^\natural)^2(M\mathrm{crit}_k)^d$, the fourth $\le N\eta_k(M\mathrm{crit}_k)^d$; each is $\le\frac14$ by (Λ19) (they carry $\beta^{-1}q^k$,
$\delta_k/\varepsilon_k\le\alpha_0^{-1}A_0\lambda_k^{p_0}\beta^{-1/2}L^{-k\gamma}$, or $(\Sigma^\natural)^2$, times polynomials in $\hat\lambda_k$). On the complex domain $|r_z|\le6K_1K_6\varepsilon_k$ (Lemma III.6.2) and $|\tilde\psi|\le2$:
$\beta_k\eta_k\varepsilon_k^2\le e^{\epsilon}\beta L^{k(d-2)}\cdot9\alpha_0^2L^{-2k\alpha}\cdot\frac{12c_\xi L^{-2\gamma k}}{\beta(1-q)}=\frac{108e^{\epsilon}\alpha_0^2c_\xi}{1-q}$ (as $d-2-2\alpha-2\gamma=0$), so the first term is $\le C\hat\lambda_k^{2d}$, and the second is
$\le48K_1K_6\Theta^\natural\le C\hat\lambda_k^{2d+1}$ by (III.1.8). $\square$

*Remark.* The audit's point P2-05 is visible here: $R_{\eta,z}$ and $R_{s,z}$ contain terms linear in $\delta\psi$, and every coefficient error carries $\beta_k$. The linear terms
are absorbed into $\frac38$ of the non-negative composed-Gaussian term $\frac12\sum_z\beta_ka^\natural_z|\mathcal Q_z\delta\psi|^2$ (which then keeps $\frac18$), and the $\beta_k$ factors are
compensated by $\eta_k=O(\beta^{-1}q^k)$ (the coefficient error is weighted towards the top scales, Lemma III.1.6) and by the volume fractions of the deep layers
(Lemma III.1.7′). On the complex domain the remainder is not small but polynomial, $O(\hat\lambda_k^{2d+1})$, and is paid by $C_R$.

### III.6.3 The remaining terms (P7 (2.59)–(2.60))

**Lemma III.6.4 ((2.59)′, (2.60)′, surface and $\nu$-terms) [v1.3: P4-01].** On the domain of Lemma III.6.3, for $1\le k\le k_0$ and $\hat\lambda_0\ge\lambda_*$ ((Λ25)):
(a) $|\beta_kA^*_{0,k}(Z_{k_1};\phi^0_k)|<\frac14$, real and complex (P7 (2.59));
(b) $\frac12\beta_k|\langle\delta\phi_{k_1,k},\alpha^0_k\delta\phi_{k_1,k}\rangle_{X_{\rm win}}|<\frac14$, and on the complex domain the same with $\alpha^0_k+\nu_k$ (P7 (2.60), (3.19));
(c) $\beta_k|S_{\rm st}|<\frac14$ and $\beta_k\nu_k|\langle\delta\phi_{k_1,k},\phi^0_k-h\rangle_{X_{\rm win}}|<\frac14$.
Consequently, on the real domain, $\beta_k\{\cdots\}\ge\gamma_0\cdot(\text{the LF-1 bracket of }\delta\psi\text{ on }X_{\rm win})-1$ (P7 p. 512 [checked]), and $\beta_k\{\cdots\}+C^\natural_1\ge-1$.

*Proof.* (a) With (2.41) for the extension ($2\varepsilon_k$ in place of $\delta_k$) and $|Z_{k_1}|_k\le\nu_{\max}(k)(M\mathrm{crit}_{k_1})^dL^{-n_1d}$ (Lemma III.1.2 (c)):
$|\beta_kA^*_{0,k}(Z_{k_1};\phi^0_k)|\le(6K_1K_6)^2\beta_k\varepsilon_k^2\,\nu_{\max}(k)(M\mathrm{crit}_{k_1})^dL^{-n_1d}$. Since $\beta_k\varepsilon_k^2\le e^{2\epsilon}\beta_{k_1}\varepsilon_{k_1}^2L^{2\gamma n_1}$ and $d-2\gamma=2+2\alpha$, the right side is
$\le C\nu_{\max}(k)(M\mathrm{crit}_k)^d\beta_{k_1}\varepsilon_{k_1}^2L^{-2(1+\alpha)n_1}\le C'\hat\lambda_k^{p_2+2d}\alpha_0^2\beta_{k_1}^{-1-2/\alpha}$ by (III.1.1) ($L^{\alpha n_1}>\beta_{k_1}a$), which is $<\frac14$ by the strengthened (Λ25)(a) (ARCH (2.59)′). (b) As P7 p. 511 with (2.49′):
$\frac12\beta_k|\langle\delta\phi,\alpha^0\delta\phi\rangle|\le\frac12\sum_{j=k_1}^{k}\beta_j(C_{24}L^{\frac{d+2}2}\hat W_k\delta_j)^2\cdot3K_1K_6\delta_k\cdot|\Lambda_j\cap Z|_jL^{-2(k-j)}$, and $|\Lambda_j\cap Z|_j\le L^d\nu_{\max}(k)(LM\mathrm{crit}_k)^d$,
$\beta_j\delta_j^2=A_0^2\lambda_j^{2p_0}/a$, $\delta_k=A_0\lambda_k^{p_0}(\beta_ka)^{-1/2}$, $\sum_jL^{-2(k-j)}\le2$: the bound is $\le CA_0^3\nu_{\max}(k)\hat W_k^2(LM\mathrm{crit}_k)^d\lambda_k^{3p_0}\beta_k^{-1/2}<\frac14$ by (Λ25)(b) (ARCH (2.60)′; P7 used
$(10LMR_j)^d$ per layer). On the complex domain replace $3K_1K_6\delta_k$ by $6K_1K_6\varepsilon_k+L^{2j-2k}\beta_k^{-1}$ ($|(\alpha^0_k+\nu_k)|$ in scale-$j$ units) and sum as in (3.17) [P7 p. 524]: the factor
$\varepsilon_k\le\varepsilon_{k_1}L^{-\alpha n_1}\le\varepsilon_{k_1}(\beta_{k_1}a)^{-1}$ replaces $\delta_k$. (c) The surface term on ${\rm st}(Z_{k_1})$ as (a); on ${\rm st}(Z)$ the response at the chosen collar in (2.49′) gives $e^{-\gamma_w(M([\hat R_k]-1)-2M_1)}$ [v1.3: P4-09]
times a polynomial (P7 p. 511: "a large power of $\beta_k^{-1}$"), at most $\frac14$ by (Λ25)(c). The $\nu$-term: $k\le k_0$ gives $\beta_k\nu_k\le e^{2\epsilon}$ by (I.2), $|\phi^0_k-h|\le2$, and $\sum_j|\Lambda_j\cap Z|_kC_{24}L^{\frac{d+2}2}\hat W_k\delta_j\le C(M\mathrm{crit}_k)^d\hat W_k\delta_{k_1}$. The strengthened (Λ25)(c) makes $2e^{2\epsilon}C(M\mathrm{crit}_k)^d\hat W_k\delta_{k_1}\le\frac14$. All four losses sum to at most $1$.
The consequence: LF-1 (a) holds for every pair of fields, in particular for $(\delta\psi,\delta\phi_{k_1,k})$ in the first two terms of $\delta A^*_k$ (P5 (2.24)); the third term is (b);
the remaining terms of $\delta A^*_k$ and the composed-Gaussian term are $\ge0$; $|C^\natural_1|$ is at most $\frac34$ of the composed-Gaussian term. $\square$

---

## III.7 Lemma 2.5: the new small-field functions imply the old ones (P7 pp. 512–516; ARCH (M5))

**Lemma III.7.1 (P7 Lemma 2.5) [v1.3: P3-01].** Let $K_{\rm win,0}^{\rm red}$ be the window kernel with exactly the old characteristic functions named below deleted and every other factor retained, including $\chi_{k_1}(Z^c_{k_1}\cap U)$, the scale-$k$ functions, $\chi^{\rm new}$, the domain indicators, and the Gaussian factors. Put $N:=\tilde\chi_k\chi_S\chi^0\chi''$. At every real configuration where $N K_{\rm win,0}^{\rm red}$ is nonzero, every deleted old characteristic function equals $1$. In particular, every old $\mathcal X_{\rm win}$ function whose
localization cube lies outside $U$ equals $1$: $\chi_j(\square)=1$ for $\square\in\pi_j$, $\square\subset\Omega^{\sim-3}_j\cap(\Omega^{\sim3}_{j+1})^c\cap U^c$, and $\chi'_{j+1}(\square')=1$ for $\square'\in\pi_{j+1}$,
$\square'\subset\Omega^{\sim3}_{j+1}\cap(\Omega^c_{j+1})^{\sim3}$, $k_1\le j\le k-1$ [checked, text layer]; and the conditions (1.24) of $\chi^{\rm new}_j$ on these cubes hold. Consequently, pointwise on real configurations,
$K_{\rm win}N=K_{\rm win}^{\rm red}N$, where $K^{\rm red}_{\rm win}$ is $K_{\rm win}$ with these characteristic functions replaced by $1$; the only window characteristic
functions left are $\chi_{k_1}(Z^c_{k_1}\cap U)$ and those at scale $k$ (on $\Omega^{\sim-3}_k\cap Z$, which enter $\chi_k(Z\cap Z''^c_0)$, P7 p. 502).

*Proof* (P7's, with the changed constants; every estimate is listed). Fix a configuration with $N K^{\rm red}_{\rm win,0}\ne0$. This gives all the retained factors listed in the statement, but assumes nothing about a deleted old function. The following two cases derive each deleted condition only from those retained factors. The equations for $\chi_j$ use $\chi''$, $\chi^0$, $\tilde\chi_k$, the retained new and scale-$k$ restrictions, BG Proposition 5.1 and the stated size bounds. The equations for $\chi'_{j+1}$ use the corresponding retained new restriction and the same response bound. No estimate below uses a deleted factor. Two cases.

*Case A: $\square^{\sim3}\cap U^{\sim3}=\varnothing$.* Then $\square^{\sim3}\subset\Lambda_j\cap\Omega^c_{j+1}$ and $\delta\psi=\psi''$ on $\square^{\sim3}$ (Definition III.5.1 item 4), so $|\psi''_j|<\delta_{j,1}$ there. Write
$\phi_j(\square;\tilde\psi_j)=\phi_j(\square;\tilde\psi^0_{k_1,k})+\delta\phi_j(\square;\tilde\psi''_j)$ (P7 (2.63), $\phi_j(\square):=\mathrm{bg}(\mathbb B_j(\square^{\sim2});\cdot)$).
- (2.64) By BG Proposition 5.1 (landed `prop51_exists_unique`, constant $K_2$): $|\delta\phi_j|,L^j|\partial\delta\phi_j|,L^{2j}|\Delta\delta\phi_j|,L^{2j}|\delta\alpha_j|<K_2\delta_{j,1}=\frac{K_2A_1}{A_0}\delta_j\le\frac18\delta_j$, using the
  relation $A_0=4K_2B_5A_1$ (P7 p. 513 [checked]; row 9).
- (2.65)–(2.67) The background $\phi_j(\square)$ is determined by the coefficients of scale $j$, $\psi^0_{k_1,k}$ by those of scale $k$; renormalizing in $k-j$ steps by P4 (4.12) with
  the bounds P4 (4.11), (5.31) gives $\phi_{j,u}(\square;\tilde\psi^0_{k_1,k})=\phi_j(\square;\tilde\psi^0_{k_1,k})+\delta\phi_{j,u}$ with $|\delta\phi_{j,u}|,\dots<56B_6K_1^2K_2K_5K_6\alpha_0^{-1/2}\gamma^{-1}\beta^{-1}L^{-2\gamma j}L^{j-k}\delta_k<\frac18\delta_j$
  for $\beta$ large ((Λ25)); the input is $\tilde\psi^0_{k_1,k}\in\tilde\Psi(\mathbb B_j(\square^{\sim2});4K_1K_6L^{j-k}\delta_k)$ (2.66), from (2.45). *Status:* cited (P7 p. 513; the free flow does not change
  P4 (4.11)–(4.12), SF §3). Under the free flow the factors $z_i$ enter here as in P4 (4.12) (field renormalization of the coefficients), not as in §III.1.
- (2.68)–(2.70) $\phi_j(\mathbb B_j(\square^{\sim2});\psi(\mathbb B_j(\square^{\sim2}),\mathbb B_k(U_k);\tilde\psi^0_k))=\phi^0_k$ on $\square^{\sim3}$ (I-2, `theorem73_real`; $\mathbb B_j(\square^{\sim2})\prec\mathbb B_k(U_k)$ by Lemma II.2.3 (b)).
  The data difference $\tilde\psi^0_{k_1,k}-\psi(\mathbb B_j(\square^{\sim2}),\mathbb B_k(U_k);\tilde\psi^0_k)$ vanishes on $\square^{\sim2}$ and is $<3(d+1)K_1K_6L^{j-k}\delta_k$ elsewhere (P7 (2.69), from (2.41) and
  BG (6.2)); by the exponential decay of the background's response (P3 Proposition 2.1; in the project LOC/G-2) the induced change is
  $<3(d+1)K_1K_3K_6e^{-\frac15\gamma_0M}L^{j-k}\delta_k\le\frac18L^{j-k}\delta_k$, which is P7 (2.70), the row-6 condition (vi) on $M$ ("one of the strongest conditions on $M$").
- (2.71) Hence $|L^j\partial\phi_j|,|L^{2j}\Delta\phi_j|,|L^{2j}\alpha_j|<\max\{|L^j\partial\phi^0_k|,|L^{2j}\Delta\phi^0_k|,L^{2j}|\alpha^0_k|\}+\frac38\delta_j$ on $\square^\sim$. If $\square^\sim\cap Z''_0\ne\varnothing$: then
  $\square^\sim\subset\Omega^c_{k_3+1}$ (Lemma III.5.0 (b)), so $j\le k_3$, $k-j\ge n_3\ge4$, and by (2.41) the maximum is $<3K_1K_6L^{j-k}\delta_k\le3K_1K_6L^{-\frac43(k-j)}\delta_j\le3K_1K_6L^{-n_3}\delta_j<\frac{27K_1K_6}{[R_{k_3}]}\delta_j\le\frac58\delta_j$
  (Lemma III.5.0 (c) and $R_{\rm base}\ge44K_1K_6$, row 7; P7 has $R_0\ge6K_1K_6$ with its threshold $1$ for $k_3$). If $\square^\sim\subset Z''^c_0$: by (2.42) the maximum is $<\frac98L^{j-k}\delta_k\le\frac38\delta_k<\frac38\delta_j$.
  In both cases the three conditions on $\phi_j(\square)$ in $\chi_j(\square)$ hold with $\delta_j$.
- (2.72) $|\psi_j-Q_j\phi_j(\square;\tilde\psi_j)|<\frac{A_1}{A_0}\delta_j+|\psi^0_{k_1,k}-Q_j\phi^0_k|+\frac38\delta_j<(L^{j-k})^2|\psi^0_k-Q_k\phi^0_k|+\frac12\delta_j$ ((2.52)-type identity of BG (6.2)), and the first term is
  $<\frac12\delta_j$ in both cases as above. So the fourth condition of $\chi_j(\square)$ holds. The domain conjunct $\mathbf 1[\cdot\in\mathcal D_{\mathbb R}]$ holds by (Λ17).

*Case B: $\square^{\sim3}\cap U^{\sim3}\ne\varnothing$.* Then $j=k_1$ and $\square\subset U^c\cap U^{\sim6}$ (the window cubes of layer $k_1$ near the core). Write
$\phi_{k_1}(\square;\tilde\psi_{k_1})=\phi_{k_1}(\square;\tilde\psi'_{k_1})+\delta\phi_{k_1}(\square;\tilde\psi_{k_1}-\tilde\psi'_{k_1})$ (P7 (2.73)); the first configuration satisfies all conditions of $\chi_{k_1}(\square)$ with $\frac12\delta_{k_1}$ by $\chi^0$.
The difference vanishes on $\mathbb B_{k_1}(\square^{\sim2})\cap U^{\sim3}$; on the rest it is $\tilde\psi_{k_1}-\psi_0$, and for $x$ there, with $z$ the $k$-block of $x$ and $z_0$ the clamped point of
§III.5.3 (c) (now $|z-z_0|\le D_0$),
$\tilde\psi_{k_1}(x)-\psi_0=\tilde\psi''(x)+(\tilde\psi^0_{k_1,k}(x)-\psi^0_k(z))+(\psi^0_k(z)-\psi_k(z_0))+(\psi_k(z_0)-\psi_0)$, so
$$|\tilde\psi_{k_1}-\tilde\psi'_{k_1}|<\delta_{k_1,1}+4K_1K_6\delta_k+3dD_0K_6\delta_k+C_{2.20}\delta_k<\Big(\frac{A_1}{A_0}+(4K_1K_6+3dD_0K_6+C_{2.20})e^{\epsilon}L^{-n_1/3}\Big)\delta_{k_1}$$
(ARCH (M7): P7's $7K_6\cdot3$ and $90d$ become $3dD_0K_6$ and $C_{2.20}$). By BG Prop 5.1 the second configuration then changes the conditions by at most
$K_2\times$ this, and $(K_2+1)\big(\frac{A_1}{A_0}+(4K_1K_6+3dD_0K_6+C_{2.20})e^{\epsilon}L^{-n_1/3}\big)\le\frac12$ by the relation of row 9 and (Λ23). So $\chi_{k_1}(\square)=1$.

*The functions $\chi'_{j+1}(\square')$ [v1.3: P3-01].* Their four small-field tests use the same decomposition of the local background as in Case A or Case B, with the scale replaced by $j+1$. The only larger input in the Case A comparison is the data bound $3(d+2)K_1K_6L^{j+1-k}\delta_k$ in place of $4K_1K_6L^{j-k}\delta_k$ (P7 p. 515); the response term (2.65)–(2.67) therefore acquires at most $C_{\chi'}=\max\{1,3(d+2)/4\}$, paid by the strengthened (Λ25)(d). The BG Proposition 5.1 perturbation and the distant-data response then each use at most $\frac18\delta_{j+1}$, while the free background uses at most $\frac58\delta_{j+1}$ as in (2.71); their sum is below the unit threshold for the three background tests.
The field test follows from (2.72) at scale $j+1$, except at $j+1=k$, where it is checked directly (P7 p. 516): on $\square'^\sim\cap\Omega^c_k$, $\frac{A_1}{A_0}\delta_{k-1}+\frac18\delta_k+\frac38\delta_{k-1}<\frac34\delta_{k-1}$; on $\square'^\sim\cap\Omega_k$, $|\psi_k-Q_k\phi^0_k|+\frac38\delta_{k-1}<\frac98\delta_k+\frac38\delta_{k-1}<\frac45\delta_{k-1}$ (P7's $\frac98L^{-1/3}+\frac38<\frac45$). The near-core Case B uses its retained $\chi^0$ restriction and the same $\frac12$ response margin as above. Thus these tests also use only factors retained in $N K^{\rm red}_{\rm win,0}$.
*Conditions (1.24).* They follow from the retained new restrictions by P1 Lemma 3.1 (SF §1.2 (D1)) as in Remark II.2.8. Thus every deleted factor is $1$ whenever $N K^{\rm red}_{\rm win,0}\ne0$. If this product is zero, both $K_{\rm win}N$ and $K^{\rm red}_{\rm win}N$ are zero because their other factors coincide; if it is nonzero, multiplication by the deleted factors changes nothing. This proves the pointwise kernel identity. $\square$

*Status:* proved here from the cited inputs listed (BG Prop 5.1 and I-2 landed; P4 (4.11)–(4.12) and P3 Prop 2.1 cited). This is also the proof of P5 Lemma
2.1 (the known gap of LF-3, ARCH §3.7; P7 p. 512: "The analysis in this case covers in particular a proof of Lemma 2.1 [5]"). The two constant changes
relative to P7 are $R_{\rm base}\ge44K_1K_6$ (row 7) and the threshold $8$ in $k_3$ (Lemma III.5.0). Lemma 2.5 uses no chains (R3-14 (a)).

---

## III.8 The normalization of $R$, the outcome operators, the refund, and LF-4R (P7 pp. 517–520, 525; ARCH Step 6)

### III.8.1 The definition of $R$ on a representation

**Definition III.8.1 (the reference density of a component; P7 (1.5), (3.1)–(3.2)).** For a ripe component $Z$ with outcome "to $R$", put $C_6:=3dD_0(K_6+1)$ and
$$\chi_{Z_0}:=\mathbf 1\big[\,|\psi_k(z)-\psi^0_k(z)|<C_6\,\beta_k^{-1/2}p_0(\beta_k)\ \ \forall z\in Z_0\,\big],\qquad\rho_{k,0}(Z):=\chi_{Z_0}\exp\big(-\beta_kA^*_k\big(Z;\psi_k,\phi_k(\mathbb B_k(U_k);\tilde\psi_k)\big)\big),$$
$U_k=Z^\approx$, the action with its $\nu$-term (P5 p. 490). (P7: $C_6=21(K_6+1)$ for $\mathrm{diam}(Z_0)<15$; the same argument with $|z-z_0|\le D_0$ gives ours, (3.21).)

**Lemma III.8.2 (the denominator; P7 (3.3)–(3.5), cited).** $\int d\psi_k\!\restriction_{Z_0}\rho_{k,0}(Z)=\exp\big(-\beta_kA^*_k(Z;\psi^0_k,\phi^0_k)-\frac N2\log\beta_k|Z_0|+\tilde{\mathcal E}^{(k)}_0(Z_0;\psi^0_k)\big)$,
where $\tilde{\mathcal E}^{(k)}_0$ is analytic in $\psi_k\restriction_{U^\sim_k\cap Z^c_0}$ on the large domain of Lemma III.3.3, $O(N)$-invariant jointly in $(\psi_k,h)$, and $|\tilde{\mathcal E}^{(k)}_0|\le C_{\tilde E}D_0^d$ with
$C_{\tilde E}=C(N,d,D_0,\gamma_0,C_6)$. *Source.* P7 pp. 517–518 [checked, text layer]: the expansion (3.3) around $\psi^0_k$ (the linear term vanishes by (2.52) and $\psi=0$ off $Z_0$),
the quadratic form bounded below by (2.38) with $c_{D_0}$ (Lemma III.3.3), the cubic remainder $O(\beta_k^{-1/2}p_0^3)|Z_0|$, the $\nu$-term $O(e^{2\epsilon}\beta_k^{-3/2}p_0^2)|Z_0|$ by $k\le k_0$ and (I.2) [v1.3: P4-01], the surface term a
high power of $\beta_k^{-1}$; "$|Z_0|\le14^d$, so the integral is very simple and elementary" (ours $|Z_0|\le D_0^d$). The lower bound on the integral (needed for $|\tilde{\mathcal E}_0|$) is the
integral over $|\psi|<1$, where the integrand is $\ge e^{-C|Z_0|}$. *Status:* cited; a finite-dimensional Gaussian estimate.

**Definition III.8.3 ($R^{(k)}$ on a representation; P7 (1.3)–(1.6)).** For $\mathbb A\in\mathfrak A$ let $\mathrm{Rip}(\mathbb A)$ be the set of ripe components of $Z^{\rm pre}_k(\mathbb A)$. Inserting the
decompositions of Definition III.5.2 in every ripe component gives $\rho=\sum_{\mathbb A}\sum_\sigma\rho(\mathbb A,\sigma)$, the inner sum over the maps $\sigma:\mathrm{Rip}(\mathbb A)\to\{\varkappa_1,\dots,\varkappa_4,\to\!R\}$,
$\rho(\mathbb A,\sigma)$ the term of (D1) with the kernel $K^{(\sigma(Z))}$ in each ripe component (Lemma II.5.3: the decompositions act on disjoint variables). Let
$\mathcal Z_\sigma:=\sigma^{-1}(\to\!R)$ and $\mathcal Z_{\sigma,0}:=\bigcup_{Z\in\mathcal Z_\sigma}Z_0$. Define (P7 (1.6))
$$R\big[\rho(\mathbb A,\sigma)\big]:=\prod_{Z\in\mathcal Z_\sigma}\rho_{k,0}(Z)\cdot\frac{\int d\psi_k\!\restriction_{\mathcal Z_{\sigma,0}}\rho(\mathbb A,\sigma)}{\prod_{Z\in\mathcal Z_\sigma}\int d\psi_k\!\restriction_{Z_0}\rho_{k,0}(Z)},\qquad\rho':=\sum_{\mathbb A\in\mathfrak A}\sum_\sigma R\big[\rho(\mathbb A,\sigma)\big].$$

**Lemma III.8.4 (normalization; P7 (1.7)–(1.8)).** On every admissible torus and for all $(h,g)$, $\|g\|_{\ell^1}<1$: $\int\rho'\,d\psi_k=\int\rho\,d\psi_k$.

*Proof.* Fix $(\mathbb A,\sigma)$. (i) The integrand of $\rho(\mathbb A,\sigma)$ depends on $\psi_k\restriction_{\mathcal Z_{\sigma,0}}$ only through the part over $Z_0$ of the composed Gaussian (III.1.4) of each
$Z\in\mathcal Z_\sigma$: by Lemma III.1.5 the window kernel reads $\psi_k\restriction_{\Omega^c_k}$ only in the Gaussians; the functions of Definition III.5.1 read $\psi_k$ only on $Z^c_0$ (items 1–2, $\psi_0$,
$\psi^0_k$, $\psi^0_{k_1,k}$); the boundary terms read the multiscale field, i.e. $\psi_k$ only on $\Omega_k$, and $Z_0\subset\Omega^c_k$ (Lemma III.3.2 (d)); the small-field functions read $\psi_k$ on
$(Z^{\rm pre c}_k)^{\approx2}$, disjoint from $\Omega^c_k$ (Lemma I.3.5 (g)). So the numerator does not depend on $\psi_k\restriction_{\mathcal Z_{\sigma,0}}$, and by (2.8) (each composed Gaussian is a
probability density, Lemma III.1.6) it is the same expression with those Gaussians removed. (ii) The denominator is positive (Lemma III.8.2) and does not
depend on $\psi_k\restriction_{\mathcal Z_{\sigma,0}}$. (iii) Hence, by Fubini (absolute integrability: (1.26) and Lemma II.6.3 (b) for the numerator; the small-field factor is bounded on the
support of $\chi_k$),
$\int d\psi_k\,R[\rho(\mathbb A,\sigma)]=\int d\psi_k\!\restriction_{\mathcal Z^c_{\sigma,0}}\frac{\int d\psi_k\restriction_{\mathcal Z_{\sigma,0}}\rho(\mathbb A,\sigma)}{\prod\int\rho_{k,0}}\cdot\prod_Z\int d\psi_k\!\restriction_{Z_0}\rho_{k,0}(Z)=\int d\psi_k\,\rho(\mathbb A,\sigma)$.
Sum over the finitely many $(\mathbb A,\sigma)$. For complex $g$ the identity holds term by term (the same Fubini argument with $|\cdot|$). $\square$

### III.8.2 The outcome operators and the refund

**Definition III.8.5 (the operator (3.7); P7 (2.74)–(2.75), (3.6)–(3.7)).** For $Z\in\mathcal Z_\sigma$ with localized history $\mathfrak a$, carry out in $\rho(\mathbb A,\sigma)$: the composition of
Lemma III.1.6 (integrating $\mathcal J$), the integral over $\psi_k\restriction_{Z_0}$ by (2.8), Lemma III.7.1 (removing the window characteristic functions outside $U$), the change of
integration variables $\psi''=\tilde\psi-\psi^0_{k_1,k}(\psi_k)$ on $D''$ (a translation for fixed $\psi_k$), the identity (2.58′), and the division by Lemma III.8.2. The result is
$R[\rho(\mathbb A,\sigma)]=\prod_{Z\in\mathcal Z_\sigma}\rho_{k,0}(Z)\,\mathbb T^{(3.7)}(Z,\mathfrak a)\otimes(\text{the other factors of }\rho(\mathbb A,\sigma))$, where $\mathbb T^{(3.7)}(Z,\mathfrak a)$ has the kernel
$$\begin{aligned}K^{(3.7)}:=&\ \chi_k(Z\cap Z''^c_0)\,\tilde\chi_k(Z''_0\cap Z^c_0)\,\chi_{Z_0}\cdot e^{\frac N2\log\beta_k|Z_0|-\tilde{\mathcal E}^{(k)}_0+\beta_kA^*_{0,k}(Z_{k_1};\phi^0_k)}\cdot\mathrm{const}\cdot\chi''\,\chi^0\,\chi_{k_1}(Z^c_{k_1}\cap U)\,K^{\rm red}_{\rm win,0}\\
&\cdot e^{-\beta_k\{\cdots\}-\beta_kS_{\rm st}-C^\natural+C_{k_1,k}}\cdot\prod_{C\in\mathcal C_*}K_{k_1}(C)\end{aligned}\tag{3.7′}$$
and the exponent $b^{(3.7)}:=b_{\rm win}+\sum_Cb_C$; $K^{\rm red}_{\rm win,0}$ is the product of the remaining factors of $K^{\rm red}_{\rm win}$ other than Gaussians and main actions (the indicators
$\mathbf 1[\cdot\in\mathcal D_{\mathbb R}]$ and $\chi^{\rm new}$ on the cubes in $U$), "const" the ideal normalization of the composed Gaussian on $Z^c_0\cap\Omega^c_k$. Its internal variables are
$I^{(3.7)}:=\{\psi''\text{ on }D''\}\cup\{\psi_{k_1}\text{ on }T^{(k_1)}\cap U^{\sim3}\}\cup\bigcup_CI(C)$; its output variables are $\psi_k$ on $T^{(k)}\cap V_Z$ (it depends on $\psi_k\restriction_{Z_0}$ only through
$\chi_{Z_0}$, and on $\psi_k\restriction_{Z^c_0}$ through $\psi^0_k$, $\phi^0_k$, $\psi_0$ and the front functions). The boundary terms and $b_{\rm win}$ are evaluated at $\tilde\psi=\psi^0_{k_1,k}+\psi''$ on $D''$ (P7 p. 519:
"the function $C_{k_1,k}$ and the boundary terms depend now on $((\psi,\psi')\restriction_{U^{\sim3}},(\psi^0_{k_1,k}+\psi'')\restriction_{(U^{\sim3})^c})$"). The decomposition (3.20) then splits
$\rho_{k,0}(Z)\mathbb T^{(3.7)}(Z)=\rho_{k,0}(Z)\mathbb T^{(3.7)}(Z)\chi_{Z''}+\rho_{k,0}(Z)\mathbb T^{(3.7)}(Z)(1-\chi_{Z''})$ (Definition III.5.1 item 5): the **removed outcome** and the **kept outcome $\varkappa_5$ (K2)**.

**Definition III.8.6 (residual loss).** $L_{\rm res}(k):=C_R\hat\lambda_k^{2d+1}$, where $C_R$ is the least constant such that, for all $\hat\lambda_k\ge\lambda_*$,
$$\Big[\tfrac N2\log2+Np_0\log\lambda_k+C_{\rm vol}\Big](M\mathrm{crit}_k)^d+D_0^d\big(Np_0\log\lambda_k+C_{\rm vol}+C_{\tilde E}\big)+(C'_E\lambda_k+C'_E)(M\mathrm{crit}_k)^d+C_\natural\hat\lambda_k^{2d+1}+10\ \le\ C_R\hat\lambda_k^{2d+1},\tag{III.8.4}$$
with $C_{\rm vol}:=\log\big(v_N\max\{3,C_6\}^NA_0^N\big)$ [v1.3: P3-04] and $|E_k|\le C'_E\lambda_k+C'_E$ (P7 p. 520 [checked]: "$|E_k|<O(1)\log\beta_k+\mathrm{const}$"). It depends on rows 0–11 only. Indeed the $Z_0$ ball times its $\beta_k^{N/2}$ prefactor has volume exactly $v_NC_6^NA_0^N\lambda_k^{Np_0}$; the factor $a^{-N/2}$ belongs only to the separate Gaussian-normalized shell estimate. Increasing $C_{\rm vol}$ by $(N/2)\log a$ increases the left side of (III.8.4) by a fixed multiple of $(M\mathrm{crit}_k)^d+D_0^d$, still $O(\hat\lambda_k^{2d})$, so the existing $C_R\hat\lambda_k^{2d+1}$ choice absorbs it.

**Lemma III.8.7 (the window integral; P7 (3.8)–(3.10), ARCH (M3)).** Put $C_W:=C_b$ and $C'_W:=C_bB_0+C_{15}$. For each outcome $o\in\{\varkappa_1,\dots,\varkappa_5,{\rm rem}\}$ let $K^{(o)}$ be its
kernel ($K^{(\varkappa_i)}$ of Definition III.5.2 for $i\le4$; $\rho_{k,0}(Z)K^{(3.7)}(1-\chi_{Z''})$ for $\varkappa_5$; $K^{(3.7)}\chi_{Z''}e^{E_k|Z|}$ for the removed outcome, without $\rho_{k,0}$, as in P7 (3.10)) and
$b^{(o)}$ its exponent. Then for all values of the parameters,
$$\int d\psi_k\!\restriction_{T^{(k)}\cap Z}\int d(\text{internal})\ K^{(o)}e^{{\rm Re}\,b^{(o)}}\ \le\ \exp\Big(-\sum_{C\in\mathcal C_*}\kappa_{k_1}(C)+\sum_{j=k_1}^{k-1}(C_W\log\beta_j+C'_W)|X_j|_{j+1}+L_{\rm res}(k)-\gamma(o)\Big),\tag{III.8.5}$$
with $\gamma(\varkappa_i):=\gamma_i$ of Lemma III.5.3 and $\gamma({\rm rem}):=0$.

*Proof.* The integrand is non-negative; integrate in this order (the order of the rewritten Lemma II.5.13). *(1) Gaussian-only variables and $\psi_k\restriction_{Z_0}$.* For
$\varkappa_1,\dots,\varkappa_4$: integrate $\mathcal J$ by Lemma III.1.6 and $\psi_k\restriction_{Z_0}$ by (2.8); what remains is the composed Gaussian on $Z^c_0\cap\Omega^c_k$, $\mathrm{const}^\natural e^{-\mathcal G^\natural}$. For
$\varkappa_5$ and the removed outcome this was done in Definition III.8.5. *(2) The exponentials.* Bound pointwise, uniformly in the core variables:
$e^{{\rm Re}\,b_{\rm win}}\le e^{\sum_j(C_b\log\beta_j+C_bB_0)|X_j|_{j+1}}$ ((S0)); $|e^{C_{k_1,k}}|\le e^{C_{15}\sum_j|X_j|_{j+1}}$ (2.15′); and
- $\varkappa_1$: $\mathrm{const}^\natural e^{-\mathcal G^\natural-\mathcal A_{\rm win}}\le\mathrm{const}^\natural e^{-\frac12\mathcal G^\natural}\cdot e^{C_{k_1,k}-\gamma_1}$ by Lemma III.5.3 (a);
- $\varkappa_2$: $e^{-\mathcal G^\natural-\mathcal A_{\rm win}}\le e^{C_{k_1,k}-\gamma_2}$ by Lemma III.5.3 (b); $\varkappa_3$: $e^{-\mathcal G^\natural-\mathcal A_{\rm win}}\le e^{-\mathcal A_{\rm win}}\le e^{C_{k_1,k}-\gamma_3}$ by (c);
- $\varkappa_4$, $\varkappa_5$, removed: by (2.58′) and Lemma III.6.4, $e^{-\mathcal G^\natural-\mathcal A_{\rm win}}\cdot\frac{\mathrm{const}^\natural}{\mathrm{const}}\le e^{-\beta_kA^*_k(Z;\psi^0_k,\phi^0_k)+1+3+|C^\natural_0|+C_{k_1,k}}\cdot e^{-(\beta_k\{\cdots\}+C^\natural_1)}$, and
  $e^{-(\beta_k\{\cdots\}+C^\natural_1)}\le e^{1}$, resp. $\le e^{1-\gamma_4}$ on $\chi''=0$ (Lemma III.5.3 (d), with $\frac58$ of the composed-Gaussian term left); for $\varkappa_5$ and the removed outcome the factor
  $e^{-\beta_kA^*_k(Z;\psi^0_k,\phi^0_k)}$ has been divided by Lemma III.8.2, which leaves $e^{\frac N2\log\beta_k|Z_0|-\tilde{\mathcal E}_0}$, and for $\varkappa_5$ the factor $\rho_{k,0}(Z)$ is $\le e^{-\gamma_5}$ on $1-\chi_{Z''}$ (Lemma III.5.3 (e)).
*(3) Volumes.* Integrate $\psi_k\restriction_{Z\setminus Z_0}$ and the window variables, for fixed core variables: every window variable (multiscale field of layers $k_1\le j<k$,
or $\psi''$, or $\psi_{k_1}$ on $U^{\sim3}\setminus Z_{k_1}$) lies in a shell $\{|u\cdot u-1|<3dL\delta_j\}$ ((1.24) in $\chi^{\rm new}$) or in the ball $|\psi''|<\delta_{j,1}$ ($\chi''$), of volume $\le1$ ((Λ17′)).
$\psi_k$ on $\Omega_k\cap Z$: shells, volume $\le1$. $\psi_k$ on $Z^c_0\cap\Omega^c_k$: for $\varkappa_1$, $\int\mathrm{const}^\natural e^{-\frac12\mathcal G^\natural}d\psi_k\restriction_z=2^{N/2}$ per block; otherwise, along a spanning tree of the
$k$-blocks of $Z^c_0\cap Z$ rooted in $\Omega_k\cap Z$, each $\psi_k(z)$ lies in a ball of radius $3\delta_k$ around its parent ($\tilde\chi_k$), and with the constant $\mathrm{const}$ of the
composed Gaussian ($\beta_ka_z\le2\beta_k$) the factor per block is $\le v_N(3\delta_k)^N(\beta_k/\pi)^{N/2}\le e^{Np_0\log\lambda_k+C_{\rm vol}}$. $\psi_k$ on $Z_0$ for $\varkappa_5$ and removed: $\chi_{Z_0}$ gives a ball of
radius $C_6\beta_k^{-1/2}p_0$, and with $e^{\frac N2\log\beta_k|Z_0|}$ the factor is $\le e^{(Np_0\log\lambda_k+C_{\rm vol})|Z_0|}$. The number of $k$-blocks of $Z$ is $|Z|_k\le(M\mathrm{crit}_k)^d$ (a box of side $\le\mathrm{crit}_k$ $\pi_k$-cubes,
Lemma III.1.2 (d)). The removed outcome also carries $|e^{E_k|Z|}|\le e^{(C'_E\lambda_k+C'_E)|Z|_k}$. *(4) The core.* For fixed window variables, $\prod_C\int K_{k_1}(C)e^{{\rm Re}\,b_C}\le e^{-\sum_C\kappa_{k_1}(C)}$ by (D5) at scale $k_1$ ((1.26) with $F\equiv1$, one core box at a
time; the window factors were bounded uniformly in the core variables in (2) and (3)). Collecting: the window-proportional terms give $\sum_j(C_W\log\beta_j+C'_W)|X_j|_{j+1}$,
the others are $\le L_{\rm res}(k)$ by (III.8.4), and the small factor is $e^{-\gamma(o)}$. $\square$

*Remark (the refund).* P7 p. 520 bounds the whole expression (3.9) by $\mathrm{const}(\log\beta_k)^{2d+2}$ and uses $-p_2(\beta_k)$ to cancel it; with $\nu$ pieces the window sum is of order
$\nu_{\max}\hat\lambda^{2d+2}$ and that route is not available (ARCH Step 6). Here the window-proportional part is charged against the quiet-step charges of $\kappa^{\rm pre}$, which
are larger than the actual costs by the slack $(c_1-C_W)\log\beta_j+(c_2-C'_W)$ per unit of new volume: P7's own alternative ("we can take the constants in the sum (3.8)
large enough, so that the sum in (3.9) is cancelled", p. 520).

### III.8.3 The kept data and LF-4R

**Definition III.8.8 (kept data of $R$).** For a ripe $Z$ with localized history $\mathfrak a$ and label $\varkappa\in\mathfrak K$:
- $\varkappa_1,\dots,\varkappa_4$ (K1): $K'':=K^{(\varkappa)}$ (Definition III.5.2), $b'':=b^{\rm pre}$, $I'':=I(Z,\mathfrak a)$;
- $\varkappa_5$ (K2): $K'':=\chi^{\rm dom}_k(Z,\mathfrak a)\cdot\rho_{k,0}(Z)\,K^{(3.7)}(1-\chi_{Z''})$ written in the original multiscale variables (undo the translation $\psi''=\tilde\psi-\psi^0_{k_1,k}$), $b'':=b^{(3.7)}$,
  $I'':=I(Z,\mathfrak a)\setminus\mathcal J$ (all multiscale and core variables; D-III.9). The factor $\chi^{\rm dom}_k$ equals $1$ on the support of the rest by Lemma III.7.1 (P7 p. 519: "these
  configurations belong to the original integration domain by Lemma 2.5, hence to (1.24)"), so it changes nothing and gives the support clause of (S3) by definition;
- $\gamma(\varkappa_i):=\gamma_i$ (Lemma III.5.3), $C_{\rm dec}(\varkappa_i):=5$.

**Theorem III.8.9 (LF-4R; ARCH (Rg), Part I (Rg), Part II (S3)).** Under (A-III.1)–(A-III.3) and $c_1\ge C_W$, $c_2\ge C'_W$ (row 14), for every ripe component $Z$ of $Z^{\rm pre}_k(\mathbb A)$,
$\mathbb A\in\mathfrak A$, with localized history $\mathfrak a$:
(a) for every $\varkappa\in\mathfrak K$ the kept data of Definition III.8.8 satisfy (S3) of Definition II.5.7 (version 1.1): $K''\ge0$ Borel, independent of $g$, vanishing unless $\chi^{\rm dom}_k=1$;
$b''$ real for real arguments, analytic in $g$ on the polydisc, local, jointly covariant, bounded on the H7 domain; (S5); and (1.26) with
$$\kappa''_k(Z,\mathfrak a,\varkappa)=\kappa^{\rm pre}_k(Z,\mathfrak a)-C_R\hat\lambda_k^{2d+1}+\gamma(\varkappa),\qquad\gamma(\varkappa)-\log C_{\rm dec}(\varkappa)\ \ge\ 2A'_3\hat\lambda_k^{p_R};$$
(b) consequently (**(Rg)**): $G''_k(Z,\mathfrak a,\varkappa)=G^{\rm pre}_k(Z,\mathfrak a)-C_R\hat\lambda_k^{2d+1}+\gamma(\varkappa)-\log C_{\rm dec}(\varkappa)\ \ge\ G^{\rm pre}_k(Z,\mathfrak a)-C_R\hat\lambda_k^{2d+1}+A'_3\hat\lambda_k^{p_R}$;
(c) (P7 (3.10)) for the removed outcome, with $T^{\rm rem}(Z,\mathfrak a)$ its operator and every Borel $F$,
$$\sum_{\mathfrak a}\int d\psi_k\!\restriction_{T^{(k)}\cap Z}\big|T^{\rm rem}(Z,\mathfrak a)e^{E_k|Z|_k}F\big|\ \le\ e^{-A_2\hat\lambda_k^{p_2}-H_k|Z|_k}\,\sup|F|,\tag{3.10′}$$
the sum over the localized histories of $Z$ in $\mathfrak A$ for which $Z$ is ripe and goes to $R$.

*Proof.* (a) *Structure.* K1: $K^{\rm pre}$ times indicators of Definition III.5.1, which are Borel, $g$- and $h$-free and $O(N)$-invariant (§III.5.2); the support and (S5) are
inherited from $K^{\rm pre}$. K2: indicators (invariant: $\psi^0_k,\psi_0$ are equivariant) times the exponential of the real analytic, jointly covariant functions of (3.7′) (the
$h$-dependence through $\nu_k$-terms only), $g$ only in $b^{(3.7)}$. Locality: all objects live in $V_Z$ (Lemma II.5.9 (a), Lemma III.1.2 (f)). *Bound.* In the quiet window
$\kappa^{\rm pre}_k(Z,\mathfrak a)=\sum_C\kappa_{k_1}(C)-\sum_{j=k_1}^{k-1}(c_1\log\beta_j+c_2)|X_j|_{j+1}$ exactly (Definition II.5.11; no gains, $\mathcal N_{j+1}\cap Z=\varnothing$). By Lemma III.8.7 with $c_1\ge C_W$,
$c_2\ge C'_W$ ($\log\beta_j\ge0$), the left side of (1.26) for $F\equiv1$ is $\le e^{-\kappa^{\rm pre}_k+L_{\rm res}-\gamma(\varkappa)}=e^{-\kappa''_k}$; for general $F$ by the support property (Definition II.5.2).
The inequality for $\gamma-\log C_{\rm dec}$ is (III.5.1). (b) $\log C''=\log C^{\rm pre}+\log5$ (Definition II.5.11) and $G=\kappa-\log C-H_k|Z|_k$. (c) By Lemma III.8.7 with $\gamma({\rm rem})=0$ and
Lemma II.6.3 (b): the sum is $\le\sup_{\mathfrak a}e^{-G^{\rm pre}_k(Z,\mathfrak a)-H_k|Z|_k+L_{\rm res}}\sup|F|$ (the combinatoric factors are summed by Lemma II.5.15). For a ripe $Z$, (H6′)$^{\rm pre}$
gives $G^{\rm pre}_k\ge\tau_k+\nu+U\ge2A_2\hat\lambda_k^{p_2}+1$ (Part I §I.5.5), and $C_R\hat\lambda_k^{2d+1}\le A_2\hat\lambda_k^{p_2}$ by (Λ10) ($p_2>2d+1$). $\square$

*Remarks.* (1) LF-4R is (Rg) of LF-2 (Part I §I.5.2) with $\lambda=\hat\lambda$; with it, LF-2 (i) (§I.5.5) gives (H6′) after $R$. (2) Kept components keep their set and
spine and become $\mathsf{Active}(k,1,\varnothing)$ ((T6)); nothing in the kept data records a new large-field region (D-III.2). (3) For K1 the operator is not normalized, so P7's
"$\frac12N\log\beta_k|Z_0|$" is absent (ARCH Step 6); the bound above treats K1 and K2 by one route. (4) This closes O-II-5.

---

## III.9 The core: Lemma L, the analytic extension, and the coset average (P7 pp. 520–525; ARCH Lemma L, (M4))

### III.9.1 Lemma L for the local sets (closes O-3)

**Lemma III.9.1 (Lemma L; ARCH §3.8 as repaired by V4-01).** Let $a:=[R_{k_1-1}]+1$ and, for a core box $C\in\mathcal C_*$, $U^C:=C^{\approx}$, $W^C:=(C^c)^{\approx2}$ (scale $k_1$). Recall $U=\bigcup_CU^C$,
$W=(Z^c_{k_1})^{\approx2}$ (local, §III.0.2). Then:
(a) the sets $(U^C)^{\sim m}$, $C\in\mathcal C_*$, are pairwise disjoint for $m\le\frac{L+8}2$, and on $(U^C)^{\sim4}$: $U^{\sim n}=(U^C)^{\sim n}$ ($n\le4$) and $W=W^C$;
(b) every $x\in\mathbb B_{k_1}(W)\cap U^{\sim3}$ lies in $(U^C)^{\sim3}$ for exactly one $C$, and there is a nearest-neighbour path of fine sites from $x$, of length $\le M(3[R_{k_1-1}]+8)L^{k_1}$, inside
$W^\sim\cap(U^C)^{\sim4}$, ending at a site of $(U^{\sim3})^c$;
(c) on the support of the kernel (3.7′) after the rotation of Definition III.9.4 by $R=R_\sigma(\psi_0)$ (so that $\psi'_{k_1}=e_1$ on $(U^{\sim3})^c$),
$$|\delta\psi|<10MR_{k_1}\delta_{k_1}\ \text{on }\mathbb B_{k_1}(W)\cap U^{\sim3},\qquad|\delta\psi|<\delta_{k_1,1}\ \text{on }\Lambda_{k_1}\cap(U^{\sim3})^c,\qquad|\delta\psi|<\delta_{j,1}\ \text{on }\Lambda_j,\ k_1<j<k,\tag{3.11′}$$
for the real configuration $\delta\psi=\delta\psi(\psi_k)$, $\delta\psi=R\tilde\psi_{k_1}-\psi^0_{k_1,k}$ on $\mathbb B_{k_1}(W)\cap U^{\sim3}$; for the complex configuration $\psi_k+\psi'_k$, $|\psi'_k|<2\varepsilon_k$, the same bounds hold
with an additional $C\varepsilon_k\le C\varepsilon_{k_1}\beta_{k_1}^{-1}$.

*Proof.* (a) Lemma I.2.13 and Lemma I.2.14 with the width $\omega_{k_1}$ (the core boxes are distinct components of $Z_{k_1}$ at mutual distance $\ge\omega_{k_1}$, Lemma III.1.2 (e)); here
there are no other components at all, since the sets are local (D-III.1): this is the point of V4-01. (b) $x\in(U^C)^{\sim3}$ for exactly one $C$ by (a). $x\in\mathbb B_{k_1}(W)$ means $x$ is within
$2a+1$ cubes of $C^c$ (range of the minimal generating set, Lemma II.2.3 (c)). Move from $x$ along a coordinate direction towards the nearest face of the box $C$, through
it and on until the first site outside $C^{\sim(a+3)}=(U^C)^{\sim3}$: at most $(2a+1)+(a+4)=3a+5=3[R_{k_1-1}]+8$ cubes of side $ML^{k_1}$. Inside $C$ the path stays within $2a+1$ cubes of $C^c$,
hence in $W^C\subset W^\sim$; outside $C$ it is in $C^c\subset W$; it stays in $(U^C)^{\sim4}$; its end is outside every $(U^{C'})^{\sim3}$ by (a). This is P7 p. 522 and ARCH Lemma P with
$N_{\mathcal C}=1$. (c) As P7 p. 522 [checked, text layer], with the constants of §III.3: along the path of (b), $|\partial^1\psi'_{k_1}|<3\delta_{k_1}$ (inside $C$ the path lies in $\Omega_{k_1}\cap C$ at depth
$\le2a+1<[2R_{k_1-1}]+3$, where the small-field functions of the step $k_1-1\to k_1$ apply (proof of Lemma III.4.6); outside $C$, $\chi_{k_1}(Z^c_{k_1}\cap U)$ and $\chi^0$), and $\psi'_{k_1}=e_1$ at its
end, so $|R\tilde\psi_{k_1}(x)-\psi_0|=|\tilde\psi_{k_1}(x)-e_1|<3\delta_{k_1}M(3[R_{k_1-1}]+8)$. Then, with $z$ the $k$-block of $x$ and $z_0$ the clamped point (§III.5.3 (c)):
$|\psi_0-\psi_k(z_0)|<C_{2.20}\delta_k$, $|\psi_k(z_0)-\psi^0_k(z)|<3dD_0K_6\delta_k$, $|\psi^0_k(z)-\psi^0_{k_1,k}(x)|<4K_1K_6\delta_k$ ((2.43)); summing,
$|\delta\psi(x)|<(9[R_{k_1-1}]+24)M\delta_{k_1}+C\delta_k<10MR_{k_1}\delta_{k_1}$, since $R_{k_1}\ge R_{\rm base}\ge4L+20$ and $\delta_k\le\delta_{k_1}$. The other two bounds are $\chi''$ (Definition III.5.1 item 4). For the
complex configuration, $\delta\psi$ is analytic on the large domain $\tilde\Psi^c(U^\sim;c'_1,c'_0)$ of P7 p. 522 and $|\delta\psi(\psi_k+\psi'_k)-\delta\psi(\psi_k)|\le C|\psi'_k|$ (P7: "$|\delta\psi'(\psi'_k)|\le O(1)|\psi'_k|+K_2|\psi'_k|$"),
and $\varepsilon_k=\varepsilon_{k_1}L^{-\alpha n_1}<\varepsilon_{k_1}(\beta_{k_1}a)^{-1}$ by (III.1.1). $\square$

*Remark (O-3 closed).* ARCH's Lemma L (c) was false for the global sets (V4-01: a far Pre component of grid shape). In Part III every set is local: $U,W$ are built
from the core boxes of the ripe lineage only, and the characteristic functions $\chi_{k_1}(Z^c_{k_1}\cap U)$, $\chi^0$ are defined with them (Definition III.5.1); the factors of the
localized operator near the core are exactly the single-box objects of P7 for each box (Lemma II.5.9, Lemma I.3.16 with $\varpi\le2$, Definition III.2.1). So (3.11)′ holds on
the localized support, as V4-01 requires, and P7's (3.11) constant $10MR_{k_1}\delta_{k_1}$ survives (no $\hat W$ is needed there).

### III.9.2 The two-chart section and the rotation of the core

**Definition III.9.2 (the sections; ARCH (M4)).** For $u\in\mathbb C^N$ put $A(u):=ue_1^\top-e_1u^\top$ and
$$R_+(u):=I+A(u)+\frac{A(u)^2}{1+u\cdot e_1}\quad(u\cdot e_1\ne-1),\qquad R_-(u):=\Big(I-A(u)+\frac{A(u)^2}{1-u\cdot e_1}\Big)D\quad(u\cdot e_1\ne1),$$
with $D\in SO(N)$ fixed, $De_1=-e_1$ (a rotation by $\pi$ in the plane of $e_1,e_2$). For a configuration, the chart is $\sigma:=+$ if ${\rm Re}(\psi_0\cdot e_1)\ge0$ and $\sigma:=-$ otherwise.

**Lemma III.9.3 (properties of the sections).** On the complex quadric $\mathcal Q:=\{u:u\cdot u=1\}$ (bilinear product):
(a) $R_\pm$ are analytic, $R_\pm(u)^\top R_\pm(u)=I$ (complex orthogonal) and $R_\pm(u)e_1=u$; for real unit $u$ they are real rotations;
(b) for real unit $u$ with $u\cdot e_1\ne\pm1$, $R_-(u)=R_+(u)V(u)$ with $V(u)\in O_{e_1}(N):=\{V\in O(N):Ve_1=e_1\}$;
(c) if $u_0$ is real, $|u_0|=1$, $\sigma u_0\cdot e_1\ge0$, and $u\in\mathcal Q$, $|u-u_0|\le\epsilon'\le\frac14$, then $|R_\sigma(u)-R_\sigma(u_0)|\le C_{\rm rot}\epsilon'$ with $C_{\rm rot}=C(N)$.

*Proof.* (a) With $c:=u\cdot e_1$ and $u\cdot u=1$: $A(u)e_1=u-ce_1$, $A(u)u=cu-e_1$, hence $A(u)^2e_1=A(u)u-cA(u)e_1=(c^2-1)e_1$, and $R_+(u)e_1=e_1+u-ce_1+\frac{c^2-1}{1+c}e_1=u$. The same with $-e_1$ gives $R_-(u)e_1=(I-A+\frac{A^2}{1-c})(-e_1)=u$. Orthogonality
$R^\top R=I$ is a polynomial identity in $u$ (after clearing the denominator) that holds on the real unit sphere, where $R_+(u)$ is the rotation by the angle $\arccos c$
in the plane of $e_1,u$ (Rodrigues' formula with $A=\sin\vartheta\,K$, $\frac{1-c}{\sin^2\vartheta}=\frac1{1+c}$); the real sphere is Zariski dense in the irreducible quadric $\mathcal Q$, so the identity holds on
$\mathcal Q$ off the pole. (b) $R_+(u)^{-1}R_-(u)$ is a real orthogonal matrix fixing $e_1$. (c) The denominators are $\ge\frac12$ in modulus on the stated set. $\square$

**Definition III.9.4 (rotated representation).** For a real configuration in the chart $\sigma$ put $R:=R_\sigma(\psi_0)$ and change the integration variables of (3.7′) by
$x_{\rm in}\mapsto Rx_{\rm in}$, where $x_{\rm in}$ are the variables $\psi_{k_1}$ on $T^{(k_1)}\cap U^{\sim3}$ and the internal variables of the core operators $\mathbb T_{k_1}(C)$ (P7 p. 521: "(ψ, ψ′) → (Rψ, Rψ′)
on $U^{\sim3}_{k_1}$"); the variables $\psi''$ on $D''$ are not changed. The reference measure is invariant (Lebesgue measure and the a priori measure of the scale-$0$ spins are
$O(N)$-invariant). In the rotated integrand: (i) $\chi^0$ becomes the function with $\psi_0$ replaced by $e_1$ ($\chi^0(Rx;\psi_0)=\chi^0(x;R^{-1}\psi_0)$); (ii) $\chi_{k_1}(Z^c_{k_1}\cap U)$, the indicator parts of
the core kernels and of $K^{\rm red}_{\rm win,0}$ (on cubes in $U$) are invariant (no $h$-condition at scales $\le k_0$; (S5)(i)); (iii) $\chi''$ does not involve $x_{\rm in}$; (iv) every other factor is
the exponential of a function analytic in $(Rx_{\rm in},x_{\rm out},\psi_k,h,g)$.

### III.9.3 The analytic extension (Lemma 3.1′) and joint covariance

**Lemma III.9.5 (complex rotation of the core) [v1.3: P3-02].** Let $\tilde R\in O(N,\mathbb C)$ with $|\tilde R-I|\le C_{\rm rot}\cdot4\varepsilon_k$. For each core box $C$, write the real kernel, including inherited kept factors, as $K_{k_1}(C)(x)=\mathbf1_{A_C}(x)e^{-a_C(x)}$ as in (S5). On the fixed real integration contour define
$$K^c_{k_1}(C;\tilde R,x,h,g):=\mathbf1_{A_C}(x)\exp\{-a_C(\tilde Rx;h)+b_C(\tilde Rx;h,g)\},\qquad x\text{ real}.$$
Then $\int d x\,|K^c_{k_1}(C;\tilde R,x,h,g)|\le e^{-\kappa_{k_1}(C)+1}$. Every indicator in $A_C$, including one inherited from a kept kernel, is evaluated at real $x$.
*Proof.* For a real rotation, change variables on the core box; real $O(N)$ invariance of $A_C$ gives $\mathbf1_{A_C}(Rx)=\mathbf1_{A_C}(x)$. For complex $\tilde R$, keep that measurable factor and continue only $a_C,b_C$. By (S5), $a_C$ is jointly invariant and analytic; joint invariance continues analytically to $O(N,\mathbb C)$ near $I$
($\tilde R\mapsto a_C(\tilde Rx;\tilde Rh)-a_C(x;h)$ is analytic on a connected neighbourhood of $I$ in the complex group and vanishes on the real points, a totally real submanifold of full
dimension). So $a_C(\tilde Rx;h)=a_C(x;\tilde R^{-1}h)$ and $|a_C(x;\tilde R^{-1}h)-a_C(x;h)|\le C_{\rm S5}|\tilde R^{-1}h-h||C|_{k_1}\le\frac12$ by (S5)(iii) and (Λ25). The boundary factor $b_C$ is analytic
on the H7 domain, which contains $\tilde Rx$ (the displacement is $\le C\varepsilon_k|x|\le C\varepsilon_k$, much smaller than the radii $\varepsilon_j$, $j\le k_1$), with the bound of (S0); by the one-variable Cauchy
estimate along the complex line from $x$ to $\tilde Rx$, $|b_C(\tilde Rx)-b_C(x)|\le2\sup|b_C|\cdot C\varepsilon_k/\varepsilon_{k_1}\le\frac12$ (as $\varepsilon_k/\varepsilon_{k_1}<(\beta_{k_1}a)^{-1}$ and $\sup|b_C|$ is polynomial in $\hat\lambda$).
The two exponential changes cost at most $e^{1/2}$ each. Consequently $|K^c_{k_1}|\le e\,\mathbf1_{A_C}(x)e^{-{\rm Re}\,a_C(x)+{\rm Re}\,b_C(x)}$ on the real contour, and (D5) at scale $k_1$ with $F\equiv1$ gives the bound. This majorant is independent of $\tilde R$ in the chart neighbourhood and is integrable. For disjoint core boxes apply it successively with other variables fixed; their indicators remain real at each integration. $\square$

**Lemma III.9.6 (Lemma 3.1′: analytic extension, coset average, joint covariance; P7 Lemma 3.1, ARCH (M4), OBS requirement 2).** Let
$\Phi(\psi_k,h,g):=\int d(\text{internal})\,K^{(3.7)}_{\rm in}e^{b^{(3.7)}}F$, where $K^{(3.7)}_{\rm in}$ is (3.7′) without the front functions $\chi_k(Z\cap Z''^c_0)\tilde\chi_k(Z''_0\cap Z^c_0)\chi_{Z_0}$, and $F$ a bounded function of the
internal variables, analytic in the parameters. Then:
(a) (*chart representation*) for real $\psi_k$ in the chart $\sigma$, $\Phi(\psi_k)=\int d(\text{internal})\,\big[K^{(3.7)}_{\rm in}e^{b^{(3.7)}}F\big](R_\sigma(\psi_0)x_{\rm in},x_{\rm out})$, and in this integrand the indicators do not
depend on $\psi_k$; equivalently (P7's coset average) $\Phi(\psi_k)=\int_{O_{e_1}(N)}dV\int d(\text{internal})[\cdots](R_\sigma(\psi_0)Vx_{\rm in},x_{\rm out})$ for either chart;
(b) (*analytic extension*) $\Phi$ extends analytically in $\psi_k$ to the complex domain $\Delta^c_k(U_k;1,\varepsilon_k)$ (P5 (1.36) at scale $k$; the tube of complex displacements of modulus
$<2\varepsilon_k$ around the real $\varepsilon_k$-regular configurations), jointly with $g$ on $\{\|g\|_{\ell^1(V_Z)}<1\}$, and with the front functions removed the removed operator satisfies (3.10′) with
$\int d\psi_k\restriction_Z$ replaced by the supremum over this domain:
$$\sup_{\psi_k\in\Delta^c}\Big|\sum_{\mathfrak a}\int d(\text{internal})\,K^{(3.7),c}_{\rm in}\,e^{E_k|Z|_k+b^{(3.7),c}}F\Big|\ \le\ e^{-A_2\hat\lambda_k^{p_2}-H_k|Z|_k}\sup|F|.\tag{3.10″}$$
[v1.3: P3-03] The superscript $c$ means the chart continuation with every internal indicator on real variables as in Lemma III.9.5. The front factor $\chi_{Z''}(\psi_k)$ is absent. It is used only in the real density identity (3.21), where the removed branch and $\rho_{k,0}$ recombine to $\chi_k(Z)$.
(c) (*joint covariance*) for $S\in O(N)$, $\Phi(S\psi_k;Sh,Sg)=\Phi(\psi_k;h,g)$ when $F$ is jointly invariant, on the real domain and on the complex domain.

*Proof.* (a) Definition III.9.4: the change of variables is exact for each fixed real $\psi_k$, and $\chi^0(R_\sigma(\psi_0)x;\psi_0)=\chi^0(x;e_1)$; integrating over $V\in O_{e_1}(N)$ (normalized Haar
measure) changes nothing because $V$ preserves $e_1$ and the integrand at $R_\sigma(\psi_0)Vx$ is the integrand at $R_\sigma(\psi_0)x$ after the change of variables $x\mapsto Vx$. By Lemma
III.9.3 (b) the two charts differ by such a $V$, so the coset form is independent of the chart (P7 p. 521: "we integrate ... over the coset $O_{\psi_0}(N)$ and we divide the integral
by the volume of the coset"). **The average is taken on the full integrand**, including the $h$- and $g$-dependent exponentials (OBS §4.2 (2)). (b) In the chart representation
the integrand depends on $\psi_k$ only through analytic functions ($\psi^0_k$, $\phi^0_k$, $\psi^0_{k_1,k}$, $\psi_0$ and $R_\sigma(\psi_0)$; Lemma III.3.3, Lemma III.9.3). For complex $\psi_k$ define
$\Phi^c$ by the same integral with $R_\sigma(\psi_0)$ complex orthogonal, keeping all internal indicators fixed on the unrotated real variables; it is analytic by dominated convergence using Lemma III.9.5 and the bounds below. The chart extensions agree on overlaps:
the intersection of two polydiscs centred at real points is convex, invariant under complex conjugation, hence contains real points, where both equal $\Phi$; by the identity
theorem they agree on the (connected) intersection. So they glue to an analytic function on the tube. *Bounds.* Write $R_\sigma(\psi_0+\psi'_0)=R_\sigma(\psi_0^r)\tilde R$, $\psi^r_0$ the reference
vector of the real part ($|\psi'_0|\le C\varepsilon_k$ by (2.20′) in its complex form), $|\tilde R-I|\le C_{\rm rot}\cdot4\varepsilon_k$ by Lemma III.9.3 (c). Undo the real rotation $R_\sigma(\psi_0^r)$ by a change of
variables. The core: Lemma III.9.5. The window and (3.7′) exponentials: P7's estimates (3.11)–(3.19) with the constants of Part III, i.e. (3.11)′ (Lemma III.9.1 (c)); the
expansion (3.12)–(3.14) of $\delta\phi_{k_1,k}(\psi_k+\psi'_k,\delta\psi+\delta\psi')$ by P2 Proposition 3.1 (in the project BG Prop 5.1, analytic on $\{|\delta\psi|<c'_6\}$, which contains the
configurations by (3.11)′ and (Λ22)), giving
$$|\delta\phi'_{k_1,k}|,\ L^j|\partial\delta\phi'|,\ L^{2j}|\Delta\delta\phi'|,\ L^{2j}|\delta\alpha'|<C\big(\hat W_k\delta_j\varepsilon_k+\varepsilon_j\beta_j^{-1}\big)\ \text{on }\Lambda_j\cap X_{\rm win}\tag{3.15′}$$
(the real part $\delta\phi_{k_1,k}$ with $C\hat W_k\delta_j$, by (2.49′)); the real part of the fluctuation action is $\ge0$ (3.16); the six cross terms of $\beta_k\delta A'^*_k$ are bounded as in (3.17):
$$|\beta_k\langle\partial\delta\phi,\partial\delta\phi'\rangle|\le\sum_{j=k_1}^k\beta_jC^2\hat W_k\delta_j(\hat W_k\delta_j\varepsilon_k+\varepsilon_j\beta_j^{-1})L^d\nu_{\max}(LM\mathrm{crit}_k)^d\le C'\hat\lambda_k^{a_{17}}\Big(n_1\varepsilon_k+\sum_j\varepsilon_j\beta_j^{-1/2}\Big)\le\beta_{k_1}^{-1/4}\tag{3.17′}$$
with $a_{17}:=p_2+2w_0+2d+2p_0$, using $\varepsilon_k\le\varepsilon_{k_1}(\beta_{k_1}a)^{-1}$ and $\varepsilon_j\beta_j^{-1/2}\le\varepsilon_0\beta_j^{-1/2}$; so $|\beta_k\delta A'^*_k|<6\beta_{k_1}^{-1/4}\le1$ (3.18′) and
$|\exp(-\beta_k\delta A^*_k)|<e^3$ (3.19′), where (2.60′) is redone with $|L^{2j}(\alpha^0_k+\nu_k)|\le6K_1K_6\varepsilon_k+L^{2(j-k)}\beta_k^{-1}$ (ARCH Step 4). The composed-Gaussian term
$\frac12\sum_z\beta_ka^\natural_z|\mathcal Q_z\psi''|^2$ is real and $\ge0$ ($\psi''$ real). $|C^\natural|$ is bounded by (III.6.1) (complex case, part of $L_{\rm res}$), $|\beta_kA^*_{0,k}(Z_{k_1})|<1$ (Lemma III.6.4 (a)),
$\tilde{\mathcal E}_0$ by Lemma III.8.2, and the arguments of $C_{k_1,k}$, $b_{\rm win}$ and of the boundary terms lie in their analyticity domains by (3.11)′ (P7 p. 525). With these bounds the
proof of Lemma III.8.7 and of Theorem III.8.9 (c) goes through with the supremum over $\Delta^c$ in place of the integral over $\psi_k\restriction_Z$ (the volume factors of $\psi_k$ were
counted in $L_{\rm res}$ and are not needed here). [v1.3: P3-03] The estimate is performed after discarding $\chi_{Z''}$: the positive real-integrand bound of Lemma III.8.7 uses no support condition of this factor, and its refund applies on the full retained domain. The gain $\gamma_5$ is reserved for the kept $\varkappa_5$ branch. Thus the analytic majorant and (3.10″) contain no output indicator. (c) In the original (unrotated) integral, change all integration variables by $x\mapsto Sx$: the
reference measure is invariant, and every factor is jointly covariant (quiet kernels: Lemma II.5.10; data: (S0), (S3); the functions of $R$: $\psi^0_k$, $\phi^0_k$, $\psi^0_{k_1,k}$ are
equivariant and $\psi_0(S\psi_k)=S\psi_0(\psi_k)$; boundary terms: (D7)). So $\Phi(S\psi_k;Sh,Sg)=\Phi(\psi_k;h,g)$ on the real domain. The complex domain is invariant under $S$ (its
conditions are invariant under real orthogonal maps), and both sides are analytic, so the identity extends (identity theorem on each connected component, each of which
contains real points). $\square$

*Remark.* P7 states that $R$ "can be chosen locally analytic" and that the coset average gives a "globally defined analytic function of $\psi_0$" (p. 521). The chart
representation with the two sections $R_\pm$ and the gluing by the identity theorem is the precise form of that sentence; the coset average is an equivalent way to write
the glued function. P7's bound "$|R(\psi_0+\psi'_0)|<e^{O(\varepsilon_k)}<\frac32$" is Lemma III.9.3 (c), and the effect of the non-orthogonal $R$ on the core operator is Lemma III.9.5,
which P7 does not discuss.

---

## III.10 The polymer expansion, the new boundary terms, and LF-4 (P7 pp. 525–529; ARCH (M6), §8.3)

### III.10.1 Joint admissibility of components (D-III.7)

For an admissible history the pre-$R$ components at scale $k$ are determined by their localized histories (Lemma I.3.9, Definition I.4.4). The polymer expansion of $R$
sums over families of removed components with a fixed kept part, so it needs the converse: when is a family of localized histories the family of components of an
admissible history?

**Definition III.10.1.** A *configuration* is a finite family $\mathfrak F=\{(Z,\mathfrak a_Z)\}$ of sets $Z\subset\mathbb T_k$ with localized histories $\mathfrak a_Z\in\mathfrak H_k(Z)$ (each an admissible history with
the single pre-$R$ component $Z$), the $Z$ pairwise at index distance $\ge\omega_k$. It is *admissible* if there is an admissible global history whose pre-$R$ components at scale $k$
are exactly the $Z$'s, with localized histories $\mathfrak a_Z$ (R-records at scales $<k$ included). Two members are *linked* if their sets are at index distance $\le2\omega_k$.

**Lemma III.10.2 (cliques suffice).** A configuration is admissible iff every subfamily whose members are pairwise linked (a clique) is admissible. Subfamilies of admissible
configurations are admissible.

*Proof.* *Subfamilies.* Remove some members. By monotonicity of the set functions (proof of Lemma I.3.9) the outputs at every step can only shrink, and each remaining
member's local output is still produced (its own seeds remain). A point produced by the remaining seeds is attributed (Lemma I.3.8) to a remaining seed by a chain of steps
$<\omega$ inside the output; in the full history the same chain lies inside the full output, so the point lies in the component of that seed, i.e. in the local output of a
remaining member. Hence the outputs of the subfamily are the disjoint union of the remaining local outputs, at every scale and hull round; R-records are per component.
*Cliques suffice.* Induction over the steps $j\to j+1\le k$ and the hull rounds. At a step, the set functions of Definition I.3.1 are openings $\mathrm{Op}_m(F)$ and $\mathrm{Op}_m(F;\Omega)$
with $m\le[2R_j]+3$: a site $x$ lies in the complement of the global opening iff every $L$-block containing $x$ is within $m-1$ of $F$, which depends only on the parts of $F$
within $m+L-2$ of $x$. These parts come from seeds of members whose lineages at scale $j+1$ lie within $m+L$ cubes of $x$; two such members are, as fine sets, within
$2(m+L)ML^{j+1}$ of each other, i.e. within $2(m+L)L^{j+1-k}\le2([2R_j]+3+L)\le2\omega_k$ cubes at scale $k$ (lineages lie in the final sets, Lemma I.4.3 (c)). So the members
involved at $x$ form a clique, and by the clique's admissibility $x$ is in the global output iff it is in the union of the local outputs. Two local outputs at distance
$<\omega$ would form a linked pair whose admissibility excludes it. The hull closure acts on separated components and its boxes are those of the local closures. The
bookkeeping (spines, clocks, states, ripeness) and the R-records are functions of the localized histories (Part I §I.4). $\square$

### III.10.2 Removed clusters and the gas identity

Fix a kept history $\mathbb A'$: an admissible pre-$R$ history of the non-removed components (non-ripe, and ripe with a kept label), whose pre-$R$ region at scale $k$ is
$Y_k$. Its underlying pre-$R$ history $\mathbb A'_{\rm pre}$ (labels forgotten) is in $\mathfrak A$ (D-III.8 and Lemma III.10.2).

**Definition III.10.3 (removed clusters).** A *removed component* is a pair $(Z,\mathfrak a)$ with $Z$ ripe at $k$ and the removed outcome. A *removed cluster* $\mathcal C$ is a
nonempty finite family of removed components whose sets are connected under "index distance $\le4\omega_k$" and at distance $\ge\omega_k$ from each other and from $Y_k$. Its *support*
is $S(\mathcal C):=\bigcup_{Z\in\mathcal C}Z^{\sim2\omega_k}$ and its *core* $c(\mathcal C):=\bigcup_{Z\in\mathcal C}Z$. Two clusters are *compatible* if their supports are disjoint (equivalently, all their members are at
distance $>4\omega_k$). The *admissibility factor* is $a(\mathcal C;\mathbb A'):=1$ if $\mathcal C\cup\mathcal Y(\mathcal C)$ is admissible, where $\mathcal Y(\mathcal C)$ is the set of components of $Y_k$ within distance
$2\omega_k$ of a member of $\mathcal C$ (with their localized histories), and $:=0$ otherwise.

**Lemma III.10.4 (gas identity).** For fixed $\mathbb A'$, the histories $\mathbb A\in\mathfrak A$ whose non-removed part is $\mathbb A'$ correspond bijectively to the families of pairwise compatible
removed clusters $\{\mathcal C_1,\dots,\mathcal C_n\}$ with $\prod_ia(\mathcal C_i;\mathbb A')=1$ (the clusters of the removed components of $\mathbb A$ under "distance $\le4\omega_k$"). Moreover $a(\mathcal C;\mathbb A')$
does not depend on $\mathbb A'$ if $S(\mathcal C)\cap Y_k=\varnothing$.

*Proof.* Given $\mathbb A$, its removed components split into the classes of "distance $\le4\omega_k$"; distinct classes are compatible. Conversely, by Lemma III.10.2 a family of removed
components together with $\mathbb A'$ is admissible iff every clique is; a clique containing a removed $Z$ consists of members within $2\omega_k$ of $Z$, hence of members of the
cluster of $Z$ and of $\mathcal Y$ of that cluster; cliques inside $\mathbb A'$ are admissible. So joint admissibility is $\prod_ia(\mathcal C_i;\mathbb A')$. If $S(\mathcal C)\cap Y_k=\varnothing$, no component of
$Y_k$ is within $2\omega_k$ of $\mathcal C$, so $\mathcal Y(\mathcal C)=\varnothing$. Completeness of $\mathfrak A$ (D-III.8) makes every admissible $\mathbb A$ a term. $\square$

### III.10.3 The expansion (P7 (3.20)–(3.29))

**The terms.** By Definition III.8.3, $\rho'=\sum_{\mathbb A,\sigma}R[\rho(\mathbb A,\sigma)]$. Group the terms by the kept history $\mathbb A'$ (which records the K1 and K2 labels: a K2 outcome is
kept). In each term:
- *Boundary terms.* For $X\in\mathcal X(\mathbb A'):=\{X\in\mathcal D_k(\mathrm{mod}\,\Omega^c_k(\mathbb A')):X\cap Y_k\ne\varnothing\ne X\cap Y^c_k\}$ put $\hat{\mathcal B}(X;\mathbb A'):=\mathcal B^{(k)}(X,\mathbb A'_{\rm pre})$ (the datum of rep). If $X$ does
  not meet a removed component of $\mathbb A$, then $\mathcal B^{(k)}(X,\mathbb A)=\hat{\mathcal B}(X;\mathbb A')$, because by (D7) the term depends on the history only through $\mathbb A\cap X$, and $\Omega^c_j\cap X\subset Z_k\cap X=Y_k\cap X$.
  So $\mathcal B^{(k)}(\mathbb A)=\sum_{X\in\mathcal X(\mathbb A')}\hat{\mathcal B}(X;\mathbb A')+\mathcal B''(\mathbb A)$, where $\mathcal B''(\mathbb A)$ collects $\mathcal B^{(k)}(X,\mathbb A)$ over the $X$ that meet a removed component, minus
  $\hat{\mathcal B}(X;\mathbb A')$ over the $X\in\mathcal X(\mathbb A')$ that meet one (P7 p. 527: "all the terms with localization domains disjoint with ($\Omega^c_k\cap Z_i$) are cancelled"; we cancel the larger class
  of domains disjoint from $Z_i$, which is what makes the remaining terms functions of $\mathbb A'$).
- *Small-field part* (P7 (3.20)–(3.25), cited). For a removed $Z$, $\chi_{Z''}$ and the front functions give $\chi_k(Z)$ (3.21) [$\chi_{Z_0}=1$ there since $C_6=3dD_0(K_6+1)$]; so
  $\chi_k((Y_k\cup\bigcup Z_i)^c)\prod_i\chi_k(Z_i)=\chi_k(Y^c_k)$. The main actions $-\beta_kA^*_k(Z_i;\psi_k,\phi_k(\mathbb B_k(Z_i^\approx)))$ of the $\rho_{k,0}(Z_i)$ and the small-field functions on
  $(Y_k\cup\bigcup Z_i)^c$ are re-expanded around the backgrounds of $Y^c_k$ (P7 (3.22)–(3.24): background change by I-2 and P3 (2.55)–(2.56); the effective actions by P1 (3.127),
  Corollary 3.10 and P3 Proposition 4.3; P6 §2): the result is $\big[\mathcal A_k+\mathcal F_k+\mathcal R^{(k)}\big](Y^c_k)+\sum_X\mathcal B'(X)$, with new terms $\mathcal B'(X)$ whose domains meet some $Z_i$, local, analytic on the
  H7 domain, jointly covariant, bounded by $B'e^{-\kappa_+d_k^{\rm cov}(X\,\mathrm{mod}\,\Omega^c_k)}$ with $B'$ an output of rows 0–11 ("the constant (3.129) [1]", P7 p. 527 [checked]; P7 adds that the background part
  of these terms is $O(e^{-\frac14\gamma_0(2R_k-2M_1)})$). *Status:* cited; same inputs as O-2′. The vacuum term $-E_k|Z_i|$ of the extended action is compensated by $e^{E_k|Z_i|}$ in the
  removed operator (P7 (3.26)).
Hence (P7 (3.26))
$$\rho'=\sum_{\mathbb A'}\chi_k(Y^c_k)\,e^{[\mathcal A_k+\mathcal F_k+\mathcal R^{(k)}](Y^c_k)}\ \mathbb T_k(Y_k,\mathbb A')\Big[e^{\sum_{X\in\mathcal X(\mathbb A')}\hat{\mathcal B}(X;\mathbb A')}\ \Xi(\mathbb A')\Big],\qquad
\Xi(\mathbb A'):=\sum_{\{\mathcal C_i\}}\prod_ia(\mathcal C_i;\mathbb A')\,\Big[\bigotimes_i\bigotimes_{Z\in\mathcal C_i}T^{\rm rem}(Z)e^{E_k|Z|_k}\Big]e^{\mathcal B''+\sum\mathcal B'},\tag{3.26′}$$
the sum over the families of compatible removed clusters (Lemma III.10.4), $T^{\rm rem}(Z)$ the removed operator without front functions, acting on the internal variables of $Z$;
$\mathbb T_k(Y_k,\mathbb A')$ is the product of the operators of the non-removed components (kept ones with their kept kernels, Definition III.8.8).

**Operator-gas application hypothesis (H-op) [v1.3: P3-05].** On each finite torus, represent the internal integration as a product of probability spaces indexed by cubes and the retained terms of (3.26′) as a finite gas of measurable, bounded, support-dependent light weights $\beta_y$ and heavy weights $\tau_z$. Their charged supports are their full supports minus $S_0$; full supports are connected animals closed under every component of $S_0$ they meet, and every heavy core is contained in its charged support. For the nearest-neighbour cube graph $H$ of maximum degree $\Delta\le2d$, require all support, dependence, norm, entropy, and geometric hypotheses of gasOp_pe_hole in HoleOperator.lean, including the integrated heavy norm bound $e^{-p-h|S(z)|}$ and the light supremum bound $B_0e^{-\kappa''\operatorname{steiner}(S(y))}$. Choose $\kappa_g,\kappa_p,\alpha$ so that
$$q:=\Delta^2 2^{\Delta+1}e^{-((\kappa_g-2)-\kappa_p-\alpha)}<1,\qquad
\frac{3e^{-p}2^{\Delta+1}e^{-((\kappa_g-2)-\kappa_p-\alpha)}}{1-q}\le\alpha\le\tfrac12\beta_k^{-m-1},$$
and require $\kappa_p\operatorname{steiner}(H,X)\ge\kappa d_k^{\rm cov}(X\,\mathrm{mod}\,\Omega^c_k\cap Y_k)$ for every output support. These are concrete conditions on the P7 re-expansion and its localization domains, not conclusions of the abstract Lean theorems.

**Lemma III.10.5 (the polymer expansion; P7 (3.27)–(3.28), PE §2.6 (GAS), landed `gasOp_eq`, `gasOp_activity_bound`, `gasOp_pe`, `gasOp_pe_hole`).** Assume (Λ25), $\kappa\ge\kappa_{\rm flow}$ and (H-op). Pointwise in the
variables of $Y_k$ and in $(h,g)$:
$$\Xi(\mathbb A')=\exp\sum_{X}P^{(k)}(X;\mathbb A'),\qquad|P^{(k)}(X;\mathbb A')|\le\tfrac12\beta_k^{-m-1}e^{-\kappa d_k^{\rm cov}(X\,\mathrm{mod}\,\Omega^c_k\cap Y_k)},\tag{3.28′}$$
the sum over the connected sets $X$ of cubes that contain every component of the hole $S_0:=\Omega^c_k\cap Y_k$ they meet and are not contained in it. Each $P^{(k)}(X;\mathbb A')$
depends only on $\psi,\psi',h,g$ restricted to $X$ and on $\mathbb A'\cap X$, is analytic (in $\psi_k$ on $\Xi_k(1,\varepsilon_k)$ localized to $X$, in the fluctuation variables on (1.37), in $g$ on the polydisc), real
for real arguments, jointly $O(N)$-covariant and invariant under the Euclidean symmetries preserving $\pi_k$. If $X\cap Y_k=\varnothing$, then $P^{(k)}(X;\mathbb A')=P^{(k)}_\varnothing(X)$, the term of
the same expansion with no kept region.

*Proof.* [v1.3: P3-05] Fix the external configuration and parameters. The finite product space in (H-op) is the configuration space of GasOperator.lean. Its light objects are the localized terms of $\mathcal B''+\sum\mathcal B'$ and its heavy objects are the removed clusters in (3.26′), including their dependent internal variables. The support maps and core map are those of (H-op). The measurability and boundedness assumptions allow Fubini on the finite gas sum. Thus gasOp_eq identifies (3.26′) with the polymer partition function whose activity is the integral of the *product* of all weights in a connected family. In particular no product of separate expectations is used.

The integrated heavy bound and light supremum bound in (H-op) are the respective hypotheses $h_\tau,h_B$ of gasOp_activity_bound. Its geometric and entropy assumptions give the activity rate $\kappa_g-2$ and prefactor $3e^{-p}$ in the hole form of the theorem. The inequalities defining $q$ and $\alpha$ are exactly the convergence inequalities $hq,hcond$ of gasOp_pe_hole; its animal and HoleClosed hypotheses make the output supports closed under the hole. Applying gasOp_pe_hole gives $\Xi=\exp\sum_X P^{(k)}(X)$ and, for each cube $b$ outside $S_0$,
$$\sum_{X\ni b}|P^{(k)}(X)|e^{\kappa_p\operatorname{steiner}(H,X)}\le\alpha.$$
For a nonempty output support choose $b\in X\setminus S_0$. Its summand is nonnegative, so $|P^{(k)}(X)|\le\alpha e^{-\kappa_p\operatorname{steiner}(H,X)}\le\frac12\beta_k^{-m-1}e^{-\kappa d_k^{\rm cov}(X\,\mathrm{mod}\,\Omega^c_k\cap Y_k)}$, by the last two conditions of (H-op). This is (3.28′). The non-hole conclusion gasOp_pe follows in the same way when $S_0=\varnothing$.

For complex external parameters, the same estimate is uniform on each compact subdomain by (H-op). Lemma III.9.6 supplies analyticity of each heavy weight with its real contour indicators fixed, and (D7) supplies it for the light weights. Finite products and sums are analytic; the uniform integral majorant permits integration by dominated convergence. The logarithmic series converges normally by the displayed weighted bound, hence each $P^{(k)}(X)$ is analytic. Dependence on the variables of $X$, reality, covariance and torus symmetry follow termwise from the support dependence and corresponding properties of the weights. If $X\cap Y_k=\varnothing$, each contributing connected family lies outside $Y_k$; its weights equal those of the no-kept-region gas by Lemma III.10.4, giving $P^{(k)}(X;\mathbb A')=P^{(k)}_\varnothing(X)$. $\square$

*Status [v1.3: P3-05]:* the abstract function-valued GAS and hole expansion are landed in GasOperator.lean and HoleOperator.lean as `gasOp_eq`, `gasOp_activity_bound`, `gasOp_pe`, `gasOp_pe_hole`. The application here remains conditional on the cited re-expansion (3.22)–(3.25), the product-space and geometric hypotheses (H-op), in particular hole closure and the two explicit PE inequalities, and the front-free analytic bound (3.10″); those are distinct inputs and are not consequences of the abstract GAS theorem.

### III.10.4 The new small-field term, the new boundary terms, and $B^\sharp$

**Definition III.10.6 (P7 (3.29) and p. 528–529).** $\mathcal R''^{(k)}_m(\psi_k,h,g):=\sum_{X}P^{(k)}_\varnothing(X;\psi_k,h,g)$, the whole-torus expansion with no kept region; its restriction to $Y^c_k$ is
$\sum_{X\subset Y^c_k}P^{(k)}_\varnothing(X)$. The boundary terms of $\mathrm{rep}'$ for $\mathbb A'$ are, for $X\in\mathcal X(\mathbb A')$,
$$\mathcal B^{(k)}_{\rm rep'}(X,\mathbb A'):=\hat{\mathcal B}(X;\mathbb A')+P^{(k)}(X;\mathbb A')\,\mathbf 1[X\cap Y_k\ne\varnothing],$$
and $\mathcal B^{(k)}_{\rm rep'}(X,\mathbb A'):=P^{(k)}(X;\mathbb A')$ for the polymers $X$ meeting $Y_k$ that are not in $\mathcal X(\mathbb A')$ (they meet $Y_k$, and they meet $Y^c_k$ because they contain a removed core).

**Lemma III.10.7 ($B^\sharp$; ARCH §5 row 12).** $|\mathcal B^{(k)}_{\rm rep'}(X,\mathbb A')|\le(B_{\rm st}+\frac12\beta_k^{-m-1})e^{-\kappa d_k^{\rm cov}(X\,\mathrm{mod}\,\Omega^c_k(\mathbb A'))}\le B^\sharp e^{-\kappa d_k^{\rm cov}(X\,\mathrm{mod}\,\Omega^c_k(\mathbb A'))}$ with
$$B^\sharp:=B_{\rm st}+1 .$$
$B^\sharp$ depends only on the constant $B_{\rm st}$ of the boundary terms created by the step (LF-3), which is an output of the small-field analysis (rows 0–11; P6 p. 15 [checked]:
"contributions to $\mathcal B^{(k+1)}$ constructed in various operations have bounds independent of $B_0$"); it does not depend on $B_0$, $H_0$, $c_1$, $c_2$ or $C_R$. The polymer part
is $\le\beta_k^{-m-1}\le1$ because $\lambda_*$ is chosen after $B_0,H_0,c_1,c_2$; the constants $B_{\rm cpl}$, $B'$ enter only through (Λ25). So the row-12 condition is $B_0\ge B^\sharp$, with no
cycle, **provided** LF-3 supplies $B_{\rm st}$ independent of $H_0,c_1,c_2$ (the large-field cost coefficients do not enter the small-field expansions; to be confirmed in Part IV.1).
*Proof.* $|\hat{\mathcal B}|\le B_{\rm st}e^{-\kappa_+d}\le B_{\rm st}e^{-\kappa d}$ (D-III.4) and (3.28′); $d_k^{\rm cov}(X\,\mathrm{mod}\,\Omega^c_k\cap Y_k)=d_k^{\rm cov}(X\,\mathrm{mod}\,\Omega^c_k(\mathbb A'))$ since $\Omega^c_k(\mathbb A')=\Omega^c_k\cap Y_k$. $\square$

*Remark (the B₀ bookkeeping across steps).* Version 4 of ARCH asked whether $B^\sharp$ is independent of $H_0,c_1,c_2$ (row 12 UNCERTAIN). In this construction the old boundary
terms are carried unchanged with the step constant $B_{\rm st}$ and decay $\kappa_+$, and $R$'s own terms are smaller than $\beta_k^{-m-1}$; the non-small constants of the cluster
expansion ($B_{\rm cpl}$, the GAS constant) are absorbed by $H_k$ and $\lambda_*$, which come last. The answer is yes, conditional on the stated property of $B_{\rm st}$.

### III.10.5 LF-4

**Theorem III.10.8 (LF-4; $R$ on covered windows; existential form; ARCH §8.3 as amended in §II.6.4).** Fix $d\ge3$, $N\ge2$ and the constants of the prefix §I.1.4 up to row 15,
with $B_0\ge B^\sharp$ (row 12), $c_1\ge C_W$, $c_2\ge C'_W$ (row 14) and $C_R$ of Definition III.8.6 (row 15). There is $\lambda^{\rm III}_*$, depending only on these constants (conditions (Λ18)–(Λ25)
of §III.O.3), such that, with $\lambda_*\ge\lambda^{\rm III}_*$ and $\beta\ge\beta_0$: for every $\nu\in(0,1]$, $h\in S^{N-1}$ and $k\ge1$, if $\mathrm{IsRep}^{\rm pre}_k(\mathsf c,\mathrm{rep},\rho)$ (Definition II.6.2, §II.6.3, version 1.1) and
$1\le k\le k_0$ for the a priori index of D-IV.11 (so $\beta_k\nu_k\le e^{2\epsilon}$ by (I.2)) [v1.3: P4-01], then there are families $\rho'$, $\mathrm{rep}'$ over the same admissible tori with:
- (a) $\int\rho'\,d\psi_k=\int\rho\,d\psi_k$ on every admissible torus, identically in $(h,g)$, $\|g\|_{\ell^1}<1$;
- (b) $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep}',\rho')$;
- (c) the small-field data of $\mathrm{rep}'$ are those of $\mathrm{rep}$ except that $\mathcal R^{(k)}_m$ is replaced by $\mathcal R^{(k)}_m+\mathcal R''^{(k)}_m$, where $\mathcal R''^{(k)}_m$ has the properties of P5 H4 with the bound
  $\frac12\beta_k^{-m-1}e^{-\kappa d_k^{\rm cov}(X)}$ for its localized terms, so that the sum satisfies H4 with $\beta_k^{-m-1}$ (the pre-class gives $\frac12\beta_k^{-m-1}$ for $\mathcal R^{(k)}_m$, §II.6.3) (analytic on $\Xi_k(1,\varepsilon_k)\times\{\|g\|_{\ell^1}<1\}$, local, jointly $O(N)$-covariant, invariant under the Euclidean symmetries preserving $\pi_k$,
  torus coherent);
- (d) the histories of $\mathrm{rep}'$ are those of $\mathrm{rep}$ with an $R$-record at scale $k$ marking every ripe component removed or kept with a label in $\mathfrak K$; the kept data are those of
  Definition III.8.8 and satisfy (S3) with LF-4R (Theorem III.8.9), in particular (Rg);
- (e) the boundary terms of $\mathrm{rep}'$ at scale $k$ are $\hat{\mathcal B}+P^{(k)}$ (Definition III.10.6), bounded by $B^\sharp e^{-\kappa d_k^{\rm cov}(X\,\mathrm{mod}\,\Omega^c_k)}$;
- (f) if $(\mathrm{rep}(\nu),\rho(\nu))_\nu$ satisfies $\mathrm{IsRepFam}^{\rm pre}_k$ (Definition II.6.4), then $(\mathrm{rep}'(\nu),\rho'(\nu))_\nu$ satisfies $\mathrm{IsRepFam}_k$.

*Proof.* Fix an admissible torus. $\rho'$ is Definition III.8.3, and (a) is Lemma III.8.4. *(D1).* By (3.26′), Lemma III.10.5 and Definition III.10.6,
$$\rho'=\sum_{\mathbb A'}\mathbb T_k(Y_k,\mathbb A')\Big[e^{\sum_X\mathcal B^{(k)}_{\rm rep'}(X,\mathbb A')}\,\chi_k(Y^c_k)\,\exp\big(\mathcal A_k+\mathcal F_k+\mathcal R^{(k)}+\mathcal R''^{(k)}_m\big)(Y^c_k)\Big],$$
where we used that $\sum_XP^{(k)}(X;\mathbb A')=\sum_{X\subset Y^c_k}P^{(k)}_\varnothing(X)+\sum_{X\cap Y_k\ne\varnothing}P^{(k)}(X;\mathbb A')$ and that the first sum is $\mathcal R''^{(k)}_m(Y^c_k)$; the history set of $\mathrm{rep}'$ is the set of
all kept histories $\mathbb A'$, i.e. all admissible histories with $R$-records at scale $k$ (it is complete). Absolute convergence: (1.26) for the operators, (3.28′). *(D2).* Only $\mathcal R^{(k)}_m$
changes; $\mathcal R''^{(k)}_m$ has the H4 properties by Lemma III.10.5 (the terms $P^{(k)}_\varnothing(X)$ with the bound $\frac12\beta_k^{-m-1}$; P7 (3.28) states const$\cdot\beta_k^{-m-1}\le\frac12\beta_k^{-m}$), and
$\mathcal R^{(k)}_m+\mathcal R''^{(k)}_m$ satisfies H4 with $\beta_k^{-m-1}$ because the pre-class gives $\frac12\beta_k^{-m-1}$ for $\mathcal R^{(k)}_m$ (§II.6.3; P5 p. 491); the other functions with superscript $k$
satisfy (D2) with $\kappa_+\ge\kappa$. *(D3).* $\chi_k(Y^c_k)$ by (3.21). *(D4).* The step data at scales $<k$ are unchanged; the kept data satisfy (S3) by Theorem III.8.9; (S4) holds
since all constructions use the localized history only. *(D5).* Lemma II.6.3 (a). *(D6).* For the components of $Y_k$: non-ripe ones are unchanged with $G_k=G^{\rm pre}_k$ and
$t^*>k$; kept ones satisfy (Rg) (Theorem III.8.9 (b)), so LF-2's $R$-step (Part I §I.5.5, with (Λ10)) gives (H6′) with the state $\mathsf{Active}(k,1,\varnothing)$. *(D7).* Lemma III.10.7
and the properties of $P^{(k)}$ in Lemma III.10.5. *(D8).* Every datum created here is a function of a localized history and of the variables in a set of diameter
$\le D''_0M+\dots$ around $Z$, defined by the same formulas on $\mathbb Z^d$; the polymer terms of sets in a small cube are torus-independent by PE (f) (transport) and
POLYMER §4.5. *(D9).* Unchanged. (d), (e) were shown. (f) The constructions are explicit formulas in the data of $\mathrm{rep}$ (indicators with thresholds $\delta_j(\nu)$, Gaussian
integrals, analytic functions of the running constants, the convergent expansion (3.28′)); outside a null set of values of the variables they have limits at
$\nu=0$, and all bounds above are uniform in $\nu$, so dominated convergence and the uniform convergence of the cluster expansion give (CONT$^{\rm LF}$) in the form of
Definition IV.3.1 (version 1.2; the $\mathbb Z^d$ data of (D8), the limit at $\nu=0$ only). $\square$

*What LF-4 replaces in P7.* Theorem 2 of P7 removes the components with $K=0$; LF-4 removes or keeps the ripe components. The kept ones carry the explicit kept data;
the removed ones are exponentiated into $\mathcal R''^{(k)}_m$ and new boundary terms. With LF-2 (ii) ((Rg) from LF-4R) and LF-3 this is the step $\mathcal R_{k-1}\to\mathcal R_k$ of LF-7
for $k\le k_0$.

---

## III.L Lean declarations asked for by Part III

Namespace `Balaban.LargeField`; all files Lean modules; files under `LargeField/R/`. Items are numbered P1–P16 in the order of the sections
(P10 is independent infrastructure and can be done first). Sizes are estimates including docstrings. "Needs" lists the landed Lean used and
the Part I–II blocks of §I.6 and §II.L; **bold** marks prerequisites that are not landed.

| # | Declaration(s) | Kind | Content | Needs | Est. lines |
|---|---|---|---|---|---|
| P1 | `ripe_quiet`, `ripe_core_boxes`, `ripe_layer_count`, `ripe_one_box`; `windowKernel`, `windowOp_eq`, `gaussOnly`, `gaussOnly_support` | def/thm | Lemmas III.1.2, III.1.3, Def. III.1.4, Lemma III.1.5 | Part I B, C (ripeness, lineages, Lemma I.4.13), J4, J6 | 600 |
| P2 | `composedWeight`, `composedMean`, `integral_window_comp` (Gaussian chain on the block tree, arbitrary positive $c_j$ and $z_j$), `composedWeight_ideal` (= `compWeight`), `composedWeight_err`, `meanShift_le`, `deepLayer_frac_le`, `totalShift_le` | def/thm | Lemmas III.1.6, III.1.7, III.1.7′ | `integral_blockSpin_comp` (`Gaussian/BlockSpin.lean`), `compWeight`, `compWeight_C1`; SF Theorem 5.3 bounds (**W43** renormalization analysis) | 900 |
| P3 | `kTwo`, `kThree`, `Zzero`, `ZzeroDD`, `lateScale_geom`, `ZzeroDD_sep` (Lemma III.5.0); `dirichlet_box_coercive` ($c_{D_0}$); `psiZero` with `psiZero_exists_unique`, `psiZero_analytic`, `psiZero_equivariant`; `refVec`, `refVec_close` | def/thm | Def. III.3.1, Lemmas III.3.2, III.3.3, III.5.0, Def. III.3.4, Lemma III.3.5 | `Background/ContractionAnalytic.lean`, `theorem72_linearResponse`, G5 | 1 100 |
| P4 | `windowBlocks`, `chainGraph`, `crossPair_window`, `nn_layers_adj`, `path_avoids_obstacles`, `lemmaCH` (with $\hat W_k$), `hatW_le`, `deltaSeq_admissible` | def/thm | Def. III.4.1, Lemmas III.4.2–III.4.5 | `enclosed_by_single_component`, `enclosed_component_diam`, `not_enclosed_boxes` (`LemmaS.lean`), `exteriorBoundary_starConn` (`Timar.lean`), torus lift (W37), Part I B | 1 000 |
| P5 | `deltaPsi`, `deltaPsi_le` ((2.48′)), `deltaPhi_le` ((2.49′)) | def/thm | Lemmas III.4.6, III.4.7 | P3, P4, `composeField`, `lemma62`, `prop51_exists_unique`; **G-2 decay / LOC** for (2.49′) | 600 |
| P6 | `windowGenSet` (a `GeneratingSet`), `windowAction_renorm` ((2.15′)), `composed_dominates` ((2.17′)) | def/thm | Def. III.2.1, Lemmas III.2.2, III.2.3 | G1–G3, `theorem73_real`, `theorem73_complex`, `compWeight_C1`; **P6 (2.31) renormalization formula and LOC I-4b, I-5** for (2.15′) | 900 |
| P7 | `chiTilde`, `chiS`, `chiZero`, `chiDD`, `chiZ''`; `Outcome` (`ϰ₁`–`ϰ₅`, `rem`), `kernel_decomp`, `smallFactor_1`–`smallFactor_5`, `smallFactor_ge` ((III.5.1)) | def/thm | Defs. III.5.1–III.5.2, Lemma III.5.3 | I2 (`lf1_gradient`, `lf1_hardSpin`), `theorem52_exists`, P3–P6 | 1 000 |
| P8 | `psiZeroMulti` (via `composeField`), `cancellation_identity` ((2.58′) with `Cnat0`, `Cnat1`), `Cnat_le`, `remaining_terms` (Lemma III.6.4) | def/thm | Def. III.6.1, Lemmas III.6.2–III.6.4 | P2, P5, BG (6.2) (`lemma62`), `isEL_compose`; **P7 Lemma 2.2** (cited) | 1 000 |
| P9 | `lemma25` (Cases A, B and the $\chi'$ functions) | thm | Lemma III.7.1 | `prop51_exists_unique`, `theorem73_real`, P5, P8; **P4 (4.11)–(4.12)**, **P3 Prop 2.1** (LOC) | 800 |
| P10 | `gasOp_eq`, `gasOp_activity_bound`, `gasOp_pe_hole`: GAS and PE with a hole for weights that are integral operators on disjoint sets of variables (pointwise in the external variables; norms = sup bounds of (3.10″)) | thm | Lemma III.10.5 (abstract part) | `gas_eq`, `gas_activity_bound`, `gas_pe` (`Polymer/Gas*.lean`), `pe_hole` (`Polymer/Hole.lean`), `pe_PY_analyticOnNhd` | 900 |
| P11 | `rhoZero`, `denominator_eq` (Lemma III.8.2), `Rop` (Def. III.8.3), `R_normalization` | def/thm | Defs. III.8.1, III.8.3, Lemmas III.8.2, III.8.4 | P2, P3, L1–L3; **P7 (3.3)–(3.5)** (finite-dimensional Gaussian estimate, to be proved) | 700 |
| P12 | `kernel37`, `Lres`, `CR`, `windowIntegral_le` ((III.8.5)), `keptData`, `lf4R` | def/thm | Defs. III.8.5, III.8.6, III.8.8, Lemma III.8.7, Theorem III.8.9 | P7–P9, P11, K1–K4, J5 | 900 |
| P13 | `lemmaL` ((3.11′)); `Aof`, `secPlus`, `secMinus`, `sec_orth`, `sec_e1`, `sec_lip`; `rotRep`; `core_complexRot_le`; `lemma31'` (chart representation, gluing by the identity theorem, (3.10″), joint covariance) | def/thm | Lemmas III.9.1, III.9.3, III.9.5, III.9.6, Defs. III.9.2, III.9.4 | P5, P8, P12, J7, (S5) in J5, Mathlib `AnalyticOnNhd` identity theorem | 1 100 |
| P14 | `Config`, `IsAdmConfig`, `adm_of_cliques`, `adm_sub`; `RemCluster`, `clusterSupp`, `admFactor`, `gas_identity` | def/thm | Def. III.10.1, Lemma III.10.2, Def. III.10.3, Lemma III.10.4 | Part I B, C (Lemma I.3.8, I.3.9, histories) | 800 |
| P15 | `expansion_326` ((3.26′); the re-expansion as a cited hypothesis-free statement once LF-3's background-change lemma lands), `polyExp`, `Rmm''`, `newBoundary`, `Bsharp`, `newBoundary_le` | def/thm | §III.10.3, Lemma III.10.5, Def. III.10.6, Lemma III.10.7 | P10, P13, P14; **LF-3 background change (O-2′)** | 900 |
| P16 | `lf4` (Theorem III.10.8, existential form, clauses (a)–(f)); `lf4_fam` | thm | Theorem III.10.8 | P11–P15, L2 (`IsRepPre`, `IsRep`, `IsRepFam`), Part I E (LF-2 $R$-step) | 600 |
| | **Total** | | | | **≈13 800** |

No file need exceed 1 200 lines. P1, P2 (given W43), P4, P10 and P14 can be drafted now (they need only landed Lean and Parts I–II blocks that
do not depend on Def-5/Def-6); P3, P6–P9 need Def-5 (landed) and the cited analytic inputs marked in bold; P11–P13, P15–P16 need Def-7 (L2).
The bold prerequisites are the open items O-2′ and O-III-2 below.

---

## III.O Status, changes, open items

### III.O.1 Status of the statements of Part III

| Statement | Status |
|---|---|
| Lemma III.1.2 ((RQ1)–(RQ5)) | proved here from Part I (Lemmas I.3.5, I.4.3, I.4.9, I.4.10, I.4.13) |
| Lemma III.1.3, Def. III.1.4, Lemma III.1.5 | proved here (P7 (2.6) [checked, text layer]) |
| Lemma III.1.6 (actual composed transformation) | proved here; one-step Gaussian identity landed (`integral_blockSpin_comp`); flow bounds of SF Theorem 5.3 cited from SF |
| Lemmas III.1.7, III.1.7′ (deep-layer fractions, total shift) | proved here (new) |
| Def. III.2.1 | definition; the generating-set property proved here (box by box) |
| Lemma III.2.2 ((2.15′)) | cited (P7 (2.10)–(2.16), P6 (2.31), P3 (2.55)–(2.56)); conditional on LOC (O-2′); P7's second bound in (2.15) is false for $\nu$ pieces and is not used |
| Lemma III.2.3 ((2.17′)) | proved here |
| Def. III.3.1, Lemma III.3.2, Lemma III.5.0 | proved here; the threshold $8$ of $k_3$ and the neighbourhood in $Z''_0$ are new |
| Lemma III.3.3 (P7 Lemma 2.1 with $D_0$) | cited, with the coercivity constant $c_{D_0}$ proved here; route via the landed analytic contraction (Lean P3) |
| Def. III.3.4, Lemma III.3.5 ((2.20′)) | proved here ($C_{2.20}=12d(D_0+2)+3$) |
| Def. III.4.1, Lemmas III.4.2–III.4.5 (Lemma CH) | proved here (Lemma S landed); $\hat W_k\le C_{\hat W}\hat\lambda_k^{w_0-2}$ explicit |
| Lemma III.4.6 ((2.48′)) | proved here from Lemma CH, Lemma III.3.3 and P7 (2.43) (cited; BG (6.2)) |
| Lemma III.4.7 ((2.49′)) | cited (P7 Lemma 2.4; P3 Prop 2.1 = BG Prop 5.1 with G-2/LOC decay) |
| Defs. III.5.1, III.5.2 | definitions; item 4 of III.5.1 (the set $D''$) is a reading of P7 (2.61), **UNCERTAIN** (minor) |
| Lemma III.5.3 (small factors) | proved here from LF-1, BG Theorem 5.2 (3), Lemma CH |
| Def. III.6.1, Lemma III.6.2 | cited (P7 (2.40)–(2.46), Lemma 2.2) |
| Lemma III.6.3 ((2.58′), remainder $C^\natural$) | proved here (new) |
| Lemma III.6.4 ((2.59′), (2.60′)) | proved here with $k\le k_0$, $\beta_k\nu_k\le e^{2\epsilon}$ and strengthened (Λ25) |
| Lemma III.7.1 (Lemma 2.5) | proved here on the support of the reduced kernel from the cited inputs P4 (4.11)–(4.12), P3 Prop 2.1; BG Prop 5.1 and I-2 landed |
| Defs. III.8.1, III.8.3, III.8.5, III.8.6, III.8.8 | definitions |
| Lemma III.8.2 (denominator) | cited (P7 (3.3)–(3.5)); a finite-dimensional Gaussian estimate |
| Lemma III.8.4 (normalization) | proved here |
| Lemma III.8.7 (window integral, refund) | proved here |
| Theorem III.8.9 (LF-4R) | proved here |
| Lemma III.9.1 (Lemma L, local sets) | proved here; closes O-3 |
| Def. III.9.2, Lemma III.9.3, Def. III.9.4 | proved here |
| Lemma III.9.5 (complex rotation of the core) | proved here (new; uses (S5)) |
| Lemma III.9.6 (Lemma 3.1′) | front-free analytic extension proved here conditional on the corrected core majorant and the expansion (3.12)–(3.14) of $\delta\phi$ (cited: P2 Prop 3.1 = BG Prop 5.1) |
| Def. III.10.1, Lemma III.10.2, Def. III.10.3, Lemma III.10.4 | proved here (new: cliques, removed clusters) |
| (3.26′): re-expansion around the backgrounds of $Y^c_k$ | cited (P7 (3.20)–(3.25), P6 §2, P1 Cor 3.10, P3 Prop 4.3); same inputs as O-2′ |
| Lemma III.10.5 (polymer expansion) | conditional on the stated function-valued GAS application and the cited P7 analytic inputs; the abstract operator GAS and hole expansion are landed as gasOp_eq, gasOp_activity_bound, gasOp_pe and gasOp_pe_hole; the application remains conditional on the P7 re-expansion and concrete hole-closure hypotheses |
| Def. III.10.6, Lemma III.10.7 ($B^\sharp=B_{\rm st}+1$) | proved here; independence of $H_0,c_1,c_2$ conditional on LF-3's $B_{\rm st}$ |
| Theorem III.10.8 (LF-4) | proved here, given the cited inputs listed above (the O-2′ group and O-III-2) and the LF-3 obligations O-III-1 |

### III.O.2 Changes to Parts I–II and to ARCH v4

*Part I* (made in place):
1. Row 4: the Part III constants $D''_0=9(2c_0+1)+8$, $c_{D_0}=4(D_0+1)^{-2}$, $C_{2.20}$, $C_6=3dD_0(K_6+1)$, $C_{23}=3dL+2$, $C_{24}=2K_3C_{23}$.
2. Row 7: $R_{\rm base}\ge44K_1K_6$ (was $6K_1K_6$; Lemma III.7.1 with the threshold $8$ of $k_3$).
3. Row 12: $B_0\ge B^\sharp:=B_{\rm st}+1$; the UNCERTAIN of ARCH row 12 is resolved, conditional on LF-3 (Lemma III.10.7).
4. Row 15: $C_R$ is defined by (III.8.4) and depends on rows 0–11 only; row 16 and §I.7.2: the conditions (Λ18)–(Λ25) of §III.O.3.
5. The constant $A'_3$ of rows 9 and (Λ10) is the explicit value of Lemma III.5.3; LF-2's (Rg) is Theorem III.8.9 (b). No change to LF-2 itself.

*Part II* (version 1.1, made in place; listed in §II.O.5): the audit fixes P2-01–P2-06, and the amendments required by Part III: (D7) of $\mathrm{IsRep}^{\rm pre}_k$
with $\kappa_+=\frac32\kappa$ and $B_{\rm st}$ (D-III.4) and its (D2) with $\frac12\beta_k^{-m-1}$ for $\mathcal R^{(k)}_m$ (Theorem III.10.8 (c)); (S5) and the $h$-dependence of kernels (D-III.6); $\mathfrak A$ = all admissible histories (D-III.8); kept kernels on
$I''\subset I$ (D-III.9). In this version of Part III also: the text of §II.1.5 and of O-8′ now states the actual bound on $C^\natural$ ($\frac38$ of the
composed-Gaussian term, $\le1$ real, $\le C_\natural\hat\lambda_k^{2d+1}$ complex); O-3 is marked closed; the forward references to Part III are to Lemma III.10.4,
Lemma III.10.7 and Theorem III.10.8 (f).

*ARCH v4* (to be carried into v5):
1. §3.8 Step 0 and (M7): $Z_0$ with $D_0=3c_0+4$; $k_3$ with the threshold $8$ and $Z''_0$ with a $3$-neighbourhood ($D''_0$); P7's $15$ and $15M$ replaced.
2. §3.8 Step 1: P7's second bound in (2.15) is dropped; (2.15′) is per unit of new volume and paid by the refund.
3. §3.8 Step 2: the decompositions are binary (D-III.2); five kept labels with $C_{\rm dec}=5$; no subset entropy.
4. §3.8 Step 3: Lemma CH with the chain graph of Definition III.4.1 (R3-03 (ii) holds automatically), $\hat W_k\le C_{\hat W}\hat\lambda_k^{w_0-2}$; the admissibility of
   $(\delta_j)$ needs the running $\lambda\ge12p_0$ ((Λ20)).
5. §3.8 (2.53)–(2.58): **new finding** — the field renormalizations $z_j$ shift the mean of the composed window Gaussian; the actual composition is
   Lemma III.1.6 and the remainder $C^\natural$ is controlled by the top-scale weighting of the coefficient errors and the deep-layer volume fractions.
6. §3.8 Step 6: $C_W=C_b$, $C'_W=C_bB_0+C_{15}$, $L_{\rm res}=C_R\hat\lambda_k^{2d+1}$, $p_R=2p_0-2w_0$, explicit $A'_3$.
7. Lemma L: local sets only (V4-01); P7's constant $10MR_{k_1}\delta_{k_1}$ in (3.11) is kept.
8. (M4): the two-chart sections $R_\pm$, gluing by the identity theorem, Lemma III.9.5 for the complex rotation of the core, requirement (S5).
9. (M6), §8.3: removed clusters and the clique lemma; $\mathfrak A$ complete; the decay margin $\kappa_+$ of the input; $B^\sharp=B_{\rm st}+1$; LF-4 with the family clause (f).
10. §5 row 7: $R_{\rm base}\ge44K_1K_6$; row 12 resolved as above.
11. §3.7: Lemma III.7.1 is also the proof of P5 Lemma 2.1 (the known gap of LF-3), with the constants of Part III.
12. D-III.10: P7's segments of length $<6M[R_{k-1}]$ are not needed (LF-1 (b)); the constants $C(c_0)$ attached to them in (M7) disappear.

*OBSERVABLES.md*: requirement 2 (coset average on the full integrand, joint covariance in $(\psi,h,g)$) is met by Lemma III.9.6 (a), (c); the
replacement of (L4) (O-II-9) is unchanged.

### III.O.3 The conditions on $\lambda_*$ added by Part III

For all real $x$ in the stated range (combined with Parts I–II into $\lambda_*$, §I.5.3, §II.1.3). In (Λ18), $x$ plays the role of a running $\lambda_j$
($\ge\hat\lambda_j-2\ge\lambda_*-2$); elsewhere $x$ is a value of $\hat\lambda$ (for (Λ22), (Λ23) the value $\hat\lambda_{k_1}$, using $\hat\lambda_k\le2c_*\hat\lambda_{k_1}$, Lemma III.1.2 (a)). Write
$C_{\rm crit}:=2c_0(R_{\rm base}+1)+10$ (so $\mathrm{crit}_k\le C_{\rm crit}\hat\lambda_k^2$), $\bar\delta(x)=eA_0x^{p_0}e^{-x/2}$ (Lemma II.1.2 (c)), and use $\beta^{-1}\le a\,e^{1-x}$ for $x=\hat\lambda_0$.

| | Condition | Used in |
|---|---|---|
| (Λ18) | $R_{\rm base}(x+\theta+1)^2+1\le\frac98(R_{\rm base}x^2-1)$ and $2c_0\big(R_{\rm base}(4x+4)+2\big)+11\le R_{\rm base}x^2$, for $x\ge\lambda_*-2$ | Lemma III.3.2 ($[R_j]\le\frac98[R_{j-1}]$, $\mathrm{crit}_j\le(2c_0+1)[R_j]$), Lemma III.5.0 |
| (Λ19) | $C_{19}\,x^{2p_0+2d}e^{-(x-1)/2}\le1$ for $x\ge\lambda_*$, where $C_{19}:=\sqrt a\,C_P\max\big\{\frac{24c_\xi}{1-q},\ 32C_\varsigma^2(MC_{\rm crit})^d,\ \frac{108K_1^2K_6^2A_0^2c_\xi}{a(1-q)}(MC_{\rm crit})^d,\ \frac{96K_1K_6A_0C_\vartheta}{\alpha_0},\ 48C_\varsigma^2(MC_{\rm crit})^d,\ \frac{48Nc_\xi}{1-q}(MC_{\rm crit})^d\big\}$ and $C_P:=\sup_k(1+k\theta)^{2p_0+2d}L^{-k\gamma}$ (each entry of the max bounds one of the listed quantities after $\beta^{-1}\le\beta^{-1/2}\le\sqrt a\,e^{-(x-1)/2}$, $\mathrm{crit}_k\le C_{\rm crit}\hat\lambda_k^2$ and $\hat\lambda_k^pL^{-k\gamma}\le C_P\hat\lambda_0^p$, $p\le2p_0+2d$) | $\eta_k\le\frac12$; last term of (2.17′) $\le1$; the four terms of $C^\natural_0$ in Lemma III.6.3 $\le\frac14$ each |
| (Λ20) | $\lambda_*\ge\max\{12p_0+2,\ 4c_*p_0\}$ | Lemma III.4.5 (running $\lambda_i\ge12p_0$), §III.5.3; the second bound makes $\bar\delta$ decreasing at $\hat\lambda_k/(2c_*)$ ((Λ25)(c)) |
| (Λ21) | $\overline{\mathrm{crit}}(x)\ge3dK_6+4K_1K_6+3d$ for $x\ge\lambda_*$ | Lemma III.4.6 ($\hat W_k\ge4(LM\mathrm{crit}_k)^d$ exceeds $3dK_6M\mathrm{crit}_k+4K_1K_6$ and $3d(2[R_{k_1-1}]+4)M$, as $c_0\ge6$) |
| (Λ22) | $C_{23}C_{\hat W}(2c_*)^{w_0-2}x^{w_0-2}\bar\delta(x)\le c'_6$ for $x\ge\lambda_*$ | Lemma III.4.7, Lemma III.9.6 (analyticity domain of BG Prop 5.1) |
| (Λ23) | $6K_1e^{\epsilon}\big(3d^2LMC_{\rm crit}(2c_*x)^2+C_{2.20}\big)e^{-x/(3\alpha)}\le1$ and $(K_2+1)(4K_1K_6+3dD_0K_6+C_{2.20})e^{\epsilon}e^{-x/(3\alpha)}\le\frac12-(K_2+1)\frac{A_1}{A_0}$ for $x\ge\lambda_*$ (the right side is positive by $A_0=4K_2B_5A_1$, row 9, with $K_2,B_5\ge1$) | Lemma III.5.3 (c), Lemma III.7.1 Case B ($L^{-n_1/3}<e^{-\hat\lambda_{k_1}/(3\alpha)}$ by (III.1.1)) |
| (Λ24) | $x\ge4$ and $2A'_3x^{p_R}\ge3+\log5$ for $x\ge\lambda_*$ | (III.5.1) |
| (Λ25) | the following, each a polynomial in $x$ times $e^{-cx}$ or $e^{-cx^2}$ or $e^{-cx^{p_2}}$, $\le$ a constant of rows 0–15, for $x\ge\lambda_*$: (a) Lemma III.6.4 (a): $C'(2c_*x)^{p_2+2d}\alpha_0^2(ae^{2-x})^{1+2/\alpha}<1$; (b) Lemma III.6.4 (b) real and complex: $CA_0^3\bar\nu(x)C_{\hat W}^2x^{2w_0-4}(LMC_{\rm crit}x^2)^dx^{3p_0}\sqrt ae^{-(x-2)/2}<\frac14$; (c) Lemma III.6.4 (c): the surface factor $e^{-\gamma_w(M([R_{\rm base}(x-2)^2]-1)-2M_1)}$ times its polynomial $<\frac14$ and $2e^{2\epsilon}C(MC_{\rm crit}x^2)^dC_{\hat W}x^{w_0-2}\bar\delta(x/(2c_*))<\frac14$; (d) Lemma III.7.1 (2.65)–(2.67): $56C_{\chi'}B_6K_1^2K_2K_5K_6\alpha_0^{-1/2}\gamma^{-1}ae^{1-x}\le\frac18$, $C_{\chi'}:=\max\{1,3(d+2)/4\}$; (e) Lemma III.9.5: $4C_{\rm rot}C_{\rm S5}(MC_{\rm crit}x^2)^de^{2-x}\le\frac12$ and $2C\,\overline{b}(x)e^{2-x}\le\frac12$, $\overline b$ the polynomial bound of (S0); (f) Lemma III.9.6: $C'x^{a_{17}}\big((\frac{x+\theta}{\alpha\log L}+2)e^{2-x}+\sum_j\varepsilon_j\beta_j^{-1/2}\big)\le e^{-(x-2)/4}$ ($n_1<1+n_q(k_1+1)$, Lemma I.4.9 (b)) and $6e^{-(x-2)/4}\le1$; (g) Lemma III.10.5: $\frac14A_2x^{p_2}(C_{\rm crit}x^2+4\bar\omega(x)+1)^{-d}\ge B_{\rm cpl}e^{B_{\rm cpl}}e^{\kappa'c}K'_0+\kappa'(c^{\rm PE}_2+c)+c^{\rm PE}_1+3+d\log(Cx^2)$ and $6c^{\rm PE}_1K_0e^{c^{\rm PE}_1+\kappa c}e^{-\frac14A_2x^{p_2}}\le a^{m+1}e^{-(m+1)x}$; (h) $e^{x-2}/a\ge2$ (so $\beta_k\ge2$) | Lemmas III.6.4, III.7.1, III.9.5, III.9.6, III.10.5, Theorem III.10.8 |

| (Λ25-op) [v1.3: P3-05] | Conditional on the finite graph and norm constants of (H-op), put $t_x:=\frac12a^{m+1}e^{-(m+1)x}$, $p(x):=\frac14A_2x^{p_2}$, $h(x):=p(x)(C_{\rm crit}x^2+4\bar\omega(x)+1)^{-d}$, and $q_x:=(2d)^2 2^{2d+1}e^{-(\kappa_+-2-\kappa-t_x)}$. Require $t_x\le1$, $q_x\le\frac12$, $\frac{3e^{-p(x)}2^{2d+1}e^{-(\kappa_+-2-\kappa-t_x)}}{1-q_x}\le t_x$, and $h(x)\ge B_{\rm cpl}e^{B_{\rm cpl}}e^{\kappa_+c}K_{0g}+\kappa_+(c_2+c)+4+\log K_{0h}$. Row 5 makes the $q_x$ bound possible, and $p_2>2d$ makes the last two eventual. | Lemma III.10.5, when the nonnumeric (H-op) hypotheses are supplied |

Each condition compares a fixed constant with a function tending to $0$ or $\infty$, so $\lambda^{\rm III}_*$ exists. (Λ25)(g) contains $B_{\rm cpl}=2B_{\rm st}+B'$ and the
PE constants, which are fixed before $\lambda_*$; it is the only place where a non-small constant of the cluster expansion enters, and it is absorbed
by $\lambda_*$ (this is why $B^\sharp$ does not contain $B_{\rm cpl}$). $\lambda_*$ is chosen after rows 0–15, as in §I.1.3.

### III.O.4 Open items (Parts I–III together)

- **O-1 (Timár's lemma, Lean).** **Closed**: `exteriorBoundary_starConn` (`LargeField/Geometry/Timar.lean`) and Lemma S on the torus (W37) are landed without
  `sorry`.
- **O-2′ (analytic half of Lemma F and the background changes).** Open (Part IV.1). Part III uses the same inputs twice more: Lemma III.2.2 (P6 (2.31) and
  the replacement of the step backgrounds by $\phi_{k_1,k}$) and the re-expansion (3.20)–(3.25) of §III.10.3. Conditional on LOC's open items.
- **O-3.** **Closed** (Lemma III.9.1).
- **O-5 ($\pi'$ offsets; adjacency in P5 (1.33)).** Open; enters Part III only through the constant $K_0$ of PE in Lemma III.10.5 and the conversion of PE
  §3.6 (G1)–(G3) between Steiner size and $d_k^{\rm cov}(X\,\mathrm{mod}\,\Omega^c_k)$.
- **O-6 (base rule at $k=0$).** Unchanged (Part IV).
- **O-8′.** **Closed** (Lemmas III.1.6, III.1.7, III.1.7′, III.6.3).
- **O-9, O-10.** Unchanged.
- **O-II-2 (Def-6, R-ν), O-II-3 (errata candidates), O-II-8 (row 3), O-II-9 (OBSERVABLES (L4)), O-II-10 (switch at $k_0$).** Unchanged. Part III adds no
  condition on $L$ beyond $L\ge3$.
- **O-II-4 (constants of the small-field step).** $C_b$, $C_{\psi'}$, $C_{15}$ and $B_{\rm st}$ are outputs of LF-3/LOC (rows 0–11); see O-III-1.
- **O-II-5.** **Closed** (Theorem III.8.9, Lemma III.9.6).
- **O-II-6 (IsRepFam).** LF-4 preserves it (Theorem III.10.8 (f)); LF-3 must (Part IV).
- **O-II-7 (torus coherence).** LF-4's data are local and defined on $\mathbb Z^d$ (proof of Theorem III.10.8, (D8)); LF-3 open.
- **O-III-1 (obligations on LF-3, Part IV.1).** (i) The boundary terms produced by the step satisfy (D7) with the decay $\kappa_+=\frac32\kappa$ (P5 Theorem 1, p. 499)
  and a constant $B_{\rm st}$ that does not depend on $B_0,H_0,c_1,c_2$ (P6 p. 15); this is what makes row 12 acyclic. (ii) The kernels of non-quiet steps have the
  rotation form (S5). (iii) $\mathrm{IsRepFam}$ is preserved. (iv) $C_b$, $C_{15}$ are outputs of rows 0–11. (v) $\mathcal R^{(k)}_m$ satisfies H4 with $\frac12\beta_k^{-m-1}$ (P5
  Proposition 3.2), so that $R$ can add $\mathcal R''^{(k)}_m$ (Theorem III.10.8 (c)).
- **O-III-2 (cited analytic inputs of Part III).** To be proved in Part IV or in Lean: P7 Lemma 2.1 with $c_{D_0}$ (Lemma III.3.3), Lemma 2.2 (Lemma III.6.2),
  Lemma 2.4 with P3 Proposition 2.1 (Lemma III.4.7), P4 (4.11)–(4.12) (Lemma III.7.1), the denominator (3.3)–(3.5) (Lemma III.8.2), P2 Proposition 3.1 in the
  form (3.12)–(3.14) (Lemma III.9.6). All of them concern a single box of bounded size or the background perturbation theory of BG/LOC.
- **O-III-3 (operator-valued gas).** GAS and PE with a hole for weights that are integral operators (Lean P10). On paper this is a direct transcription of
  POLYMER §2.6 with sup norms; it should be checked by the audit of Part III.
- **O-III-4 (reading of P7 (2.61)).** The set $D''$ of $\chi''$ (Definition III.5.1 item 4), UNCERTAIN (minor); only the constant of Lemma III.9.1 (c) depends on it.
- **O-III-5 (errata candidates for `notes/ERRATA.md`).** N-III-1: P7's $Z''_0$ (cubes meeting $Z_{k_3}$, threshold $1$) does not keep $\square^{\sim3}$ away from $Z_0$
  (Lemma III.5.0); the repair changes $R_0\ge6K_1K_6$ to $44K_1K_6$. N-III-2: P7 pp. 499–510 compose the window transformations as if $z_j\equiv1$; the field
  renormalizations shift the composed mean (Lemma III.1.6). N-III-3: P7 (3.26) does not say which families of removed components occur with a given
  kept region; joint admissibility is not pairwise (§III.10.1). N-III-4: P7 p. 521 does not treat the effect of a complex (non-real) rotation on the core
  operator (Lemma III.9.5). N-III-5: P7 (2.15)'s second bound depends on one piece per window (not an erratum of P7; recorded for ARCH).


---
---

# Large-field reconstruction document, §II.7 and Part IV: the base case, the flow, the end, and the assembly

Version 1, 2026-10-12. Brief: `orchestration/briefs/D-LFR-partIV.md`. Input: Parts I–III above (commit d9e499e), ARCH v4 §1.2–§1.4,
§3.7 (LF-3, LF-5, LF-6, LF-7, LF-8), §8, §9; `SMALLFIELD.md` v2 (**SF**: Def-6, I-7, I-9, Theorem 5.3 with the (F1) clause, §5.5);
`CHECKS1-astra.md` (**CHK**: §2, R-ν); `OBSERVABLES.md` (**OBS**) and `OBSERVABLES-review.md` (**OBSR**); `CORRELATIONS.md` (**CORR**) §§1–2;
`POLYMER.md` (**PE**) §§2–4; the Lean interface `Balaban/Correlations/C1Star.lean` (`C1Star`, `C1StarF1`–`F3`, `RootFAndC1Star`, after W34) and
`Balaban/Correlations/Clauses.lean` (`RootFClauses`); the frozen Root-F `Balaban/Frozen/Roots/LogPartitionMultiscale.lean` and the frozen
model `Balaban/Frozen/Model/*.lean`. The text layers of P5, P6, P7, P9 were re-read for this Part at the pages cited ([checked]); P4 is a scan and
its pages 691–694 (the first step) and 719–720 (the last step) were read in the OCR layer only ([review]). Tags, status words and the UNCERTAIN
convention are those of Parts I–III. Status: draft for independent review; nothing here is approved or frozen.

**Placement.** §II.7 belongs to Part II (it completes Def-7's interfaces at $k=0$); it was written after Part III, as ARCH §9 plans, and is placed
here, after §IV.0, because it uses the decisions D-IV.1–D-IV.4 and D-IV.11 below. Part II carries a pointer to it.

**Purpose.** This Part closes the large-field reconstruction. §II.7 constructs the first step $\rho_0\mapsto\rho_1$ for hard spins (LF-6, open item O-6).
§IV.1 states and proves LF-3 (one full step for $1\le k<k_0$) with the obligations O-III-1 of Part III; §IV.2 LF-5 (the transfer at $k_0$, the switch
to complete backgrounds, the frozen regime); §IV.3 LF-7 (the flow, its normalization and its continuity in $\nu$); §IV.4 LF-8 (the last step, the case
$k_f=0$, and the one- and two-point functions with the massive final covariance); §IV.5 the assembly of Root-F exactly as frozen and of
`RootFAndC1Star` exactly as in Lean, with a clause-by-clause table of sources and the list of remaining cited inputs. §IV.L lists the Lean
declarations and §IV.O the status, the changes to Parts I–III, the new conditions on $\lambda_*$ and the open items.

## IV.0 Setting, design decisions, summary

### IV.0.1 Standing assumptions

- **(A-IV.1)** $d\ge3$, $N\ge2$; the constants of the prefix §I.1.4 (with the amendments of §IV.O.2) are fixed up to row 15; $\lambda_*$ satisfies the
  conditions of §I.5.3, §II.1.3, §III.O.3 and §IV.O.3; $\beta\ge\beta_0:=\max\{e^{\lambda_*-1}/a,\,2B\}$ (row 16 as amended, D-IV.10).
- **(A-IV.2)** $\nu\in(0,1]$, $h\in S^{N-1}$. The running constants are those of the flow (§IV.3). The regime index is the a priori
  $k_0:=\max\{k\ge0:\beta\nu L^{kd}\le1\}$ (*genuine* if $\beta\nu\le1$), read as $0$ (*conventional*) if $\beta\nu>1$ (D-IV.11); $k_f$ is the first $k$ with $\nu_k>\frac78L^{-2}$;
  $\hat k_f=\min\{k:\nu L^{2k+2}\ge1\}$ (I.1). By Lemmas I.5.6 and IV.3.3, $k_f\le\hat k_f\le k_f+1$ when $k_f\ge1$, $k_0<k_f$, $\beta_k\nu_k\le e^{2\epsilon}$ for $k\le k_0$ and
  $\beta_k\nu_k>e^{-2\epsilon}$ for $k>k_0$.
- **(A-IV.3)** *Admissible tori* are the tori $\mathbb T_\ell=(\mathbb Z/\ell\mathbb Z)^d$ with $ML^{\hat k_f+1}\mid\ell$ (D-IV.1). Everything below is done on each
  admissible torus; families over admissible tori are coherent in the sense of (D8) (version 1.2, D-IV.9).

Notation. The running coefficient at scale $0$ is $\beta$ itself; it is never written $\beta_0$, which denotes the threshold of (A-IV.1). Likewise
$\delta_0:=(\beta a)^{-1/2}p_0(\beta)$, $p_j(\beta):=A_j(\log\beta a)^{p_0}$ ($j=0,1$; P5 p. 498 [checked]). The fine torus has spacing $1$; $\pi_j$-cubes have
side $ML^j$ (Part II conventions). $\sigma$ is the surface measure `(volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere` on $S^{N-1}$ (total mass
$|S^{N-1}|=Nv_N$, Mathlib `Measure.toSphere_apply_univ`), and $\sigma^{\otimes}$ the frozen `aprioriMeasure`.

### IV.0.2 Design decisions

Each decision is explained where it is used; D-IV.1–D-IV.4, D-IV.8, D-IV.9 and D-IV.11 change Parts I–III in details (listed in §IV.O.2), the others make the sources precise.

**D-IV.1 (admissible tori and the scale $k_f$ of Root-F).** The flow is run on the tori with $ML^{\hat k_f+1}\mid\ell$, and Root-F's integer `kf` is
$\hat k_f$, not the flow's last scale $k_f$. Reasons: (i) $\hat k_f$ is a function of $\nu$ alone, so the set of tori is known before the flow is run
(causality, ARCH R3-06); Part I's Def. I.2.0 used $ML^{k_f+1}\mid\ell$, which depends on the running $\nu_k$; (ii) Root-F asks the identity on *every*
torus with $ML^{\mathrm{kf}+1}\mid\ell$, and with $\mathrm{kf}=\hat k_f\ge k_f$ these are exactly the tori on which the flow is run; (iii) $\hat k_f$ satisfies Root-F's two
bounds (Lemma IV.5.1). The flow still stops at $k_f$; its terms of scale $j\in(k_f+1,\hat k_f+1]$ are $0$. `C1Star`'s last scale is $J:=k_f+1$ (Lemma IV.5.1 (c)).
Lemma I.5.6 (c) holds a fortiori ($n_k\ge L^{\hat k_f+1-k}\ge L^{k_f+1-k}$).

**D-IV.2 (a priori region radii).** In the flow the region rules of Definition I.3.1, the thick neighbourhoods $X^{\approx}$ of P5 (1.2) and P7's late
scales $k_2,k_3$ (Definition III.3.1) use the a priori radii $\hat R_j=R_{\rm base}\hat\lambda_j^2$ in place of the running $R_j=R_{\rm base}\lambda_j^2$. The running
$\lambda_j$ enter only analytic objects (thresholds $\delta_j$, $p_0(\beta_j)$, $\varepsilon_j$, the couplings $\beta_j,\nu_j$). Reasons: (i) the radius hypotheses (RH) of §I.3.1
hold with equality. [v1.3: P4-09] A numerical estimate $|F|\le Ce^{-R^{\rm run}_j}$ does **not** imply $|F|\le Ce^{-\hat R_j}$; every separation-dependent analytic estimate must be established again on the geometry with the chosen $\hat R_j$. The pass immediately below records the needed estimates and constants. Size estimates instead use the upper bound $R^{\rm run}_j\le\hat R_j$. (ii) The integer parts $[R_j]$ of the running
radii are step functions of $\nu$, so with running radii the set of admissible histories changes with $\nu$ and (F-ii) of Definition II.6.4 is false; with
$\hat R_j$ the region histories at scales $\le k$ do not depend on $\nu$. This is the reading of ARCH R3-06 already used in §III.0.1 ("all bookkeeping
(radii, widths, …) uses $\hat\lambda$"); Part I's flow specialization and Definition II.1.1 said "running", and are corrected (§IV.O.2).

[v1.3: P4-09] **Source-estimate pass after D-IV.2.** In the table, “chosen” means a geometric separation to be supplied by the actual region construction, so the proof must start with $\hat R_j$. “Running” means a coefficient or a small-field threshold computed from $\beta_j,\nu_j$; it is never enlarged by changing the collar. Write $D_j:=M([\hat R_j]-1)-2M_1$ and $\gamma_w:=\gamma_0/4$. LOC I-4a/b gives response $C_{\rm BG}\delta_j e^{-\gamma_wD_j}$ when the data change vanishes on the $\hat R_j$ collar. The integer loss of one cube and $2M_1$ is retained. No line below infers stronger exponential decay from an old bound with $R_j^{\rm run}$.

| Source estimate consumed here | Role of its $R_j$ and rerun with $\hat R_j$ | Constant or residual obligation |
|---|---|---|
| P5 (1.2), (2.3), (2.14), (2.43)–(2.45); P6 (2.1), (2.3); P7 (2.1)–(2.3) | Chosen separation. Lemmas I.3.5(f), II.2.5(c) prove the new collar and disjointness directly with $[\hat R_j]$; Lemma III.3.2 bounds its upper size by $C_{\rm crit}\hat\lambda_j^2$. | Exact margins $([\hat R_j]+4)LM$ and $D_j$; no analytic inference. |
| P5 (2.34), (2.41), (3.9) determinant and marked terms; P5 Propositions 3.1–3.4 | The determinant difference uses the chosen collar, while $\beta_j^{-m-2}$ is a running coefficient bound. Reapply LOC I-4c and V3 with $D_j$, use $C_{\rm sqrt}e^{-\gamma_wD_j}\le e^{-\hat R_j}$ from (Λ29), then FLUCTUATION Theorem 3.1(d) and §3.5(d) to all terms, including whole-torus terms. | $C_{\rm PE}K_0\beta_j^{-m-2}$ for the marked terms, $\beta_j^{-m-3}$ for the determinant, under (Λ29). Conditional on LOC and FLUCTUATION (Vmod). |
| P6 (2.12)–(2.17), (2.13)–(2.14) | Chosen collar. For the local backgrounds the distance is $D_j$, not $2M\hat R_j$; FLUCTUATION Theorem 4.2 applies the weighted LOC response to the data change zero on $E_{Z'}$ and localizes its first variation. | $C_FA_0^2\hat\lambda_j^{2p_0}e^{-\gamma_wD_j}$, reduced to $e^{-\hat R_j/2}$ by (Λ28′); rate $2\kappa-1-\kappa_0\ge\kappa_+$. |
| P6 (2.18)–(2.29), Propositions 2.1–2.3, and P5 (3.2), (3.8)–(3.11) | Chosen localization cover; the polynomial powers of $\beta_j$ are running. Reapply FLUCTUATION Theorem 3.1(c)–(f), Corollary 4.3, with $\mathbb B^\sharp_{j+1}$ and $D_j$. | Constants $C_f,E_0,B_{\rm st}$ of rows 0–11. Auxiliary-cover admissibility and (Vmod) remain cited inputs. |
| P7 (2.10)–(2.17), P6 (2.31); LFR III.2.2 | Chosen separation in the background replacement; the RG coefficient variation is running. Use the $\hat R_{j-1}$ collar and weighted response, then the same localization of the difference. | At most $C_{\rm win}e^{-\gamma_wD_{j-1}}|X_j|_{j+1}$, with $C_{\rm win}$ fixed before $\lambda_*$. The localization of P7's window action is still a cited input; the stronger printed $e^{-\hat R_{j-1}}$ needs its own threshold and is not assumed here. |
| P7 (2.22)–(2.30), (2.41), (2.49), (2.59)–(2.60); LFR III.4, III.6 | Chain distances and collars are chosen; $\delta_j,\varepsilon_j,\beta_j\nu_j$ are running. Lemma III.4.7 uses $\hat W_k$ and LOC response at the actual distance. Lemma III.6.4 pays the response at $e^{-\gamma_wD_j}$ and the running factor $e^{2\epsilon}$. | Constants $C_{23},C_{24},C_{\hat W}$ and the strengthened (Λ25)(a)–(c); $e^{-\hat R_j}$ is not substituted for a weaker established bound. |
| P2 Proposition 3.1 and P3 Proposition 2.1; P7 Lemmas 2.1, 2.2, 2.4 | P2's existence and the $D_0$ core domain are fixed local inputs. P3's response and P7 Lemma 2.4 use the chosen separation of the window data: apply the weighted response at its actual $\hat R$ collar and the size bound $\hat W_k$ of Lemma III.4.7. | Constants $K_2,C_{\rm BG},C_{23},C_{24},C_{\hat W}$; the P3/LOC response on this generating set remains a cited input. |
| P4 (4.11)–(4.12), P7 (2.65)–(2.67) | P4's coefficient variation is running (the $\varepsilon_j$ and renormalization constants); its background comparison is performed on a chosen local box. Reuse P4's $7K_2\varepsilon_{j+1}$ bound on the local domain, then pay the data replacement at the actual chosen distance in Lemma III.7.1. | The P4 (4.11)–(4.12) formula is checked on the PDF p. 702; (Λ25)(d) pays the running factor. The chosen-distance replacement retains the P3/LOC input of the preceding row. |
| P7 (3.3)–(3.5), (3.11)–(3.19); LFR III.8.2, III.9.5–III.9.6 | The denominator uses a fixed $D_0$ box and running $\beta_k,\nu_k$, not a separation radius. The chart uses chosen collars only through the preceding window bounds. | $C_{\tilde E}D_0^d$ with the $e^{2\epsilon}$ mass factor; the core majorant is Lemma III.9.5. |
| P7 (3.20)–(3.25), (3.27)–(3.29); LFR III.10 | The background re-expansion sees the chosen distance of a removed component from the retained region; the gas summability uses $\hat\lambda_k$ and $\hat R_k$ for object sizes. | The $O(e^{-\gamma_wD_k})$ background contribution and $B'$ remain conditional on the cited P7 re-expansion and LOC inputs; GAS itself is the landed operator theorem. |
| P7 (4.1)–(4.9) and P9 (4.7)–(4.9) | Final-step covariance and $\beta_{k_f},\nu_{k_f}$ are running analytic data. No source $R_j$ is used as a fresh separation in the last Gaussian integral. | The frozen threshold is $p_2(\beta_{k_0})$ (Lemma IV.4.2); observable estimates remain the cited input. |

**D-IV.3 ((S1)–(S2) with Gaussian witness factors; Part II version 1.2).** The Gaussian factorization (S1) of Definition II.5.7 (version 1.1) asked
that the step kernel be $\prod_y z^N_{k+1}t_k(z_{k+1}\psi_{k+1}(y),(Q\psi_k)(y))$ times a factor independent of $\psi_{k+1}\restriction_{\Omega^c_{k+1}}$. This is false for every
non-quiet step with $\mathsf P_{k+1}\ne\varnothing$: the factor $\chi'^{(k)c}(\mathsf P_{k+1})\chi'^{(k)}(\mathsf P^c\cap\Omega'\cap\Omega^c)$ of P5 (2.47) [checked, p. 512] reads $\theta=z_{k+1}\psi_{k+1}$ on
$\Omega^c_{k+1}$, and it is exactly where the gain of the $\mathsf P$-cubes comes from (P6 (3.4) [checked, p. 16]: "we estimate the Gaussian integrations in
(2.47)"). The repair keeps the composition argument of Lemma II.5.13: the extra factor depends on $\psi_{k+1}\restriction_{\Omega^c}$ only through the
*differences* $u_y:=z_{k+1}\psi_{k+1}(y)-(Q\psi_k)(y)$, and its Gaussian measure is a number. (S1), (S2) and step (1) of the proof of Lemma II.5.13 are
restated in place (§IV.O.2 item 3); the restated form is used in §II.7 and §IV.1.

**D-IV.4 (scale-$0$ variables; the sphere chart).** The scale-$0$ large-field variables are spins ($S^{N-1}$-valued, reference measure $\sigma$); the
scale-$0$ fluctuation variables are $\psi'_0\in\mathbb R^N$, defined on the small-field sites by the sphere chart around the background, the representation of
the tangent integral by an integral over $\mathbb R^N$ (Lemma II.7.4) and the localized covariance (P5 (2.39) at $k=0$). On the large-field sites no change of
variables is made. This fixes the convention announced in Definition II.5.1.

**D-IV.5 (the switch at $k_0$).** The step $k_0\to k_0+1$ is written as P6 p. 11 [checked] suggests: (i) the unrenormalized backgrounds of the step are
$\nu$-free (they are built from the data of scale $k_0$, where $\mu_{k_0}=0$); (ii) the renormalized backgrounds of scale $k_0+1$ are complete (mass $\mu_{k_0+1}>0$),
and the difference is the explicit term $f_0=\nu_{k+1}(\phi_{k+1}-h)$-type source of P6 (2.24) [checked, p. 10], of order $\beta_{k_0+1}^{-1}$ because
$\beta_{k_0+1}\nu_{k_0+1}\le e^{2\epsilon}L^d$ (D-IV.11; P5 p. 490 [checked] has $<\frac98L^d$ for its running index). The RG system of this step is P4's full-background system with data perturbed at zeroth and first order
by $O(\nu_{k_0+1})=O(\beta^{-1}_{k_0+1})$ (P6 p. 11: "these contributions are very small ... and they do not change anything in the analysis of Sect. 5 [4]").

[v1.3: P4-05, switch] Use the author-accepted two-step switch of FLUCTUATION Lemma 2.9. First change from the unrenormalized mass-free background $\phi^0$ to the complete background $\phi^\nu$, and add the exact quadratic switching term $-\frac12\beta_{k+1,u}\langle\phi^0-\phi^\nu,(H^\nu+\alpha^\nu)(\phi^0-\phi^\nu)\rangle$ and the differences of the old $\mathscr E,\mathscr F$ compositions to the zeroth-order data. Then solve the ordinary complete-background RG system with its matrixInfty. Lemma 2.9 bounds every localized switching term by $C_{\rm sw}\beta_{k+1}^{-1}e^{-(2\kappa-1)d^{\rm cov}_{k+1}}$, $C_{\rm sw}=C(d,L,N,\kappa_1)L^{2d}$; it changes the data bound by the factor $1+C_{\rm sw}L^{2d}\beta^{-1}$. There is no perturbed matrix and no (L1′) hypothesis.

**D-IV.6 (the last covariance is massive).** At the last step the covariance of the final fluctuation integral is $A_{k_f}^{-1}$ (no coarse coupling $aL^{-2}Q^*Q$;
P7 p. 530 [checked]: "the basic quadratic form is 'massive'"; P9 p. 515 [checked]), and the final generating function contains the tail
$(\beta\gamma_{k_f})^{-1}P_{k_f+1}A^{-1}_{k_f+1}P^\top_{k_f+1}$ (OBSR Q2). In `C1Star` this tail is part of the remainder $r_{tr}$, bounded by the term
$c_*\nu^{(d-2)/2}e^{-c'\sqrt\nu|z|}$ that W34 added to `C1StarF3`.

**D-IV.7 (the terms $T_j$ of Root-F).** $T_j(x,X;g)$ collects, for $1\le j\le k_f$, the localized terms $\mathcal M^{(j)}(x,X;h,h,g)$ of P4 (H.7) at the
constant configuration, and for $j=k_f+1$ the last-step terms $\mathcal M^{(k_f+1)}_n$, $0\le n\le m$, of P7 (4.17) together with the $g$-increments of the
polymer terms $\mathcal R^{(k_f+1)}_n(Y)$, $\mathcal P^{(k_f+1)}(Y)$ written by the device $f(g)-f(0)=\sum_{x}\langle g(x),\int_0^1\partial_{g(x)}f(tg)\,dt\rangle$ (ARCH (F3), PE §4.4).
The flow is run with the decay rate $\kappa_{\rm flow}:=\max\{C_{d,L}(\kappa+1)+C'_{d,L},\,16\kappa_0+16,\ 2(4+\log(2(2d)^2 2^{2d+1}))\}$, where $C_{d,L}$ is the conversion constant between
tree length and block count (FLUCTUATION Lemma 1.2 (G1), and PE §3.6: $d_j^{\rm cov}(X)\ge|X|_\#/C_{d,L}-1$, with [v1.3: constant b] $C_{d,L}=3^{d+1}L^{2d+1}$) and $C'_{d,L}:=C_{\rm loss}+C_{d,L}L^d\log2$ pays the rate lost in the last
step and the entropy of the regrouping of scale-$k_f$ polymers into scale-$(k_f+1)$ polymers (Definition IV.5.2, Theorem IV.5.3 item 5); Part I row 5 wrote $C_d(\kappa+1)$, which omits the $L$-dependence. Root-F's
$\delta$ is $\gamma/2$ with $\gamma:=\frac14$, and row 10 requires $\alpha_1\le\gamma/2$, so that $\gamma-\alpha_1\ge\delta$.

**D-IV.8 (the family class on the $\mathbb Z^d$ data).** The continuity class $\mathrm{IsRepFam}_k$ (Definition II.6.4) is restated on the torus-coherent
$\mathbb Z^d$ data (Definition IV.3.1): for fixed $k$ the admissible tori of $\nu$ shrink as $\nu\downarrow0$ ($ML^{\hat k_f(\nu)+1}\mid\ell$ with $\hat k_f(\nu)\to\infty$), so no
torus carries the whole family, and the limits used by `C1Star` are limits of $\mathbb Z^d$ objects (OBS Lemma 5.4). The clause is also weakened in a
second point: only the limit as $\nu\downarrow0$ is required, almost everywhere for each limit point separately. The version-1.1 wording ("for almost every
value of the variables it is a continuous function of $\nu\in(0,\nu_*]$") is false for indicator functions with $\nu$-dependent thresholds: for a fixed
configuration, $\nu\mapsto\mathbf 1[f<\delta_j(\nu)]$ jumps where $\delta_j(\nu)=f$.

**D-IV.9 ((D8) on Root-F's box).** (D8) of Definition II.6.2 is restated for supports contained in the image of a box $\{y\in\mathbb Z^d:|y_\mu-c_\mu|<\ell/4\}$, which has
side $<\ell/2$; version 1.1 had "a cube of side $<\ell/4$", which does not reach Root-F's agreement clause (sets in $\{|y_\mu|<\min(\ell,\ell')/4\}$). The
proof is unchanged: the map $\{|y_\mu-c_\mu|<\ell/4\}\to\mathbb T_\ell$ is injective and preserves nearest-neighbour adjacency and the sup-distance (two of its points
differ by less than $\ell/2$ in each coordinate), so every localized construction inside the image is the push-forward of the same construction in $\mathbb Z^d$.

**D-IV.10 (two constants of the prefix).** Row 13 adds $H_0\ge2L^d(C'_E+1)$, where $|E_k|\le C'_E\lambda_k+C'_E$ per $k$-block (P7 p. 520 [checked]); it is used for the volume
weights of the last step (P7 (4.12) [checked]; Lemma IV.4.2, where the weight per $k_f$-block is $L^{-d}H^{\rm fin}_{k_f+1}$). Row 16 reads $\beta_0:=\max\{e^{\lambda_*-1}/a,2B\}$, so that $\beta_k=\beta L^{k(d-2)}\gamma_k>BL^{k(d-2)}$ ((D9)) follows from
$\gamma_k\ge e^{-1/20}$.

**D-IV.11 (the regime index $k_0$ is a priori).** P5 p. 490 [checked] defines $k_0$ as the index with $\beta_k\nu_k\le1$ for $k\le k_0$ and $>1$ after, and lets it decide
three things: the background convention at each scale ($\nu$-free for $k\le k_0$), whether $R^{(k)}$ is applied, and (in the reconstruction) windows and hulls. At the step
$k\to k+1$ the convention of scale $k+1$ must be known before the RG equations of the step are solved, but $\beta_{k+1}\nu_{k+1}$ is an output of those equations, and the two
conventions give two different RG systems (CHK §2). The decision is therefore made with the a priori product $\beta\nu L^{kd}=\hat\beta_k\hat\nu_k$ (the free values of $\beta_k,\nu_k$):
$k_0:=\max\{k:\beta\nu L^{kd}\le1\}$. It is a function of $(\beta,\nu)$, computable before the flow, in the spirit of ARCH R3-06 and ruling 2 (bookkeeping on a priori data). By (I.2),
$\beta_k\nu_k=\beta\nu L^{kd}\gamma_k\delta_k$, so $\beta_k\nu_k\le e^{2\epsilon}\le\frac{11}{10}$ for $k\le k_0$ and $\beta_k\nu_k>e^{-2\epsilon}$ for $k=k_0+1$; P5's index differs from $k_0$ by at most one. Every statement of
[v1.3: P4-01] The operative hypotheses of (A-III.2), Theorem III.10.8 and LF-7 are stated with $k\le k_0$. Lemmas III.6.4 and III.8.2 show exactly where $e^{2\epsilon}$ is paid, and (Λ25) retains the needed margin; the older blanket reading is withdrawn. Lemma IV.3.3 re-derives (H-λ) and (H-T) for this $k_0$.

### IV.0.3 Summary of results

*Proved here:* the base record at $k=0$ and its geometry (Lemma II.7.2), the exact quadratic identity of the hard-spin action (Lemma II.7.3), the
sphere chart with the $\mathbb R^N$ representation (Lemma II.7.4), the spins of the small-field region lie in the chart (Lemma II.7.5), the structure
and the one-step bound of the base data with the gain $\kappa^{(0)}$ (Lemmas II.7.7–II.7.8), LF-6 given the small-field part (Theorem II.7.10); the
one-step bound for non-quiet steps from P6's small factors (Lemma IV.1.4), the independence of $B_{\rm st}$ from $B_0,H_0,c_1,c_2$ (Lemma IV.1.5), the
rotation form (S5) of non-quiet kernels (Lemma IV.1.6), LF-3 given the cited analytic inputs (Theorem IV.1.1); the transfer and the frozen
steps of LF-5 (Lemma IV.2.1, Theorem IV.2.2); LF-7 (Theorem IV.3.2); the budget of the last step (Lemma IV.4.2), LF-8 (a) given P7 §4's analytic
inputs (Theorem IV.4.1); the scale bookkeeping for Root-F and `C1Star` (Lemma IV.5.1) and the two assembly theorems IV.5.3, IV.5.4 given the inputs listed in
§IV.5.4. *Cited:* the small-field analysis of P4–P6 at every step (I-7, I-8, I-9 of SF, with the R-ν revision), the analytic half of Lemma F (O-2′), P7 §4
and P9 §4 for the last step, OBS for the observable layer, and the case $k_f=0$ (sketched, Proposition IV.4.3).

---

## II.7 LF-6: the base case (the first step $\rho_0\mapsto\rho_1$ for hard spins; open item O-6)

### II.7.1 The first transformation and the two regimes

Assume (A-IV.1)–(A-IV.3) and $k_f\ge1$ (the case $k_f=0$ is LF-8 (b), Proposition IV.4.3). The initial density is the frozen Gibbs factor with source,
$$\rho_0(\phi;h,g):=\exp\big(-\beta H(\phi)+\langle g,\phi\rangle\big),\qquad\phi\in(S^{N-1})^{\mathbb T_\ell},\qquad\int\rho_0\,d\sigma^{\otimes}=Z(g),$$
with $H$, $\sigma^{\otimes}$ and $Z$ the frozen `energy`, `aprioriMeasure` and `partitionFunction` (P1 (1.5)–(1.6) at $\lambda=\infty$, P9 (1.1)). For a scale-$1$ block $y$ write
$(Q\phi)(y):=L^{-d}\sum_{x\in B_1(y)}\phi_x$, and let $t_0$ be the Gaussian kernel of Definition II.5.6 at $k=0$ (P1 (1.11) [review]; the units of Part II). With the
field renormalization $z_1=1+\zeta_1$ of the first step (SF §3.1, P4 (4.1)),
$$(T^{(0)}\rho_0)(\theta):=\int\prod_{y\in T^{(1)}}t_0\big(\theta(y),(Q\phi)(y)\big)\,\rho_0(\phi)\,\sigma^{\otimes}(d\phi),\qquad\rho_1(\psi_1):=z_1^{N|T^{(1)}|}\,(T^{(0)}\rho_0)(z_1\psi_1),\tag{II.7.1}$$
so that $\int\rho_1\,d\psi_1=Z(g)$ by Fubini and $\int t_0(\vartheta,w)\,d\vartheta=1$. (The rescaling $S^{(0)}$ is the passage to scale-$1$ units, implicit in the fine-unit
conventions of Part II.)

Two regimes occur. **(A)** $k_0\ge1$, i.e. $\beta\nu L^d\le1$ (D-IV.11; then $\beta_1\nu_1\le e^{2\epsilon}$): the backgrounds of scale $1$ are $\nu$-free, the field term is a perturbation in
the main action (P5 p. 490 [checked]), and the target class is $\mathrm{IsRep}_1$. **(B)** $k_0=0$, i.e. $\beta\nu L^d>1$ (genuine if $\beta\nu\le1$, conventional if $\beta\nu>1$):
the step $0\to1$ is the switching step of D-IV.5, but since there is no background at scale $0$ the switch is vacuous: the backgrounds of scale $1$ are
complete from the start (P4 (2.42)–(2.48) with $\nu_0$, pp. 691–693 [review]), and the target class is $\mathrm{IsRep}^\flat_1$ with the threshold $A_2\hat\lambda_0^{p_2}$.

### II.7.2 The base rule

**Definition II.7.1 (the scale-$0$ small-field function and the base record).** For $\square'\in\pi_1$ put
$$\chi'^{(0)}(\square'):=\underbrace{\prod_{y\in T_1(\square')}\mathbf 1\big[|\theta(y)-(Q\phi)(y)|<2\delta_0\big]}_{=:\,A(\square')}\cdot\underbrace{\prod_{b\cap\square'\ne\varnothing}\mathbf 1\big[|\partial\phi(b)|<\delta_0\big]\cdot\Big(\prod_{x\in\square'}\mathbf 1\big[|\phi_x-h|<\delta_0\nu^{-1/2}\big]\Big)^{[\text{regime (B)}]}}_{=:\,B(\square')},$$
the bond product over the nearest-neighbour bonds with at least one end point in $\square'$. Sources: the block condition is P5 (2.5) at $k=0$; the bond and
site conditions are P1 (1.15) [review] and P5 p. 487 [checked] ("either $|(\partial\phi)(b)|<\beta_0^{-1/2}p_0(\beta_0)$, or $|(\partial\phi)(b)|\ge\beta_0^{-1/2}p_0(\beta_0)$ on bonds of the
lattice, etc."), with P5's $\delta_0$; the site condition is ARCH LF-6 (i) and occurs only in regime (B) (in regime (A) no characteristic function at scales
$\le k_0$ carries an $h$-condition, §II.3.1). There is no condition on $|\phi|$ (hard spins). The *base decomposition* is
$$1=\prod_{\square'\in\pi_1}\big[\chi'^{(0)}(\square')+\chi'^{(0)c}(\square')\big]=\sum_{\mathsf P_1\subset\mathbb T_1}\chi'^{(0)c}(\mathsf P_1)\,\chi'^{(0)}(\mathsf P_1^c),$$
P5 (2.6) at $k=0$ with $\Omega'_1=\mathbb T_1$. The later decompositions, with the sets $\mathsf Q_1$ (failure of $\chi'_1$, Definition II.3.2 item 3 with the mixed lift
$\mathrm{lift}_{0,1}(\phi,\theta)$, scale-$0$ variable $\psi_0:=\phi$), $\mathsf R_1$ (failure of $\chi^{(0)}$ for the fluctuation variables of D-IV.4) and $\mathsf S_1$ (failure of $\chi_1$, P6 (2.1)),
are P5 (2.14), (2.43) and P6 (2.1) at $k=0$. A *base record* is a quadruple $(\mathsf P_1,\mathsf Q_1,\mathsf R_1,\mathsf S_1)$ satisfying the constraints of Definition I.3.1 at
$k=0$ (with $Z_0=\varnothing$, $U_0=U'_0=\varnothing$, the convention of §I.3.1, and the a priori radius $\hat R_0$, D-IV.2).

**Lemma II.7.2 (the base record; Part I O-6, second half).** Assume (RH). For every base record:
(a) $\Omega'_1=\mathrm{Op}_{[\hat R_0]+2}(\varnothing)=\mathbb T_1$, the sets of Definition I.3.1 at $k=0$ are defined, and the history ($Z_0=\varnothing$; the base record) is an admissible
region history up to scale $1$;
(b) (G1) holds at $k=0$ with new seeds only: every $x\in Z^{(0)}_1$ lies in the component of some $q\in\mathcal N_1$ with $\mathrm d(x,q)\le s'r_0$;
(c) every component $Z'$ of $Z^{\rm pre}_1$ contains a new cube, so the step $0\to1$ is quiet in no component (Definition II.5.5); $Z'$ is a (T2) output with $m=0$, $r\ge1$;
in regime (A) its window state is $\mathsf{Pre}$ or $\mathsf{Active}(1,1,\varnothing)$; no component of $Z^{\rm pre}_1$ is ripe, so $Z_1=Z^{\rm pre}_1$;
(d) $\mathsf P_1^{\sim3}\subset\Omega^c_1\subset Z^{\rm pre}_1$; a bond with an end point in a cube of $\mathsf P_1$ has both end points in $\Omega^c_1$, inside one component; and no cube at index
distance $\le3$ from $\Omega_1$ lies in $\mathsf P_1$;
(e) the budget recursion (B) of LF-2 holds at $k=0$: $G^{\rm pre}_1(Z')\ge g_0|\mathcal N_1\cap Z'|_\#-c_v\hat\lambda_1|Z'|_\#$, with $\kappa^{(0)}(Z'):=A_3(\log\beta)^{2p_0}|\mathcal N_1\cap Z'|_\#-(c_1\log\beta+c_2)|Z'|_1$
and $\log C_1(Z'):=\frac54|Z'|_{\#0}$ (Definition II.5.11 at $k=0$; empty sums vanish).

*Proof.* (a) $\mathrm d(\mathrm{Bl},\varnothing)=+\infty$ (Part I convention), so every $L$-block is admissible in the opening; the remaining rows of Definition I.3.1 are formulas
in $\Omega'_1$ and the record. (b) Lemma I.3.8 at $k=0$; step 5 of its proof (the old seeds) does not occur because $\Omega'^c_1=\varnothing$. (c) Every component contains a
seed (Lemma I.3.7 (a)), and all seeds are new. The state is the (T2) output (Part I §I.4.4 "Base"); a ripe component would be Active with $t^*=1$, but a (T2) output
has $t^*\ge1+n_q(1)>1$ (Lemma I.4.10 and Definition I.4.6). (d) Lemma I.3.5 (b) gives $\Omega_1\cap\mathsf P^{\sim3}_1=\varnothing$, hence $\mathsf P^{\sim3}_1\subset\Omega^c_1$ since $\Omega'_1=\mathbb T_1$, and
$\Omega^c_1\subset Z^{(0)}_1\subset Z^{\rm pre}_1$ (Lemma I.3.5 (e)). The other end point of such a bond lies in the same or an adjacent cube, in $\mathsf P^{\sim1}_1$; adjacent cubes
are linked ($1<\omega_1$), so they lie in one component (Lemma I.2.12 (d)). The last claim restates $\Omega_1\cap\mathsf P^{\sim3}_1=\varnothing$. (e) The proof of Lemma II.5.12 with
$n_1=0$ (there is no old region): the gain is $A_3(\log\beta)^{2p_0}\ge g_0$ by Lemma II.1.2 (d), and the new-volume term is the one estimated there. $\square$

### II.7.3 Two hard-spin identities

**Lemma II.7.3 (the action is exactly quadratic in the chord; P4 (2.44) at $\lambda=\infty$).** Let $\Omega$ be a finite set of sites, $H$ a real symmetric operator
on $(\mathbb R^N)^\Omega$ acting componentwise, $S\in(\mathbb R^N)^\Omega$, $A(\phi):=\frac12\langle\phi,H\phi\rangle-\langle S,\phi\rangle$, and let $\phi^{\rm b}:\Omega\to S^{N-1}$, $\alpha:\Omega\to\mathbb R$ solve
$H\phi^{\rm b}-S=-\alpha\phi^{\rm b}$ (the Euler–Lagrange system (EL) with multiplier). Then for every $\phi:\Omega\to S^{N-1}$, with the chord $\phi':=\phi-\phi^{\rm b}$,
$$A(\phi)-A(\phi^{\rm b})=\tfrac12\big\langle\phi',(H+\alpha)\phi'\big\rangle .\tag{II.7.2}$$
*Proof.* $A(\phi^{\rm b}+\phi')-A(\phi^{\rm b})=\langle H\phi^{\rm b}-S,\phi'\rangle+\frac12\langle\phi',H\phi'\rangle=-\sum_x\alpha_x\,\phi^{\rm b}_x\cdot\phi'_x+\frac12\langle\phi',H\phi'\rangle$, and
$1=|\phi^{\rm b}_x+\phi'_x|^2=1+2\phi^{\rm b}_x\cdot\phi'_x+|\phi'_x|^2$ gives $-\phi^{\rm b}_x\cdot\phi'_x=\frac12|\phi'_x|^2$. $\square$

*Use.* At the first step the action on the small-field sites is $\beta$ times the quadratic polynomial
$\frac{aL^{d-2}}2\sum_y|\theta(y)-(Q\phi)(y)|^2+\frac12\sum_b|\partial\phi(b)|^2+\frac\mu2\sum_x|\phi_x-h|^2$ in the spins of $\Omega_1$ (the spins of $\Omega^c_1$ enter $S$), and its constrained
minimiser is the Def-5 background (BG Theorem 5.2 (4): the unique global minimiser for real data), which solves (EL) with its multiplier. So (II.7.2) holds
with $H+\alpha=\beta G^{-1}_\alpha$, $G^{-1}_\alpha:=aL^{-2}Q^*Q-\Delta_\Omega+\mu+\alpha$, $Q^*=L^dQ^\top$ (P4 (2.48) at $\lambda=\infty$), **for all spin configurations**, not only on a chart. In regime (A) the
background is $\nu$-free ($\mu=0$) and the field term is added exactly: $\frac{\beta\nu}2(\|\phi-h\|^2-\|\phi^{\rm b}-h\|^2)=\beta\nu\langle\phi^{\rm b}-h,\phi'\rangle+\frac{\beta\nu}2\|\phi'\|^2$ (the term
$\nu_{k+1}\langle\delta\phi_{k+1},\phi_{k+1}-h\rangle$ of P6 p. 11 [checked]). GREEN G-1 at level $1$ gives $aL^{-2}Q^*Q-\Delta_\Omega\ge\gamma_GL^{-2}$ with $\gamma_G=\gamma_G(d,L)>0$, and
$|\alpha|_2\le K_1\cdot4dL\delta_0\le\frac12\gamma_GL^{-2}$ (BG Theorem 5.2 (3) with the data bound of Lemma II.7.5 below, and (Λ26)); so $H+\alpha\ge\frac12\beta\gamma_GL^{-2}$ and the spin weight
relative to the background is $\le e^{-\frac14\beta\gamma_GL^{-2}\|\phi'\|^2}$.
The non-quadratic terms of the first step come only from the chart (below), not from the action.

**Lemma II.7.4 (sphere chart and the $\mathbb R^N$ representation of the tangent integral).** Let $e\in S^{N-1}$, $P^\perp_e:=I-e\otimes e$, $s>0$.
(a) $\xi\mapsto(1-|\xi|^2)^{1/2}e+\xi$ is a diffeomorphism of $\{\xi\in e^\perp:|\xi|<1\}$ onto the open hemisphere $\{\phi\in S^{N-1}:\phi\cdot e>0\}$, and there
$\sigma(d\phi)=(1-|\xi|^2)^{-1/2}\,d^{N-1}\xi$ (Lebesgue measure on $e^\perp$).
(b) For every Borel $f\ge0$ (or integrable $f$) on $e^\perp$: $\displaystyle\int_{e^\perp}f(\xi)\,d^{N-1}\xi=\Big(\frac s{2\pi}\Big)^{1/2}\int_{\mathbb R^N}f(P^\perp_eu)\,e^{-\frac s2(e\cdot u)^2}\,d^Nu$.
(c) [v1.3: P4-02] For complex $e$ near the real sphere put $P^\perp_e:=I-e\,e^\top/(e\cdot e)$. This algebraic projection is holomorphic where $e\cdot e\ne0$. Analyticity of an integral obtained from (b) is asserted only when its complete integrand has a holomorphic continuation and a locally uniform integrable majorant on the fixed real $u$-contour. In the base step this requires the combined quadratic form and determinant of the chart integral; any Borel indicator stays a function of real $u$. This clause makes no assertion for an arbitrary Borel $f$.
*Proof.* (a) The hemisphere is the graph of $F(\xi)=(1-|\xi|^2)^{1/2}$ over the unit ball of $e^\perp$, with area element $(1+|\nabla F|^2)^{1/2}=(1-|\xi|^2)^{-1/2}$. For the
Lean `toSphere` measure this identification is a lemma to be proved (§IV.L item Q2): the graph measure, extended to both hemispheres, and $\sigma$ are
$O(N)$-invariant finite measures on $S^{N-1}$ with the same total mass $Nv_N$, hence equal (uniqueness of the invariant probability measure). (b) Write $u=te+v$,
$v\in e^\perp$; Lebesgue measure factorizes, $P^\perp_eu=v$ and $\int e^{-st^2/2}dt=(2\pi/s)^{1/2}$. (c) Since $e\cdot e\ne0$ near the real sphere, every entry of $P^\perp_e$ is a quotient of holomorphic polynomials with nonzero denominator. The integral criterion follows from dominated convergence on compact complex parameter sets when the stated majorant exists. The required majorant for the actual base integrand belongs to the separate LF-BASE-KF0.md calculation; the real identity (b) alone cannot supply it. $\square$

At the first step the chart is used at every small-field site $x$ with $e=e_x:=\phi^{\rm b}(x)$ and $s=\beta$ (so that in the rescaled variable $v=\beta^{1/2}u$ both the
tangent and the normal directions have unit scale); the quadratic form of the rescaled fluctuation is then $\langle v,(P^\perp G^{-1}_\alpha P^\perp+P)v\rangle$, $P:=\bigoplus_x e_x\otimes e_x$, which is
GREEN §4.4 (ii)'s form (range $\le L$, real part $\ge\frac14L^{-2}$, SF §5.5), and $C^{(0)}:=(P^\perp G^{-1}_\alpha P^\perp+P)^{-1}$ is the fluctuation covariance of the first step.

**Lemma II.7.5 (small-field spins lie in the chart).** On the support of $\chi'^{(0)}(\mathsf P^c_1)$, for every site $x\in\Omega_1$ (as a fine set) and the step background
$\phi^{\rm b}=\phi'_1(\square';\phi,\theta)$ of the cube $\square'\ni x$ (Definition II.2.7 (ii) at $k=0$),
$$|\phi_x-\phi^{\rm b}(x)|\le C_{\rm hs}L\delta_0,\qquad C_{\rm hs}:=d+2+4dK_1,\tag{II.7.3}$$
and by (Λ26) of §IV.O.3 the right side is $\le\frac14$; so $\phi_x\cdot\phi^{\rm b}(x)>0$ and the chart coordinate satisfies $|\xi_x|\le C_{\rm hs}L\delta_0$.
*Proof.* By Lemma II.7.2 (d) every cube within distance $3$ of $\Omega_1$ is outside $\mathsf P_1$, so $A=B=1$ there. For $x$ in the $1$-block $y$: the bond conditions along a
path of $\le d(L-1)$ bonds inside $B_1(y)$ give $|\phi_x-(Q\phi)(y)|\le dL\delta_0$, and the block condition gives $|\phi_x-\theta(y)|<(dL+2)\delta_0$. The data $\mathrm{lift}_{0,1}(\phi,\theta)$
of $G_1(\square')$ are $\theta$ on the blocks of $\Omega_1$ and the spins outside; adjacent blocks satisfy $|\theta(y)-\theta(y')|\le4\delta_0+|(Q\phi)(y)-(Q\phi)(y')|\le(L+4)\delta_0$ (two
adjacent block averages differ by at most $\max_x|\phi_x-\phi_{x+Le}|\le L\delta_0$), block–site pairs across $\partial\Omega_1$ likewise, and $1-dL\delta_0\le|(Q\phi)(y)|\le1$ gives
$||\theta(y)|^2-1|\le3(dL+2)\delta_0$; so the data lie in $\tilde\Psi(G_1(\square');4dL\delta_0)$ ((R1)–(R2) of BG §1.3, $4dL\delta_0\le c_1$ by (Λ26); in regime (B) (R3)–(R4) follow from the site
conditions). By BG Theorem 5.2 (3), $|\phi^{\rm b}-Q^*\mathrm{lift}|_0\le4dK_1L\delta_0$, i.e. $|\phi^{\rm b}(x)-\theta(y)|\le4dK_1L\delta_0$. Add. $\square$

### II.7.4 The base step data

**Definition II.7.6 (base kernels and boundary factors).** Let a base record and a component $Z'$ of $Z^{\rm pre}_1$ be given; $\Omega:=\Omega_1$, $\Omega'':=\Omega''_1$, all sets
intersected with $Z'$ (localized, Lemma I.3.9).
- *Variables* (D-IV.4). Internal: the spins $\phi_x$, $x\in\Omega^c\cap Z'$, and the fluctuation variables $\psi'_0(x)\in\mathbb R^N$, $x\in(\Omega\setminus\Omega'')\cap Z'$; reference measure
  $\sigma^{\otimes}\otimes$ Lebesgue. Output: $\psi_1$ on $T^{(1)}\cap V_{Z'}$. On $\Omega$ the spins are functions of $(\theta,\phi\restriction_{\Omega^c},\psi'_0)$ through the chart of Lemma II.7.4 around
  $e_x=\phi^{\rm b}(x)$ and the substitution $u=\beta^{-1/2}C^{(0)1/2}_{\rm loc}\psi'_0$ (P5 (2.39) at $k=0$; Lemma II.7.5 makes it well defined); on $\Omega''$ the fluctuation is integrated
  in the small-field integral (Proposition II.7.9) and does not appear in the kernel.
- *Kernel.* $K_0(Z')$ is the kernel of P5 (2.47) [checked, p. 512] times P6 (3.2) [checked, p. 16] at $k=0$, with these replacements: $\chi_k(\cdot)\mapsto B(\cdot)$ and
  $\chi'^{(k)}(\cdot)\mapsto\chi'^{(0)}(\cdot)$ of Definition II.7.1; $\psi_k\mapsto\phi$; $\psi^{(k)}(\square';\theta)\mapsto\phi^{\rm b}$; the substitution (2.39) $\mapsto$ the chart substitution; the
  ultra-local Gaussian $(2\pi)^{-N/2}e^{-\frac12\|\psi'\|^2}$ of (2.47) on $\Omega\cap\Omega''^c$ times the chart Jacobian $\prod_x(1-|\xi_x|^2)^{-1/2}$; and the main action of P6 (3.2)
  $\mapsto\mathcal A_1(Z';\psi)$ of Definition II.5.4 with the local background (D-II.1; on layer $0$, $\Lambda_0=\Omega^c\cap Z'$, the multiscale field is the spin field, P2's
  convention $a_0=\infty$). In addition $K_0$ contains $\chi^{\rm new}_0(Z')$ and $\mathbf 1[\phi^{\rm loc}\text{-data}\in\mathcal D_{\mathbb R}]$ (as Definition II.5.6). It has the form
  $$K_0(Z')=\prod_{y\in T^{(1)}\cap\Omega^c\cap Z'}z_1^Nt_0\big(z_1\psi_1(y),(Q\phi)(y)\big)\cdot\sum_{w}F^w_0(u)\,\tilde K^w_0(Z'),\qquad u_y:=z_1\psi_1(y)-(Q\phi)(y),\tag{II.7.4}$$
  where $w$ runs over the maps $\mathsf P_1\cap Z'\to\{\mathrm{blk},\mathrm{bd}\}$ (the witness type of each cube) from $\chi'^{(0)c}(\square')=1-A(\square')B(\square')=(1-A(\square'))+A(\square')(1-B(\square'))$,
  $F^w_0(u):=\prod_{\square':w=\mathrm{blk}}(1-A(\square'))\prod_{\square':w=\mathrm{bd}}A(\square')\prod_{\square'\subset\Omega^c\setminus\mathsf P_1}A(\square')$ depends on $\psi_1\restriction_{\Omega^c}$ only through $u$,
  and $\tilde K^w_0(Z')$ (all other factors, with $1-B(\square')$ for $w=\mathrm{bd}$) does not depend on $\psi_1\restriction_{\Omega^c}$.
- *Boundary factor.* $b_0(Z')$ is the sum of: the vacuum constants of P6 (3.2) at $k=0$ (with the normalization $-\frac{N-1}2\log\beta$ per site of $\Omega\setminus\Omega''$ of the
  chart and of $C^{(0)1/2}$); the renormalization term $\beta_1C^{(1)}$ of P6 (2.31) on $Z'$ (on layer $0$ it is $\beta\frac{\xi^{(0)}_3}{1+\xi^{(0)}_3}\cdot\frac12\sum_{b\subset\Lambda_0}|\partial\phi(b)|^2$ plus the
  $\nu$-term analogue); the corrections of the background change of Lemma IV.1.3 whose localization domains lie in $Z'$; the terms of the small-field integral with
  localization domains in $Z'$ (P6 p. 14 [checked]: "the sum of terms from $\mathcal B''^{(k+1)}$ with localization domains contained in $Z_{k+1}$"); and the source on the
  large-field sites, $\langle g\restriction_{Z'},\phi\rangle$ (OBS §4.2 item 1; §II.6.5 item 1). There are no old boundary terms ($\mathcal B^{(0)}=0$).

**Lemma II.7.7 (structure of the base data: (S0), (S1), (S3)–(S5) at $k=0$).** (a) (S1) in the form of version 1.2 (D-IV.3): (II.7.4) holds, every $F^w_0$ takes
values in $[0,1]$, $\tilde K^w_0\ge0$ is Borel, independent of $g$, and vanishes unless $\chi^{\rm new}_0(Z')=1$. (b) (S0): $b_0$ depends on $\psi_1$ only on $T^{(1)}\cap\Omega_1\cap V_{Z'}$, on the
internal variables and on $(h,g\restriction_{V_{Z'}})$; it is real for real arguments, analytic on the H7 domain jointly in $g$, and $|b_0|\le(C_b\log\beta+C_b)|Z'|_1$, with $C_b$ an
output of rows 0–11 (it contains $N$, $L^d\log(Nv_N)$, the constants of P6 (2.25) and of Lemma IV.1.3, and $1$ for the source term, $|\langle g,\phi\rangle|\le\|g\|_{\ell^1}<1\le|Z'|_1$).
(c) (S3): no kept data occur at scale $1$. (d) (S4): all data are functions of the localized history of $Z'$. (e) (S5) in regime (A): $K_0=\sum_w\mathbf 1_{A_w}e^{-a_w}$ with
$O(N)$-invariant sets $A_w$ (block, bond, $\chi'_1$, $\chi^{(0)}$, $\chi_1$ conditions; the background and $C^{(0)1/2}$ are equivariant, so $\psi'_0$ rotates with the spins) and
exponents $a_w$ (Gaussian exponents, $\mathcal A_1$, $\frac12|\psi'_0|^2$, the logarithm of the chart Jacobian) that are jointly invariant, analytic in the variables on the
displacement neighbourhoods of (S5)(ii) (polynomials in the spins; the chart is analytic for $|\xi|\le\frac12$), with $|a_w(x;h')-a_w(x;h)|\le3|Z'|_1|h'-h|$, since $h$ enters only
through the $\nu$-term, whose coefficient per site is $\beta^{(1)}_0\mu=\beta_1\nu_1L^{-d}\le e^{2\epsilon}L^{-d}$. (S5) is a sum of terms of the stated form; Lemma III.9.5 applies to each.

*Proof.* (a) The factorization of $\chi'^{(0)c}(\square')$ and the list of factors in Definition II.7.6: only $A(\cdot)$ reads $\theta$ on $\Omega^c$; every other factor reads $\psi_1$
on $\Omega_1$ (Definition II.3.2 items 3, 5; the main action and the background read the multiscale field). Measurability: Lemma II.3.3. (b) The terms are those of P6
(2.32)–(2.33) [checked, p. 15] at $k=0$ and of Lemma IV.1.3, with $B_0$ absent; the normalization constants are $O(\log\beta)$ per site; on layer $0$,
$|\beta\xi^{(0)}_3|\le\frac{c_\xi}4q$ (SF Theorem 5.3) and $|\partial\phi|\le2$. (c) Lemma II.7.2 (c). (d) Lemma I.3.9. (e) As in Lemma II.5.10 for the quiet kernels. $\square$

**Lemma II.7.8 (one-step bound at $k=0$; (S2) of version 1.2 with the gain $\kappa^{(0)}$).** Assume (Λ17′), (Λ26), (Λ27), $c_1\ge C_b$ and $c_2\ge C_b$ (both hold by row 14, since $c_2\ge C_bB_0\ge C_b$). For every
base record and component $Z'$ there are Borel majorants $S^w_0\ge0$ of the new′ variables ($\psi_1$ on $T^{(1)}\cap\Omega\cap Z'$, the spins on $\Omega^c\cap Z'$, $\psi'_0$; there are
no old variables) with $\tilde K^w_0e^{{\rm Re}\,b_0}\le S^w_0$ and
$$\sum_wm^w_0\int d(\text{new}')\,S^w_0\ \le\ e^{-\kappa^{(0)}(Z')},\qquad m^w_0:=\int\prod_yg_0(u_y)\,F^w_0(u)\,du,\tag{II.7.5}$$
$g_0$ the centred Gaussian density of $t_0$ (so $\int z_1^Nt_0(z_1\psi,w)F(z_1\psi-w)\,d\psi=\int g_0F$).

*Proof.* *Splitting of the main action.* $\mathcal A_1\ge0$ for real arguments; write $e^{-\mathcal A_1}=e^{-\frac12\mathcal A_1}e^{-\frac12\mathcal A_1}$, one half for the bond and site witnesses, one half
for the $\mathsf Q$- and $\mathsf S$-witnesses through LF-1 (Theorem II.4.1, which holds for every field, in particular for the local background and with layer $0$ the spin
field). *Witnesses.* For each cube of $\mathcal N_1\cap Z'$ choose one violated condition (a block $y$, a bond $b$ or a site $x$ for $\mathsf P_1$-cubes according to $w$; a $\chi'_1$-, $\chi^{(0)}$- or
$\chi_1$-condition for $\mathsf Q_1,\mathsf R_1,\mathsf S_1$); $1-\prod(\cdot)\le\sum(\text{failures})$ bounds each failure function by the sum over its witnesses. A bond witness serves at most two
cubes (Lemma II.7.2 (d)); every other witness serves one. The factors are:
- block witness ($w=\mathrm{blk}$): in $m^w_0$, $\int g_0(u)\mathbf 1[|u|\ge2\delta_0]du\le2^{N/2}e^{-\frac14\beta aL^{d-2}(2\delta_0)^2}=2^{N/2}e^{-L^{d-2}p_0(\beta)^2}$ (half the Gaussian exponent for the gain, the
  other half for the integral; P6 (3.4), first factor);
- bond witness: $e^{-\frac12\mathcal A_1}\le e^{-\frac14\beta^{(1)}_0|\partial\phi(b)|^2}\le e^{-\frac18\beta\delta_0^2}=e^{-p_0(\beta)^2/(8a)}$, since the bond lies in $\Lambda_0\cap Z'$ (Lemma II.7.2 (d)), its term
  $\frac12\beta^{(1)}_0|\partial\phi(b)|^2$ is part of $\mathcal A_1$ (Definition II.5.4, layer $0$), and $\beta^{(1)}_0=\beta/(1+\xi^{(0)}_3)\ge\beta/2$;
- site witness (regime (B)): $e^{-\frac12\mathcal A_1}\le e^{-\frac14\beta^{(1)}_0\mu|\phi_x-h|^2}\le e^{-p_0(\beta)^2/(9a)}$, as $\mu=\nu_1L^{-2}=\nu\delta_1\ge\nu e^{-\epsilon}$;
- $\mathsf Q_1$- and $\mathsf S_1$-witnesses: P6 (3.7)–(3.8) [checked, p. 18] with LF-1 applied to $\frac12\mathcal A_1$: factors $\exp(-\frac{4\gamma_0}{6^d(9K_1)^2}p_0(\beta)^2)$ and $\exp(-\frac{\gamma_0}{4\cdot6^dK_1^2}p_0(\beta)^2)$
  per cube (P6's exponents halved);
- $\mathsf R_1$-witness: the ultra-local Gaussian, $(2\pi)^{-N/2}e^{-\frac12|\psi'_0|^2}\mathbf 1[|\psi'_0|\ge p_1(\beta)]\le e^{-\frac14p_1(\beta)^2}\cdot(2\pi)^{-N/2}e^{-\frac14|\psi'_0|^2}$ (P6 (3.4), second factor).
With $A_3:=\frac14\min\{\frac{8\gamma_0}{6^d(9K_1)^2}A_0^2,\frac18A_1^2\}$ (a quarter of P6's constant (3.9) [checked, p. 18]; row 9 as amended, §IV.O.2: the factor $\frac14$ pays the halving of
$\mathcal A_1$ and of the bond overlap), $A_1<A_0$ (row 9: $A_0=4K_2B_5A_1$), $\gamma_0=\frac1{28d}$ and $p_j(\beta)\ge A_j(\log\beta)^{p_0}$, every factor is $\le e^{-2A_3(\log\beta)^{2p_0}}$ per cube after the
bond overlap is halved, up to polynomial prefactors; the number of witness choices per cube is $\le(d+1)(2LM)^d$, and (Λ27) makes the prefactors and this entropy
$\le e^{A_3(\log\beta)^{2p_0}}$ per cube. *Volumes.* The remaining factors are bounded by: the shell indicators of $\chi^{\rm new}_0$ for
$\psi_1$ on the blocks of $\Omega\cap Z'$ (Lemma II.5.14's argument: (1.24) at $j=0$, first family, gives $||\psi_1(y)|^2-1|<3dL\delta_0$; volume $\le1$ by (Λ17′)); the spins on
$\Omega^c\cap Z'$ (mass $Nv_N$ each); $\psi'_0$ (Gaussian $(2\pi)^{-N/2}e^{-\frac14|\psi'_0|^2}$ at witness sites, integral $2^{N/2}$, and the probability density elsewhere); the chart
Jacobian ($\le(1-\frac1{16})^{-1/2}\le2$ by Lemma II.7.5); all other indicators and the second half of $e^{-\mathcal A_1}$ by $1$; and $e^{{\rm Re}\,b_0}$ by (b) of Lemma II.7.7. The volume
factors are $\le e^{L^d\log(2^{N+1}Nv_N)|Z'|_1}$, which $C_b$ contains. Collecting, $\sum_wm^w_0\int S^w_0\le e^{-A_3(\log\beta)^{2p_0}|\mathcal N_1\cap Z'|_\#+(C_b\log\beta+C_b)|Z'|_1}\le e^{-\kappa^{(0)}(Z')}$. $\square$

### II.7.5 The small-field part of the first step

[v1.3: P4-03] Proposition II.7.9 below is superseded by notes/phase1/LF-BASE-KF0.md (in preparation). Its stated interface is retained for LF-6 and the assembly.

**Proposition II.7.9 (the small field at scale $1$; I-9 at $k=0$; cited/sketched).** For every base record, on $Z^c_1$ the result of the first step has the form
(D1) at scale $1$ with: small-field data satisfying Def-6 at $k=1$ (regime (A); $\nu$-free backgrounds, the $\nu$-free RG system of CHK §2) resp. (D2♭) (regime (B); complete
backgrounds and P4's system); the characteristic function $\chi_1(Z^c_1)$; boundary terms $\mathcal B^{(1)}(X)$ with domains meeting $Z_1$ and $Z^c_1$, satisfying (D7) with $\kappa_+=\frac32\kappa$
and a constant $B_{\rm st}$ of rows 0–11; and $\mathcal R^{(1)}_n=0$ for $n<m$, $\mathcal R^{(1)}_m=\mathcal R'^{(1)}_m$ bounded by $\frac12\beta_1^{-m-1}$ (P5 Proposition 3.2 at $k=0$). The running
constants $(\beta_1,\nu_1,z_1,E_1)$ solve I-7 at $k=0$.
*Status and route.* This is I-9 (SF §5) at $k=0$, which SF §5.5 leaves to LF-6, with the following differences, each of which is written out above or cited:
1. the input has no small-field data: $\mathscr E^{(j)}=\mathscr M^{(j)}=0$, the scale-$0$ "background" is the spin field itself, and $\mathscr F_0=\langle g,\phi\rangle$;
2. the action is exactly quadratic in the chord (Lemma II.7.3): the interaction $V^{(1)}$ of P4 (2.46) [review] consists only of the chart terms ($(1-|\xi|^2)^{1/2}-1$, the Jacobian,
   the normal factor of Lemma II.7.4 (b)) and, in regime (A), of the explicit field term; all are analytic on the chart domain of Lemma II.7.5;
3. the fluctuation covariance is $C^{(0)}=(P^\perp G^{-1}_\alpha P^\perp+P)^{-1}$; its localization (I-4c at the first step) is GREEN §4.4 (ii) and G-1 (cited);
4. the localization and cluster expansions of the fluctuation integral are I-8 at $k=0$ (SF §4, sketched; P6 §4 [checked, pp. 22–45]), with the old boundary terms absent;
5. I-7 at $k=0$: in regime (A) the system with $\nu$-free backgrounds (CHK §2: (E1-free), (E2-free), the new transversal equation; SMALLFIELD v3 §3, queued), in
   regime (B) P4's system (SF §3.4);
6. (H.5) for the new term $\mathscr E^{(1)}$ by construction (the three renormalization conditions are the equations of I-7).
The large-field part of the first step (the base kernels) is Definition II.7.6; the split of the boundary terms between $b_0$ (domains inside $Z_1$) and $\mathcal B^{(1)}$ (domains meeting
$Z^c_1$) is P6 p. 14 [checked] at $k=0$.

### II.7.6 LF-6

**Theorem II.7.10 (LF-6; ARCH §3.7 LF-6, roadmap LF-6).** Assume (A-IV.1)–(A-IV.3), $k_f\ge1$, and the cited inputs of Proposition II.7.9. On every admissible torus
let $\mathrm{rep}_1$ consist of: the small-field data of Proposition II.7.9; the set $\mathfrak A_1$ of **all** admissible histories up to scale $1$ (the base records; Lemma II.7.2 (a));
the step data of Definition II.7.6; the boundary terms $\mathcal B^{(1)}$ of Proposition II.7.9. Then:
(a) $\int\rho_1\,d\psi_1=Z(g)$ identically in $(h,g)$, $\|g\|_{\ell^1}<1$;
(b) in regime (A), $\mathrm{IsRep}_1(\mathsf c,\mathrm{rep}_1,\rho_1)$; in regime (B), $\mathrm{IsRep}^\flat_1(\mathsf c,\mathrm{rep}_1,\rho_1)$ with the threshold $A_2\hat\lambda_0^{p_2}\ge p_2(\beta)$;
(c) the step data satisfy (S0)–(S5) (version 1.2) with $\kappa^{(0)}$ of Lemma II.7.2 (e);
(d) the boundary terms satisfy (D7) with $\kappa_+$ and $B_{\rm st}\le B_0-1$; (D8) holds;
(e) for fixed $\beta,h$ the family $(\mathrm{rep}_1(\nu),\rho_1(\nu))_{0<\nu\le\nu_*(1)}$ satisfies $\mathrm{IsRepFam}_1$ in the form of Definition IV.3.1.

*Proof.* (a) (II.7.1). *(D1).* Insert the base decomposition and the later decompositions into (II.7.1), perform the small-field integral on $\Omega''_1$ (Proposition
II.7.9) and collect the factors of each history: the terms with the same history are the term of (D1) with $\mathbb T_1(Z_1,\mathbb A)=\bigotimes_{Z'}(K_0(Z'),b_0(Z'))$ (no ancestors,
Definition II.5.8 at $k=0$; the factorization over components is Lemma II.5.9 (b), whose proof at $k=0$ uses Lemma I.2.13 and the base data's supports), and absolute convergence
follows from (II.7.5) and Lemma II.5.13 (composition with no ancestors). Every admissible history occurs (completeness, D-III.8), because the decompositions are expansions
of $1$ into all records. *(D2)/(D2♭), (D3).* Proposition II.7.9. *(D4).* (S0)–(S5): Lemmas II.7.7, II.7.8. *(D5).* Lemma II.6.3 (a), from (S2) at $j=0$. *(D6).* Regime (A):
LF-2 (i) at $k=1$ (Theorem I.5.4, its base case §I.5.5: (B) at $k=0$ is Lemma II.7.2 (e), Case 1 with $m=0$), applied to every history of $\mathfrak A_1$; the hypotheses (G1), (G2) are
Lemma II.7.2 (a)–(b) and (R8); (H-λ), (H-T) are Lemma IV.3.3 (c), (d); (Rg) is void at scale $1$ (Lemma II.7.2 (c)). Regime (B): LF-2 (ii) with $k_0=0$ (Theorem I.5.4 (ii), the frozen base
step (I.6) with $m=0$) gives (H6♭) at $k=1$. *(D7).* Proposition II.7.9 and row 12 ($B_0\ge B_{\rm st}+1$). *(D8).* Every datum is defined by the same formula on $\mathbb Z^d$ from the
localized history and the variables of its support; inside a box of side $<\ell/2$ these coincide with the torus formulas (D-IV.9). *(D9)/(D9♭).* $\beta_1=\beta L^{d-2}\gamma_1>BL^{d-2}$
(row 16, D-IV.10); $\nu_1\le e^{2\epsilon}\beta_1^{-1}\le\frac78L^{-2}$ in regime (A); $\nu_1=\nu L^2\delta_1\le\frac78e^{2\epsilon}<1$ in regime (B) because $k_f\ge1$ means $\nu\le\frac78L^{-2}$. (b)–(d) are these
clauses. (e) The base data are explicit formulas in $(\beta_1(\nu),\nu_1(\nu),z_1(\nu),E_1(\nu))$, $b=\nu h$, the variables, and indicators with thresholds $\delta_0$ (independent of $\nu$)
and $\delta_1(\nu)$; the running constants have limits as $\nu\downarrow0$ (SF §3.5, (CONT)), the backgrounds of regime (A) do not depend on $\nu$, the history sets do not depend on
$\nu$ (D-IV.2), and all bounds above are uniform in $\nu$; so Definition IV.3.1 holds by dominated convergence (the level sets $\{f=\delta_1(0)\}$ of the real-analytic functions
$f$ read by the indicators are null sets). For $\nu\le\nu_*(1)$ we are in regime (A). $\square$

*What LF-6 adds to the sources.* P5 p. 487 describes the first step in words; P4 (2.42)–(2.50) treats it for $\lambda_0$ finite and the whole lattice small field; the base
case for hard spins with large fields is not in the sources (ER-062, ER-063). The new items are the base rule (Definition II.7.1, the bond and site conditions as
part of the $\mathsf P$-decomposition), the exact quadratic identity (Lemma II.7.3), the chart without local sections (Lemma II.7.4), the a priori containment of the
small-field spins in the chart (Lemma II.7.5), and the gain at $k=0$ from three witness types (Lemma II.7.8).

---

## IV.1 LF-3: one full step for $1\le k<k_0$ (P5 Theorem 1, P6 Theorem 1)

### IV.1.1 Statement

**Theorem IV.1.1 (LF-3).** Assume (A-IV.1)–(A-IV.3) and the cited inputs of §IV.1.3. Let $1\le k<k_0$ (so $\beta_{k+1}\nu_{k+1}\le e^{2\epsilon}$ and $\nu_k\le e^{2\epsilon}\beta_k^{-1}\le\frac78L^{-2}$) and let
$\mathrm{rep}=(\mathfrak s,\mathfrak A,\mathfrak D,\mathcal B)$ satisfy $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep},\rho)$ on the admissible tori. Then there are $z_{k+1}>0$ and a representation $\mathrm{rep}'$ such that, with
$\rho'(\psi_{k+1}):=z_{k+1}^{N|T^{(k+1)}|}(T^{(k)}\rho)(z_{k+1}\psi_{k+1})$ (P1 (1.11), P4 (4.1)):
- (a) $\int\rho'\,d\psi_{k+1}=\int\rho\,d\psi_k$ identically in $(h,g)$, $\|g\|_{\ell^1}<1$;
- (b) $\mathrm{IsRep}^{\rm pre}_{k+1}(\mathsf c,\mathrm{rep}',\rho')$ (Definition II.6.2, §II.6.3, versions 1.1–1.2); in particular its (D7) holds with $\kappa_+=\frac32\kappa$ and $B_{\rm st}$, and its (D2) gives $\mathcal R^{(k+1)}_m$ the
  bound $\frac12\beta_{k+1}^{-m-1}$;
- (c) the history set of $\mathrm{rep}'$ is the set of all admissible histories up to scale $k+1$ without an $R$-record at $k+1$; each is a history of $\mathrm{rep}$ followed by a step
  record (Definition I.3.1) and the hull closure (R8);
- (d) the step data of the step $k\to k+1$ are the quiet kernels (Definition II.5.6) where the step is quiet, and otherwise the kernels of P5 (2.47)·P6 (3.2) with the local
  background (D-II.1) and the boundary factors of P6 (2.32)–(2.33), (3.3) with the corrections of Lemma IV.1.3; they satisfy (S0)–(S5) (version 1.2);
- (e) the small-field data of $\mathrm{rep}'$ are the image of those of $\mathrm{rep}$ under I-9 (SF Theorems 5.1–5.3; P5 Theorem 1 [checked, p. 499]) with the free flow and the $\nu$-free
  RG system (CHK §2), extended to the subdomain $Z^c_{k+1}$ by P5 Propositions 3.1–3.4 and P6 Propositions 2.1–2.4;
- (f) (O-III-1) the constants $B_{\rm st}$, $C_b$, $C_{15}$ are outputs of rows 0–11; they do not depend on $B_0,H_0,c_1,c_2,C_R$;
- (g) if $(\mathrm{rep}(\nu),\rho(\nu))_\nu$ satisfies $\mathrm{IsRepFam}_k$ (Definition IV.3.1), then $(\mathrm{rep}'(\nu),\rho'(\nu))_\nu$ satisfies $\mathrm{IsRepFam}^{\rm pre}_{k+1}$;
- (h) (D8) holds for $\mathrm{rep}'$.

*What LF-3 replaces in the sources.* P5 Theorem 1 and P6 Theorem 1 assert the step on the space (1.42) "except that Hypothesis (H6) may be not satisfied, only the
weaker hypothesis with the inequality '≥'" (P5 p. 499 [checked]); P6 p. 21 [checked]: "Instead we have a weaker condition $K(Z,\mathbb A_{k+1}\cap Z)\ge0$". Here (D6) of the
pre-class is the budget invariant (H6′)$^{\rm pre}$, proved by LF-2 (i). The analytic part is cited to P5 §§2–3 and P6 §§2–4 with four modifications written out below: the
local background (Lemma IV.1.3), the Gaussian structure of (S1)–(S2) (Lemma IV.1.4), the independence of $B_{\rm st}$ (Lemma IV.1.5) and the rotation form (Lemma IV.1.6).

### IV.1.2 Lemmas

**Lemma IV.1.2 (P5 Lemma 2.1).** In the step $k\to k+1$ ($k\ge1$): if $\square\in\pi_k$, $\square\subset\square'\in\pi_{k+1}$, $\square'\subset\Omega^{\sim3}_{k+1}\cap\mathsf Q^c_{k+1}$, and the fluctuation variables on
$R_{k+1}(\square')$ satisfy $\chi^{(k)}=1$ (P5's condition "$R_{k+1}(\square')\cap\mathsf R^\sim_{k+1}=\varnothing$" [checked, p. 511]), then $\chi_k(\square)=1$; likewise $\chi'^{(k)}(\square')=1$ for
$\square'\subset\Omega_{k+1}\cap\mathsf Q^c_{k+1}$ with the same condition.
*Proof.* This is Case A of Lemma III.7.1 with a window of one step (P7 p. 512 [checked]: "The analysis in this case covers in particular a proof of Lemma 2.1 [5]"):
on $\square'$, $\psi_k=\psi^{(k)}(\square';\theta)+\beta_k^{-1/2}C^{(k)1/2}_{\rm loc}\psi'$ (P5 (2.20), (2.39)) with $|\psi'|<p_1(\beta_k)$, so the deviation from $\psi^{(k)}(\square';\theta)=Q_k\phi'_{k+1}(\square';\theta)$ is
$<\|C^{1/2}\|\beta_k^{-1/2}p_1(\beta_k)=\|C^{1/2}\|\frac{A_1}{A_0}\delta_k\le\frac1{8K_2}\delta_k$ (row 9, $A_0=4K_2B_5A_1$; $B_5$ bounds $C^{(k)1/2}_{\rm loc}$, LOC I-4c (ii), and with the exponential decay of its kernel also in the sup norm, up to a constant absorbed in $B_5$); the configuration $\psi^{(k)}(\square';\theta)$ satisfies the
conditions of $\chi_k(\square)$ with $\frac34\delta_k$ because $\chi'_{k+1}(\square')=1$ (the composition identity I-2, landed `theorem73_real`, maps the scale-$(k+1)$ background to the
scale-$k$ one); BG Proposition 5.1 (constant $K_2$) moves each condition by $<\frac18\delta_k$, as in (2.63)–(2.64) of Lemma III.7.1; the domain conjunct holds by (Λ17). $\square$

**Lemma IV.1.3 (the analytic half of Lemma F) [v1.3: P4-09, Lambda28', F-1].** Assume the inputs of FLUCTUATION Theorem 4.2: LOC I-4a/b, Lemma AE, GM, and its weighted response Lemma 4.1, with the auxiliary cover of FLUCTUATION Definition 2.7. In the step $k\to k+1$, on the real support of the step functions and on the complex H7 domain,
$$\beta_{k+1}A^*_{k+1}(Z^c_k\cap Z_{k+1},\mathbb B_{k+1};\psi,\phi^\partial)=\sum_{Z'}\mathcal A_{k+1}(Z';\psi)+\sum_{Y\in\mathcal D_{k+1}(\bmod\Omega^c_{k+1})}\Delta(Y),\tag{IV.1.1}$$
where $\phi^\partial$ is the background of $\mathbb B_{k+1}(\partial\Omega_{k+1})$, each $\Delta(Y)$ is local, real for real arguments, jointly $O(N)$-covariant, and analytic on the H7 domain at $Y$. With $D_k=M([\hat R_k]-1)-2M_1$,
$$|\Delta(Y)|\le C_Fp_0(\beta_k)^2e^{-\gamma_wD_k}e^{-(2\kappa-1-\kappa_0)d^{\rm cov}_{k+1}(Y\bmod\Omega^c_{k+1})}\le e^{-\hat R_k/2}e^{-\kappa_+d^{\rm cov}_{k+1}(Y\bmod\Omega^c_{k+1})}.$$
The terms supported inside one component of $Z_{k+1}$ enter $b_k$; the others enter $\mathcal B^{(k+1)}$.

*Proof.* This is FLUCTUATION Theorem 4.2 in the notation of LFR Definitions II.2.7 and II.5.4; the following identification checks its hypotheses and constants. Put $\mathbb B^{\rm loc}=\bigcup_{Z'}G^{Z'}_{k+1}$ and $E_{Z'}=Z'^{\sim[\hat R_k]}$. Lemma II.2.3(b) gives $\mathbb B^{\rm loc}\prec\mathbb B^\partial$, and BG Theorem 6.1 (landed theorem73_real and theorem73_complex) writes $\phi^\partial=\phi(\mathbb B^{\rm loc};\tilde\psi+\delta\Psi)$. By Lemma II.2.5(c), the generating sets agree on $E_{Z'}$, hence $\delta\Psi=0$ there; outside, BG Theorem 6.1 and the retained step indicators give $|\delta\Psi|\le C\delta_k$. This holds for each decoupling parameter because the equality on $E_{Z'}$ is geometric. The weighted response of FLUCTUATION Lemma 4.1 therefore gives, on $X_{Z'}^+$, a bound $CK_{\rm far}e^{N_0\kappa_1}\delta_ke^{-\gamma_wD_k}$ for the background difference and its derivative and multiplier. The distance is $D_k$, after losing one $M$-cube and $2M_1$ at the cover; it is not $2M\hat R_k$.

For a scale-$(k+1)$ cube $\square\subset X_{Z'}$, form the difference $F_\square(s)$ between the restricted actions at the changed and original local backgrounds, with one common decoupling vector $s$. Each action is a sum of at most $C(LM)^d$ quadratic terms. Both background values are $O(\delta_k)$ on the real support and complex H7 domain. Expanding each quadratic term as $Q(v+w)-Q(v)=2B(v,w)+Q(w)$ and using $\beta_{k+1}\delta_k^2\le2L^{d-2}p_0(\beta_k)^2$ gives $|F_\square(s)|\le C_F'p_0(\beta_k)^2e^{-\gamma_wD_k}$. The first variation includes the surface terms of P6 (2.14), so no vanishing first derivative is assumed. LOC I-4a/b makes $F_\square$ analytic in $s$ and in the H7 data. Lemma AE and GM expand it into terms bounded by this prefactor times $e^{-2\kappa\tilde d^{\rm cov}_{k+1}(Y)}$. The multiscale size dominates the modular cover size; pre-summing labels of one support loses $\kappa_0$ and summing over $\square\subset Y$ loses one further unit of rate. This gives the first displayed inequality. The rate condition $2\kappa-1-\kappa_0\ge\kappa_+$ and (Λ28′) give the second.

For the complex statement, the H7 domain maps into the background data domain by (Ξ1) with $C_{\Xi1}=(4d+8)(2d+1)$ and the threshold in row 16; the local $\mathscr E,\mathscr M$ outputs use the author-accepted $\Xi^c$ domain. Analyticity, locality, reality and covariance then follow respectively from the decoupled background, AE, conjugation and equivariance, as in FLUCTUATION Theorem 4.2 Step 5. $\square$

*Status.* The proof imports precisely the hypotheses of FLUCTUATION Theorem 4.2. Its auxiliary-cover admissibility and LOC (GM) inputs remain explicit in IV.5.6. The modular size $d^{\rm cov}$ is the one of FLUCTUATION §4.3(iv); (D7) and its consumers must use that size.
**Lemma IV.1.4 (one-step bound for non-quiet steps; (S1)–(S2) of version 1.2).** Let $1\le k<k_0$ and let the step be non-quiet in the component $Z'$ of $Z^{\rm pre}_{k+1}$.
(a) The kernel has the Gaussian structure (S1) with the single witness function $F_k(u)=\chi'^{(k)c}(\mathsf P_{k+1})\chi'^{(k)}(\mathsf P^c_{k+1}\cap\Omega'_{k+1}\cap\Omega^c_{k+1})$, a function of the differences
$u_y=z_{k+1}\psi_{k+1}(y)-(Q\psi_k)(y)$, $y\subset\Omega^c_{k+1}\cap Z'$; every other factor reads $\psi_{k+1}$ only on $\Omega_{k+1}$.
(b) (S2) holds with $\kappa^{(k)}(Z')=A_3(\log\beta_k)^{2p_0}|\mathcal N_{k+1}\cap Z'|_\#-(c_1\log\beta_k+c_2)|Z^c_k\cap Z'|_{k+1}$ (Definition II.5.11), $A_3$ of row 9 as amended, provided
$c_1\ge C_b$, $c_2\ge C_bB_0$.
*Proof.* (a) P5 (2.47) [checked, p. 512]: $\chi'^{(k)}$ is the only factor reading $\theta$ on $\Omega^c_{k+1}$ (Definition II.3.2 item 2); $\chi'_{k+1}$ reads $\theta$ on $\Omega_{k+1}$ (item 3), $\chi_{k+1}$
and the main action read $\psi_{k+1}$ on $\Omega_{k+1}$ (item 5, Definition II.5.4), $b_k$ likewise ((S0) version 1.1). (b) P6 (3.4)–(3.9) [checked, pp. 16–18], read with the order of
integration of Lemma II.5.13 (version 1.2): the $\mathsf P$-factor $e^{-aL^{d-2}p_0(\beta_k)^2|\mathsf P|/M^d}$ of (3.4) is the Gaussian measure $m_k$ of $F_k$ (with the entropy $(d\log M+\frac N2\log2)|\mathsf P|/M^d$ of the
witness block and the half-Gaussian); the $\mathsf R$-factor $e^{-\frac14p_1(\beta_k)^2|\mathsf R|/M^d}$ comes from the ultra-local Gaussian of the fluctuation variables; the $\mathsf Q$- and $\mathsf S$-factors (3.7),
(3.8) come from LF-1 (Theorem II.4.1, valid for every field, hence for the local background); the new′ variables are integrated in shells ((1.24) in $\chi^{\rm new}_k$, volume $\le1$ by
(Λ17′)) or against the ultra-local Gaussian; the boundary factor is bounded by (S0). P6 (3.4) takes the supremum over $\psi'_k$ and the old variables *after* bounding the new
integrals, which is the uniformity in the old variables required by (S2). The gain per new cube is $\ge4A_3(\log\beta_k)^{2p_0}$ (P6's constant is $4A_3$), and the volume term
$(O(1)\log\beta_k+{\rm const.}E_0)|Z^c_k\cap Z_{k+1}|$ of (3.9) together with (S0) is $\le(C_b\log\beta_k+C_bB_0)|Z^c_k\cap Z'|_{k+1}$ by the definition of $C_b$ (row 11). The hull cubes lie in
$\Omega''_{k+1}$ and are covered by the same integrals (Lemma II.5.12). $\square$

**Lemma IV.1.5 ($B_{\rm st}$ does not depend on $B_0,H_0,c_1,c_2$; O-III-1 (i)).** The boundary terms $\mathcal B^{(k+1)}(X)$ created by the step $k\to k+1$ ($k\ge0$) satisfy (D7) with $\kappa_+$ and a
constant $B_{\rm st}$ of rows 0–11, provided (Λ28) holds.
*Proof.* They are of three kinds (P5 p. 512 [checked], P6 p. 14–15 [checked]). (i) New terms of the fluctuation integral, of the renormalization and of the surface terms
(P5 Propositions 3.1–3.4, P6 Propositions 2.1–2.3): their constants are those of I-4, I-5, I-8 and P6 (2.25), i.e. of rows 0–11 (P6 p. 15: "contributions to $\mathcal B^{(k+1)}$
constructed in various operations have bounds independent of $B_0$"). (ii) The terms $\Delta(Y)$ of Lemma IV.1.3 with $Y$ meeting $Z^c_{k+1}$: bounded by $e^{-\hat R_k/2}\le1$. (iii) The
contributions of the old boundary terms $\mathcal B^{(k)}(X')$ whose domains meet $\Omega_{k+1}$ (the part $\mathcal B''^{(k)}$ of P5 p. 512, which enters the fluctuation integral). Such an $X'$
meets $Z_k$ (Definition II.6.1) and $\Omega_{k+1}\subset\Omega_k$. Since $Z_k$ contains the collar $(\Omega''^c_k)^{\sim([2\hat R_{k-1}]+6)}\setminus\Omega^c_k$ of $\Omega^c_k$ (Lemma I.3.5 (d), (e) at scale $k$), the connected
set $X'$ meets $Z_k\cap\Omega_k$; any chosen cover family for $d_k^{\rm cov}(X'\,\mathrm{mod}\,\Omega^c_k)$ must cover a cube there and a cube in $\Omega_{k+1}\cap X'$, at index distance $\ge([\hat R_k]+4)L-1$ (Lemma I.3.5(f)). A cover cube has side $L$ in these units, so a tree meeting the two cover cubes has length at least $([\hat R_k]+4)L-1-2L\ge L[\hat R_k]$. Taking the infimum over covers preserves this lower bound. Hence [v1.3: FLUCTUATION §4.3(iv)] $|\mathcal B^{(k)}(X')|\le B_0e^{-\frac\kappa2L[\hat R_k]}e^{-\frac\kappa2d_k^{\rm cov}(X'\,\mathrm{mod}\,\Omega^c_k)}\le e^{-\frac\kappa2d_k^{\rm cov}(X'\,\mathrm{mod}\,\Omega^c_k)}$ by (Λ28) ($\lambda_*$ is chosen after $B_0$). In the
fluctuation integral these terms enter as interactions bounded independently of $B_0$, and P5 Proposition 3.1 turns them into terms of $\mathcal B^{(k+1)}$ with constants of rows
0–11 and the decay $\kappa_+$ (the tree length contracts by $L^{-1}$ under the rescaling; with $L\ge3$ the rate $\frac\kappa2L\ge\frac32\kappa$). The old terms with domains inside $\Omega^c_{k+1}$
(the part $\mathcal B'^{(k)}$) do not enter $\mathcal B^{(k+1)}$; they are part of $b_k$ ((S0): the term $C_bB_0$). $\square$

So the only place where $B_0$ enters the step is the bound (S0) of $b_k$, which the cost coefficient $c_2\ge C_bB_0$ pays (row 14). This is P7's mechanism (p. 529 [checked]: "a
constant in the bound (1.35) [5] independent of $B_0$. We can fix $B_0$ as equal to this constant"), now with the dependence on $H_0,c_1,c_2$ excluded as well: none of these
constants enters a small-field expansion.

**Lemma IV.1.6 ((S5) for non-quiet kernels; O-III-1 (ii)).** For $1\le k<k_0$ every non-quiet step kernel has the rotation form (S5) with $C_{\rm S5}=3$.
*Proof.* The factors of P5 (2.47)·P6 (3.2) are: indicators of conditions on $\theta-Q\psi_k$, on backgrounds and on $|\psi'|$ (no $h$-condition at scales $\le k+1\le k_0$, §II.3.1), which define
$O(N)$-invariant sets because the backgrounds are equivariant (uniqueness, BG Theorem 7.1) and the substitution $\psi_k=\psi^{(k)}(\square';\theta)+\beta_k^{-1/2}C^{(k)1/2}_{\rm loc}\psi'$ is equivariant when
$\psi'$ is rotated ($C^{(k)}$ is built from the equivariant background, so $C^{(k)1/2}(R\psi)=RC^{(k)1/2}(\psi)R^\top$); Gaussian exponents; the ultra-local Gaussian $\frac12|\psi'|^2$; and the main
action $\mathcal A_{k+1}(Z';\psi)$ with the local background. The exponents are jointly invariant, analytic in all variables on the displacement neighbourhoods of (S5)(ii) (BG
Theorem 5.2 (2) for the backgrounds; the localized $C^{1/2}$ is analytic, LOC I-4c), and $h$ enters only through the $\nu$-term of $\mathcal A_{k+1}$, whose coefficient per site is
$\beta_{k+1}\nu_{k+1}L^{-(k+1)d}\le e^{2\epsilon}L^{-(k+1)d}$; this gives $|a(x;h')-a(x;h)|\le3|Z'|_{k+1}|h'-h|$ as in Lemma II.7.7 (e). $\square$

**Lemma IV.1.7 (the family class; O-II-6, O-III-1 (iii)).** If $(\mathrm{rep}(\nu),\rho(\nu))$ satisfies $\mathrm{IsRepFam}_k$, the data constructed in Theorem IV.1.1 satisfy $\mathrm{IsRepFam}^{\rm pre}_{k+1}$.
*Proof.* Every new datum is an explicit formula in the data of $\mathrm{rep}(\nu)$: the running constants (with limits as $\nu\downarrow0$, SF §3.5 and Lemma 3.3 there, applied to the
$\nu$-free system), the $\nu$-free backgrounds (independent of $\nu$), Gaussian kernels with coefficients $\beta_j(\nu)a$, indicators with thresholds $\delta_j(\nu)$, and absolutely convergent
localization expansions with $\nu$-uniform bounds (P5–P6 §§3–4). Limits of indicators exist off the null level sets $\{f=\delta_j(0)\}$; limits of the expansions follow by
dominated convergence (Tannery) and by Vitali for the analytic dependence (OBS Lemma 3.6). The localized histories with support in a box do not depend on $\nu$ (D-IV.2). $\square$

**Lemma IV.1.8 (the reduced-symmetry terms; O-III-1 (v)) [v1.3: P4-04].** The output of the step satisfies the pre-class half-budget at scale $k+1$: each localized term of $\mathcal R_m^{(k+1)}$ has modulus at most $\frac12\beta_{k+1}^{-m-1}e^{-\kappa_b d^{\rm cov}_{k+1}(Y\bmod\Omega^c)}$. This includes terms $Y\subset\Omega''_{k+1}$ equal to their whole-torus counterparts. For $n<m$, the image terms $\mathcal R^{(k+1)}_n$ satisfy the corresponding H4 budget. The assertion uses FLUCTUATION Theorem 3.1(d),(e), conditional on its stated localization inputs (V0), (Vmod), LOC I-4/GM and Theorem 3.4; it does not use decay of domain-dependent differences to estimate whole-torus terms.

*Proof.* P5 (3.9) writes $\mathcal R'^{(k+1)}$ as the integral over $u\in[0,1]$ of the marked fluctuation expectation. Each mark is one of the $\delta_0^{(k)}$ interactions localized in FLUCTUATION Proposition 3.3. P6 Lemma 4.2, in the parameter choice used in FLUCTUATION §3.5(d), gives the bound $\beta_k^{-m-2}e^{-\kappa_Ud^{\rm cov}(Y_0)}$ for *every* such mark, with constants independent of the region and torus. The marked expansion of FLUCTUATION Theorem 3.4 therefore bounds its term at $Y$ by $C_{\rm PE}K_0\beta_k^{-m-2}e^{-\kappa_a d^{\rm cov}_{k+1}(Y\bmod\Omega^c)}$. The determinant difference $-\delta D^{(k)}$ of P5 (2.41) is estimated from the localized square-root difference of P5 (2.34): the latter is at most $C_{\rm sqrt}e^{-\gamma_wD_k}\le e^{-\hat R_k}\le\beta_k^{-m-4}$ by LOC I-4c on the chosen collar and (Λ29); its trace expansion by LOC V3 and Lemma AE contributes at most $\beta_k^{-m-3}e^{-2\kappa d^{\rm cov}}$. Enlarge the fixed coefficient to $C_*:=C_{\rm PE}K_0+1$ and lower the rate to $\kappa_b$. Since $\beta_{k+1}\le2L^{d-2}\beta_k$, the inequality $\beta_k\ge2C_*(2L^{d-2})^{m+1}$ implies
$$C_*\beta_k^{-m-2}\le\tfrac12\beta_{k+1}^{-m-1}.$$
This is an eventual condition on $\lambda_*$ and replaces the old (Λ29) second inequality. The argument covered the full marked expectation, so it also covers $Y\subset\Omega''_{k+1}$. On these domains every ingredient of the mark and of Theorem 3.4 is the whole-torus ingredient by their locality clauses (FLUCTUATION §3.5(d)); the coefficient and bound are identical, not inferred from a domain difference. For $n<m$, P5 (3.10)–(3.11) have marked terms of size at most $C_{\rm PE}K_0\beta_k^{-n-1/2}e^{-\kappa_a d^{\rm cov}}$ by FLUCTUATION §3.5(e); $\beta_k^{1/2}\ge2C_{\rm PE}K_0(2L^{d-2})^n$ gives $\frac12\beta_{k+1}^{-n}$. Terms disjoint from $\Omega_{k+1}$ are unchanged and retain their original H4 bound. Integration over the compact interpolation interval preserves all bounds. $\square$

*Status.* The coefficient proof is complete from the named FLUCTUATION estimates. The latter still depend on (Vmod) and the auxiliary-cover verification identified in FLUCTUATION §§2.7 and 3.3; LF-3 remains conditional at those inputs.

### IV.1.3 Proof of Theorem IV.1.1

*Cited inputs.* P5 §2 (pp. 501–512: the decompositions (2.5)–(2.14), (2.42)–(2.45), the substitution (2.20), (2.39), the operator (2.47), the formula (2.48)) and §3 (pp.
512–521: the fluctuation integral, Propositions 3.1–3.4, the formula (3.18)); P6 §2 (pp. 3–15: the renormalization, (2.11)–(2.33), Propositions 2.1–2.4) and §3 (pp. 15–21: (3.1)–(3.11));
P6 §4 (localization expansions); I-1, I-2 (landed), I-4, I-5 (LOC), I-7, I-8, I-9 (SF; with the $\nu$-free RG system of CHK §2); PE (POLYMER). The large-field parts are written out in
Lemmas IV.1.2–IV.1.8 and Part II.

*(a).* $\int T^{(k)}\rho\,d\theta=\int\rho\,d\psi_k$ (P1 (1.11)) and the Jacobian $z^N_{k+1}$ per block. *(c), (D1).* Insert into $T^{(k)}\rho$ the decompositions of P5 §2 on the small-field region
$Z^c_k$ of each history (P5 (2.1)–(2.14), (2.42)–(2.45)), perform the fluctuation integral on $\Omega''_{k+1}$ (P5 §3) and the renormalization (P6 §2), and collect: for every history
$\mathbb A$ of $\mathrm{rep}$ and every step record, the term is (D1) at scale $k+1$ with $\mathbb T^{\rm pre}_{k+1}=(K_k,b_k)\circ\bigotimes_Y\mathbb T_k(Y)$ (P6 (3.3) [checked, p. 16]; Definition II.5.8), where the
step kernel is P5 (2.47)·P6 (3.2) with the main action rewritten by Lemma IV.1.3, the hull closure applied (R8; the hull cubes join the large-field region with their $\psi_{k+1}$ as output
variables and their fluctuation integrated, Lemma II.5.12), and $b_k$ collects the vacuum constants, $\mathcal B^{(k)}$ (P6 (3.3)), the renormalization terms of P6 (2.31), the terms of P6
p. 14 with domains in $Z_{k+1}$ and the $\Delta(Y)$ with $Y$ in one component. The factorization over components is Lemma II.5.9, which uses only the supports, and these are those of
Lemma II.5.9 for the constructed data (Lemma IV.1.3: $\Delta(Y)$ with $Y$ inside a component is local to it). Every admissible step record occurs, since the decompositions expand $1$.
*(D2), (e).* I-9 on $Z^c_{k+1}$ with P5's subdomain form; the reduced-symmetry terms by Lemma IV.1.8. *(D3).* $\chi_{k+1}(Z^c_{k+1})$ is the product left by the $\mathsf S$-decomposition (P6
(2.1)–(2.7), Proposition 2.4). *(D4), (d).* (S0): P6 (2.33) [checked, p. 15] gives $|\mathcal B^{(k)}(Z^c_k\cap Z_{k+1})|<{\rm const.}B_0(\cdots)$, the other parts of $b_k$ are $O(\log\beta_k)$ per unit volume
(vacuum constants, P7 p. 520) or $O(1)$ (P6 (2.25), Lemma IV.1.3); analyticity and covariance are those of the constituents; $b_k$ reads $\psi_{k+1}$ only on $\Omega_{k+1}$. (S1)–(S2): Lemma
II.5.14 (quiet) and Lemma IV.1.4 (non-quiet). (S3): no kept data are created by a step. (S4): Lemma I.3.9 and the locality of the constructions. (S5): Lemma II.5.10 with the
quiet-kernel computation of Definition II.5.7 (quiet) and Lemma IV.1.6 (non-quiet). *(D5).* Lemma II.6.3 (a). *(D6).* For every history of $\mathrm{rep}'$: the hypotheses of LF-2 hold
up to scale $K=k+1$ ((G1), (G2) by Lemmas I.3.7, I.3.8 and (R8); (B) at every step by Lemma II.5.12; (Rg) at scales $\le k$ by (S3) and Definition II.5.11, as in Theorem III.8.9 (b);
(H-λ), (H-T) by Lemma IV.3.3, the tori being admissible; (K) by §I.1.3), so Theorem I.5.4 (i) gives (H6′)$^{\rm pre}$ at $k+1$. *(D7).* Lemma IV.1.5, with $B_0\ge B_{\rm st}+1$ (row 12).
*(D8), (h).* The constructions are local (supports in $V_{Z'}$, resp. in the localization domains) and are given by the same formulas on $\mathbb Z^d$; D-IV.9. *(D9).* $\beta_{k+1}=\beta L^{(k+1)(d-2)}\gamma_{k+1}>BL^{(k+1)(d-2)}$
(D-IV.10), and $k+1\le k_0$ (D-IV.11). *(f).* Lemma IV.1.5; $C_b$ is defined from P6 (2.33)'s const., the vacuum constants, P6 (2.25), Lemma IV.1.3 and the base
constants of Lemma II.7.7 (b); $C_{15}$ is the constant of P6 (2.31) in the bound (2.11) of P7 (Lemma III.2.2), from the same renormalization formula. *(g).* Lemma IV.1.7. $\square$

---

## IV.2 LF-5: the transfer at $k_0$, the switch to complete backgrounds, and the frozen regime (P5/P6 Theorem 4, repaired)

The sources: P5 p. 500 [checked] ("We start with $\nu_{k_0}$ satisfying $\nu_{k_0}>\frac78L^{-d}\beta^{-1}_{k_0}$ ... we finish when $\nu_k$ satisfies for the first time $\nu_k>\frac78L^{-2}$ ... $k-k_0<\log\beta_{k_0}$.
Because of this the bounds of the large field densities for $k=k_0$ are enough to control all the remaining steps"); P5 Theorem 4 = P6 Theorem 4 [checked, P6 p. 2]: the densities
(1.44) satisfy (H.1)–(H.5), (H.7) and (1.31) with $\ell=1$ "as long as $\nu_k\le1$"; P6's proof of Theorem 4 (pp. 21–22 [checked]), whose last inequality fails as printed (ARCH §4.8;
replaced by LF-2 (ii), Part I §I.5.6); P5 p. 490 and P6 pp. 10–11 [checked] for the switch at $k_0$.

**Lemma IV.2.1 (transfer).** If $k_0\ge1$ is genuine and $\mathrm{IsRep}_{k_0}(\mathsf c,\mathrm{rep},\rho)$, then $\mathrm{IsRep}^\flat_{k_0}(\mathsf c,\mathrm{rep}^\flat,\rho)$, where $\mathrm{rep}^\flat$ is $\mathrm{rep}$ with the window states
discarded ((T7) of §I.4.4).
*Proof.* (D1), (D3)–(D5), (D7), (D8) are the same clauses. (D2)$\Rightarrow$(D2♭): at scales $\le k_0$ both read the backgrounds $\nu$-free (§II.6.3 (iii)); the mass range $0<\nu_{k_0}\le1$
holds since $\nu_{k_0}\le e^{2\epsilon}\beta^{-1}_{k_0}$. (D9)$\Rightarrow$(D9♭) likewise. (D6)$\Rightarrow$(H6♭): the transfer of Part I §I.5.6 ((B.20), (Λ11)) for every component of every history. $\square$

**Theorem IV.2.2 (LF-5: one frozen step).** Assume (A-IV.1)–(A-IV.3) and the cited inputs of §IV.1.3. Let $\max\{k_0,1\}\le k<k_f$ and $\mathrm{IsRep}^\flat_k(\mathsf c,\mathrm{rep},\rho)$. Then there
are $z_{k+1}>0$ and $\mathrm{rep}'$ with $\rho':=z_{k+1}^{N|T^{(k+1)}|}(T^{(k)}\rho)(z_{k+1}\,\cdot)$ such that:
- (a) $\int\rho'\,d\psi_{k+1}=\int\rho\,d\psi_k$ identically in $(h,g)$;
- (b) $\mathrm{IsRep}^\flat_{k+1}(\mathsf c,\mathrm{rep}',\rho')$;
- (c) the histories of $\mathrm{rep}'$ are those of $\mathrm{rep}$ followed by all step records, with $Z_{k+1}:=Z^{(0)}_{k+1}$ (no hull, no $R$; (G2) for $k+1>k_0$), components for the width
  $\omega_{k+1}$, possibly winding around the torus;
- (d) the step data are those of P5 (2.47)·P6 (3.2) with the local backgrounds of mass $\mu_{k+1}=\nu_{k+1}L^{-2(k+1)}$ (complete), and for $k=k_0$ the switch of D-IV.5; they satisfy (S0), (S1),
  (S2) (version 1.2) and (S4); (S3) and (S5) are not required at scales $>k_0$;
- (e) [v1.3: switch] the small-field data of $\mathrm{rep}'$ are the image under FLUCTUATION Theorem 5.3 with complete backgrounds: P4's RG system for $k>k_0$; for $k=k_0$ the two-step switch of FLUCTUATION Lemma 2.9, with the quadratic switching and old-term re-expression added to the zeroth-order data before the ordinary complete-background RG solution;
- (f) [v1.3: P4-04] (D7) holds with the covering size and $B_{\rm st}\le B_0-1$: the proof of Lemma IV.1.5 applies to the frozen geometry with the same chosen radius, and its old terms reaching $\Omega_{k+1}$ obey $\le e^{-\frac\kappa2d_k^{\rm cov}}$ by (Λ28).

*Proof.* As Theorem IV.1.1, with these differences. *The backgrounds.* For $k>k_0$ every background of the step has mass $\mu_{k+1}>0$ and the characteristic functions carry the
$h$-conditions (Definition II.3.2; P5 (1.19) [checked, p. 492]: "if $k\le k_0$ then we omit the last two conditions"). For $k=k_0$ the unrenormalized backgrounds $\phi'_{k+1}(\square';\psi_k,\theta)$
(Definition II.2.7 (ii)) carry the mass $\mu_k=0$ of the input, and the renormalized backgrounds of scale $k_0+1$ carry $\mu_{k_0+1}>0$: the difference solves P6 (2.24) [checked, p. 10]
with the source $f_0\ni\frac{1+2\beta^{-1}_{k+1}b_{k+1}}{1+\beta^{-1}_{k+1}b_{k+1}}\nu_{k+1}(\phi_{k+1}-h)$, which is small because $\beta_{k_0+1}\nu_{k_0+1}\le e^{2\epsilon}L^d$ (D-IV.11; P5 p. 490 [checked] has $<\frac98L^d$) and $\frac{27}4L^d\beta^{-1}_{k+1}\varepsilon^{-1}_{k+1}\le r_0$
(P6 p. 10, implied by P4 (5.27), which I-9 already assumes); P6 p. 11 [checked]: "we could divide the operations in the case $k=k_0$ into two steps. In the first step we would include
the external field term into the variational problem for the background configurations, without the renormalization ... These solutions are of the order $O(\beta^{-1}_{k+1,u})$, and we
would include the new term $-\beta_{k+1,u}C^{(k+1)}(Z^c_{k+1})$ into the function $\mathcal E^{(k+1)}_0(Z^c_{k+1})$. In the second step we would perform the usual renormalization operation". In the
large-field region the main action of the new region uses the complete local background (Definition II.2.7 (iv) with $\mu_{k_0+1}$), and the term $\nu_{k+1}\langle\delta\phi_{k+1},\phi_{k+1}-h\rangle$ of P6
p. 14 [checked] goes into $\beta_{k+1}C^{(k+1)}$, hence into $b_k$ ((S0), bounded by a constant per unit volume). *The RG system [v1.3: P4-05, switch].* Apply FLUCTUATION Lemma 2.9 before imposing the renormalization conditions. Its exact chord identity is
$$A^\star_{k+1,u}(\theta,\phi^0)=A^\eta_{k+1,u}(\theta,\phi^\nu)+\tfrac12\langle\delta\phi,(H^\nu+\alpha^\nu)\delta\phi\rangle,\qquad\delta\phi=\phi^0-\phi^\nu.$$
BG Proposition 5.1 gives $|\delta\phi|_{\rm scaled}\le2K_2\nu_{k+1,u}$. Since $\beta_{k+1,u}\nu_{k+1,u}\le e^{2\epsilon}L^d$, the quadratic switching term costs at most $4K_2^2e^{4\epsilon}L^{2d}\beta_{k+1,u}^{-1}$ per unit block. The old $\mathscr E,\mathscr F$ terms are re-expressed at the complete background by their first variation, with the localization and analyticity estimate of FLUCTUATION Lemma 2.9(b). Their sum is placed in the zeroth-order data, so the derivatives of the renormalization conditions with respect to $\xi$ are exactly those of the complete system, matrixInfty. FLUCTUATION Theorem 5.3, Step 7, uses the bound $\eta=B_6K_5(1+C_{\rm sw}L^{2d}\beta^{-1})\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2}$ and the landed rg_step_infty under its hcond, which holds for $\beta\ge\beta_0$ after enlarging $\lambda_*$. It yields $|\xi^{(k)}|_\infty\le C_\xi\beta^{-1}q^{k+1}$, the same bound required by LF-7(d). Theorem 5.3, Step 8, verifies H4, H5 and H7 in the complete convention, which are precisely LF-5(b),(e); the region and operator parts remain supplied by LF-5's other paragraphs. The small-field input is still conditional on FLUCTUATION's auxiliary-cover and localization hypotheses, including (Vmod); Lemma 2.9 removes the separate matrix-perturbation obligation only. *(S2).* Lemma IV.1.4's proof
with the $h$-terms of LF-1 (b) (P6 (3.6)) in the $\mathsf Q$- and $\mathsf S$-factors. *(D6)$\to$(H6♭).* LF-2 (ii), the frozen step of §I.5.6 (inequality (I.6)), for every history, with (B) by
Lemma II.5.12 (whose proof does not use $k\le k_0$) and $K=k+1\le k_f\le\hat k_f$. Winding components are allowed: Lemma V and (4.1) hold on tori and no hull is taken (§I.5.6).
*(D9♭).* $\nu_{k+1}=\nu_kL^2\frac{1+\xi_3}{1+\xi_2}\le\frac78e^{c_\xi/\beta}<1$ for $k<k_f$ (§II.6.3), and $\beta_{k+1}>BL^{(k+1)(d-2)}$ (D-IV.10). $\square$

**Corollary IV.2.3 (the frozen operator bound; the repaired P6 Theorem 4).** Under the hypotheses of LF-2, for $\max\{k_0,1\}\le k\le k_f$, every history and every component $Z$
of $Z_k$, $\sum_{\mathfrak a}\int d\psi_k\!\restriction_Z\int\mu\,|Ke^b||F|\le e^{-p_2(\beta_{k_0})-H_k|Z|_k}\sup\chi^{\rm dom}|F|$, the sum over the localized histories of $Z$ in $\mathfrak A$ (for the conventional $k_0=0$
read $p_2(\beta)$). *Proof.* Lemma II.6.3 (b), (c) with (H6♭). $\square$

This is P5 (1.31) with $\ell=1$ and the frozen threshold $p_2(\beta_{k_0})$ in place of P6 Theorem 4's $p_2(\beta_k)$ (ARCH §4.8: P6's last inequality "$>p_2(\beta_{k+n})$" (p. 22) is false as printed
for long frozen runs; the frozen threshold suffices at the last step because $e^{-p_2(\beta_{k_0})}$ is smaller than any fixed power of $\beta^{-1}_{k_f}$, Lemma IV.4.2).

---

## IV.3 LF-7: the flow, its normalization, and its continuity in $\nu$ (P7 Theorem 5, method form)

**Definition IV.3.1 (the family class, version 1.2; replaces Definition II.6.4 (F-ii), (F-iii); D-IV.8).** Fix $\beta\ge\beta_0$, $h$, the constants, $k\ge1$, and put
$\nu_*(k):=\beta^{-1}L^{-kd}$, so that $k\le k_0(\nu)$ (D-IV.11) and hence $k<k_f(\nu)$ for $\nu\in(0,\nu_*(k)]$. A family $(\mathrm{rep}(\nu),\rho(\nu))_{0<\nu\le\nu_*(k)}$, each member on the admissible tori of its
$\nu$, satisfies $\mathrm{IsRepFam}_k$ (resp. $\mathrm{IsRepFam}^{\rm pre}_k$) iff:
- (F-i) $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep}(\nu),\rho(\nu))$ (resp. $\mathrm{IsRep}^{\rm pre}_k$) for every $\nu$;
- (F-ii) for every finite $A\subset\mathbb Z^d$ the set of localized region histories (on $\mathbb Z^d$, with the $R$-records) of components whose lineage lies in $A$ does not depend on $\nu$;
- (F-iii) **(CONT$^{\rm LF}$ on $\mathbb Z^d$ data.)** For every finite $A\subset\mathbb Z^d$ and every localized datum attached to $A$ in the sense of (D8) — the small-field terms
  $\mathscr E^{(j)}(y,X)$, $\mathscr M^{(j)}(x,X)$, $\mathcal R^{(k)}_n(X)$ with $X\subset A$, the observable layer terms of OBS (O1)–(O3), the step and kept data of the localized histories with support
  in $A$, and the boundary terms $\mathcal B^{(k)}(X,\cdot)$ with $X\subset A$ — the datum depends on $\nu$ only through the running constants $(\beta_j,\nu_j,z_j,E_j)_{j\le k}(\nu)$ and the variable
  $b=\nu h$; outside a Lebesgue-null set of values of its variables (which may depend on the datum) it has a limit as $\nu\downarrow0$; and the bounds (S0)–(S3), (S5), (D7) and those of
  Def-6 hold with constants independent of $\nu$. The running constants have limits as $\nu\downarrow0$.

Changes from version 1.1: the clause is stated on the torus-coherent $\mathbb Z^d$ data, because the admissible tori of $\nu$ ($ML^{\hat k_f(\nu)+1}\mid\ell$) shrink as $\nu\downarrow0$; only the
limit at $0$ is required (the version-1.1 continuity on $(0,\nu_*]$ "for almost every value" fails for indicators with moving thresholds); (F-ii) holds because the radii and the
bookkeeping are a priori (D-IV.2). By (D8) the $\mathbb Z^d$ datum attached to $A$ is the push-forward datum on every admissible torus containing a box around $A$, so it is well defined
for every $\nu$. These are exactly the limits used by `C1Star` (OBS Lemma 5.4, §5.3 (F1)–(F2)).

**Theorem IV.3.2 (LF-7, the flow).** Assume (A-IV.1)–(A-IV.3), $k_f\ge1$, and the cited inputs of §II.7.5, §IV.1.3, Theorem III.10.8 and §IV.2. On the admissible tori
define recursively:
- $(\mathrm{rep}_1,\rho_1)$ by LF-6 (Theorem II.7.10);
- for $1\le k<k_0$: $(\mathrm{rep}^{\rm pre}_{k+1},\rho^{\rm pre}_{k+1})$ by LF-3 (Theorem IV.1.1) from $(\mathrm{rep}_k,\rho_k)$, and $(\mathrm{rep}_{k+1},\rho_{k+1})$ by LF-4 (Theorem III.10.8; the families constructed in
  its proof: Definition III.8.3, Definition III.8.8, (3.26′), Definition III.10.6) from $(\mathrm{rep}^{\rm pre}_{k+1},\rho^{\rm pre}_{k+1})$;
- if $k_0\ge1$: $\mathrm{rep}_{k_0}\mapsto\mathrm{rep}^\flat_{k_0}$ (Lemma IV.2.1);
- for $\max\{k_0,1\}\le k<k_f$: $(\mathrm{rep}_{k+1},\rho_{k+1})$ by LF-5 (Theorem IV.2.2) from $(\mathrm{rep}_k,\rho_k)$.
Then:
- (a) every step is applicable: its hypotheses hold at its input;
- (b) $\mathrm{IsRep}_k(\mathsf c,\mathrm{rep}_k,\rho_k)$ for $1\le k\le k_0$, and $\mathrm{IsRep}^\flat_k(\mathsf c,\mathrm{rep}_k,\rho_k)$ for $\max\{k_0,1\}\le k\le k_f$;
- (c) $\int\rho_k\,d\psi_k=Z(g)$ for $1\le k\le k_f$, identically in $(h,g)$, $\|g\|_{\ell^1}<1$;
- (d) [v1.3: switch] the running constants $(\beta_k,\nu_k,z_k,E_k)_{1\le k\le k_f}$ are produced by the steps (FLUCTUATION Theorem 5.3 at each step: the $\nu$-free system for $k<k_0$, the two-step switch of Lemma 2.9 followed by the ordinary complete system at $k_0$, P4's complete system
  after), with $\|\xi^{(k)}\|_\infty\le\frac{c_\xi}{4\beta}q^{k+1}$, $q=L^{-2\gamma}$ (SF Theorem 5.3), hence (I.2) with $\epsilon=\frac{c_8q}{1-q}\le\frac1{20}$, $c_8=c_\xi/\beta$;
- (e) for every $k$ the families $(\mathrm{rep}_k(\nu),\rho_k(\nu))_{0<\nu\le\nu_*(k)}$ satisfy $\mathrm{IsRepFam}_k$ (Definition IV.3.1), and the running constants $\xi^{(k)}(\nu)$ and the observable layer
  $\mu_j(\nu;x)$, $R^{ij}(\nu)$ (OBS (O1)–(O3)) have limits as $\nu\downarrow0$;
- (f) at $k_f$, Corollary IV.2.3 holds: $\sum_{\mathfrak a}\int|\mathbb T_{k_f}F|\le e^{-p_2(\beta_{k_0})-H_{k_f}|Z|_{k_f}}\sup\chi^{\rm dom}|F|$.

*Proof.* Induction on $k$. *Causality.* Every object at scale $k$ uses the running constants up to $k$ only (§II.1.4), and the bookkeeping, the radii (D-IV.2), the regime index $k_0$
(D-IV.11), the horizon $\hat k_f$ and the tori (D-IV.1) are functions of $(\beta,\nu)$ fixed before the flow; so the recursion is well defined. The bound (d) at the steps $j<k$ is
produced by those steps (SF Theorem 5.3 is proved inside the same induction: each step's I-7 bound needs (H.6) at the previous scale, P4 (5.29), SF Theorem 3.2 (b)); it gives (I.2)
at scales $\le k$, which is what Lemma II.1.2 and the analytic estimates of the step $k\to k+1$ use. *(a).* LF-3 needs $\mathrm{IsRep}_k$ and $k<k_0$; LF-4 needs $\mathrm{IsRep}^{\rm pre}_{k+1}$ and
$k+1\le k_0$ directly, hence $\beta_{k+1}\nu_{k+1}\le e^{2\epsilon}$ by Lemma IV.3.3(a) [v1.3: P4-01]; LF-5 needs $\mathrm{IsRep}^\flat_k$ and $k<k_f$ ($\nu_k\le\frac78L^{-2}$); the hypotheses of LF-2 at every scale hold by
Lemma IV.3.3 ((H-λ), (H-T)), Lemma I.3.8 ((G1)), (R8) ((G2)), Lemma II.5.12 ((B)), Theorem III.8.9 ((Rg)) and §I.1.3 ((K)). *(b).* The conclusions of LF-6, LF-3 + LF-4, Lemma
IV.2.1, LF-5. *(c).* LF-6 (a), LF-3 (a), LF-4 (a), LF-5 (a). *(d).* As said. *(e).* LF-6 (e), Lemma IV.1.7, Theorem III.10.8 (f) (with the version-1.2 wording: its proof uses dominated
convergence at the single limit $\nu\downarrow0$ and the uniform convergence of the cluster expansion); the running constants by SF §3.5 (Lemma 3.3 there with (CONT)); the observable
layer by OBS §3.8 (sketched there) and OBS Proposition 4.1 for the steps with $R$. *(f).* Corollary IV.2.3. $\square$

**Lemma IV.3.3 (the a priori regime, horizon and tori; replaces Lemma I.5.6 (b), (c) for the flow).** Let $k_0=\max\{k:\beta\nu L^{kd}\le1\}$ ($0$ if $\beta\nu>1$), $\hat k_f$ as in (I.1),
$\theta=(d-2)\log L$, and assume $\hat\lambda_0\ge\lambda_*$. Then:
(a) $\beta_k\nu_k\le e^{2\epsilon}$ for $k\le k_0$ (when $\beta\nu\le1$) and $\beta_k\nu_k>e^{-2\epsilon}$ for $k>k_0$;
(b) if $k_f\ge1$ then $k_0<k_f$;
(c) (H-λ) for $\lambda=\hat\lambda$, $\theta_\pm=\theta$ and the index $k_0$: $\hat k_f-k_0<\frac d2+\frac{\hat\lambda_{k_0}}{2\log L}<\hat\lambda_{k_0}$ and $\hat\lambda_{\hat k_f}\le\frac d2\hat\lambda_{k_0}+c_H$, $c_H=\frac{(d+3)(d-2)}2\log L$;
(d) (H-T) on every admissible torus: for $1\le k\le k_0$, $n_k=\ell/(ML^k)\ge L^{\hat k_f+1-k}\ge(e^{\hat\lambda_k-1}/a)^{1/2}$, which is $\ge4\nu_{\max}(k)(\mathrm{crit}_k+\omega_k)+4$ by (Λ13).
*Proof.* (a) (I.2): $\beta_k\nu_k=\beta\nu L^{kd}\gamma_k\delta_k$ and $|\log\gamma_k|,|\log\delta_k|\le\epsilon$. (b) $\nu_{k_0}=\nu L^{2k_0}\delta_{k_0}\le e^\epsilon\nu L^{2k_0}\le e^\epsilon(\beta L^{k_0(d-2)})^{-1}\le e^\epsilon\beta^{-1}<\frac78L^{-2}$ by
$\beta\ge\beta_0$ and (Λ12′); $\nu_k$ is increasing, so $k_f>k_0$ (for the conventional $k_0=0$, $k_f\ge1>0$). (c) If $\beta\nu\le1$: $\beta\nu L^{(k_0+1)d}>1$, and if $\hat k_f\ge1$, $\nu L^{2\hat k_f}<1$; so
$L^{2\hat k_f}<\nu^{-1}<\beta L^{(k_0+1)d}$, i.e. $\hat k_f-k_0<\frac{\log\beta+k_0\theta}{2\log L}+\frac d2\le\frac{\hat\lambda_{k_0}-1}{2\log L}+\frac d2$ since $\hat\lambda_{k_0}=\log(\beta a)+1+k_0\theta$; the second inequality is (Λ12).
If $\beta\nu>1$ ($k_0=0$): [v1.3: P4-10] when $\hat k_f=0$, the first bound in (c) is $0<\frac d2+\frac{\hat\lambda_0}{2\log L}$ and the second is $\hat\lambda_0\le\frac d2\hat\lambda_0+c_H$, both immediate since $d\ge3$ and $\hat\lambda_0>0$. When $\hat k_f\ge1$, the minimality of $\hat k_f$ gives $\nu L^{2\hat k_f}<1$, hence $L^{2\hat k_f}<\nu^{-1}<\beta$ and $\hat k_f<\frac{\hat\lambda_0}{2\log L}$. Then $\hat\lambda_{\hat k_f}=\hat\lambda_{k_0}+(\hat k_f-k_0)\theta<\hat\lambda_{k_0}(1+\frac{d-2}2)+\frac d2\theta\le\frac d2\hat\lambda_{k_0}+c_H$. (d) $ML^{\hat k_f+1}\mid\ell$
gives $L^{\hat k_f+1-k}\mid n_k$. For $k\le k_0$, $\beta\nu L^{kd}\le1$ and $\nu L^{2(\hat k_f+1)}\ge1$ give $L^{2(\hat k_f+1-k)}\ge(\nu L^{2k})^{-1}\ge\beta L^{k(d-2)}=e^{\hat\lambda_k-1}/a$. (Λ13) is stated with
$e^{x/2-1}/\sqrt2\le(e^{x-1}/a)^{1/2}$. $\square$

*Remarks.* (1) The step counter and the instantiation of §I.5.7 now use only a priori data: $\hat\lambda$, $\hat R$, $k_0$, $\hat k_f$, and the tori; the running constants enter LF-2 only through
the budgets $G$, which are bounded by Lemma B. (2) Lemma I.5.6 (a) ($k_f\le\hat k_f\le k_f+1$) is still used, for `C1Star`'s $J$ (Lemma IV.5.1).

---

## IV.4 LF-8: the last step (P7 §4, P9 §4)

Throughout, $k:=k_f\ge1$ unless stated otherwise, $J:=k_f+1$, and $(\mathrm{rep}_k,\rho_k)$ is the output of LF-7, so $\mathrm{IsRep}^\flat_k$ holds and $\nu_k>\frac78L^{-2}$.

### IV.4.1 The final integration

The last step is P7 §4 [checked, pp. 529–533]: the steps of P5 §2–3 and P6 §2 are repeated with $\int d\psi_k$ in place of $T^{(k)}$, *without* the decompositions (2.6) [5] and (2.1) [6]
("so $\Omega_{k+1}=\Omega'_{k+1}$ by (2.9) [5]"; "(2.2)–(2.7) [6] have a simpler form with $\mathsf S_{k+1}=\varnothing$"), so the last record has $\mathsf P=\mathsf S=\varnothing$ and arbitrary $\mathsf Q,\mathsf R$ (Definition I.3.1
with $\mathsf P=\mathsf S=\varnothing$); the variational problem (4.3) is massive because $\nu_k>\frac78L^{-2}$ (P2 Proposition 4.1 applies, P7 p. 530: "it has a unique solution", the space "is a small
neighbourhood of the constant configuration equal to $h$"); the characteristic functions restrict $|\psi_k-h|<(5L+3)\delta_k$ (P4 (6.2) [review]); the new effective action is not
renormalized (P7 p. 531). The covariance of the final fluctuation integral is the massive $A^{-1}_k$ (D-IV.6), and the representation (4.9) of P7 has the operators $\mathbb T'_{k+1}(Z_{k+1},\mathbb A'_{k+1})$,
which are integrations with no free variable (P7 p. 531: "its value is independent of any spin variable").

**Lemma IV.4.2 (the budget of the last step; P7 (4.10) with the frozen threshold).** Measure the volumes of the last step in scale-$(k+1)$ units and put
$H^{\rm fin}_{k+1}:=H_0(\log\beta_k+(d-2)\log L)$ (the value $H_0\log(\beta_kL^{d-2})$ of the unrenormalized coefficient). For every multi-index of the last step and every component $Z'$ of the
final large-field region $Z'_{k+1}$, the budget $G'(Z')$ (Definition II.5.11 with the last-step one-step bound and $H^{\rm fin}_{k+1}$) satisfies $G'(Z')\ge\frac12A_2\hat\lambda_{k_0}^{p_2}$. Consequently,
summing over the multi-indices with the same $Z'$,
$$\sum\big|\mathbb T'_{k+1}(Z',\cdot)F\big|\ \le\ e^{-\frac12p_2(\beta_{k_0})-H^{\rm fin}_{k+1}|Z'|_{k+1}}\,\sup|F|,\qquad\text{for all }\|g\|_{\ell^1}<1.\tag{IV.4.1}$$
*Proof.* *(B) at the last step.* Lemma II.5.12's computation with $H^{\rm fin}_{k+1}$ in place of $H_{k+1}$: the old-volume bracket uses $H_k-L^{-d}H^{\rm fin}_{k+1}=H_0[(1-L^{-d})\log\beta_k-L^{-d}(d-2)\log L]\ge M^{-d}$ by
(Λ16); the gain and the new volume are unchanged ((S2) at the last step is P6 (3.4)–(3.9) with $\mathsf P=\mathsf S=\varnothing$, as in Lemma IV.1.4). *The invariant.* If $k_f+1\le\hat k_f$, LF-2 (ii)
with $K=k_f+1$ gives (H6♭) at $k_f+1$. If $k_f=\hat k_f$, take one more frozen step from (H6♭) at $k_f$ (where $W_{k_f+1}(\hat k_f)=0$): the computation of Lemma I.5.5 with $\tau_{t^*}$ replaced by
$A_2\lambda_{k_0}^{p_2}$ gives $G'(Z')\ge A_2\hat\lambda_{k_0}^{p_2}+2\sigma_{k+1}\ell(\Gamma(Z'))-w_{k+1}$, provided $(m-1)A_2\hat\lambda_{k_0}^{p_2}+g_kr\ge(m+r-1)E_{k+1}$ (the inequality (I.6) without its $W$-terms), which
holds by (Λ11) because $\hat\lambda_{k+1}\le\hat\lambda_{\hat k_f}+\theta\le d\hat\lambda_{k_0}$ ((Λ30)); and $w_{k+1}\le C_w(d\hat\lambda_{k_0})^{2d+1}\le\frac12A_2\hat\lambda_{k_0}^{p_2}$ by (Λ11). In both cases $G'\ge\frac12A_2\hat\lambda^{p_2}_{k_0}\ge\frac12p_2(\beta_{k_0})$
(Lemma II.1.2 (b)). (IV.4.1) is Lemma II.6.3 (b) for the last step. $\square$

**Theorem IV.4.1 (LF-8 (a); P7 (4.9)–(4.17), P9 (4.4)–(4.7)).** Assume (A-IV.1)–(A-IV.3), $k_f\ge1$, (Λ30)–(Λ31), row 13 as amended, and the cited inputs listed in the
proof. On every admissible torus,
$$\int\rho_k\,d\psi_k=\exp\Big[-E_{k+1,0}|T^{(k+1)}|+\mathscr F_{k+1,0}(h,g)+\mathcal R^{(k+1)}(h,g)\Big],\qquad\mathcal R^{(k+1)}=\sum_{n=1}^m\mathcal R^{(k+1)}_n+\mathcal P^{(k+1)},\tag{IV.4.2}$$
where:
- $\mathscr F_{k+1,0}(h,g)=\langle g,h\rangle_1+\sum_{j=1}^k\langle g,\mathscr M^{(j)}(\cdot;h,h,g)\rangle_1+\langle g,\mathscr M^{(k+1)}_0(\cdot;h,g)\rangle_1$ (P7 (4.17) [checked] with $n=0$), $\mathscr M^{(j)}(x;h,h,g)=\sum_{X\ni x}\mathscr M^{(j)}(x,X;h,h,g)$
  with the (H.7) bounds $|\mathscr M^{(j)}(x,X)|<c_9^{\rm flow}L^{-j(\frac{d-2}2+\gamma-\alpha_1)}e^{-\kappa_{\rm flow}d_j^{\rm cov}(X)}$ for $j\le k+1$;
- $\mathcal R^{(k+1)}_n=\sum_Y\mathcal R^{(k+1)}_n(Y;h,g)$, $|\mathcal R^{(k+1)}_n(Y)|\le\beta_k^{-n-1}e^{-\kappa_{\rm flow}d_{k+1}(Y)}$ (P7 (4.9), H4);
- $\mathcal P^{(k+1)}=\sum_{X\in\mathcal D_k}\mathcal P^{(k+1)}(X;h,g)$, $|\mathcal P^{(k+1)}(X)|\le\frac12\beta_k^{-m-1}e^{-\kappa'd_{k+1}(X)}$ with $\kappa'\ge\kappa_{\rm flow}-C_{\rm loss}$, $C_{\rm loss}$ a constant of rows 0–4 (P7 (4.14)
  [checked, p. 532–533]; P9 (4.6) [checked, p. 516] prints $\beta_k^{-2}e^{-2\kappa d_{k+1}(Y)}$, implied for $m\ge1$ up to the rate);
- every localized term is analytic in $g$ on $\|g\|_{\ell^1}<1$ with the stated bound there, depends on $g$ only through its restriction to the localization domain, is jointly
  $O(N)$-covariant, and satisfies (D8);
- with the normalization $\int\rho_k=Z(g)$ of LF-7,
  $$\log\frac{Z(g)}{Z(0)}=\mathscr F_{k+1,0}(h,g)+\mathcal R^{(k+1)}(h,g)-\mathcal R^{(k+1)}(h,0)\qquad(\text{P7 (4.15)–(4.16) with }c_k=1),\tag{IV.4.3}$$
  as an identity of analytic functions on $\|g\|_{\ell^1}<1$, with the principal logarithm on the left (PE §4.6).

*Proof.* *Cited inputs.* P7 (4.1)–(4.9) [checked, pp. 529–531] (the last fluctuation integral by the procedure of P5 §§2–3 and P6 §2 with the changes listed above; P2 Proposition 4.1 =
BG Theorem 5.2 (5) with mass; P4 §6 [review]); I-8 for the massive fluctuation integral (SF §4; the covariance $A^{-1}_k$ is exponentially decaying with rate $\ge c\sqrt{\nu_k}\ge c/L$,
GREEN G-5 with mass); the completion of the small-field functions to the whole torus (P7 (4.11) [checked]). *The large-field sum.* (4.11) is a gas of heavy objects (the components
$Z'$ of $Z'_{k+1}$ with their halos, weights $\tau(Z')=\sum\mathbb T'_{k+1}(Z',\cdot)e^{E_{k+1,0}|Z'|}$, which are numbers depending on $(h,g)$) and couplings (the boundary terms $\mathcal B''^{(k+1)}$:
the old $\mathcal B^{(k)}$ re-expanded in the last integral, the new terms of the integral, and the completion differences; bounded by $B_{\rm cpl}e^{-\kappa d}$ with $B_{\rm cpl}:=B_0+B_{\rm st}+1$).
By (IV.4.1) and $|E_{k+1,0}|\le C'_E\lambda_k+C'_E$ per $k$-block, $|\tau(Z')|\le e^{-p-h\,v(Z')}$, where $v(Z')$ is the number of $\pi_{k+1}$-cubes of $Z'$ (so $|Z'|_{k+1}=M^dv$ and
$|Z'|_k=(LM)^dv$), $p:=\frac12p_2(\beta_{k_0})$ and $h:=M^d\big(H^{\rm fin}_{k+1}-L^d(C'_E\lambda_k+C'_E)\big)\ge(LM)^d\lambda_k$ by row 13 ($H_0\ge2L^d(C'_E+1)$, $\log\beta_k\ge\lambda_k-\frac12$, $\lambda_k\ge2$);
$h\to\infty$ with $\beta$. GAS (PE §2.6; landed `gas_eq`, `gas_activity_bound`, `gas_pe`) applies with $S_0=\varnothing$ and volume weights (PE §3.6,
"P7 §4 with volume weights") once $h\ge B_{\rm cpl}e^{B_{\rm cpl}}e^{\kappa'c}K'_0+\kappa'(c^{\rm PE}_2+c)+c^{\rm PE}_1+2+\ln K''_0$, which is (Λ31) ($B_0$ is chosen before $\lambda_*$); the weights are scalars here, so
the operator-valued version (Lean P10) is not needed. Its output activities are $\le3c_1^{\rm PE}e^{-p}e^{-(\kappa'-2)d}$, and PE-L (landed `pe_blockTorus`, `pe_PY_bound`, `pe_PY_analyticOnNhd`)
exponentiates them into $\mathcal P^{(k+1)}$ with $|\mathcal P^{(k+1)}(X)|\le\alpha e^{-\kappa''d(X)}$, $\alpha=3c^{\rm PE}_1e^{-\frac12p_2(\beta_{k_0})}K_0e^{c^{\rm PE}_1+\kappa c}\le\frac12\beta_k^{-m-1}$ by (Λ31) (since
$\log\beta_k\le\hat\lambda_k\le\hat\lambda_{\hat k_f}\le d\hat\lambda_{k_0}$, Lemma IV.3.3 (c), and $p_2>1$). The comparison of the Steiner size with $d_{k+1}$ is PE §3.6. Analyticity, locality in $g$ and
covariance: PE (c), (d) and the corresponding properties of the weights ((S0), (D7), the coset average of LF-4 for the $\mathcal R''$-terms inside $\mathcal R_n$, Lemma III.9.6 (c)); torus
coherence: PE (f) and (D8). *(IV.4.3).* $\log\int\rho_k=\log Z(g)$ by LF-7 (c); evaluate (IV.4.2) at $g$ and at $0$, use $\mathscr F_{k+1,0}(h,0)=0$ (every term carries a factor $g$), and
identify the analytic logarithms as in PE §4.6 (both sides are analytic on the convex domain, exponentiate to $Z(g)/Z(0)$ and vanish at $g=0$). $\square$

*What LF-8 (a) changes in P7 §4.* (i) The operator bound (4.10) is used with the frozen threshold $\frac12p_2(\beta_{k_0})$ and the last-step coefficient $H^{\rm fin}_{k+1}$ (Lemma IV.4.2), not with
$p_2(\beta_k)$; the GAS condition $e^{-p}\cdot{\rm const}\le\frac12\beta_k^{-m-1}$ holds because $\log\beta_{k_f}\le d\hat\lambda_{k_0}$ (ARCH §4.8). (ii) P7's parameter $\varepsilon$ and the assumption "$H_0$ sufficiently
large" (p. 532) are replaced by the explicit GAS constants and by row 13 with $\lambda_*$. (iii) No loss bookkeeping of D3 Lemma 15 is used (LFR-12).

### IV.4.2 The case $k_f=0$

[v1.3: P4-06] Proposition IV.4.3 below is superseded by notes/phase1/LF-BASE-KF0.md (in preparation). Its stated interface is retained for LF-8 and Root-F.

**Proposition IV.4.3 (LF-8 (b); sketched).** If $k_f=0$ ($\nu>\frac78L^{-2}$), then for $\beta\ge\beta_0$, on every admissible torus ($ML^{\hat k_f+1}\mid\ell$, $\hat k_f\in\{0,1\}$),
$$\log\frac{Z(g)}{Z(0)}=\langle g,h\rangle+\sum_x\sum_X\big\langle g(x),T_1(x,X;g)\big\rangle,$$
the sum over the scale-$1$ polymers $X\ni x$ ($ML$-blocks), with $T_1(x,X;\cdot)$ analytic on $\|g\|_{\ell^1}<1$, depending on $g\restriction_X$, torus coherent, and
$|T_1(x,X;g)|\le C\beta^{-1}e^{-\kappa_{\rm flow}|X|_\#/C_{d,L}}$ on $\|g\|_{\ell^1}\le\frac12$; and the one- and two-point functions have the form of Proposition IV.4.4 with $J=1$ and $\gamma_0=1$.
*Route.* (i) Decomposition of unity on $\rho_0$ per $\pi_1$-cube with the bond and site conditions of Definition II.7.1 ($B(\square')$, with the site condition $|\phi_x-h|<\delta_0\nu^{-1/2}$; there is no
block variable). (ii) A violated condition gives $e^{-p_0(\beta)^2/(9a)}$ from the Gibbs factor (Lemma II.7.8's bond and site witnesses), so a large-field cube carries $e^{-2A_3(\log\beta)^{2p_0}}$.
(iii) On the small-field cubes the spins are within $\delta_0\nu^{-1/2}\le2L\delta_0$ of $h$; the chart of Lemma II.7.4 around the constant $e=h$ (no background, no variational problem)
and Lemma II.7.3 with $\phi^{\rm b}\equiv h$, $\alpha=0$ ($h$ is the exact minimiser of $H$) give the quadratic form $\beta\langle\xi,(-\Delta+\nu)\xi\rangle$ on $h^\perp$, massive with $\nu>\frac78L^{-2}$, so the
covariance decays at rate $\ge c\sqrt\nu$ per lattice unit, i.e. $\ge cM$ per $\pi_1$-cube; the interaction consists of the chart terms only. (iv) The fluctuation integral is expanded by
I-8 (SF §4) at the unit scale with this covariance (or by MY + PE-L after a finite-range decomposition of the massive covariance), and the large-field cubes are summed by GAS
with the volume decay of (ii); one PE-L application (`pe_blockTorus`) exponentiates. The terms are localized in scale-$1$ polymers, of size $O(\beta^{-1})$. (v) The observable
form (OBS §5.1, "the cases $k_f=0$ and $k_f=1$ are folded into LF-6, LF-8 (b)"): the Gaussian term is $\beta^{-1}(-\Delta+\nu)^{-1}(I-h\otimes h)=\beta^{-1}[T_0+P_1A_1^{-1}P_1^\top](I-h\otimes h)$ in plain
units (Woodbury, OBS (5.3)), with $\gamma_0=1$. *Status:* sketched (ARCH LF-8 (b) has the same outline); no source treats this case.

### IV.4.3 The one- and two-point functions (P9 (4.7)–(4.9) with the massive final covariance)

**Proposition IV.4.4 (P9 §4 in the reconstructed form; sketched, with the decomposition proved from Theorem IV.4.1).** Let $k_f\ge0$, $J=k_f+1$, and let the flow carry the
observable layer $\mathcal O_k$ of OBS §2.1 ((O1)–(O5)) at every scale (OBS Theorem 3.1 for the steps, Proposition 4.1 for $R$, D-IV.6 for the last step). Then on every admissible torus
$$M_\ell(x)=m_J(x)h+\partial_{g(x)}\big[\mathcal R^{(J)}+\mathcal P^{(J)}\big](h,0),\qquad G_\ell(x,x')=G_J(x,x';h,h)+\partial^2_{g(x)g(x')}\big[\mathcal R^{(J)}+\mathcal P^{(J)}\big](h,0)\tag{IV.4.4}$$
(P9 (4.8)–(4.10) [checked, pp. 516–517]; by Lemma 0.1 of CORR and (IV.4.3)), where $G_J=C_J+R_J$ and the last summand of $C_J$ is massive:
$$C_J(x,x';h,h)=m_J(x)m_J(x')\Big[\sum_{j<k_f}(\beta\gamma_j)^{-1}T_j^{\ell,\nu\delta_j}(x,x')+(\beta\gamma_{k_f})^{-1}\big(P_{k_f}A^{-1}_{k_f}P^\top_{k_f}\big)(x,x')\Big](I-h\otimes h),\tag{IV.4.5}$$
and $P_{k_f}A^{-1}_{k_f}P^\top_{k_f}=T_{k_f}+E_{\rm tail}$, $E_{\rm tail}:=P_JA^{-1}_JP_J^\top\ge0$ (OBS (5.3)), $|E_{\rm tail}(x,y)|\le C_GL^{-J(d-2)}e^{-\delta_GL^{-J}|x-y|}\le C_G2^{d-2}\nu^{(d-2)/2}e^{-\frac{\delta_G}{L^2}\sqrt\nu|x-y|}$
(GREEN G-5 extended to the masses of CORR D-03; $\frac12\le L^J\sqrt\nu\le L^2$). The remainders obey $|\partial_{g(x)}[\mathcal R^{(J)}+\mathcal P^{(J)}](h,0)|\le6K_0^{\rm O}\beta_{J-1}^{-2}$ and
$|\partial^2_{g(x)g(x')}[\cdots]|\le C\beta^{-2}_{J-1}e^{-\frac12\delta_0L^{-J}|x-x'|_1}$ for $\ell\ge\ell_0(\nu,x)$ (OBS Lemma 3.2; OBSR O-02 for the winding terms on small tori).
*Status.* (IV.4.4) is proved from (IV.4.3) by differentiation (CORR Lemma 0.1, OBS Lemma 3.2). The structure of $G_J$ and $M_J$ is the observable layer (OBS (2.3)–(2.6), Lemma 2.1;
sketched there, OBS Theorem 3.1); the massive last term is OBSR Q2: P9 prints the regular $C^{(j)}_{tr}$ in (4.14) for every $j$ including the last, which we read as the massive one, as P9 p. 515
[checked] requires ("a quadratic form with a massive covariance, the mass $\approx v_k\approx L^{-1}$", and "we have performed now all the integrations down to 0-momentum"). In `C1Star`
the tail $(\beta\gamma_{k_f})^{-1}m_Jm_JE_{\rm tail}$ is part of $r_{tr}$ (D-IV.6; it is never zero, OBSR O-01).

**Remark IV.4.5 (replacement of OBS (L4); open item O-II-9).** OBS §4.1 assumed "(L4) the integral operators $\mathbb T_k$ do not depend on $g$". By Definition II.5.2 (audit P2-04) they do,
through the factors $e^b$ of their kernels. The replacement is **(L4′)**: *the large-field operators depend on $g$ only through the factors $e^{b}$ ((S0), (S3)), analytic in $g$ on
$\|g\|_{\ell^1}<1$ with the bounds of (S0), (1.26) uniform on the polydisc; their $g$-dependence never enters the small-field functions $\mathscr F_k$ or the observable layer, and reaches
$\log Z$ only through the boundary terms and the polymer activities $\mathcal R''^{(j)}_m$ (inside $\mathcal R_n$, then $\mathscr E,\mathscr M$ after $m$ steps) and $\mathcal P^{(J)}$, whose $g$-derivatives are
bounded by OBS Lemma 3.2 from their sup bounds on the polydisc.* This is all that OBS §§4–5 use: (L4) was invoked only in the last step (OBS §4.1: "(L4)–(L5) only in the last step"),
where the operators are inside the activities of $\mathcal P^{(J)}$, which Theorem IV.4.1 bounds on the whole polydisc. The edit to `OBSERVABLES.md` is §4.1 item (L4) and the sentence
after it; the proof of OBS Theorem 5.2 is unchanged.

---

## IV.5 The final assembly: Root-F and `RootFAndC1Star`

### IV.5.1 Scales and terms

**Lemma IV.5.1 (the scales of Root-F and of `C1Star`).** Let $\beta\ge\beta_0$ and $\nu\in(0,1]$.
(a) $\mathrm{kf}:=\hat k_f(\nu)$ satisfies Root-F's bounds $L^{\mathrm{kf}}\sqrt\nu\le L$ and $\frac12\le L^{\mathrm{kf}+1}\sqrt\nu$, and the tori with $ML^{\mathrm{kf}+1}\mid\ell$ are the admissible tori (A-IV.3).
(b) The flow's last scale satisfies $k_f\le\hat k_f\le k_f+1$; for $k_f=0$, $\hat k_f\le1$.
(c) $J(\nu):=k_f(\beta,\nu)+1$ satisfies $1\le J$, $J(\nu)\to\infty$ as $\nu\downarrow0$, $\frac12\le L^{J}\sqrt\nu\le L^2$, and $ML^{J+1}\mid\ell$ implies that $\ell$ is admissible.
*Proof.* (a) If $\hat k_f\ge1$, $\nu L^{2\hat k_f}<1$, so $L^{\hat k_f}\sqrt\nu<1\le L$; if $\hat k_f=0$, $\sqrt\nu\le1\le L$. $\nu L^{2\hat k_f+2}\ge1$ gives $L^{\hat k_f+1}\sqrt\nu\ge1$. (b) Lemma I.5.6 (a) for $k_f\ge1$; for
$k_f=0$, $\nu>\frac78L^{-2}$ gives $\nu L^4>\frac78L^2\ge1$. (c) $\nu_{k_f}=\nu L^{2k_f}\delta_{k_f}>\frac78L^{-2}$ and $\delta_{k_f}\le e^\epsilon$ give $L^{2J}\nu>\frac78e^{-\epsilon}>\frac14$; if $k_f\ge1$, $\nu_{k_f-1}\le\frac78L^{-2}$ gives
$L^{2k_f}\nu\le\frac78e^\epsilon<1$, so $L^J\sqrt\nu<L$; if $k_f=0$, $L^J\sqrt\nu=L\sqrt\nu\le L$. $L^J\ge(2\sqrt\nu)^{-1}\to\infty$. Finally $\hat k_f+1\le J+1$ by (b). $\square$

**Definition IV.5.2 (the terms $T_j$ of Root-F; D-IV.7).** Let $\ell$ be admissible, $h\in S^{N-1}$, and let the flow of LF-7 and the last step of LF-8 be given (Proposition IV.4.3 if $k_f=0$).
For a scale-$j$ polymer $X$ (Def-2 `IsPolymer d ℓ (M * L ^ j) X`; equivalently $X\in\mathcal D_j$ as a set of $\pi_j$-cubes, §I.2.8) and $x\in X$:
- for $1\le j\le k_f$: $T_j(x,X;g):=\mathscr M^{(j)}(x,X;h,h,g)$, the localized (H.7) term of scale $j$ at the constant configuration $\psi^{(j)}=h$ (the terms $\mathscr M^{(j)}$ are not changed after
  their creation, P4 (1.8); the contributions $\mathcal R''^{(i)}_m$ of $R$ reach them after $m$ steps, P5 pp. 491–492);
- for $j=k_f+1$: $T_{k_f+1}(x,X;g):=\mathscr M^{(k_f+1)}_0(x,X;h,g)+\sum_{f}\sum_{Y:\bar Y=X,\ Y\ni x}\int_0^1\partial_{g(x)}f(Y;h,tg)\,dt$, where $f$ runs over the polymer terms $\mathcal R^{(k_f+1)}_n$ ($1\le n\le m$) and
  $\mathcal P^{(k_f+1)}$ of (IV.4.2), $Y$ over their localization domains, and $\bar Y$ is the union of the scale-$(k_f+1)$ blocks meeting $Y$ (a scale-$(k_f+1)$ polymer); the inner sum over $f=\mathcal R_n$ is
  P7's $\mathscr M^{(k_f+1)}_n(x,X)$ of (4.15)–(4.17);
- for $k_f=0$: $T_1$ of Proposition IV.4.3;
- $T_j(x,X;g):=0$ in all other cases (in particular for $k_f+1<j\le\hat k_f+1$, for $x\notin X$, and for non-polymers). On non-admissible tori $T:=0$.

### IV.5.2 Root-F

**Theorem IV.5.3 (Root-F from the flow).** Assume the cited inputs listed in §IV.5.4. Then `Balaban.logPartition_multiscale` holds, with the following choices:
$\delta:=\frac18$ ($=\gamma/2$, $\gamma=\frac14$); for given $\kappa,c_9>0$: $L:=\max\{L_0,3\}$ (row 3), $\kappa_{\rm flow}:=\max\{C_{d,L}(\kappa+1)+C'_{d,L},16\kappa_0+16,\ 2(4+\log(2(2d)^2 2^{2d+1}))\}$ (row 5 as amended), $M:=L^{m_0}M_1$ with
$M_1$ from row 6 (with $\kappa_{\rm flow}$), the rows 7–15 as in §I.1.3, $c_9^{\rm flow}:=\min\{c^{\rm P4}_9,\frac12c_9e^{-\kappa_{\rm flow}}\}$ (row 10), $\lambda_*$ satisfying all the conditions (Λ0)–(Λ32), and
$\beta_0:=\max\{e^{\lambda_*-1}/a,2B\}$; for given $\beta\ge\beta_0$, $\nu\in(0,1]$, $h$: $\mathrm{kf}:=\hat k_f(\nu)$ and $T$ of Definition IV.5.2.

*Proof.* Clause by clause (the frozen statement's order; Table IV.5.5 lists the sources).
1. *Bounds on kf:* Lemma IV.5.1 (a).
2. *Vanishing off polymers:* Definition IV.5.2 ($j\le k_f+1\le\hat k_f+1$ by Lemma IV.5.1 (b)).
3. *Locality in $g$:* the (H.7) terms depend on $g\restriction_X$ (P4 (H.7), the localization of $\mathscr F^{(j)}$, SF §1.3); the polymer terms $f(Y;\cdot)$ depend on $g\restriction_Y$ (PE (c) and the locality of the
   weights: (S0), (D7), LF-4's (c), (e)), and $\partial_{g(x)}f(Y;tg)$ on $g\restriction_Y\subset g\restriction_X$.
4. *Analyticity on $\|g\|_{\ell^1}<1$:* (H.7) and PE (d) (`pe_PY_analyticOnNhd`); the $t$-integral of $\partial_{g(x)}f(Y;tg)$ is analytic because the $\ell^1$-ball is convex and contains $tg$, and
   the integrand is jointly continuous and analytic in $g$.
5. *Bounds on $\|g\|_{\ell^1}\le\frac12$:* for $j\le k_f$, $|\mathscr M^{(j)}(x,X)|<c^{\rm flow}_9L^{-j(\frac{d-2}2+\gamma-\alpha_1)}e^{-\kappa_{\rm flow}d_j^{\rm cov}(X)}$ (Theorem IV.4.1), $\gamma-\alpha_1\ge\delta$ (row 10), and the
   conversion $d_j^{\rm cov}(X)\ge|X|_\#/C_{d,L}-1$ (FLUCTUATION Lemma 1.2 (G1), PE §3.6) gives $\le c^{\rm flow}_9e^{\kappa_{\rm flow}}L^{-j(\frac{d-2}2+\delta)}e^{-(\kappa+1)|X|_\#}\le c_9L^{-j(\frac{d-2}2+\delta)}e^{-\kappa|X|_\#}$, with $|X|_\#=|X|/(ML^j)^d$. For
   $j=k_f+1$: the term $\mathscr M^{(k_f+1)}_0$ as before; for the polymer terms the Cauchy estimate on the disc of radius $\frac12$ in the coordinate $g_i(x)$ (PE §4.4) gives
   $|\partial_{g_i(x)}f(Y;tg)|\le2\sup|f(Y)|$, the bounds of (IV.4.2) give $\sup|f(Y)|\le\beta_{k_f}^{-2}e^{-\kappa'd_{k_f+1}^{\rm cov}(Y)}$ (for $m\ge1$), the number of $Y$ with $\bar Y=X$ is $\le2^{L^d|X|_\#}$, and
   $d_{k_f+1}^{\rm cov}(Y)\ge|X|_\#/C_{d,L}-1$; with $C'_{d,L}:=C_{\rm loss}+C_{d,L}L^d\log2$ (so $\kappa'/C_{d,L}\ge\kappa+L^d\log2$) and $\beta_{k_f}^{-2}\le4\beta^{-2}L^{-2k_f(d-2)}\le\frac{c_9}{8N(m+1)}e^{-\kappa_{\rm flow}}L^{-(k_f+1)(\frac{d-2}2+\delta)}$ ((Λ32); $2(d-2)k_f\ge(k_f+1)(\frac{d-2}2+\delta)$
   for $k_f\ge1$, $d\ge3$, $\delta=\frac18$), the bound follows. For $k_f=0$: Proposition IV.4.3 and (Λ32).
6. *The identity:* (IV.4.3) and, for every polymer term, $f(Y;g)-f(Y;0)=\int_0^1\frac{d}{dt}f(Y;tg)\,dt=\sum_{x\in Y}\langle g(x),\int_0^1\partial_{g(x)}f(Y;tg)\,dt\rangle$ (chain rule; $\partial_{g(x)}f(Y)=0$ for $x\notin Y$); the terms
   $\langle g,\mathscr M^{(j)}\rangle_1$ are already of the form $\sum_x\sum_{X\ni x}\langle g(x),T_j(x,X;g)\rangle$; the principal logarithm by PE §4.6. For $k_f=0$: Proposition IV.4.3.
7. *Agreement of two tori:* for $A$ in the box $\{|y_\mu|<\min(\ell,\ell')/4\}$, every term attached to the image of $A$ is the push-forward of the same $\mathbb Z^d$ datum on both tori: the
   (H.7) terms and the polymer terms by (D8) (version 1.2, D-IV.9; the box has side $<\ell/2$), PE (f) (transport) and PE §4.5; the running constants, $k_f$ and $J$ do not depend on the torus
   (they are defined from $\mathbb Z^d$ data: the renormalization conditions (H.5) use $\lim_{T\to\mathbb Z^d}$, SF §1.3); the regrouping $Y\mapsto\bar Y$ is the same inside the box; the evaluation of $g$
   through `valMinAbs` is the identification of the box with its image. $\square$

### IV.5.3 `RootFAndC1Star`

**Theorem IV.5.4 (`RootFAndC1Star d N hN`, exactly as in `Balaban/Correlations/C1Star.lean` after W34).** Assume the cited inputs listed in §IV.5.4. Then
`RootFAndC1Star d N hN` holds with: $\delta:=\frac18$; $L,M$ the integers of Theorem IV.5.3 at $\kappa=\kappa_*:=$ `kappaStar d` $=2\log(8d^2)$ and $c_9=1$ ($L\ge3$ by row 3); $\beta_0$ of Theorem IV.5.3
there; and the following instance of `C1Star d N L M hN`:
- `a` := the free-flow kernel constant $a\in[\frac9{10}(1-L^{-2})^{-1},\frac32)$ (SF §1.1), which satisfies `a_range`;
- `γ₀` := $\gamma=\frac14$ (so `rate L γ₀` $=q=L^{-2\gamma}$ of SF Theorem 5.3);
- `cXi` := $c_\xi=4C_\xi$, $C_\xi=168B_6K_5/\alpha_0^2$ (SF Theorem 3.2; rows 6b, 11);
- `ρ₀` := $\gamma$, `ρ₁` := $4\rho_2$ with $\rho_2:=\frac12\min\{\frac{\frac{d-2}2-\gamma}{3(d-2)},\frac\gamma{2(d-2)},\frac{1-\gamma}{2(d-2)}\}$ (OBS Lemma 1.1 with OBSR O-04, O-05);
- `cPrime` := $\frac14L^{-2}\min\{\delta_0^{\rm O},\delta_G\}$ ($\delta^{\rm O}_0=\kappa/M$ of P9 p. 509, $\delta_G$ of GREEN G-5; OBS §5.3 with the halving of OBSR's F-B);
- `cStar` := the constant $c_*$ of OBS Theorem 5.2 with the amended (F2), (F3) (it collects $K^{\rm O}_0$, $C_G$, the constant $K$ of OBSR O-04, $24K^{\rm O}_0L^{2(d-2)}$ and the $C(d,c')$ of F-B);
- `βStar` := $\max\{\beta_0,\beta_0^{\rm O}\}$, $\beta_0^{\rm O}$ the threshold of OBS Theorem 5.2;
- `data β`: $J:=k_f+1$ (Lemma IV.5.1 (c)); $\xi(\nu,k):=\xi^{(k)}(\nu)$ of the flow for $\nu\in(0,1]$, $k<k_f(\nu)$, $:=0$ for $k\ge k_f(\nu)$, and $\xi(0,k):=\lim_{\nu\downarrow0}\xi(\nu,k)$ (SF §3.5 convention);
  $\mu(j,\nu,x):=\mu_j(\nu;x)$ (OBS (O1)) for $1\le j\le J(\nu)$, $:=0$ for $j>J(\nu)$, $\mu(j,0,x):=\lim_{\nu\downarrow0}$; `em ℓ ν x` $:=$ `blockM` $-$ `magJ` (by subtraction); `rtr ℓ ν x y` $:=$ `blockGtr` $-$
  `magJ x * magJ y * mainTr`, `rlg` $:=$ `blockGlg` (by subtraction); `rtrLim`, `rlgLim` the limits along $(ML)^n\mid\ell$ (OBS Lemma 5.3); `rtrZero`, `rlgZero` their limits as $\nu\downarrow0$ (OBS
  Lemma 5.4).
*Proof.* The Root-F conjunct is Theorem IV.5.3 at $(\kappa_*,1)$. The `C1Star` fields: the ranges are immediate from the choices. `J_pos`, `J_tendsto`, `J_bounds`: Lemma IV.5.1 (c).
`C1StarF1`: the bound for $\nu\in(0,1]$, $k<k_f(\nu)$ is SF Theorem 5.3 along the flow (LF-7 (d)); it holds trivially under the zero convention and passes to $\nu=0$ by closedness; continuity of
$\nu\mapsto\xi(\nu,k)$ at $0$ is LF-7 (e) (for fixed $k$ and $\nu<\nu_*(k)$, $k<k_f(\nu)$, and the limit exists by SF §3.5, Lemma 3.3 there, with (CONT) of Definition IV.3.1). `C1StarF2`: the
bound on $\mu_j$ is OBS (O1) (with the constant of OBSR O-04), continuity at $0$ is LF-7 (e), and the decomposition `blockM = magJ + em` with $|{\rm em}|\le c_*\beta^{-2}L^{-2J(d-2)}$ on
$\ell\ge\ell_0(\nu,x)$, $ML^{J+1}\mid\ell$, is Proposition IV.4.4 ((IV.4.4) at $h=e_1$, CORR Lemma 0.2 for `blockM`) with OBS §5.3 (F2) and OBSR O-02 (winding terms dropped for $\ell\ge\ell_0$); `magJ`
is $m_J$ (the Lean sum $\sum_{j<J}\beta_j^{-1/2}\mu_{j+1}$ is $\sum_{j=1}^J\beta_{j-1}^{-1/2}\mu_j$). `C1StarF3`: the two decompositions and the bounds are Proposition IV.4.4 with OBS Theorem 5.2 (F3): $r_{tr}$
collects $\frac1{N-1}{\rm tr}_\perp[R_J+\partial^2(\mathcal R^{(J)}+\mathcal P^{(J)})]$, the tail $(\beta\gamma_{k_f})^{-1}m_Jm_JE_{\rm tail}$ (D-IV.6; $\le c_*\nu^{(d-2)/2}e^{-c'\sqrt\nu|z|}$), the mass reconciliation of OBS Lemma 4.2
for the massless kernels $T_i$, $i\le k_0$ (with the mass factor of OBSR O-06), the difference between $\mathscr M$ evaluated at winding and non-winding polymers ($\le c_*\nu^{(d-2)/2}e^{-c'\sqrt\nu|z|}$ for
$2|z_i|<\ell$, OBSR O-02), and $r_{lg}$ consists of remainders only (OBS Lemma 2.1: $h^\top G^{(j)}h=0$); the bounds are OBS Lemma 2.3 (b) for $R_J$ and Proposition IV.4.4 for the rest; `mainTr` is
$\sum_{j<J}(\beta\gamma_j)^{-1}T_j^{\ell,\nu\delta_j}$ with `termKernel` on the free sequence (CORR (2.1)–(2.2)). The limits along tori: OBS Lemma 5.3 (CORR Theorem 4.1 with Root-F's agreement clause,
and (G1) of I-G). The limits as $\nu\downarrow0$: OBS Lemma 5.4 (Tannery with the summable majorant $b_{ij}$; the convergence of each $R^{ij}_\infty(\nu)$ and $\beta_{i-1}(\nu)$ is LF-7 (e); the last-step terms are
$O(\beta^{-2}_{J-1})\to0$ and the tail is $O(\nu^{(d-2)/2})\to0$ at fixed $x,y$). $\square$

### IV.5.4 The assembly table and the remaining cited inputs

**Table IV.5.5 (clause → source).** "Proved" refers to this document (Parts I–IV); "cited" to the input named. Document keys: LFR = this document, SF, OBS, OBSR, CORR, PE, BG, LOC,
GREEN; Lean names are landed declarations.

| Clause | Supplied by | Status |
|---|---|---|
| Root-F: $\exists\delta>0$ | $\delta=\gamma/2=\frac18$; row 1, row 10 ($\alpha_1\le\gamma/2$) | definition |
| Root-F: $\exists L\ge2,M\ge1,\beta_0$ after $(\kappa,c_9)$ | prefix §I.1.4 with rows 3, 5, 6, 10 as amended; $\lambda_*$ from §§I.5.3, II.1.3, III.O.3, IV.O.3 | definition / existence of thresholds |
| [v1.3: constants a–d] localization and analytic-domain constants | row 5a $r_1=(r_0-4dL^3)/L$, row 7 $\rho\ge4dLM$; row 5 $C_{d,L}=3^{d+1}L^{2d+1}$; row 16 $C_{\Xi1}=(4d+8)(2d+1)$ and $K_\Sigma$ with $+8$ | fixed before $\lambda_*$; the new lower bounds are monotone |
| [v1.3: P4-01, P4-09] geometric and regime hypotheses of LF-4 | $R_j=\hat R_j$ and $1\le k\le k_0$; Lemmas III.6.4, III.8.2, IV.3.3; source-estimate pass after D-IV.2 | conditional on the named localization and P7 window inputs |
| [v1.3: F-1, Lambda28'] analytic half of LF-3 | Def-6/Def-7 local terms analytic on $\Xi^c_j$; FLUCTUATION Theorem 4.2 and (Λ28′) | proved from its stated LOC/AE/GM inputs; auxiliary cover remains an input |
| [v1.3: P4-04, switch] half-budget and switching RG | FLUCTUATION Theorem 3.1(d),(e), Lemma 2.9, Theorem 5.3; Lemmas IV.1.8 and IV.2.2 | coefficient and matrix argument supplied; localization inputs remain conditional |
| [v1.3: P3-02, P3-03, P3-05, P4-07] analytic removed activity and gas | Lemmas III.9.5–III.10.5; operator GAS in GasOperator.lean and HoleOperator.lean | abstract GAS landed; application conditional on front-free analytic estimate, re-expansion and hole closure |
| Root-F: $\exists$kf with $L^{\rm kf}\sqrt\nu\le L$, $\frac12\le L^{\rm kf+1}\sqrt\nu$ | Lemma IV.5.1 (a), $\mathrm{kf}=\hat k_f$ | proved |
| Root-F: $T_j=0$ off scale-$j$ polymers containing $x$, $j\notin[1,\mathrm{kf}+1]$ | Definition IV.5.2, Lemma IV.5.1 (b) | definition |
| Root-F: $T_j$ depends on $g\restriction_X$ | P4 (H.7) via Def-6 (SF §1.3); PE (c); (S0), (D7); LF-4 (c), (e) | cited (H.7) / proved |
| Root-F: analyticity on $\|g\|_{\ell^1}<1$ | (H.7); PE (d); Theorem IV.5.3 item 4 | cited / proved |
| Root-F: bound on $\|g\|_{\ell^1}\le\frac12$ | Theorem IV.4.1 ((H.7) at $j\le k_f+1$, (IV.4.2)), PE §3.6 (tree length vs blocks), PE §4.4 (Cauchy), (Λ32) | conditional on LF-8 and its cited inputs |
| Root-F: identity for $\log(Z(g)/Z(0))$ | LF-8 (a) Theorem IV.4.1 (IV.4.3), LF-7 Theorem IV.3.2 (c), LF-8 (b) Proposition IV.4.3, PE §4.6 | conditional on LF-6…LF-8; Proposition IV.4.3 is superseded by LF-BASE-KF0.md (in preparation) |
| Root-F: agreement of two tori | (D8) v1.2 (D-IV.9), PE (f), PE §4.5, torus independence of the running constants (SF (H.5)) | proved from (D8) |
| `RootFAndC1Star`: Root-F clauses at $(\kappa_*,1)$, $L\ge3$ | Theorem IV.5.3 | proved |
| `C1Star`: constants and ranges | SF §1.1, Theorem 3.2, 5.3; OBS Lemma 1.1 + OBSR O-04/O-05; OBS §5.3 | definitions |
| `J_pos`, `J_tendsto`, `J_bounds` | Lemma IV.5.1 (c) | proved |
| `C1StarF1` bound | SF Theorem 5.3 along the flow (LF-7 (d)) | conditional on FLUCTUATION Lemma 2.9 and Theorem 5.3; ordinary complete RG matrix at the switch |
| `C1StarF1` continuity at $0$ | LF-7 (e); SF §3.5, Lemma 3.3 | cited (SF (CONT) "reduced to an explicit clause") |
| `C1StarF2` bound on $\mu_j$ | OBS (O1), Theorem 3.1 (X3) | cited (OBS: sketched) |
| `C1StarF2` continuity | LF-7 (e); OBS §3.8 | cited (sketched) |
| `C1StarF2` `blockM = magJ + em`, bound on `em` | Proposition IV.4.4, OBS §5.3 (F2), OBSR O-02; CORR Lemma 0.2 | conditional on LF-8 and the cited OBS layer |
| `C1StarF3` decomposition and bounds | Proposition IV.4.4 (massive last term, D-IV.6), OBS Theorem 5.2 (F3), Lemma 2.1, Lemma 2.3, Lemma 4.2; OBSR F-B, O-02, O-06 | conditional on LF-8 and the cited OBS layer (OBS Thm 3.1 sketched) |
| `C1StarF3` limits along tori | OBS Lemma 5.3; CORR Theorem 4.1; I-G (G1) | proved there |
| `C1StarF3` limits as $\nu\downarrow0$ | OBS Lemma 5.4; LF-7 (e) | proved there from (CONT) |
| (internal) $\int\rho_k=Z(g)$ | LF-6 (a), LF-3 (a), LF-4 (a), LF-5 (a) | proved |
| (internal) the classes along the flow | LF-6 (Thm II.7.10), LF-3 (Thm IV.1.1), LF-4 (Thm III.10.8), LF-5 (Lemma IV.2.1, Thm IV.2.2), LF-7 (Thm IV.3.2) | conditional on the cited inputs in IV.5.6, including P7 re-expansion and FLUCTUATION localization |
| (internal) budgets (D6), (H6♭) | LF-2 (Theorem I.5.4) with Lemma B (II.5.12), LF-4R (III.8.9), Lemma IV.3.3 | proved |
| (internal) operator bounds (D5), Corollary IV.2.3, (IV.4.1) | Lemmas II.5.13, II.5.14, II.7.8, IV.1.4, IV.4.2; LF-1 (Thm II.4.1) | proved (non-quiet (S2) from P6 (3.4)–(3.9), cited) |

**IV.5.6 The remaining cited inputs** (each is used as stated in the document named; "landed" = Lean without `sorry`).
1. *Background fields.* I-1 (BG Theorem 5.2, Def-5: landed `theorem52_*`, `bgField`, `bgFieldC`, `theorem71`, `theorem72`), I-1(e) (landed `bgFieldC_holder`), I-2 (landed `theorem73_*`), BG
   Proposition 5.1 (landed `prop51_*`). P2 Proposition 4.1 with mass (the last step) = BG Theorem 5.2 (5) with $\mu>0$.
2. *Green's functions.* GREEN G-1 (coercivity), G-2 (decay; landed machinery, NC3 landed), G-4, G-5 (with the extension to masses $\le2$, CORR D-03), G-6; GREEN §4.4 (ii) (the first-step form).
3. *Localization [v1.3: P4-09, constants a,b].* LOC I-4a/b/c with $r_0=4dL^3+L$, $r_1=(r_0-4dL^3)/L$, $\rho\ge4dLM$, I-5, Lemma AE (landed `abstract_expansion`), with the open items GM2 (false as printed; repair (d̃$^{\rm cov}$) of CHK §1 queued as LOCALIZATION v3) and the
   variation V1.
4. *Small field [v1.3: F-1, P4-04, switch].* Def-6/Def-7 local terms are analytic on $\Xi^c_j(\mathbb B_j(X);1,\varepsilon_j)$, with the landed constants xiC1 and xiSigma; FLUCTUATION Theorem 3.1(d),(e) supplies the full P5 (3.9) half-budget, including whole-torus terms, conditional on (Vmod) and the auxiliary cover. FLUCTUATION Lemma 2.9 and Theorem 5.3 supply the two-step switch and ordinary complete RG matrix; (L1′) is retired. I-8/I-9 on subdomains and (CONT) remain conditional on their cited localization inputs. The base Proposition II.7.9 is superseded by notes/phase1/LF-BASE-KF0.md (in preparation).
5. *The analytic half of Lemma F [v1.3: Lambda28′].* FLUCTUATION Theorem 4.2 gives Lemma IV.1.3 with the actual distance $D_k=M([\hat R_k]-1)-2M_1$ and condition (Λ28′), conditional on LOC I-4a/b, AE, GM and its auxiliary-cover hypothesis. Its decay is in $d^{\rm cov}_{k+1}(\bmod\Omega^c)$.
6. *Large-field small factors.* P6 (3.4)–(3.9) (Lemma IV.1.4), with LF-1 (proved).
7. *$R$ [v1.3: P3-01–P3-05, P4-01, P4-07, P4-09].* P7 Lemmas 2.1, 2.2, 2.4, P4 (4.11)–(4.12), P7 (3.3)–(3.5) and P2 Proposition 3.1 retain their stated roles. The analytic core has a fixed real contour indicator (Lemma III.9.5), the heavy activity is front-free (3.10″), and the mass bound uses $e^{2\epsilon}$ for $k\le k_0$. The window renormalization P7 (2.10)–(2.16) with P6 (2.31), and P7 (3.20)–(3.25), remain cited analytic inputs after the $\hat R$ pass. The front-free majorant and concrete hole-closure instantiation need a fresh audit before unconditional LF-4 use.
8. *Polymer expansions [v1.3: P3-05].* Scalar PE/GAS is the cited input for the last step. The function-valued versions are landed in GasOperator.lean and HoleOperator.lean as gasOp_eq, gasOp_activity_bound, gasOp_pe and gasOp_pe_hole. Lemma III.10.5 gives their application hypotheses; abstract theorem availability does not establish the preceding P7 re-expansion.
9. *The last step.* P7 (4.1)–(4.9) (the last fluctuation integral; Theorem IV.4.1), P4 §6 (P4 (6.2)); the case $k_f=0$ (Proposition IV.4.3, superseded by notes/phase1/LF-BASE-KF0.md (in preparation)).
10. *Observables.* OBS Theorem 3.1 (X1–X7, sketched), Proposition 3.3 (P9 (3.13) via PE-M with a hole; OBSR O-09: the reduction for the non-product Gaussian measure is the main risk),
    Lemma 3.4 (P9 Lemma 2, sketched), Proposition 4.1, Lemma 4.2 (conditional on G-5 (b)), Theorem 5.2; CORR Theorem 4.1 and I-G (G1)–(G5).
11. *Geometry.* Timár 2013 Lemma 2 (landed `exteriorBoundary_starConn`); the identification of `toSphere` with the graph measure of the chart (Lemma II.7.4 (a); Lean item Q2).
12. *Errata readings* used in Part IV: P9 (4.14)'s last covariance read as massive (OBSR Q2); P5 Proposition 3.2's printed scale-$k$ bound is strengthened by P6 Lemma 4.2 and FLUCTUATION Theorem 3.1(d) (Lemma IV.1.8, conditional on its localization inputs); P6 (3.2)'s
    "$\cap\,\mathsf S$" read as "$\cup$" (N-II-1).

---

## IV.L Lean declarations asked for by §II.7 and Part IV

Namespace `Balaban.LargeField`; all files Lean modules; sizes are estimates including docstrings. Blocks Q (base case, `LargeField/Base/`), S (steps, `LargeField/Step/`),
T (flow, `LargeField/Flow/`), U (last step, `LargeField/Last/`), V (assembly, `LargeField/Assembly/` and the Root-F provider). **Bold** marks prerequisites that are not landed.
Parts I–III's blocks A–L and P1–P16 are assumed.

| # | Declaration(s) | Kind | Content | Needs | Est. lines |
|---|---|---|---|---|---|
| Q1 | `chiPrimeZero` ($A\cdot B$), `BaseRecord`, `baseRecord_isStep`, `baseRecord_seeds_new`, `base_noRipe`, `base_budget` | def/thm | Def. II.7.1, Lemma II.7.2 | Part I B, C; K2 | 400 |
| Q2 | `toSphere_eq_graph` (hemisphere chart: $\sigma=(1-|\xi|^2)^{-1/2}d\xi$), `integral_perp_eq_integral` (Lemma II.7.4 (b)), `perpProj` (complex) | thm | Lemma II.7.4 | Mathlib `HaarToSphere`, invariance of `toSphere`; **uniqueness of the invariant measure on $S^{N-1}$** | 600 |
| Q3 | `action_sub_eq_chord_quadratic` | thm | Lemma II.7.3 | `IsEL` (`Background/Data.lean`) | 100 |
| Q4 | `spins_near_background` | thm | Lemma II.7.5 | `theorem52_exists` (bounds), H1 | 250 |
| Q5 | `baseKernel`, `baseBoundary`, `baseStepData`; `baseStepData_S0`, `_S1`, `_S4`, `_S5` | def/thm | Def. II.7.6, Lemma II.7.7 | J5 (v1.2), H1–H3, J3 | 700 |
| Q6 | `baseStep_bound` ((S2) at $k=0$) | thm | Lemma II.7.8 | Q5, I2 (LF-1), K4 | 600 |
| Q7 | `lf6` | thm | Theorem II.7.10 | Q1–Q6, L2; **I-9 at $k=0$ (Prop. II.7.9)** | 300 |
| S1 | `StepData` (S1)–(S2) version 1.2 (witness functions, Gaussian measures `mWit`), `bound126_comp` v1.2 | def/thm | Def. II.5.7, Lemma II.5.13 (amended) | J5, K3 (edit) | 300 |
| S2 | `lemma21` (P5 Lemma 2.1) | thm | Lemma IV.1.2 | P9 (`lemma25`) | 200 |
| S3 [v1.3: switch] | `switch_two_step` (FLUCTUATION Lemma 2.9; ordinary matrixInfty after re-expression) | thm | §IV.2, FLUCTUATION §2.8 | BG Proposition 5.1, LOC I-4a, FLUCTUATION Theorem 5.3, `rg_step_infty` | 250 |
| S4 | `bgChange_expansion` | thm | Lemma IV.1.3 | `theorem73_real`, `abstract_expansion`; **LOC I-4b, I-5** | 800 |
| S5 | `nonQuiet_bound` | thm | Lemma IV.1.4 | S1, I2; **P6 (3.4)–(3.9) small factors written out** | 900 |
| S6 | `Bst_indep` | thm | Lemma IV.1.5 | S4, Part I B3 | 300 |
| S7 | `nonQuiet_rotationForm` | thm | Lemma IV.1.6 | J7, **LOC I-4c** | 300 |
| S8 | `IsRepFam` v1.2 (on $\mathbb Z^d$ data), `isRepFam_step`, `reducedSymmetry_bound` | def/thm | Def. IV.3.1, Lemmas IV.1.7, IV.1.8 | L2, **SF (CONT)** | 500 |
| S9 | `lf3` | thm | Theorem IV.1.1 | S1–S8; **I-8, I-9** | 500 |
| S10 | `transfer`, `lf5_step`, `frozen_bound` | thm | Lemma IV.2.1, Thm IV.2.2, Cor. IV.2.3 | S9, D8 (LF-2 frozen) | 600 |
| T1 | `kZero` (a priori), `kZero_props`, `hLambda_apriori`, `hT_apriori` | def/thm | Lemma IV.3.3 (replaces E1's `hT_of_flow`) | D2, `betaSeq_eq`, `nuSeq_eq` | 300 |
| T2 | `flow` (recursive construction), `lf7` | def/thm | Theorem IV.3.2 | Q7, S9, S10, P16 | 600 |
| U1 | `lastStep_budget` | thm | Lemma IV.4.2 | D6–D8, K2 | 300 |
| U2 | `lf8a` | thm | Theorem IV.4.1 | U1, `gas_eq`, `gas_pe`, `pe_blockTorus`, `pe_PY_analyticOnNhd`; **P7 (4.1)–(4.9) last integral (I-8 massive)** | 800 |
| U3 | `lf8b` | thm | Proposition IV.4.3 | Q2, Q3, GAS, PE; **I-8 at the unit scale with mass** | 700 |
| U4 | `lastStep_observables` | thm | Proposition IV.4.4 | U2, `Correlations` (Lemma 0.1, 0.2), **OBS layer** | 500 |
| V1 | `kfHat_rootF_bounds`, `J_bounds_flow` | thm | Lemma IV.5.1 | T1 | 150 |
| V2 | `rootFTerms`, `rootFTerms_clauses` | def/thm | Def. IV.5.2, Thm IV.5.3 items 2–7 | U2, U3, PE §4.4 (Cauchy, `norm_fderiv_line_le`) | 600 |
| V3 | `rootF_of_flow` (the proof of the provider `Balaban/Provider/LogPartitionMultiscale.lean`) | thm | Theorem IV.5.3 | V1, V2, T2 | 300 |
| V4 | `c1Star_of_flow`, `rootFAndC1Star_of_flow` | thm | Theorem IV.5.4 | V3, U4, `C1Star`, **OBS Theorem 3.1, 5.2** | 500 |
| | **Total** | | | | **≈12 300** |

No file need exceed 1 000 lines. Q1, Q3, S1, S3, T1, V1 can be drafted now; Q2 needs a Mathlib-level lemma on invariant measures on spheres; the others need Def-7 (L2) and the cited
analytic inputs in bold. The provider proof of Root-F (V3) is the last item; until it lands, Root-F stays `DRAFT_SORRY` (AGENTS.md).

---

## IV.O Status, changes, conditions on $\lambda_*$, open items

### IV.O.1 Status of the statements of §II.7 and Part IV

| Statement | Status |
|---|---|
| Def. II.7.1, II.7.6; Def. IV.3.1, IV.5.2 | definitions |
| Lemma II.7.2 (base record), II.7.3 (exact quadratic identity), II.7.4 (chart, $\mathbb R^N$ representation; (a) for `toSphere` via invariance, Lean Q2), II.7.5 (spins in the chart) | proved here |
| Lemma II.7.7 (structure of the base data), II.7.8 (one-step bound at $k=0$) | proved here, with the $\mathsf Q$-, $\mathsf S$-factors from P6 (3.7)–(3.8) via LF-1 |
| Proposition II.7.9 (small field at scale $1$) | cited/sketched: I-9 at $k=0$ with the listed differences |
| Theorem II.7.10 (LF-6) | proved here given Proposition II.7.9 |
| Lemma IV.1.2 (P5 Lemma 2.1) | proved here from Lemma III.7.1 Case A |
| Lemma IV.1.3 (analytic half of Lemma F) | FLUCTUATION Theorem 4.2 with (Λ28′); conditional on LOC I-4a/b, AE, GM and auxiliary cover |
| Lemma IV.1.4 (non-quiet one-step bound) | proved here from P6 (3.4)–(3.9) [checked] and LF-1, in the version-1.2 form |
| Lemma IV.1.5 ($B_{\rm st}$), IV.1.6 ((S5)), IV.1.7 (family class) | proved here (IV.1.5 uses P5 Prop 3.1 for the fluctuation integral; IV.1.7 uses SF (CONT)) |
| Lemma IV.1.8 (reduced-symmetry terms) | coefficient proof from FLUCTUATION Theorem 3.1(d),(e), conditional on its localization inputs; includes whole-torus terms |
| Theorem IV.1.1 (LF-3) | proved here given the cited small-field analysis (P5 §§2–3, P6 §§2–4; I-7, I-8, I-9 with the $\nu$-free RG system) |
| Lemma IV.2.1 (transfer), Theorem IV.2.2 (LF-5), Corollary IV.2.3 | proved here using FLUCTUATION Lemma 2.9 and Theorem 5.3 for the two-step switch; conditional on their stated inputs |
| Theorem IV.3.2 (LF-7), Lemma IV.3.3 (a priori regime, horizon, tori) | proved here |
| Lemma IV.4.2 (last-step budget) | proved here |
| Theorem IV.4.1 (LF-8 (a)) | proved here from P7 (4.1)–(4.9) [checked; the last fluctuation integral cited], GAS and PE (landed scalar versions) |
| Proposition IV.4.3 (LF-8 (b), $k_f=0$) | superseded by LF-BASE-KF0.md (in preparation); interface retained |
| Proposition IV.4.4 (P9 (4.7)–(4.9) with the massive last term), Remark IV.4.5 ((L4′)) | the decomposition proved from Theorem IV.4.1; the layer cited from OBS (sketched there) |
| Lemma IV.5.1, Theorem IV.5.3 (Root-F) | proved here given LF-6…LF-8 and the inputs of §IV.5.4 |
| Theorem IV.5.4 (`RootFAndC1Star`) | proved here given Theorem IV.5.3 and OBS Theorems 3.1, 5.2 (sketched there) |

### IV.O.2 Changes to Parts I–III (made in place, marked "version 1.2 (Part IV)")

1. **Admissible tori** (D-IV.1): Part I Def. I.2.0 now reads $ML^{\hat k_f+1}\mid\ell$; Root-F's `kf` is $\hat k_f$.
2. **A priori radii** (D-IV.2): Def. I.3.1 (data), Def. II.1.1 (row $R_j$) and Def. III.3.1 ($k_2,k_3$) use $\hat R_j$ in the flow.
3. **(S1)–(S2) version 1.2** (D-IV.3): Definition II.5.7 (S1), (S2) with witness functions $F^w_k(u)$ of the differences $u_y$ and their Gaussian measures $m^w_k$; Lemma II.5.13 step (1)
   integrates $\psi_{k+1}\restriction_{\Omega^c}$ to $\sum_wm^w_k(\cdots)$; the quiet kernels have $F\equiv1$ and are unchanged.
4. **Reference measure** (D-IV.4): Definition II.5.1 — the spin measure is `volume.toSphere` (total mass $Nv_N$, not normalized); the scale-$0$ fluctuation convention is §II.7.
5. **(D8)** (D-IV.9): supports in the image of a box $\{|y_\mu-c_\mu|<\ell/4\}$ (side $<\ell/2$).
6. **Family class** (D-IV.8): Definition II.6.4 is replaced by Definition IV.3.1 (pointer in place); Theorem III.10.8 (f) is read with it (its proof uses only the limit at $\nu=0$).
7. **Definition II.6.1**: the tori are the admissible tori of (A-IV.3).
8. **Constant chain** (§I.1.3, §I.1.4): row 5 $\kappa_{\rm flow}:=\max\{C_{d,L}(\kappa+1)+C'_{d,L},16\kappa_0+16,\ 2(4+\log(2(2d)^2 2^{2d+1}))\}$; row 9 $A_3:=\frac14\min\{\frac{8\gamma_0}{6^d(9K_1)^2}A_0^2,\frac18A_1^2\}$ (a quarter of P6's
   constant); row 10 $\alpha_1\le\gamma/2$ and $c^{\rm flow}_9:=\min\{c^{\rm P4}_9,\frac12c_9e^{-\kappa_{\rm flow}}\}$; row 11 $C_b$ also bounds the base constants of Lemma II.7.7 (b); row 13 $H_0\ge2L^d(C'_E+1)$;
   row 16 $\beta_0:=\max\{e^{\lambda_*-1}/a,2B\}$ and the conditions (Λ26)–(Λ32).
9. **A priori regime index** (D-IV.11): Def. II.1.1 (rows $k_0$, $\mu_j$), (D9), §II.6.3, (A-III.2) and the hypothesis of Theorem III.10.8 read "$k\le k_0$" for "$\beta_k\nu_k\le1$"; consequences:
   $\beta_k\nu_k\le e^{2\epsilon}$, $C_{\rm S5}=3$ (Definition II.5.7 (S5)); Lemma I.5.6 (b), (c) are superseded for the flow by Lemma IV.3.3; §I.5.7 points there.
10. Part I §I.5.7: the base gain is Lemma II.7.2 (e) and Lemma II.7.8; Part II §II.5.12's remark on $k=0$ points to §II.7.
11. Part II carries a pointer to §II.7 (after §II.6.5).

[v1.3: P3-01–P3-05, P4-01, P4-09] The version-1.2 assertion that the weaker mass hypothesis and larger radius only change constants was false. Lemmas III.6.4 and III.8.2 now pay $e^{2\epsilon}$ with an explicit margin, and the source-estimate pass after D-IV.2 distinguishes a chosen separation from a running coefficient. The Part III audit has arrived and its corrections are tagged in §§III.7–III.10. The analytic P7 window and re-expansion inputs remain conditional as recorded in IV.5.6.

### IV.O.3 The conditions on $\lambda_*$ added by Part IV

For all real $x\ge\lambda_*$ (combined with §I.5.3, §II.1.3, §III.O.3); $\bar\delta(x)=eA_0x^{p_0}e^{-x/2}$, $\theta=(d-2)\log L$, constants of rows 0–15 and of the Root-F data $(\kappa,c_9)$.

| | Condition | Used in |
|---|---|---|
| (Λ26) | $4dL\bar\delta(x)\le c^{\rm BG}_1$, $\ C_{\rm hs}L\bar\delta(x)\le\frac14$, $\ 4dK_1L\bar\delta(x)\le\frac12\gamma_GL^{-2}$ | Lemmas II.7.3 (use), II.7.5 |
| (Λ27) | $\log\big((d+1)(2LM)^d\big)+\frac N2\log2+d\log M\le A_3(x-3)^{2p_0}$ | Lemmas II.7.8, IV.1.4 (witness entropy and prefactors) |
| (Λ28) | $B_0e^{-\frac\kappa2L[R_{\rm base}(x-2)^2]}\le1$ | Lemma IV.1.5, Theorem IV.2.2 (f) |
| (Λ28′) [v1.3: Lambda28', P4-09] | $C_FA_0^2x^{2p_0}e^{-\gamma_w(M([R_{\rm base}(x-2)^2]-1)-2M_1)}\le e^{-R_{\rm base}x^2/2}$, $\gamma_w=\gamma_0/4$; $C_F=C_F(d,L,N,\kappa,\kappa_1,M)$ of FLUCTUATION Theorem 4.2 | Lemma IV.1.3 and the analytic half of Lemma F |
| (Λ29) [v1.3: P4-04] | $e^{x-2}/a\ge2C_*(2L^{d-2})^{m+1}$, $(e^{x-2}/a)^{1/2}\ge2C_{\rm PE}K_0(2L^{d-2})^m$, and $C_{\rm sqrt}e^{-\gamma_w(M([R_{\rm base}(x-2)^2]-1)-2M_1)}\le e^{-R_{\rm base}x^2}\le a^{m+4}e^{-(m+4)x}$, where $C_*=C_{\rm PE}K_0+1$ and $C_{\rm sqrt}$ is the LOC I-4c square-root response constant | Lemma IV.1.8: for $x=\hat\lambda_k$, these imply respectively the two lower bounds on $\beta_k$ and $e^{-\hat R_k}\le\beta_k^{-m-4}$ |
| (Λ30) | $c_H+\theta\le\frac d2x$ | Lemma IV.4.2 ($\hat\lambda_{k_f+1}\le d\hat\lambda_{k_0}$) |
| (Λ31) | $(LM)^d(x-2)\ge B_{\rm cpl}e^{B_{\rm cpl}}e^{\kappa'c}K'_0+\kappa'(c^{\rm PE}_2+c)+c^{\rm PE}_1+2+\ln K''_0$ ($B_{\rm cpl}=B_0+B_{\rm st}+1$), and $\frac12A_2(x-3)^{p_2}\ge(m+1)dx+\log(6c^{\rm PE}_1K_0e^{c^{\rm PE}_1+\kappa c})+(m+1)$ | Theorem IV.4.1 (GAS at the last step; $\alpha\le\frac12\beta_{k_f}^{-m-1}$) |
| (Λ32) | $a^{1/4}e^{-(x-1)/4}\le c^{\rm flow}_9$ (P4 (5.40): the new (H.7) constants are $\beta^{-1/4}$); $32N(m+1)a^2e^{2-2x}e^{\kappa_{\rm flow}}\le c_9$; $C_{\rm IV.4.3}\,a\,e^{1-x}L^{\frac{d-2}2+\delta}e^{\kappa_{\rm flow}}\le c_9$ | Theorem IV.5.3 item 5, Proposition IV.4.3 |

Each compares a fixed constant with a function tending to $0$ or $\infty$, so $\lambda^{\rm IV}_*$ exists. For (Λ28′) and (Λ29), $D(x)=M([R_{\rm base}(x-2)^2]-1)-2M_1=M R_{\rm base}x^2+O(x)$; row 6 makes $\gamma_wM>1$, so the left exponential in (Λ29) decays faster than $e^{-R_{\rm base}x^2}$, and the (Λ28′) comparison is weaker. (Λ32) contains $c_9$ and $\kappa_{\rm flow}(\kappa)$, which are given before $L$ in Root-F's order
$\forall\kappa,c_9\,\exists L,M,\beta_0$, and $\lambda_*$ is chosen after them; (Λ28), (Λ31) contain $B_0$, which is fixed before $\lambda_*$ (row 12 before row 16).

### IV.O.4 Open items (Parts I–IV together)

- **O-1, O-3, O-4, O-7, O-8′, O-II-1, O-II-5.** Closed (as recorded in §III.O.4).
- **O-2′ (analytic half of Lemma F) [v1.3: Lambda28′].** FLUCTUATION Theorem 4.2 supplies Lemma IV.1.3 with the corrected distance and (Λ28′), conditional on its stated LOC/AE/GM and auxiliary-cover inputs.
- **O-5 ($\pi'$ offsets; adjacency in P5 (1.33)).** Open; enters only constants of PE.
- **O-6 (base rule).** **Closed** for the large-field part (§II.7: Lemmas II.7.2, II.7.7, II.7.8, Theorem II.7.10). The small-field part of the first step is O-IV-1.
- **O-9, O-10.** Unchanged.
- **O-II-2 (Def-6, R-ν) [v1.3: F-1, switch].** The Def-6/Def-7 output domain is the accepted $\Xi^c$ domain. FLUCTUATION Lemma 2.9 removes (L1′) at the switch and Theorem 5.3 gives the ordinary complete RG step there. The remaining conditions are the small-field subdomain localization inputs, especially (Vmod) and auxiliary-cover admissibility.
- **O-II-3 (errata candidates) [v1.3: P4-04].** **N-IV-1** is answered by FLUCTUATION Theorem 3.1(d) and Lemma IV.1.8, conditional on the named localization inputs. **N-IV-2** P5's $k_0$
  (p. 490) is defined from the running $\beta_k\nu_k$, which the switching step itself produces; the decision is circular unless made with a priori data (D-IV.11). **N-IV-3** P7 (4.10) uses
  $p_2(\beta_k)$ for the last step; only $p_2(\beta_{k_0})$ (frozen threshold) is available (repaired by Lemma IV.4.2; ARCH §4.8 recorded the same for P6 Theorem 4). **N-IV-4** P9 (4.14) prints
  the regular covariance for the last term; the final covariance is massive (OBSR Q2; D-IV.6).
- **O-II-4 (constants of the small-field step).** **Closed:** $C_b$, $C_{\psi'}$, $C_{15}$, $B_{\rm st}$ are outputs of rows 0–11 (Theorem IV.1.1 (f), Lemma IV.1.5).
- **O-II-6 (family class).** **Closed** by Definition IV.3.1, Lemma IV.1.7, Theorem III.10.8 (f), Theorem IV.3.2 (e).
- **O-II-7 (torus coherence).** **Closed** by (D8) version 1.2 and the locality of the constructions (Theorems II.7.10 (d), IV.1.1 (h)).
- **O-II-8 (row 3 of the chain).** Open (G-1–G-6 as $L\ge L_i(d)$); Part IV adds $L\ge3$ only (Lemma IV.1.5's rate $\frac\kappa2L\ge\frac32\kappa$, and `RootFAndC1Star`'s `hL`).
- **O-II-9 ((L4) of OBSERVABLES).** The replacement (L4′) is stated (Remark IV.4.5); the edit of `OBSERVABLES.md` §4.1 is pending (queued).
- **O-II-10 (switch at $k_0$) [v1.3: switch].** The matrix-perturbation obligation is closed by FLUCTUATION Lemma 2.9; LF-5 still inherits that lemma's LOC inputs.
- **O-III-1 (obligations on LF-3) [v1.3: P4-04].** The coefficient mismatch N-IV-1 is repaired by Lemma IV.1.8. LF-3 remains conditional on the FLUCTUATION localization inputs.
- **O-III-2 (cited analytic inputs of Part III), O-III-3 (operator-valued gas), O-III-4, O-III-5 [v1.3: P3-05].** The abstract operator-valued GAS is landed. The concrete Part III application retains the P7 re-expansion, hole-closure and analytic-activity obligations in Lemma III.10.5. The last-step weights are scalar.
- **O-IV-1 (the small field of the first step).** Proposition II.7.9: I-9 at $k=0$ in the sphere chart (SF §5.5), including the localization of $C^{(0)}$ (GREEN §4.4 (ii)) and (H.5) for $\mathscr E^{(1)}$; cited/sketched.
  Lean also needs the identification of `toSphere` with the chart measure (Q2).
- **O-IV-2 (LF-8 (b), $k_f=0$).** Sketched (Proposition IV.4.3); no source.
- **O-IV-3 (the observable layer).** `RootFAndC1Star` rests on OBS Theorem 3.1 (X1–X7), Proposition 3.3 (P9 (3.13) with a hole; OBSR O-09 is the main risk) and Lemma 3.4, all sketched in OBS.
- **O-IV-4 (audit of D-IV.2 and D-IV.11) [v1.3: P4-01, P4-09].** The source-estimate pass after D-IV.2 and the explicit mass rerun in Lemmas III.6.4 and III.8.2 replace the blanket assertions. The P7 window and re-expansion rows remain conditional and require verification with the chosen $\hat R_j$ before LF-4 is unconditional.
- **O-IV-5 (the cited small-field step).** LF-3 and LF-5 cite P5 §§2–3 and P6 §§2–4 for the small-field analysis on $Z^c_{k+1}$ (I-8, I-9 on subdomains); this is the largest cited block of the
  whole Root-F proof.

### IV.O.5 Drafting log for version 1.3

**2026-10-12 [v1.3].** The Part III audit was incorporated at the point of use. The support in Lemma III.7.1 is the product of the retained kernel and the new restrictions; Lemma III.9.5 keeps each core indicator on the real contour; (3.10″) is the front-free activity; the $Z_0$ volume in (III.8.4) has no $a^{-N/2}$; and Lemma III.10.5 now uses the landed function-valued gas statements gasOp_eq, gasOp_activity_bound, gasOp_pe and gasOp_pe_hole with explicit application hypothesis (H-op). The abstract theorem is available, while the concrete P7 re-expansion and (H-op) remain to be checked.

**2026-10-12 [v1.3].** The Part IV audit was incorporated in the operative induction: LF-4 runs for $1\le k\le k_0$ with $\beta_k\nu_k\le e^{2\epsilon}$ and its losses paid in III.6.4, III.8.2 and (Λ25). Lemma II.7.4(c) now states a valid holomorphic-integral criterion. FLUCTUATION Theorem 3.1(d),(e) supplies the stronger P5 (3.9) coefficient for every localized term, including whole-torus terms, under its localization inputs. FLUCTUATION Lemma 2.9 supplies the two-step switch at $k_0$ and Theorem 5.3 then uses the ordinary complete RG matrix. Lemma IV.3.3(c) separates the $\hat k_f=0$ endpoint. The base and $k_f=0$ interfaces point to LF-BASE-KF0.md (in preparation); the observable layer remains a cited input.

**2026-10-12 [v1.3].** The chosen-radius source pass is after D-IV.2. Its constants are recorded in (Λ28′), (Λ29) and the strengthened (Λ25); P7 window localization and re-expansion remain conditional. Def-6/Def-7 local analyticity uses the accepted $\Xi^c$ domain, and the boundary and fluctuation rates use $d^{\rm cov}$. The constant prefix uses the landed X₀ separation margin, the extra $L$ in the multiscale block count, $\rho\ge4dLM$, xiC1 and xiSigma; row 11 now exposes the required upper bound on $\alpha_0$ as a small-field input. The assembly table and IV.5.6 list retain the resulting dependencies. No root theorem is claimed unconditionally while those cited inputs or the separate base document remain outstanding.
