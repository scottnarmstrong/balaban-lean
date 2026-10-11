# LF v3 counting audit

**Verdict: does not close as written. Confidence: high for C-01, C-02 and C-04; medium-high for C-03.** The local threshold/bank arithmetic in §4.5 Case 2a survives the checks below, including chains of crossed strips. The transition rules and one geometric input to $R$ do not. The proposed repairs need a new induction over a pending core and a corrected path lemma before LF-2/LF-4 can be declared proved.

## Scope and frozen input

This is a focused, adversarial audit of §3.5, Lemma C(e)–(f), §3.8 Lemma S and its use, §§4.4–4.7, and §8.1. It is not a re-audit of the analytic estimates of P7. The input is `/home/scott/Balaban/notes/phase1/LF-ARCHITECTURE.md` at commit `9c378381b9b45e24f192ddbd063f2ac9f3172fa8`, SHA-256 `2023f410b51b2b974d9f6e9af33838b3d5b4ab85e3d976d2b7fbcde7f331de27` (frozen v1). All line references below are to that snapshot. The only file created by this audit is this report in the scratch directory. Nothing under `/home/scott/Balaban` was changed.

For context, P5 is Balaban, *Commun. Math. Phys.* **196** (1998), 485–521; P6 is Balaban, *Commun. Math. Phys.* **198** (1998), 1–45; P7 is Balaban, *Commun. Math. Phys.* **198** (1998), 493–534. The exact P7 point used below is (3.11) on journal p. 522. The v3 reconstruction, rather than those papers, is the source of the strip and bank rules.

## Findings

### C-01 — BLOCKER — a restart can put a lineage merge at its own core

**Location.** §3.5 (W1), (W4), lines 649–660; Lemma C(e) and its proof, lines 680–700; the claim after (W3), lines 668–670. The claimed condition is: “every merge of the lineage at a scale $\mu\le q$ satisfies $\mu+h_\mu<q$.”

**History and failed inequality.** Take $L=2$ and write $C=\mathrm{crit}_k$, an even integer. At scale $k$ put a connected pre-window component on coordinate sites $0,\ldots,C+1$ (non-point spine, diameter $C+1>C$) and a separate single-cube component at $C+3$; the empty site $C+2$ makes them $*$-separated. At $\mu=k+1$, their coarsenings occupy $0,\ldots,C/2$ and $C/2+1$. They now contact, and their union has side $C/2+2\le\mathrm{crit}_\mu$. The canonical hull rule makes it one box and (U3) makes its spine a point. This is a merge with a pre-window part, so (W4) assigns $(q',\nu',\mathcal M')=(\mu,1,\varnothing)$. The lineage has a merge at $\mu=q'$. Lemma C(e) would require

$$\mu+h_\mu<q'=\mu,$$

which is false since $h_\mu\ge2$. A related history merges pre-window pieces at $\mu$ without immediate hulling, then becomes a point box at $q=\mu+1$ by a quiet shadow/hull step (W1). It requires $\mu+h_\mu<\mu+1$, also false. These histories are permitted by the stated rules and do not use an overflow or a bank.

**Refutation check.** The resulting core *is* a box at the entry scale; §4.3 proves that a point-spine component is hulled. Thus this counterexample refutes the literal merge-free assertion, not the desired shape conclusion. The proof of Lemma C(e) checks released (W3) merges but never checks merges in the history before a (W1)/(W4) box entry.

There is also a harmless wording distinction: with the nonconstant lengths $h_j$, the exact condition $\mu+h_\mu<q$ does not literally exclude every $\mu\in[q-h_q,q]$. If $h_\mu=h_q-1$ and $\mu=q-h_q$, then $\mu+h_\mu=q-1<q$. The exact variable-strip condition is the one needed for collapse.

**Minimal repair and check.** Replace the global condition by: every merge *since the last certified one-box entry* is either recorded after the core or has $\mu+h_\mu<q$; earlier merges are allowed because that entry itself certifies one box. Prove the shape conclusion by splitting at the last entry: it is one box at entry; any later merge before a raised core is followed by at least $h_\mu+1$ shadow scales and hence collapses by the displayed diameter recurrence on lines 695–699. The $R$ use in §3.8 needs the one-box core conclusion, not the stronger no-merge sentence. If a literally merge-free interval is required as a theorem, (W1) and (W4) must also delay the core past these strips and the extra delay must be charged; v3 does neither.

### C-02 — BLOCKER — (W3) is not closed on the declared window states

**Location.** §3.5 window-state type $q\le k$, $\mathcal M\subset(q,k]$, lines 625–628; (W3), lines 653–657; Lemma C induction, lines 672–702; §4.5 Case 2a, especially (4.2), lines 1257–1300.

**Explicit two-merge history.** Use $L=2$ and embed the following one-dimensional coordinates in $\mathbb Z^d$, $d\ge3$. Take $s_*=s'=0$ in the abstract (G1), so a seed may be just its coarsening. At scale 1, create two isolated single cubes at coordinates 0 and 3, each with $(q,\nu,\mathcal M)=(1,1,\varnothing)$. At scale 2 their coarsenings occupy coordinates 0 and 1 and merge; their hull is the box $[0,1]$. Separately create a new single cube at scale 2 at coordinate 3. The two scale-2 components are $*$-separated by coordinate 2. The first has

$$q_A=1,\quad \nu_A=2,\quad\mathcal M_A=\{2\},\quad U_A=\tfrac12\tau_2;$$

the new component has $q_B=2$, $\nu_B=1$, $\mathcal M_B=\varnothing$. At scale 3 the first box coarsens to coordinate 0 and the second to coordinate 1, so they merge with $r=0$. Both are in-window, and $3\le\nu_{\max}(3)$ for large $\lambda_0$, hence (W3) applies. The hull is again a point-spine box, so $s'=3$. Since $n_2(3)=O(\log\lambda_3)$ whereas $n_q(2)$ is of order $\lambda_2$, for large $\lambda_0$,

$$t_0=\max\{2+n_q(2),3+n_2(3)\}=2+n_q(2),\qquad k_1(t_0)=2.$$

The old and new blocked strips are $[2,2+h_2]$ and $[3,3+h_3]$. Because $h_3\ge h_2$, their union contains every integer from 2 through $3+h_3$. Consequently (W3) gives

$$q'=k_1(\tilde t)=4+h_3>3=k+1,\qquad \mathcal M'=\varnothing,\qquad\nu'=3.$$

The required state inequality $q'\le k+1$ fails by $h_3+1$ scales. The lineage $Z_j\cap Z$ and the cover in Lemma C(b) are not defined at the purported core $q'$ of this scale-3 component. This is a history allowed by the abstract §8.1 geometry (and can be spaced farther apart if the application uses positive seed thickening). Set $k_0\ge3$; no component is ripe during these steps since $n_q(1),n_q(2)\gg3$.

**Bank check and refutation attempt.** The first deposit is actually funded. It comes from one threshold freed by the scale-2 merge:

$$\tau_{t^*_{\rm other}}\ge\tau_2,\qquad U_A=\tfrac12\tau_2,\qquad \tfrac12\tau_2-E_2>0$$

for large $\lambda_0$, since $\tau_2\asymp\lambda_2^{p_2}$ and $E_2=O(\lambda_2^{2d+1})$, $p_2\ge2d+3$. At scale 3 the old $\tfrac12\tau_2$ bank is released, and the new merge frees at least $\tau_3$ from its second part. The numerical strip shift is $O(h_3)$ and can be paid by those amounts. Hence this is a closure failure of the *state transition*, not an example of insufficient money in (4.2). Treating $q'$ as if it were already a historical core does not repair the induction.

**Minimal repair and check.** Add a distinct **pending-core** state carrying $(q,\nu,\mathcal M)$ with $q>k$, $\mathcal M\subset(q,k]=\varnothing$, and the same $t^*$ and budget. At each quiet step keep the pending target; at each merge recompute (W3); a gain, pre-window merge or overflow still uses (W4). Activate the ordinary window only when the process reaches $q$, after proving that all released merges have collapsed to boxes. No $R$ is ripe while pending, since $t^*\ge q+n_q(q)>q>k$. The numerical Case 2a inequality continues to have the correct sign: a new merge occurring wholly behind a pending core has no bank deposit and no strip shift, so reserving $\tau_{k+1}/2$ is conservative; if its strip is crossed, that half-threshold pays it. But the pending transition, its bounded horizon, and the box certification at activation have not been proved in v3. Simply allowing $q>k$ under the existing word “in-window” is insufficient: (W2), Lemma C(a)–(e), (RQ1)–(RQ5), and the §8.1 data type all assume an existing core.

### C-03 — MAJOR — Lemma S does not give the path length claimed for the thickened core

**Location.** §3.7 Lemma S, lines 929–944; §3.8 “All window points are exposed,” lines 978–989; (3.11)$'$, lines 1059–1062. The latter says that P7’s path to $(U^{\sim3}_{k_1})^c$ is replaced by one of length at most $\frac12M\mathrm{crit}_{k_1}+8M$ “inside the core box containing the point.”

**What is correct.** Lemma S is true on $\mathbb Z^d$. Its exterior-boundary input is stated in the correct adjacency pair: the nearest-neighbour exterior boundary of a finite nearest-neighbour connected set is $*$-connected. Timár, [*Boundary-connectivity via graph theory*](https://arxiv.org/pdf/0711.1713), *Proc. Amer. Math. Soc.* **141** (2013), 475–480, Lemma 2 (arXiv v2 p. 4), gives this precise version; Theorem 3 (arXiv v2 p. 5) also covers a finite $*$-connected set. Timár attributes the stronger form to Deuschel–Pisztora, *Probab. Theory Relat. Fields* **104** (1996), 467–482, Lemma 2.1. I verified Timár’s primary text directly; I did not inspect the original Deuschel–Pisztora page. The proof at v3 lines 934–942 then correctly puts one exterior boundary in one $A_i$. Thus a union of pairwise $*$-separated unthickened boxes encloses no point. Subject to the stated non-winding lift from the torus, this supplies qualitative exposure of points outside the core.

**Counterexample to the quantitative use.** Put $5^d$ core boxes of side $b=\mathrm{crit}_{k_1}$ into a $5\times\cdots\times5$ array, leaving one $\pi_{k_1}$-cube of gap between adjacent boxes. They are pairwise $*$-separated and $5^d\le\nu_{\max}$ for large $\lambda$. These may enter as separate box components at $k_1$, merge during the following shadows, and become one box long before the $n_q(k_1)$-scale ripeness time. Their $U^{\sim3}_{k_1}$ neighbourhoods overlap across each gap, so the central box lies inside one thickened cluster whose distance to $(U^{\sim3}_{k_1})^c$ is at least of order $2Mb$ along every coordinate direction. For $b$ large this is greater than the asserted $\frac12Mb+8M$. A point in the central gap has no “core box containing the point,” yet the gap belongs to the relevant small-field region: P5 (1.4), journal p. 488, defines $W_{k_1}=(Z_{k_1}^c)^{\approx2}$. Lemma S concerns the complement of the *unthickened* union and cannot bound distance to the complement of the *thickened* union. P7 (3.11), journal p. 522, makes its $3MR_{k_1}+8M$ estimate in the original single-core geometry; it does not assert the v3 per-box replacement for a dense array.

**Minimal repair and check.** Prove a path lemma for each connected component of the *thickened* union, with a length bound $C\nu M\mathrm{crit}_{k_1}$ and with the path kept in the exact characteristic-function domain used in P7 (3.11). The numerical exponent has room: $\nu\le C\lambda_k^{p_2}$ and $\mathrm{crit}_{k_1}=O(\lambda_k^2)$ give $C\nu M\mathrm{crit}_{k_1}=O(\lambda_k^{p_2+2})$, while $w_0=p_2d/2+3d$ satisfies

$$w_0-(p_2+2)=\tfrac12p_2(d-2)+3d-2>0\qquad(d\ge3).$$

Thus the already declared $\hat W=O(\lambda_k^{w_0})$ can absorb the larger path length without changing $p_R$, if the domain-confined path and the associated (3.11)$'$ estimate are proved. That geometric/domain check is absent, so §3.8 does not yet get all it needs from Lemma S.

### C-04 — MAJOR — the §4 LF-2 theorem omits the horizon hypothesis used in its proof

**Location.** §4.1 setting, lines 1124–1145; §4 theorem (iv), lines 1215–1221; §4.7 transfer, lines 1358–1374; §8.1 (H-$\lambda$), lines 1706–1724. The §4 theorem assumes only (G1), (G2), (B), (Rg), (K) and large $\lambda_0$. Its transfer proof additionally uses $k_f-k_0<\lambda_{k_0}$ and $\lambda_{k_f}\le\frac d2\lambda_{k_0}+c_d$.

**Counterexample and failed inequality.** Take $k_0=1$, one new cube at scale 1, no ripe $R$ event, and a large fixed $\lambda_0$. At equality in the base budget lower bound its finite budget can be $G_1=g_0-c_v\lambda_1|Z_1|_\#$. Since $2p_0>p_2\ge2d+3$, this exceeds $\tau_{t^*}+\sum_{j=2}^{t^*}w_j+1$ for sufficiently large $\lambda_0$, so (H6$'$) holds at $k_0$. Keep the increment bounds but choose $k_f$ arbitrarily far away. Because $w_j\asymp\lambda_j^{2d+1}$ and $\lambda_j$ grows at least linearly,

$$\sum_{j=2}^{k_f}w_j\longrightarrow\infty,$$

so choose $k_f$ with $A_2\lambda_1^{p_2}+\sum_{j=2}^{k_f}w_j>G_1$. Then (H6$^\flat$) fails already at $k_0=1$. The precise sufficient inequality used in §4.7,

$$A_2\lambda_{k_0}^{p_2}\ge(k_f-k_0)C_w\lambda_{k_f}^{2d+1},$$

does not follow from bounded positive increments alone. No future event or bank can alter failure of the transfer at scale $k_0$.

**Minimal repair and check.** Add (H-$\lambda$) explicitly to the §4.1 hypotheses and the §4 LF-2 theorem. §8.1 already does so. Then $k_f-k_0<\lambda_{k_0}$ and $\lambda_{k_f}\le\frac d2\lambda_{k_0}+c_d$ imply

$$\sum_{j=k_0+1}^{k_f}w_j\le\lambda_{k_0}C_w(\tfrac d2\lambda_{k_0}+c_d)^{2d+1}=O(\lambda_{k_0}^{2d+2})<A_2\lambda_{k_0}^{p_2}$$

for large $\lambda_{k_0}$, since $p_2\ge2d+3$. This closes this specific mismatch. It does not repair C-01–C-03.

### C-05 — MINOR — the abstract base history is not typed explicitly

**Location.** §8.1 “Abstract history” and (G1), (B), lines 1699–1712; §4.6(iii), lines 1353–1356. The history lists $Z_k$ only for $1\le k\le k_f$, while (G1) at the base step $0\to1$ refers to components of $Z_0$; (B) says their sum is empty for $k+1=1$. §4.6(iii) then treats the base as an $m=0$ event with gain $g_0$.

**Repair and check.** Declare $Z_0=\varnothing$, $Z^{(0)}_1=\bigcup_{q\in\mathcal N_1}B_q$, and apply (B) at $k=0$. Then (4.2) with $m=0$, $r\ge1$ has its intended base inequality $g_0r\ge\tau_{t^*}+\sum_{j=1}^{t^*}w_j+(r-1)E_1+1$ for large $\lambda_0$, because $2p_0>p_2>2d+2$. This is an interface omission, not an independent budget counterexample.

## Step and bank ledger

This ledger separates the arithmetic that checks from the transitions that fail above. It uses $\mu=k+1$, $\tau_t=2A_2\lambda_t^{p_2}$, $w_j=O(\lambda_j^{2d+1})$, $E_\mu=O(\lambda_\mu^{2d+1})$, and $h_\mu=O(\log\lambda_\mu)$. All asymptotic inequalities are for a fixed choice of typing constants and sufficiently large $\lambda_0$.

| Step | Required balance and result |
|---|---|
| Quiet shadow, including a hull without contact | From (B), $G'\ge G-v_\mu\ell/L-w_\mu$. Since $2\sigma_k=2(v_\mu+\sigma_\mu)/L$, the old $2\sigma_k\ell$ pays that loss and leaves $2\sigma_\mu\ell/L$; $\ell'\le\ell/L$, $t^{*\prime}\le t^*$, and $\nu,U$ stay fixed. Numerically (H6$'$)$^{\rm pre}$ follows. |
| New cube, with or without old parts | (W4) sets $U'=0$, $\nu'=1$. The new income $rg_k\asymp r\lambda_k^{2p_0}$ pays the new threshold $O(\lambda^{p_2})$, waiting costs $O(\lambda^{2d+2})$, and $(m+r-1)E_\mu$, because $2p_0>p_2\ge2d+3$. For large spines the reserve $v_\mu\sum\ell_i/L$ is used exactly as in §4.5 Cases 1b/2b. |
| All parts in-window, within cap | Let $X$ be the crossed strips. The set accounting gives $U'-\sum U_i\le\frac12\tau_\mu[\mu\notin X]-\frac12\sum_{\xi\in X,\xi\le k}\tau_\xi$; duplicates at the same old scale only add slack. One old threshold is freed because $m\ge2$: $\sum_{i\ne i_0}\tau_{t_i^*}\ge(m-1)\tau_\mu$. Half of one $\tau_\mu$ funds the new deposit or its crossed strip, and at least $\frac12(m-1)\tau_\mu$ remains for $E_\mu$ and the smallness shift. The strip union has $q'-k_1(t_0)\le\sum_{\xi\in X}(h_\xi+1)$; each released bank pays $O((h_\mu+1)\lambda_{t^{*\prime}}^{p_2-1})$ because $\lambda_\xi\ge\lambda_{t^{*\prime}}/(4c_*^2)$ and $(\log\lambda)/\lambda\to0$. The derivation does **not** establish that the output is an existing-core window (C-02). |
| Merge with a pre-window part | (W4) drops all banks and resets $\nu$ to 1. The freed $(m-1)\tau_\mu$ and spine reserve pay the restarted clock by the §4.5 Case 2b estimates. If the output is a point box at the merge scale, the exact Lemma C(e) condition fails (C-01). |
| Overflow merge | $\sum_i\nu_i>\nu_{\max}(\mu)$ gives $\sum_i\nu_i-1\ge\nu_{\max}(\mu)$. The released unit reserves pay $\tau_{t^{*\prime}}+\sum w+1\le(2A_2c'^{p_2}+o(1))\lambda_\mu^{p_2}$ in the bounded-spine branch, using $p_2>2d+2$; the large-spine branch uses the exponential size of the reserve. Banks are discarded. A point-box output has the same C-01 exception. |
| R removed or kept | Removal leaves no obligation. At a ripe kept component, the old $\nu+U$ and $\tau_k$ remain available and (W5) resets $U'=0$, $\nu'=1$. The gain $A'_3\lambda_k^{p_R}$ pays $C_R\lambda_k^{2d+1}+O(\lambda_k^{p_2})+O(\lambda_k^{2d+2})+1$ because $p_R>p_2+2d$. No bank is spent twice: a bank is present only while its scale remains in $\mathcal M$, and raising $q$ removes it permanently. |
| Window end at $k_0$ | The flat transfer needs (H-$\lambda$); C-04 shows why. Once transferred, the frozen shadow/event computation has a fixed threshold and no bank or ripeness clock. |

The bank formula is conservative even if two old lineages have the same merge scale: $\sum_iU_i$ counts both deposits, whereas the union $\mathcal M'$ counts that scale at most once. For any finite chain of nested or overlapping blocked strips, the number of traversed core scales is at most the sum of strip lengths, so no arithmetic example makes the *total* delay exceed the available per-scale banks under the Case 2a comparability bound. This does not validate the present state machine: the two-merge history reaches a future core after just two strips.

## Closeout

The independent refutation checks were: (i) test W1/W4 entries against the exact quantified statement of C(e); (ii) compute (W3) on a fully specified two-merge lattice history; (iii) distinguish the unthickened complement in Lemma S from $U^{\sim3}$ in P7 (3.11); and (iv) let the frozen horizon grow while retaining every §4.1 premise. C-01, C-02 and C-04 survive those checks as explicit contradictions. C-03 refutes the displayed per-box path length; a component-wide polynomial replacement is plausible but its allowed-domain proof remains open. The bank deposit, release, and exponent inequalities above show no separate numerical bank deficit for histories on which the bookkeeping is defined.

**Overall verdict: does not close.** A repaired version may close with (a) a last-box-entry exception in Lemma C(e), (b) a pending-core state and its activation proof, (c) a component-wide path proof for (3.11)$'$, and (d) (H-$\lambda$) in the §4 theorem. I cannot mark “closes with repairs” until (b) and (c) are proved for every transition and the $R$ domain.
