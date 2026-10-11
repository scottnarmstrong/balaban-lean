# Refute-first audit of LF-RECONSTRUCTION, Part I

**Verdict.** Part I does not close as written. The abstract LF-2 counter is plausible under its stated positive-scale hypotheses, and I found no counterexample to its merge accounting. Four stand-alone geometric or flow assertions have missing hypotheses or false conclusions, and the printed constant quantifier prefix is inconsistent. The P5/P6 set-function translations are substantially faithful, but the iterated hull is an extra convention whose agreement with P6's one-pass prose has not been established. This is a mathematical and source-correspondence audit, not a Lean proof certificate. Confidence is high in P1-01–P1-05, medium in P1-06 and in the conditional LF-2 assessment.

## Frozen scope and method

The audited text is **only Part I, §§I.0–I.7**, at `/home/scott/Balaban/notes/phase1/LF-RECONSTRUCTION.md`, git commit `e2c83ae`. Its local read-only copy [PART1-frozen.md](PART1-frozen.md) has SHA-256 `84cfbfd1348d0366a1137f9a9b2684dc637859f33befee204c57467f4a030654`; all Part I line numbers below refer to that snapshot. P5 is `s002200050433 (1).pdf`, SHA-256 `b3f0ef3491fc63b3988768893c1452b4bd1458a5f3e408e6af6000a555fd9a0f`; P6 is `s002200050470.pdf`, SHA-256 `ee0ca061c9a7418d5da907a4dd09b66fb247f46bffcf68f83fa3ba502c342fc4`. I extracted their text layers locally as [P5.txt](P5.txt) and [P6.txt](P6.txt), and checked the formulas and surrounding prose in P5 §2, pp. 501–512, and P6 §2, pp. 3–4, plus P6 p. 22. P7 (`s002200050486.pdf`, SHA-256 `c48e08dd439878a0245cceb6e6aead787a8ce7671865f6360c8464a7e579d2e9`) was used only for the indicated downstream context. For the change comparison I used ARCH v4 at commit `44141ef` (current file SHA-256 `aaa3a0f397f04ed2117eaa19f9a82a6475587c6b777c7aa3f0d118e2a118e859`) and the prior audit `LF-V4-AUDIT-astra.md` (SHA-256 `3ee87a288b9e17be73650c3fe57a66abcd6c8fb633b6d916fd1de03e5ac53e22`). The manuscript-audit skill's focused, refutation-first protocol was used. I made no changes under `/home/scott/Balaban` and did not inspect the concurrently written Part II.

The acceptance criterion for this audit was an exact source-rule comparison, a concrete attempted refutation of each named lemma, a check of the fifteen changes, and an explicit account of what prevents Lean statements from being formed. The findings below survived a second check against the hypotheses at their point of use. I did not independently verify the cited Timár lemma, the P2/P3 page images, or the analytic inputs (B) and (Rg), which Part I assigns to later parts.

## Findings

### P1-01 — BLOCKER: the constant prefix quantifies over impossible values of $M$

**Location.** §I.1.3 row 5 and row 6, frozen lines 178–180; §I.1.4, lines 200–206; §I.0 item 13, lines 88–90. The row-5 condition is “$\kappa_1\ge4d\log((2L+1)M/M_1)+2$,” while the prefix fixes $\kappa_1$, then $M_1$, then states “$\exists m_0'\ \forall m\ge m_0'$” with $M=L^m$.

**Argument and refutation check.** Fix any finite $\kappa_1,M_1,L>1$. The right side tends to infinity as $m\to\infty$. Thus no $m_0'$ makes the row-5 inequality true for every $m\ge m_0'$. Enlarging $M_1$ before that universal quantifier does not help. The manuscript marks this coupling UNCERTAIN, but the displayed quantifier prefix and the assertion that the row-6 conditions are lower bounds are nevertheless false together. This blocks the claimed uniform flow instantiation, independently of LF-2's conditional proof.

**Repair.** Replace the final universal quantifier on $m$ by a controlled choice of $m$ with a bounded ratio $M/M_1$, and verify every other row-6 lower bound for that choice; or obtain a localization estimate without this ratio condition. State the actual quantifier order before claiming the full chain.

### P1-02 — MAJOR: disjoint neighbourhoods fail for the unrestricted flow data

**Location.** (I.3), frozen lines 103–117, and Lemma I.2.13, lines 412–419. The text infers “$R_k:=R_0\lambda_k^2\le\hat R_k$” from $\lambda_k\le\hat\lambda_k$, then uses $[R_{k-1}]\le[\hat R_{k-1}]$ in (I.4).

**Counterexample.** Take $d=3$, $L=3$, base coefficient $R_{\mathrm{base}}=32$, $a=9/8$, $\gamma_0=1$, and $\beta a=e^{-100}$. Then $\lambda_0=-100$, $\hat\lambda_0=-99$, so the running radius is $32\cdot10000$, larger than the hatted radius $32\cdot9801$. On a sufficiently large scale-1 torus let $X=\{0,\omega_1e_1\}$, where $\omega_1=2[32\cdot9801]+L+11=627278$. Its two points are distinct $\omega_1$-components, while each thick neighbourhood has radius $[32\cdot10000]+1=320001$. Their neighbourhoods overlap because $2(320001)>627278$. All logarithmic perturbation bounds in (I.2) hold with $\epsilon=0$. The initial §I.1.1 assumption is merely $\beta>0$; the later large-$\beta$ condition is absent from this lemma.

**Repair.** State $\lambda_{k-1}\ge0$ or directly $R_{k-1}\le\hat R_{k-1}$ in the flow specialization of I.2.13, and qualify (I.3) accordingly. Under $\lambda_0\ge\lambda_*\ge1$ the advertised separation calculation is valid. The general first sentence of I.2.13 remains valid.

### P1-03 — MAJOR: (G1) attribution is false with the hypotheses printed in I.3.8

**Location.** Lemma I.3.8, frozen lines 568–601, especially “$r\ge R_0\ge4L+20$” at line 601. Its hypotheses say $R_0\ge4L+20$, $R_k\le r_k$, and $R_{k-1}\le r_k$, but do not say $r_k\ge R_0$ or $\lambda_k\ge1$.

**Counterexample.** Use a large cube torus, $L=3$, base coefficient $R_{\mathrm{base}}=32$, and $\lambda_0=\lambda_1=0$, so $r_1=R^{\rm run}_0=R^{\rm run}_1=0$. Start the step $1\to2$ with $Z_1=\varnothing$. Choose $\mathsf P_2=\{p\}$ and $\mathsf Q_2=\mathsf R_2=\mathsf S_2=\varnothing$. Then $U'_1=\varnothing$, $\Omega'_2=\mathbb T_2$, and $\Omega_2=\mathrm{Op}_1(\{p\}^{\sim3};\mathbb T_2)$. Both $p$ and $p+e_1$ lie in $\Omega_2^c\subset Z^{(0)}_2$. The only seed is $\{p\}$. For $x=p+e_1$, the claimed bound is $\mathrm d(x,p)\le s'r_1=0$, which is false. The region rules and all printed hypotheses are satisfied. The same omission propagates to the unqualified invocation of I.3.8 in I.3.9.

**Repair.** Add $r_k\ge R_{\mathrm{base}}$ (equivalently here $\lambda_k\ge1$) and monotonicity of the radius sequence where the proof uses it. The choice $s_*=4$, $s'=5$ and $R_{\mathrm{base}}\ge4L+20$ then survives the displayed distance sums. State locality I.3.9 under these hypotheses or under the corrected attribution lemma.

### P1-04 — MAJOR: the generating-set conclusion needs a uniform lower radius

**Location.** Lemma I.3.10(c) and its “Consequently” sentence, frozen lines 655–667. Its proof yields distance $>LMR_j$, then identifies a Lean `GeneratingSet` with fixed separation parameter $\varrho=LMR_0$ without assuming $R_j\ge R_{\mathrm{base}}$.

**Counterexample to the stated implication.** Keep $L=3$ and take an arbitrarily large base coefficient $R_{\mathrm{base}}$, but put $\lambda_0=\lambda_1=0$. At step $0\to1$ choose one $\mathsf P_1$ cube and no other new cubes; at step $1\to2$ choose no new cubes, with $k_0=0$ so there is no hull. The first large-field set and its $Z_1$ halo have bounded index radius depending on $L$, independent of $R_{\mathrm{base}}$, because both running radii are zero. A scale-2 cube twenty indices from the first event belongs to $\Omega_2$ on a large torus, while the first event lies in $\Omega_1^c$. Their fine-site distance is $O(ML^2)$, whereas the claimed fixed threshold is $LMR_{\mathrm{base}}L$ at $j=1$ and can be made arbitrarily larger. The valid estimate $>LMR_1=0$ does not supply it. This counterexample avoids the removal overwrite, so Lemma I.3.12 does not repair it.

**Repair.** Add $R_j\ge R_{\mathrm{base}}$ for the relevant scales, as follows from the intended $\lambda_j\ge1$, or use the actual minimum of the running radii in the generating-set parameter. Also explicitly fill the terminal $\Omega_{k+2}=\varnothing$ field required by the cited Lean `GeneratingSet` structure.

### P1-05 — MAJOR: I.5.6(c) is false when $k_0=0$

**Location.** Lemma I.5.6(c), frozen lines 1402–1419. The proof uses “$\nu_{k_0}\le\beta_{k_0}^{-1}$” at line 1417, though the convention $k_0=0$ when $\beta\nu>1$ makes that inequality false.

**Counterexample.** Set $d=3$, $L=3$, $a=9/8$, $\gamma_j=\delta_j=1$, $\nu=1/81$, and $\beta=10^8$. Then $k_f=\hat k_f=1$, $k_0=0$, and a minimal admissible torus has $\ell=ML^{k_f+1}=9M$, hence $n_0=9$. The claimed inequality is $n_0\ge e^{\hat\lambda_0/2-1}/\sqrt2=\sqrt{\beta a/(2e)}$, which is greater than $9$. Increasing $\beta$ only widens the failure. The printed hypotheses $k_f\ge1$ and (I.2) hold.

**Repair.** Restrict part (c) to a genuine $k_0$ with $\beta_{k_0}\nu_{k_0}\le1$. When $k_0=0$ by convention, prove (H-T) by its empty index range. Treat $k_f=0$ separately in §I.5.7, since I.5.6 itself assumes $k_f\ge1$ whereas §I.1.4 quantifies over all $\nu\in(0,1]$.

### P1-06 — MAJOR, UNREFUTED-TENTATIVE source correspondence: iterated hulling is additional data

**Location.** (R8), frozen line 477; Definitions I.3.2–I.3.3, lines 494–500; §I.0 item 4, lines 61–64. P6 p. 22 says that if a component of the large-field domain has diameter below the critical size, “we replace it by a smallest rectangular parallelepiped containing it.” It does not specify simultaneous iteration to a fixed point. The side test is listed as a change, but iteration after hull-induced merging is not separately identified as a deviation from that source sentence.

**Configuration distinguishing the readings.** On a large two-dimensional torus take contact width $\omega=5$ and critical side $b=40$. Let $C_1$ be the connected L-shaped set $\{(0,y):0\le y\le20\}\cup\{(x,20):0\le x\le20\}$ and $C_2=\{(24,0)\}$. They are distinct width-5 components. A single simultaneous hull round yields $[0,20]^2\cup C_2$; the new set is one width-5 component but is not a box. A second round fills $[0,24]\times[0,20]$, adding, for example, $(22,10)$. Both the first and merged components have Euclidean diameter below $40$, so the distinction does not rest on replacing P6's diameter test by a side test. Thus the two rules are genuinely different as set functions. The example does not decide whether Balaban intended repeated application; it does show that literal source fidelity has not been proved.

**Repair.** Label fixed-point hulling explicitly as an architectural extension of P6 p. 22, or provide a source argument that P6's operation is iterative. For an exact source theorem, distinguish the one-pass and closure outputs and prove the needed budget and generating-set properties for the chosen one.

### P1-07 — MINOR: the radius notation and several interfaces are not Lean-ready

**Location.** §I.1.1 (I.3), lines 115–117; §I.1.2, lines 125–145; Definition I.3.1 at lines 461–470; (G1) at lines 1183–1188; Lemma I.5.2 (F1), lines 1204–1207. The symbol $R_0$ denotes both a fixed coefficient and the $k=0$ member of $R_k:=R_0\lambda_k^2$; literally substituting $k=0$ makes $R_0=R_0\lambda_0^2$. The rule $U_0=\varnothing$ avoids the negative index $R_{-1}$ only by prose. In (F1), $n_q(a+x)$ is written with $x\ge0$, though $n_q$ is defined only on natural indices. The abstract (G1) should explicitly require each old seed to be contained in one next-scale component; its phrase “same component ... as a seed” otherwise carries an implicit typing obligation for successors and attribution sets.

**Repair.** Use $R_{\mathrm{base}}$ and $R^{\rm run}_k$; define the $k=0$ step by cases; bind $x\in\mathbb N$ in (F1); choose an extended-distance type for empty-set distances; and put seed containment, nonempty seed families, and the indexing of all component data into the `LF2Hyp` structure. These are definitional repairs, not counterexamples to the intended large-$\beta$ theorem.

### P1-08 — MINOR: the advertised $\lambda_*$ list is not one closed list

**Location.** §I.1.3 row 16, frozen line 190; §I.5.3, lines 1238–1258; §I.5.7, lines 1421–1424. Row 16 promises (Λ0)–(Λ11) and (Λ12)–(Λ13). The instantiation additionally invokes (Λ12′), $\frac23e^{x-2}\ge2L^2$, to obtain $\beta_{k_0}\ge2L^2$ and $k_0<k_f$. It is not in the displayed conditions defining $\lambda_*$, nor in row 16's enumeration. It may follow from a stronger listed condition, but no implication is shown.

**Repair.** Include (Λ12′) in the formal `LamStarConditions`, or prove and cite its redundancy. Separate the abstract LF-2 conditions (Λ0)–(Λ11) from the extra flow-instantiation conditions so the theorem's binder is unambiguous.

## Source-rule comparison

| Part I rule | Source check | Verdict |
|---|---|---|
| (R1)–(R3) | P5 (2.1)–(2.3), pp. 501–502: $U_k$, coarsening, and blocks at distance $>LMR_k$ | Correct index translation, with the $k=0$ exception needing a typed case. |
| (R4) | P5 (2.6), (2.8), p. 502: $\mathsf P\subset\Omega'$ and blocks contained in $\Omega'$ avoiding $\mathsf P^{\sim3}$ | Correct under the all-offset $L$-block cover chosen in I.2.5. |
| (R5) | P5 (2.14), (2.43), (2.45), pp. 504, 511–512: $\mathsf Q\subset\Omega^{\sim3}$, $\mathsf R\subset\Omega$, avoiding $(\mathsf Q^{\sim})^{\approx}\cup(\mathsf R^{\sim2})^{\approx2}$ | The radii $[R_k]+2$ and $2[R_k]+4$ follow by neighbourhood composition. The weaker $L-1$ consequence in the remark on P5 (2.46) is declared. |
| (R6) | P6 (2.1), (2.3), pp. 3–4: $\mathsf S\subset\Omega''^{\sim-3}$ and block distance $>2MR_k+M$ from $(\Omega''^c)^{\sim4}\cup\mathsf S^{\sim}$ | Correct conversion to $[2R_k]+3$. |
| (R7)–(R9) | (R7) is bookkeeping; P6 p. 22 supplies hull prose; $R$ removal and overwrite are architectural choices | These are not literal P5/P6 §2 set functions. In particular see P1-06. |

The use of every offset in $\pi'_{k+1}$ remains an explicit uncertainty in I.2.5, frozen lines 308–318. P5 (2.4) is compatible with it but does not alone prove the exact cover identity. This uncertainty is not promoted to a mathematical counterexample; settle it from P1's definition of $\pi'$ before asserting literal source equivalence.

## Checks of the named proof claims

| Claim | Refutation attempted and result |
|---|---|
| I.2.13 | Two singleton components at the minimum permitted separation give equality in the bound when $R\le\hat R$; the low-$\beta$ configuration P1-02 defeats the unrestricted flow specialization. |
| I.3.4 | Tested a hull touching and merging another component and a later second fill. Since each nonstationary round adds a torus cube, termination by $|\mathbb T_j|$ and determinism of the chosen simultaneous map stand. P1-06 is about fidelity to P6. |
| I.3.8 and I.3.9 | The witness chains use at most $2[R_k]+L+3<\omega_{k+1}$; the four length sums fit $4r_k$ or $5r_k$ when $r_k\ge R_{\rm base}$. P1-03 defeats the printed weaker hypotheses. The locality proof's level-by-level witness argument appears sound after that repair and seed containment. |
| I.3.10 and I.3.12 | The local separation $>LMR_j$ and the removal overwrite survive the distance check. Their fixed generating-set parameter fails without $R_j\ge R_{\rm base}$ (P1-04). |
| I.4.8 | Checked a pure shadow, a fresh seed, direct contacts, and a hull contact followed by another round. Each old spine is charged once and each spanning tree uses at most seeds minus one edges. The pure-shadow length bound in (4.1) survives; it depends on corrected (G1), monotone $r_k$, and large tori for the point-spine equivalence. |
| I.4.10; I.4.12–I.4.13 | Tested Active/Pending merges, repeated pushes, activation, overflow, a reset after a Pre ancestor, and a released merge strip. The core is nondecreasing under (T4), so the floor argument and the one-box core proof survive under the stated LF-2 hypotheses. I found no explicit history violating C4 or C. |
| I.5.1 | A winding projected spine still has a connected finite lift; maximal $\rho$-separated points of the lift give the printed $O(\rho^{d-1}(\ell+\rho))$ count. No counterexample found. |
| I.5.4 | Rechecked the budget inequality (B.7), the bank release in (B.10), the cap bound on $\Lambda'$, both long-spine branches, the kept-$R$ payment, and transfer (B.20). No counterexample found to the **conditional abstract theorem**. This does not discharge its analytic hypotheses (B), (Rg), or the flow interface defects above. |
| I.5.6 | The increment and upper-horizon arithmetic in (a)–(b) survives when $k_f\ge1$; the $k_0=0$ example P1-05 refutes (c) as stated. |

The other proved geometric claims in I.2–I.3 were sampled at their uses: cyclic distance conversion, block-opening inclusions, the finite-hull properties, the seed disjointness calculation, lineages, and the local/global comparison. Lemma S remains conditional on its cited exterior-boundary input; its proof's reduction to a single $*$-component is consistent with that input. I did not elevate that cited result to an independently verified source claim.

## The fifteen changes from ARCH v4

| Item in §I.0 | Audit judgment |
|---|---|
| 1–3: width, (G1), radii | The larger width and weaker within-component attribution are sufficient for the displayed witness chains in the intended positive regime. Minimality of the added $L$ is not shown. Item 3 needs P1-03's lower-radius premise. |
| 4: hull trigger | Side rather than diameter removes the one-cube side discrepancy; the fixed-point closure also needs the source qualification in P1-06. |
| 5–6: lifted spines, event bound, floor | The lifted count, spanning-tree charge, and reset invariant survive the tested histories; these changes address genuine gaps in the prior architecture. |
| 7: counting constants and conditions | The polynomial-versus-exponential comparisons are viable and the Case 2b split survived. The list for flow instantiation needs P1-08. |
| 8–9: flow horizon, final $K$ | A final scale $K\le\hat k_f$ is coherent. The claimed all-branch torus bound is false by P1-05; $k_f=0$ needs its own interface. |
| 10–11: generating sets, locality | Moving P3's $M_1$-cube construction to Part II is appropriate. Locality is conditional on corrected attribution; fixed generating-set separation needs P1-04. |
| 12: short spines | Restricting point replacement to pure shadows preserves the stated radius argument; no event-spine counterexample to the new rule found. |
| 13: constant order | The proposed reordering leaves the impossible universal $M$ quantifier P1-01. |
| 14: scope of Lemma L | Restriction to the localized ripe lineage addresses the prior global counterexample; analytic restriction remains expressly open. |
| 15: interface details | $d\ge3$, $\omega_0$, and the $k_0=0$ frozen branch are sensible. P1-05 shows the latter is not fully reflected in I.5.6. |

## Closeout

All named proof claims have a verdict above. P1-01–P1-05 are refutation-surviving findings with explicit configurations or quantifier contradictions; P1-06 is a documented source-fidelity uncertainty with a distinguishing configuration; P1-07–P1-08 are interface defects. No manuscript or Lean file was edited. The abstract LF-2 proof remains conditional on (B) and (Rg), and source equivalence remains conditional on the $\pi'$ cover and P6 hull interpretation. The appropriate next gate is to repair the stated hypotheses and prefix, then re-audit the flow instantiation and source-rule declaration before freezing Lean declarations.
