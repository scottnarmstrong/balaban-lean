# LFH7PRIME: can a strengthened H7 class pay the inherited-hole residual?

**Verdict (2026-10-13). REFUTED** as a consequence of P5 H7 or of the displayed P5–P7
small factors. **OPEN** as a new physical, history-funded inductive class. R1 excludes the
LFROOT3 constant coefficient if imposed, but its physical base and one-step preservation
are unproved; R2 is unavailable with P5's unchanged domain/locality clauses. Neither is
currently a closed Roland-independent repair of blocker 3. R3 remains OPEN.

**Scope/freeze.** Focused, refute-first design check at commit `283e59e8`: P5
`sources/s002200050433 (1).pdf` SHA256 `b3f0ef34`; P6 `s002200050470.pdf`
`ee0ca061`; P7 `s002200050486.pdf` `c48e08dd`; `LFROOT3.md` `78eed465`;
`Def6v2.lean` `627c158d`; `Def7.lean` `795e0a0a` (hash prefixes). Source
claims below refer to printed pages/equations; H7′ and its leaves are our proposals.
No physical coefficient or full P5–P7 induction was audited.

## Refutation gate: where the purported payment is missing

**PROVED (class counterexample, LFROOT3 §2; physical instantiation OPEN).** In the
two-step aligned-rectangle history, one old modular label $X_n$ contains a length-$n$
hole and a bounded active attachment. Its old P5/landed size $D_-(X_n)=O(1)$.
The nonzero constant $B(X_n)=\varepsilon_n<B_0e^{-\kappa D_-(X_n)}$ is analytic,
local, invariant, and has only the zero-mark P6 branch. P6 p. 34 requires
$Y\supseteq X_n$, $Y\in\mathcal D_K(\mathrm{mod}\,\Omega_K^c)$; completion of the
new, misaligned hole forces $D_+(Y)\ge cn-O(1)$. Hence
$b_{\rm ret}:=[D_+(Y)-L^{-1}D_-(X_n)-C_{d,L}|J|]_+=\Omega(n)$ at $J=\varnothing$.
The family fails any positive uniform per-hole bonus. This refutes an H7-only proof,
not the possibility that actual O(N) coefficients obey a stronger estimate.

**PROVED (source scope).** P5 p. 492 (1.18)–(1.19) gives $0/1$ characteristic
functions; neither formula yields a numerical factor in a surviving $B(X)$.
P5 pp. 495–96 (1.30)–(1.31) bounds $T_k(Z,\mathbb A_k\cap Z)$ by
$e^{-\ell p_2(\beta_k)-H_k|Z|_\eta}$ **after integration**, not each H7 term.
P5 p. 497 (1.38)–(1.39) bounds that term only by
$B_0e^{-\kappa d_k(X\bmod\Omega_k^c)}$. P6 p. 34 (4.32)–(4.34) claims a
new *coefficient* estimate before a separate operator gain; its displayed
old-term argument spends old modular decay and localization marks, with no
retained-hole factor. P6 (3.9) is an operator factor, and its new-seed part
vanishes in LFROOT3's seedless step (`VMOD-36` §3).

**PROVED (source scope); OPEN (physical factorization).** P7 pp. 519–20
(3.7)–(3.10) gives $e^{-p_2(\beta_k)-H_k|Z|_\eta}$ to an $R$ operator on a
**removed** component $Z$. P7 pp. 527–29 (3.23), (3.26)–(3.28) also creates
action-conversion boundary terms and resums old labels meeting removed
components. A different long **retained** hole is not charged by (3.10).
The two-label retained-hole cluster of `VMOD-41` §2 has bounded old sizes
and removed-component costs, but output size $\Omega(n)$. P7's stated gas
polymer-activity estimate does not display a termwise retained-hole gain. It may rely on a
physical cancellation/incidence rule; this remains OPEN, not REFUTED.

## R1: an explicit proposed H7′ and the one-step test

**PROPOSAL (not a source clause).** On a history $A$, let $\mathcal H_k(A,X)$
be the components $H$ of $\Omega_k^c$ wholly contained in $X$ for which
$X\cap\Omega_k$ meets a fixed-width collar of $H$. Let
$q_k(A,X)=\sum_{H\in\mathcal H_k(A,X)}|\{\pi'_k\text{-cells meeting the
boundary shell of }H\}|$ (fixed scale normalization). Add to the pre/post `D7Bdry2`
bound field of `IsRepPre2`/`IsRep2`, for every history, valid boundary $X$,
and every argument of the existing `hSetB2`/`H7Domain`:
$$\|B_A(X)\|\le B_*\exp[-a_kD_k(A,X)-\sigma q_k(A,X)],\qquad\sigma>0.\tag{H7′}$$
Take $a_{\rm pre}=3\kappa/2$, $a_{\rm post}=\kappa$ and $D_k=$ `d7SizePre`/`d7Size`;
the P5 continuous-tree version needs the separate `P5FineRealization` bridge.
`Def6v2.SFTermClauses`/`IsSFFamily2` retain their (H.2)–(H.7) small-field
clauses: the added field belongs to the **large-field** `bdry` record, not
to the small-field density. A zero-boundary witness makes the new class
inhabited; it does not establish the physical density belongs to it.

**PROVED conditional arithmetic.** For each P6 branch $(X,J,Y)$, H7′ pays
the output target rate $\tau$ only if a *producer* proves, uniformly in
history and torus,
$$\tau D_+(Y)+E_{\rm fib}\le a_kD_-(X)+\sigma q_k(A,X)+g|J|,
\quad g|J|\text{ supplied by marked localization}.\tag{P6-spend}$$
Here $E_{\rm fib}$ includes old-label and mark-fiber entropy; strict
prefactor slack must also fit $B_*$. In LFROOT3, $q_k(A,X_n)=\Omega(n)$,
so H7′ excludes the constant family unless $\varepsilon_n$ already has
the required decay; if (P6-spend) holds, it pays $b_{\rm ret}$. A bare
"straddles/adjacent" flag, or diameter alone for arbitrary high-dimensional
holes, does not imply (P6-spend). Scale-dependent collar growth may also
outrun this shell charge; its uniform domination and physical membership are OPEN.

**OPEN (preservation, not implied by P5 Theorem 1).** Base: exhibit the
factor in every physical initial boundary coefficient, despite P5
(1.18)–(1.19) being indicators. Step: prove (P6-spend) for the *actual*
background and mixed covariance square root, plus history-locality and
analyticity; show the next $q_{k+1}$ reserve survives at the same $\sigma$
after relabeling. R: prove an analogous cluster spend with old $q_k$ counted
**once per old coefficient** and P7 (3.10) only once per removed component,
including new action-conversion terms (3.23). Establish an allocation
identity preventing the same historical reserve from paying both P6 and R.
The post-R output must again satisfy H7′, not just ordinary H7. A new
boundary term adjacent to a retained hole but not containing it is outside
the displayed $q_k$ definition; either prove its residual zero or extend
the charge and `loc_hist` rule. These are genuine missing leaves, not
consequences of enlarging a bound field.

## R2: output labels, and decision

**REFUTED within the unchanged class.** P5 p. 496 (1.33) requires each
component of $\Omega_K^c$ to be wholly in or out of $Y$; (1.34) still
charges tree length inside a hole. P6 p. 34 explicitly constructs terms
over $Y\supseteq X$ in that class. The P3 (4.44) incidence component
$Y_1(J)$ plus a bounded neighborhood can cut a hole and need not contain
$X$; it then cannot be substituted for $Y$ in (4.33)–(4.34).
For a general inherited $B(X)$, old exterior spins, $h,g$, and history on
$X$ remain spectator arguments even at zero marks (P6 (4.32), p. 34).
Shrinking the label therefore also needs a new locality/history clause,
exact exponent decomposition, and P7 (3.26)–(3.28) cluster/support rules.
A constant term can sometimes be relabeled algebraically, but it does
not justify the relabeling uniformly over H7. A redesigned incidence
class is OPEN and would no longer be P5 H7 or the landed `D7Bdry2`.

**Decision/risk.** No completed Roland-independent R1/R2 route is shown.
The most testable conditional route is to derive (P6-spend) from the
physical producer, then a P7 retained-hole spend/factorization and a
base-plus-preservation theorem for H7′; if the physical terms have no
such gain, use a new output decomposition or R3's O(N)-specific
cancellation. The highest risk is that P5/P7 small factors live only
in operators or final activities, while H7′ demands a coefficient
factor at every scale. R1/R2 would make R3 unnecessary only after
those exact physical identities and the no-double-spend budget are proved.
