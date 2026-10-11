# Review of `notes/phase1/BACKGROUND.md` (brief D-V-review)

Referee: independent session, 2026-10-11. Refute-first. No Lean was written or run. Checked: every step of
Prop 5.1; the structure of Thm 5.2 and Lemma 5.3; the minimiser identity (5.3); §6 against the page images of
P2 (journal pp. 610, 611, 631, 632, 633, 635, 636, 637, 638 = PDF pages 4, 5, 25, 26, 27, 29, 30, 31, 32);
§7; the statements of the landed `global_bound`, `constrained_sup`, `constraintForm_isUnit`,
`multiscale_coercive_sharp`, `IsSmoothField`, `IsConstraintField`, `Standing`, `IsAdmissibleWeights` and
`exists_analytic_fixedPoint`. Severity: BLOCKER (a stated result is false or cannot be frozen), MAJOR (a
statement or proof must change before freezing or Lean assignment), MINOR (local repair).

## Verdict: APPROVE-WITH-CHANGES

No BLOCKER. The core mathematics is sound: the contraction of Prop 5.1 is correct (every identity and
inequality checks, with the constants repaired as in V-01 and V-05), the exact minimiser identity (5.3) is
correct and is a real improvement on P2 (3.48), the composition identities of §6.4 are correct, and the
document's two claims about errors in transcription are confirmed or sharpened (V-11, V-12). Four MAJOR items
concern what is frozen (Prop 6.4, Theorem 6.1(iii), Def-5(b), the proof-carrying definitions), and one concerns
how much of Lemma 5.3 is really proved (V-04).

---

## Findings

### V-01 (MINOR) The input (G) is landed, but not in the form assumed
Location: §2 row G-2(iv); §3 Lemma 3.3; §5.1 (choice of $\gamma_1=\tfrac18$).
The document says G-2(iv) is "in progress (W16)". The landed `Balaban.Multiscale.global_bound` already gives
$|u|_0$, the bond bound with spacing at each endpoint, and $|\Delta^Du|_2$, all $\le B\,C_f$ for
$|f|_2\le C_f$, with $B=B(d,L)$. Differences from what Prop 5.1 uses:
1. Range of $\alpha$. `global_bound` assumes $|\alpha(x)|\le\texttt{coerciveConst}\,d/(2\ell(x)^2)$, and
   `coerciveConst d` $=\min(1/d,1/2)/2$, so the range is $\gamma_1(d)=\min(1/d,1/2)/4$ ($=1/12$ for $d=3$),
   smaller than the $1/8$ of the document. The same range is in `Standing` (hence `constrained_sup`,
   `constraintForm_isUnit`). Coercivity and invertibility (`multiscale_coercive_sharp`, `..._isUnit_sharp`)
   hold for $|\alpha|\le\tfrac18\ell^{-2}$, so only the Green bound limits the range.
2. The landed bond bound is for the bonds $(x,x+e_\mu)$, $x\in\Omega_1$, $\mu\le d$ (and, if $x+e_\mu\in\Omega_1$,
   at both endpoints). A bond $(x-e,x)$ with $x-e$ in the collar is not covered. Lemma 3.1 uses
   $|\Delta_e\tilde u(x)|\le\|u\|_*/\ell(x)$ for all $2d$ neighbours. For such a wall bond it follows from
   $|u(x)|\le|u|_0$ and $\ell(x)=L$ (wall sites lie in layer 1), at the cost of a factor $L$ in $B_1$.
   So "the norms are exactly those of the landed `global_bound`" is true for $|\cdot|_0,|\cdot|_2$ and
   $|\Delta^D\cdot|_2$ and true for $|\partial\cdot|_1$ only after this factor.
3. `global_bound` is scalar. Euclidean norms in $\mathbb C^N$ cost $\sqrt N$ (the document already says the
   constants depend on $N$).
4. The separation hypothesis is $2d\log L\le(\texttt{agmonRate}\,d/4)(\varrho-1)$. State $R_0(d,L):=\max(3L,\cdot)$ with this
   expression so that `R_0` of Theorem 5.2 is the one used by the Lean lemma.
Fix: define $\gamma_1:=\min(\tfrac18,\texttt{coerciveConst}\,d/2)$ and redo the order of choice in §5.1 with it
(only numerical constants move; $c_0=c_6/2\le\gamma_1/8$ keeps (5.3) valid). Note also that the
$|\Delta^D\delta\phi|_2$ bound of Prop 5.1 can be read off `global_bound` directly; the recovery from (P-1)
in step (iv) is then unnecessary. Replace "in progress" by "landed; bridge lemma needed (items 1–4)".

### V-02 (MAJOR) Proposition 6.4: the smallness hypothesis does not match the proof
Location: §6.7.
The conclusion needs Prop 5.1 for $\mathbb B_j$ with the data $(\delta\Psi,\phi_0|,\alpha_0|,f_1|)$, whose own
smallness is "$(\delta_0,\delta_1^{(j)})$ with $\delta_0,\delta_1^{(j)}\le\delta_*$ and $C_N\delta_1^{(j)}\le c_6/2$" where
$\delta_1^{(j)}=(2K_2+1)\delta_1$ is the new bound on $|\delta\Psi|$. The proposition instead assumes
"$K_2(2K_2+1)\delta_1\le c_6$", which neither implies nor is implied by these conditions (and
$|\delta\alpha'|_2\le K_2\delta_1<c_6$ already holds from the $\mathbb B'_k$ problem). Uniqueness for
$\mathbb B_j$ is the only point where the hypothesis is used, so the stated result is not what the proof gives.
Fix: assume "the hypotheses of Prop 5.1 hold for $\mathbb B'_k$ with $(\delta_0,\delta_1)$ and for $\mathbb B_j$ with
$(\delta_0,(2K_2+1)\delta_1)$". Since $(P4)$ is used only with $g\equiv0$ here, nothing else changes. Because this
is a frozen statement (I-2c), the exact form matters. Also state that $\phi_0|_{\Omega_1}$ with
`IsSmoothField` for $\mathbb B_j$ follows from $\ell_{\mathbb B_j}\le\ell'$ at points of $\Omega_1$, including bonds to
the collar of $\Omega_1$ (these are bonds at a point of $\Omega_1\subseteq\Omega'_1$, so they are covered by the
$\mathbb B'_k$ hypothesis; the proof says this only implicitly).

### V-03 (MAJOR) Theorem 6.1(iii) cannot be written as a Lean declaration as stated
Location: §6.3(iii), §6.5.
The statement uses objects defined only by reference to P2: the composed Lagrangian (4.15), the reduced
function $\mathcal A$ of (4.14), $Q(\mathbb B'_k,\mathbb B_j)$, $a(\mathbb B'_k,\mathbb B_j)$ (4.5)–(4.10), the class
$\{\psi:(\psi,h)\in\tilde\Psi(\mathbb B_j;c_1),\,|\alpha(\mathbb B_j;\psi)|'_2<c_0\}$ in which $\alpha(\mathbb B_j;\psi)$ is itself the
background field being defined. "Critical point of $\mathcal A$" needs $\mathcal A$ to be differentiable on an open
set, which is not shown. The last clause ("the minimal value is the quadratic form (4.12)") is not proved in §6.5
at all (only the critical-point system is); P2 Lemma 4.1 (4.12) is a statement about the Gaussian composition,
not about the hard-spin minimum.
What I checked and found correct: the linear system (6.3) and its solution. With
$\psi_n(x)=Q_n\phi-\frac{a^{(p)}}{a_n}L^{2(n-p)}t$, averaging, (C1) $L^{2(n-p)}u_n=u_p-u_{p-n}$ and
$a^{(p)}u^{(p)}=1$ gives $t\,a^{(p)}/a_p=Q_p\phi-\psi'_p$, i.e. (6.2). This matches P2 (4.19)–(4.21), (4.18), (4.7) on
pp. 632, 635, 636, including $a_0=\infty$ for the gap rows. The reduction of (4.17) to (EL) for $\mathbb B'_k$ is also
correct.
Fix: freeze I-2 as (i) domain, (ii) identities, (iv) complex data, plus the following exact form of (iii): for the
composed system (6.3), the $\phi$-equations and the constraint (all explicit equations in unknowns
$(\psi,\phi,\alpha)$, with $\alpha$ restricted by $|\alpha|'_2<c_0$), $(\Psi,\phi',\alpha')$ is the unique solution.
Drop the "critical point of $\mathcal A$" and "minimal value" clauses unless a consumer (I-4, I-5) needs them; the
roadmap's I-2 asks only for the formula and (4.39).

### V-04 (MAJOR) Lemma 5.3 is a sketch that hides a geometric lemma; it is the weakest part
Location: §5.3.
The pieces I checked and found correct: (A2) the identity
$\tilde\phi\cdot\tilde\phi=1-\tfrac12\sum h_yh_{y'}(\phi^y-\phi^{y'})^{\cdot2}$; (A3) $\Delta_e\tilde\phi=\sum\Delta_eh_y(\phi^y-\phi^{y_x})$
from $\sum\Delta_eh_y=0$; (A5) the residual formula (I re-derived it from $S$, $H_D(\alpha_0)\phi_0=-\Delta\bar\phi_0+\mathfrak b(\phi_0)+\dots$ and the block
equation); the wall term lives in layer 1, so $\ell^2=L^2$; the quadratic B-spline facts ($\beta\ge\tfrac12$ on $[-\tfrac12,\tfrac12]$, $C^{1,1}$,
partition of unity) and (h1)–(h3).
What is missing for a formalizable proof, in order of risk:
1. (A1) "chains of at most $C(r,L,d)$ adjacent blocks" is not automatic: blocks in layers far below $n$ can lie
   within distance $O(L^{n+1})$ of a layer-$n$ site (separation only gives $\mathrm{dist}(\Omega_{m-1}^c,\Omega_m)>\varrho L^{m-1}$),
   and a chain through them would have length unbounded in $n$. The chain needed is always inside layers
   $\ge n-1$: a block of layer $n-1$ active at $x$ is within $2L^{n-1}$ of $x$, and the whole segment lies in $\Omega_{n-1}$
   because $\mathrm{dist}(\Omega_{n-1}^c,\Omega_n)>\varrho L^{n-1}\ge3L^n$; a block of layer $n+1$ active at $x$ is within $2L^{n+1}<\varrho L^n$ of
   $\Omega_{n+1}$, so the segment lies in $\Omega_n$, layers $n,n+1$ only. A short lemma with exactly these two
   statements should be written; Lean will need it as a separate declaration.
2. (h4) is stated for $h_y=\tilde h_y/D$ but the bounds on first and second differences of $D=\sum\tilde h_{y'}$ (a
   sum of bumps of different scales, a fixed function on $\mathbb Z^d$) and the quotient rule are not written.
   Since $D\ge2^{-d}$ and each $\tilde h_{y'}$ with $h_{y'}(x)\ne0$ has scale $L^{n(y')}\ge\ell(x)/L$, the constant is
   $C(d,L)$; say so.
3. Near the wall the collar bumps (scale 1) have differences $O(1)$, not $O(\ell(x)^{-1})$. This is fine only because $\ell=L$ there, so
   $O(1)\le O(L)/\ell$. The statement of (h4) with "$C=C(d,L)$ and $\ell(x)^{-1}$" is true, but the reader is not told why it
   survives at layer 0.
4. (h2): the stated inequality chain "$\mathrm{dist}>\varrho L^{n+1}>2L^{n+2}$" is right for $\varrho\ge3L$; for layers $m\ge n+2$ the argument
   must be done for each $m$ (the bump of a layer-$m$ block extends $L^m$ outside the block, and $\mathrm{dist}(x,\Omega_m)>\varrho L^{m-1}\ge3L^m$).
Simplification: $\alpha_0\equiv0$ works. Prop 5.1 needs only $|\alpha_0|_2\le\delta_0$ and no smoothness, and in (A5) the third
term is bounded by $|\alpha^y||\phi^y|\ell^2\le C_1L^2\delta$ without any cancellation between $\alpha^y$ and $\alpha_0$. This removes
$\alpha_0=\sum h_y\alpha^y$, the exclusion of layer 0, and part (b)'s bound on $\alpha_0$.
The Lean estimate for this lemma (1,800–2,800 lines plus 1,200–1,800 for the interpolation) is plausible. Do not
assign it before items 1–2 are written as exact lemmas.

### V-05 (MINOR) Lemma 4.1 omits a factor $|h|$
Location: §4.1, proof of Lemma 4.1, "Second" term.
The term is $\nu\,\psi'\cdot h$, bounded in the text by $\nu|\psi'|\le2\nu\varepsilon\le2\delta$; this drops $|h|$. (R4) gives only
$|h|^2\le1+\delta^2/\nu_*$. Correct bound: $\nu|\psi'||h|\le2\nu\varepsilon+2\nu\varepsilon\,\delta/\sqrt{\nu_*}\le2\delta+2\sqrt{\nu_*}\varepsilon\,\delta\le4\delta$, using $\nu\le\nu_*$ and
$\sqrt{\nu_*}\,\varepsilon\le\delta$. The same $|h|$ appears in $\nu\Psi\cdot h'$ only through (C3), which is already stated for
$\psi_0\cdot h'$, so that term is correct. The conclusion of Lemma 4.1 is unchanged.

### V-06 (MINOR) Lemma 6.2 (R3), (R4), collar: three small gaps
1. (R3) uses $1-\Psi_0\cdot h=\tfrac12|\Psi_0-h|^2$, true only for $|h|=1$. In general
   $1-\Psi_0\cdot h=\tfrac12|\Psi_0-h|^2+\tfrac12(1-|h|^2)$ and the extra term is bounded by (R4) at scale $k$:
   $\mu L^{2n}\tfrac12|1-|h|^2|\le\tfrac12\delta^2$. P2 handles this in (4.27) ("using the condition on $h$", p. 638).
2. (R4) for $\mathbb B_j$ with parameter $C_4K_1\delta$ needs $C_4K_1\ge1$ (fine, state it) and $\mu L^{2j}\le\mu L^{2k}$.
3. The collar–collar cases of (R1) (both sites in the gap, or one in the gap and one outside $\Omega'_1$; wall bond
   $|\phi'(x_1)-\Psi'(x_2)|\le K_1\delta/\ell'$) and (R3) at gap sites ($\Psi=\phi'$, $|\phi'|=1$, $\mu|1-\phi'\cdot h|\le\tfrac12\mu|\phi'-h|^2+\tfrac12\delta^2$) are not treated.
All are one-line repairs.

### V-07 (MINOR) The $L$-dependence of $C_4$ is an artefact of the literal reading of P2's condition
Location: §6.6 (R1), the UNCERTAIN paragraph, §8.3 "New candidate errata (ii)".
P2 p. 637 (after (4.24)) compares $\psi_n(y_2)$ with $\psi_{n-1}(x)$ for **all** $(n-1)$-blocks $x\in B(y_1)$ of the
neighbouring $n$-cell, which is P2's (1.11) condition $|\psi_j(b_+)-\psi_{j-1}(x)|<\delta$, $x\in B(b_-)$. For such $x$ the path
from $x$ to $y_2$ crosses up to $L$ blocks of layer $n-1$ of $\mathbb B_j$, which may be layer $n-1$ of $\mathbb B'_k$, so $\ell'$ can be $L^{n-1}$ along it and
the stated bound $dK_1\delta$ is not derived by P2's one sentence; $dLK_1\delta$ is. The document's (R1) uses **physically
adjacent** blocks only. For that condition the bound has no $L$: for adjacent $y_1$ (layer $n$) and $y_2$ (layer $n-1$) pick neighbouring
sites $z_1\in y_1$, $z_2\in y_2$; the path $x_1\to z_1$ inside $y_1$ has all bonds with $\ell'\ge L^n$ (length $\le dL^n$), the bond $z_1z_2$,
and the path $z_2\to x_2$ inside $y_2$ has $\ell'\ge L^{n-1}$ (length $\le dL^{n-1}$); the variation is $\le(2d+1)K_1\delta$, so
$|Q_n\phi'(y_1)-Q_{n-1}\phi'(y_2)|\le(2d+1)K_1\delta$ and $|\Psi(y_1)-\Psi(y_2)|\le(2d+3)K_1\delta$. Hence $C_4=C_4(d)$ for the document's
domain, and the UNCERTAIN paragraph and the "candidate erratum (ii)" should say: P2's literal condition would need $L$, the
adjacency version does not. Also correct the attribution: the cross-layer sentence is after (4.24) on p. 637; (4.26)–(4.27) on
p. 638 are the (R3) estimates and (4.28) is the general relation between $\psi^{(j)}_k$ and $\phi_k$.

### V-08 (MAJOR) Def-5(b): the domain and the "constant package"
Location: §7 Def-5(b); Theorem 5.2 item 2.
1. The domain $\tilde\Psi^c(\mathbb B_k;c_1,c_0)$ is not the union of the $\tilde\Psi^c(\delta,\varepsilon)$ allowed by Theorem 5.2. The condition
   (C3), $\mu L^{2n}|h'|<\delta^2/\varepsilon$, becomes **stronger** when $\varepsilon$ grows, so $\tilde\Psi^c(\delta,\varepsilon)\not\subseteq\tilde\Psi^c(c_1,c_0)$ in general (take $\delta=c_1$,
   $\varepsilon=c_0/10$). Consumers who use $(\delta,\varepsilon)$ with small $\varepsilon$ would fall outside the defined domain. Define the domain
   as $\mathcal D:=\bigcup\tilde\Psi^c(\delta,\varepsilon)$ over the admissible $(\delta,\varepsilon,\mu)$ (an open set); the solution is defined on
   $\mathcal D$ by uniqueness, which is exactly what item 2 ("functions for different $(\delta,\varepsilon)$ agree on overlaps") proves.
2. "If $\mu L^{2k}c_0^2>c_1^2$ the domain is empty" is false: the set of data is not empty; it is Theorem 5.2 that does not
   apply (its hypothesis $\mu L^{2k}\varepsilon^2\le\delta^2$ fails). State it so.
3. Choosing $(c_0,c_1,K_1)$ by `Classical.choose` inside a frozen definition makes the object depend on a non-canonical
   choice. Better: the predicate `IsSmallSolution c₀ data (φ,α)` (carrying $c_0$ as a parameter), the definition of the
   function by `if h : ∃! s, IsSmallSolution c₀ data s then h.choose else default` for a stated $c_0$, and Theorem
   "there are $c_0,c_1,K_1$ such that for all data in the domain the `∃!` holds and the bounds hold". Frozen downstream
   statements then quantify over such $c_0$ (they only need existence) and nothing depends on a choice.
4. Openness of $\tilde\Psi^c$ is not "finitely many strict inequalities": a complex point has many decompositions $\Psi+\Psi'$. The set is the image of an
   open subset of $\mathbb R^m\times\mathbb C^m$ under the linear surjection $(x,x')\mapsto x+x'$, hence open. Say this; the solution depends only on the sum, so it is well defined.

### V-09 (MAJOR) Def-5(a), (c): proof-carrying definitions and the API
Location: §7 Def-5(a), (c).
Def-5(a) defines $\phi(\mathbb B_k;\Psi,h):=\texttt{hΨ.choose}$ with the proof `hΨ` as an argument, and Def-5(c) defines
$\psi(\mathbb B_j,\mathbb B'_k;\Psi')$ from that $\phi'$. Every consumer statement then carries proof terms, and (c) inherits the
domain restriction of (a)/(b) although the formula (6.2) is explicit. Recommended shape (nothing is lost, and rule 4
of AGENTS.md is respected):
* `IsMinimizer`, `IsEL`, `IsSmallSolution` as predicates; `bgField` as a function on the subtype of data with the `∃!` proved, or as a total function by
  `dite`, with the characterization theorem stating membership of the domain.
* `composeField G G' a φ' Ψ'` defined by (6.2) for **any** $\phi'$, no `∃!`; Theorem 6.1 then says: if $(\phi',\alpha')$ is the small solution for $\mathbb B'_k$, then
  `composeField ...` is in the $\mathbb B_j$ domain and $(\phi',\alpha')|_{\Omega_1}$ is the small solution for $\mathbb B_j$. Def-5(c) is then only an abbreviation
  at the point of use. The values of $\Psi$ off $\Omega_1\cup C(\Omega_1)$ must be fixed in the definition (say $0$), since $\Psi$ is a function on the torus; the problem for $\mathbb B_j$
  does not see them.
* The data type `BgData G` must fix: $\Psi:\mathbb T\to\mathbb C^N$ (or $\mathbb R^N$), the predicate "constant on each layer-$n$ block, $n\ge1$" (arbitrary on $C$), $\tilde h$ block-constant on layers $1..k$.
  Statements must say that only values on $\Omega_1\cup C$ matter, or the analyticity statement is about irrelevant coordinates too (harmless but confusing).
Quantifier order for the `∃!` theorems is otherwise fine: $\exists c_0,c_1,K_1,R_0$ (depending on $d,L,N$) $\forall k,N_0,\varrho\ge R_0,G,a,\mu,\Psi,h$.

### V-10 (MINOR) Boundary case in the uniqueness class; weights interval
1. Theorem 5.2 item 1 requires $|\alpha|_2<c_0$ while item 3 gives $|\alpha|_2\le K_1\delta$ and the constants satisfy only $K_1c_1\le c_0$ (§5.4: $c_1\le c_6/(2K_1)=c_0/K_1$), so equality $|\alpha|_2=c_0$ is not excluded at $\delta=c_1$. Take $K_1c_1\le c_0/2$. The same strictness is needed in §6.4 ("$\le K_1\delta\le c_0$"
   must be $<c_0$) and in Theorem 6.1 ("and $K_1\delta\le c_0$").
2. Theorem 5.2 assumes $a_n\in(\tfrac12,2]$, Lean's `IsAdmissibleWeights` is $[\tfrac12,2]$, and §4.1 says the closed case works (with $|Z|\le\tfrac18$). Use the closed interval in the statement.
3. (iv) of Theorem 6.1: for $\mathbb B_j$ the pair $(\delta',\varepsilon)=(2C_4K_1\delta,\varepsilon)$ must satisfy $\delta'\le\varepsilon$ to apply Theorem 5.2. Since $C_4\ge d+2$ the hypothesis "$4dK_1\delta\le\varepsilon$" does not give it. Use
   $\varepsilon':=\max(\varepsilon,\delta')$; then (C3) is inherited because $\delta^2/\varepsilon\le\delta'^2/\varepsilon'$ (as $\delta^2\le\varepsilon\delta'$) and $\mu L^{2j}\varepsilon'^2\le\delta'^2$ needs one more check; state the exact parameters.

### V-11 (confirmed) The extra factor in (1.15)
P2 p. 611 (PDF page 5) prints
$|\phi-Q^*(\psi+\psi')|<K_1\delta,\ |\partial^\eta\phi|<K_1(L^j\eta)^{-1}\delta,\ \dots,\ |\Delta^\eta\phi|<K_1(L^j\eta)^{-2}\delta,\ |\alpha|<K_1(L^j\eta)^{-2}\delta,\ |\delta\phi(\psi',h')|<\varepsilon+K_1\delta$.
`review/papers/P2-variational-problems.md` §2 prints $K_1(L^j\eta)^{-1}\delta$ on the first line. The document is right; the
review is wrong (not P2). Also confirmed on the page: (1.16) is $|\phi-h|<K_1(L^j\eta)^{-1}\delta/\sqrt\nu$ and $|\nu\phi\cdot Q^*h'|<K_1(L^j\eta)^{-2}\delta^2$; the appearance of $Q^*h'$ supports
the block-constant $h'$ of §1.3.

### V-12 (MINOR) Page references for other P2 rows
(4.4) $a_{r+1}=aa_r/(L^{-2}a+a_r)$, $a_r=a(1-L^{-2})/(1-L^{-2r})$, $a_r\searrow a(1-L^{-2})$ is on p. 631 (confirmed). The misprint $[a(1-L^2),a]$ is in **(4.8) on p. 633**, not p. 632 as ER-034 row and §8.3 say (p. 632 has (4.5)–(4.7)); (4.8) reads $a_p\le a(\Lambda_p(y),\mathbb B_j)\le a_1=a$, then "the interval $[a(1-L^2),a]$". The document's conclusion is right.
(4.7) is as in §6.5 (volume average of $1/a_{p-n}$, $1/a_0=0$ by the sentence after (4.18), p. 635), (4.18)–(4.21) as in (6.2).
ER-035 confirmed (p. 610, (1.11): $|\nu(|h|^2-1)|<\delta^2$).

### V-13 (MINOR) Faithfulness of the data domain (author's Q1), details
P2 (1.11)–(1.12) read on pp. 610: (R2)–(R4), (C1)–(C3) match, including $|\nu(1-(\psi_j)_0\cdot h)|<(L^j\eta)^{-2}\delta^2$ and
$|\nu h'|<(L^j\eta)^{-2}\delta^2/\varepsilon$. Units: P2 states $0<\nu\le1$ with $L^k\eta=1$ (p. 611: "we can take $L^j\eta=1$" for $\Omega_j=T_\eta$), so $\mu=\nu\eta^2=\nu L^{-2k}$
and $\nu\le1\iff\mu\le L^{-2k}$; the conversions $\nu(\dots)<(L^j\eta)^{-2}\delta^2\iff\mu L^{2j}(\dots)<\delta^2$ are right. Differences to record in the Lean docstring:
1. (R1) interface condition: P2 requires $|\psi_j(b_+)-\psi_{j-1}(x)|<\delta$ for **all** $(j-1)$-blocks $x$ of the neighbouring cell; the document requires it for adjacent blocks. The document's set is larger; by chaining inside the cell (R1 same layer), P2's set contains the document's set for $\delta$ replaced by $dL\delta$ and conversely. So the two are equivalent up to a factor $C(d,L)$, not equal; the text "contains the interface bonds" should read "is implied by".
2. Collar $\Lambda_0$: P2 p. 610 says "one layer of big blocks in $\mathscr D_1$ surrounding $\Omega_1$", a band of width $\sim L$ (of fine sites, since (1.13) sets $\psi_0=\phi|_{\Lambda_0}$ pointwise), not one site. The equations see only the sites adjacent to $\Omega_1$; so the one-site collar gives the same theorem (a weaker hypothesis) but is a different predicate. Whether I-4/I-5 use conditions on $\psi_0$ at distance $>1$ from $\Omega_1$ cannot be decided from P2.
3. (C3)/(R3) at layer 0 and $h'$ on layer 0: (1.12) states them for $j=0..k$; the document restricts $h'$ to layers $1..k$. Harmless (they are not used).

### V-14 (MINOR) Prop 5.1: remaining small points
* The polarisation remark in Lemma 3.2 should say "each of the three pieces of $R$ is a bilinear expression bounded directly by the same estimates", since a symmetric bilinear form of norm $C$ on the diagonal does not by itself give $|B(u,w)|\le C\|u\|\|w\|$ with the same $C$. The Lipschitz bound is true.
* Lemma 3.1: the coefficient $(1+2d)$ is correct only because the neighbour-difference term is bounded by $|\partial v|_1$ (not $\|v\|_*$); the text writes "$\le 2d(\delta_0/\ell)(\|v\|_*/\ell)\ell^2$", which is a weaker true bound and would give $1+4d$ in total. State it with $|\partial v|_1$.
* The data hypothesis (P4) is more general than any use in I-1, I-2 (all uses have $g\equiv0$). It costs one line of Lean ($H_0\tilde g$). Keep it only if I-4 needs it (§10 Q2).
* Analyticity: `exists_analytic_fixedPoint` needs $T$ analytic on a neighbourhood of the closed ball; this holds because invertibility of $H_D(\alpha_0+\xi)$ extends to a slightly larger radius, and the parameter $\alpha_0$ enters $G(\alpha_0+\xi)$ analytically. Say so once.

### V-15 (MINOR) Prop 5.4 hypotheses are stated more weakly than the landed lemma needs
§5.5 says `constraintForm_isUnit` "needs only `IsSmoothField` with $\delta\le(300d^2)^{-1}$". It takes `Standing G a ν α δ φ`: `IsConstraintField` (adds $|\phi|\le\tfrac32$ and $|\phi\cdot\phi-1|\le\delta$, both true here), $|\alpha(x)|\le\texttt{coerciveConst}\,d/(2\ell^2)$ (the range of V-01, so $c_0\le\gamma_1$ is needed there too) and `δ² * smallnessConst d ≤ 1/4`. State it with these. $G-\Pi\succeq0$ for real data is correct (the range of $G^{1/2}T$ argument).

---

## What was checked and found correct (no finding)

* Prop 5.1: the exact identity $H_0u=-2\delta\alpha(1+u)+2(\phi_0+\delta\phi)\cdot F_s-2K\delta\phi+R(\delta\phi)+H_0\tilde g$ and (5.2),
  the equivalence $u=0\iff\mathcal N(\delta\alpha)=\delta\alpha$ via invertibility of $H_D(\alpha_0+2\delta\alpha)$ (needs $|\alpha_0+2\delta\alpha|_2\le\tfrac34\gamma_1$: OK),
  (5.1), the estimates of $\mathcal N(0)$, the Lipschitz constant, the self-map, the bound $|\delta\alpha|_2\le2|\mathcal N(0)|_2$, $K_2$, uniqueness by recentring, and the use of `exists_analytic_fixedPoint`
  (its hypotheses `hmaps`, `hlip`, analyticity on `closedBall × P`).
  The "no inverse of $\phi_0\cdot G\phi_0$" claim is right.
* §5.4: constants, uniqueness by recentring (needs $c_0+C_3\delta\le c_6$: OK), conjugation argument for real data, and the exact identity
  $A(\sigma)-A(\phi_*)=\tfrac12\langle\sigma-\phi_*,H_D(\alpha_*)(\sigma-\phi_*)\rangle$. I rederived it: $A(\sigma)=\tfrac12\langle\sigma,H_D(0)\sigma\rangle-\langle\sigma,S\rangle+c$ (expansion of (1.2) with
  $\langle\Psi,Q_n\phi\rangle=\langle\Psi,\phi\rangle$ for block-constant $\Psi$ and the wall bonds giving $\mathfrak b(\Psi)$), $\sum_x\alpha_*(x)|\sigma(x)|^2=\sum_x\alpha_*(x)$ on the sphere, and positivity
  of $H_D(\alpha_*)$ for real $|\alpha_*|\le\tfrac18\ell^{-2}$ is `multiscale_coercive_sharp` ($c_0\le\tfrac1{64}$ here). So uniqueness of the **global** minimiser needs only the existence of one small-$\alpha$ solution, as the document says;
  "no condition on $\alpha$ is needed" in item 4 is true for the conclusion but the proof does use $|\alpha_*|_2<c_0$ for positivity; say "no uniqueness class is needed".
* §6.4: the identity (6.4) from (6.3') and (6.2), the uniqueness class computation $L^{2n}|\alpha'|\le K_1\delta L^{2(n-p)}\le K_1\delta$ ($p\ge n$), block-constancy of $\Psi$ on $n$-blocks (an $n$-block of $\mathbb B_j$ lies inside a single $p$-block of $\mathbb B'_k$ because $\Omega'_{p}$ is a union of $p$-blocks and hence of $n$-blocks), $\kappa\le1$ from monotonicity of $a_r$.
* §4.3 (effective potential at $\lambda=\infty$): exact formula and the constants $\gamma_2=\tfrac15$, $C_2=2$ re-derived; valid for $|h|=1$ as stated.
* Lemma 6.2 (E1), (E2), (R1) same layer ($3K_1\delta$), (R2) with the corrected threshold ($\tfrac12d^2x^2+2x+x^2\le(d+2)x$ for $x\le d/(d^2+2)$ holds).
* P2 translation of the sphere constraint at the gap: P2 (4.17) fourth line, confirmed on p. 635.

---

## Answers to §10

1. **Data domain.** Acceptable as the definition of $\tilde\Psi,\tilde\Psi^c$ for I-1 and I-2, provided the docstring records the two differences of V-13 (adjacent-block interface condition; one-site collar instead of a band of 1-blocks) and V-08.1 (the domain of the complex field is a union). Sources decide: $h'$ is block-constant (P2 (1.16) has $Q^*h'$, p. 611); (R1)–(R4), (C1)–(C3) are as printed (p. 610). Sources I have read do not decide whether I-4/I-5 need conditions on $\psi_0$ beyond the sites adjacent to $\Omega_1$; ask seaturtle2 only if the consumers' statements mention $\Lambda_0$ at distance $>1$.
2. **Defect version.** For I-1 and I-2 only $g\equiv0$ is used (Theorem 5.2, item 6, Prop 6.4). Whether P3–P7 use $g\ne0$ is not decided by P2. If the decoupled fields of I-4 are solutions of the constrained system for complex data, then $g\equiv0$ for them as well, because $\phi\cdot\phi=1$ persists under analytic continuation in the parameters. Keep (P4) in Prop 5.1 only if I-4's design needs it; it is cheap but it enlarges the frozen statement.
3. **Hölder.** P1 (3.107) uses $|\partial^2\psi^{(j)}_k|<K_1C_{\alpha_1}(L^j\eta)^{2-\alpha_1}\varepsilon_k$ (ER-016, `P1` review §3), which needs the Hölder bound of $\partial\phi$ with one fixed exponent. So keep it, but as a separate frozen item (I-1(e)), with $\theta$ fixed, so that it does not gate I-1(a). G-2(iii) is landed (`prop49`, as stated in the brief).
4. **Weights.** Agree with the recommendation: I-1 for `IsAdmissibleWeights` ($[\tfrac12,2]$), I-2 for the one-parameter family (6.1) with a common $a_1$ for $\mathbb B_j$ and $\mathbb B'_k$ (P2 (4.4), p. 631; $a_j=\frac{1-L^{-2k}}{1-L^{-2j}}a_k$ with the same $a_1$). Confirmed that (C1) holds for (6.1) and fails for general weights.
5. **Constants depend on $N$.** Yes: say $(d,L,N)$ in the interface (V-01 item 3).
6. **Mass range.** $\mu=0$ is covered: `global_bound` is stated for $0\le\nu$, Lemma 4.1 is trivial for $\nu=0$, (R3), (R4), (C3) are void. The strictness $0<\nu$ of P2 is not needed.
