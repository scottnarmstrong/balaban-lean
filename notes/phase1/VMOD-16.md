# The long-hole test with Balaban's original modular size

**12 October 2026.** Response to `followup_r16.txt`. I checked the images of P1 printed p. 117 and P5 printed p. 496, then checked the P5 region rules and P6 printed p. 34 against the long-thin-hole construction of `GRAPH-GM-3.md` Proposition 2.1. The conclusion is **source-level**, subject to the paper-level verification of that proposition's two-step history: its obstruction persists for P5's original size $d_k$, not just for the covering size $d_k^{\rm cov}$. No contraction of a hole component appears in P5 (1.34).

## 1. Exact source definitions and the distinction from Definition 1.1

In P1 (2.26), printed p. 117, the class $\mathcal D_j$ consists of connected open domains satisfying the displayed formula
$$X=\bigcup_{\square\in\pi'_j:\,\square\subset X}\square.\tag{1.1}$$
The adjacent P1 (2.27) reads
$$d_j(X)=\inf\{M^{-1}|\Gamma|:\ \Gamma\text{ is a continuous tree graph contained in }X
\text{ and intersecting every }\square\subset X,\ \square\in\pi'_j\}.\tag{1.2}$$
The cover $\pi'_j$ consists of overlapping blocks of side $L$ partition cells. The formula uses **all** cover blocks contained in $X$, not a selected subcover. These are transcriptions of the displayed formulas on the PDF image, with the source's $\Gamma$ and $M$.

P5 (1.33), printed p. 496, first assumes a domain $\Omega$ whose components belong to $\mathcal D_k$, then defines
$$\mathcal D_k(\operatorname{mod}\Omega^c)
=\{X\in\mathcal D_k:\text{ any component of }\Omega^c
\text{ is either contained in }X,\text{ or disjoint with }X\}.\tag{1.3}$$
Its displayed (1.34) is
$$\begin{aligned}
d_k(X\operatorname{mod}\Omega^c)=\inf\{M^{-1}|\Gamma|_\eta:\;&\Gamma\text{ is a connected tree graph}\
&\text{in the continuous space, contained in }X,\text{ and}\
&\text{intersecting every cube from the cover }\pi'_k
\text{ which intersects }X\cap\Omega\}.\tag{1.4}
\end{aligned}$$
The tree may lie in $\Omega^c$ where that hole lies in $X$, but its geometric length is still counted in $|\Gamma|_\eta$. Neither (1.3) nor (1.4) identifies an entire hole to one point or gives its traversal zero length. P5's sentence following (1.34) says the function measures the size of the parts of $X\cap\Omega$ and the distances between them; it does not change the metric.

`FLUCTUATION.md` Definition 1.1 instead minimizes over **chosen** $\pi'_j$ cubes contained in $X$ whose union covers $X\cap\Omega$, and requires the tree to meet only those chosen cubes. Thus for a P1/P5 modular domain
$$d_j^{\rm cov}(X\operatorname{mod}\Omega^c)
\le d_j(X\operatorname{mod}\Omega^c).\tag{1.5}$$
Indeed every active point of $X$ lies in a $\pi'_j$ cube contained in $X$ by (1.1); take the subfamily of such cubes intersecting $X\cap\Omega$. A P5-admissible tree meets this entire subfamily and is admissible for the chosen-cover infimum. The landed `Fluctuation/SizeModDefs.lean` `ModAdmissible` and `dcovModE` implement the left side, not (1.4). Inequality (1.5) alone does not transfer an upper bound from $d^{\rm cov}$ to $d$; the counterexample below supplies a direct lower bound for $d$.

## 2. The two-step history in source notation

Use $d=3$, $L=8$, a fixed integer $r=R_{\rm base}\ge4L+20$, $R_j=r$, $\lambda_j=1$, and $k_0=0$. Let $\mathbb T_1=(\mathbb Z/8N\mathbb Z)^3$, $\mathbb T_2=(\mathbb Z/N\mathbb Z)^3$, where points of $\mathbb T_j$ index the $\pi_j$ partition cells. Choose $N$ much larger than $T+p+r$, in particular $N>4(T+p+r+L)$, so all sets and all relevant trees have a nonwrapping coordinate chart. `LF-RECONSTRUCTION.md` Definition I.2.0 gives this cube-torus convention; its Definition I.2.5 identifies $\pi'_j$ with all translated $L$-blocks. The paper-level derivation is `GRAPH-GM-3.md` Proposition 2.1.

At the first step take $Z_0=\varnothing$, $\mathsf P_1=\{0\}$ and $\mathsf Q_1=\mathsf R_1=\mathsf S_1=\varnothing$. The P5 (2.3), (2.6), (2.8) rules give $\Omega'_1=\mathbb T_1$ and
$$\Omega_1^c=H=[-3,3]^3,\qquad H\subset Z_1.\tag{2.1}$$
At the second step choose $p$ a fixed distance $\gg r+L$ from the old seed and put
$$\mathsf P_2=\{(p+t,0,0):0\le t\le T\},\qquad
\mathsf Q_2=\mathsf R_2=\mathsf S_2=\varnothing.\tag{2.2}$$
P5 (2.6) sums over arbitrary subdomains $\mathsf P_2\subset\Omega'_2$ that are unions of $\pi_2$ cells; this path is such a subdomain when $p$ is chosen outside the fixed old-seed neighborhood. P5 (2.8) removes the three-neighborhood of $\mathsf P_2$ by an $L$-block opening. In a neighborhood of the new path the resulting complement is precisely
$$F_T=[p-3,p+T+3]\times[-3,3]^2.\tag{2.3}$$
The remaining component of $\Omega_2^c$ is confined near the old seed and is separated from $F_T$. The latter is a single face-connected, hence also star-connected, hole component. The two active domains are unions of $\pi'_j$ blocks by their opening definitions. In $d=3$ the exterior of these two separated bounded boxes is connected; a path can be moved around either box, and consecutive translated $L$-blocks along such a path overlap. Thus their active connected components are connected unions of those blocks, as P5 requires of $\Omega$. The set-function identities and the admissibility of the two steps under (R1)–(R9) are proved on paper in `GRAPH-GM-3.md` §2; they have **not** been landed as a Lean theorem.

In scale-1 partition-cell coordinates take
$$X=[-4,8p+7]\times[-4,4]^2.\tag{2.4}$$
It is a connected union of old translated eight-blocks, hence $X\in\mathcal D_1$ by (1.1). It contains all of $H=\Omega_1^c$, so $X\in\mathcal D_1(\operatorname{mod}\Omega_1^c)$. It meets $Z_1$ and $\Omega_2$. The source $X$, the old hole, and the set of old $\pi'_1$ blocks intersecting $X\cap\Omega_1$ are fixed as $T$ grows. A grid tree inside this fixed rectangle meets all those blocks, so
$$\Delta:=d_1(X\operatorname{mod}\Omega_1^c)\le C_{p,r,L}<\infty\tag{2.5}$$
uniformly in $T$. This is the **source** $d_1$ of (1.4), not $d_1^{\rm cov}$.

## 3. The output and its original P5 size

Let $B$ be any bounded new-block nesting family attached to the fixed old source, as in `GRAPH-GM-3.md` §2. The raw saturation
$$Y_0=\operatorname{holeCl}_{\Omega_2}(X\cup B)\tag{3.1}$$
contains all of $F_T$. For $t$ in the middle third of the tube, its cross-section is just the seven-cell-wide $F_T$. An eight-block cannot fit in that cross-section. Thus $Y_0$ fails (1.1), and **P5's $d_2(Y_0\operatorname{mod}\Omega_2^c)$ is not defined**. Formally evaluating a tree functional on this outside-class set could give a bounded value because its active trace stays near the fixed source; that value is not P5 (1.34) on an admissible localization domain.

**Proposition 3.1 (source-size obstruction, proved from the history of §2).** Every $Y\in\mathcal D_2(\operatorname{mod}\Omega_2^c)$ with $X\subset Y$ obeys, for $T\ge64$,
$$d_2(Y\operatorname{mod}\Omega_2^c)\ge T-C_L,
\qquad C_L:=32+2L+4=52.\tag{3.2}$$
The bound is in new $\pi_2$-cell units; the factor $M^{-1}|\Gamma|_\eta$ in (1.4) makes one partition-cell step cost one. The extra four in $C_L$ allows the continuous open-cube endpoint convention. There are admissible solid rectangular completions with $d_2\le C_{p,r,L}(T+1)$, so the least source size of a block-union modular completion is $\Theta(T)$.

*Proof of the lower bound.* Since $X$ contains the scale-2 cell $(p,0,0)$ of $F_T$ and $Y$ is modular, (1.3) forces $F_T\subset Y$. For $t=16$ and $t=T-16$, put $x_t=(p+t,0,0)\in F_T$. By (1.1), some $Q_t\in\pi'_2$ satisfies $x_t\in Q_t\subset Y$. The transverse width of $F_T$ is $2\cdot3+1=7<L$. Therefore $Q_t$ has a point $z_t\notin F_T$. The other hole component is near the old seed, so $z_t\in\Omega_2$; thus $Q_t\cap Y\cap\Omega_2\ne\varnothing$. Formula (1.4) forces **every** admissible continuous tree $\Gamma\subset Y$ to meet both $Q_{16}$ and $Q_{T-16}$. Each block extends at most $L$ partition-cell units in the longitudinal coordinate beyond its $x_t$, even allowing continuous endpoints. The longitudinal separation of the two blocks is at least $T-32-2L$ up to a fixed endpoint convention. Any continuous connected tree meeting both has length at least that separation times the physical side of a new partition cell. The added four units in $C_L$ absorb the convention, so dividing by the scale factor in (1.4) proves (3.2). A path through $F_T$ itself still has this longitudinal length; there is no quotient edge of zero cost. $\square$

For the upper bound, choose a rectangular $Y_T$ of fixed transverse width large enough to contain the fixed old-hole component and $X$, and longitudinal extent from the old seed to the far end of $F_T$, with fixed padding. It contains both complete hole components and is a connected union of translated eight-blocks; hence it belongs to $\mathcal D_2(\operatorname{mod}\Omega_2^c)$. Only $O_{p,r,L}(T+1)$ translated blocks meet $Y_T\cap\Omega_2$. Joining a point of each by a grid tree inside $Y_T$ takes at most $C_{p,r,L}(T+1)$ normalized length. This proves the stated $\Theta(T)$ claim. The lower bound alone suffices for the transfer test.

## 4. Verdict on P6 and on a size-functional repair

P6 printed p. 34, after (4.32), says the P3 inequalities (4.48)–(4.49) continue with $d_j(X),\widetilde d_{k+1}(Y)$ replaced by the modular sizes $d_k(X\operatorname{mod}\Omega_k^c),d_{k+1}(Y\operatorname{mod}\Omega_{k+1}^c)$; it also says its output $Y$ contains $X$. P3 (4.48), printed p. 80, is the tree-size transfer $\widetilde d_{k+1}(Y)\le L^{-1}L^j\eta\,d_j(X)+d(2L+1)^d|\mathcal C|$. In the adjacent-scale specialization $j=k$, $L^k\eta=1$, so the old-size coefficient is $L^{-1}$. For the present example the derivative family is empty, $\Delta$ in (2.5) is fixed, and every admissible output has (3.2). Hence, for all sufficiently large $T$,
$$d_2(Y\operatorname{mod}\Omega_2^c)>L^{-1}d_1(X\operatorname{mod}\Omega_1^c)
+C|\mathcal C|\qquad(\mathcal C=\varnothing).\tag{4.1}$$
Thus the proposed **universal uncharged transfer is false for the source's own $d$**, provided the two-step history has precisely the P5 admissibility claimed in `GRAPH-GM-3.md`. The source does have additional large-field factors attached to the long $\mathsf P_2$ path; those could pay a modified estimate, but they are not the derivative charge $|\mathcal C|$ in the quoted transfer. This does not by itself refute the final equality or bound (4.33)–(4.34) by some different reorganization.

The branch in the follow-up asking for a corrected $d^{\rm cov}$ **if** the source $d$ succeeds therefore does not arise. The issue is not repaired by replacing $d^{\rm cov}$ with $d$ or by contracting the tube. More generally, let $D_2$ be *any* proposed size on the same block-union modular outputs satisfying a uniform G1 bound
$$n_{\pi_2}(Y\cap\Omega_2)\le c_1(1+D_2(Y)).\tag{4.2}$$
For each longitudinal location spaced $2L$ cells apart in the middle of $F_T$, the preceding block argument produces an active $\pi_2$ cell in $Y\cap\Omega_2$. Such cells are distinct: a block containing $x_t$ lies within $L-1$ longitudinal cells of $t$, and the resulting intervals are disjoint at this spacing. Thus $n_{\pi_2}(Y\cap\Omega_2)\ge (T-O(1))/(2L)$, whence
$$D_2(Y)\ge\frac{T-O(1)}{2Lc_1}-1.\tag{4.3}$$
If the old size remains bounded as in (2.5), no such $D_2$ can satisfy an uncharged transfer with a history-independent constant. In particular a formal zero-cost contraction of $F_T$ would break G1. One must change the output class to permit a site support with no active collar, as in `VMOD-15.md`, or charge the collar through a new large-field weight or another explicit geometric input. Each choice requires its own analytic and summability theorem.

The landed `Fluctuation/SizeMod*.lean` results `G1_cellCount`, `G1_card`, `G2_X`, `G2_S`, `G3_dcov`, `G3_dOmega`, `G4_subset`, `G4_dOmega_le_mod`, and `G5` remain **proved for their existing definitions**. They establish G1–G5 for the covering size and its active-support version; none states the missing P6 source-to-output transfer. The direct comparison (1.5) and the source lower bound (3.2) do not change those theorems. `VMOD-15.md`'s corrected decorated site-domain theorem remains a conditional alternative organization, not a proof of P6's printed block-union claim.

## 5. What can be sent to the author, and the remaining check

The precise candidate counterexample is: P5 (2.6) with a long path $\mathsf P_2$ as in (2.2), fixed P1/P5 boundary source (2.4), no interpolation derivatives, and any P1/P5 modular output containing $X$. Equations (2.5) and (3.2) contradict the source's asserted modular analogue of P3 (4.48). The mechanism is purely geometric: saturation of one seven-cell-wide hole plus the required eight-block union forces an active collar of unbounded longitudinal extent, and P5 (1.34) charges that extent.

The displayed geometric inequality is refuted without choosing a nonzero coefficient: it is asserted as the size comparison supporting the resummation. Before making a stronger claim that the actual nonzero P6 coefficient violates its final bound, one must instantiate **all** restrictions on $\mathsf P_2$ and on the boundary term's multi-index, beyond P5 (2.6) and the reconstructed (R1)–(R9) set rules. `GRAPH-GM-3.md` verifies those set rules but does not show that a chosen old boundary coefficient is nonzero for this long-path multi-index. An additional restriction excluding the path, or an explicit $T$-dependent decay payment, would have to be cited and included in the transfer hypothesis. None appears in the defining formulas (1.1)–(1.4) or in P6's p. 34 transfer sentence. **Confidence:** high in the PDF transcription and the geometric contradiction under the stated history; medium in its promotion to a claim about an actual nonzero RG coefficient.
