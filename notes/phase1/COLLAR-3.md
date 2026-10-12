# The collar in the first P7 window background: a source and consumer audit

## Verdict

**CB-1 remains OPEN for the physical P7 window.** P7 (2.13) and the landed `WindowPieces.windowGenSet_Ω` identify the *layers* of the glued generating set. They do not identify the value of the original field $Q^*(\mathbb B_{k_1,k},\mathbb B_k)\psi$ on its Dirichlet collar. P2 (4.9) defines an averaging map on the blocks of a generating set and gives an identity clause on common blocks; it supplies neither a formula for $Q^*$ on a newly exposed layer-zero site nor an overlap rule for the three P7 pieces. The candidate parent-field formula below makes the missing rule exact, but it is not a consequence of the cited results.

**CB-2 remains OPEN at the scale asserted in P7 (2.49).** The printed small-field functions control specified $k$- and $k_1$-scale regions and window blocks. Neither the printed bound (2.48) nor the landed interior theorem controls the physical minus reference datum on every site of the window collar by $C\widehat W_k\delta_{k_1}$. The only unconditional pointwise bound from two real data-domain conditions with thresholds at most one is $|\Delta\Psi|<4$; it does not meet the small perturbation premise of the landed response theorem. No fully P7-admissible counterexample is established here.

**The consumer audit is decisive.** Part III.6.4 uses the response on every layer of $X_{\rm win}$ in its multiplier and mass sums, and on the surfaces ${\rm st}(Z_{k_1})$ and ${\rm st}(Z)$. The small-factor proof for $\varkappa_4$, the analytic continuation in III.9.6, and Theorem III.8.9 inherit that use. A collar response with exponential decay would suffice only after a geometric distance bound and revised estimates for these whole-window sums. Neither the printed P7 hypotheses nor `WindowPieces.Hyp` supplies that bound. III.7.1 has a separate local background comparison and does not cite (2.49′) as its response input.

The exact conditional replacement for (2.49′) is proved in §4 from the landed weighted response theorem. It keeps both the lower-layer and collar data as an explicit decaying term. Its hypotheses and constants are stated there; it is **not** an unconditional replacement for P7 Lemma 2.4.

## 1. Which datum does the first background read? (CB-1)

Write $G=\mathbb B_{k_1,k}$ and $I=\Omega_1(G)$, with one-site Dirichlet collar
$$C_G=\{x\notin I:\text{some }y\in I\text{ is adjacent to }x\}.$$
P7 pp. 500–501, (2.13)–(2.16), first forms the background $\phi_k(G;\widetilde\psi)$ from the original window field. P7 p. 508, (2.46), then names $\widetilde\psi=Q^*(G,\mathbb B_k)\psi$. The later reference field is
$$\psi^0_{k_1,k}=\psi(G,\mathbb B_k(U_k);\widetilde\psi^0_k),
\qquad \phi^0_k=\phi_k(\mathbb B_k(U_k);\widetilde\psi^0_k)\tag{1.1}$$
from (2.40). P7 (2.14) composes a local-step background *from the first window background*; it does not replace the first datum by (1.1).

For clarity, name the three generating sets of (2.13) $P_0=\mathbb B_{k_1}(W_{k_1})$, $P_1=\mathbb B_k$, and $P_2=\mathbb B_k(U_k)$, and their restricting regions
$$R_0=Z_{k_1},\qquad R_1=Z\setminus Z_{k_1},\qquad R_2=\widetilde U_k\setminus Z.\tag{1.2}$$
The landed `WindowPieces.pieces`, `WindowPieces.windowGenSet`, and `WindowPieces.windowGenSet_Ω` give, for each $n\ge1$,
$$\Omega_n(G)=\bigcup_{i=0}^2\bigl(\Omega_n(P_i)\cap R_i\bigr).\tag{1.3}$$
Their `Hyp` is a block-union and margin condition on the restricted layers. It has no spin-field member, no assertion that $C_G\subset\bigcup_iR_i$, and no common-value condition on overlaps. Consequently (1.3) cannot be substituted into a formula for the boundary values of $\widetilde\psi$.

Here is the **candidate explicit parent datum** that a bridge from P7's actual $Q^*$ must prove. Let $b_{n_i(x)}(x)$ be the $P_i$ block containing $x$, where $n_i(x)$ is its layer index and $n_i(x)=0$ means the surviving fine site. With parent fields $\psi^{(i)}$, define, for $x\in C_G\cap R_i$,
$$\Psi^{\rm par}_i(x)=
\begin{cases}
\psi^{(i)}_{n_i(x)}(b_{n_i(x)}(x)),&x\in\Omega_1(P_i),\\
\psi^{(i)}_0(x),&x\notin\Omega_1(P_i).
\end{cases}\tag{1.4}$$
For a single globally inherited parent $\mathbb B_k$, this reduces to its multiscale block spin at the parent's local layer, with the fine spin in its layer-zero region. Formula (1.4) is meaningful for the glued window only if (i) every collar site is assigned a parent piece or the original field is separately specified outside the union of (1.2), (ii) the assigned parent fields agree where assignments overlap, and (iii) the actual $Q^*(G,\mathbb B_k)\psi$ has this value. The last condition is the **CB-1 bridge**. It is not proved by (1.3). If $Q^*$ uses a different interpolation at a site released from a parent block, (1.4) must be replaced by that interpolation, with its coefficients from the original kernel.

P2 p. 633, (4.9), does not remove this ambiguity: its $Q(\mathbb B'_k,\mathbb B_j)$ takes a conditional average $Q(\Delta_p(y'),\mathbb B_j)\phi$ for newly generated blocks and copies $\phi_p(y')$ for common blocks. The displayed definition acts on *block variables*; the formula for the conditional average is P2 (4.6). Thus the common layer-zero case, $x\in C_G\cap\Omega_1(\mathbb B_k)^c$, has the explicit inherited value $\psi_0(x)$ under the identity clause. A site in $C_G\cap\Omega_1(\mathbb B_k)$ is in layer zero of $G$ but lies inside a positive parent layer, so that clause does not identify its value. Moreover P7 writes $Q^*$ for the original lift, while P2 (4.9) is a definition of $Q$. Identifying these operations at all collar sites requires a separate kernel identity. The landed `DeltaPsiDef.psiTilde` assigns the unrestricted `BlockV` coordinate $\psi_0(x)$ off $I$. That coordinate is not shown to be the inherited physical value if $x$ is inside a positive parent block; `BlockV` contains coordinates that the physical P7 field need not have as independent variables.

The reference datum *is* identified. By the landed `composeField_of_collar`, for $x\in C_G$ and `Precedes G G'` with $G'=\mathbb B_k(U_k)$,
$$\Psi^0(x)=\bar\phi_k^0(x)=
\begin{cases}\phi_k^0(x),&x\in\Omega_1(G'),\\
\widetilde\psi_k^0(b_k(x)),&x\notin\Omega_1(G').
\end{cases}\tag{1.5}$$
The second branch uses the single-scale lift and the fact that a collar point of $G$ outside $\Omega_1(G')$ lies in the collar of $G'$. The landed `theorem73_real` and `theorem73_complex` identify the background of this composed datum on $I$; they do not identify the original datum with it on $C_G$. The full perturbation field relevant to the Euler–Lagrange equation is therefore
$$\Delta\Psi=D^{\rm ph}.\Psi-D^0.\Psi\quad\text{on }I\cup C_G,\tag{1.6}$$
where $D^{\rm ph}$ must first be connected to the original P7 action. The landed `DeltaPsiDef.deltaPsi` is set to zero outside $I$, so it is only the interior part of (1.6).

There is a useful warning in the currently landed interior theorem. `DeltaPsiCoreFinal.deltaPsi_le_pieces` assumes `hcoreTop` (every retained core site is in its top $k_1$ layer), `hbl` (every retained boundary-piece site is in its top $k$ layer), and conditions placing each retained central site in a layer at least $k_1$. Thus, under those premises and $k_1\ge2$, every site of $I$ is in $\Omega_2(G)$, so $\Omega_1(G)=\Omega_2(G)$. If $C_G$ contained $x$ adjacent to $y\in I$, the separation axiom at $j=1$ would require $d_{\rm torus}(x,y)>\varrho L>1$, a contradiction. Hence **those theorem premises force $C_G=\varnothing$ whenever $k_1\ge2$ and $\varrho L\ge1$**. This is a proved implication of the stated hypotheses, not a proof that the actual P7 window has empty collar: the missing verification of these extra premises for the actual ripe window is precisely where the geometric issue must be settled. If the actual $I$ has a nonempty collar, a layer-one shell is present and one of these top-layer premises cannot hold. If the actual $I$ has no collar, CB-1 and CB-2 become vacuous for that geometry, but the source-level proof of $C_G=\varnothing$ is still required.

## 2. What the small-field functions give (CB-2)

P7 (2.47)–(2.48) states $\Delta\Psi=0$ on terminal window blocks and
$$|\Delta\Psi(x)|\le C_{23}\widehat W_k\delta_j\quad
(x\in I\cap\Lambda_j,\quad k_1\le j<k),\qquad C_{23}=3dL+2\tag{2.1}$$
in the strengthened reconstruction. The argument on P7 p. 509 explicitly begins with a *window block* $x$ and reads its spin $\psi_j(y)$. It never treats a site of $C_G$. The landed `deltaPsi_le_pieces` has the same interior conclusion with a clamped profile, but takes the additional top-layer premises just discussed. It has no collar conclusion.

The functions on the support of $X_{\rm win}=Z\setminus Z_{k_1}$ have narrower scopes: $\widetilde\chi_k$ tests $\psi_k$ on $Z_0^c\cap(\Omega_k^c)^{\sim3}$; $\chi_S$ tests selected scale-$k$ cubes in $Z$; $\chi^0$ tests $k_1$ cubes near $U$ with the patched field $\psi'_{k_1}$; $\chi''$ tests the fluctuation on specified window blocks outside $U^{\sim3}$. The retained old/new (1.24) conditions compare adjacent **blocks where those functions are imposed**. None of their definitions says that every $x\in C_G$ is in such a tested block, or that its physical parent value is within $C\widehat W_k\delta_{k_1}$ of (1.5). This is a missing inclusion and comparison, not a change of constants.

One can quantify the most direct interface argument. If $x\in C_G$ is adjacent to $y\in I$, then, for $k\ge2$, $\varrho>1$, and $L\ge2$, the landed `layerIndex_eq_one_of_adj_not_mem` makes $y$ a layer-one site. If both data have the corresponding P2 (R1) interface bounds, with radii $r_{\rm ph}$ and $r_0$, then
$$|\Delta\Psi(x)|\le r_{\rm ph}+r_0+|\Delta\Psi(y)|.\tag{2.2}$$
This is the triangle inequality along the two interface pairs. For $k_1>1$, (2.1) does not apply at $y$; the printed (2.48) starts at $j=k_1$. Even if an independent layer-one estimate were supplied, the right side of (2.2) contains the interface radii. The P7 functions listed above do not compare these radii with $\widehat W_k\delta_{k_1}$. Thus (2.2) gives no scale-independent constant $C_\partial$ in
$$\sup_{x\in C_G}|\Delta\Psi(x)|\le C_\partial\widehat W_k\delta_{k_1}.\tag{CB-2}$$

There is a weak explicit bound. If both real data lie in P2's real domain with (R2) threshold at most one, then $||D.\Psi(x)||^2-1|<1$ gives $||D.\Psi(x)||<\sqrt2<2$ at each data site. Hence $|\Delta\Psi(x)|<4$ on $C_G$. This uses only the domain clauses, and is the best uniform statement available here without a common reference or a spatial comparison. In the complex domain, if the two perturbations have norms bounded by $\varepsilon_{\rm ph}+\delta_{\rm ph}$ and $\varepsilon_0+\delta_0$, respectively, the corresponding bound is
$$|\Delta\Psi^{\mathbb C}(x)|<4+\varepsilon_{\rm ph}+\delta_{\rm ph}+\varepsilon_0+\delta_0.\tag{2.3}$$
These bounds are much larger than the small $\delta_w$ required by the landed weighted perturbation theorem, so they do not justify its application. They also presuppose that the original physical datum has been put into the P2 data domain; that is part of CB-1's bridge.

The construction in `COLLAR-2.md` varies one collar spin while keeping the stated interior block inequalities fixed. It refutes the implication “(2.48) alone implies (2.49).” It does **not** exhibit a full P7 history satisfying every characteristic function and the exact original $Q^*$ lift. A P7-admissible failure would additionally require a geometrically realized independent collar coordinate and verification of all retained functions. This remains **OPEN (CB-3)**. Conversely, a proof of CB-2 must give the original collar formula, a cover of every relevant collar site by the tested regions, and a bound of those values against (1.5), with the complex-domain version.

## 3. Where (2.49′) is actually consumed

The support matters because the response is a global solution on $I$, even when the action is localized to $X_{\rm win}$. The following uses are in `notes/phase1/LF-RECONSTRUCTION.md` Part III.

| Consumer | Use of response | Required set |
| --- | --- | --- |
| III.6.2, Lemma III.6.3 (P7 (2.53)–(2.58)) | The algebraic cancellation uses $\delta\phi$ in $\delta A_k^*(X_{\rm win};\delta\psi,\delta\phi)$, the mass term, and a surface term. Algebra alone does not use the numerical (2.49′) bound. | Fields defined on all $X_{\rm win}$ and ${\rm st}(X_{\rm win})$. |
| III.6.3, Lemma III.6.4(b) (P7 (2.60)) | Bounds $\frac12\beta_k\langle\delta\phi,\alpha_k^0\delta\phi\rangle$ by layer sums. | **All** $\Lambda_j\cap X_{\rm win}$, $k_1\le j\le k$. |
| III.6.3, Lemma III.6.4(c) | Bounds the $\nu_k\langle\delta\phi,\phi_k^0-h\rangle_{X_{\rm win}}$ sum and $S_{\rm st}$; the ${\rm st}(Z)$ contribution needs exponential decay. | **All** $X_{\rm win}$; both named surfaces. |
| III.5.3 | $\varkappa_1,\varkappa_2,\varkappa_3,\varkappa_5$ use action positivity and local tests. $\varkappa_4$ invokes the lower bound of III.6.4 after (2.58). | $\varkappa_4$ inherits the whole-window requirement. |
| III.7.1 | Lemma 2.5 uses P3 Proposition 5.1 and a separate far-data comparison for local boxes, namely P7 (2.63)–(2.70). It does not insert the global (2.49′) bound into that comparison. | Local cubes and their own collars; an independent data-domain verification is needed there. |
| III.8.9 | The LF-4R estimate uses the small factors and III.6.4. | Inherits their whole-window requirement. |
| III.9.6 | The real $\delta\phi$ factor in (3.15′)–(3.17′) is multiplied by a complex variation and summed over $\Lambda_j\cap X_{\rm win}$. | **All** $\Lambda_j\cap X_{\rm win}$. |

In particular, it is insufficient to establish (2.49′) only on a subset far from $C_G$ unless one first proves that every set in the third column is far from $C_G$, or directly estimates the near part. The exponential in printed P7 (2.49) is a distance to $(\Omega_k^c)^\sim$, not a distance to the Dirichlet collar $C_G$. P7 p. 511 uses it to pay the ${\rm st}(Z)$ term. Replacing that exponential by collar distance needs a new geometric comparison between these two distances at ${\rm st}(Z)$. No such comparison is part of `WindowPieces.Hyp`.

## 4. A conditional response bound with the collar contribution displayed

This proposition is a mathematical consequence of the **proved** landed `weightedProp51S_exists` (and the source estimate `pertSource_local`), under the explicitly stated data and geometric hypotheses. It is the bound that should replace an unqualified appeal to (2.49′) while CB-1/CB-2 remain open.

Assume $d\ge3$ and $L\ge3$, as in `weightedProp51S_exists`. Let $I=\Omega_1(G)$, $C=C_G$, $\gamma=\operatorname{gammaW}(d)$ and $d_G$ the landed path metric. Let $A\subset I$ be the sites whose interior difference is proved to obey the layer profile, for example the retained layer-$j$ sites with $j\ge k_1$. Put $T=I\setminus A$ and
$$S=T\cup\{z\in I:\exists c\in C,\ z\sim c\}.\tag{4.1}$$
Let $\tau(n)=C_{23}\widehat W_k\delta_{\max(k_1,\min(n,k))}$, positive and decreasing. Assume
$$|\Delta\Psi(z)|\le\tau(n(z))\ (z\in A),\qquad
|\Delta\Psi(z)|\le B\ (z\in T\cup C),\qquad B\ge0.\tag{4.2}$$
Define $E_\gamma(x,S)=\sup_{s\in S}e^{-\gamma d_G(x,s)}$, with value zero if $S$ is empty or unreachable, and
$$P(x)=\sup_{z\in A}\tau(n(z))e^{-\gamma d_G(x,z)}+B E_\gamma(x,S).\tag{4.3}$$
Suppose the two actual data sets have the same $h$, are in the real or complex P2 background domain as appropriate, and their backgrounds and multipliers satisfy the `Prop51Hyp` and `Dec2.OpSetting` premises of `WeightedProp51S`, including $\delta_0,\delta_1\le\delta_w$, the vanishing base defect, the perturbed equation, and the required small multiplier. Here the uniform difference parameter $\delta_1$ may be taken at least $\max(\tau(1),B)$ and must still obey $\delta_1\le\delta_w$. These are **additional hypotheses**, not consequences of (2.1) or of the bound $B<4$.

Then each of the five componentwise quantities in `SupBoundsW`—$|\delta\phi|$, forward and backward $\ell|\partial\delta\phi|$, $\ell^2|\Delta\delta\phi|$, and $\ell^2|\delta\alpha|$—obeys
$$\mathcal R(x)\le K_w c_F(d,L)P(x).\tag{4.4}$$
If, in addition, $\tau$ satisfies `LayerProfile k τ A_0 R`, $1\le\varrho$, $1\le A_0,R$, and
$$R\le e^{\gamma(\varrho-1)},\tag{4.5}$$
then at $x\in A$ of layer $j$ the landed `ratio_decay_le` gives
$$\boxed{\mathcal R(x)\le K_w c_F(d,L)
\left[A_0R\,C_{23}\widehat W_k\delta_j+B e^{-\gamma d_G(x,S)}\right].}\tag{2.49-collar}$$
For the running scales in III.4, the profile comparison can take $A_0=e^\epsilon$ and $R=L^{(d-2)/2}$ when (4.5) is verified; then the first coefficient is $K_wc_F e^\epsilon L^{(d-2)/2}C_{23}$. Conversion to P7's derivative units may use the weaker common factor $L^{(d+2)/2}$. This is not an identification of that coefficient with P7's printed $C_{24}=2K_3C_{23}$.

*Proof.* At each interior $x$, the perturbation source reads $\Delta\Psi(x)$ and its adjacent collar values only; this is exactly `DeltaPhiResp.pertSource_local`. If $x\in A\setminus S$, its local data are bounded by $\tau(n(x))\le P(x)$. If $x\in A\cap S$, its own value is bounded by $\tau(n(x))$ and the adjacent collar values by $B$, while $P(x)\ge\tau(n(x))+B$. If $x\in T$, then $x\in S$ and both its own and adjacent collar values are bounded by $B\le P(x)$. Thus, for every component of the source, $\ell(x)^2|F_s(x)|\le c_F P(x)$.

For $\eta>0$ set $P_\eta=P+\eta$ and $M_\eta=\max_xP_\eta(x)$. Each summand $a_z e^{-\gamma d_G(x,z)}$ in (4.3) obeys the two-sided multiplicative path-distance comparison by the triangle inequality; so does the supremum, the sum, and $P_\eta$. Consequently $w_\eta(x)=M_\eta/P_\eta(x)$ satisfies `IsWeight G γ w_η`: it is at least one and $w_\eta(x)e^{-\gamma d_G(x,y)}\le w_\eta(y)$. The weighted source constant is at most $c_FM_\eta$. Apply `WeightedProp51S` with this weight, divide by $w_\eta(x)$, and let $\eta\downarrow0$ to obtain (4.4). The same argument works across disconnected components, using $e^{-\gamma\infty}=0$ and the positive $\eta$ floor. Finally, for $x\in A$, each good-source term satisfies
$$\tau(n(z))e^{-\gamma d_G(x,z)}\le A_0R\,\tau(n(x))$$
by `DeltaPhiWeight.ratio_decay_le`; the supremum has the same bound. The second term of (4.3) is $B e^{-\gamma d_G(x,S)}$, which proves the boxed formula. $\square$

`lemma41_uncond` is a special case for a perturbation supported in one set with one amplitude; it does **not** itself split the actual window perturbation into a good interior part and a collar part. `layered_response` assumes a bound by the same profile on the collar. Formula (2.49-collar) uses the more general proved weighted proposition directly, avoiding an intermediate datum whose background-domain membership has not been checked. The direct proof still requires the actual full difference (1.6), its data-domain and `Prop51Hyp` premises, and a small $B$.

To recover the estimates of §3 from (2.49-collar), one must establish, on each consumer set $E_j=\Lambda_j\cap X_{\rm win}$ and on the two surfaces, a lower distance $D_j\le d_G(x,S)$ and a numerical budget for
$$K_wc_FB e^{-\gamma D_j}.\tag{4.6}$$
For III.6.4(b), the revised quadratic sum includes $\sum_j\beta_j\sum_{x\in E_j}|\alpha_k^0(x)|[A_0R\tau_j+B e^{-\gamma D_j}]^2$ with the same scale conversion and volume factors as the original proof. The mass and III.9.6 cross terms acquire the corresponding *linear* collar errors. For ${\rm st}(Z)$ the required comparison must also give the exponential power of $\beta_k^{-1}$ used in III.6.4(c). These checks are **OPEN (CB-4)**. A large $D_j$ alone is not enough if the prefactor $B$ violates the smallness premise $B\le\delta_w$.

## 5. Exact repair obligations

1. **CB-1, physical datum.** Prove from the original P7 kernel and its $Q^*$ convention a field identity on *every* $x\in C_G$, with a collar cover, parent-piece assignment, overlap agreement, and the formula used for sites released from a positive parent layer. `windowGenSet_Ω` proves only (1.3).
2. **CB-2, collar size, or empty collar.** Either prove $C_G=\varnothing$ for the actual ripe window, or prove (CB-2) for the actual full data difference in both real and complex domains, with an explicit $C_\partial$, using precisely the retained characteristic functions. The landed `DataChangeBound` and `deltaPhi_le_of_dataChange` take the collar estimate as a premise.
3. **CB-3, counterexample option.** A counterexample must realize an independent collar coordinate in a true P7 ripe window and check the original lift plus every retained small-field function. The abstract example of `COLLAR-2.md` is not that construction.
4. **CB-4, decay alternative.** If using (2.49-collar), prove small $B$, `Prop51Hyp` for the full difference, the geometry $d_G(E_j,S)\ge D_j$, and all revised III.6.4, III.9.6, and LF-4R inequalities. This is the exact additional work needed to turn the conditional bound into a replacement theorem.

## Source and declaration register

P7: T. Balaban, *The large field renormalization operation for classical N-vector models*, pp. 499–501 (2.13)–(2.16), pp. 508–509 (2.40), (2.46)–(2.49), pp. 510–512 (2.53)–(2.60), source PDF `sources/s002200050486.pdf` and text layer `P7.txt`. P2: T. Balaban, *The variational problems for classical N-vector models*, pp. 632–633 (4.6), (4.9) and p. 636 (4.19)–(4.21), source PDF `sources/BF02099510.pdf`; the formulas were checked against the PDF image in the prior collar audit because the OCR is unreliable. Local reconstruction: `notes/phase1/LF-RECONSTRUCTION.md` §§III.4.4, III.5.1–III.5.3, III.6.1–III.6.3, III.7.1, III.8.9, III.9.6. Prior audit: `COLLAR-2.md`.

The named Lean declarations checked here are `WindowPieces.windowGenSet_Ω` in `Balaban/LargeField/R/WindowGenGlue.lean`; `psiTilde`, `psiZeroWin`, `deltaPsi` in `Balaban/LargeField/R/DeltaPsiDef.lean`; `composeField_of_collar` in `Balaban/Background/Composition.lean`; `deltaPsi_le_pieces` in `Balaban/LargeField/R/DeltaPsiCoreFinal.lean`; `DataChangeBound`, `deltaPhi_le_of_dataChange` in `Balaban/LargeField/R/DeltaPhi.lean`; `pertSource_local`, `layered_response` in `Balaban/LargeField/R/DeltaPhiResp.lean`; `ratio_decay_le` in `Balaban/LargeField/R/DeltaPhiWeight.lean`; `weightedProp51S_exists` in `Balaban/Fluctuation/WeightedProp51.lean`; and `lemma41_uncond` in `Balaban/Fluctuation/FarDecayUncond.lean`. The bound (2.49-collar) is a prose deduction from the landed weighted result, **not a named Lean theorem**. All files under `/home/scott/Balaban` were read only.
