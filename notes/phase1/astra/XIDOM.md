# OPEN-I6-XIDOM: the anisotropic datum and the tube comparison

## Verdict and scope

The source-level assertion is **true under the strict step-chart margin, the same-mass class-chart inclusion, and P1's second-difference estimate (3.107)**: for $k-j\ge n_1$, the composed, fluctuation-shifted datum has `DataHypAniso` with $\sigma=C_0s_{jk}$ and $\varepsilon=\varepsilon_k$. The complex datum must be treated as a real source witness plus a small complex displacement. Applying the landed `ScaledPsiC.c2b` field verbatim would lose one power of $s_{jk}$; its **proof** contains the stronger square estimate needed here. The tube comparison also works label by label: use a real rotation to align the *real* centre, compare the class term with `trickFnA` on small polymers by `CRotE`, and pay for any discrepancy on large polymers with $e^{-d_j(X)}$. This does not remove or weaken `CRotE`.

This is a mathematical proof and a precise Lean target, **not a claim that the target is already compiled**. The step-to-birth-domain inclusion used by `ClassOldCover.hchart`, the level-$j$ second-difference estimate of P1 (3.107), and the torus defect for $X=\square(y)$ remain distinct implementation obligations. The result below gives the needed bound for $X\ne\square(y)$ without the `polyAniso ∨ ∉ TubeAniso` premise of `irrelTorus_bound_of_dataHyp_of_poly`. A bound for *every* label additionally requires the torus version of the renormalization conditions at the special cube; it is not a consequence of `DataHypAniso` or `CRotE`.

All journal page numbers below are printed page numbers. P1 is Balaban, *Commun. Math. Phys.* **167** (1995), 103–154, `/home/scott/Balaban/sources/BF02099355.pdf`; P4 is Balaban, *Commun. Math. Phys.* **182** (1996), 675–721, `/home/scott/Balaban/sources/Balaban.pdf`. I checked P1 pp. 122–124 and 145–153 (including the p. 123 page image), and P4 p. 704. The source text explicitly warns on P1 p. 147 that its newly constructed analytic extension need not equal the initially assumed one. The comparison below therefore uses the **landed class term** and checks equality to its tube extension at the actual data; it never identifies two extensions merely because they agree on real fields.

## Exact quantitative statement

Fix $d\ge3$, $L\ge3$, $N\ge2$, the class constants $P$, $0<\gamma<1/2$, $0<\alpha_1<1-2\gamma$, and a label $(j,y,X)$ with $1\le j\le k-n_1$, $y\in X$. Write

$$
s=L^{-(k-j)},\qquad \alpha=(d-2)/2-\gamma>0,\qquad
\varepsilon_i=P.\mathrm{eps}(d,L,i),\qquad \nu_j=\texttt{nuIdeal}\ L\ k\ \nu_k\ j.
$$

Put $K_1=\texttt{bgK1}(d,L,N)$, $B=\texttt{rotB}(N)=64000N^2$, $D=NB$, $\delta_j=\varepsilon_j/(2K_1+2)$, and

$$
Q=(2K_1+2)4N(1+D),\qquad r_j=\texttt{anisoRadius}(d,L,N,P,j)=\varepsilon_j/Q
=\delta_j/[4N(1+D)].                                      \tag{1}
$$

The input chart is the step's `XiCRaw` at level $k+1$, with the fluctuation $u\,cc\,C^{1/2}\widehat\psi$, $|cc|=\beta_k^{-1/2}$, $\|u\|<a'$, and $\widehat\psi$ in its stated box. The **strict chart test** is that its shifted level-$k$ datum lies in `XiCData` with output radius

$$
e_{\rm out}=b^2\varepsilon'+\texttt{xiK2}(d,L,N)(\delta_3+\delta_{\rm fl})
\le\varepsilon_k.                                                 \tag{2}
$$

This is the test called `hE` in `ClassOldCover`/`SharpChartTest`; $\|u\|<a'$ alone does not assert (2). Let $H=\texttt{xiC1}(d)=(4d+8)(2d+1)$ and $c_s=\texttt{scaledC0}(d)=8d+12$. The level-$j$ composition of that datum supplies a real field $p$, a complex displacement $z$, a real constant field $h_0$, and a complex displacement $h'$ with physical data $\psi=p+z$, $b=\nu_j(h_0+h')$. One may take

$$
\tau=c_s s,\qquad \zeta=H e_{\rm out}\le H\varepsilon_k,\qquad
C_0=16c_sH,\qquad \sigma=C_0s.                              \tag{3}
$$

The chart statement also includes the domain test for the **same class mass as the term**: the composed pair and its constant-at-$y$ pair belong to `XiDom (Tm.gs j X) a μ j ε_j`. For a running-mass class this follows from P1 Lemma 3.2 and the gap below; for birth-frozen domains it is exactly the level-$j$ `ClassOldCover.hchart` mass-transport obligation recorded in WIDEGEN W206. It must not be inferred from membership at a different mass. Assume the source's second-difference estimate at this composed field,

$$
\|\partial^2\psi\|\le K_\alpha s^{2-\alpha_1}\varepsilon_k,
\quad K_2:=K_\alpha s^{2-\alpha_1}\varepsilon_k,
\quad K_{\rm sig}:=K_\alpha/C_0^{2-\alpha_1}.                   \tag{4}
$$

Here $K_\alpha$ is the constant of P1 (3.107), p. 147, for the chosen $\alpha_1$; it may be enlarged to account for the fixed chart constants. The exact conclusion is `DataHypAniso Dom νj (C₀*s) (P.eps d L k) K₂ ψ_y b`, where $\psi_y(t)=\Psi(y+\texttt{ibase}\ j\ t)$, $b=\nu_jh$, and `Dom` is **the same existential `XiDom` pullback set printed in the signature of** `irrelTorus_bound_of_dataHyp_of_poly` (`IrrelTorusBound.lean`, pp. 265 onward), with this $y,X,S$ and class mass $\mu$.

Choose $n_1$ so that for all $n\ge n_1$,

$$
C_0L^{-n}\le1/4,\qquad HQ L^{-\alpha n}\le(100D^2)^{-1},
\qquad c_s^2L^{-2n}H\varepsilon_k\le1/8.                 \tag{5}
$$

The last inequality follows uniformly from the fixed small upper bound on $\varepsilon_1$ (and can be replaced by that explicit class smallness condition). Also require $\varepsilon_j\le(2K_1+2)\min(\texttt{bgC0}(d,L,N),\texttt{bgC1}(d,L,N))$, so `anisoRadius_spec` gives `AnisoRadiusOK` for (1). Since `epsSeq` has a decreasing tail, $\varepsilon_k/\varepsilon_j\le s^\alpha$, hence (5) gives

$$
0<\zeta\le r_j/(100D^2),\quad 0<\tau\le1/4,\quad
0<\sigma\le1/4,\quad \varepsilon_k/r_j\le Qs^\alpha\le1.
                                                                    \tag{6}
$$

The class mass bound $0<\nu_k\le1$ gives $0<\nu_j=\nu_ks^2\le s^2\le\tau^2\le\sigma^2$. If the class uses a different explicit upper mass, replace $1$ in this sentence by that fixed upper bound and enlarge $C_0$ once; no parameter may depend on $j,k$ or the torus size.

## The anisotropic inequalities

The following conservative bounds combine P1 (3.13)–(3.14), p. 123, with the landed `ScaledPsiC` output for the source witness with $(\tau,\zeta)$. They hold at every relevant site, with $a=|p(y)|$ and $e=p(y)/a$:

$$
\begin{array}{lll}
|\partial p|<\tau\zeta,& |p^2-1|<\tau^2\zeta,&
\nu_j|1-e\cdot h_0|<\tau^2\zeta^2,\\
\nu_j|h_0^2-1|<\tau^2\zeta^2,& |z|<\zeta+\tau\zeta\le2\zeta,&
|\partial z|<\tau\zeta,\\
|(p+z)^2-p^2|<\tau^2\zeta,&
\nu_j|h'|<\tau^2\zeta,&
\nu_j|e\cdot h'|<\tau^2\zeta^2 .
\end{array}                                                       \tag{7}
$$

P1 (3.14) has the sharper size bound $|z|<\zeta+\tau^2\zeta$; the weaker $\zeta+\tau\zeta$ in (7) is exactly `ScaledPsiC.c2a` and suffices here. The strict spin-square displacement in (7) is also printed in (3.14); the landed `ScaledPsiC.c2b` field currently says only $<\tau\zeta$. To recover (7) from its proof on a whole-level set, use `CompHyp.dot_sub_one` and `b2_le` in `Background/CompositionEstimates.lean` and `Background/ScaledComposition.lean`. At an interior site the complex composition has square deficit at most $s^2\zeta(d+7)$ (the proof's $M=3$); the real one has deficit at most $s^2\zeta(d+3)$ ($M=1$). Their difference is at most $s^2\zeta(2d+10)<(c_ss)^2\zeta=\tau^2\zeta$. At a collar site of a whole-level set both background spins are unit and the difference is zero. Thus this sharpening uses inequalities already proved inside the composition argument; it is a new **Lean declaration**, not a new hypothesis on the class. The output of `xiC_scaledComposition` (`SmallField/XiCompose.lean`) supplies the other lines of (7) with $\zeta=H e_{\rm out}$.

For a whole-level generating set (`IsLevel G j`), neighbouring sites of the pulled-back $j$-block lattice form an `IsInterfacePair`; hence `ScaledPsiC.r1` and `.c1` give the differences in (7) and (9). The field is periodic on the torus, so these estimates hold at every site of the pulled-back $\mathbb Z^d$ field. The first, second, and fourth fields of `DataHyp` follow directly:

$$
|\psi^2-1|\le |p^2-1|+|\psi^2-p^2|<2\tau^2\zeta
\le2c_s^2H s^2\varepsilon_k\le\sigma^2\varepsilon_k,       \tag{8}
$$

$$
|\partial\psi|\le|\partial p|+|\partial z|<2\tau\zeta
\le2c_sH s\varepsilon_k\le\sigma\varepsilon_k,              \tag{9}
$$

and $|\psi(y)|\le a+2\zeta\le1+\tau^2\zeta+2\zeta<2$ under (5). Equation (4) is precisely `DataHyp.sec`, with $K_2\ge0$ and $K_2=K_{\rm sig}\sigma^{2-\alpha_1}\varepsilon_k$.

For `b_close`, put $t=e\cdot h_0$ and write $h_0=te+h_{0,\perp}$ (this is a **real** orthogonal decomposition). From (7), $\nu_j\le\tau^2$, and $\zeta\le1$,

$$
\begin{aligned}
\nu_j^2|h_{0,\perp}|^2
&\le\nu_j^2|h_0^2-1|+(\nu_j|1-t|)(\nu_j|1+t|)\\
&\le\nu_j\tau^2\zeta^2+\tau^2\zeta^2(2\nu_j+\tau^2\zeta^2)
\le4\tau^4\zeta^2,
\end{aligned}                                                     \tag{10}
$$

so $\nu_j|h_{0,\perp}|\le2\tau^2\zeta$. Also $|a-1|=|p(y)^2-1|/(a+1)\le\tau^2\zeta$, whence $\nu_j|t-a|\le\tau^2\zeta^2+\tau^4\zeta\le2\tau^2\zeta$. Consequently

$$
|b-\nu_j\psi(y)|\le\nu_j|h_0-p(y)|+\nu_j|h'|+\nu_j|z(y)|
\le(4+1+2)\tau^2\zeta
\le7c_s^2Hs^2\varepsilon_k\le\sigma^2\varepsilon_k.          \tag{11}
$$

The longitudinal field requires the normalization; estimating $\nu_jh_0$ and $\nu_j\psi$ separately loses a power of $\varepsilon_k$. After a real rotation sending $e$ to $e_{i_0}$, write $z=z_\parallel e+z_\perp$, $q=a+z_\parallel$, $w=\sqrt{\psi(y)^2}=\sqrt{q^2+z_\perp^2}$ on the branch near $1$. By (5), $|q-1|\le1/4$, $|w-1|\le1/4$, $|w|\ge3/4$, and $|w+q|\ge3/2$. Therefore

$$
\left|q/w-1\right|=\frac{|z_\perp^2|}{|w||w+q|}
\le2|z_\perp|^2\le8\zeta^2,
\qquad |z_\perp/w|\le4\zeta .                              \tag{12}
$$

Moreover $\nu_j|h_{0,\parallel}+h'_\parallel|\le\nu_j+\tau^2\zeta^2+\tau^2\zeta\le3\tau^2$ and $\nu_j|h_{0,\perp}+h'_\perp|\le3\tau^2\zeta$. Expanding `vInv ψ b = ψ(y)·b / w` now gives

$$
\begin{aligned}
|\texttt{vInv}\ \psi\ b-\nu_j|
&\le\nu_j|h_{0,\parallel}-1|+\nu_j|h'_\parallel|
+|q/w-1|\,\nu_j|h_{0,\parallel}+h'_\parallel|\\
&\quad+|z_\perp/w|\,\nu_j|h_{0,\perp}+h'_\perp|\\
&\le(1+1+24+12)\tau^2\zeta^2
\le38c_s^2H^2s^2\varepsilon_k^2
\le\sigma^2\varepsilon_k^2 .
\end{aligned}                                                     \tag{13}
$$

The generous $C_0=16c_sH$ covers (8)–(13). For `DataHyp.mem`, apply the actual step-to-class chart inclusion at the term's mass. For `DataHyp.mem_const`, use P1 Lemma 3.2, p. 124: derivatives of the constant field vanish, all pointwise inequalities in (7) hold at $y$, and (6) gives the required gap into $\Xi_j^c(1,\varepsilon_j)$. Equivalently, after the same real rotation use the rectangular sufficient inclusion of I6-ANISO §1.1: $|\psi^Q(y)-e_{i_0}|\le3\zeta$, $|b^Q_{i_0}-\nu_j|\le2\tau^2\zeta^2$, $|b^Q_\perp|\le3\tau^2\zeta$; (5) puts these below $\delta_j/(8N)$, $\delta_j^2/8$, $\delta_j/(8N)$ respectively. `XiD2.psiTildeC_subset_xiC` at the equal pair $(\delta_j,\delta_j)$ and `XiSymm.xiC_rot_iff` finish the domain membership. The level-$j$ background mass inequality $\mu L^{2j}\le\nu_j$ is used here. This proves every field of `DataHypAniso` for the pulled-back datum.

## Comparison with the landed tube extension

Let $S$ be the placement of $X$ at $y$, $c=\texttt{pack}\ S\ \psi_y\ b$, $F$ the centred class term used in `premisesTermAniso_centred`, and $M_X=E_0e^{-\kappa d_j(X)}$. The current `irrelTorus_eq_Itw_centred` assumes $c\in\texttt{polyAniso}$ or $c\notin\texttt{TubeAniso}` because it proves $F(c)=\texttt{trickFnA}(c)$ only there. Here is the missing comparison for $c\in\texttt{TubeAniso}\setminus\texttt{polyAniso}`.

Choose a real orthogonal $Q_y$ carrying the real unit vector $p(y)/|p(y)|$ to $e_{i_0}$. `XiSymm.xiC_rot_iff` keeps the actual datum in its class domain and the landed `irrelTorus_rot` carries the final bound back. In this frame, let $R$ be **any** tube witness, so $Rc\in\texttt{polyAniso}$ and $|R_{ab}|\le B$. Both $R$ and $R^{-1}=R^T$ have operator norm at most $D=NB$ in the coordinate maximum norm. Write $t_X=1+d_j(X)$ and $A=\texttt{diamA}(d,L,P.m_0,m_1)$. In the small-polymer case

$$A t_X\sigma\varepsilon_k\le r_j/(100D^2),                  \tag{14}$$

(9), the polymer path bound, and (6) give for every placed site of $X$

$$
|Q_y\psi_y(x)-e_{i_0}|_\infty
\le3\zeta+A t_X\sigma\varepsilon_k
\le4r_j/(100D^2)=r_j/(25D^2).                       \tag{15}
$$

On $X$, retain the actual $Q_y\psi$; outside $X$, extend it by $R^{-1}e_{i_0}$. Because $y\in X$ implies $0\in S$, the tube witness gives $|R Q_y\psi(y)-e_{i_0}|_\infty<r_j$; (15) also holds at $y$. Hence

$$
|R^{-1}e_{i_0}-e_{i_0}|_\infty
\le D\bigl(r_j+D|Q_y\psi(y)-e_{i_0}|_\infty\bigr)
\le(D+1/25)r_j<(1+D)r_j=\delta_j/(4N).               \tag{16}
$$

The spin on $X$ also lies within $\delta_j/(4N)$ of $e_{i_0}$. The rotated source has $|b^Q_{i_0}-\nu_j|\le2\tau^2\zeta^2<\delta_j^2$, and all its field coordinates differ from $\nu_je_{i_0}$ by at most $4\tau^2\zeta$, so $2N(4\tau^2\zeta)<\delta_j$ by (6). `xiDom_of_fieldA` thus places the **patched original full field** in the class domain. Apply $R$: on $X$ its configuration is $Rc\in\texttt{polyAniso}$ and outside $X$ its spin is $e_{i_0}$, so `fp_mem_xiDomA` places the **entire rotated full field** in the class domain. If $\det R=-1$, precede $R$ by a real transverse reflection fixing $e_{i_0}$; the polydisc is preserved, and the real class rotation clause handles the reflection. The resulting complex rotation has determinant $1$. The reflection preserves the transverse polydisc and the class term by its real rotation clause, so it has the same tube-extension value. `CRotE` therefore equates the two class-term values. `SFTermClauses.localE` replaces the patched original by the actual field. The value at $Rc$ is exactly the value selected by `trickFnA` (and its independence of the witness is `TubeHypA.witness`). Thus

$$F(c)=\texttt{trickFnA}\ i_0\ \nu_j\ r_j\ F\ c
\quad\text{whenever (14) holds}.                               \tag{17}
$$

No claim that $R$ is near a real matrix occurs in (15)–(17). The complex boost in CROTE.md §2 is allowed; only its fixed entry bound $B$ and the smallness of the **data on this label** are used.

In the complementary case, $t_X>r_j/(100AD^2\sigma\varepsilon_k)$. Both $|F(c)|\le M_X$ (class H4 at `DataHyp.mem`) and $|\texttt{trickFnA}(c)|\le M_X$ (its polydisc bound if a tube witness exists; otherwise it equals $F(c)$). Since $e^t\ge t^3/6$ for $t>0$,

$$
\begin{aligned}
|F(c)-\texttt{trickFnA}(c)|
&\le2M_X=2E_0e^{-(\kappa-1)d_j(X)}e^{-d_j(X)}\\
&\le12e(100AD^2)^3E_0e^{-(\kappa-1)d_j(X)}
\sigma^3(\varepsilon_k/r_j)^3\\
&\le12e(100AD^2)^3E_0e^{-(\kappa-1)d_j(X)}
\sigma^{3-\alpha_1}(\varepsilon_k/r_j)^2.
\end{aligned}                                                     \tag{18}
$$

The last step uses $\sigma\le1$ and $\varepsilon_k/r_j\le1$. The reference jets of $F$ and `trickFnA` agree because the two functions agree on the open polydisc around `refPt`; hence the subtraction terms `Ttw`, `Ax`, and `Phitw` are identical. For $X\ne\square(y)$, the definitions and `irrelTorus_eq_Itw_centred` therefore extend to the exact identity

$$\mathcal E_{\rm irrel}^{(j)}(y,X;\Psi,h)
=\texttt{Itw}(\text{one-polymer }\texttt{trickFnA};\psi_y,b)
+F(c)-\texttt{trickFnA}(c).                            \tag{19}$$

Combine (18) with the landed `termwise_irrelevant_aniso_scaled`, the `DataHypAniso` just proved, and $\varepsilon_k/r_j\le Qs^\alpha$. If $C_{\rm landed}$ is its constant for $\Lambda=1$, $K_{\rm sig}$ from (4), $C_0$ from (3), and $K_R=Q$, one may take

$$
C_I=C_{\rm landed}+12e(100AD^2)^3C_0^{3-\alpha_1}Q^2.
                                                                    \tag{20}
$$

Indeed $\sigma^{3-\alpha_1}(\varepsilon_k/r_j)^2\le C_0^{3-\alpha_1}Q^2s^{3-\alpha_1+2\alpha}=C_0^{3-\alpha_1}Q^2s^{d+\alpha_3}$, $\alpha_3=1-2\gamma-\alpha_1>0$. Thus for **every** $X\ne\square(y)$, with no polydisc/tube disjunction,

$$
|\texttt{irrelTorus}\ P.m_0\ Tm\ i_0\ i_1\ j\ y\ X\ \Psi\ (\texttt{constFld}\ h)|
\le C_IE_0s_{jk}^{d+\alpha_3}e^{-(\kappa-1)d_j(X)}.      \tag{21}
$$

The constants depend on $d,L,N,\kappa,\alpha$ and the fixed class/geometric constants ($m_0,m_1,K_1,K_\alpha$). They do not depend on $j,k,\beta_k$, the torus side, or the label. Fix them first, then take $n_1$ as in (5) and $\beta$ large enough for (2) and the fixed smallness of $\zeta$.

## Lean shape and remaining gates

The first new source lemma should strengthen `ScaledPsiC.c2b` for the whole-level composition, with the same hypotheses as `xiC_scaledComposition`:

```lean
-- Proposed, not compiled.
theorem scaledPsiC_comp_square_sharp (H : HypS G G' a₁ ν η η η θ j Ψ₀ h₀ Ψ'' h'' φr φc)
    (hLevel : IsLevel G j) (x : Torus d (N₀ * L ^ k)) :
    ‖dot (ccv G G' a₁ φc Ψ₀ Ψ'' x) (ccv G G' a₁ φc Ψ₀ Ψ'' x) -
      dot (crv G G' a₁ φr Ψ₀ x) (crv G G' a₁ φr Ψ₀ x)‖
      ≤ θ ^ 2 * η * (2 * d + 10)
```

The whole-level qualification avoids a false claim at an arbitrary collar where the source's top datum need not be unit. The proof is the two calls to `CompHyp.dot_sub_one` and `b2_le` described above. Next prove `dataHypAniso_of_scaledPsiC`, whose conclusion is exactly `DataHypAniso Dom νj (C₀*s) (P.eps d L k) K₂ ψ_y b`; its hypotheses are the strengthened `ScaledPsiC` witness, (2), (4), (5), $\mu L^{2j}\le\nu_j$, and the *same-mass* class-chart inclusion for `mem`. `mem_const` is proved from the displayed product estimates, not added as a second premise. A separate `dataHypAniso_rot_real` transports the result through $Q_y$.

For the label theorem, take the full signature of `irrelTorus_bound_of_dataHyp_of_poly` in `IrrelTorusBound.lean` and **remove its `hpack` premise**. Retain `SFTermClauses`, `CRotE`, `BgHyp`, `AnisoRadiusOK`, the exact placement and block-constancy premises, `DataHypAniso` and its numerical premises. Add the source frame witness $(p,z,h_0,h')$ satisfying (7) at the pulled-back label, the scale gap (5), and the chart membership at the actual class mass. Its conclusion is exactly (21). The proof is (14)–(19), followed by `termwise_irrelevant_aniso_scaled`. This is a noncircular new theorem: the added witness contains only source-field inequalities and domain membership, not the term value or the desired bound. `irrelTorus_rot` transports the real alignment; `CRotE` is invoked only after proving both full-domain memberships.

The special label $X=\square(y)$ in `irrelTorus` has the extra resummed local terms of P1 (3.126)–(3.127), pp. 152–153. Equation (19) does not apply to it. Write $T\Phi_Z$ for the local expression in the definition of `irrelTorus` and set $\Delta_j(y;\Psi,h)=\sum^{\mathrm f}_{Z\in\mathrm{polysAt}(j,y)}T\Phi_Z(\Psi,h)$. Directly expanding that definition gives (19) **plus** $\Delta_j$ at the special cube. Thus the exact additional premise for an all-label version of (21) is $|\Delta_j(y;\Psi,h)|\le C_D E_0s^{d+\alpha_3}e^{-(\kappa-1)d_j(\square(y))}$, uniform in $y$ and the chart datum. The same argument then gives (21) at every label with $C_I$ replaced by $C_I+C_D$. This defect bound must be derived from the finite-torus renormalization conditions of P1 (H.6), p. 118, together with the local Taylor estimates; it is not itself asserted verbatim by (H.6), and no such bound is part of the currently landed `DataHypAniso` theorem. P4 (H.5), pp. 677–678, is stated in infinite volume; P4 p. 704 explicitly says the whole resummed action is needed for the irrelevant representation. Neither `DataHypAniso` nor the tube argument proves that defect lemma. Winding polymers and the birth-mass `hchart` are further gates, as WIDEGEN W966 and W206 record. No full W960/W962 closure is claimed here.

## Confidence

High for (8)–(13), the sharpened composition square inequality, and the tail estimate (18). Medium for the small-polymer Lean bridge (15)–(17): it uses only the landed class hypotheses, but its patching and determinant correction have not been compiled. Medium for the actual step-chart instantiation: (2), the birth-mass `hchart`, and (4) must be supplied by the step proof; this note identifies their precise use and does not assert they are already landed. The cube-label defect is independent and remains open.
