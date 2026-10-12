# The repaired source tube under one RG step

This note answers [followup4.txt](followup4.txt). It uses the mass and tube conventions of [RGFREE-4.md](RGFREE-4.md), especially (1.1)–(1.4) and (2.2)–(2.4). **FREE-ACT-TUBE and SWITCH-JOINT are not proved by the currently landed results.** There is also a precise geometric obstruction to preservation of the *whole* proposed tube with a margin uniform as the physical mass tends to zero. The estimates below prove transfer on the three RG reference slices and identify the remaining physical assertions. None of the read-only sources or Lean files was changed.

Write $M>0$ for the physical mass at the parent level, $m=\lambda M$ at the child level, $\lambda=L^{-2}$, and $r_p=\varepsilon_{j+1}$, $r_c=\varepsilon_j$, so $r_p<r_c$. The same physical field $h$ gives $B=Mh$ and $b=mh=\lambda B$. Let $F$ and $G$ be the parent and child complex background sphere fields at corresponding sites. All dot products are complex bilinear; $\|\cdot\|$ is Hermitian. Constants below are independent of $M$.

## 1. Exact source transport

**Lemma 1 (proved).** Suppose $F\cdot F=G\cdot G=1$, $\|F\|,\|G\|\le K$, and set
$$
v=B\cdot F,\quad t=B-vF,\quad \Delta=G-F,\quad \delta=\|\Delta\|,
\quad v'=b\cdot G,\quad t'=b-v'G.
$$
Then
$$
v'-m=\lambda\{v-M+B\cdot\Delta\},\qquad
t'=\lambda\{t+v(F-G)-(B\cdot\Delta)G\}.                 \tag{1.1}
$$
In particular, if $|v-M|<Q=r_vr_p^2$ and $\|t\|<T=r_t\sqrt M\,r_p$, then
$$
\begin{split}
|v'-m|&\le\lambda\left[Q+\{T+K(M+Q)\}\delta\right],\\
\|t'\|&\le\lambda\left[T+\{KT+(1+K^2)(M+Q)\}\delta\right].
\end{split}                                                       \tag{1.2}
$$
Consequently the child source tube is reached with a strict margin whenever the two right sides of (1.2) are strictly below $r_vr_c^2$ and $r_t\sqrt{\lambda M}\,r_c$, respectively. These inequalities are the exact quantitative obligation for a one-step source-tube argument; the separate XiC and composed-field domain obligations must also hold.

*Proof.* Since $b=\lambda B$, $v'=\lambda(v+B\cdot\Delta)$. Subtract $\lambda M$ for the first identity. Also $t'=\lambda[B-(v+B\cdot\Delta)G]$, which gives the second. Cauchy–Schwarz for the bilinear dot product gives $|B\cdot\Delta|\le\|B\|\delta$. The decomposition $B=t+vF$ implies $\|B\|\le T+K(M+Q)$ and $|v|\le M+Q$. Insert these bounds in (1.1). The child tube is exactly $|v'-m|<r_vr_c^2$, $\|t'\|<r_t\sqrt m\,r_c$. $\square$

The transverse inequality in (1.2) contains the term $\lambda(1+K^2)Qr_c$ when $\delta$ is of order $r_c$. It is independent of $\sqrt M$, whereas the child transverse width is proportional to $\sqrt M$. Neither `Lemma25.lemma25` nor the source XiC bounds couple a permitted spin fluctuation to the independent complex longitudinal displacement $v-M$.

**Proposition 2 (proved local obstruction).** Fix $r_p,r_c,r_v,r_t>0$, $r_p<r_c$, $0<\lambda<1$, and $0<\delta<1/2$. Let $N\ge2$ and put
$$
F=e_1,\quad G=\sqrt{1-\delta^2}\,e_1+\delta e_2,\quad
B=(M+q r_p^2)e_1,\quad b=\lambda B,
\qquad 0<q<r_v/4.                                       \tag{1.3}
$$
The parent source lies strictly in its tube for every $M>0$. For all sufficiently small $M>0$, the child longitudinal condition also holds, but its transverse condition fails. In fact,
$$
\|t'\|=\lambda(M+qr_p^2)\delta,
\qquad r_t\sqrt m\,r_c=r_t\sqrt{\lambda M}\,r_c.           \tag{1.4}
$$
Here $\|G-F\|\le2\delta$. Thus no implication from parent-tube membership and a mass-independent bound $\|G-F\|\le2\delta$ to child-tube membership can hold uniformly for $M\downarrow0$.

*Proof.* At the parent, $v=M+qr_p^2$ and $t=0$. At the child, $v'=\lambda(M+qr_p^2)\sqrt{1-\delta^2}$. Hence
$$
|v'-m|\le\lambda(qr_p^2+M\delta^2)<r_vr_c^2
$$
for sufficiently small $M$, since $\lambda<1$, $r_p<r_c$, $q<r_v/4$. The vector $e_1-(e_1\cdot G)G$ has Hermitian norm $\delta$, proving (1.4). The left side tends to $\lambda q r_p^2\delta>0$ while the permitted width tends to zero. $\square$

The example concerns the source geometry of a normalized sphere background. It is **not** claimed to instantiate every constraint of a specific Balaban generating-set transition. It disproves a domain-preservation proof based only on the available source-tube and background-closeness estimates. An actual transition theorem would have to prove an additional correlation of the form
$$
 (|v-M|+M)\|G-F\|\ \lesssim\ \sqrt M\,r_c
\quad\text{on every transported datum},                   \tag{1.5}
$$
or restrict its domain to the preimage of each inherited old-level tube. Call the former **OPEN SOURCE-CORRELATION**. The mass-free solver does not use $B$, so a general bound on $\Delta$ alone cannot produce the factor $\sqrt M$ in (1.5). A preimage restriction remains possible but must be shown to contain the actual RG reference data and to possess margins uniform over old scales. Call that **OPEN TAGGED-PREIMAGE**. This is the precise status of `TUBE-FLOW` in RGFREE-4; full one-step preservation is **not proved**.

The local coordinates in (1.3) also fit the ordinary anisotropic XiC probes of I6-ANISO (1.3) when $q$ and $\delta/r_c$ are chosen below its fixed longitudinal and spin constants: the longitudinal shifts are $qr_p^2$ and $O(qr_p^2+M\delta^2)$, and the spin shift is at most $2\delta$. This observation concerns domain widths. It does not assert that these two coordinates are the image of one actual RG composition.

## 2. What is preserved on the RG reference slices

The three reference slices are narrower than the whole source tube. Their source algebra survives one scale as follows.

**Lemma 3 (proved, given the stated background values).** On the aligned constant $U$ and $V$ slices of RGFREE-4 (1.4), suppose both level backgrounds equal $e_1$. Then $F=G=e_1$. The $U$ slice has $B=Me_1$ and $v'=m,t'=0$; on the $V$ slice $B=Ve_1$, so $v'-m=\lambda(V-M)$ and $t'=0$. In particular $|V-M|<r_Vr_p^2$ implies child source-tube membership if $\lambda r_Vr_p^2<r_vr_c^2$. The same statements hold for every complex $\xi$ for which the aligned background branch exists. The switch difference $D=\phi^0-\phi^m$ is zero there, and both old composed arguments coincide; hence the first two switch reference jets, including their $\xi$ derivatives, vanish identically as in RGFREE-4 (2.2).

*Proof.* Insert $F=G=e_1$ into (1.1). For the switch, both critical points are the aligned sphere vector; their composition maps agree because they use the same vector and the same data. Each term in RGFREE.md (2.2) therefore vanishes as a function of $U,V,\xi$ on the stated open slice. Differentiation preserves zero. $\square$

**Lemma 4 (proved source algebra; physical domain conditional on OPEN PROFILE-DOM).** On the transverse *spin* slice let $F=e_1$, $B=Me_1$, and let $G\cdot G=1$, $\|G-e_1\|\le\delta\le C_pr_c$, $\|G\|\le K$. Then
$$
|v'-m|=\lambda M|e_1\cdot(G-e_1)|
 \le\tfrac12\lambda M\delta^2,
\qquad \|t'\|\le\lambda M(1+K^2)\delta.               \tag{2.1}
$$
For fixed $C_p,K,r_v,r_t$, both child tube inequalities hold when $M$ is chosen sufficiently small: for example it suffices that $\lambda M C_p^2<2r_v$ and $\sqrt{\lambda M}(1+K^2)C_p<r_t$. Here $K\ge1$ follows from $G\cdot G=1$. The formula extends uniformly over a fixed complex $\xi$ ball if its masses have comparable positive moduli and the inequalities are given a strict margin.

*Proof.* The sphere identity $2e_1\cdot(G-e_1)+(G-e_1)^2=0$ gives the first bound. For the second, apply (1.1) with $t=0$, $v=M$ and $|B\cdot\Delta|\le M\delta$. The displayed smallness inequalities compare (2.1) with $r_vr_c^2$ and $r_t\sqrt{\lambda M}r_c$. $\square$

Lemma 4 establishes only the source part of the transverse slice. The actual mixed-cover background must obey $\delta\le C_pr_c$ on a common complex $\xi$ neighbourhood, and all XiC and old composed arguments must retain strict margins. Neither the normalization model nor the algebra proves those geometric facts. This is **OPEN PROFILE-DOM / TAGGED-PREIMAGE**. These slice results suffice for Cauchy estimates of the three RG jets *if* a physical local expansion is available there; they do not imply a class-wide transported tube.

## 3. Audit of the allowed landed input

| Input | Exact contribution | Hypothesis it does not supply |
|---|---|---|
| `Fluctuation/ExpansionNuFree.lean`: `actionC_mass_split`, `expansion_nuFree` | Exact physical mass variation at a zero-mass background, including `massVar`. | A bounded complex physical activity or a polymer expansion. |
| `Fluctuation/RenormIdentity.lean`: `lemma35_i_nuFree_bg`, `lemma35_i_complete_bg`, `lemma35_ii_perturbed`, `lemma35_iii` | Action and composition identities under the displayed background-domain and Euler–Lagrange hypotheses. | Bounds on the resulting old-term difference or its support. |
| `Fluctuation/Lemma25.lean`: `lemma25` and `Lemma25Xi.lean`: `xiBounds_of_perturb` | Real fluctuation-cutoff inclusion under `chiU`, the stated `h` test, and quantitative radius hypotheses. | A complex fluctuation integral on the source tube or a mass-uniform bound for each label. |
| `Fluctuation/ExpansionBounds.lean`: `expansion_bounds`; `ExpansionLocal.lean`: `interaction_block_bound`; covariance and critical-point modules | Background, covariance and interaction bounds when their complex interpolation-domain and smallness hypotheses are met. | Construction of those hypotheses for the joint $(\psi,\xi)$ switch tube, a cutoff-compatible complex measure, or physical polymer labels. |
| `Fluctuation/FarDecay.lean`: `lemma41`, `lemma41_domain` | Far response for a local *background-data* change **conditional on OPEN `WeightedProp51`** and its `Prop51Hyp` and domain premises. | A decoupled weighted response with the fluctuation variable and joint source-tube margins. The file explicitly excludes decoupled mode U/P. |
| `Polymer/MarkedCubes*.lean`: `marked_cubes`, `marked_cubes_two`, `Pst_Gst_differentiableOn` | Localized integral and holomorphy estimates from an already supplied `LabelAct`, mark dependence, bounds and holomorphy. | Construction of the physical labels and marks from the mass vertex and the old-term compositions. |
| `SmallField/RenormTermwiseIrrel.lean`: `termwise_irrelevant`, `termwise_irrelevant_scaled` | A bound for `Itw` under `PremisesTerm` and `DataHyp` on an isotropic `Tube` of radius $\rho$. | A `PremisesTerm` for a term known only on the narrower source tube, or the physical source-domain witness. |
| `notes/phase1/I6-ANISO.md` | A mathematical specification of anisotropic XiC Cauchy domains and the termwise I-6 replacement, with the needed source `DataHypAniso`. | A landed `termwise_irrelevant_aniso` theorem or an extension of its XiC discs to a source-tube-bounded inherited term. |

The distinction in the last row is substantive. I6-ANISO (1.3) permits a transverse $b$ disc of radius $c_\perp\varepsilon_j$, and (1.4) permits a transverse invariant-coordinate disc of comparable order. The repaired term bound in RGFREE-4 is asserted only for $\|t\|<r_t\sqrt{m_j}\varepsilon_j$. For arbitrarily small $m_j$ the former discs are not subsets of the latter. Thus even after the stated anisotropic I-6 specification is formalized for an XiC-bounded term, it cannot be invoked unchanged for a term bounded only on the repaired tube. The missing replacement is **OPEN I6-SOURCE-TUBE**: a termwise irrelevant estimate on the actual transported source domain using separate reference-slice Cauchy bounds, or a proved stronger extension/bound for the physical terms. The already landed isotropic theorem has the same mismatch; its $\rho\asymp\varepsilon_j$ premise cannot be inferred from the source tube.

## 4. FREE-ACT and SWITCH-JOINT: exact remaining assertions

The bare mass vertex is exactly $V_M(w)=-t\cdot w+(v/2)w^2$ by `actionC_mass_split` and the sphere equation (RGFREE-4 (1.3)). On the source tube its pointwise bound (RGFREE-4 (1.5a)) is proved. `expansion_nuFree` places this vertex in the fluctuation action. These facts do **not** imply the weighted local bound (RGFREE-4 (1.9)). To prove **FREE-ACT-TUBE**, one still needs all of the following in one compatible construction:

1. **OPEN FREE-LABEL:** for the physical zero-background-mass fluctuation integrand, construct the decoupled `LabelAct` and determinant/measure factors, holomorphic in $(\psi,b,\xi)$ on the appropriate source-tube preimages; bound their activities uniformly in $M\downarrow0$ after the exact field-only factor is assigned to the main action. This includes the nonlinear sphere chart and the real cutoff replacement supplied by `lemma25`.
2. **OPEN FREE-FLUCT-DECAY:** prove a weighted response with the fluctuation variable and a fixed decoupling vector on its polydisc, then obtain the mixed-cover support, star-crossing allocation and the $x_1^2$ moment. The current `lemma41` has the open premise `WeightedProp51` and addresses background-data changes only. `marked_cubes` becomes applicable after FREE-LABEL and the marked dependence bounds are established; it does not establish them.
3. **OPEN FREE-SLICE-DOMAIN:** establish the XiC, tube-preimage and background-response margins for all three slices uniformly on $\|\xi\|_\infty\le c_{10}$; Lemmas 3–4 give only their source algebra. Prove torus-independent stabilization and conjugation for the resulting local coefficients.

Their conjunction, with the quantitative norm and moment in RGFREE-4 (1.9), is precisely FREE-ACT-TUBE. Once it is proved, the three Cauchy estimates in RGFREE-4 (1.10) give the proposed $B_{\rm free}\widehat\beta^{-1}\varepsilon^{-2}$ forcing. This implication is **proved conditional on the named OPEN assertions**; no cited landed theorem supplies their conjunction.

For the switch, `lemma35_*` and the chord identity give the exact correction (RGFREE.md (2.2)); RGFREE-4 Proposition 2 bounds its unlocalized chord on the switch tube by $C\beta_u m\varepsilon^2$ per block. The first two reference jets vanish by Lemma 3 above. For the remaining transverse jet, **SWITCH-JOINT** requires:

1. **OPEN SW-CHORD-LOC:** localize $\langle D,(H^m+\alpha^m)D\rangle$ jointly in $\Theta=(1+\zeta)\psi$, $\xi$ and the decoupling variables, with a new-scale exponential norm and $x_1^2$ moment. `lemma41` would only assist after `WeightedProp51` and its physical data hypotheses are proved; a separate decoupled version is still needed.
2. **OPEN SW-OLD-TRANSPORT:** for every inherited term born at level $j$, prove that $J_j^0$, $J_j^m$ and their interpolation enter one common old tagged domain with a fixed Cauchy margin on the three slices, and quantify their local dependence on $D$. The source transfer obstruction in Proposition 2 prevents obtaining this from a uniform full-tube preservation claim.
3. **OPEN SW-OLD-LOC:** sum the old-term first variations over scales with mixed-cover support, star-crossing allocation, the asserted $E_0\sqrt m$ norm, new-scale $x_1^2$ moment, and joint holomorphy in $\xi$. `RenormTermwise*` estimates an already supplied term and does not build this difference expansion; `marked_cubes_two` likewise assumes its two physical marks.

With these three assertions and FREE-SLICE-DOMAIN, Cauchy's formula proves RGFREE-4 (2.6)–(2.7), including the literal scale factor $\widehat\beta^{-1}\varepsilon^{-2}$ required by `Flow/RGInfty.lean` `rg_step_infty`'s `hηbd`. This is **conditional on OPEN**, even if `WeightedProp51` becomes proved. The already verified `matrixInfty` triangular bounds are algebraic and cannot replace the missing forcing bound.

## 5. Conclusion and confidence

**Proved here:** exact mass/source transport (1.1)–(1.2); the local counterexample (1.3)–(1.4) to mass-uniform whole-tube transfer from the available hypotheses; source-tube preservation on the two aligned slices and, with an explicitly stated background displacement, on the transverse spin slice; exact identification of the incompatible transverse radii in I6-ANISO and the repaired term domain. The algebra and the cited Lean declaration signatures were checked directly. Confidence: high.

**Proved conditional on a PROVED cited result:** the physical mass identity uses `actionC_mass_split` and `expansion_nuFree`; the action re-expression uses `lemma35_i_nuFree_bg` under its displayed hypotheses; the real cutoff inclusion uses `lemma25` under its displayed hypotheses. These results do not assert FREE-ACT-TUBE or SWITCH-JOINT.

**Conditional on OPEN:** `WeightedProp51`; FREE-LABEL, FREE-FLUCT-DECAY, FREE-SLICE-DOMAIN, I6-SOURCE-TUBE; SW-CHORD-LOC, SW-OLD-TRANSPORT, SW-OLD-LOC; TAGGED-PREIMAGE (or an actually valid replacement for whole-tube transfer). Therefore FREE-ACT-TUBE, SWITCH-JOINT and class-wide one-step domain preservation are **not closed**. In particular this note does not claim a complete proof of the requested RG step from the currently landed inputs.
