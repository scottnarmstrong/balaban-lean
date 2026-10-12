# Mass response, regional chord, and switch wall

## Result

The mass change can be treated by the landed weighted Proposition 5.1 with **zero data change**. Let the massless solution be the base field, put the complete mass term on the right of its Euler–Lagrange equation, and take the source $f_1=-\mu_q(\phi^m-h)$, where $\mu_q=mL^{-2q}$. The two fields have the same original spin datum on the whole Dirichlet collar. For real unit $h$, $|\phi^m-h|\le2$; on a pinned complex chart with $|\phi^m|\le3/2$ and $|h|\le1+r_h$, use $B_h=5/2+r_h$. Under the explicit smallness and operator hypotheses below, WeightedProp51S with weight one gives all four scaled response bounds with $K_m=\sqrt N K_w$, uniformly in $m$. The source is distributed throughout the variational set, so weight one is the justified layer profile. No decay from the window boundary follows from this mass source alone.

For the new region $X=Z_k^c\cap Z'$ at $q=k+1$, the response and the actual small-field gradient give a regional chord cost $C_D\beta_qm^2|X|_q$ and a crossing-wall cost $C_W\beta_qm\delta_k|X|_q$. The constants are stated in §2. This discharges the numerical response, Hessian and wall inputs of the landed massChange_wall_bound_of_bounds once the two real backgrounds and their full-collar domains are supplied. It does not construct the full changed step kernel: regional inherited $E,F$ terms, cutoffs, reference measure and denominator remain separate operator comparisons.

## 1. The same-datum mass source

Fix a level-$q$ generating set $G$ with Dirichlet sites $I=\Omega_1(G)$ and collar $C_G$. Let $D=(\Psi,h)$ be the **same** datum for both minimizations, including every site of $C_G$. Write $H_\nu(\alpha)=-\Delta^D+Q^*aQ+\nu+\alpha$, $\mu_q=mL^{-2q}$, and let $(\phi^0,\alpha^0)$ and $(\phi^m,\alpha^m)$ solve respectively

$$H_0(\alpha^0)\phi^0=Q^*a\Psi+\mathfrak b(\Psi),\qquad
H_{\mu_q}(\alpha^m)\phi^m=Q^*a\Psi+\mathfrak b(\Psi)+\mu_q h,\qquad
\phi^s\cdot\phi^s=1.\tag{1.1}$$

Here $\mathfrak b$ is the Dirichlet boundary source of Background/Data.lean:source. Extend $\phi^0$ by the **common** $\Psi$ on the collar. Set $u=\phi^m-\phi^0$, $a_*=\alpha^m-\alpha^0$ (the symbol $a_*$ is local to this paragraph), and extend $u$ by zero off $I$. Subtraction of (1.1) gives the exact identity

$$H_0(\alpha^0)u+a_*u=-\mu_q(\phi^m-h)-a_*\phi^0,\qquad
(\phi^0+u)\cdot(\phi^0+u)=1.\tag{1.2}$$

Thus (1.2) is Background/Contraction.lean:IsPerturbed with base $\bar\phi^0$, $\nu=0$, $\delta\Psi=0$, $f_1=-\mu_q(\phi^m-h)$, $\delta\phi=u$, and $\delta\alpha=a_*$. The zero-collar extension is essential in the first equation: a collar change would add BoundaryTerm$(\delta\Psi)$ and invalidate this source formula. Background/Prop51Mass.lean:dirichletOperator_mass_shift is another algebraic check of the diagonal mass term. Background/Def5Response.lean:theorem72_linearResponse differentiates a fixed-mass *data* family; it is not itself the finite-mass comparison (1.2).

Here are sufficient, scale-uniform hypotheses and constants. Take $d,L\ge3$, $N\ge2$, $1/2\le a_j\le2$, and a generating-set separation satisfying both GreenSetting$(G,a,0)$ and Dec2.OpSetting$(G,a,0)$; the latter requires $2d\log L\le\operatorname{agmonRate}(d)(\varrho-1)/16$ (Localization/Decoupled2.lean:OpSetting). Let $K_1=\operatorname{bgK1}(d,L,N)$, $c_6=c6(d,L,N)$, $\delta_*=\operatorname{deltaStar}(d,L,N)$, and choose $K_w,\delta_w>0$ from Fluctuation/WeightedProp51.lean:weightedProp51S_exists. Suppose both solutions are on the indicated P2 existence branches, their full datum is in the background domains, and for a common real data radius $\eta_q=C_{\rm dat}\delta_k$ one has

$$\operatorname{BgBounds}(G,D,\phi^s,\alpha^s,K_1\eta_q)\quad(s=0,m),\qquad
\delta_0:=K_1\eta_q\le\min(\delta_*,\delta_w,c_6/2,1),\qquad
\delta_1:=mB_h\le\min(\delta_*,\delta_w).\tag{1.3}$$

For the real switch region, LFR Remark II.2.8 gives a $3dL\delta_k$ regularity target; take $C_{\rm dat}=3dL$ **after** the inherited physical datum, including its collar, has a P2 domain witness giving the two BgBounds in (1.3) at that radius. The massless bound implies IsSmoothField$(G,\delta_0,\bar\phi^0)$ and $|\alpha^0|_2\le\delta_0$; the real hard-spin constraint gives $|\phi^0|=1<3/2$ and zero defect $g=\phi^0\cdot\phi^0-1$, including its zero Laplacian. Hence Prop51Hyp holds with $\delta\Psi=0$ and $(\delta_0,\delta_1)$ if $f_1$ satisfies its source bound. For the complete field, $|\phi^m|=|h|=1$ gives $B_h=2$. Since $\ell(x)=G.\operatorname{spacing}(x)\le L^q$,

$$\ell(x)^2|f_1(x)|\le mB_h\bigl(\ell(x)/L^q\bigr)^2\le\delta_1.\tag{1.4}$$

The same bound with complex moduli holds on a pinned chart with $|\phi^0|,|\phi^m|\le3/2$, $|h|\le1+r_h$ and $B_h=5/2+r_h$, provided both complex solutions satisfy their bilinear hard-spin constraints and (1.3) uniformly. The two multiplier bounds in (1.3) give $|\alpha^m-\alpha^0|_2\le2\delta_0\le c_6$, so the *actual* pair $(u,a_*)$ is in the uniqueness class required by WeightedProp51S. There is no need to identify it with a newly constructed solution by an unproved global uniqueness claim.

Take the admissible weight $w\equiv1$ (Localization/DecoupledWeighted.lean:IsWeight.one); (1.4) is its weighted-source hypothesis with $C=mB_h$. WeightedProp51S now yields, at every $x\in I$ and for every component, its SupBoundsW and SmallW conclusions. Converting component suprema to the Euclidean vector norm gives the promised explicit response

$$\boxed{\ |u(x)|_2,\quad \ell(x)|\partial u(x)|_2,\quad
\ell(x)^2|\Delta^D u(x)|_2,\quad
\ell(x)^2|\alpha^m(x)-\alpha^0(x)|
\ \le K_mB_hm,\qquad K_m:=\sqrt N\,K_w.\ }\tag{1.5}$$

The factor $\sqrt N$ is harmless for the scalar multiplier and makes one constant valid for all four entries. This is a constant layer profile $\tau_j=mB_h$: it is a LayerProfile with $A_0=R=1$. The source has the smaller pointwise factor $(\ell/L^q)^2$, but a response with that same declining factor at every lower layer needs an additional admissible-weight calculation; it does not follow from (1.5). Likewise lemma41_uncond in Fluctuation/FarDecayUncond.lean treats a supported *data* change and gives no distance decay for this distributed mass source.

At the switch $q=k_0+1$, LFR Theorem IV.2.2 and D-IV.11 give $\beta_qm\le C_{\rm sw}:=e^{2\epsilon}L^d$. Choose the final $\beta$ so that $\beta_q\ge C_{\rm sw}B_h/\min(\delta_*,\delta_w)$, and choose the data radius so that (1.3) holds. These choices make (1.5) uniform for all $m\in(0,1]$ satisfying the switch bound. They are compatible with the LFR order: $K_w,\delta_w,K_1,c_6$ and geometry first, the fixed budget constants next, $\lambda_*,\beta$ last. For a complex chart, (1.3) and its existence-branch assumption must hold uniformly throughout the bounded chart; this statement does not grant a mass-uniform wide transverse-$h$ disc.

## 2. A localized Hessian and the scaled wall

Let $D_X$ be the landed Region of the main action whose sites are $I\cap X$, with $X=Z_k^c\cap Z'$ a union of scale-$k$ cubes, $q=k+1$, and $n=|X|_q$ the number of scale-$q$ cubes meeting it. In fact $X\subset I$, so $D_X.sites=X$: if $x\in X\cap\Omega_q$, its layer is $q$; if $x\in X\cap\Omega_q^c$, then $x\in Z_k^c\cap Z'\subset W_k\cap U_{Z'}$, hence lies in the top layer of the local $\mathbb B_k(W_k\cap U_{Z'})$ used in Definition II.2.4. Consequently every $x\in X$ has $\ell(x)\ge L^k$. The equality of sites and the spacing bound must be instantiated for the actual region constructor; without the equality, an $I\cap X$ boundary could have additional fine-scale wall bonds that (2.4) does not count.

Put $W=K_mB_hm$. The response (1.5) bounds $|u|\le W$ and every outgoing difference from $x\in D_X$ by $W/L^k$, including a bond to the common collar, where $u=0$. In the chord of LargeField/R/MassChangeChord.lean, the block average of $u$ has norm at most $W$, the coefficient $a_{n(x)}L^{-2n(x)}$ is at most $2L^{-2k}$, the half-bond weight is at most one, the multiplier is at most $\delta_0L^{-2k}$, and $\mu_q\le L^{-2k}$ since $m\le1$. Assign each bond touching $D_X$ to an endpoint in $D_X$; there are at most $2d$ such bonds per site. With at most $M^dL^{qd}n$ fine sites in the counted scale-$q$ cubes and $\delta_0\le1$, the bilinear chord obeys

$$\bigl|2\,\operatorname{massChangeChord}_{D_X}\bigr|
\le(2d+4)M^dL^{q(d-2)+2}W^2n.\tag{2.1}$$

This proves the hHess input of LargeField/R/MassChangeWall.lean:massChange_wall_bound_of_bounds with $C_H=(2d+4)M^dL^{q(d-2)+2}$ and $n=|X|_q$. Multiplication by $\beta_0^{(q)}=\beta_qL^{-q(d-2)}$ gives the chord contribution

$$\beta_0^{(q)}|\operatorname{massChangeChord}_{D_X}|
\le C_D\beta_qm^2n,\qquad
C_D=(d+2)M^dL^2K_m^2B_h^2.\tag{2.2}$$

The scale factor in $C_H$ cannot be omitted when the unscaled fine-lattice chord theorem is used. Equation (2.1) is an absolute bound, so it also covers the bounded pinned complex chart under its corresponding derivative and multiplier hypotheses. It does not assert a polymer diameter decay.

For the wall, the complete background's BgBounds.grad with data radius $C_{\rm dat}\delta_k$ gives

$$|\partial_b\bar\phi^m|_2\le G_\nabla\delta_k/L^k,\qquad
G_\nabla:=K_1C_{\rm dat}=3dLK_1,\tag{2.3}$$

for each crossing bond assigned to its endpoint in $D_X$. This is a bound on the **complete** field at the actual wall; a bound for P7's massless reference alone would not suffice. In each scale-$q$ cube there are at most $L^d$ scale-$k$ cubes, each with at most $2d(ML^k)^{d-1}$ outgoing fine bonds. The bondwise theorem starPair_norm_le in MassChangeWall.lean and (1.5) therefore give

$$\beta_0^{(q)}|S_{D_X}(u,\bar\phi^m)|
\le C_W\beta_qm\delta_k n,\qquad
C_W:=2dM^{d-1}L^2K_mB_hG_\nabla.\tag{2.4}$$

The exponent cancellation is $L^dL^{k(d-1)}L^{-k}L^{-q(d-2)}=L^2$. If an implementation counts both assignments of a crossing bond, replace $C_W$ by $2C_W$. The wall is in the one-site support of the **new** regional action: each crossing bond has its assigned endpoint in $X$, and its exterior endpoint is precisely in $X^{+1}$ of Definition II.5.4. Equation (2.4) is therefore charged per new cube in (S2) of Definition II.5.7, then propagated by Lemma II.5.12, the (B) premise of LF-2. The old (D6) invariant is not an independent reserve for a wall placed elsewhere.

Combining the landed regional identity massChange_region_chord_with_star, (2.1), (2.3), and (1.5) gives exactly the hresp, hHess and hgrad instances of massChange_wall_bound_of_bounds, and hence

$$\beta_0^{(q)}
\left|A_{m,D_X}(D,\phi^0)-A_{m,D_X}(D,\phi^m)\right|
\le\bigl(C_D\beta_qm^2+C_W\beta_qm\delta_k\bigr)|X|_q.\tag{2.5}$$

At $q=k_0+1$ use $\beta_qm\le e^{2\epsilon}L^d$, not the smaller bound valid through $k_0$. Thus the chord is at most $C_DC_{\rm sw}^2/\beta_q$ per cube and the wall at most $C_WC_{\rm sw}\delta_k$ per cube.

## 3. One-step scheme-A interface

The mass comparison (2.5) is one edge of the full interface. For the inherited energy and observable terms, INTERFACE-A.md (2.3)–(2.4) gives **whole-torus** comparison estimates under a common complex Cauchy margin and the field-comparison bound $|\psi_k^{(j),m}-\psi_k^{(j),0}|\le C_{\rm cmp}L^{-(k-j)}m$. The energy constant there is

$$C_E=\frac{C_{\rm cmp}}r\left[
\frac{C_IL^{-n_1\alpha_3}}{1-L^{-\alpha_3}}
+K_0\sum_{n=0}^{n_1-1}L^{nd}\right],\tag{3.1}$$

up to its stated fixed comparison and coordinate-count factors. The observable coefficient is $(C_{\rm cmp}K_{0,1}/r)c_9\xi_q^{\rho_F}m/[\varepsilon_q(1-L^{-(1-2\gamma+\alpha_1)})]$ times $\|g\|_1$, plus the leading-source cost $K_mB_hm\|g\|_1$. These formulas retain the distinct $E_0$ and $c_9\xi_q^{\rho_F}$ coefficients. They do **not** prove the corresponding regional bounds: the marginal energy term cancels only after a whole-torus sum, and localizing the observable needs a decoupled response and a common Cauchy tube.

Here is the precise one-step clause to prove. Suppose regional identities assign the inherited differences to $X_{Z'}$ and provide per-new-cube constants $C_E^{\rm loc},C_F^{\rm loc}$, with all segment-domain and analytic-locality premises verified. Suppose also the cutoff, reference-measure and common-denominator comparison has a uniform new-cube cost $q_{\rm cut,meas,norm}$, and any physical-to-reference datum conversion has cost $q_{\rm data}$. Then for all old variables and $\|g\|_1<1$ the interface exponent obeys

$$|\operatorname{Re}J_{q,Z'}(g)|
\le q_{\rm A}|X_{Z'}|_q,\quad
q_{\rm A}:=C_D\beta_qm^2+C_W\beta_qm\delta_k
+C_E^{\rm loc}E_0\frac m{\varepsilon_q}
+\left(C_F^{\rm loc}c_9\xi_q^{\rho_F}\frac m{\varepsilon_q}
+K_mB_hm\right)\|g\|_1
+q_{\rm data}+q_{\rm cut,meas,norm}.\tag{3.2}$$

The first two summands are proved by §§1–2 under (1.3) and the actual region-spacing/domain incidence. The formulas (3.1) and INTERFACE-A.md (2.4) establish the inherited comparison only globally and under their Cauchy hypotheses; $C_E^{\rm loc},C_F^{\rm loc}$ in (3.2) remain named local inputs. The physical-to-reference data cost still depends on the constructor-level collar work of COLLAR-FIX.md. The cutoff, measure and denominator costs are likewise open. No whole-operator (S2) conclusion follows by setting those costs to zero.

Once (3.2) is proved uniformly and $q_{\rm A}\le q_*$ with $q_*$ fixed before row 14 of LF-RECONSTRUCTION §I.1.3, enlarge the $c_2$ coefficient of Definition II.5.11 by $q_*$. The scalar one-step (S2) exponent then decreases by $q_*|X_{Z'}|_q$; Lemma II.5.12 propagates the old (D6) bound to (H6$^\flat$). Set the geometry and response constants first, choose $c_2$ in row 14, then choose $\lambda_*,\beta$ in row 16 so that (1.3), the bound on $q_{\rm A}$, and the later budget inequalities hold. A localized polymer decay rate, if required by (S4) or (S5), needs a separate decoupled analytic expansion; (2.5) is a volume estimate.

## 4. Lean dependency order and limits

1. In Background/Contraction.lean or a mass-response module, prove massSource_perturbed from the two IsEL equations and Background/Prop51Mass.lean:dirichletOperator_mass_shift: $\delta\Psi=0$, $f_1=-\mu_q(\phi^m-h)$, $\delta\phi=\phi^m-\phi^0$, $\delta\alpha=\alpha^m-\alpha^0$. Prove massSource_bound (1.4) and massMultiplier_small from the two BgBounds.
2. Instantiate Prop51Hyp at $\nu=0$ using BgBounds.grad/lap/alpha, the hard-spin defect identity, and GreenSetting. Instantiate Dec2.OpSetting at $\nu=0$ from the separation condition. Apply weightedProp51S_exists and IsWeight.one to obtain massChange_sameData_response (1.5); convert component bounds to the Euclidean vnorm used by MassChangeWall. Theorem72_linearResponse is optional for an infinitesimal derivative, not a substitute for this finite comparison.
3. In the actual step geometry prove newRegion_spacing_ge and crossingBond_count; on the verified complete-background domain prove massChange_complete_wall_grad (2.3) from theorem52_exists and BgBounds.grad.
4. Prove massChange_local_hessian (2.1) by expanding MassChangeChord and bounding its four finite sums, then pass (1.5), (2.1), (2.3) to MassChangeWall.lean:massChange_wall_bound_of_bounds for (2.5). This lemma should record the factor $L^{q(d-2)}$ in the fine-lattice Hessian input.
5. Prove regionalInheritedEnergy and regionalInheritedObservable from the actual complete-class terms, including the marginal boundary piece, common chart margin and decoupled locality. Then prove massChange_cutoff_reference_glue, massChange_measure_compare and massChange_denominator_common; only afterward instantiate (3.2), (S0), (S2), (S4), (S5) and the scheme-A LF-2 budget.

**Source and status.** BG Proposition 5.1 (the reconstruction of P2 Lemma 3.2 and Proposition 3.1) is represented by Background/Contraction.lean:prop51_exists_unique; its weighted version is Fluctuation/WeightedProp51.lean:WeightedProp51S and weightedProp51S_exists. The exact mass diagonal identity is Background/Prop51Mass.lean:dirichletOperator_mass_shift. The regional chord and wall algebra is landed in LargeField/R/MassChangeChord.lean and MassChangeWall.lean. LFR Definitions II.2.4, II.5.4, II.5.7, II.5.11, Lemma II.5.12, III.4.6 and IV.2.2 supply the geometry, budget and switch regime. The response proof is conditional only on the explicit full-data domain, smoothness and operator premises (1.3); the Hessian and scaled wall then follow by finite-sum estimates. The actual constructor incidence, regional inherited re-expression and full operator comparison remain to be implemented. No source file under /home/scott/Balaban was changed.
