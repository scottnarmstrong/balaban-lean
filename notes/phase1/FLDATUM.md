# The fluctuation datum in I-5

The worker's finding is correct. The datum on $\mathbb B_k(X)$ is the background composition plus the **full composition of the pair** $(\delta\phi_k,\psi')$. P3 (4.17) retains $\psi'-Q(\mathbb B_k)\delta\phi_k$; the landed `flDatum` and `D1rawFl` substitute zero for $\psi'$. The omitted term is generally nonzero. In the limiting case $\mathbb B_k(X)=\mathbb B_k$, the source formula gives $\delta\psi=\psi'$ on the data sites, whereas the landed increment is zero there. No constraint or change of fluctuation variables identifies the two formulas.

The formal `i5_fluct` theorem therefore expands the function assembled from the landed datum, but its identification with Balaban's P3 (4.41) function is false. The old effective-action contribution $\delta\mathscr E'$ and the old observable-term contribution to $\delta\mathscr F'$ in `interaction_expansion` inherit this error. The direct fluctuation potential and direct source pairing have different constructions and are not changed by the datum formula itself. The repair must pass $\psi'$ through both the raw and structured compositions, enlarge the fluctuation radius by its direct contribution, and represent $\psi'$ on its proper block-constant parameter space.

## 1. The source formula

P3 p. 71, (4.16), identifies the old-scale field on $X$ by composing the background datum on $\mathbb B_k(X)$ **plus** $\delta\psi(\mathbb B_k(X),\mathbb B_k;\psi')$. On the same page, (4.17) defines the increment (suppressing its localization parameter $s$) as
$$
\delta\psi(\mathbb B_k(X),\mathbb B_k;\psi')
=Q(\mathbb B_k(X))\delta\phi_k
 +a(\mathbb B_k(X))^{-1}Q^*(\mathbb B_k,\mathbb B_k(X))a(\mathbb B_k)
       \bigl(\psi'-Q(\mathbb B_k)\delta\phi_k\bigr).\tag{1}
$$
Here $\delta\phi_k$ is the solution of P2 (3.20) with perturbation datum $\delta\psi=\psi'$, background $(\phi_{k+1},\alpha_{k+1})$, and the other forcing terms set to zero; P3 (4.18) inserts the decoupling parameters $s$. P3 p. 72, (4.20) bounds this **whole** increment by $(2K_3+1)\delta_1$, including the direct $\psi'$ contribution. Its (4.21), (4.32), and p. 77 (4.41) then use the whole increment in the argument of the old term. The component $+1$ in (4.20) is consistent with the explicit $\psi'$ in (1).

P6 p. 23, (4.1) evaluates $\mathscr E_k'$ and $\mathscr F_k'$ along $\psi^{(k)}(\theta)+\beta_k^{-1/2}\sigma C^{(k)1/2}\psi$; pp. 24–25, after (4.7), applies P3's Proposition 4.3 to obtain (4.8). P6 does not supply a replacement for (1). `LOCALIZATION.md` §4.4 states the I-5 composite with $\delta\psi(\mathbb B_k(X),\mathbb B_k;\psi',s)$, and `FLUCTUATION.md` §3.3 uses its fluctuation variant for the $\delta\mathscr E'$ and $\delta\mathscr F'$ terms. These references point back to (1).

In the fine-lattice notation of `Background/Composition.lean:167–203`, let $G=\mathbb B_k(X)$, $H=\mathbb B_k$, and write $n(x)$ and $p(x)$ for their active layers. The exact field represented by (1) is
$$
\delta\Psi_G(x)=\operatorname{composeField}(G,H,a,\delta\phi,\psi')(x)
=Q_{n(x)}\delta\phi(x)+\kappa_{n(x),p(x)}
       \bigl(\psi'(x)-Q_{p(x)}\delta\phi(x)\bigr),\quad x\in\Omega_1(G),\tag{2}
$$
where $\kappa_{n,p}=(a_p/a_n)L^{2(n-p)}$. On the collar of $G$, (2) is the extension of $\delta\phi$ by $\psi'$ used in `composeField`; outside the data sites it is zero. The complete $G$ datum is
$$
D_G^{\rm fl}.\Psi=
\operatorname{composeField}(G,G_+,a,\phi_+,D_+.\Psi)
 +\operatorname{composeField}(G,H,a,\delta\phi,\psi'),\qquad
D_G^{\rm fl}.h=\operatorname{composeData}(G,G_+,a,\phi_+,D_+).h.\tag{3}
$$
The two terms of (3) are exactly the two terms of P3 (4.21). The further composition from $G$ to $\mathbb B_j(X)$ uses (3) as its input, as in P3 (4.16), (4.32), (4.41).

## 2. Why the landed expression differs

`Localization/I5FluctChain.lean:94–108` defines
```
flDatum = perturbData Gk (composeData hP a φ D)
  (composeField Gk Hm a δφ 0)
```
and proves that its spin datum is the sum of the background composition and `composeField Gk Hm a δφ 0`. `Localization/I5FluctFacts.lean:105–115` builds the same zero-outer-data expression in `D1rawFl`; `I5Fluct.lean:44–50` packages it as `flDatumOne`. The solver itself does receive $\psi'$ through `flEdat` (`I5FluctData.lean:49–52`), but that only determines $\delta\phi$. It does not insert the separate datum term in (1).

On an active site the difference between (2) and the landed increment is exactly $\kappa_{n,p}\psi'(x)$. On a collar site outside $\Omega_1(H)$ it is $\psi'(x)$; inside $\Omega_1(H)$ the collar extension uses $\delta\phi$ for both. In particular, if $G=H$ then $n=p$, $\kappa_{n,p}=1$, and the source (2) gives $\psi'$ on active data sites, independently of $\delta\phi$. The landed expression gives $Q_n\delta\phi+(0-Q_n\delta\phi)=0$. This is an exact algebraic witness, with no appeal to an approximate estimate.

The equation for $\delta\phi$ does not impose $Q\delta\phi=\psi'$. P2 p. 621, (3.20) has $Q^*a\delta\psi$ on the right of a *soft* block-penalty Euler–Lagrange equation, together with a sphere constraint and multiplier. The constraint fixes the spin norm, not the block average. More decisively, even if a special solution happened to satisfy $Q\delta\phi=\psi'$, the omitted $\kappa\psi'$ in (2) would remain; in the same-set test the correct increment would still be $\psi'$ and the landed one zero. Relabeling $\delta\phi$ or absorbing $\psi'$ in the background datum cannot make `flDatum` equal (3) without changing the actual function being expanded.

## 3. Correct Lean interface and proof changes

The structured definition should take the fluctuation datum as an explicit argument. A direct form, for a block-constant $\psi'$ on $H$, is
```
flDatum (hP : Precedes Gk Gp) (hPm : Precedes Gk Hm)
    (a : ℕ → ℝ) (φ : Gp.Ω 1 × Fin N → ℂ)
    (δφ : Hm.Ω 1 × Fin N → ℂ) (D : BgData Gp N)
    (ψ' : CTorus ... → Fin N → ℂ)
    (hψ' : IsLayerConstant Hm ψ') : BgData Gk N :=
  perturbData Gk (composeData hP a φ D)
    (fun x i => composeField Gk Hm a δφ ψ' x i)
    (composeField_layerConst hPm a δφ hψ')
```
`flDatum_Ψ` must state (3); `D1rawFl` must replace its `composeField ... δφ 0` by `composeField ... δφ u.2`; `flDatumOne` must pass its $\psi'$ argument to `flDatum`. At $s=1$, prove the new exact identification by linearity of `composeField` (`Fluctuation/RenormIdentity.lean:274–285`) and P3's composition identity (4.16); `exact_fluct_eq_flFieldOne` in `InteractionBridge.lean:120–145` supplies the field increment $\delta\phi$ but does not by itself supply the missing datum term.

The present `FlBall` (`I5FluctFan.lean:36–37`) is an open ball of **arbitrary fine-site fields** and does not assert `IsLayerConstant Hm ψ'`. A `BgData` cannot simply be constructed from (3) over that full ball. The faithful route is to parameterize $\psi'$ by its level-$k$ block values (a finite-dimensional complex space), extend it canonically to a layer-constant field on $H$, and use the open ball in those coordinates. An equivalent full-space interface may precompose **both** `flEdat` and (3) with a linear block projection $P_H$ that preserves physical block fields; its supremum bound and agreement on physical data must be proved. Restricting the theorem to a non-open subset of the current ambient `FlBall` without changing the analyticity carrier is insufficient for its stated `AnalyticOnNhd` conclusion.

The bound `flPsi_bound` in `I5FluctChain.lean:68–88` estimates only `composeField δφ 0`. Under the same admissible weight ratio $0\le a_p/a_n\le1$, $n\le p$, its proof plus (2) gives the elementary replacement
$$\|\delta\Psi_G(x)\|\le N\bigl(5V+\delta_1\bigr),
\quad V=cK'_2\delta_1,\quad x\in\operatorname{dataSites}(G),\tag{4}$$
provided $\|\psi'(x)\|\le\delta_1$ on the needed $H$ data sites. For active sites use $0\le\kappa_{n,p}\le1$; for collar sites use the extension rule. The larger choice $\delta_{\rm fl}\ge N(5cK'_2+1)\delta_1$ replaces `FlNum.flb` (`I5FluctFacts.lean:39–55`) and its existence proof in `I5FluctNonempty.lean`; all subsequent smallness inequalities are then chosen with this new constant. This is a bound of the same order as P3 (4.20), not a claim that the numerical constants coincide.

`point_facts_fl` and its `hrawD` proof (`I5FluctFacts.lean:170–243`) must use the corrected bound and raw identity. `I5FluctLocal.lean:273–290` must compare $\psi'$ and $\psi''$ at each composition dependency, replacing the current `rfl` for the zero outer datum; the existing `psiThick` agreement is intended to supply it. The direct $\psi'$ dependence is linear, so the analytic proof in `I5FluctFan.lean` gains an analytic coordinate map; its domain and bound proofs must be rerun with (4). `I5Fluct.lean:i5_fluct` then expands the corrected function. The background-only I-5 theorem is unaffected.

Downstream, `Fluctuation/InteractionETerm.lean:flComp` and `eterm_locInt` and `Fluctuation/InteractionMPart.lean` must evaluate their old $\mathscr E^{(j)}$ and $\mathscr M^{(j)}$ terms at the repaired `flDatumOne`. Their derivative in $\psi'$ must include the explicit derivative of $\kappa\psi'$ (and the collar contribution), as well as the response through $\delta\phi$. The Cauchy/localization argument can then be reapplied to the corrected `flComp`. `InteractionAssemble.lean` and `Interaction.lean:interaction_expansion` must be re-established with these E and M terms; their current algebraic assembly proves an expansion of the wrong old-term composite. `InteractionVBlock.lean`, `InteractionVPart.lean`, and the direct $\langle g,\delta\phi\rangle$ part of `InteractionFPart.lean` use the fluctuation solution directly and do not acquire a new datum term. The old $\mathscr M$ contribution to $\delta\mathscr F'$ does acquire it. This is a source-fidelity repair, so the changed statements require proof and cannot be treated as a cosmetic edit to the existing theorem.
