# VMOD-40: the post-`R` H7 boundary charge

**Source and status.** P7 is Balaban, *The large field renormalization operation for classical N-vector models*, pp. 519–20, 527–29, equations (3.8)–(3.10) and (3.26)–(3.29) (`sources/s002200050486.pdf`). The paper uses its continuous-tree H7 size; the landed `d7SizePre` and `d7Size` are the different fine chosen-cover size of `LargeField/Def7FineSize.lean`. Claims below marked PROVED follow directly from the cited formulas or landed definitions. An estimate asserted in P7 for its size is not thereby proved for the fine size.

## 1. Assignment after removal

**PROVED (source formula).** Put $C=\bigcup_i Z_i$, the union of removed components, and $Y_k=Z_k^{\rm post}$. Equation (3.26) factors out $T''_k(Y_k)\exp B^{(k)}(Y_k)$; its braces sum the removed-component operators $T''_k(Z_i)e^{E_k|Z_i|}$ multiplied by
$$
 \exp\{B^{(k)}(Y_k\cup C)-B^{(k)}(Y_k)+B'^{(k)}(Y_k\cup C)\}.
$$
P7 p. 527 says explicitly that terms with localization domain disjoint from every removed $Z_i$ cancel in the displayed difference. Hence an old coefficient $B(X)$ with $X\cap C=\varnothing$ remains in the factored $B^{(k)}(Y_k)$; one with $X\cap C\ne\varnothing$ is in the exponential inside the braces, combined with the new $B'^{(k)}$ terms. It is not an inherited output H7 coefficient with a larger label.

**PROVED (source construction).** P7 pp. 527–28 takes the Mayer expansion of that exponential. A cluster of connected labels $X_1,\ldots,X_p$ touches at least one $Z_i$; its polymer is the union of those labels and the prescribed thickened touched components. Summing all clusters and component sets with the same polymer gives the activity $\rho''_k(\mathcal X)$ in (3.27); cluster exponentiation gives $P^{(k)}(\mathcal X)$ in (3.28).

Thus the assignment $(X,C)\mapsto\mathcal X$ is many-to-many, followed by resummation; there is no single-label map. By p. 529, $\mathcal X\subset Y_k^c$ contributes to the new H4 term $R''_m$, whereas $\mathcal X\cap Y_k\ne\varnothing$ contributes to the new H7 boundary family. P7 then identifies the post-`R` large region as $Z_k=Y_k$. The other new boundary terms from action conversion, P7 (3.23), also meet removed components (p. 527).

**REFUTED.** VMOD-37 inequality (3), applied independently to every old $B(X)$ meeting $C$, is not the physical post-`R` mechanism. Such a coefficient is consumed by the gas. The needed estimate concerns the *sum of all gas clusters assigned to each new boundary label*. In particular, one component factor cannot be multiplied once for every old $X$ touching that component.

## 2. One reserve per component

**PROVED (source bound).** P7 (3.8) supplies $e^{-2p_2(\beta_k)-H_k|Z|_\eta}$. The first $e^{-p_2}$ pays the integration/action/volume estimate (3.9) and $E_k|Z|$; P7 bounds these costs by $O((\log\beta_k)^{2d+2})$ and $O((\log\beta_k)^{2d+1})$, assumes degree $p_2\ge 2d+2$ and a large leading coefficient, and obtains (3.10):
$$
 \|T''_k(Z)e^{E_k|Z|}F\|\le e^{-p_2(\beta_k)-H_k|Z|_\eta}\sup|F|.
$$
This *remaining* factor is once per removed component. P7 p. 528 uses it together with the enhanced $3\kappa/2$ decay of the old boundary terms to sum the Mayer gas, obtaining activities with H7-type rate $3\kappa/2$ and prefactor $\beta_k^{-m-1}$; after (3.28) their prefactor is ${\rm const}\,\beta_k^{-m-1}\le\tfrac12\beta_k^{-m}$. P7 p. 529 assigns a final boundary constant independent of the input $B_0$. These are paper-level claims for its size.

**OPEN-PAPER-FINE-REALIZATION.** P7's continuous-tree estimate does not state a bound for the landed fine chosen-cover size. The required replacement must root clusters at removed components, retain decay in the polymer label, and prove the post-label sum before extracting the single remaining factor from (3.10).

**OPEN-R-D7-CHARGE (fine-size version).** A sufficient *reserve ledger*, before proving the full gas bound, is
$$
 p_{2,\rm run}(k)\ge \kappa(dL+d+3)(S.\mathrm{crit}\,k)^d
       +E_{\rm labels}(k,c)+E_{\rm Mayer}(k,c)+E_{\rm gas}(k,c)
       +\log^+(B_{\rm st}/B_0),\qquad c\in\mathrm{rem}_k.
$$
Here the three $E$ terms must be explicit upper bounds for, respectively, rooted old-label sums using the spare $\kappa/2$ rate, connected-cluster choices, and polymer/cluster exponentiation; they are charged *once to the component gas*, not once per old term. The first term is the geometric worst case from VMOD-38: $D_+-D_-\le(dL+d+3)|A_X|$ and `RRipeCard.removed_card_le` gives $|c|\le(S.\mathrm{crit}\,k)^d$. A sharper gas theorem may pay the size increment directly through $H_k|c|_\eta$, but that term cannot also pay earlier volume costs.

**PROVED (definitions), OPEN (domination).** `Counter/Params.lean` defines `S.r k = ⌈S.Rb * S.lam k ^ 2⌉₊`, `S.rho k = S.c0 * S.r k`, `S.crit k = 2*S.rho k+10`, and `Setting.Ok.p2_ge` requires $p_2\ge2d+3$. `Analytic/Constants.lean` defines `p2Run S.A2 S.p2 P.beta k = S.A2*(log(P.beta k))^S.p2`; `RunningHyp.logBeta_ge` gives a lower bound on that logarithm in terms of $\hat\lambda_k-3$. Thus $\mathrm{crit}_k^d=O(1+\hat\lambda_k^{2d})$ while $p_{2,\rm run}$ has degree at least $2d+3$, so the *displayed polynomial geometry cost* is asymptotically payable after choosing the initial $\beta$ threshold and constants. The three entropy functions have no landed bound, so `Setting.Ok` alone does not prove the ledger. `BudgetConsts` (`Budget/Exponents.lean`) contains only `c1,c2,H0,beta`, and `HRun = H0 log beta`; it has no H7 reserve field. `R/SmallFactorGe.lean:smallFactor_ge` controls its five $\gamma_i-\log5$ exponents, not this $p_2$ ledger. Add a numerical `RD7ChargeParams` condition after deriving explicit entropy bounds; rechoose the initial $\beta$ threshold, or choose `S.A2` jointly with downstream constants.

For one component $c$, the usable old-label estimate must have the form $\sum_{\Gamma\ni c}|w(\Gamma)|e^{(3\kappa/2)D_{\rm post}(\mathcal X_\Gamma)}\le e^{-p_{2,\rm run}(k)+E_{\rm gas}(k,c)}$, with combinatorial and boundary factors included in $w$. A naked estimate $p_2\ge\kappa(dL+d+3)|c|$ does not establish this sum.

## 3. Landed record target and Lean packages

**PROVED (record inspection).** `LargeField/Def7v2Class.lean` declares `D7Bdry2` and `D7Bdry2Post`; `Def7v2Variants.lean` uses pre constant/rate `C7.Bst, (3/2)*P6.κ`, raw region `A.H.F.Zpre k`, and post `C7.B0, P6.κ`, region `(A.H.step k).Z`. Their `bound` fields use `bdryDomsPre`/`d7SizePre` and `bdryDomsPost`/`d7Size`, respectively, on the same pinned ball `hSetB2` and `H7Domain` formula. `Def7FineSize`'s `d7SizePre_le_d7Size` gives the *wrong direction* for direct transfer.

**Proposed bound theorem (conditional on OPEN producer).** For pre and output `Rep` records `rin,rout`, assume `hin : D7Bdry2 Fr hnn hkK rin (fun A => A.H.F.Zpre k) ... Bst ((3/2)*κ) hv rH`, $0\le\kappa$, $0\le B_{\rm st}\le B_0$ and $0<B_0$, and a history projection from each `rout.hist` member to its pre class. For every `A∈rout.hist`, `Y∈bdryDomsPost Fr A k ((A.H.step k).Z)`, and H7-domain input, require a disjoint case split: if $Y\cap A.H.\mathrm{removedSet}(k)=\varnothing$, `rout.B A Y = rin.B Apre Y`, with either `Y∈bdryDomsPre` and $D_+(Y)=D_-(Y)$, or the old coefficient zero by `hin.support`; if they meet, require the gas/action-conversion output directly satisfy $\|rout.B\,A\,Y\|<B_0e^{-\kappa d7Size\,Fr\,A\,k\,Y}$. Then `D7Bdry2Post.bound` follows: the first case uses $e^{-3\kappa D_-/2}\le e^{-\kappa D_+}$ with equal sizes, and the second is the producer bound. This theorem does **not** assume or prove a per-old-term multiplier $W_R$. If both kinds contribute to one label, replace the case split by a decomposition and the explicit budget $B_{\rm avoid}+B_{\rm gas}\le B_0$ at that label.

**Transfer of other fields.** On an unchanged valid label, `loc_field`, `real`, `analytic`, and `rot` transfer by coefficient identity; `H7Domain` still uses `globalLH` in both records. `loc_hist` and `euclid` transfer only if identity is coherent across the two histories and lattice symmetries; pointwise equality for one history does not supply those equalities. `support` needs a separate output-zero statement on post-invalid labels, and new gas coefficients require all seven fields afresh. A post-valid label avoiding removal can fail pre-validity because removal splits a complement component; its old coefficient is then zero by pre `support`. This label case and size equality follow from definitions but are not cited as landed lemmas.

**Lean packages, dependency order (proposed; each at most 300 lines).** (1) `R/D7AvoidGeometry` (150–240): characterize labels avoiding `removedSet`, old support, and size equality from `SizeModDefs.ModAdmissible`, `History/OmegaPost`, `Def7FineSize`; pure geometry. (2) `R/D7ReserveArithmetic` (180–260): polynomial bound for `S.crit`, `p2Run` domination under an explicit `RD7ChargeParams`; reuse `Counter/Params`, `Analytic/Constants`, `RRipeCard.removed_card_le`; arithmetic can start now. (3) `R/D7BoundTransport` (120–200): the preceding two-case bound-field theorem with explicit coefficient-map and gas-bound hypotheses; pure record transport can start now. (4) `R/D7GasActivity` (220–300 per leaf): rooted H7-label entropy, Mayer connectivity, and component reserve, culminating in a fine-size activity estimate; **OPEN**, waits for the physical `R` generator and source action-conversion coefficients. (5) `R/D7GasBoundary` (180–280): cluster exponentiation, split into H4 and H7, analytic/symmetry/support producers and the full `D7Bdry2Post`; **OPEN**, depends on (4) and the physical `R` construction. `RHistoryLabels.exists_enum` and `realized_congr` provide history enumeration, not gas bounds.

**Confidence.** High for the source assignment and the failure of independent $W_R$ charges; high for record and constant inspection; medium for the stated sufficient numerical ledger; low for closing the fine-size gas estimate until a rooted entropy theorem and the physical coefficients are supplied.
