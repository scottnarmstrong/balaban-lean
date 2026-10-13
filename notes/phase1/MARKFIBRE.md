# MARKFIBRE — the marked coefficient hull and its fibre

Source check: the declaration names below occur in the current, read-only `/home/scott/Balaban/Balaban` tree. This note resolves leaf 4
of `notes/phase1/ENERGYFAM.md` at the geometric and fixed-datum levels. The physical parameter family and the class output remain
separate obligations.

## 1. Index, size, and read set

**PROVED.** In `Fluctuation/Thm31CoeffA.lean`, `gsumCoeff` is exactly
`∫₀¹ Gsum μ Lab (A(s)).H y0 (fun i => G i s) T ds`.
Here `T : Finset (CubeB m₀ K univ)` is a finite set of level-$K$ cubes.
It is the external Mayer coefficient index; the label sum is inside `Gsum`.
`interpCoeff I T` is this `gsumCoeff` for the data of `I`.
`interpCoeff_spec` gives, for every $T$,
$$
\|\operatorname{interpCoeff}(I,T)\|
 \le B_I\exp[-\kappa'_I d_{\rm ext}(T)],\qquad
B_I=C_{\rm PE}\sum_i F_{0,i}\exp[-\kappa_{0,I}d_L(Y_{0,i})].
$$
Thus the coefficient rate is $\kappa'$, after the Mayer label sum;
the label weight is part of the prefactor, not a second size for $T$.

**PROVED CONDITIONAL ON the locality premises in the cited theorem.** `gsumCoeff_ext_congr` says that agreement of external fields on
`Yhat Ω (sitesOf T)` makes the coefficients equal, if each activity and mark reads only its own label sites as stated in its
hypotheses. `Yhat_univ` gives `Yhat univ (sitesOf T) = sitesOf T`. At the whole torus the needed read set is therefore
precisely $X_T:=\operatorname{sitesOf}(T)$, with no halo. `gsumCoeff_congr` separately restricts the contributing labels to those with
`blocksOf (Y ∩ Ω) ⊆ T`; it does not enlarge the read set.

**PROVED.** `sitesOf` is the union of the boxes of $T$.
An arbitrary $T$ need not produce a nonempty connected polymer.
`gsumCoeff_eq_zero_of_dOmega_top` gives vanishing when
$d_\Omega(X_T)=\top$, and `isPolyDom_and_dExt_eq_sizeJ`
gives, for nonempty $T$ of finite $d_\Omega$,
$$ X_T\in\mathcal D_K,\qquad d_{\rm ext}(T)=d_K(X_T). $$
For actual interpolation marks, the packaged
`interpCoeff_ne_zero_active` proves both assertions
whenever `interpCoeff I T ≠ 0`, including nonemptiness of $T$.
`isDj_of_isPolyDom` makes $X_T$ an `IsDj` domain.
The generic `gsumCoeff` version also follows: the empty coefficient
vanishes by `dOmega_empty` and `gsumCoeff_eq_zero_of_dOmega_top`;
for a nonempty nonzero coefficient, $d_\Omega\ne\top$, so apply
`isPolyDom_and_dExt_eq_sizeJ`.

## 2. The minimal hull and rooted support

**PROVED.** Take $H_{\rm mark}(T)=X_T=\operatorname{sitesOf}(T)$. On the nonzero support it is `IsPolyDom`, hence `IsDj`, contains the
whole-torus read set, and has size **exactly** $d_{\rm ext}(T)$. The hull cost is $a=1,b=0$; no `thick`, `nbhdF`, or determinant collar
is needed. Defining this map on all $T$ is harmless: its value is legal whenever the coefficient is nonzero, which is the support
assertion needed by the regrouped term.

**PROVED CONDITIONAL ON a root-label premise.** The polymer property alone does not imply that the root site lies in $X_T$.
`anchor_of_labels` proves `rootCube z ∈ T` for a nonzero coefficient if every mark label of root $z$ contains that
cube. `anchor_of_bridgeFamily` supplies this condition if the actual labels belong to `bridgeFamily` and its domain
hypotheses hold. Then `rootSite_mem_sitesOf_iff` gives `rootSite z ∈ X_T`;
`y_mem_of_markedTerm_ne_zero_of_anchor` packages the result at fixed $(y,X)$. `bridge_of_mem`
concerns a *label*: if it already contains the root cube, its bridge equals the label. It supplies no reason to thicken the
*coefficient* hull once the label anchor holds. **OPEN:** prove the root-label premise for the physical family at all field parameters
used by the output class.

## 3. Fibre count and decay transfer

**PROVED.** With $L^{m_0}\mid N_1$, `sitesOf_injective`
at $j=K$ says that $T\mapsto X_T$ is injective. Consequently
$$\#\{T: H_{\rm mark}(T)=X\}\le1.$$
At fixed root site $y$, `rootSite_injective` and
`fibre_subsingleton` give at most one pair $(z,T)$.
`rootedSum_eq_of_pair` identifies the sum with that coefficient
when the pair exists; `rootedSum_eq_zero` handles an empty fibre.
One must retain the root index $y$ while forming the class term;
an unrooted sum over all $z$ is a different count.

**PROVED CONDITIONAL ON a uniform coefficient prefactor.** If
$\|e(z,T)\|\le B_{\rm mark}e^{-\kappa'd_{\rm ext}(T)}$ and nonzero
coefficients satisfy the active-size identity, then
`rootedSum_norm_le_of_activeSize` gives
$$\left\|\sum_{\substack{z:\operatorname{rootSite}z=y\\
                 T:X_T=X}}e(z,T)\right\|
 \le B_{\rm mark}e^{-\kappa'd_K(X)}.$$
For fixed-datum `InterpMarks`, `norm_markedTerm_le`
already proves this statement from the uniform bound on
$C_{\rm PE}\sum_iF_{0,i}e^{-\kappa_0d_L(Y_{0,i})}$.
Its prefactor is $B_{\rm mark}$ itself; regrouping multiplies it by $1$.

**PROVED numerically.** `StepTower` has $\kappa'=\tfrac32\kappa_{\rm dec}+\kappa_0+1$; `stepOutputPhysical` sets
$\kappa_{\rm out}=\tfrac32\kappa_{\rm dec}$. Thus $\kappa'-\kappa_{\rm out}=\kappa_0+1>0$. Since `sizeJ` is
`treeLenCovOne` and `treeLenCovOne_nonneg` proves $d_K(X)\ge0$, $e^{-\kappa'd_K(X)}\le e^{-\kappa_{\rm out}d_K(X)}$. No part of the $\kappa_0+1$ gap is spent on this mark fibre.

## 4. Why the determinant collar is the wrong mark hull

**PROVED containment; REFUTED rate suitability.**
`sitesOf_subset_detCollarHull` shows that the collar
contains the mark read set at $\Omega=\mathrm{univ}$.
`detCollarHull_isDj` makes it legal on active $T$, and
`detCollarHull_fibre` bounds its fibre by
$2^{c_1(1+d_K(X))}$. But `detCollarHull_sizeJ_le` costs
$d_K(H_{\rm det}(T))\le(1+B)d_{\rm ext}(T)+B$.
The resulting `hullRate` for marks would be
$\kappa'/(1+B)-c_1\log2$.
`collarB_three` gives $B=60750$,
and `c1_three` gives $c_1=3375$ at $d=L=3$.
To obtain $\kappa_{\rm out}$ from this method one would need
$$\kappa'\ge60751(\kappa_{\rm out}+3375\log2).$$
The tower instead has $\kappa_{\rm dec}=100(\kappa_0+3385)$ and
$\kappa'=\kappa_{\rm out}+\kappa_0+1$.
Because $\kappa_{\rm out}=150(\kappa_0+3385)$ and $\kappa_0\ge0$,
$\kappa_0+1<60750\kappa_{\rm out}$; the required inequality fails.
Increasing $\kappa_{\rm dec}$ while keeping the tower formulas would
increase the shortfall. The landed `stepHullMin` is a threshold on the
raw determinant rate, not a new independent mark rate.

## 5. One output index and symmetry

**PROVED at the level of indices.** `Terms.E` takes
one site $y$ and one set $X$; `polysAt` selects `IsPolyDom` sets
containing $y$. There is no requirement that mark and determinant
summands use the same map from $T$ to $X$. At each $(y,X)$ set
$$e^+_y(X,q)=\sum_{\substack{z,T:\operatorname{rootSite}z=y\\X_T=X}}
e_{\rm mark}(z,T,q)
+\sum_{\substack{z,T:\operatorname{rootSite}z=y\\H_{\rm det}(T)=X}}
e_{\rm det}(z,T,q).$$
The first sum is `rootedSum`; the second is the rooted
version of `detCollarGrouped`.
`sum_detCollarGrouped` and `sum_markedTerm`
give the corresponding finite sum identities at fixed datum.
**OPEN:** the joined analytic class term with common physical fields,
its domain inclusions, and the determinant plus mark prefactor budget.

**PROVED geometry; PROVED CONDITIONAL ON coefficient covariance.** `sitesOf_cubeAct` gives $H_{\rm mark}(r\cdot T)=rH_{\rm mark}(T)$ for a paving symmetry. `genSymm_mem_pavingSymGroup` applies it to `GenSymm`.
`rootedSum_covariant`, or its specialization `markedTerm_covariant`, then gives term covariance provided
the coefficients themselves satisfy the stated covariance premise. That premise for the physical parameter family is **OPEN**.

## 6. Remaining leaves, in dependency order

| Leaf and size | Exact target and input | Status / worker |
| --- | --- | --- |
| `markFibre_sitesOf`, ≤80 lines | Repackage active `IsDj`, `dExt=sizeJ`, fibre ≤1 and `sitesOf_cubeAct`; `RootActiveSize`, `CubeSystem`, `RootPavingMap`. | **PROVED** from landed lemmas; **OPEN** as wrapper; Sonnet can start now. |
| `markCoeff_active_family`, ≤120 lines | For every chart parameter and root, nonzero `gsumCoeff` has active $X_T$, and a common $B_{\rm mark}$, $\kappa'=O.k'$. Use `gsumCoeff_eq_zero_of_dOmega_top`, `isPolyDom_and_dExt_eq_sizeJ`, `paramMarked_analytic_local_bound`. | **OPEN** physical `ParamMarkFamily` and uniform prefactor; strong after that family lands. |
| `markCoeff_local_on_sitesOf`, ≤120 lines | On an open chart, equality of fields on $X_T$ implies equality of coefficients; use `gsumCoeff_ext_congr`, `Yhat_univ`, and explicit activity/mark label locality. | **OPEN** physical label-local hypotheses; strong after the family lands. |
| `markCoeff_anchor_covariant`, ≤180 lines | Root cube in $T$ for each nonzero coefficient and coefficient covariance; use `anchor_of_bridgeFamily` and `sitesOf_cubeAct`. | **OPEN** family labels and coefficient covariance; strong. |
| `energyMarkGrouped_zero`, ≤180 lines | Define the rooted mark sum on $X_T$; prove support, locality, analytic chart bound $B_{\rm mark}e^{-O.kout d_K(X)}$, covariance, and total-sum identity. | **OPEN** pending the preceding family leaves; strong. |
| `energyOutputTerms`, ≤300 lines | Add this mark term to `detGrouped` on the same $(y,X)$ index, checking the class domain and output prefactor. | **OPEN** joined physical class inputs; strong. |
