# How the papers close the decay rate

**Scope and status.** This is a source-correspondence audit of the rate mechanism, not a proof of the whole renormalization step. `PROVED` means the displayed assertion follows from the cited definitions or inequalities. `PROVED CONDITIONAL ON ...` names an analytic or probabilistic input used without a new proof here. `OPEN` names a statement not supplied by the landed Lean declarations. Journal pages are used below. The P1, P3 and P4 formulas were checked against PDF page images; their OCR layers are unreliable.

| Key | Source | Relevant pages |
| --- | --- | --- |
| P1 | [*A low temperature expansion ... I*](/home/scott/Balaban/sources/BF02099355.pdf) | 117, 153 |
| P3 | [*Localization expansions I*](/home/scott/Balaban/sources/BF02506385.pdf) | 34, 75–81 |
| P4 | [*A low temperature expansion ... II*](/home/scott/Balaban/sources/Balaban.pdf) | 678, 680, 696, 706, 718 |
| P5 | [*A low temperature expansion ... III*](</home/scott/Balaban/sources/s002200050433 (1).pdf>) | 515–518 |
| P6 | [*Renormalization and localization expansions II*](/home/scott/Balaban/sources/s002200050470.pdf) | 29–44; consulted because P5 leaves its §3 proofs to P6 |

The source keys agree with [SOURCES.md](/home/scott/Balaban/review/SOURCES.md). For reproducibility, SHA-256 values of the PDFs in key order P1, P3, P4, P5, P6 are `3ed7e5c063208fab074aa9304e059fa46dbad182edc0070b90f213f1eb8d10c0`, `091adb3c13f9a718b84bc3b96e4619fece789d1a3140eb166c29af3d4b87fe3d`, `804ba741c65367a4bae3e1ce84f0c415999a32de0ff2e1c337b41d9fa9104a303`, `b3f0ef3491fc63b3988768893c1452b4bd1458a5f3e408e6af6000a555fd9a0f`, and `ee0ca061c9a7418d5da907a4dd09b66fb247f46bffcf68f83fa3ba502c342fc4`.

## 1. Source domains, supports and units

**PROVED (source reading).** In P1 p. 117, before (2.26), $M=L^m$ and $\pi_j$ is the compatible partition into $M$-cubes at the $j$-scale, or $ML^j$-cubes before rescaling. The overlapping cover $\pi'_j$ consists of $LM$-cubes, each the union of $L^d$ partition cubes. The domain class $\mathcal D_j$ consists of connected open unions of cubes from $\pi'_j$, with all cover cubes contained in $X$ used in (2.26). Equation (2.27) is

$$
d_j(X)=\inf_{\Gamma\subset X}\{M^{-1}|\Gamma|:\ \Gamma\text{ is a continuous tree meeting every }Q\in\pi'_j\text{ with }Q\subset X\}.
\tag{P1.2.27}
$$

The length is computed on the lattice of the $j$-scale; equivalently one rescales the set back before applying (2.27). A single $j$-scale edge therefore carries cost $M^{-1}$; in common unrescaled units an edge carries $1/(ML^j)$. P1 p. 117, (H.5) makes the old term depend only on the fields within $X$ and bounds it by $E_0e^{-\kappa d_j(X)}$. P1 p. 153, (3.127)–(3.128) gives the renormalized irrelevant term the rate $\kappa-1$, with a separate scale-small amplitude. The one unit loss occurs before P3's localization estimate.

**PROVED (source reading).** P3 p. 34, (1.2) defines $\mathcal D(\mathbb B_j)$ as connected $Y$ for which every connected component of $Y\cap\Omega_n\cap\Omega_{n+1}^{c}$ lies in $\mathcal D_n$, $n\le j$ (with $\Omega_0=T$ and $\Omega_{j+1}=\varnothing$). Its (1.3) defines $\widetilde d_j(Y)$ using a continuous tree $\Gamma\subset Y$ that meets every contained cube of the layer's cover and the weighted length

$$
|\Gamma|_{\mathbb B_j}=\sum_{n=1}^{j}(L^n\xi)^{-1}
|\Gamma\cap\Omega_n\cap\Omega_{n+1}^{c}|_{\xi},\qquad
\widetilde d_j(Y)=\inf_{\Gamma}\frac1M|\Gamma|_{\mathbb B_j}.
\tag{P3.1.3}
$$

The intersections in (1.3) are the layer pieces $Y\cap\Omega_n\cap\Omega_{n+1}^{c}$, whose connected components must lie in $\mathcal D_n$ by (1.2). Its (1.4)–(1.5) already state the intended expansion over $Y\supset X$, with terms local in both the background variable and the fluctuation variable inside $Y$, bounded by $E e^{-\kappa_0d_j(X)-2\kappa\widetilde d_{k+1}(Y)}$. For $Y\subset\Omega_{k+1}$, this mixed size is the ordinary next-scale size $d_{k+1}(Y)$. The two size arguments in this estimate are deliberately different: the original $X$ remains measured at scale $j$; the attached $Y$ is measured at the next scale (P3 pp. 34, 80–81, (1.3), (4.48), (4.52)).

**PROVED (source reading).** P3 pp. 75–79, (4.31)–(4.47) starts with $E e^{-(\kappa-1)d_j(X)}$. The interpolated field depends on independent $\theta$ and $\psi'$; (4.24) also realizes $\psi'$ through a hatted Gaussian field. The decoupling parameters $s_Q$ range over a complex polydisc of radius $e^{\kappa_1}$, where $\kappa_1$ is a separate parameter. Differentiated cubes $\mathcal C$ first give $Y_1$ in (4.41)–(4.43). The derivatives for disconnected components vanish, and setting parameters outside $Y_1$ to zero makes the summand depend only on the fields inside $Y_1$ (P3 pp. 77–78). Since $Y_1$ need not belong to the domain class, (4.44) completes every marked cube to admissible cover cubes and defines

$$
Y=X_1\cup\bigcup_iY^{(i)}\in\mathcal D(\mathbb B_{k+1}),\qquad Y_1\subset Y.
\tag{P3.4.44}
$$

The sum (4.45) is then over all $Y_1$ producing this **fixed** $Y$. Therefore the final term depends on $\theta,\psi'$, or on $\theta,\widehat\psi$ in the hatted version, only through their restrictions to $Y$. This is stated explicitly on P3 pp. 78 and 81 after (4.45) and in Proposition 4.3. The analytic domain is rebuilt from $\mathbb B_{k+1}(Y)$ before the fixed-$Y$ sum; see P3 pp. 78–79, (4.46). This is stronger than merely bounding the dependence by a collar after labeling.

## 2. Where the geometric cost goes

**PROVED (source reading and arithmetic).** Put $x=d_j(X)$, $t=\widetilde d_{k+1}(Y)$, $c=|\mathcal C|$, and $D=d(2L+1)^d$. P3 p. 80, (4.48) constructs a tree in $Y$ by joining a tree in $X$ to the cover cubes added by each mark:

$$
t\le L^{-1}L^j\eta\,x+Dc.\tag{P3.4.48}
$$

At this step $L^j\eta\le1$; hence $t\le x/L+Dc$. The $Dc$ term is the cost of the completion and its surrounding cover cubes. Thus the paper does **not** assert $d(Y^{+})\le d(Y)+O(1)$ for a generic collar, and overlap of $\pi'_j$-cubes by itself does not supply such an additive estimate. Nor is the old size prematurely replaced by $d_{k+1}(X)$. The source uses both the rescaling gain $L^{-1}L^j\eta$ and a large independent mark rate (P3 p. 80, (4.48)–(4.49)).

The Cauchy estimate (P3 p. 79, (4.47)) assigns each mark $e^{-(\kappa_1-1)}$ and retains $e^{-(\kappa-1)x}$. Assume

$$
L\ge3,\quad L^j\eta\le1,\quad \kappa\ge3\kappa_0+3,\quad
\kappa_1\ge4D\kappa.\tag{R1}
$$

Then, setting $\kappa_2=\kappa_1/2-1$, direct splitting gives

$$
\begin{aligned}
(\kappa_1-1)c+(\kappa-1)x
&=\kappa_2c+(\kappa/3-1)x
  +(\kappa_1/2)c+(2\kappa/3)x\\
&\ge\kappa_2c+\kappa_0x+2\kappa(Dc+L^{-1}L^j\eta x)\\
&\ge\kappa_2c+\kappa_0x+2\kappa t.
\end{aligned}\tag{R2}
$$

The first inequality uses $\kappa_1/2\ge2\kappa D$, $2\kappa/3\ge 2\kappa L^{-1}L^j\eta$, and $\kappa/3-1\ge\kappa_0$. This is exactly P3 p. 80, (4.49). For a fixed $Y$, P3 p. 81, (4.50) proves the remaining mark sum $\sum_{Y_1\mapsto Y}e^{-\kappa_2|\mathcal C|}\le1$ when, with $A=(2L+1)^d(M/M_1)^d$,

$$
M/M_1=L^{m_0}\ge14d,\qquad \kappa_1\ge 4\log A+2.\tag{R3}
$$

Here (R3) is a simple sufficient form of the printed entropy condition $\kappa_2/2\ge\log A$. The same page gives the stronger convenient condition $\kappa_1\ge8dm_0\log(2L+1)$ under its choice of $m_0$. The result is (4.51)–(4.52): each $Y$-term is local on $Y$, and has rate $\kappa_0d_j(X)+2\kappa\widetilde d_{k+1}(Y)$. **PROVED CONDITIONAL ON P3 Proposition 4.3's analytic interpolation premises:** (R1)–(R3) account for the rate; they do not replace the complex-domain hypotheses in that proposition.

## 3. From the two-budget estimate to the RG class rate

**PROVED CONDITIONAL ON P3 Proposition 4.3 and P6 Lemma 4.1.** P6 p. 29 explicitly keeps $X\subset X_1\subset Y$ when applying P3, saying this inclusion is needed for the improved $2\kappa$ factor. P6 pp. 30–31, (4.18)–(4.21) applies P3 to each old generation $j$ at its own $d_j(X)$, obtaining $e^{-\kappa_0d_j(X)-2\kappa d_{k+1}(Y)}$. It then sums over $j,y,X$ for fixed $Y$, spending one unit of the $Y$-rate on this counting. P6 pp. 31–32, (4.24)–(4.28), Lemma 4.1, gives a physical interaction activity $U_Y$, analytic on its indicated domain, local in $\theta,h,\psi$ on $Y$, with

$$
|U_Y|\le\epsilon\,e^{-(2\kappa-1)d_{k+1}(Y)}.\tag{R4}
$$

Its $\epsilon$ can be made arbitrarily small by the stated large-$\beta$ conditions (4.26)–(4.28). P6 p. 30, (4.19) explicitly says the old source amplitude is either the improved P1 (3.128) amplitude or $E_0$, depending on $j$. Thus the old-$j$ rescaling gain has survived into (R4).

**PROVED CONDITIONAL ON P6's cluster estimates.** The polymer activities in P6 pp. 35–39 are indexed by their actual domains $Y$. The touching family has a union domain $Z$, and the Cauchy radius $r_Y=\epsilon^{-1/2}e^{(2\kappa-1-5\kappa_0)d(Y)}$ in (4.43) leaves $e^{-5\kappa_0d(Y)}$ per marked activity. Equations (4.52) and (4.54) then give the effective-action rate $2\kappa-3-6\kappa_0$. P6 p. 43, (4.67) gives the observable rate $2\kappa-4-7\kappa_0$. The proof of P5 Proposition 3.3 on P6 pp. 43–44, (4.68), gives a further boundary rate $2\kappa-5-8\kappa_0$; P6 p. 44 then proves P5 Proposition 3.1 using the modified connectedness and $d_{k+1}(\cdot\bmod\Omega^c)$, with intermediate rate $2\kappa-4-7\kappa_0$. In P5 p. 515, (3.3)–(3.4), the advertised boundary bound is $\beta_k^{-1}e^{-3\kappa d_{k+1}(Y\bmod\Omega^c)/2}$; P5 p. 518, Proposition 3.3 separately preserves terms supported wholly outside $\Omega_{k+1}$. The P5 statements are explicitly deferred there to P6 for details.

For $\kappa_0\ge0$, a single sufficient inequality for all three displayed surplus rates to dominate $3\kappa/2$ is

$$
\kappa\ge10+16\kappa_0.\tag{R5}
$$

Indeed the weakest of the three is $2\kappa-5-8\kappa_0$, and subtracting $3\kappa/2$ gives $\kappa/2-5-8\kappa_0\ge0$. The other two differences are then nonnegative as well. P6 p. 43 states the two weaker conditions $\kappa-4-7\kappa_0\ge\kappa/2$ and $\kappa-5-8\kappa_0\ge\kappa/2$ in its respective proofs. This proves the numerical preservation of a $3\kappa/2$ working reserve.

**PROVED CONDITIONAL ON P4 Proposition 5.2 and the P6 inputs just cited.** P4 p. 678 says its localized H.4 is stronger than P1's H.5, and P4 p. 680, Theorem 1, (1.5) states return to the same class rate $\kappa$. P4 pp. 696 and 706, Propositions 2.1–2.2 and 4.1–4.2, invoke the localization results subsequently supplied by P6. P4 p. 718, (5.38)–(5.39) records the final effective-action estimate $4C_4B_6K_0K_5e^{-\kappa d_{k+1}(Y)}$ and chooses $E_0\ge4C_4B_6K_0K_5$. Equations (5.40)–(5.41) choose the observable bound and the large-$\beta$ threshold. Proposition 5.2 then states closure of the induction. The source does not identify $3\kappa/2$ with the final class rate; it spends further rate in summations and returns to $\kappa$. The final amplitude conditions and analytic hypotheses are part of the conditional claim, not consequences of (R1)–(R5) alone.

### A precise rate theorem extracted from the papers

**PROVED CONDITIONAL ON P3 Proposition 4.3, P6 Lemma 4.1 and its cluster bounds, and P4 Proposition 5.2.** Let $d\ge3$, $L\ge3$, $\kappa_0\ge0$, $M/M_1=L^{m_0}\ge14d$, $D=d(2L+1)^d$, and choose

$$
\kappa\ge\max\{3\kappa_0+3,\,10+16\kappa_0\},\qquad
\kappa_1\ge\max\{4D\kappa,\,4\log[(2L+1)^d(M/M_1)^d]+2\}.\tag{R6}
$$

Assume the complex field domains, smallness conditions and large-$\beta$ inequalities of those cited results, and assume $L^j\eta\le1$ for each old generation under discussion. Then an old input $E_j e^{-(\kappa-1)d_j(X)}$ expands into terms supported and field-local on admissible $Y$ with the P3 rate $E_je^{-\kappa_0d_j(X)-2\kappa\widetilde d_{k+1}(Y)}$. After the P6 fixed-$Y$ and cluster sums, the displayed reserve is at least $3\kappa/2$; the P4 final sums and amplitude choice yield its class bound $E_0e^{-\kappa d_{k+1}(Y)}$. The rate proof is (R2), the fixed-$Y$ bound (R3), and the inequalities preceding (R6). The conditions on $M/M_1$ here are the explicit rate and counting conditions; P3 also chooses $M_1$ large enough for its analytic estimates (P3 pp. 73–76, §4), and the corresponding landed `interaction_expansion_hat_bound` assumes `hMX`, namely $c_{\star}e^{N_0\kappa_1}\le M_1=L^{m_1}$. This extra scale-separation premise is part of the named analytic input, not a consequence of (R6). This conditional theorem does **not** assert that the open Lean locality bridge below follows from the papers automatically.

## 4. Exact comparison with landed Lean objects

| Object | Landed declaration and what it says | Correspondence and status |
| --- | --- | --- |
| One class rate | [`SmallField/Def6.lean`, `Consts.κ` and `IsSFFamily`](/home/scott/Balaban/Balaban/SmallField/Def6.lean) use one rate parameter across the family. | **PROVED:** P4 p. 680, (1.4)–(1.5) likewise uses the same $\kappa$ at input and output. The source intermediate rates exceed it before the final sums. |
| Single-scale size | [`SmallField/Def6Terms.lean`, `sizeJ`](/home/scott/Balaban/Balaban/SmallField/Def6Terms.lean) abbreviates [`Localization/TreeLengthCov.lean`, `treeLenCovOne`](/home/scott/Balaban/Balaban/Localization/TreeLengthCov.lean). Its `scaleW` is $L^{-(m_0+m_1+j)}$, the cell-side normalization. | **PROVED:** old generation $j$ is measured at $j$, as in P1 p. 117, (2.27). The proposed failure “all old sizes are measured at $k+1$” is false. |
| Domain and cover | [`Fluctuation/SizeModDefs.lean`, `IsDj`](/home/scott/Balaban/Balaban/Fluctuation/SizeModDefs.lean) is a nonempty connected union of overlapping cover cubes. `ChosenOne` in `TreeLengthCov.lean` chooses a cover family whose union is $X$; `treeLenCovOne` asks a tree to meet the chosen family. | **PROVED:** P1 p. 117, (2.26)–(2.27) asks the tree to meet every contained cover cube. The conventions differ. An equality or comparison theorem identifying the two full functionals is **OPEN-COVER-EQUIVALENCE**; it is not needed to explain the lost hat rate because Lean's own `gm2` uses its chosen-cover size. |
| Geometric expansion | [`Localization/TreeLengthCov.lean`, `gm2`](/home/scott/Balaban/Balaban/Localization/TreeLengthCov.lean) bounds the completed `Ysites` size by $L^{-1}d_j^{\rm cov}(X)+D\lvert C\rvert$; [`Localization/PolymerCount.lean`, `gm4`](/home/scott/Balaban/Balaban/Localization/PolymerCount.lean) proves the exponent split. | **PROVED:** this is P3 p. 80, (4.48)–(4.49), with the safe bound $L^j\eta\le1$. The extra $L^j\eta$ improvement of P3 is absent in the Lean bound, but its absence does not remove the rate gain needed here. |
| Old-term input | [`Fluctuation/InteractionHatAssemble.lean`, `interaction_expansion_hat_bound`](/home/scott/Balaban/Balaban/Fluctuation/InteractionHatAssemble.lean) assumes $E_{b,E}e^{-(\kappa_{\rm dec}-1)d_{j_E}^{\rm cov}(X_E)}$ and the corresponding $M$-term bound at $j_M$. It uses the decoupling parameter named `κ` there, separate from `κdec`. | **PROVED:** matches P3 p. 75, (4.31) and P6 pp. 29–31, (4.19)–(4.21); old generation sizes have not been collapsed. |
| I-5 conclusion | [`Localization/I5Expansion.lean`, `localization_expansion`](/home/scott/Balaban/Balaban/Localization/I5Expansion.lean) proves the fixed-$Y$ bound $E_be^{-\kappa_0d_j(X)-2\kappa_{\rm dec}\tilde d(Y)}$. [`Localization/I5Fluct.lean`, `i5_fluct`](/home/scott/Balaban/Balaban/Localization/I5Fluct.lean) retains this bound with fluctuation. | **PROVED:** numerical rate matches P3 pp. 80–81, (4.48)–(4.52). **OPEN-PAPER-LOCALITY:** `i5_fluct` gives agreement on `thickSet Y` for background data and `psiThick Y` for fluctuation, while P3 Proposition 4.3 says dependence on fields restricted to $Y$. |
| Physical hatted expansion | `interaction_expansion_hat_bound` reaches next-scale $Y\in\mathcal D_{k+1}$ with coefficient $\epsilon_Ue^{-(2\kappa_{\rm dec}-1)d^{\rm cov}_{k+1}(Y)}$. [`Fluctuation/InteractionHatV.lean`, `AgHatF`](/home/scott/Balaban/Balaban/Fluctuation/InteractionHatV.lean) requires hat agreement on `blockThick Y`; [`Fluctuation/HatEngineLocal.lean`, `blockThick`](/home/scott/Balaban/Balaban/Fluctuation/HatEngineLocal.lean) includes all $(k+1)$-blocks meeting `psiThick Y`. | **PROVED:** rate is P6 p. 31, (4.21), but its recorded hat locality is wider than the labeled $Y$. P3 pp. 78–81, (4.44)–(4.52) and P6 pp. 30–32, (4.18)–(4.28) attach a domain containing dependencies before estimating its rate. The tempting claim “the papers expand only in the old field” is false: P3 p. 81, Proposition 4.3 explicitly includes $\psi'$ or its hatted realization. |
| Label conversion | [`Fluctuation/HatLabelsGeom.lean`, `thick_spec`](/home/scott/Balaban/Balaban/Fluctuation/HatLabelsGeom.lean) bounds a completed collar $Z$ by $d(Z)\le A d(Y)+B$, $A=1+2^dc_1c_G>1$. [`Fluctuation/HatLabelsTerms.lean`, `labelAct_of_hatTerms`](/home/scott/Balaban/Balaban/Fluctuation/HatLabelsTerms.lean) therefore gives label rate $\kappa_H=(2\kappa_{\rm dec}-1)/A-c_1$. | **PROVED:** this conversion is valid for the current generic `HatTerms` interface. It spends the size increase *after* P3's mark exponent has already been summed away. P3 p. 80, (4.48) pays the completion by $\kappa_1\lvert C\rvert$ while the mark count still exists. No additive bound for the canonical Lean collar is claimed. |
| One-rate closure | [`Fluctuation/StepRates.lean`, `stepRates_no_closure_landed`](/home/scott/Balaban/Balaban/Fluctuation/StepRates.lean) combines the landed conversion with the class input and Step bounds. | **PROVED:** those particular landed inequalities cannot close a positive single class rate. This does not refute the source rate theorem (R6), because its Y-local activity has rate $2\kappa-1$ before the final cluster/label estimates. |

The extra rate loss that prevents closure in the landed chain is the **post-expansion** `HatTerms` to label conversion. `gm2`, `gm4`, `localization_expansion` and the old-term hypotheses have retained the source's two-budget estimate. The separate chosen-cover convention needs a source-equivalence audit, but it is not a reason to rewrite all old terms at scale $k+1$.

## 5. Smallest source-faithful repair, and its limits

**OPEN-PAPER-LOCALITY.** Strengthen the *physical* localization theorem, or add a new variant, so the term indexed by $Y$ factors through the background data on $Y$ and the actual hat block coordinates indexed by $Y$. In a useful Lean form, add a witness

$$
\operatorname{DepOn}_Y(T_Y):\quad
\Phi|_{\operatorname{blocksOf}(Y)}=\Phi'|_{\operatorname{blocksOf}(Y)}
\Longrightarrow T_Y(\Phi)=T_Y(\Phi').\tag{L1}
$$

The construction must attach any cube needed by `resDep`, `psiThick`, or `blockThick` **while the decoupling marks are still present**, and prove (L1) for its resulting $Y$, together with the bound $\epsilon_Ue^{-(2\kappa_{\rm dec}-1)d(Y)}$ and the source's open analytic neighbourhood. P3 pp. 78–81, (4.44)–(4.52) and P6 pp. 29–32, (4.18)–(4.28) give the mathematical pattern. Merely replacing `AgHatF` by (L1) in the existing theorem is invalid: a generic term local on `blockThick Y` can read a hat coordinate outside $Y$. This is a genuine new locality proof. The present `i5_fluct` also records `thickSet Y` and `psiThick Y`, so the repair may need to start there or at the physical resummation, with an explicit complex-domain inclusion. Call those missing assertions **OPEN-I5-Y-LOCAL** and **OPEN-PAPER-DOMAIN**.

**PROVED CONDITIONAL ON OPEN-PAPER-LOCALITY, OPEN-I5-Y-LOCAL and OPEN-PAPER-DOMAIN.** Define a `PaperHatTerms` interface with all existing analytic, measurable and bound fields of `HatTerms`, plus (L1), and retain its domain $Y$ as the label site/support. Then a `labelAct_of_paperHatTerms` construction can use `Lab.ysite = Y` and $d_{\rm label}(Y)=d^{\rm cov}_{k+1}(Y)$, applying the existing cube-label geometry and entropy estimate. Its rate is exactly

$$
\kappa_H=2\kappa_{\rm dec}-1,\tag{L2}
$$

with the same Cauchy/amplitude factors required by the label construction; no use of `thick_spec`, `hatA`, or `hatKappaH` is needed. The equality of sizes in (L2) follows because no relabeling of $Y$ takes place. Measurability and holomorphy must be carried through the new constructor; (L1) alone supplies neither.

This is smaller than the halo plan: leave `Def6`'s one rate, `sizeJ`, `IsDj`, `treeLenCovOne`, `gm2`, `gm4`, the I-6 termwise statements, the existing generic `HatTerms` theorem, and the abstract Mayer theorem intact. Add a stronger physical theorem and a direct label bridge. The halo plan in [HALO.md](./HALO.md) changes the class support and requires a positive-width I-6 bridge plus a two-set I-5 estimate; those obligations do not follow from this note. A separate proof that the physical Y-local theorem actually holds for the landed fields is indispensable.

### Lean-compatible arithmetic once (L2) is available

**PROVED (arithmetic); PROVED CONDITIONAL ON OPEN-PAPER-LOCALITY for an actual step.** Let the class input rate and P3 parameter both be $\kappa>0$; then the old input rate $\kappa-1\le\kappa$ is admissible. Set $\kappa_{\rm dec}=\kappa$, $\kappa_H=2\kappa-1$, $\kappa'=3\kappa/2+\kappa_0+1$, choose the auxiliary $\kappa_h\ge\kappa'$, and target $\kappa_{\rm out}=3\kappa/2$. The landed [`StepNonvanishBound.hκ`](/home/scott/Balaban/Balaban/Fluctuation/StepNonvanishBound.lean) condition is

$$
\kappa'+3\kappa_0+c_1+\tfrac32\le\kappa_H.
$$

It holds whenever $\kappa\ge8\kappa_0+2c_1+7$: substitution reduces it to $\kappa/2\ge4\kappa_0+c_1+7/2$. The [`Thm31b.thm31b_of_input`](/home/scott/Balaban/Balaban/Fluctuation/Thm31b.lean) output restriction is $\kappa_{\rm out}\le\min(\kappa_h,\kappa')-\kappa_0-1$; with this choice its right side is $3\kappa/2$. If $\kappa_h$ also meets its separate landed hypotheses and the activity satisfies the required smallness bound, the one-rate output dominates the input $\kappa$. Thus the Lean arithmetic does close for a Y-local activity at rate (L2). It does not close for the current `hatKappaH` conversion, as `stepRates_no_closure_landed` proves. The paper's sufficient condition (R5) and this Lean-specific condition are distinct because their cluster estimates are packaged differently.

## 6. Dependency-ordered Lean work packages

Each item is a candidate task of roughly 300 lines or less; dependencies are sequential. No item below is claimed to have been implemented.

1. **PROVED prerequisite:** freeze the current size/rate API in a short source audit: `sizeJ = treeLenCovOne`, `gm2`, `gm4`, and `interaction_expansion_hat_bound`'s $\kappa_{\rm dec}-1$ hypotheses. If paper-identical size is needed, prove **OPEN-COVER-EQUIVALENCE** separately; do not put it into the locality bridge by assumption. Source checks: P1 p. 117, (2.26)–(2.27), P3 p. 80, (4.48)–(4.49).
2. **OPEN-PAPER-DOMAIN:** define the fixed-$Y$ generating set and prove restriction/inclusion of the relevant open complex neighbourhoods before Cauchy estimates. The target corresponds to P3 pp. 78–79, (4.45)–(4.46). Include the precise background and fluctuation radii used in the landed I-5 interface.
3. **OPEN-I5-Y-LOCAL:** expose the mark-indexed `Y1` and completed `Y` in the localization construction, prove $Y_1\subset Y$, and show all background and fluctuation dependencies lie in the completed $Y$. Carry `gm2` and `gm4` through this change without weakening the exponent. Source: P3 pp. 77–81, (4.41)–(4.52).
4. **OPEN-PHYSICAL-HAT-LOCAL:** prove that the actual interaction terms, after composing the covariance square root with the hatted block field, factor through the block variables of $Y$, or attach the required blocks during the mark-indexed construction and rerun the same two-budget bound. The statement must include the old terms, potential, and observable pieces. Source: P3 p. 81, Proposition 4.3, and P6 pp. 29–32, (4.18)–(4.28).
5. **OPEN-PAPER-HAT-TERMS:** add `PaperHatTerms` and derive it from the theorem in item 4, preserving the existing complex $\sigma$ neighbourhood, $Y$-rate $2\kappa_{\rm dec}-1$, $\epsilon_U$, measurability, and fixed-$Y$ sum. This is the contract for a label theorem; no arbitrary `HatTerms` coercion is valid.
6. **OPEN-PAPER-LABELS:** prove `labelAct_of_paperHatTerms` with label support $Y$, checking `CubeLabels` geometry, `LabelAct` locality, entropy, measurability and holomorphy. The rate is (L2); the existing halo conversion remains available for generic terms.
7. **OPEN-PAPER-STEP:** supply a rate arithmetic lemma with the choices below (L2) and all `StepNonvanishBound`, `ObsMarks`, `Thm31b`, and amplitude premises, then thread it into the physical step. This task depends on items 4–6 and on the independent complex/amplitude inputs; arithmetic alone cannot certify the RG theorem.

**Conclusion.** The papers pay for geometric completion with a large independent decoupling rate while the marks remain visible, then obtain a physical activity local on the same $Y$ that carries the $2\kappa-1$ rate. The landed numerical localization already has this rate. Its current hat-locality interface forces a later support enlargement and rate contraction; proving a source-faithful $Y$-local physical interface is the remaining substantive repair.
