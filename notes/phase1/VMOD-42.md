# VMOD-42: length through a retained hole

**Decision.** **PROVED from the printed definitions:** P5 charges the full length of a connecting tree inside a component of $\Omega^c$. The word “mod” removes the obligation to visit cover
cubes wholly in the hole; it does not give a zero-cost passage through it. The landed fine chosen-cover size makes the same choice about the cost of passage. The proposed contracted-hole
reading (case A of the follow-up) is **REFUTED** by P5 (1.34).

## 1. Printed definitions and their use

**PROVED (page images checked).** P5, printed p. 496, (1.33), defines $\mathcal D_k(\mathrm{mod}\,\Omega^c)$ by requiring every component of $\Omega^c$ to be contained in $X$ or disjoint
from $X$. In (1.34),
$$d_k(X\,\mathrm{mod}\,\Omega^c)=\inf_\Gamma M^{-1}|\Gamma|_\eta,$$
where $\Gamma$ is, in the paper's words, “a connected tree graph in the continuous space, contained in the domain $X$ ” and intersects every $\pi'_k$ cube meeting $X\cap\Omega$. The
following sentence says the function measures the linear size of components of $X\cap\Omega$ “together with distances between the components.” The tree may pass through a hole, but its
length there is included in $|\Gamma|_\eta$.

**PROVED (definition lineage).** P1 (2.26)–(2.27), printed p. 117, makes $\mathcal D_j$ a connected union of overlapping open $\pi'_j$ cubes and defines $d_j(X)$ as
$\inf_\Gamma M^{-1}|\Gamma|$, with a continuous tree contained in $X$ meeting **every** $\pi'_j$ cube contained in $X$. P3 (1.2)–(1.3), printed p. 34, uses a continuous tree contained in
the multiscale domain $Y$ meeting the eligible cubes in each layer and gives each layer a positive scale factor in $|\Gamma|_{\mathbb B_j}$. Neither definition identifies distinct points of
a hole. P3 (4.33)–(4.36), printed pp. 75–76, concern analytic spaces and are not the definition of $d_k(X\,\mathrm{mod}\,\Omega^c)$; that definition is P5 (1.33)–(1.34).

**PROVED (H7 reading).** P5 H7, (1.38)–(1.39), printed p. 497, bounds each boundary coefficient by $B_0e^{-\kappa d_k(X\,\mathrm{mod}\,\Omega_k^c)}$ on its stated analytic spaces. A label
containing a very large hole and only one small active attachment has bounded modular size: the tree need only visit cover cubes meeting that attachment. Two distant active attachments
require a connecting tree and pay their separation, even if its shortest route lies in the hole. Thus H7 does not give free decay in the diameter of a singly attached large-field component.

**PROVED (P3 construction); OPEN (modular transfer).** In P3 (4.44)–(4.48), printed pp. 78–80, $Y$ is made from the old $X_1$ and patches generated locally by marked cubes $\mathcal C$. The
proof takes a source tree $\Gamma_0\subset X$ for the **nonmodular** $d_j(X)$; p. 79 explicitly says it meets every eligible cover cube contained in $X_1$. This permits each patch to be
joined to $\Gamma_0$ by a path of bounded length, yielding (4.48), $\tilde d_{k+1}(Y)\le L^{-1}L^j\eta\,d_j(X)+d(2L+1)^d|\mathcal C|$. A modular source tree can miss the remote side of an
inherited hole. If an assignment there completes the hole or attaches a distant active patch, the bounded joining path used on p. 79 is unavailable. Formula (4.48) does not itself prove its
modular analogue or pay such a completion; the needed P6 assignment property remains
**OPEN-P6-INHERITED-HOLE-ASSIGNMENT**.

**PROVED (scope of P7 text); OPEN (bridge).** P7 (3.26)–(3.28), printed pp. 527–28, clusters old boundary labels meeting removed components and takes the polymer to be the union of their
labels and thickened removed components. Page 528 calls the activity bound “almost completely standard,” invokes the old exponential decay and (3.10), and asserts a bound of the form of P5
(1.35) with rate, for example, $3\kappa/2$. P7 (3.10), printed p. 520, supplies $e^{-p_2(\beta_k)-H_k|Z|_\eta}$ for a **removed** component $Z$. That displayed factor does not grow with
the length of a distinct retained hole. No corridor charge for two labels joined only through that retained hole is displayed in these steps. Whether the actual coefficients or incidence
rules supply one is **OPEN-P7-RETAINED-BRIDGE**; this is not a refutation of the paper's claimed result.

## 2. Landed definition and explicit comparison

**PROVED (landed declarations checked).** `Fluctuation/SizeModDefs.lean:ModAdmissible` chooses a family $\mathcal K$ of aligned $\pi'_j$ boxes contained in $X$ whose union covers
$X\cap\Omega$, and a nearest-neighbour connected graph $(W,E)$ contained in $X$ meeting each chosen box. `dcovModE` is the infimum of `bondCost (scaleW L m₀ m₁ j) E`, with $+\infty$ if no
witness exists; `dcovMod` is its real value on finite admissible labels. `Localization/TreeLength.lean:scaleW` is the constant $(L^{m_0+m_1+j})^{-1}$ for
**every** bond, including bonds wholly in $\Omega^c$. No quotient or zero-weight bond occurs.

**PROVED (witness, at a fixed scale).** Take a long interval $H_N\subset\Omega^c$ of normalized length $N$ in a sufficiently large one-dimensional torus. Let $X_-$ contain all of $H_N$ and
an active cover-sized collar at its left end, and $X_+$ contain all of $H_N$ and such a collar at its right end; choose the collars so these are admissible unions of cover cubes. Both labels
obey the whole-component rule and overlap in $H_N$. Their individual P5 sizes are $O_L(1)$, since all required cubes meet one collar, whereas
$d_k^{P5}((X_-\cup X_+)\,\mathrm{mod}\,\Omega^c)\ge cN-O_L(1)$: a connected tree visiting both collars crosses $H_N$. In the VMOD-41 fine chosen-cover realization, one box and a one-vertex
graph give $d^{\rm cov}(X_\pm)=0$; every union witness has cost at least $c'N-O_L(1)$. Thus **both** charge the long interior crossing, though their values need not agree.

**OPEN (global size comparison).** The papers require all eligible open cubes and a continuous tree; Lean chooses a cover subfamily, uses half-open fine boxes and nearest-neighbour bonds,
and has its own component relation. Neither $d^{\rm cov}\ge d^{P5}$, nor equality, nor the reverse inequality is landed. `LargeField/Def7FineSize.lean` names the needed estimate
`OPEN-PAPER-FINE-REALIZATION`: $d^{P5}_k(X)\ge a\,\mathrm{d7Size}(X)-b$ for uniform $a>0,b\ge0$, plus component and domain identifications. Its comment is an **open assertion**, not a
theorem. It would rebase H7 to $B_0e^{\kappa b}e^{-\kappa a\,\mathrm{d7Size}}$.

**PROVED (what is compared in Lean).** `d7SizeAtE` pulls `dcovModE` to the fine torus; `d7SizePreE` uses the raw region and `d7SizeE` the post-$R$ region.
`Def7FineSize.lean:d7SizePreE_le_d7SizeE`, `R/RExtraSize.lean:d7Size_le_d7SizePre_add` and `d7Size_le_d7SizePre_add_removed`, and `R/D7AvoidGeometry.lean:d7SizeE_eq_d7SizePreE_of_disjoint`
compare these **landed** regions or bound newly active cells. They do not compare P5's continuous size to Lean's chosen-cover size and do not waive the cost of bonds inside a retained hole.

## 3. Consequences and author question

**REFUTED (case A).** A zero-weight quotient of each component of $\Omega^c$ is not P5 (1.34). If imposed hypothetically, it would make the VMOD-41 two-attachment union cheap, change
`dcovModE` and all `d7Size*` bounds, and require new proofs of G1, G2, G3 and `SizeModExtend`. In particular, G2 would need to count potentially many exits from a large hole despite the
whole-component label rule; the paper's finite rooted sum (1.35) gives no such quotient statement. No Lean correction to a contracted functional is warranted.

**PROVED (case B, logical effect).** Full interior length leaves `Fluctuation/SizeModG1.lean:G1_cellCount`, `SizeModEntropy.lean:G2_X`, `SizeModUnion.lean:G3_dcov` under their actual
hypotheses, and `SizeModExtend.lean:modAdmissible_extend` and `dcovMod_le_add_of_region_grow`, unchanged. G3 requires an overlap in an active $\pi_j$ cell; common overlap only in a retained
hole fails, as VMOD-41 proves. `R/RExtraSize.lean` bounds the cost of **newly active cells**; it cannot pay a bridge inside a retained component that is never removed.
`R/D7AvoidGeometry.lean`, `R/RRawHoleComponent.lean`, and `R/RRipeCard.lean` remain valid geometry. These facts preserve the landed proofs while leaving the P5-to-fine comparison and the
physical P7 bridge open.

**Revised item 14(iv) for Roland.** P5 (1.34) counts the full tree length through $\Omega^c$, while P3 (4.48) uses a nonmodular source tree that visits all source cover cubes. In P6
(4.32)–(4.34), when a long inherited component of $Z_k$ is completed in the output domain without a new $P,Q,R,S$ seed, what source coefficient, incidence restriction, or operator estimate
pays the connecting length to an active patch at its remote end? Does the actual assignment exclude such a patch unless a marked cube pays for it? The original observation that inserting an
entire inherited hole has no uniform local cost remains; it should **not** be withdrawn on the ground that “mod” contracts the hole.

**Lean order, each proposed leaf at most 300 lines.** No change to the landed size definition or the last two days' geometry is indicated.
(1) `P5FineRealization` (200–300 lines per geometric leaf, **OPEN**): for every valid aligned $X,\Omega$, prove component compatibility and
$d_k^{P5}(X\,\mathrm{mod}\,\Omega^c)\ge a\,\mathrm{d7SizeAt}(\Omega,X)-b$, with $a>0,b\ge0$ depending only on $d,L$; `Def7FineSize.lean` states this open target.
(2) `P6InheritedHoleAssignment` (180–280 lines, **OPEN**): for every nonzero marked assignment $(X,\mathcal C,Y)$, supply $b_{\rm ret}\ge0$ such that
$\tilde d_{k+1}^{\rm mod}(Y)\le\lambda d_k^{\rm mod}(X)+C_{d,L}|\mathcal C|+b_{\rm ret}$ and its coefficient has an additional factor $e^{-\kappa b_{\rm ret}}$;
the zero-residual case is the sought modular analogue of P3 (4.48).
(3) `R/D7RetainedBridge` (200–300 lines per leaf, **OPEN**): for each nonzero physical cluster $\Gamma$ with old labels $X_i$, removed components $c_r$ and output $Y_\Gamma$,
prove $D_+(Y_\Gamma)\le\sum_iD_-(X_i)+c_G(p-1)+c_{\rm ext}\sum_r|c_r|+b_{\rm ret}(\Gamma)$ together with an extra weight factor $e^{-\kappa b_{\rm ret}(\Gamma)}$;
then use the two-size gas plan of VMOD-41. `RExtraSize`, `SizeModExtend`, `D7AvoidGeometry`, `RRawHoleComponent`, and `RRipeCard` require no correction.

**Confidence.** High for the paper's full-length definition, the landed full-length rule, and the counterexample to unrestricted union cost; medium for the exact physical realizability of
the retained-hole cluster; unresolved for its missing analytic payment and the continuous-to-fine comparison.
