# Round 38: the post-$R$ cover extension

**13 October 2026.** Lean paths are relative to /home/scott/Balaban/Balaban/. Sources: P5, sources/s002200050433 (1).pdf, printed pp. 499–500, Theorems 1–2; P7, sources/s002200050486.pdf, printed p. 497, Theorems 2 and 5. The proof concerns the **landed fine chosen-cover size**, not P5's continuous-tree functional. Write $d=S.d$, $L=S.L$, $a=L^{m_0+m_1+k}$ fine sites per scale-$k$ cell. Assume $d\ge1$, $L\ge2$, $1\le k\le k_0$, $k\le K$, a Good setting, an admissible history, and $n_j\ge4\rho_j+21$ for $1\le j\le k_0$.

## 1. Exact functionals and minimizer

**PROVED from landed definitions.** For frame $F$, history $A$ and coarse finite $X$, set $X_f=d7Pull(F,k,X)$, $\Omega_-=d7Pull(F,k,\operatorname{OmegaCube}(A.H,k))$, $\Omega_+=d7Pull(F,k,A.H.\operatorname{omegaPost}(k))$. Def7FineSize.lean:297–316,418–480 defines
$$D_-=d7SizePre(F,A,k,X)=\bigl(dcovModE(m_0,k,\Omega_-,X_f)\bigr)_{\mathbb R},\qquad
D_+=d7Size(F,A,k,X)=\bigl(dcovModE(m_0,k,\Omega_+,X_f)\bigr)_{\mathbb R}.\tag{1}$$
The real conversion is ENNReal.toReal. FineValid and FineValidPre are, respectively, DjMod plus finiteness for $\Omega_+$ and $\Omega_-$. A finite post label supplies IsDj: $X_f$ is a nonempty connected union of aligned side-$La$ boxes. Post validity need **not** imply pre validity, but IsDj makes the pre infimum finite (Fluctuation/SizeModCore.lean:95). Def7FineSize.dcovModE_mono_region and d7SizePre_le_d7Size give $D_-\le D_+$.

**PROVED minimizer.** Fluctuation/SizeModDefs.lean:90–106 defines ModAdmissible $m_0\,k\,\Omega\,X_f\,\mathcal K\,W\,E$: every aligned side-$La$ box in the chosen family $\mathcal K$ lies in $X_f$; their union covers $X_f\cap\Omega$; $(W,E)$ is a nonempty connected nearest-neighbor graph inside $X_f$ meeting each chosen box. Its cost is $|E|/a$ (Localization/TreeLength.lean:42–47,528). Fluctuation/SizeModCore.lean:74–85,120–129 proves an attained minimizer $(\mathcal K_-,W_-,E_-)$ for $D_-$. It may contain cycles; none are needed in the added graph. The family is **chosen**, so it need not contain every eligible box.

**PROVED region change.** History/OmegaPost.lean:39–65 defines $\Omega_k^{post}=\Omega_k^{pre}\cup\bigcup\mathrm{Rem}_k$. The newly active coarse cells are
$$A_X=X\cap(\mathrm{removedSet}_k\setminus\Omega_k^{pre}).\tag{2}$$
The frame and d7Pull make $X_f$, $\Omega_-$ and the fine lift of $A_X$ unions of aligned side-$a$ cells. At $k=0$, RegionHistory.rem_empty makes $A_X$ empty.

## 2. Construction and explicit constant

**PROVED raw-hole component fact.** Let $Q$ be a nearest-neighbor coarse-cell component of $X\cap(\Omega_k^{pre})^c$ meeting $A_X$. Then $Q$ lies wholly in one removed component $c$ and hence in $A_X$. For $k\ge1$, RegionStep.Omega_compl_subset_Z0 and Z0_subset_Zpre (Region/Inclusions.lean:200,213) put the raw hole in $Z_k^{pre}$. Nearest-neighbor adjacency is included in the $S.\omega k$ adjacency defining H.Comp $k$; $S.\omega k\ge1$ follows from GasIdentity.omega_ge_eleven (R/GasIdentity.lean:163). A path in the raw hole cannot change its $Z_k^{pre}$ component. One cell in removed $c$ therefore puts all of $Q$ in $c$, by component uniqueness (Region/Hull.lean:147). Distinct removed components cannot be joined by a free raw-hole path.

**PROVED cover extension.** For every coarse cell $q\in A_X$, choose an aligned base $b_q$ of a side-$La$ box $B_q=\operatorname{box}(b_q,La)\subset X_f$ containing it. IsPiPrimeUnion (Fluctuation/SizeModDefs.lean:43–48) gives such a box from any fine site in $q$; alignment makes the whole cell lie in the box. Let $\mathcal K_+=\mathcal K_-\cup\{b_q:q\in A_X\}$. There are at most $|A_X|$ new bases, and the family covers $X_f\cap\Omega_+$. Unioning chosen bases preserves the box-containment clause of ModAdmissible. No cover of all boxes is imposed.

**PROVED graph extension.** If $A_X=\varnothing$, retain the old admissible pair. Otherwise represent each side-$a$ cell by its aligned corner. For each $Q$ above, take a spanning tree of its coarse-cell graph; realize each tree edge by an $a$-bond fine path through the two adjacent cells. Cost: $|Q|-1$. Its corner vertices meet the new boxes $B_q$. If $X_f\cap\Omega_-\ne\varnothing$, connectedness of the cell union $X_f$ gives adjacent cells $q\in Q$, $p\in X\cap\Omega_k^{pre}$. An old chosen box covers $p$, and $W_-$ meets it at $w$. Connect $w$ to the corner of $p$ inside that side-$La$ box in fewer than $dLa$ bonds; connect this corner to $q$ in $a$ bonds. Thus $Q$ costs at most $|Q|+dL$ after division by $a$. If $X_f\cap\Omega_-=\varnothing$, connectedness puts all $X_f$ in one raw-hole component $Q$; connect any old vertex $w\in W_-$ to its cell corner within that cell at cost at most $d$, then use the same spanning tree. The cost is at most $|Q|-1+d$. Every path lies in $X_f$. Union with the old graph remains ConnStruct; bondCost_union_le (Localization/TreeLength.lean) bounds cost. Since the $Q$ are disjoint and cover $A_X$,
$$\boxed{D_+\le D_-+(dL+d+3)|A_X|.}\tag{3}$$
The slack covers corner choices and the empty-old-active case. A removed component may be far from a chosen old vertex, but its adjacent active cell has an old chosen box, hence an old vertex within $dL$ cell units. If old active islands connect through a removed component, the old graph already connected their boxes; the new branches preserve connectivity.

**PROVED CONDITIONAL ON PROVED cited geometry.** RegionHistory.Admissible makes each removed $c$ ripe. Under the stated Good and thickness premises, RegionHistory.ripe_window (History/RipeWindow.lean:111) and RipeWindow.lin_eq_box (R/RipeBox.lean:87) make $c$ one box of side at most $\operatorname{crit}_k=2\rho_k+10$; ncard_box_le (R/ChainCount.lean:61) yields $|c|\le\operatorname{crit}_k^d$. From (2)–(3),
$$D_+\le D_-+(dL+d+3)\sum_{c\in\mathscr C_R(X)}|c|
 \le D_-+\underbrace{(dL+d+3)}_{C_{d,L}}
 \sum_{c\in\mathscr C_R(X)}(\operatorname{crit}_k+2L)^d.\tag{4}$$
Here $\mathscr C_R(X)=\{c\in\mathrm{Rem}_k:c_f\cap X_f\ne\varnothing\}$. Hence VMOD-37 (2) is **PROVED mathematically**, conditional only on **PROVED cited** component geometry, for each finite post label. Its Lean implementation is **OPEN**. The volume bound alone would not establish (3).

**PROVED rate arithmetic; analytic charge OPEN.** The slope in (3) is one, so the old $3\kappa/2$ rate keeps its $\kappa/2$ margin. If an allocated factor $e^{-g_c}$ for each used removed component has $g_c\ge\kappa(dL+d+3)|c|$ plus separate gas/fiber costs, the product pays $e^{-\kappa(D_+-D_-)}$ in VMOD-37 (3). P7 (3.10) has a removed-operator reserve, but its assignment to the actual H7 coefficient and other costs remains OPEN-R-D7-CHARGE.

## 3. Endpoint $k_0$

**PROVED source comparison; REFUTED literal P7 endpoint sentence.** P5 Theorem 2, printed p. 499, applies $R^{(j+1)}$ for $j<k_0$, hence includes $R^{(k_0)}$ at $j=k_0-1$. P7 Theorem 5, printed p. 497, repeats this composition. On the same page P7 Theorem 2 says $R^{(k)}$ for $k<k_0$ and identity for $k\ge k_0$; this conflicts at $k=k_0$ with both formulas after its stated $k+1\mapsto k$ reindexing. Its detailed discussion also says “$k\le k_0$ considered here” (P7 printed p. 501). The consistent induction is nontrivial $R^{(k)}$ for $1\le k\le k_0$, identity for $k>k_0$. Landed RegionHistory.rem_empty, $(k=0\lor k_0<k)\Rightarrow\mathrm{rem}\,k=\varnothing$, and the IsRepPre2-to-IsRep2 class indexing already follow this convention; **no landed declaration changes**. At $k>k_0$ use the flat-class branch, not an unrestricted IsRep2 budget theorem.

## 4. Lean packages in dependency order

Each package is at most 300 new lines. Packages 1–5 are pure geometry and can start now.

1. **140–230 lines, RRawHoleComponent.** State for $1\le k\le K$: if $Q$ is a nearest-neighbor component of $X\cap(\operatorname{OmegaCube} A.H k)^c$ and meets $c\in A.H.\mathrm{rem}\,k$, then $Q\subset c$. Reuse Omega_compl_subset_Z0, Z0_subset_Zpre, comp_eq_of_mem and the cell correspondence.
2. **160–250 lines, RCellPath.** State: adjacent aligned side-$a$ cells admit an $a$-bond path in their union; any site in an aligned side-$La$ box reaches a selected cell corner in at most $dLa$ bonds. Reuse Localization/TreeLength.lean path lemmas and ConnStruct.union.
3. **230–300 lines, RModAdmissibleExtend.** State for $\Omega_-=d7Pull\,F\,k\,(\operatorname{OmegaCube} A.H k)$, $\Omega_+=d7Pull\,F\,k\,(A.H.\operatorname{omegaPost} k)$, $X_f=d7Pull\,F\,k\,X$, and $A_X$ in (2): if $h:\mathrm{ModAdmissible}\ m_0\ k\ \Omega_-\ X_f\ \mathcal K\ W\ E$, IsDj $m_0\,k\,X_f$, and the raw-hole component conclusion of package 1 holds, then there are $\mathcal K',W',E'$ with ModAdmissible $m_0\,k\,\Omega_+\,X_f\,\mathcal K'\,W'\,E'$ and $\mathrm{bondCost}(\mathrm{scaleW}\,L\,m_0\,m_1\,k,E')\le\mathrm{bondCost}(\mathrm{scaleW}\,L\,m_0\,m_1\,k,E)+(dL+d+3)|A_X|$. Include the frame's cell-lift and divisibility hypotheses; use packages 1–2 and bondCost_union_le.
4. **100–180 lines, RExtraSize.** State under FineValid $F\,A\,k\,X$, $1\le k\le k_0$, $k\le K$, and the hypotheses of package 3:
$$d7Size(F,A,k,X)\le d7SizePre(F,A,k,X)+(S.d\,S.L+S.d+3)
  |X\cap(\mathrm{removedSet}_k\setminus\operatorname{OmegaCube}(A.H,k))|.$$
Use exists_admissible_eq_dcovMod, package 3, dcovMod_le_of_admissible and d7Pull.
5. **100–160 lines, RRipeCardAndCharge.** State $|c|\le(S.\mathrm{crit}\,k)^{S.d}$ for removed ripe $c$, using ripe_window, lin_eq_box, ncard_box_le; combine package 4 with the finite component union bound to obtain (4).
6. **50–90 lines, REndpointIndex.** Prove $j<k_0\iff j+1\le k_0$ and the no-removal identity for $k>k_0$ from RegionHistory.rem_empty and omegaPost_eq_OmegaCube_of_rem_empty. No declaration change is proposed.
