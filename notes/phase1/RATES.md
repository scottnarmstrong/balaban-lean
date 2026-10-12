# Decay rates in one fluctuation step

**Scope and status.** This audits the present FLUCTUATION.md rate construction using the explicit support conversion of HAT-RATE.md §1. **PROVED** below means an elementary consequence of displayed bounds. The geometry is proved mathematically in HAT-RATE.md but has no landed Lean declaration. The physical activity, complex domains, and cover premises remain **OPEN**.

## 1. The one-step inequality

Write $\kappa_{\rm in}>0$ for the input class rate and $\kappa_{\rm dec}$ for the decoupling rate. The combined output of Fluctuation/InteractionHatAssemble.lean, theorem interaction_expansion_hat_bound, has
$$\kappa_U=2\kappa_{\rm dec}-1. \tag{1}$$
Its old energy and observable premises hEbdE, hEbdM require bounds at rate $\kappa_{\rm dec}-1$ in treeLenCovOne. The input SmallField/Def6.lean SFTermClauses.boundE and .boundM, and Def6v2.lean, use $e^{-\kappa_{\rm in}\operatorname{sizeJ}}$; Def6Terms.lean defines sizeJ to be treeLenCovOne. For arbitrary old terms fed directly from this class, the required implication holds uniformly in support only if
$$\boxed{\kappa_{\rm dec}-1\le\kappa_{\rm in}}. \tag{2}$$
The *actual termwise I-6 route* is stricter: SmallField/RenormTermwiseIrrel.lean theorem termwise_irrelevant_all_scales produces $e^{-(\kappa_{\rm in}-1)d_j(X)}$ (FLUCTUATION.md Lemma 3.2 (iii), with its OPEN physical premises). Its bounded star enlargement changes only the amplitude. Feeding that output into the old-energy I-5 premise at $\kappa_{\rm dec}-1$ requires $\kappa_{\rm dec}\le\kappa_{\rm in}$. We retain (2), the more generous direct-class restriction, to make the obstruction independent of that additional one-unit loss. The input-domain inclusion and amplitude comparison remain separate **OPEN** premises. A special family might have faster decay; Def-6/H7 does not guarantee it.

Put $c_1=[3(2L-1)]^d$, $r=\lceil(L^{k+1}+1)/L^{k+1+m_0+m_1}\rceil\le2$, and
$$H=2L+2r+3,\quad A:=a_+=c_1H^d,\quad b_+=A,\quad F:=c_1\log2.$$
For the actual row-5a choice $m_0\ge1$, $r=1$, so $A=c_1(2L+5)^d$. The uniform choice $c_1(2L+7)^d$ also works. HAT-RATE.md (1.3)–(1.5) gives, after aggregating original supports by enlarged hat support, the certified activity rate
$$\kappa_H\le\frac{2\kappa_{\rm dec}-1}{A}-F,\qquad
C_+=2^{c_1}e^{(2\kappa_{\rm dec}-1)b_+/A}. \tag{3}$$
This is the largest rate certified by that cell-count argument, not an upper bound on the decay of every possible physical expansion. The support conversion is **PROVED** mathematically in HAT-RATE.md; its Lean implementation and the physical activity are **OPEN**.

Let $D=3\kappa_0+c_1+\frac32$. StepActivityBound.hκ, InterpMarks.hκ and ObsMarks.hκ require $\kappa_H\ge\kappa'+D$. Thm31b.thm31b_of_input requires observable rate $\kappa_b\le\min(\kappa_h,\kappa')-\kappa_0-1$. Even with $\kappa_h\ge\kappa'$, the largest certified rate shared by new energy and observable terms obeys
$$
\kappa_{\rm out}^{\rm cert}\le
\frac{2\kappa_{\rm dec}-1}{A}-F-D-\kappa_0-1
\le\frac{2\kappa_{\rm in}+1}{A}-B,\quad
B:=F+D+\kappa_0+1=c_1\log2+4\kappa_0+c_1+\frac52. \tag{4}
$$
The old terms retain at most the input class rate, so the next class rate is bounded by the minimum of $\kappa_{\rm in}$ and (4). For $d\ge3,L\ge3$, $A>2$ and $AB>1$. Hence
$$
\kappa_{\rm out}^{\rm cert}-\kappa_{\rm in}
\le-\left(1-\frac2A\right)\kappa_{\rm in}
-\left(B-\frac1A\right)<0. \tag{5}
$$
This strict loss is **PROVED** for every positive input rate under the present conversion. Iterating its certificate gives $\kappa_{n+1}\le(2/A)\kappa_n+1/A-B$, a fixed-factor contraction with negative additive drift; it becomes nonpositive after finitely many steps. The stronger new-term requirement of FLUCTUATION.md §3.7, $\kappa_b\ge\frac32\kappa_{\rm in}$, would require
$$2\kappa_{\rm in}+1\ge A\left(\frac32\kappa_{\rm in}+B\right), \tag{6}$$
which is impossible for $A>2$, $AB>1$.

With the actual termwise route, replace the final numerator $2\kappa_{\rm in}+1$ in (4) and (6) by $2\kappa_{\rm in}-1$. Thus (4) is a deliberately optimistic upper certificate; the exact rate inequality supplied by that route is $\kappa_{\rm out}^{\rm cert}\le(2\kappa_{\rm in}-1)/A-B$ under its stated physical premises. It strengthens (5).

**Rescaling.** FLUCTUATION.md §5.2 Step 4 states the pre-rescaling bound in $d^{\rm cov}_{k+1}$; Steps 5 and 8 use the *same numerical rate* in the new scale-$k+1$ class. The landed Def6Terms.sizeJ and Localization/TreeLength.scaleW normalize bond length by $L^{j+m_0+m_1}$. A coordinate contraction by $1/L$ alone is not a theorem multiplying this normalized exponent by $L$; no such rate-transport declaration occurs in the cited consumers. Thus (4) has no extra $L$. Even if one granted the more favourable **hypothetical** bound $\kappa_{\rm out}\le L[(2\kappa_{\rm in}+1)/A-B]$, closure would require $(A-2L)\kappa_{\rm in}\le L(1-AB)$, impossible since $A>2L$ and $AB>1$. This check does not assert that the hypothetical gain exists.

At $d=L=3$, $m_0\ge1$, one has $c_1=3375$ and $A=3375\cdot11^3=4{,}492{,}125>2L$. Larger $L$ preserves the obstruction. Consequently **no numerical choice closes the full class-to-class chain with (2)–(3)**, including for $d=3$ and all sufficiently large $L$.

An *additive* enlargement bound $d(Y^+)\le d(Y)+b_+$ would change (3) to $\kappa_H\le2\kappa_{\rm dec}-1-F$, with $b_+$ entering only the amplitude. Even using the actual termwise restriction $\kappa_{\rm dec}=\kappa_{\rm in}$, the choices $\kappa'=\frac32\kappa_{\rm in}+\kappa_0+1$ and $\kappa_H=\kappa'+D$ would satisfy the rate inequalities if $\kappa_{\rm in}\ge2(F+D+\kappa_0+2)$, together with the independent lower bounds $\kappa_{\rm dec}\ge3\kappa_0+3$ and $\kappa'\ge\kappa_0$. **OPEN-ADDITIVE-HAT-GEOMETRY:** no uniform additive estimate for the canonical $Y^+$ has been established. Local thickening of a long support may add a transverse covering burden along its length. The current definition must therefore change or be supplemented by a stronger theorem: define decoupled labels on the hat-dependent enlarged supports at construction and prove decay in *their* covering size sufficient for (6), or prove a support conversion with a coefficient small enough to close the rate. Renaming old labels does not strengthen (2).

## 2. Landed numerical consumers

Here $\kappa_{\rm AE}$ denotes the decoupling-polydisc exponent, $\kappa_{\rm tr}$ the separate trace-decoupling rate of Theorem 4.2, and $\kappa'_{\rm tr}$ its output. They are distinct from $\kappa_{\rm in}$. Each landed theorem is **PROVED CONDITIONAL ON its stated structures and nonnumerical hypotheses**; this table lists the rate fields relevant to the chain.

| Consumer | Exact numerical requirements relevant here | Joint rate decision |
|---|---|---|
| Polymer/MarkedCubes.lean LabelAct, numerics_PE | LabelAct needs $\varepsilon_He^{-\kappa_H\mathsf d}$ and entropy $K_c$. numerics_PE takes $\varepsilon_H>0$, $K_c\ge1$, $c_1\ge1$, $c_G\ge0$, $\kappa'\ge0$, $\kappa_H-2\kappa_0\ge0$, and $\varepsilon_H\le[8K_c^3c_1e^{(\kappa_H-2\kappa_0)c_G+c_1+\kappa'c_G}]^{-1}$. Its conclusions supply hq, hα and $H_0\le\log2$. | Satisfiable for fixed rates by sufficiently small $\varepsilon_H$; the physical amplitude includes $C_+$. |
| StepNonvanishBound.lean StepActivityBound; Thm31cde.lean InterpMarks; Thm31a.lean E1Marks | $\kappa_0\ge a_{\rm ent}+1$, $K_c\ge K_0(d,L,\kappa_0)+1$, $\varepsilon_H>0$, $\kappa'\ge0$, $\kappa_G\ge\kappa_H$, $\kappa_H\ge\kappa'+D$, and the preceding $\varepsilon_H$ bound. E1Marks abbreviates InterpMarks. | Internally satisfiable; with (2)–(3) it forces (4). |
| Thm31b.lean ObsMarks and thm31b_of_input; Thm31a.lean thm31a_of_input | ObsMarks adds $\kappa_0\le\kappa'$, $\kappa_h\ge\kappa_0$; output $\kappa_b\le\min(\kappa_h,\kappa')-\kappa_0-1$. The energy/determinant combination asks $\kappa_{\rm det}\ge\kappa'$. Thm31cde uses the InterpMarks rate fields. | Internally satisfiable with $\kappa_h,\kappa_{\rm det}\ge\kappa'$. The observable output is the bottleneck in (4). The two-mark argument in FLUCTUATION.md §3.4 reserves $\varepsilon_H\le\varepsilon_{\rm PE}/4$. |
| InteractionHatAssemble.lean interaction_expansion_hat_bound; InteractionHatE.lean; Prop33 wrappers | $\kappa_{\rm dec}\ge3\kappa_0+3$, $\kappa_{\rm AE}\ge4d(2L+1)^d\kappa_{\rm dec}$, $1\le(\kappa_{\rm AE}/2-1)/2$, and $\log(((2L+1)^d)(L^{m_0})^d)\le(\kappa_{\rm AE}/2-1)/2$. Old terms enter at $\kappa_{\rm dec}-1$; combined output is $2\kappa_{\rm dec}-1$. The landed termwise I-6 output is $\kappa_{\rm in}-1$, requiring $\kappa_{\rm dec}\le\kappa_{\rm in}$ on that route. | The AE inequalities are satisfiable by increasing $\kappa_{\rm AE}$, then $m_1$. Even the weaker direct-class comparison (2) conflicts with marked output closure after (3). |
| Theorem42.lean theorem42_of_input and theorem42_late_of_input; Theorem42RealVolume.lean | $\kappa_{\rm tr}\ge3$, $\kappa_{\rm AE}\ge4d(2L+1)^d\kappa_{\rm tr}$, the same $1$ and log inequalities, $\kappa'_{\rm tr}\ge0$, $a_{\rm Multi}+2\le2\kappa_{\rm tr}-\kappa'_{\rm tr}$. The late bound adds $\kappa'_{\rm tr}\ge3\kappa_{\rm tr}/2$ and its separate amplitude inequality $(\Lambda28')$. The empty-trace bound uses $a_{\rm Multi}+1\le2\kappa_{\rm tr}$. | Choose $\kappa_{\rm tr}\ge\max\{3,2a_{\rm Multi}+4\}$, $\kappa'_{\rm tr}=3\kappa_{\rm tr}/2$, then large $\kappa_{\rm AE}$. The rate fields are compatible; the late response/amplitude is conditional. |
| SmallField/Def6.lean and Def6v2.lean | Consts.κ is one positive class rate. Energy and observable clauses use $e^{-\kappa\operatorname{sizeJ}}$ at each old scale. | No hidden decay reserve. Class preservation fails by (5) with the present conversion. |

The numerical fields *without* the class-to-old-term implication have witnesses. Fix $d=3$ and any $L\ge3$ satisfying the other geometric thresholds; take $\kappa_0\ge\max\{a_{\rm ent}+1,c_1\}$, $K_c=K_0+1$, and
$$
\kappa_{\rm in}=\max\{3\kappa_0+3,\,2a_{\rm Multi}+4,\,7+8\kappa_0+2c_1\}+10,\quad
\kappa_{\rm tr}=\kappa_{\rm in},\quad \kappa'_{\rm tr}=\tfrac32\kappa_{\rm tr},
$$
$$
\kappa'=\tfrac32\kappa_{\rm in}+\kappa_0+1,\quad
\kappa_H=\kappa'+D,\quad \kappa_G=\kappa_h=\kappa_{\rm det}=\kappa_H,\quad
\kappa_{\rm dec}=\tfrac12+\tfrac A2(\kappa_H+F).
$$
Choose $\kappa_{\rm AE}$ above $4d(2L+1)^d\max(\kappa_{\rm dec},\kappa_{\rm tr})$, $6$, and $4\log(((2L+1)^d)(L^{m_0})^d)+2$, and $0<\varepsilon_H\le\varepsilon_{\rm PE}/4$. The trace and marked arithmetic then hold, but $\kappa_{\rm dec}-1>\kappa_{\rm in}$, so this is **not** an induction witness. The physical $\varepsilon_H$ inequality also needs the final $\beta$ reduction and remains **OPEN** until an activity family is constructed.

## 3. Replacement text for FLUCTUATION.md §§1.5 and 3.5

The following proposed replacement is less than one manuscript page. It has not been inserted into FLUCTUATION.md.

> **§1.5, row 5 onward [rate correction].** After $L,c_1,a_{\rm ent}$, choose $\kappa_0\ge a_{\rm ent}+1$ and $K_c\ge K_0(d,L,\kappa_0)+1$. Denote the class rate by $\kappa_{\rm in}$, the decoupling rate by $\kappa_{\rm dec}$, the activity rate by $\kappa_H$, and the cluster output rate by $\kappa'$. The old-term class gives $\kappa_{\rm dec}-1\le\kappa_{\rm in}$ directly; the termwise I-6 input actually used requires $\kappa_{\rm dec}\le\kappa_{\rm in}$. For the canonical hat-support conversion put $A=c_1(2L+2r+3)^d$, $F=c_1\log2$. Before the marked expansion one must have $\kappa_H\le(2\kappa_{\rm dec}-1)/A-F$, whereas the marked theorem needs $\kappa_H\ge\kappa'+3\kappa_0+c_1+\frac32$. The observable output rate is at most $\kappa'-\kappa_0-1$. These inequalities have no choice preserving a positive class rate. Thus rows 5–6 and the later $\beta_*(\alpha_0,E_0)$ do not constitute a completed induction. Once a replacement support/rate theorem is proved, choose its rate constants before $\kappa_{\rm AE}$ and $m_1$, then $\alpha_0,E_0$, and finally $\beta_*(\alpha_0,E_0)$.
>
> **§3.5, after Proposition 3.3 [hat activity status].** Proposition 3.3 yields terms at rate $2\kappa_{\rm dec}-1$ on their original supports. The hat field reads blockThick $Y$, so form $Y^+$ from all aligned cubes of side $La$, $a=L^{k+1+m_0+m_1}$, meeting it and combine every original term with the same $Y^+$. The proved support/fiber bounds give $d(Y^+)\le A d(Y)+A$ and $\kappa_H\le(2\kappa_{\rm dec}-1)/A-c_1\log2$, with amplitude $2^{c_1}e^{2\kappa_{\rm dec}-1}\varepsilon_U$. LabelAct and InterpMarks remain conditional on the open complex activity and cover inputs. These bounds imply the strict rate loss (5); Theorem 3.1(a)–(e) can be applied to the induction only after a new support/rate theorem supplies class preservation. The previous choice $\kappa_H=2\kappa_{\rm dec}-1$ is invalid.

## 4. Lean targets and disposition

1. **Geometry: OPEN in Lean; mathematically PROVED in HAT-RATE.md §1.** Targets hatSupportPlus_isDj, blockThick_subset_hatSupportPlus, hatSupportPlus_cov_le with $A,b_+$, and hatSupportPlus_fiber_exp_le with $2^{c_1}e^{\kappa_Ub_+/A}$. Derive $n_a(Y^+)\le H^dn_a(Y)$, use a cell spanning tree for $d(Y^+)\le n_a(Y^+)$ and landed G1_cellCount, then count subsets of cells of $Z$ for the fiber. Aggregate by distinct supports and use landed G2_X for entropy. OPEN-ADDITIVE-HAT-GEOMETRY is a distinct, stronger target.
2. **Arithmetic: mathematically PROVED; OPEN as Lean declaration.** The requested stepRates_consistent *with positive-class preservation witnesses* is false under (2)–(3). Formalize stepRates_no_closure: define $D=3\kappa_0+c_1+3/2$ and $B=F+D+\kappa_0+1$; for $A>2$, $B>1/A$, $\kappa_{\rm in}>0$, premises $\kappa_{\rm dec}-1\le\kappa_{\rm in}$, $\kappa_H\le(2\kappa_{\rm dec}-1)/A-F$, $\kappa_H\ge\kappa'+D$, $\kappa_{\rm out}\le\kappa'-\kappa_0-1$ imply $\kappa_{\rm out}<\kappa_{\rm in}$. The derivation is (4)–(5). A positive stepRates_consistent with witnesses becomes a valid target only **CONDITIONAL ON a named new support/rate theorem** replacing (3); the additive conditional witness is displayed after (6).

**Overall:** The landed abstract results are **PROVED CONDITIONAL ON their explicit inputs**. The present certified rate induction is **PROVED impossible**. A physical support/rate construction restoring class closure is **OPEN**.
