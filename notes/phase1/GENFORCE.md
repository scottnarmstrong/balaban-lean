# GENFORCE: can whole-torus term generators survive the full step?

13 October 2026. `/home/scott/Balaban` was read only. **PROVED** cites a landed declaration or proves the stated deduction; **PROVED CONDITIONAL ON** lists the needed extra input; **OPEN** means no such proof is supplied; **REFUTED** identifies a false implication. `GENERATOR.md` in `notes/phase1` was read in full before the definitions below.

## 1. Generator uses and the verdict for (G)

**PROVED (formal admissibility).** `SmallField/Def6Terms.lean`, `levelGS j`, has `Ω_i=univ` for `i≤j`; hence `dataSites(levelGS j)=univ` for `j≥1`. `GsSpecDef.levelGS_strong` lets `Tm.gs j X=levelGS j` satisfy the landed `IsSF2.gsStrong` for every polymer. This is a class witness, not a full-step preservation theorem.

**OPEN (a: old-term analytic chart).** `SmallField/Def6v2.lean`, `SFTermClauses.analyticE/analyticM`, requires a term on `X` to be analytic on `Dom.dom j (Tm.gs j X)`, and its bounds have the same domain. For (G), every complex old-step path `P_{j,D}(s,x)=composedPairAtC(S.a,S.ν,j,dataUC(psiAtCc(s,x)))`, including an open neighbourhood of each
Cauchy contour, must lie in `XiDom(levelGS j,S.a,S.ν,j,ε_j)` after the exact `GENERAL-PARAM-MATCH` identifications of `GENERAL.md` §1. At output scale `K`, the image of the new physical chart must likewise lie in the global `XiDom(levelGS K)` with strict radius slack. The landed `InUnionDomainC`/`XiCData` for the step parent and the relative
openness of `XiCRaw` in `rawSub` do not imply these whole-torus inclusions (`ParamActivitySubspace.isOpen_physV` is relative).

**PROVED compatible at the formal clause; OPEN for physical output (b).** `SFTermClauses.localE/localM` requires equality for **all** field pairs that agree on `X`, independent of `Tm.gs`. Thus (G) does not itself prevent sharp locality. The constructed marked, determinant and old-composite coefficients still have to satisfy this all-field clause;
`PhysicalSharpLoc` on admissible data is weaker (`OUTPUT.md` §4). The permitted read sites of a term on `X` are precisely `X` for `Ψ,h,g` in the landed class, while the analytic-domain tests may use all of `dataSites(levelGS j)`.

**REFUTED (c: direct regional-domain implication).** `LargeField/Def7SmallField.lean`, `C.EresJ` and `C.MresJ`, evaluate inherited total functions at `C.psiJ Y ψk hv j` for `X⊆C.sset(thickY R Y)`. `C.psiJ` is the pullback of `psiSF j (W2 R Y)`; `psiSF` uses the *local* `G_j=genSF j (W2 R Y)`. `Background/Composition.composeField_of_not_mem` says
this field is zero at every site outside `dataSites G_j`. Fix `1≤j≤k` and a site `x∉dataSites G_j` on a torus where at least one inherited summand is present. Then `C.psiJ(x)=0`, whereas `x∈dataSites(levelGS j)`, so the field is outside `XiDom(levelGS j)` by the lemma in §2. The functions are still evaluated because `Terms.E/M` are total; their
**global-domain class bounds and analyticity cannot be applied at this argument**.

**PROVED (source requirement); OPEN (global replacement).** P5 p. 489 (1.4), (1.8), pp. 496–497 (1.33), (1.36)–(1.39) uses the regional background `B_k(W_k)`, inherited polymers restricted to the regular region and boundary terms `B^{(k)}(X)` on the layerwise domain `D^c(X,B_k;{ε_j})`. P6 (4.32) re-expands those boundary terms, including their
reads in `X∩Ω_{k+1}^c`. A global `gs` supplies no estimate on a regional datum with a zero outside the local generator. A termwise good global extension, equality with the regional evaluation by `localE/M`, uniform analytic sections and matching boundary terms could replace direct evaluation; no such theorem is landed. P5's boundary domain is not
`XiDom(levelGS j)`.

**OPEN (d: torus agreement).** `SmallField/Def6.lean`, `TorusIndep.E_eq`, separately requires values for each non-winding `X'` to agree on two tori for every pulled-back infinite field. A whole-torus generator alone neither contradicts nor proves that equality: zero terms satisfy it, while an output built from a whole-torus Green function may
retain volume dependence. A physical (G) output needs a termwise torus comparison or a local reconstruction proving the equality; the formal `TorusIndep` field does not provide its producer.

**OPEN (e: volume-uniform constants).** The formal `boundE/boundM` fields impose one volume-independent amplitude and rate on the global domain. To use them in a history, one needs either the false direct inclusion in (c), or a global extension with strict bounds uniform in torus size and history, plus a volume-independent rooted activity and
boundary count. `Q13-TRANSFER.md` §2 refutes the proposed nearby-factor cover from `gsStrong`: a tiny `X` with `gs=levelGS j` has whole-torus data sites. A new nonlocal estimate is conceivable but not proved. The subsequent P7 `R` step inherits the same regional-domain, locality, torus and constant requirements; no physical `R` preservation theorem
closes them (`PATHAUDIT.md` §§1–2).

## 2. An exact, formalizable failure of the direct (G) route

**PROVED (zero exclusion).** Let `0<d`, `G` be any generator, `x∈dataSites G`, `j≥1`, and assume `InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν Dc`. If `Dc.Ψ(x,i)=0` for every `i`, unpack `InDomainC` as `Dc.Ψ=Ψ+Ψ'` on `dataSites G`. Put `q=Σ_i Ψ(x,i)^2≥0`. `InPsiTilde.r2` gives `|q-1|<δ`; `InPsiTildeC.c2b` gives `|0-q|<δ`. Hence `1≤|1-q|+|q|<2δ≤2 bgC1≤2
bgC0≤1/8`, impossible. The last two inequalities are `ExistenceSetup.bgC1_le_bgC0` and `bgC0_le`. Thus **every** datum in this union domain has a nonzero spin vector on each data site.

**PROVED (global-chart exclusion).** `SmallField/Xi.XiC` contains an `InUnionDomainC` complex datum realizing its input field on `dataSites G`; `Def6Terms.XiDom` is the field form of this assertion. Since `levelGS j` contains every site, any field with one zero spin vector fails `XiDom(levelGS j, a,ν,j,ε)` for every `a,ν,ε`. This uses no assertion
about whether the regional real field elsewhere is large or small.

**PROVED CONDITIONAL ON a proper local support and a present inherited term.** Choose `Y` with a nonempty regular component and a sufficiently wide excluded region so that `G_j=genSF j(W2 R Y)` has `x∉dataSites G_j`, and choose `X` among the nonempty summands of `EresJ` or `MresJ`. `composeField_of_not_mem`, `sfPull` and the preceding lemma give
`¬XiDom(levelGS j, …, C.psiJ Y ψk hv j, constFld(hv))`, for **every** `ψk,hv`. The two geometric premises must be exhibited for a concrete `RegionHistory`; they are not consequences of merely `Y^c≠∅`.

**REFUTED.** “Every nonempty large-field region makes the global domain empty” is too strong. The halo `W2 R Y` may cover the torus when the excluded region is small; then the zero-off-support argument has no site `x`. The domain `XiDom(levelGS j)` itself is not made empty by a history: it contains, for example, suitably admissible constant unit
fields under the standard mass/radius hypotheses. The proven failure concerns the **particular regional composed datum** on a proper local generator, not every datum or every history.

**REFUTED as an inference from the landed class; OPEN as a different scheme.** `IsSF2` with (G), `IsRep2.sfData : D2SF2`, and `SFCtx.EresJ/MresJ` contain no lemma mapping each regional `psiJ` into the global term domain. The explicit zero obstruction shows such a universal mapping is false. It does **not** prove that all conceivable
global-generator schemes fail: `localE/M` permits replacing a regional field outside `X` by a good global extension if one constructs it, and P3-style rebuilding could create a local family before the large-field step. Both repairs require new local-domain and equality theorems, so neither is a consequence of the existing (G) class.

**OPEN (Lean refutation package, ≤300 lines).** Prove `no_zero_on_dataSites_of_inUnionDomainC` from `InPsiTilde.r2`, `InPsiTildeC.c2b`, `bgC1_le_bgC0`, `bgC0_le`; then `not_xiDom_level_of_zero`; then `regional_psiJ_not_globalXiDom` under explicit `x∉dataSites(genSF j(W2 R Y))`, `1≤j≤k`, and the torus transport of `sfPull`. The final conclusion is
only `¬XiDom(levelGS j, …, C.psiJ …, constFld(hv))`. This would formally refute the direct-domain bridge without claiming that (G) is mathematically impossible.

## 3. The same five uses for (L)

**PROVED source pattern; OPEN physical clause (a).** P3 pp. 78–79 (4.46)–(4.47) assigns `B_K(Y)` to the output polymer, replaces the generator in the pre-resummation formula, and proves its analytic estimate on `Xi^c(B_K(Y))`. The landed `MinimalGenSet.minimalGenSet` models aligned full-level top polymers; `LOCALGEN.md` §1 records the still open
mixed-level recurrence. The old-step image must lie in `XiDom(B_j(X),S.a,S.ν,j,ε_j)` with an open chart neighbourhood and strict radius. `CanonicalPrecedes`, local comparison of composed fields, old-term radius rescaling, and the local chart `G_p[Y]` are OPEN (`GENERAL.md` §1; `CHART.md` §3). There is no contradiction for (L).

**PROVED compatible; OPEN physical output (b).** The same all-field `localE/M` clauses apply. A canonical `B_j(X)` must retain the top and lower-layer parts of `X`, and its collar may extend beyond `X`; those extra sites are **domain tests**, while the coefficient's field reads remain in `X`. The physical marked and determinant families still need
all-field sharp locality and a rooted support certificate (`OUTPUT.md` §4; `MARKASM.md` §§1–2). `PhysicalSharpLoc` alone does not fill this clause.

**PROVED geometry in the full-level case; OPEN transfer (c).** `LOCALGEN.md` §3 derives `dataSites(B_j(X))⊆{z:dist∞(z,X)≤11M₁L^j+1}` from `MinimalGenSet.exists_near_of_mem_minLayer` and collar adjacency, and proves its placement inside the second halo under the explicit inequality (3.3). Mixed-level transport, assignment of each site and collar
bond to an active history factor (`collarInterfaceCover`), and same-datum R1/R2 margins (`referenceR12Margin`) remain OPEN (`Q13-TRANSFER.md`). P5 H7 and P6 (4.32) still require the separate boundary-domain and operator estimates. `LOCALGEN.md` §2 refutes using the narrow P3 generator as the **parent** `Gp` of the present `I5Fan.BgSetting` without
a new geometry theorem; it does not refute (L) as the term's **child** generator `Gj` or as a different output engine.

**OPEN (d, e).** Prove that the canonical generator, local comparison, coefficient formula and root choice commute with paving symmetries and non-winding torus lifts, then establish `TorusIndep.E_eq`. Prove uniform local-domain Cauchy bounds, collar and rooted entropy, old-block counts, boundary H7 constants and post-`R` transfer with constants
independent of torus volume. The local support removes the whole-torus counterexample to nearby-factor assignment, but does not prove the factor and reference estimates. No item (a)–(e) has been refuted for (L).

## 4. Decision and first Lean packages

**OPEN (decision).** The evidence does not force (L) as the only conceivable induction. It **does** refute using the landed (G) analytic/bound clause directly at every regional argument. (G) could survive only with an additional good-extension/local-rebuilding theorem that carries essentially the local chart, support and equality work. (L) is
therefore the recommended main class, as in P3 and P5; (M) buys no proved shortcut. The author still has to choose between strengthening `IsSF2` to (L) and retaining (G) with an explicit second local inherited-term class. The formal refutation target is the three-declaration chain in §2, not a false theorem that every global-generator class fails.

**OPEN (first five Lean packages, each ≤300 lines; one main theorem per package, in dependency order).**

1. `OldEnergyHatLocalValue`: for a finite old label `(j,y,X)`, parent `S.G'`, middle `stepG`, child `Gj=B_j(X)` with `BgSetting`/`FlSetting`, prove `hatFun(flComp(β⁻¹ E_j(y,X)))` at the physical hat input equals `β⁻¹ E_j(y,X)` at the **local** `composeData Gj` pair. Use `hatFun_rawOf`, `flComp_rawOf` and the real-chart identity; do not claim equality with the global `composedPairAt` yet. Generator choice: dependent on (L).
2. `LocalGenBirth`: for a birth-level `j` polymer `X` that is a union of aligned `j`-cubes, construct `B_j(X)` from `MinimalGenSet.minimalGenSet`; prove its top layer contains `X`, its layer index is `j` on `X`, `Precedes B_j(X) (stepG k)`, and the collar inclusion required by `BgSetting`. The mixed-level output generator needs a later, separate package. Generator choice: dependent on (L).
3. `CanonicalPrecedesLocalCompare`: at each `x∈X` for the **birth-level** generator of package 2, prove equality of the local `composeData B_j(X)` field and the `levelGS j` `composedPairAt` field, including `h`, on the same real/complex step datum. Use `Background/Composition.composeField_of_mem`, identical `j`-blocks and layer index `j` on `X`; require equality of the parent solutions on the relevant blocks if they were obtained from different charts. This equality is not asserted for lower-layer sites of a mixed output polymer. Generator choice: dependent on (L).
4. `OldEnergyHatMatchLocal`: index the finite family by all participating `(j,y,X)`; set `EE_{j,y,X}=β⁻¹ E_j(y,X)`. Apply packages 1 and 3, `SFTermClauses.localE`, and finite reindexing to prove the exact `OldEnergyHatMatch` equality, including the subtraction at hat input zero. Supply `hBE/hFE` for each label, not just an existential family. Generator choice: dependent on (L).
5. `OldObsHatMatchLocal`: repeat the value and comparison argument for `(j,x,X,i)` and `M_j(x,X)_i`, use `localM`, retain the source factor `g(x,i)/β`, and prove the exact `OldObsHatMatch` equality after the outer `β` cancels. Packages 2–3 and the local `hBM/hFM` are inputs. Generator choice: dependent on (L).

**OPEN after package 5.** Prove the common open local `XiDom` chart and strict radii, then the marked/determinant sharp output, P5 history margins, H7 boundary transfer and physical `R` preservation. The five packages above do not by themselves close the full induction.
