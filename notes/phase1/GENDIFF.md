# Generator choice: source-level impact at current main

This is an inventory of the landed Lean surface, not a proof of a new generator bridge. Paths below are relative to `/home/scott/Balaban/`; that tree was read only. “Agnostic” means the declaration is parameterized by a generating set or terms and does not assert that the set is local. “Whole” and “local” identify a generator fixed by the declaration.

## Where the generator enters

| Landed file and declarations | Role | Kind |
| --- | --- | --- |
| `Balaban/SmallField/Def6.lean:89` `Terms.E`, `Terms.M`, `Terms.gs`; `:106` `Eloc`, `:118` `Mloc`, `:147` `Ecomp` | Term data and evaluations; `E/M` take fields, while `gs` assigns a set to each `(j,X)`. | Agnostic definitions |
| `Balaban/SmallField/Def6Terms.lean:51` `levelGS`, `:86` `XiDom`, `:203` `levelGS_precedes` | Whole-level generator, complex chart parameterized by a generator, and precedence of the former. | Whole; agnostic; whole |
| `Balaban/SmallField/GsSpecDef.lean:33` `GsSpecCore`, `:67` `GsSpecStrong`, `:88` `levelGS_strong` | Core/strong layer conditions and the whole-level witness. `GsSpecStrong` permits `levelGS`; it does not bound the data-site footprint by a neighbourhood of `X`. | Agnostic; agnostic; whole |
| `Balaban/SmallField/GsSpecStrong.lean:39` `GsSpecStrong.adj_dataSites`, `:47` `precedes_levelGS`, `:69` `minimalGenSet_core` | Neighbour data sites, precedence toward a whole top level, and the minimal-set core. | Agnostic; agnostic; local |
| `Balaban/SmallField/GsSpecPoly.lean:150` `polyGS`, `:156` `gsSpecCore_polyGS`, `:179` `gsSpecStrong_polyGS` | Canonical small-field local set built from `MinimalGenSet.minimalGenSet`. | Local |
| `Balaban/SmallField/GsSpecPolyEqv.lean:230` `mem_polyGS_Ω_iff`; `Balaban/SmallField/GsSpecCounter.lean:138` `weakTerms_not_isSF2`; `Balaban/SmallField/GsSpecStrong.lean:109` `gsSpecStrong_minimal_witness` | Local-set layer test, failure of the weak class, and a nontrivial minimal-set witness. | Local; agnostic counterexample; local |
| `Balaban/SmallField/GsSpecPolyClass.lean:48` `localTerms`, `:69` `sfTermClausesStrong_localTerms` | Existing zero terms with `gs = polyGS`; proves the old strong clauses. | Local |
| `Balaban/SmallField/Def6v2Domain.lean:66` `FieldDom.dom`; `Balaban/SmallField/Def6v2.lean:78` `SFTermClauses` | Arbitrary generator-indexed complex domain; `gs_spec`, `analyticE/M`, `boundE/M`, `localE/M`, covariance and locality clauses use `Tm.gs`, while `eucEloc/eucMloc` use `levelGS`. | Agnostic except named whole-level clauses |
| `Balaban/SmallField/Def6v2.lean:214` `IsSF2.gsStrong`, `:236` `IsSFFamily2`; `Balaban/SmallField/Def6.lean:488` `IsSFFamily`, `:331` `TorusIndep` | V2 class, family, legacy family, and torus equality of term values. Only `gsStrong` purports to control the per-polymer generator; `TorusIndep` does not equate generating sets. | Agnostic specification, whole witnesses |
| `Balaban/SmallField/Def6v2.lean:292` `IsSF.toV2`, `:338` `IsSFFamily.toV2`, `:361` `IsSFFamily.toPin`, `:381` `IsSFFamily.toXi`; `Balaban/SmallField/Def6v2Bridge.lean:356` `IsSFFamily2.toLanded` | Legacy/V2 class conversions; the forward conversions receive an explicit `GsSpecStrong` input. | Agnostic, but forward hypotheses must strengthen under L |
| `Balaban/SmallField/GsSpecClass.lean:33` `SFTermClausesStrong`, `:47` `IsSF2.termsStrong`, `:56` `IsSF2.strongGS`; `Balaban/SmallField/GsSpecAgree.lean:131` `StrongGS`, `:166` `EcompAt_eq_local`, `:181` `McompAt_eq_local` | Generic strong-set access and local pair evaluation identities. | Agnostic |
| `Balaban/SmallField/Def6v2Source.lean:106` `SourceForm`, `:157` `SourceForm.indepE_of_nu_zero`, `:166` `SourceForm.indepM_of_nu_zero` | Source-domain consumers; `SourceForm.factE/factM` require `Dom.dom j (Tm.gs j X)`. | Agnostic |
| `Balaban/SmallField/Def6v2Renorm.lean:218` `IsSFFamily2.termwise_irrelevant_aniso_class`, `:359` `IsSFFamily2.renormalization_aniso` | Representative renormalization consumers of the class, via its term clauses. | Agnostic |
| `Balaban/LargeField/Def7v2Class.lean:66` `D2SF2.sfClass`, `:74` `SFFlat2.torus`, `:281` `IsRep2.sfData`, `:324` `IsRep2WithInterface` | Embeds `IsSFFamily2` in representations; the last record carries a separate SF-to-LF interface. | Agnostic wrappers |
| `Balaban/LargeField/Background/StepGenSets.lean:130` `genSF`, `:135` `genSF_precedes`; `Balaban/LargeField/Def7SmallField.lean:238` `SFCtx.genW`, `:256` `SFCtx.psiJ` | Regional set `genSF j (W2 R Y)`, its precedence, and the regional composed field. | Local |
| `Balaban/LargeField/Def7SmallField.lean:291` `SFCtx.EresJ`, `:312` `SFCtx.MresJ`; `:300` `EresK`, `:306` `Ares`, `:348` `sfFactor` | Evaluate the *class* `Tm.E/M` at regional `psiJ`; these definitions do not inspect `Tm.gs`. | Generator-agnostic syntax, local evaluation geometry |
| `Balaban/LargeField/Def7v2Form.lean:110` `EresJ2`, `:120` `EresK2`, `:124` `Ares2`, `:129` `sfFactor2`, `:217` `D1Form2` | V2 correction and representation form; inherit the same regional evaluation. | Generator-agnostic syntax, local evaluation geometry |
| `Balaban/LargeField/History/ParentDomain.lean:248` `inPsiTilde_genW_of_factors`, `:320` `inDomainR_genW_of_factors`, `:346` `theorem73_parent_of_factors` | Q13 parent-domain chain on `genW`, without any `Tm.gs` assertion. | Local |
| `Balaban/Fluctuation/StepObjects.lean:254` `StepClass`; `Balaban/Fluctuation/GeneralClassMatch.lean:68` `ClassParamMatch` | Old-term carrier and parameter match. | Agnostic |
| `Balaban/Fluctuation/GeneralClassMatch.lean:120` `stepTermsAnalytic_of_isSF2_of_subset`, `:138` `stepTermsAnalytic_of_isSF2`, `:189` `classRegular_of_isSF2` | Converts class charts into step analyticity and regularity; the needed inclusion is for each `Tm.gs j X`. | Agnostic, with new chart input under either option |
| `Balaban/Fluctuation/GeneralClassPathAnalytic.lean:60` `StepSetting.OldXiDomC`; `Balaban/Fluctuation/GeneralClassRegularC.lean:64` `OldXiDomOpenC`, `:588` `classRegularLocC_of_oldXiDomOpenC`, `:598` `classRegularObsC_of_oldXiDomOpenC` | Exact pointwise and open-neighbourhood domain inputs, then complex regularity. Both domain inputs quantify over `C.Tm.gs j X`. | Agnostic, but inputs must be reproved for a local set |
| `Balaban/Fluctuation/StepActivityHatGeneral.lean:304` `OldEnergyHatMatch`, `:330` `OldObsHatMatch`; `Balaban/Fluctuation/StepActivityHatLevel.lean:179` `oldEnergyHatMatch_level`, `:232` `oldObsHatMatch_level` | Abstract hat identities and their whole-level instantiations. | Agnostic predicates; whole-level proofs |
| `Balaban/Fluctuation/StepIdentityInhabited.lean:34` `zeroClass`; `Balaban/SmallField/Def6Inhabited.lean:48` `zeroTerms`; `Balaban/SmallField/Def6v2Inhabited.lean:215` `pinTerms`; `Balaban/Inhabited/GeneralClassWitness.lean:175` `qTerms` | Step zero class and global-generator test terms. `zeroClass` is a `StepClass`, not an `IsSF2` witness. | Whole |

## L: one local generator in the small-field class

The literal in-place edit is to strengthen `IsSF2.gsStrong` in `Balaban/SmallField/Def6v2.lean:228`; keep `SFTermClauses` and its analytic/bound/local fields as they stand. A safe successor record would retain `IsSF2` and add `localGS : ∀ j hj1 hjk X, IsPolyDom P.m₀ j X → GsSpecStrong j hjk X (Tm.gs j X) ∧ dataSites (Tm.gs j X) ⊆ nbhd r X`, with one uniform, stated radius `r(j)` and a regional `Precedes` lemma as additional fields or derived theorems. This schematic clause uses landed `dataSites`, `nbhd`, `Precedes`; the exact radius and proof are OPEN. Its neighbourhood must cover the collar required by the regional background argument.

At separation parameter `ϱ = minSep L 1`, the sharper proposed field is `Tm.gs j X = GsSpec.polyGS hjk X` (`polyGS` is the transported `MinimalGenSet.minimalGenSet`). This equality cannot be inserted at arbitrary `ϱ`: `polyGS` has type `GeneratingSet … (minSep L 1)`, whereas `Terms … ϱ` fixes `ϱ`; for example the landed `wSF2` uses `bgR0 3 3`. In the concrete case `d=L=3`, `minSep 3 1 = 15` while `bgR0 3 3 ≥ 4·3·3 = 36`, so the bare `polyGS` value does not even meet that background separation threshold. A typed local construction at the required separation, or a different parameter/radius theorem, is a prerequisite.

If `IsSF2` is edited in place, the following **15 direct witness declarations in seven files** cease to discharge its new local field on proper polymers: `Def6v2Inhabited.lean` `isSF2_pinTerms`, `isSFFamily2_xi_witness`, `isSFFamily2_pin_witness`, `isSFFamily2_of_landed_witness`; `GsSpecClass.lean` `sfTermClausesStrong_pin_nonempty`, `sfTermClausesStrong_witness` (still true for the old `SFTermClausesStrong`, unusable for the new field); `Inhabited/V2Wide.lean` `isSF2_pinTermsB`, `isSFFamily2_xi_witness_M`; `Inhabited/V2Energy.lean` `isSF2_eTerms`, `isSFFamily2_xi_witness_E`; `Inhabited/GeneralClassWitness.lean` `isSF2_qTerms`; `Inhabited/GeneralClassWitnessStep.lean` `isSF2_witClass`; `LargeField/Def7v2Inhabited.lean` `wIsSFFamily2`, `wSF2_D2`, `wIsRep2`. This is a direct-witness lower bound, not an estimate of all transitive build failures.

`levelGS_strong`, `pinTerms_gs`, `qTerms_gs`, `eTerms_gs`, and the algebraic terms remain true as written; what fails is their certification as members of a stricter class. The legacy `IsSFFamily` and `Def6.isSF_zero` are unaffected unless independently strengthened. `IsSF2.termsStrong`, `IsSF2.strongGS`, `EcompAt_eq_local` and `McompAt_eq_local` keep their current conclusions; their proofs can project stronger hypotheses. `D2SF2.sfClass`, `SFFlat2.torus`, and `IsRep2.sfData` retain source text but their inhabitance becomes stronger transitively.

| L measured category | Files | Declarations | Existing source lines in measured spans |
| --- | ---: | ---: | ---: |
| (a) Direct global witnesses unusable for a strict local class | 7 | 15 | 380 |
| (b) `IsSF2` plus the four forward legacy/V2 conversion statements | 1 | 5 | 127 |
| (c) Explicit neutral cohort below, unchanged as Lean declarations | 41 | 740 | 15,112 |

The span count is from each declaration header through the line before the next top-level declaration; it measures exposed existing code, **not** lines necessarily deleted or rewritten. Categories (a) and (b) are disjoint. The four conversion proofs should survive once their `hS` inputs are strengthened to the local clause; no such proof is claimed here. A versioned successor leaves all 380 witness lines compiling as old-class work, but does not make them witnesses of the successor. To prove a first nonzero local-class step, one still needs a typed local generator at the required `ϱ`, new nonzero `E/M` witnesses on it, regional domain inclusion, and a local hat identity.

## G+: retain the whole-level class, add a regional inherited-term interface

Keep `Terms`, `IsSF2`, `IsSFFamily2`, `D2SF2`, `IsRep2`, and all their current witnesses. Add a record of inherited `E/M` terms indexed by `(j,X,Y)` and a local `GeneratingSet` compatible with `genSF j (W2 R Y)`. Its fields must give the birth-level `Dom.dom` open chart, `analyticE/M`, `boundE/M`, `localE/M`, covariance, and an explicit equality or reconstruction law between inherited terms and the original class terms at `SFCtx.psiJ` and `constFld (hC hv)` (and at the observable `g`). A statement merely restricting `levelGS` data is insufficient because regional `psiJ` can be zero outside `dataSites (genSF j (W2 R Y))`.

Minimal additive G+ introduces new regional evaluation expressions and proves their equality to landed `SFCtx.EresJ` and `SFCtx.MresJ`; `EresJ2_eq` and `sfFactor2_eq` can then be reused. The `ParentDomain.lean` Q13 chain stays exactly as landed and supplies the regional geometry, but a **new** bridge must place the evaluated pair in the inherited class's open `Dom.dom` for every relevant `X`. `OldXiDomC`/`OldXiDomOpenC` stay abstract and require fresh witnesses for the inherited terms; `oldEnergyHatMatch_level`/`oldObsHatMatch_level` remain whole-level results and do not prove that comparison.

Replacing existing regional forms instead of adding comparison theorems would change `SFCtx.EresJ/MresJ` (2 declarations, 18 lines), then `EresJ2`, `EresK2`, `Ares2`, `sfFactor2`, `integrand2`, `postTerm2`, `PostConv2`, `D1Form2`, `preTerm2`, `PreConv2`, `D1PreForm2` (11 declarations, 110 lines), and at least the representation wrapper `IsRep2`/`IsRep2WithInterface` (2 declarations, 45 lines): **three files, 15 declarations, 173 existing lines** in this measured direct replacement surface. Further consumers such as `Balaban/LargeField/R/RegionEnergyAlgebraFR.lean` can need proof edits, so 173 is a lower bound for that optional path. `SFCtx.genW`, `psiJ`, the parent-domain chain, and the Q13 bounds themselves need no restatement.

| G+ measured category, additive design | Files | Declarations | Existing source lines |
| --- | ---: | ---: | ---: |
| (a) Landed declarations discarded | 0 | 0 | 0 |
| (b) Landed statements restated | 0 | 0 | 0 |
| (c) Explicit neutral cohort unchanged | 41 | 740 | 15,112 |

The new record and bridges have no landed line count; their design and proofs are OPEN. Minimum proof obligations before a nonzero step: a regional `Dom.dom` inclusion, the inherited/class evaluation equality for both `E` and `M`, and a local hat identity. The first usable result would be an `OldXiDomOpenC` or `OldEnergyHatMatch` witness for one nonzero inherited class, then the existing general regularity/marked expansion consumers apply.

## Generator-neutral and frozen work

The 41-file, 740-declaration, 15,112-line cohort consists of `Balaban/Inhabited/ScaleActivityFinal.lean`; `Balaban/Fluctuation/Marked*.lean`, `DetCauchy*.lean`, `SizeModExtend.lean`; `Balaban/LargeField/R/{RRipeCard,RRawHoleComponent,RHistoryLabels,SizeModExtendPull}.lean`; `Balaban/Localization/P6Pair*.lean`; `Balaban/Green/Final*.lean`; `Balaban/SmallField/FinalCutoff.lean`; and `Balaban/Flow/StopIndex.lean`. A text scan found no `Tm.gs`, `levelGS`, `IsSF2`, `IsSFFamily2`, `EresJ`, or `MresJ` references in those files. Their landed statements and proofs need no edits under either additive option. A strict in-place L edit can still interrupt compilation through imported witness files until those upstream witnesses are repaired. `ScaleActivityFinal` and zero-class marked results remain zero-class theorems; this does not turn them into nonzero-class witnesses.

`frozen/manifest.json` has eight `SEALED` definition anchors and two root anchors in `DRAFT_SORRY` state, `LogPartitionMultiscale` and `LowTemperatureCorrelations`. The manifest-declared `definition_closure` paths and `Balaban/Frozen/` sources contain no `IsSF2`, `IsSFFamily2`, `D2SF2`, or `Terms` reference. Neither option changes a frozen statement or its declared definition closure. This does not assert that future proofs of the roots have no small-field dependencies. An in-place `IsSF2` change is outside the sealed ABI, but the versioned successor is preferable if the old witness theorems should keep compiling.

## Decision table

| | L, in-place | L, successor | G+, additive |
| --- | --- | --- | --- |
| Existing lines discarded | No measured deletion; 380 lines of direct whole-level witnesses lose their intended class use | 0; old witnesses retained for the old class | 0 |
| Existing lines restated | Class and forward conversions: 127 lines exposed; 380 further direct-witness lines at risk | 0 | 0; optional replacement route exposes at least 173 lines |
| New theorem before first nonzero step | Typed local generator and domain bridge; nonzero local witness; local hat identity | Same, plus successor projection | Inherited `E/M` equality, regional open domain inclusion, local hat identity |
| First attainable nonzero result | Local-class `OldXiDomOpenC`/hat witness | Same | Inherited-class `OldXiDomOpenC`/hat witness |
| Main risk | `ϱ` mismatch and direct witness breakage | New class API and conversion proofs | Regional equality may fail for terms with nonlocal dependence |

**Recommendation:** choose L as a *versioned local successor*, with an explicit rule for `ϱ` and a proved data-site radius, if the intended mathematical class really assigns `𝔹_j(X)` to each polymer. This retains existing whole-level Lean and gives one generator semantics to the future nonzero proof. Choose G+ only if the author intends whole-level class terms as primary data and can state a physically justified regional reconstruction theorem; that theorem is currently OPEN. No frozen-anchor approval is forced by either additive path.
