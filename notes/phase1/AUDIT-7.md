# AUDIT-7 — energy record and parameter families

**Verdict.** G1, G2, G4 and G5 are **FAITHFUL** to their precise, restricted statements. G3 is **WEAKER THAN CLAIMED** if `obsCoeffParam_fromTower` is described as unconditional: its analytic conclusion still takes explicit activity and amplitude hypotheses. The available tilt theorem supplies compatible data after a particular radius and threshold are chosen, but that application is not a conclusion of `obsCoeffParam_fromTower` itself. G1 is likewise **WEAKER THAN CLAIMED** if the `ℰ₁(z)` expansion is called the complete Theorem 3.1(a) expansion. No inspected statement is VACUOUS or a WRONG OBJECT. This is a statement-and-definition audit, not a build or proof-term audit.

**Frozen input.** Commit `58401132f1b9ade7aca2a72e920ea3558cd8ca92` (2026-10-13 UTC); `/home/scott/Balaban` was read only. File:line anchors below refer to this commit. Paths in the table and text are relative to that repository; `F/` abbreviates `Balaban/Fluctuation/`, `I/` abbreviates `Balaban/Inhabited/`, `S/` abbreviates `Balaban/SmallField/`, `L/` abbreviates `Balaban/Localization/`. SHA256 records the exact reviewed bytes.

| File | SHA256 |
|---|---|
| `F/DecMarkCorrSum.lean` | `89a2b776bb86b537567546682eb52165fbb82839749bd9fec742c4f106b9c372` |
| `F/DecMarkCorrRooted.lean` | `c3e10fcbc5126d5a0a46a6e931d3dcf275294c12644c6893dccadcc22e9a0d43` |
| `F/GsumActiveParam.lean` | `94b28cf94b7553b75f0be99ed115bafee5405ba13068c29a8197a298371dae65` |
| `F/ObsHkerSupport.lean` | `0e0a04ffa9e5adb6ac3d0a307c85abaec4e724e72b510a40ece3b3218b65c748` |
| `F/StepComplexOut.lean` | `df16d2de12afbbf7594f28e103b48a1df7171dc46e306a0486cc98223925463c` |
| `F/Thm31cde.lean` | `474a83db5b8212d850d99c3ac4c0e4016618dfa6b23a0ee2327d21d11e0856e6` |
| `F/StepComplexThm31.lean` | `994c71730ff4ac3ec2e6a41e4a2b87595e24dc7356d32335d3a69e41a217259a` |
| `F/StepComplex.lean` | `4676c849df68cf9352473f55dcdd9be9ad1c779a3ee3eecbcc04b6a101f9ac58` |
| `F/StepIdentityInhabited.lean` | `565ed4fce9f200f9f50d8dcade18c90fb8a2bca6a1079e2b6513d6219d657041` |
| `F/Thm31CoeffB.lean` | `5f83b1fe23d0ddfb028d12d535a6890e1f4c88f656ea4dff531019d7131d5998` |
| `I/DecMarkCorrSumFromTower.lean` | `033d328e22bdb90e2f5510f16273e773bbd3f2dff28703c4615857a7339a0a11` |
| `I/E1RecordFromTower.lean` | `8f22fb1a67e7647153ee9acc91bc1f2ae42104db1b29ea0dd61266f40f2a8644` |
| `I/E1RecordOfSum.lean` | `c4092a99f12cd848bccdc4de292963f93320bcf47e09665f8c0f8d9788826f4d` |
| `I/E1MarkParamCommon.lean` | `7b8f33204028f0672484b816cb6c0d35d2efea7df1ce7f90d75513d01409efb0` |
| `I/E1ParamRawLocal.lean` | `231f02451e2a3df8ee3b452020e4951aebae13e6f9fe0065b9636d8ade4e6072` |
| `I/ObsCoeffAnalytic.lean` | `b1df14fbf7ade871a27ba846521cbbf360efd244a9181ba05b52fc72aa392ec6` |
| `I/Thm31bPolymerSupport.lean` | `80ff0d769baf7068c456398e4b03bfd0c66c923650e66e3873dcb0452db095ef` |
| `I/Thm31aPolymer.lean` | `df7881e22218b05858fe1cc6ca53685b18b13269f8678a3de4f2ee96a1e80a1c` |
| `I/Thm31bKernelSupport.lean` | `b7398ba7ae21dc939f9e4e9824af75e736017e95505131c09108c98e3af42c5e` |
| `I/LevelRayDataGeneral.lean` | `ecf7f4641fb7cb8809eba06109e0d3d54d46b1d31954095c06ee2e2e5b634dc8` |
| `I/ObsTiltLabels.lean` | `1ed6039f78aa540e5f25b53f5e0943172a00b7771fc6453146e37a6339cfdbc8` |
| `I/DecMarkCorrFamilyFromTower.lean` | `9b023e2d5d07a9ee45294c4d904fcb94f6a4a6f4164900f76052559a60f4e13e` |
| `I/ZeroSourceActivityCommon.lean` | `21d56a83a7f0202e63f12bb7b5010eabf1796a13566b5da0122dc71751a901f5` |
| `I/LevelPairGeneral.lean` | `c4ec163ad5b5dbfa81e1cb2768ccf0d4cb9bfcfac27f47f3014b983f9ff9e83c` |
| `S/Def6Terms.lean` | `a0c93ce2410aebac4b2803cdb5cdde0ebcab8ea0247494ca102d2600c4056e4f` |
| `L/PolymerGeometry.lean` | `c74b191de98f9d64da8aedeb3be3044e1cdf765c4974a770a4bb5ef3169e6c2c` |
| `L/TreeLengthCov.lean` | `46183dce317e7b29decc25af62ad13f6acf47e041bb665a620da3d10730b7da8` |
| `F/SizeModDefs.lean` | `df897aff0ac98d6966bdb37d16c6367d1df8f21aa201005cc1e1f188eeb56d5d` |
| `F/RootActiveSize.lean` | `31fbb89533c5fa48097e154ae068dce3d605d384a0aedfe7e3c3fde25b88d3bb` |
| `F/Prop33CloseC7.lean` | `1e91a6780a1607ce72a1ee63589b2e8315f8e3dc00dbbb81ba2f979524b42127` |
| `Balaban/Background/ExistenceSetup.lean` | `bcf6ce65a7fb680a344aed73df309e2c7c189e8f7ddecfdbd626d12f10d0eb56` |
| `Balaban/Multiscale/Coercivity.lean` | `61c5d81ddd97b3de5557361b94e44fa800b9c7e9e57a9b1a29bede7e7606bc6f` |
| `sources/Balaban.pdf` | `804ba741c65367a4ba3e1ce84f0c415999a32de0ff2e1c337b41d9fa9104a303` |

## G1. Physical sum and energy record

**FAITHFUL, with a precise scope.** `StepComplexOut.lean:169–180` defines `Phi1C C(y)=-β VkC(ψ0C+y)+dEC C(ψ0C+y)` and `E1locC C z=∫₀¹ ds avgFun(νfl,WoneC C,D Phi1C(s shiftUC x)[maskUC z(shiftUC x)])`. `StepComplex.lean:327–344` identifies `VkC` with the actual interaction and `dEC` with the effective-action difference; `StepIdentityInhabited.lean:33–38` makes that difference zero for `zeroClass`. The PDF image at printed p. 695, (2.55)–(2.57), directly confirms the local integral and two summands. This is the physical first-order interaction exponent at the **zero class**, not a proxy.

`DecMarkCorrSum.lean:351–412` derives the corrected-mark sum from the block-energy identity on a complex disc; `DecMarkCorrRooted.lean:75–120,178–232` resums it over bridge labels and passes to the fluctuation measure. `DecMarkCorrSumFromTower.lean:71–132,190–232` discharges the physical hypotheses at the tower for **any given** pair family satisfying its displayed `hP`. That premise is inhabited: `DecMarkCorrFamilyFromTower.lean:34–50,150–181` chooses one `(F₁,Sol)` indexed by `(root,block)` and supplies `MarkedBlockExpansionDecPair` for every root and block. No pair is selected after `x`; the pair precedes the root-specific identity. The threshold precedes `k,N₁,ν,β,p₁,D,z` in `E1RecordFromTower.lean:98–118`.

**FAITHFUL record fields.** `StepComplexThm31.lean:50–53` sets `E1MarksC` to `InterpMarks νfl BS (WoneC C) (D Phi1C[...] [maskUC...])`. `Thm31cde.lean:117–120` requires both `hW` and `hF` for **every** real `s∈[0,1]` and `νfl`-a.e. `x`; `E1RecordOfSum.lean:103–106,145–157` supplies the physical `WoneC` activity identity and the physical `hF`, while `E1RecordFromTower.lean:50–89,114–118` proves the latter from the pair clauses. The Lean fields have quantifier order `∀s, ∀ᵐx`, so they do not themselves assert one common null set for all uncountably many `s`.

**WEAKER THAN CLAIMED as full Theorem 3.1(a).** `E1RecordFromTower.lean:148–165` proves `E1locC(z)=∑_T E(T)` with `‖E(T)‖≤K0 3 3 T.κ0 exp(-T.κ' dExt T)`. It is precisely the local `ℰ₁^{(k+1)}(z)` of P4 (2.57), as displayed at printed p. 695. The complete local `ℰ₀(z)` of (2.60) adds `-½` of the block trace of `log C`; see `StepComplexOut.lean:182–185`. Thus this theorem alone does not give the determinant term or the canonical coefficient of Theorem 3.1(a). Its record remains base datum and zero class only; do not infer an analytic family in `θ`, a general class, or a full RG step.

## G2. Parameter marks and local premises

**FAITHFUL.** `E1MarkParamCommon.lean:51–68` cuts `e1MarkGParam` to zero when raw `θ` leaves `XiCRaw` or `‖u‖≥corrU`. The equality with `e1MarkG` at the step datum is explicit (`:96–104`); physical `s∈[0,1]` satisfies `‖s‖<corrU` in `E1RecordFromTower.lean:79–89`. The parameter-family output is asserted on `physV × ball(0,corrU)` (`E1MarkParamCommon.lean:197–209,316–372`), where the cut-off is inactive, so no reviewed physical identity uses its zero values outside that set. Its empty-mark input is exactly the `ParamMarkFamily` produced by `ZeroSourceActivityCommon.lean:491–527` after `q=1`, `reads=univ`, `dom=e1Dom`; the theorem is an implication from that inhabited input, not an independent activity construction.

`E1ParamRawLocal.lean:226–232` proves that `π(θ)=physRestrict(thickSet(Yhat univ (sitesOf T)))(physIncl θ)` forces the raw agreement required by both `commonAct_zeroSourceAct_hA` (`:257–278`) and `markedOutDec_decMarkCorrTerm_hG` (`:297–344`). The latter uses agreement on `thickSet Y'`, not merely `Y'`, via the pair locality and bridge-subset argument (`:124–170,188–215`). Both premises quantify only over `θ,θ'∈physV` and the real interpolation segment; these are the local restrictions needed for the landed coefficient arguments.

`GsumActiveParam.lean:41–174` has four complete theorem statements; each binds the measure, activity, mark, positivity, decay and smallness hypotheses used in its body. The section variables are types, dimensions and instances, not a stranded proof hypothesis. In the other audited files, hypotheses appearing after section `variable` declarations are likewise present when used in conclusions (`ObsCoeffAnalytic.lean:326–337,411,540,640` explicitly includes `Dsc hS`). I found no second instance of the reported syntactic problem in the audited set; this is not a whole-repository parser audit.

## G3. Observable parameter coefficient

**FAITHFUL algebra, conditional analytic theorem.** `ObsCoeffAnalytic.lean:44–55` defines `obsCoeffParam` as `kernelMarkSum(hker,markIntTerm)+gsumCoeff(Gr)`; `Thm31CoeffB.lean:93–103` defines the fixed-parameter `obsCoeff` by the same first-order kernel sum and remainder. The first-order terms, kernel sum, and remainder are the three analytic parts in `ObsCoeffAnalytic.lean:65–99,424–537`. The sharp-hat `Ev` and both parameter mark families are returned by `obsCoeffParam_fromTower` (`:549–636`), but its binder list still requires `hhol`, `hcont` and `hε: Rg·max(2εH,εH)≤stepTheta 3 3 Kobs (2κdec−1) κ0 κ'` (`:551–558`); the norm theorem also requires `hσ,hzero` (`:655–662`).

**Compatible instantiation, not an arbitrary-radius conclusion.** `ObsTiltLabels.lean:297–313,332–365` supplies `hhol,hcont` on the entire parameter carrier and, after choosing `Θ>0` before its threshold, supplies `obsRg(CR,s,p,β3^k)·max(2εH,εH)≤Θ` and `1<obsRg` (its last clause is phrased under a source `g` in the radius-`q` ball; `g=0` inhabits that ball when `q>0`). Choose fixed `Kc≥K0+1`, `Kobs≥2Kc+2K0`, and `Θ=stepTheta 3 3 Kobs (2κdec−1) κ0 κ'` before invoking that theorem; the tower positivity inequalities make `Θ>0`. Then choose `Rg=obsRg`, obtaining the numerical binder in `obsCoeffParam_fromTower`. `ObsTiltLabels.lean:345–353` also gives the `σ` analyticity and zero at `σ=0` for all parameters of `physVq`. An arbitrary `Rg>1` or an unrelated `Θ` is **not** certified by the output. There is no standalone unconditional observable-family theorem in the audited file.

## G4. Polymer support

**FAITHFUL nearest-neighbour domain.** `Def6Terms.lean:93–97` defines `IsPolyDom m₀ j X` as `X.Nonempty`, a `ChosenOne` cover of `X` by aligned `π'_j` cubes, and `∀x,y∈X, ReflTransGen (λa b, a∈X ∧ b∈X ∧ Nbr a b) x y`. `TreeLengthCov.lean:42–46` says the chosen cubes lie in `X` and cover it; `PolymerGeometry.lean:135–136` defines `Nbr` by a single positive or negative coordinate step on the **site lattice**. This is not coarse cube adjacency. `SizeModDefs.lean:58–66` likewise defines `IsDj` by a nearest-neighbour site path. The finite-size equivalence for cube sets is `RootActiveSize.lean:120–131`.

`Thm31aPolymer.lean:45–95` proves the canonical energy coefficient vanishes off `IsPolyDom` (and the root support under its explicit anchor premise). `Thm31bPolymerSupport.lean:60–66,98–138` gives the observable remainder and kernel-conditional support; `ObsHkerSupport.lean:27–42` supplies the kernel's finite-size premise when its label domains are `IsDj`. The one-scale and common-witness support statements actually carry those domain hypotheses (`Thm31bKernelSupport.lean:36–40,141–175`). The support conclusion is for `sitesOf T`; it does not itself establish all analytic, symmetry or rate clauses of the paper's observable theorem.

## G5. General ray and G6 caveats

**FAITHFUL and jointly satisfiable.** `LevelRayDataGeneral.lean:57–69` takes one `m₁,δ,δ'`, with `hbig`, `hsm`, `hδ'a–c` all visible, and yields `RayData(2p₁)` for `hatStepKG` at `rhoSepG d L m₁`. For every `d≥3,L≥3,N≥2`, first choose `m₁≥4` large enough for `cstarX d L≤L^{m₁}` (the positive base `L>1` is decisive), then choose `δ>0` small enough for `δ² smallConstX d L 0≤1/4`, and finally choose `δ'>0` below `thm73C3 d L N/2`, `δ/(4 bgK1 d L N)` and `coerciveConst d/(4 bgK1 d L N)`; their numerator constants are positive (`Fluctuation/Prop33CloseC7.lean:31` `thm73C3_pos`, `Background/ExistenceSetup.lean:113` `bgK1_pos`, `Multiscale/Coercivity.lean:197` `coerciveConst_pos`). `scale_C_items_general` uses that same choice through `:139–143,169–208`, with one threshold before all scales. This is a numerical witness for a fixed separation; `LevelPairGeneral.lean:35–37` sets `ϱ=rhoSepG d L m₁`, so the theorem covers this particular sufficiently large separation, not every admissible `ϱ` allowed by the paper.

**G6 — corrected docstring sentences.** For `E1RecordFromTower.e1loc_expansion_zeroClass_fromTower` (`:143–160`): “This expands the zero-class local `ℰ₁(z)` of P4 (2.57) at the base datum; the local `ℰ₀(z)` of Theorem 3.1(a) also contains the determinant trace.” For `ObsCoeffAnalytic.obsCoeffParam_fromTower` (`:540–559`): “For the sharp-hat family, the parameter mark records and analytic coefficients follow after `hhol`, `hcont` and the specified `Rg` amplitude inequality are supplied, for example by a compatible instantiation of `obsTiltLabels_fromTower`.”

## Refutation ledger and closeout

| Candidate defect | Verdict and decisive anchor |
|---|---|
| Sum identity concerns a surrogate exponent, or its pair premise is empty | **REFUTED** for the zero class: `F/StepComplexOut.lean:169–180`, PDF p. 695 (2.55)–(2.57), `I/DecMarkCorrFamilyFromTower.lean:34–50,163–181` |
| Energy record asserts only `s=0`, or cuts off real `s∈[0,1]` | **REFUTED**: `F/Thm31cde.lean:117–120`, `I/E1RecordFromTower.lean:79–89` |
| Energy `ℰ₁` expansion alone is full Theorem 3.1(a) | **SURVIVED** as an overstatement: `F/StepComplexOut.lean:178–185`, `I/E1RecordFromTower.lean:148–160` |
| Parameter mark's cut-off is used outside its physical chart/disc | **REFUTED** in reviewed uses: `I/E1MarkParamCommon.lean:61–68,97–104,197–209` |
| Observable amplitude holds at every `Rg>1` | **SURVIVED** as an overstatement: `I/ObsTiltLabels.lean:363–365` singles out `obsRg`; `I/ObsCoeffAnalytic.lean:558` carries `hε` |
| `IsPolyDom` means only coarse adjacency | **REFUTED**: `S/Def6Terms.lean:95–97`, `L/PolymerGeometry.lean:135–136` |
| General `δ,δ',m₁` clauses contradict each other | **REFUTED** by the positive-constant choices above; `I/LevelRayDataGeneral.lean:59–67,139–143` |

**Limit.** The source comparison used the PDF image for P4 p. 695 because its OCR loses formulas. No Lean build, axiom census, or complete dependency audit was run. Only `AUDIT-7.md` and the temporary PDF page image were written in the scratch directory; the read-only repository was untouched.
