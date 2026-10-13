# AUDIT-13 — refute-first statement and definition audit

**Scope and verdict.** Focused tier-2, read-only audit of W586/W587/W591/W597/W598 and the W588/W590 files carried by W585. Overall **FAITHFUL** for the stated conditional declarations; **WEAKER THAN CLAIMED** at two downstream interfaces: applying `localB` to an arbitrary class polymer without an alignment bridge, and applying the observable record at `q<1`. No statement was found **VACUOUS** or a **WRONG OBJECT** within its written hypotheses. This is a source inspection, not a Lean build or proof-term/axiom audit.

**Frozen-v1 commits (13 October 2026).** Main `74cea1e805af188cd508c54c936428fa469a787a`; W586 `9a961a2ad5afcc863ff1cf90f0975b474b14876d`; W587 `87003dbd08ea52b35c428c77fa7255ca20b9e660`; W591 `1442181f8db5b20d38b9fe75ba54e64ecc0d93ab`; W597 `c8f6b1c41cd2c1d7a3d4d162a41f3a86b8314193`; W598 `bdff38b3cca585d92e4867c64ad825184d7cde63`; W585 (W588/W590 carrier) `df5799a9fd98cd761224647ae86103175206c756`. Main was clean at inspection.

**Frozen-v1 SHA-256 manifest.** Paths in the next two lists are relative to `Balaban/`; each hash is of `git show commit:path` bytes. Branch targets:

| Commit | File | SHA-256 |
|---|---|---|
| W586 | `Inhabited/ObsFamilyPrefactor.lean` | `0bbc56ca78798dd7b34310f4d432195ea234b11eb46f9634e0b40f139441c4fa` |
| W587 | `Fluctuation/MarkedEvJoint.lean` | `627f1e86cadfc031e2f127bffdec66a3b46914e1485e907765523915c786dc57` |
| W587 | `Fluctuation/DecMarkOfPair.lean` | `5c3f7f73c6408ee09997691641b82c19a95a0a43f981488f9a43bc42f411d878` |
| W587 | `Inhabited/DecMarkCorrFamilyFromTower.lean` | `42dda0fc9fab63474d156079df59dd86a9a365597c42abb72fcc929d397dbe18` |
| W587 | `Inhabited/E1CoeffFamily.lean` | `9fe5777c22acf5105644fcb8b8a026d33f8088e7369fee02e7106195313103c6` |
| W591 | `Fluctuation/SharpENu.lean` | `44e9824940da0813ea5a2725d4750529872ff62e9974e1a78265605ca3dfd3da` |
| W591 | `Fluctuation/SharpAE.lean` | `f47de3c6ec6f07d9b1b1bd16cd2af40119609763ea5352045721d425359a86b8` |
| W591 | `Fluctuation/SharpEngine.lean` | `c1b5eb540e84842bee22ff2b54c160848e1d29154d7337ed28c4af9d1b249e3b` |
| W597 | `SmallField/LocalGeneratorSource.lean` | `989babdea5fed5f2c43eb26c1d4030e47549e7b99807976a8082516cc6a1d339` |
| W598 | `Inhabited/LevelCoversG.lean` | `dd93cb98740c76b712dc357f9c38ee1642279a1069ada2d3157defde11e204f6` |
| W585 | `Inhabited/RenJoinClassWitness.lean` | `e5019fb1c19c7a211da9007384aa06e7f279441e5c7d7d3b01ac4316374189f8` |
| W585 | `Inhabited/RenormM0SiteRecord.lean` | `75b2371b0d3c207a8255c799d2c4a4df390fc881c5d072ec6b793da820fdadfe` |

**Frozen-v1 comparison SHA-256 (main).**

| File | SHA-256 |
|---|---|
| `Fluctuation/MarkedVRawY.lean` | `0b7210fbc03cde6c26220726d2a35dfcea2f3888def65c7205a5814113d98616` |
| `Inhabited/E1ParamRawLocal.lean` | `78657166e7d32d31dd48a20a79121749b8bf2b91412c96d735d9bb8923d822df` |
| `Inhabited/E1MarkParamCommon.lean` | `7b8f33204028f0672484b816cb6c0d35d2efea7df1ce7f90d75513d01409efb0` |
| `Fluctuation/ObsRemainderFamily.lean` | `e89b50eacfe5af9cfd37cdf216c9e3b9ddde16b4f95071b52cc30dfd65ce5624` |
| `Fluctuation/PhysicalReadsE.lean` | `7d0c151a3c0fe9d03816e074dc774469fb175adf5438e8d086ef0820bd53ec36` |
| `Fluctuation/InteractionHatE.lean` | `0da849004eb6476d9810b50680c758f68fe1379e5e04cbb537bb62e6d07d08ec` |
| `Localization/I5Fan.lean` | `c4c4ab0b40d4d52e129afcb656c25d6ee8ce6fc9f827eec54c9a54cb3b9ec5be` |
| `Localization/DecoupledBackground.lean` | `9fc29bbaffe5bffb913f039308bf6157eb2b59b336e6c6f9142614f04418720b` |
| `Background/Data.lean` | `9fd2ab665e228cc29f62835c6f53d3db7e297e70841295981e4659b3ab017a10` |
| `LargeField/Background/MinimalGenSet.lean` | `d53b990b4a745da938329c688008cbbb44b1e57747f435dbc91eae8f2d65f875` |
| `SmallField/Def6Terms.lean` | `a0c93ce2410aebac4b2803cdb5cdde0ebcab8ea0247494ca102d2600c4056e4f` |
| `Localization/TreeLengthCov.lean` | `46183dce317e7b29decc25af62ad13f6acf47e041bb665a620da3d10730b7da8` |
| `Inhabited/StepTowerScale.lean` | `6124b14f4687e3d7c4454a55f0020994017fcbd9847293801e26d91b2ecfebb4` |
| `Fluctuation/SourceFamilyRelative.lean` | `c41534a4b3fd46e28751588a6fcc2581f7dfdd4b7372b6cbd9dc0fcfe9ca76ce` |
| `Inhabited/ObsFamilyJoint.lean` | `2d8c45eac0c9c4adb0101f8a7254bc279a2bfd6e5e446bfea077df57356c7a7a` |
| `Localization/I5Chain.lean` | `6608afba04884a128b7b1deef78a36736ab93d6d9440f0be772ccd66550218ea` |
| `SmallField/Def6InfShapes.lean` | `41d4dd196e9a8b9a686451e90df7e040eb35aca66e244fe4fa0195088d261899` |
| `Localization/PolymerGeometry.lean` | `c74b191de98f9d64da8aedeb3be3044e1cdf765c4974a770a4bb5ef3169e6c2c` |
| `Inhabited/ObsMarksFromTower.lean` | `93eae1e25e34daf1a875a935a1b42224e76abf1718c82283a356727fd3b33747` |
| `Inhabited/ObsCoeffFamily.lean` | `5ceb58326a54098acf4d52992748bab7b079f18b1bbbdd52b9d96dbafdc41875` |
| `notes/phase1/GENL.md` | `f51af3ef6819b49014e2c93202a0be1fd6094e75bd6f3d58abac08478aaa2020` |

## Statement ledger and refutation results

| ID | Verdict | Frozen-v1 anchors and tested claim |
|---|---|---|
| L1a | **FAITHFUL** | W587 `MarkedEvJoint.lean:194–212,616–631,739–754` repeats the `hF₁`/`hSolprop` slots of main `MarkedVRawY.lean:353–369` and `E1ParamRawLocal.lean:563–580`: `c7`/`rho4`/`K4` use `BG`; `c6'`/`cK2'` use `BG₂`; `eps` occurs as `xiC1 d * eps`, and `δ₁` remains the strict-data radius. W587 tower substitution in `E1CoeffFamily.lean:117–133` sets `d=L=3,N=2,eps=δ₁=T.t,Gp=S.G',Hm=stepG`, with `a₁=S.a₁,ν=S.ν`. No swapped radius or level pair found. |
| L1b | **FAITHFUL**, not **VACUOUS** on the asserted domain | `InUnionDomainC` is `∃ δ ε, … ∧ InDomainC` (main `Background/Data.lean:306–310`); `i4b_exists_unique` produces `φ,α` with `IsDecBg` for such a witness (main `Localization/DecoupledBackground.lean:228–244`). At the tower, `Dsc.xi` and `xiCData_inDomainC` give an inhabited instance (main `Localization/I5Chain.lean:137–148`), while `s≡1` satisfies `‖s P‖<exp κ` from positive `κ`. Thus `hF₁` pins `F₁` there. The `hSol` clause is conditional on `StrictDataM`, and its existence/uniqueness is supplied by the `Dec2.i4a_analytic` choice in W587 `MarkedEvJoint.lean:636–641`. |
| L1c | **FAITHFUL** on `physV` | W587 `E1CoeffFamily.lean:274–303` assumes both `θ∈physV`, proves `‖s‖<corrU`, then rewrites the guard of `e1MarkGParam` using `hθ.1`; main `E1MarkParamCommon.lean:61–68,80–89` defines that guard as raw `XiCRaw` plus `‖u‖<corrU`, and main `ObsRemainderFamily.lean:120–124` proves `physV→XiCRaw`. The consumer guard `θ∈physV ∧ ‖s‖<U` is therefore true at each quantified point when `U=corrU`. These guards need not agree outside `physV`; no conclusion here ranges outside it. |
| L1d | **FAITHFUL** | Diff `git diff --unified=1 main W587` shows only appended `SPEC` conjuncts in the five existing surfaces `markedEv_joint_param`, `MarkedEvJointPhysV`, `decMarkPair_family`, `markCorrFamily_fromTower`, `e1MarkParam_pairs_fromTower` (W587 `MarkedEvJoint.lean:603–641,737–754`; `DecMarkOfPair.lean:193–212`; `DecMarkCorrFamilyFromTower.lean:123–140`; `E1CoeffFamily.lean:116–133`). `decMarkPair_exists`, `markedEv_joint_physV`, and `e1CoeffFamily_value_fromTower` change projections/proof destructuring, not their theorem conclusions. `e1Mark_hG_rawY_fromTower` is a new declaration. |
| L2a | **FAITHFUL** | Main `InteractionHatE.lean:54–62` defines `eTermFun pa δφ u := E (D2raw … (d1Triple … pa.1 δφ u))`; main `I5Fan.lean:45–49` shows `D2raw` reads the *whole composed raw datum*, while main `Background/Composition.lean:171–179` shows `composeField` reads `φ` through `svec` at composite dependencies. W591 `SharpENu.lean:60–109` assumes `hφ` only at `composeDep Gk Gp x` for `x∈dataSites Gk`, proves equality of the *entire* intermediate raw datum (outside data sites both branches are zero), then applies `congrArg (D2raw …)` and `congrArg E`. Arbitrary `Fk,E` therefore cause no extra `φ` read. |
| L2b | **FAITHFUL** | W591 `SharpENu.lean:201–230` derives `hφ` from `i4b_local_of_agree_on_component` and main `PhysicalReadsE.lean:153–186`, whose exact roles are `x∈dataSites Gk`, `u∈composeDep Gk Gp x`, `approxDep Gp u⊆X₁f`, with `IsLevel Gp (k+1)`. `X₁f⊆Y=compY … C` is supplied explicitly by `subset_compY` at W591 lines 209–210; the same inclusion feeds `hδ`, raw-data agreement and hat agreement. No Gk/Gp/Gj substitution was found: `Gj` enters only the outer `D2raw` after the intermediate raw data are equal. |
| L2c | **FAITHFUL** | W591 `SharpEngine.lean:620–685` keeps the `FlRealLC` analyticity/bound, fan hypothesis for every `F₁,Sol` with their full specifications, `IsLevel Hm k` and `IsLevel Gp (k+1)`; it replaces only the agreement relation by a monotone, reflexive `Ag`. W591 lines 829–914 instantiate the *same* theorem at `AgHatDir`; W591 `SharpAE.lean:309–316` identifies `hconn,hrow,Z,Zα,hZ,hBM,hΦloc` as inputs of the concrete fan proof, now incorporated in `hfan`, not silently discarded from an unconditional theorem. |
| L3 | **FAITHFUL** | W586 `ObsFamilyPrefactor.lean:31–49,69–75` chooses `C` before `b,p₁,ι,dl`; its entropy premise is the weighted sum with exactly the `obsRemLab` label distance used in the family bound. W586 lines 327–347 obtain the *one* `obsFamily_full_fromTower` witness (`Ev`, activity and coefficient), replace only `hbd`, and pass `hsum` from that same mark-half record into the abstract `dl` premise; `obsFamilyRate_eq_tower` is the equality `λ=3κdec/2` (main `ObsFamilyJoint.lean:462–471`). Caveat: this bound is the project's `obsPrefactor`, not the paper's final prefactor, and W586 has not yet been merged with W585's sharp `Ev` branch. |
| L4a | **FAITHFUL** | W597 `LocalGeneratorSource.lean:41–46,60–100` is the transported `minimalGenSetAt` from main `MinimalGenSet.lean:47–123`: top sites have their whole `M₁L^j` cube in `X`, lower layer uses `supDist(fineCubeIdx_n x,fineCubeIdx_n y)≤5L`, and layers above `j` are empty. This is cube-index sup-distance at scale `n`, matching the “within `5L` cubes” recursion recorded in `notes/phase1/GENL.md:T1`; it is the minimal (whole-input) object, not the mixed-history local chart of GENL T1. |
| L4b | **WEAKER THAN CLAIMED** at the class interface | W597 `LocalGeneratorSource.lean:102–144` proves `gsSpecStrong_localB` only under an explicit `hX` that `X` is a union of `M₁L^j` cubes. `IsPolyDom` itself is nonempty + a `ChosenOne` family + connectivity (main `Def6Terms.lean:93–97`); `ChosenOne` uses aligned boxes of side `L*cellSide`, with `cellSide=L^(j+m₀+m₁)` (main `TreeLengthCov.lean:42–46`, `PolymerGeometry.lean:236–244`). The intended arithmetic is `M₁L^j=L^(m₁+j) ∣ L^(m₀+m₁+j+1)`; aligned-box partition on the torus also needs `L^m₀∣N₁` and `j≤k` (the same hypotheses of main `Def6InfShapes.lean:50–64`). W597 supplies no `IsPolyDom→hX` bridge; `IsPolyDom` alone does not carry these ambient divisibility hypotheses. This is an integration obligation, not a counterexample to `localB` or its conditional `GsSpecStrong` theorem. |
| L4c | **FAITHFUL** | W598 `LevelCoversG.lean:30–61` replaces the numerals in main `StepTowerScale.lean:45–76` by `d,L,N`; its source-site binder is `Fin N`, and `blockSites`/`scaleW` use `d,L`. W598 lines 75–79 gives `Iff.rfl` at `3,3,2`; `levelCoversG_of_dvd` lines 63–71 still assumes `DGSetting`, `IsLevel Gp (k+1)`, `1≤m₀`, and `L^m₀∣N₁`. No hidden `N=2` remains in the body. |
| L5a | **FAITHFUL** | W585 `RenJoinClassWitness.lean:101–163` obtains one `⟨F,hF,h1,h2,h3⟩` from `renLoc_fields_scale_of_tower_at` and extends `h1,h2,h3` to `renYs∪S` using the same `F`, classes, radius `R.r₀`, rates and `Kloc=1`. There is no second solution existential. The principles remain over `XiCOneReal`; a later fibre restriction is separate. |
| L5b | **FAITHFUL** for `q=1`; **WEAKER THAN CLAIMED** for a direct `q<1` instantiation | W585 `RenormM0SiteRecord.lean:34–79,89–102` assumes `han`, `hloc`, `hbd`, `hsupp` on `physV`, takes `hval: M0C=√βU∑c`, and uses positive `βU` to conclude an expansion of `(√βU)⁻¹M0C` with budget exactly `B` (no extra square-root factor). W585 lines 106–158 only extends the index family. Main `SourceFamilyRelative.lean:82–89` proves `physVq … 1=physV`; for `q<1`, `physVq⊆physV` gives no analytic/locality extension to all `physV`. Use `q=1` or prove a separate record restricted to `physVq`. |

## Refutation ledger (frozen-v1)

| Candidate | Adversarial attempt and result |
|---|---|
| R1 “`hF₁` is vacuous” | Tried the empty-domain reading; `InUnionDomainC` explicitly contains an `InDomainC` witness and `i4b_exists_unique` constructs `IsDecBg`; the tower chart supplies an instance. **Refuted**. |
| R2 “guard changes the mark” | Compared guard definitions pointwise; `θ∈physV` yields raw `XiCRaw`, and real interpolation gives `‖s‖<corrU`. **Refuted on the quantified carrier**; global equivalence was not claimed. |
| R3 “`Fk`/`E` read remote `φ`” | Expanded `eTermFun→D2raw→d1Triple`; W591 proves equality of the full `d1Triple` raw datum before applying arbitrary `Fk,E`. **Refuted**. |
| R4 “prefactor chooses a scale-dependent `C` or new family” | Checked binder order and proof `obtain` chain at W586 lines 31–49,327–347. **Refuted**. |
| R5 “`IsPolyDom` directly supplies `localB` alignment” | Tried main `IsPolyDom.block_closed`; it needs `L^m₀∣N₁`, `j≤k` and only states `jBlock` closure. Larger `M₁L^j` closure is plausible from aligned `ChosenOne` boxes but absent as a theorem in W597. **Survived** as an interface finding L4b. |
| R6 “the observable record accepts any `q≤1` tower family” | Tried `physVq_subset`; it points from the smaller carrier to `physV` and cannot extend analyticity/locality. `physVq_one` resolves only `q=1`. **Survived** as finding L5b. |

## L6. Suggested docstring caveats (no source edits)

1. **W587 `e1Mark_hG_rawY_fromTower`**: “This proves the exact mark premise for the exported pair on `physV`; exact locality of the assembled coefficient also requires the activity premise.” (`E1CoeffFamily.lean:233–303`.)
2. **W591 `eterm_expansion_hat_rawY`**: “Exact locality holds for this old-term expansion on the global admissible fan; it does not identify a local-generator chart or all physical summands.” (`SharpENu.lean:232–272`.)
3. **W597 `localB`**: “This is the transported minimal generating-set formula; applying its top-layer specification to `IsPolyDom` requires a separate aligned-polymer bridge and the ambient divisibility hypotheses.” (`LocalGeneratorSource.lean:38–46,102–144`.)
4. **W598 `levelCoversG_of_dvd`**: “Divisibility is the only size assumption on `N₁`; the theorem also assumes `DGSetting`, a whole-level `Gp`, and `m₀≥1`.” (`LevelCoversG.lean:63–71`.)
5. **W590 `renM0_siteRecord_of_family`**: “The input coefficient is analytic and exactly local on `physV`; a tower family on `physVq` supplies this directly at `q=1`.” (`RenormM0SiteRecord.lean:34–57`.)

**Closeout and limits.** All five requested lanes were classified against frozen source and adversarially checked. The two surviving findings are integration caveats with explicit proof obligations; neither invalidates the conditional declarations. No build, axiom census, full proof audit, merge check, or source edits were performed; the report should be rechecked after branch integration.
