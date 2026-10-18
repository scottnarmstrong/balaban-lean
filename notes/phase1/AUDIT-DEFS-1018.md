# Audit of the definitions landed on 17-18 October 2026 (W1061)

Posture: refute first. Each definition is read in its exact Lean body, compared with the cited source,
and tried against its whole carrier. Verdicts: FAITHFUL (literal on the whole carrier),
WITH-NOTE (a harmless convention, named), DEFECT (the definition, or a bundled hypothesis, does not
mean the source object, or breaks hard rule 4).
Worktree: `/home/scott/Balaban-worktrees/W1061`, branch `w1061-audit`, base = current `main`.
Sources read: P5 pp. 488-489 (1.4) and p. 521 (3.18); P7 p. 496 (1.5)-(1.6), pp. 527-531
((3.26), (4.1)-(4.7)); notes `astra/ALIGNED.md` Round 4 (the copy in
`/home/scott/Balaban-scratch/astra-aligned/ALIGNED.md`; the copy under `notes/phase1/astra/` stops at
Round 3, so Round 4 is not committed), `astra/SFFAM.md` Parts 2-3, `astra/XIDOM.md`, `PLAN-B.md` R6,
`LF4R-PLAN.md`, `Q13-YM.md` section 5, `astra/RADIUS.md` (11), `CROTE.md`.

## Verdict table

| Definition | Verdict |
|---|---|
| `gasLinkedActive`, `gasLinkedA`, `gasLinkedW`, `gasLinkedXi`, `gasLinkedK` | WITH-NOTE (empty activation set is never active) |
| `RopC` | WITH-NOTE (division by zero gives 0, as for `Rop`) |
| `rhoSigma` | FAITHFUL |
| `hOpMeasure` | WITH-NOTE (a name for `Measure.pi`; physical measure is an argument) |
| `r4Coupling` | FAITHFUL (algebraic; `fresh` is an argument) |
| `r4Fresh` | WITH-NOTE (matches Round 4 (40); the physical extension `F` is an input) |
| `finalSelectedGenSet`, `finalSelectedDatum` | WITH-NOTE (`Q*ψ_k` is read as the block lift) |
| `oldTorusEquiv`, `liftOldField`, `lowerNewField`, `liftOldPoly`, `liftOldSites` | FAITHFUL |
| `liftOldGS`, `liftOldTerms`, `liftOldTermsFam` | WITH-NOTE (layers above `k` are discarded, top layer empty) |
| `birthXiDom` | WITH-NOTE (only the mass is frozen; kernel sequence is that of scale `k`) |
| `transportField` | FAITHFUL |
| `pieceWindowSetupOfFamily` | WITH-NOTE (bundling of caller-supplied data) |
| `stepVacuumTerm`, `stepVacuumVolume` | WITH-NOTE (literal (3.18); volume identity with `Z_{k+1} \ Z_k` is false in general; docstrings overclaim) |
| `StepData.vacE`, `vacEpp`, `vacEppp`, `b0`, `b_vac`, `b0_bound` | WITH-NOTE (data fields; `b0` is determined by `b_vac`) |
| `StepData.VacuumTie` | FAITHFUL (inhabited by `vacuumTie_zero`) |
| `OpConsts.muBg` and its uses | WITH-NOTE (default `muBg := mu`) |
| `DataDirClose`, `ChiKLongProp`, `chiKLong`, `dirRadius`, `chiY` (new body) | WITH-NOTE |
| `srcTube`, `KerBoundSrc` | WITH-NOTE (`<=` instead of `<`) |
| `locDataC`, `locBgC`, `mainActionLocC` | FAITHFUL |
| `kf0CovAtom` (W1005) | no definition exists; only theorems (the atom is written inline) |
| `Def6v2.CRotE` | **DEFECT** (bundled hypothesis carrying an unproved step; may be unsatisfiable) |
| `IsRot` (redefined), `IsCRot`, `rotM` clause change | WITH-NOTE |
| `quietSharp` | WITH-NOTE (defined by dividing out the action) |
| `removedK`, `removedKernel`, `toRKernel`, `remDecomp`, `remDen`, `remNum`, `remZeroSplit`, `remZeroMerge`, `OutZero`, `OutRest`, `remUnitEquiv` | WITH-NOTE (zero denominator gives 0) |
| `dataRH`, `actionZ`, `rhoZeroRestrictedWith`, `rhoZeroRestricted`, `tildeE0Restricted` | FAITHFUL |
| `famDecompOf`, `famDecomp` | FAITHFUL |
| `famRhoRestricted`, `famDecompRestricted` | WITH-NOTE (value 0 off the tube; measure is restricted to the tube) |
| `psi0H`, `Phi1H`, `E1locH`, `E0locH`, `M0H` | WITH-NOTE (fibre theorems; `fderiv`/`deriv` junk off differentiability) |
| `E1locJ`, `rootTraceJ`, `E0locJ`, `M0J`, `densE0`, `densM0` | WITH-NOTE (same; analytic representatives) |
| `PieceWindowSetup`, `pieceChain` | WITH-NOTE (mass branch: `muBg` at the first scale, `muAct` after) |
| `cellCount`, `nodeEquiv`, `tailW` (private) | FAITHFUL |
| `AnalyticFam`, `soParam`, `rotExp`, `soCoord`, `rotCay`, `boost3`, `sig`, `gs`, `specMat`, `nsq`, `cayMat`, `sigC`, `lamC` | FAITHFUL (matrix utilities; inverses used only under `IsUnit` hypotheses) |
| `irrelTorus` | not re-audited here (earlier audit); no change found against its docstring |

One DEFECT: `CRotE`. Details at the end.

---

## 1. Polymer/GasLinked.lean (W990)

Files: `Balaban/Polymer/GasLinked.lean`, `GasLinkedEq.lean`. Source: P7 after (4.11) (Mayer expansion),
KF0B Theorem B.7 note (activation set `{a,c}` disconnected, footprint `{a,b,c}` connected).

Refutation attempts.
- Empty activation set: `gasLinkedActive` is false in both modes (all-required demands `Nonempty`;
  intersection mode demands a non-disjoint pair). A coupling with no activation block is therefore
  never selected and never contributes `β y`. This is a convention, not a fallback of the source object:
  the landed `gasXi` behaves the same for `cy y = ∅`.
- Consistency of `gasLinkedXi` and `gasLinkedK`: `gasLinked_eq` proves
  `gasLinkedXi = Xi (shareBlock) (gasLinkedK)` under `activation ⊆ footprint`, `zs z` nonempty,
  `cr z ⊆ zs z`. These are typing premises. Without `activation ⊆ footprint` the equality can fail
  (an activated coupling would not be connected to its heavy objects); the theorem states it.
- Reduction to the landed gas: `gasLinkedActive_intersection_eq`, `gasLinkedA_intersection_eq`,
  `gasLinkedXi_intersection_eq`, `gasLinkedK_intersection_eq`, `gas_eq_of_gasLinked_eq`. These are the
  unfolding lemmas the rules require, all present.
- `gasLinkedActive_pair_iff` checks the three-block example.

Verdict: FAITHFUL-WITH-NOTE. Note: empty activation never active. `gasLinkedXi` does not take the
footprint, only `gasLinkedK` does; the link between them is `gasLinked_eq`. The object is a design
generalization (separate activation and footprint), not a literal P7 object; P7 uses the intersection
mode (`gasLinkedK_intersection_eq`).

## 2. Large-field R4 definitions (W1001, W1007)

Files: `LargeField/R/RGasRepR4Complex.lean`, `RGasRepR4Term.lean`, `RGasRepR4Measure.lean`,
`RGasRepR4Decor.lean`, `RGasRepR4Fresh.lean`. Source: P7 (1.3)-(1.6) pp. 495-496, (3.22)-(3.28)
pp. 526-528.

`RopC`. P7 (1.6): `R ρ = Σ ρ_{k,0}(Z) · ∫ ρ'' / ∫ ρ_{k,0}`. `RopC` is
`∏ r · (∫ ρ ∘ e⁻¹ / ∏ ∫ r)`, the same decomposition and reference densities as the landed `Rop`.
Refutation: the Bochner integral is 0 when `ρ` is not integrable and a zero denominator gives 0.
Both are off the source's carrier (the source assumes a positive denominator and an integrable
density) and identical to `Rop`. Characterization: `RopC_apply`, `RopC_ofReal` (agrees with `Rop` on
real densities), `RopC_congr`, `RopC_zero`. Verdict WITH-NOTE (junk values off integrability and
positivity, shared with `Rop`).

`rhoSigma`. Integral over the internal variables of `gWeight · (∏_{i ∈ ripe} ROutcome.weight ...) ·
integrand`. This is the term `ρ(𝔸,σ)` of (1.3)-(1.6): the outcome weights for ripe components,
the unsplit kernel elsewhere. `ripe` and `σ` are arguments, as in the source, where they index the
sum. `rhoSigma_eq_gOp` unfolds it. FAITHFUL.

`hOpMeasure`. `Measure.pi μ`, with `hOpMeasure_eq_pi := rfl` and the probability instance. It carries
no content beyond the name; the source's reference measure (3.26)-(3.28) is the normalized
`ρ_{k,0}`-measure and is the argument `μ`. WITH-NOTE: no physical instance of `μ` is constructed here.

`r4Coupling`. `old x S - kept x + fresh x S`. Source (3.26) p. 527: the exponent
`B(Y ∪ ∪Z_i, A'') - B(Y, A'' ∩ Y) + B'(Y ∪ ∪Z_i)`, with the terms of disjoint domain cancelled.
Checked against the printed text: the Lean formula is the per-domain form. `r4Coupling_empty`
(vanishes at `S = ∅` under `old x ∅ = kept x`, `fresh x ∅ = 0`) and `gasR4Decor_eq` (the literal gas
identity, via `gasDecor_eq`) are present. FAITHFUL; `fresh` is an argument.

`r4Fresh`. `evTerm c G m₀ X₁ (F S) Y u`, the P3 mixed-derivative coefficient summed over connected
cut families with final domain `Y`. Compared with `ALIGNED.md` Round 4, (39)-(43) and section 4.4:
it is exactly the "one `evTerm` definition on a specified combined extension `F_S := Σ_q F_{q,S}`".
The note's (40) sums over `q` outside; the Lean folds the sum into `F` (linearity,
`evTerm_sum_linear`), as the note says in section 4.1.
The aggregate identity P7 needs is `Σ_X B'_X(Γ_X; u) = Δ_Γ(u)` (43). Lean gives
`r4Fresh_aggregate_of_localization`: `F S u 1 = Σ_Y r4Fresh ... S Y u` plus data locality, the
bound (42), and analyticity, and `r4Fresh_congr_cut` for the replacement of `S` by the members
meeting `Y` (41). Together these are (43), but only for an `F` that satisfies the P3 analytic,
cut-locality and geometry premises, and with `F S u 1 = Δ`. The physical `F` (the four P7 differences
in the decoupled functionals) is not constructed anywhere; `Rep` does not provide it. So the
definition is faithful to the chosen construction and does not by itself give P7's `B'`.
Free choice check: `F` is a visible argument, not a hidden choice. The condition `fresh x ∅ = 0`
needed by `r4Coupling_empty` is not a consequence of `r4Fresh_aggregate_of_localization`; it must be
arranged by `F ∅ ≡ 0` (note, 4.1). Verdict WITH-NOTE. Downstream: only the R4 files
(`RGasRepR4Operator`, `RGasRepR4Pointwise` and the gas identity); no theorem states a claim about the
physical `B'`, so none becomes misleading.

## 3. Green/FinalSelectedDatum.lean (W1013)

`finalSelectedGenSet C Zk := C.genW Zkᶜ`, `genW = genSF (W2 R ·)`, `W2 R Y = thick ⌊R(k-1)⌋ (thick ⌊R(k-1)⌋ Y)`.
Source P5 p. 489 (1.4): `W_k = (Z_k^c)^{≈2}`, `ψ̃_k = Q*(T_1^{(k)}, B_k(W_k)) ψ_k`; P7 p. 530 (4.3)-(4.6)
uses `B_k(W_k)`. The thickening `≈` is by `M R_{k-1}` in `ξ`-scale, i.e. `R_{k-1}` cubes; `W2`
applies it twice. Matches.
`finalSelectedDatum` is `liftSingle` of `lift_k ψ_k` with constant `h`, clipped to the data sites.
Note: the source datum is `Q*(B_k(W_k))ψ_k`, an adjoint of the averaging operator (P2 `Q*`), and the
Lean reads it as the block lift of `ψ_k`, the identification used by the older `SFCtx.phiK` (P5 (1.4),
Def II.2.7 (iii)). I did not re-derive `Q*ψ = lift ψ` from P2 (the P2 text layer is garbled); it is the
same reading as in already landed code. Unfolding lemmas: `finalSelectedGenSet_eq`,
`finalSelectedDatum_eq`, `finalSelectedDatum_Ψ`, `finalSelectedDatum_h`. Verdict WITH-NOTE.
`Zk` is the old region `Z_k`, as the docstring says, not `Z_{k+1}`.

## 4. Fluctuation/OldTermsLiftGeom.lean (W985)

`oldSide_eq_newSide`: `((L N₁) L^{m₁}) L^k = (N₁ L^{m₁}) L^{k+1}`, so the fine sites coincide;
`oldTorusEquiv` is the cast. `liftOldField`, `lowerNewField` are mutually inverse
(`lowerNewField_liftOldField`, `liftOldField_lowerNewField`); `liftOldPoly` is the image,
`liftOldSites` the map; membership lemmas `mem_liftOldPoly`, `mem_liftOldSites`;
`oldTorusEquiv_val` (coordinates unchanged), `oldTorusEquiv_jBlock_iff` (`j`-blocks agree for `j ≤ k`).
FAITHFUL.
`liftOldGS`: `Ω j` is the image for `j ≤ k` and `∅` above. Refutation: the old set may have junk
`Ω j` for `j > k + 1` (only `j ≤ k` constrained by `subset`); the new set drops it, and
`liftOldGS_Ω` is stated only for `j ≤ k`, so no claim is lost. The new top layer `Ω_{k+1} = ∅`: the
separation field is vacuous there. `liftOldGS_mem_layer`, `liftOldGS_layerIndex` show layers and layer
indices agree on `Ω 1`.
`liftOldTerms`: `E`, `M`, `gs` pulled back pointwise on the whole carrier
(`liftOldTerms_E`, `liftOldTerms_M` are `rfl`); locality clauses transported
(`liftOldTerms_localE`, `liftOldTerms_localM`). `liftOldTermsFam`: family at `L N₂` read at `N₂`
(`liftOldTermsFam_apply`). The meaning of the old data as scale-`k+1` data is a relabeling only; the
scale-dependent constants live in `P` and `Dom`, outside `Terms`. Verdict for `liftOldGS`,
`liftOldTerms`, `liftOldTermsFam`: WITH-NOTE (layers above `k` discarded; top layer empty; the rest
of the transport of the class clauses is stated as not yet proved in SFFAM Part 3).

## 5. SmallField/Def6v2Birth.lean (W1003, ruling R6)

`birthXiDom P Rg a N₁`: `phys := Set.univ`, `dom j G Ψ h := XiDom G (aIdeal L k (a k)) (physMass L j (Rg.ν j)) j (P.eps d L j) Ψ h`.
Ruling R6 (PLAN-B): domains frozen at the birth mass of each level; birth mass at level `j` is
`μ_j = ν_j L^{-2j}`. This is `physMass L j (Rg.ν j)`. At `j = k` it is `completeXiDom`
(`birthXiDom_dom_self`, `Iff.rfl`), which is the correct top-level case.
Refutation attempts. (1) The mass is the physical mass at every level, not `bgMass` (which is `0` for
`k ≤ k₀`); consistent with `completeXiDom` (`Rg.sfBgMass k = physMass`). (2) The kernel sequence is
`aIdeal L k (a k)`, the current scale's, not frozen at the birth scale: R6 and PLAN-B speak of the
mass only, and `birthXiDom_dom_congr` makes the equality of kernels an explicit hypothesis when
transporting. A kernel that varies with the scale would not be frozen. (3) `ε_j = P.eps d L j` depends
on `j` only; fine. (4) `phys = univ` as in `completeXiDom`.
Verdict WITH-NOTE: only the mass is frozen. If the transport to the next scale changes `aIdeal L k (a k)`,
`birthXiDom_dom_congr` needs `aIdeal L k (a k) = aIdeal L k (a' k)`, which is a premise the next-step
construction must meet; it is not automatic. Characterization lemmas present (`_phys`, `_dom_iff`,
`_dom_self`, `_dom_congr`).

## 6. WindowConvPhysRead / WindowCompose (W1023, W1006)

`transportField e Ψw φw := fun p => barField Gw Ψw φw (e.symm p.1) p.2`, the extension of `φw` by the
data `Ψw` read at `e⁻¹`. This is the transported field of P7 p. 501 (2.14)-(2.16) / P6 (2.13)-(2.16).
No choice, no fallback beyond `barField`'s own convention (data outside `Ω₁`). Characterized by
`transportField_barField`, `transportField_svec`, and the action-transport theorem in the same file.
FAITHFUL.
`pieceWindowSetupOfFamily`: a structure literal. Every field is either a caller argument (`ak`, `νk`,
`βk`, `Datw`, `φw`, `br`, `chain`, `decomp`, `Xc`) or fixed by the geometry
(`N₀c := M1 (c n(j+1))`, `Kc := j+1`, `Gc := locGen ...`, `mcount := (decomp i).total`). It makes no
claim by itself. `PieceWindowSetup` has no `Prop` field that could make it empty beyond geometry
facts proved from `hjf`, `hcf`, `hinj` (`Xw_disj` by `pieces_regions_disjoint`). WITH-NOTE (bundling).

## 7. StepData vacuum clause (W1002, W1018, ruling R5)

Fields (StepData.lean): `vacE`, `vacEpp`, `vacEppp : ℕ → LocalHistory → ℝ`, `b0` (complex-valued
remainder), `b_vac : b = b0 - stepVacuumTerm ...`, `b0_bound`.
`stepVacuumTerm a k Ek Epp Eppp = Ek |Z_{k+1}∖Z_k∖Ω_k|_k + Epp |Ω∖Ω''|_k + Eppp |Ω''∩Z_{k+1}|_k`
with `a.Omega k`, `a.OmegaDD k` the localized `Ω_{k+1}`, `Ω''_{k+1}` of step `k`.

Source: P5 p. 521 (3.18): `-E_k L^d |Z_k^c ∖ Ω_{k+1}| - E''_k L^d |Ω_{k+1} ∖ Ω''_{k+1}| - E'''_k L^d |Ω''_{k+1}|`
(volumes in the `L^{-1}η`-scale, hence the `L^d`, which `volScale S k` absorbs). The Lean form
is this expression restricted to the local history of the component `Z'`, with the first and third
region cut by `Z_{k+1}` and `Z_k`. The plan (`LF4R-PLAN.md`, W968 vacuum) calls the three regions "a partition
of `Z_k^c ∩ Z_{k+1}`" and the docstrings of `StepData.b_ref_bound`, `VacuumTie.b_backward_bound`
use "the geometric identity `stepVacuumVolume = |Z_{k+1} ∖ Z_k|_k`".

Refutation of that identity. With `Ω'' ⊆ Ω` (`OmegaDD = Op_1(F''; Ω)`) and `Z_k ⊆ Z_{k+1}`, restricted
to the localized fine set `Z'`:
`stepVacuumVolume = |Z'∖Z_k∖Ω| + |(Ω∖Ω'')∩Z'| + |Ω''∩Z'∩Z_{k+1}|`. Only the first region excludes `Z_k`.
So `stepVacuumVolume = |Z'∖Z_k| + |Ω ∩ Z_k ∩ Z'|` (when `Ω'' ⊆ Z_{k+1}`, as `Ω'' ⊆ F^Z ⊆ Z^{(0)}_{k+1}`).
In the Lean region definitions `Ω = Op_1(P^{~3}; Ω')`, `Ω' = Op_{ρ+2}((U'_k)^{~3})` and `U'_k` is a
neighbourhood of `Z_k` (`RegionStep.Uprime`), so `Ω_{k+1}` contains parts of `Z_k` by construction. Hence
the equality fails whenever `Ω ∩ Z_k ∩ Z'` is nonempty, and `stepVacuumVolume` can exceed
`|Z_{k+1}∖Z_k|` by a quantity that is not controlled by it. This is the volume question of W1018, and it is
real. I could not decide from the P5 text layer whether P5's `Ω_{k+1}` in (3.18) is contained in `Z_k^c`
(in which case the source's partition is of `Z_k^c`); the Lean `Omega` is built as in P7 (R4)-(R5) and is not
contained in `Z_k^c`.

Consequences. (a) `stepVacuumTerm` is the literal three-region formula, so I do not call it a DEFECT:
`b_vac` is satisfiable (`b0 := b + stepVacuumTerm`, and the witnesses in `QuietWitness`, `Def7WitData`,
`QuietLocalInput` use zero constants), and `vacuumTie_zero` inhabits the tie. (b) `b0_bound` bounds `b0`
by `(C_b log β_k + C_b B_0)|Z_{k+1}∖Z_k|_{k+1}` with no vacuum constant; whether the true `b0` satisfies
it depends on how the producer chooses regions. (c) The statements `b_ref_bound`, `b_backward_bound`
are correct as written (they carry `stepVacuumVolume` explicitly). Their docstrings claim the `O(log β_k+1)`
per-block conclusion "using the geometric identity", which is not proved and is false in general.
Recommendation: either prove `stepVacuumVolume ≤ C |Z_{k+1}∖Z_k|_k` from the region definitions for the
histories used, or restrict the second and third regions to `Z_{k+1} ∖ Z_k` (and say so), and correct the two docstrings.
`b0` is determined by `b_vac` (it is `b + vacuum term`), so `b0` as a "free data field" has content only
through `b0_bound`.

`StepData.VacuumTie`: `vacE = E k`, `vacEpp = E k + dpp k`, `vacEppp = E k + dppp k` on a set `T`.
Inhabitation `vacuumTie_zero` (rule 10). The offsets `dpp`, `dppp` are free functions, so the tie
does not say they are the offsets of P4 (2.41), (2.63) (`δ''`, `δ'''`); the docstring states this identification as
the producer's burden. FAITHFUL as a Prop; the physical identification is not enforced.

## 8. Ruling R2 (W1029)

`OpConsts.muBg` (default `mu`). Three masses: `mu` (cutoff, sharp characteristic functions),
`muBg` (backgrounds), `muAct` (actions). Refute: the default `muBg := mu` is a structure default, not a
branch inside a definition; the route R-YM' sets `muBg = muAct` through the class clause
`Def7.FieldClauses.muBg_eq`. Spot checks of the uses: `locBg`, `mainActionLoc`, `locBgC`, `phiK`,
`psiJ`, `Theorem42WireAction`, `Quiet`, `QuietStepData` read `muBg` for backgrounds; the characteristic
functions (`chiK`, `chiY`, `TopBlockTransport`, `BondLiftY`, `KeptOutcomeThreeSupport`) keep `mu`, which is right: they
evaluate their own background at the cutoff mass. `pieceChain` uses `muBg (j+1)` for the first scale and
`br.elMass (muAct m)` after; coherent when `muBg = muAct` at the first scale (hypothesis `hB0`).
A full check of all uses was not made (about 35 files mention `muBg`). Verdict WITH-NOTE.

`DataDirClose Ψ h ν S δ`: for `ν > 0`, `|Ψ x - h| < δ/√ν` on `S` and `|h·h - 1| < δ²/ν`; vacuous for `ν ≤ 0`.
This is `FieldClose` with the datum `Ψ` in place of the background `φ̄`, so it reaches collar sites outside
`Ω₁`. `dataDirClose_congr`, `dataDirClose_of_nonpos` present. `ChiKLongProp ρ`: `ChiKProp ∧ DataDirClose`
on `cubeNbhd ... ρ y0` with dimensionless mass `μ L^{2q}`, the same normalization as `RegIneq`.
`chiKLong` is `charFn`. `chiY` is `cubeProd` of `chiKLong` with `ρ = dirRadius R k = 2⌊R_{k-1}⌋ + 3`,
matching `Q13-YM.md` section 5 leaf 4 ("neighbourhood of `2R_{k-1}+3` cubes", P5 (1.19) with the
direction test extended). At `μ = 0` it is the old `chiK`. Notes: `dirRadius` uses `R (k-1)`, so at
`k = 0` it reads `R 0` (natural subtraction); `k ≥ 1` in all uses. `|h·h-1|` is tested twice
(once in `FieldClose`, once here) with the same `δ`; harmless. WITH-NOTE.

`srcTube m β c hv = {h | Σ |m (h_i - hv_i)|² ≤ c² m/β}`. `RADIUS.md` (11) has strict `<`. The closed tube
is a slightly larger set, so `KerBoundSrc` over it is a slightly stronger requirement; no consequence for
the use. For `m < 0` or `β ≤ 0` the tube can be empty; `ofReal_mem_srcTube` carries the premise.
`KerBoundSrc`: `∫⁻ ofReal (Kc(·, hv) · exp(Re bc(·, s, g)))` over the output and internal variables is at most
`e^{-κ}`, for every real field, every `s ∈ D hv`, every `g` in the `ℓ¹` ball; the sharp kernel is read at the
real field. Same shape as `KerBound` (`kerBound_of_kerBoundSrc` reduces to it), satisfiable
(`kerBoundSrc_zero`), monotone. WITH-NOTE.

`locDataC`, `locBgC`, `mainActionLocC`: the datum with a complex constant source on `Ω₁`, the complete background
at mass `muBg (k+1)`, the star cube action at mass `muAct (k+1)` times `β^{(k+1)}_0`.
`locDataC_ofReal`, `locBgC_ofReal` are `rfl`; `mainActionLocC_ofReal` equals the real `mainActionLoc` under
`BgHyp` and `InUnionDomainC`; analyticity `mainActionLocC_analytic`. FAITHFUL.

## 9. Green/KF0CovarianceAtoms.lean (W1005)

No definition is added. The atom `a^{-2n-2} Aⁿ (a I + A) Aⁿ` (`a = 2d + ν`, `A = kf0Adj`) is written inline in
`kf0CovAtom_form_nonneg` and `kf0CovAtom_posSemidef`. I checked the algebra: the even and odd terms
`a^{-2n-1} A^{2n}` and `a^{-2n-2} A^{2n+1}` of `(aI - A)^{-1} = Σ a^{-m-1} A^m` add to the atom
(KF0B (B.22)-(B.23)). Nothing to audit as a definition.

## 10. Other definitions added since 2026-10-17

Found by `git diff 00251520..HEAD -- Balaban` (added `def`/`abbrev`/`structure`/`instance` lines, 566 new
files). Listed with their verdicts in the table. Notes on the ones that need one.

`Def6v2.CRotE`: see the DEFECT below.

`Def6.IsRot` and `IsCRot`. `IsRot` was "real orthogonal or `det = 1`"; it is now real orthogonal (`Rᵀ R = 1` and real entries),
the form of P1 (H.4) and P4 (H.3). `IsCRot` is the old notion; `IsRot.isCRot` present. The `rotM` clause of
`SFTermClauses` gained `l1 g < 1` and `l1 (rotField R g) < 1` (source domain `‖g‖₁ < 1`; a rotation preserves
the norm of each site vector, so the second is redundant for an `ℓ¹` norm of Euclidean norms). The clause is weaker
in carrier, matching the source. WITH-NOTE.

`quietSharp := quietKernel * exp(mainActionLoc)`; `quietKernel_eq_sharp` recovers the kernel. Defined by dividing
out the action rather than as the product of the sharp factors; the characterization theorem makes it the sharp
product (Gaussians, characteristic functions, real-domain indicator). WITH-NOTE.

`RRemovedKernel` (`removedK`, `removedKernel`, `toRKernel`, `remDecomp`, `remDen`, `remNum`): P7 (3.7) on `χ_{Z''}`:
`e^{EZ} u c₀ ∫ K^pre ... / ∫ r`. `u`, `c₀`, `r`, `EZ`, `t`, `s`, `z`, `w` are arguments (the values of `χ_{Z''}`,
`χ_{Z₀}`, `ρ_{k,0}`, `E_k|Z|_k`, and the four small-field functions). Characterization:
`Rop_remDecomp_removed`, `Rop_remDecomp_removedKernel`, `removedK_eq_outcomeKernel`, `removedKernel_K`,
`removedKernel_b`. A zero denominator gives kernel value 0 (division in `ℝ`); the source assumes a positive
denominator. `EZ = 0` is P7's `T''_k(Z) χ_{Z''}`. WITH-NOTE.

`RhoZeroRestricted` (`dataRH`, `actionZ`, `rhoZeroRestrictedWith`, `rhoZeroRestricted`, `tildeE0Restricted`):
P7 (1.5) `ρ_{k,0}(Z) = χ_{Z₀} exp(-β_k A*_k(Z; ψ_k, φ_k(B_k(U_k); ψ̃_k)))`, action restricted to `Z` with the
half-bond convention on `∂Z`, massless background, `C₆ = 3dD₀(K₆+1)`, centre `ψ⁰_k`. Characterized by
`rhoZeroRestricted_eq_mul` (relation with the landed `rhoZero`), `rhoZeroRestrictedWith_eq_zero`,
`..._of_cutoff`, `denominatorRestricted_eq`; `tildeE0Restricted` is defined by the identity of Lemma III.8.2 and
the identity is proved with positivity. FAITHFUL. The file records the open oscillation bound honestly.

`famDecompOf`, `famDecomp`, `famRhoRestricted`, `famDecompRestricted`: the generic `RDecomp` of a family of
reference densities. `famRhoRestricted` has an `else 0` branch off the tube `FamTube`. The `RDecomp`'s measures
are restricted to the tube (`volume.restrict famTubeSet`, `νY` restricted to good `y`), and the source defines
`ρ_{k,0}(Z)` only for `ψ_k` in `Ψ̃(X∖Z₀; δ)`, so the branch is a total extension outside the carrier and is not
read. `famRhoRestricted_eq_rhoZeroRestricted` gives the value in the tube. WITH-NOTE.

`psi0H`, `Phi1H`, `E1locH`, `E0locH`, `M0H` and `E1locJ`, `rootTraceJ`, `E0locJ`, `M0J`, `densE0`, `densM0`: the new
local densities of P4 (2.53), (2.56)-(2.60) at a block datum with a complex non-constant field, and as functions of
the raw datum. Fibre theorems (`psi0H_fibre`, `Phi1H_fibre`, `shift_fibre`, `E1locH_fibre`, `E0locH_fibre`,
`M0H_fibre`) show they are the landed `E1locC`, `E0locC`, `M0C` when `θ.h ≡ h₀`; `_datum` theorems tie
the `J` forms to the `H` forms on the chart. They use `fderiv`/`deriv`, which are 0 where the function is not
differentiable; differentiability is supplied by the analyticity hypotheses where used. WITH-NOTE.

`PieceChain.pieceChain`: see section 8 (mass branch). `e m = (β_{m-1}ν_{m-1} - β_m ν_m)/ν_m` with `ν_m = muAct m`; division
guarded by `hμ : muAct m ≠ 0`.

`cellCount`, `nodeEquiv`, `tailW` (private abbreviation `1/4` on `Z`, `1/2` elsewhere, used for the tail bound),
the rotation utilities (`AnalyticFam`, `soParam`, `rotExp`, `soCoord`, `rotCay`, `sig`, `gs`, `specMat`, `nsq`, `cayMat`,
`sigC`, `lamC`, `boost3`): literal. `rotCay`, `cayMat` use `Matrix.inv`; lemmas carry `IsUnit` hypotheses.

---

## DEFECT: `Balaban.SmallField.Def6v2.CRotE`

File `Balaban/SmallField/Def6v2.lean` (added with W869, 2026-10-17).

Body: for all `j` in `[1, k]`, polymers `X` of `𝒟_j`, `y ∈ X`, every complex matrix `R` with `IsCRot R`
(`Rᵀ R = 1` and real entries or `det R = 1`), every pair `(Ψ, h)` with `(Ψ, h)` and `(RΨ, Rh)` both in
`Dom.dom j (Tm.gs j X)`: `Tm.E j y X (RΨ) (Rh) = Tm.E j y X Ψ h`.

Discrepancy.
1. The source has the invariance under real `O(N)` only (P1 (H.4), P4 (H.3)); the class clauses
   `SFTermClauses.rotE` now state exactly that (`IsRot` real). Complex invariance follows by analytic
   continuation along a path of rotations inside the domain. `CRotE` asks for it for every `R` relating
   two domain points, with no path. Its own docstring says: "The existence of such a path for the pairs
   `(Ψ, h)`, `(RΨ, Rh)` met by the frame bridges is not proved; this predicate carries it." That is a step
   of the proof used as a hypothesis (hard rule 4).
2. It may be unsatisfiable for the tower class. `notes/phase1/CROTE.md` section 4: "No `hCR : CRotE ...` can
   be discharged as stated (it asks for every `R` relating two domain points; no path in the domain is
   known)". A complex orthogonal matrix relating two points of a domain that is not stable under the rotation
   path need not leave the energy invariant (an analytic function invariant under the real group is invariant
   under the complex group only along connected rotation orbits inside the domain); `boost3` and
   `boost3_far_from_real` (Def6RotFrames) show frames of the landed bridge are far from real.
3. Inhabitation (rule 10): only for members of the landed class `IsSF`, via `cRotE_of_landed`
   (`Def6v2RenormCompare.lean`), because `IsSF.rotE` is stated for `IsCRot`. The class of the renormalization
   step (`SFTermClauses`, real clause only) has no such theorem.

Downstream (grep `CRotE`): 34 files; the hypotheses `hCR`/`hC` occur in about 20 theorems:
`Def6v2Bridge` (lines 259, 373: `isSF_of_termClauses` and the bridges), `Def6v2Renorm`,
`RegionalAlignedSource`, `LayerV2RenormFirst`, `IsSFFamily2.toLanded`,
`IrrelTorusDefectMatrix`, `IrrelTorusDefectFiled(All)`, `IrrelTorusDefectJet`, `IrrelTorusDefectMatch`,
`IrrelTorusDefectBirth*` (Birth, BirthCap, BirthCapMain), `IrrelTorusXidom{Defect,Large,SmallSource,Rotate}`.

Do the statements become misleading? They display `hCR` openly, so nothing is hidden, but any such theorem applied
to the class produced by the renormalization step needs a hypothesis nobody can prove, so the chain from the
tower to the irrelevant-part bounds is conditional (the ledger records this as OPEN-CROTE, 2026-10-17). The
statements are not false, but they are vacuous if `CRotE` is false for the class at hand.

Repair already planned: `CROTE.md` section 4 (and W875: `SFTermClauses.rotE_of_near`, `rotE_of_cay_path`,
`exists_cay_path_near`) replaces the four call sites by the real clause plus a Cayley path for bounded-entry matrices
and removes every `hCR`. Until it lands, the theorems above should not be cited as unconditional.

## Other findings to act on

- `notes/phase1/astra/ALIGNED.md` in the repository stops at Round 3; Round 4 (the source of the `r4Fresh`
  definition) exists only in `/home/scott/Balaban-scratch/astra-aligned/ALIGNED.md`. It should be committed.
- Docstrings of `StepData.b_ref_bound`, `VacuumTie.b_backward_bound` and the plan's "partition of `Z_k^c ∩ Z_{k+1}`"
  claim an identity that is false when `Ω_{k+1}` meets `Z_k` (section 7).
- `birthXiDom` freezes the mass only (section 5); the kernel-sequence equality is an unstated premise of the next-step transport.
