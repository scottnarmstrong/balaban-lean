# AUDIT-5 — joint and assembly statements

Snapshot: `/home/scott/Balaban` at `9a88681c221371c9d58f92986690018303e28de4` (clean working tree), 2026-10-13. This is a source-level audit of the named declarations and their displayed consumers, not a fresh Lean build or a proof of the physical theorem. Verdicts describe the stated scope, with the caveats below.

## E1. Determinant-only renormalization

**FAITHFUL** — `Balaban/Inhabited/RenormHalfDetOnly.lean:39-46,72-93`. The record is `RenormExpInputOn` at `e = R.t / 2`; its `E0θ` is `renE0θ_det (R.t / 2) E`, and the next three function arguments (observable and old terms) are zero. Both the file heading and theorem docstring explicitly say that this is determinant only and is not the physical record (`:14-29,39-46`).

**FAITHFUL** — `Balaban/Inhabited/RenormHalfDetOnly.lean:54-71,159-170,204-219`. The `IsRenSol` witness `F`, the endpoint `Fcut ... 1 = F ...`, the record, and the `C₂` term all use the same existential `F`; the `C₁/C₂` proof passes that record to `thm31g_C1_on` and `thm31g_C2_on`. The explicit conjunct asserting `XiCOneReal ... D'` *and* the field equality proves that this fibre contains the tower datum (`:111-115`). The chart inclusion quantifies over the same step's fibre and yields `XiCData` for that step at radius `R.t` (`:116-124`).

## E2. Common witness

**FAITHFUL** — `Balaban/Inhabited/CommonWitnessJoint.lean:387-428,429-468,468-578,579-665`. For each admissible scale, one `val, 𝒴, Tt` and `hdom` are chosen before the value formula, amplitude bound, per-source real/complex activity bounds, segment representation, zero/source activities, direct terms, ray regularity, the ray-premise tuple, and the observable representation. The segment `Jr`, the direct-terms `Jr, I`, and the observable `Jr, I` occur in separate existential conjuncts (`:429,468,579`); equality of those separately chosen objects is not claimed. Their relevant `I` instances are tied to the common `𝒴,Tt` by `I.𝒴 = 𝒴` and `I.T = Tt` (`:468-474,579-665`).

**FAITHFUL** — `Balaban/Inhabited/CommonWitnessJoint.lean:404-414,560-578`; `Balaban/Inhabited/ObsMarksFromTower.lean:276-310`. Projection of the value formula and the `:560-578` tuple gives exactly the one-scale clause list required by `obsMarks_zeroClass_family_of_ray`'s `hray`: `hval`, diagonal continuity, a `DirectTerms` instance at every slice point with the same `𝒴,Tt`, base membership, membership for every source in the strict unit `ℓ¹` ball, and the holomorphic ray on the hat disc. The construction takes these clauses from one source witness (`CommonWitnessJoint.lean:692-700`). The consumer's `hray` still universally quantifies over scales; this theorem supplies the scale-wise witnesses under its displayed assumptions.

## E3. Corrected-mark family

**FAITHFUL** — `Balaban/Inhabited/DecMarkCorrFamilyFromTower.lean:34-50,64-122,181-202`. The order is `∃ F₁ Sol, ∀ zr`; the datum `Θ`, complex `um`, and configuration `Φ` are still farther inside. The pair record, output count/support/bridge identity, and correction fields all use `F₁ (zr,b), Sol (zr,b)`, with the proof passing those same functions to the count and field lemmas (`:181-202`). The count and correction bound use `Θ ∈ XiCRaw ... T.t` and `‖um‖ ≤ corrU` (`:64-106`). This is the raw chart, not an unrestricted datum.

**FAITHFUL** — `Balaban/Inhabited/DecMarkCorrFamilyFromTower.lean:36-38,119-122,131-149,190-202`. Analyticity is on an open ball of radius `corrR`; `corrR > 0` and `2*corrU ≤ corrR` put the closed `corrU` disc strictly inside it. The proof uses precisely these radius hypotheses in the count and field bounds.

## E4. E1 bridge and numerical budget

**FAITHFUL** — `Balaban/Inhabited/E1LabelsBudget.lean:52-78`. For every root, the empty connected family gives an `X₁` label whose bridge contains the root site; the displayed `bridgeFamily` is nonempty, so the sum is not empty by construction.

**FAITHFUL** — `Balaban/Inhabited/E1LabelsBudget.lean:106-115,123-141,147-166`; `Balaban/Fluctuation/RootMarkedBound.lean:227-234`; `Balaban/Fluctuation/Thm31CoeffB.lean:260-262`. The numerical inequality has the consumer's `CPE 3 3 Kc κH κ0 κ'` shape with `Kc = T.marksKc'`, `κH = 2*T.κdec-1`, `κ0 = T.κ0`, `κ' = T.κ'`, weight `exp (-κ0*treeLenCovOne ...)`, and target `K0 3 3 κ0`. `exists_beta0_e1` chooses one threshold before all `k,N₁,ν,β,p₁,z`, and also supplies `2*corrU ≤ corrR` (`:147-166`). This establishes a numerical budget template; applying it to an `InterpMarks` record still requires identifying that record's labels, coefficients and parameters with this template.

## E5. Observable labels and clamped first-order mark

**FAITHFUL, with scoped null-set caveat** — `Balaban/Inhabited/ObsTiltLabels.lean:297-331`. At fixed scale and `q`, `Lb, Lab, εH, A` are selected before the observable label system `𝒴obs`, the datum `D'`, and the source `g`. The first almost-everywhere assertion places `∀D',g,t,𝒴obs,Kobs` *inside* one `∀ᵐ x ∂S.nuFl`, including both ordinary and tilted activity identities. The later `hW` style clause has `∀r, ∀ᵐ x` (`:363-387`), so that separate clause permits the exceptional set to depend on `r`; it should not be cited as one null set uniform in `r`.

**FAITHFUL** — `Balaban/Fluctuation/ObsFirstOrderClamp.lean:37-41,66-95,115-125`. `blockMarkC` is the continuous clamp `hatOf`; it equals `blockMark` almost everywhere for `Measure.pi (S.blockSplit m₀ hp).μ`, and `integral_blockMarkC` inherits mean zero for that *same* block product measure. `blockMarkC_fields` exposes that mean-zero field to the consumer. `markIntTerm_congr_ae` substitutes almost-everywhere equal marks under the same product measure and fixed activity.

## E6. Local domain and relative source radius

**FAITHFUL** — `Balaban/Fluctuation/RenDom.lean:38-63,80-115`. `RenDom` asks `h=h₀` only on `G.Ω 1`; off that set the datum field is clipped to zero. The equivalence to the old global predicate requires `G.Ω 1` to be the whole torus. The file proves independent nonemptiness and tower-step membership, and can restrict a full `RenormExpInput` record to this domain (`:65-115`).

**FAITHFUL** — `Balaban/Inhabited/SourceFamilyRelativeRadiusFromTower.lean:36-71`. `β₀,CE,CF` precede `ρ`; the hypothesis is exactly `max 1 ρ ≤ β`, followed by `0 < q ≤ ρ`. For a fixed `ρ`, the required lower bound on `β` is therefore `max(β₀,1,ρ)`. The displayed amplitude bound has `q*CF` and the family is on `physVqRho ... ρ q`, with the same `I.𝒴=𝒴` and `I.T=Tt` (`:51-71`).

## E7. Two assembly caveats

1. **WRONG OBJECT if promoted to a physical record** — `Balaban/Inhabited/RenormHalfDetOnly.lean:27-28,39-46,86-93,149-153`. Its name and docstrings correctly identify a determinant-only record. Any downstream assertion that it supplies the marked energy, observable, or physical Theorem 3.1(g,h) record needs a different construction.
2. **WEAKER THAN CLAIMED if `RenDom` is said to repair every fibre use** — `Balaban/Fluctuation/RenDom.lean:38-63`; `Balaban/Inhabited/RenormHalfDetOnly.lean:90-93,173-193`. `RenDom` is a nonempty local domain, but the determinant-only record and its `C₁/C₂` clauses still display global equality `∀x i, D.h x i = h₀ i`. Replacing those premises requires a separate declaration or a full-domain hypothesis; the new definition alone does not rewrite them.
