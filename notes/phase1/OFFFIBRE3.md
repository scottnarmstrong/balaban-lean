# OFFFIBRE3 — raw `JointRep` route to the second off-fibre leaf

**PROVED (snapshot).** Read-only audit of `/home/scott/Balaban` main, initially at `3ff15e72cd1671dc668892595b331ad2378907b9` and rechecked at `7c867c3606e90e4b54c8d2f7e51c8ae30411d7ca`; the intervening commits changed no Lean files. Clean worktree; no build. “PROVED” below means source inspection, not that a proposed theorem has elaborated.

## T1. Decision and the obstruction in the current proof

**PROVED.** `StepSettingH.lean:28–90` has already landed the only necessary new *datum* object: `withDatumH D`, `dataUCH`, `rawUCH`, `dataUCH_h`, `rawOf_dataUCH`, and fibre equalities. `JointRep.gJ` preserves the incoming raw field as `q.1.2` (`StepComplexJoint.lean:307–314`); `FJ`, `VJ`, `PJ`, `EJ`, `FcJ`, `W1`, `W2`, `tKJ`, `rhoJ` are functions of that raw pair (`:316–382`). `TstepJ` is the raw fluctuation integral (`StepComplexOutAnalytic.lean:385–389`). Thus the integral side of an off-fibre step has a landed definition; `analyticAt_TstepJ` already treats raw data jointly (`:415–449`).

**OPEN (answer: yes, conditional as in the landed theorem).** At every `D : BgData S.G' N` satisfying `XiCData`, the identity can be stated for `Jr.TstepJ C g (rawOf D)` with the same numerical chart margins, ray regularity and nonvanishing as `prop26C_step`. No equality `D.h = h₀` belongs in its type. The identity is not unconditional on all chart data: `prop26C_step` itself takes `StepRegularC` and `StepNonvanishingC` (`StepComplexProp26.lean:491–498`), and `prop26C_class` obtains the former from class regularity (`:641–651`).

**PROVED (specific fibre uses).** `dataUC_psi0C` identifies the old critical datum's field by `S.hh₀` (`StepComplex.lean:387–405`); `compTangent_dataUC` uses that identity (`StepComplexHat.lean:190–200`); `rawOf_dataUC_psiHat` uses `S.dataUC_h` and `S.hh₀` (`StepComplexJoint.lean:146–160`). The plus-domain lemma passes the field equality to `inUnionDomainC_of_tangent_hatLift` (`StepComplexProp26.lean:265–278`), and `JbgC_expansion` passes it to `expansion_quadratic` (`:401–425`). `H.dataUCH_h` supplies precisely the off-fibre equality (`StepSettingH.lean:62–67`); its `rawOf_dataUCH` is at `:72–80`. Merely replacing `S.hh₀` in `prop26C_step` is insufficient: its `psiKdC`, `covSqrtC`, `AnewC`, `AoldC`, `rhoExpC`, `WoneC`, `WtwoC` still read `S.D'`/`S.dataUC` (`StepComplex.lean:265–302,331–360`; `StepComplexOut.lean:56–155`).

**PROVED (proof split).** `JbgC_expansion` and `integrandC_eq` are the geometric/action and pointwise-integrand part (`StepComplexProp26.lean:401–481`). The core of `prop26C_step` (`:491–610`) is generic probability normalization, the two-stage interpolation of `W₁,W₂`, the Gaussian prefactor and the determinant identity. Its current `hV0`, `hint`, `hdet`, and `hI1/hI2` are fibre-flavoured applications, not intrinsic to that algebra. `prop26C_class` is a short regularity-to-step corollary (`:641–651`).

**REFUTED (a tempting shortcut).** The existing `prop26C_class` cannot be applied to arbitrary `D` via `withDatum`: its constructor requires `∀ x i, D.h x i = (S.h₀ i : ℂ)` (`StepComplexAnalytic.lean:324–327`); the existing `JointRep.withDatum` and all six listed comparison lemmas inherit that premise (`StepComplexJoint.lean:556–623`; `StepComplexOutAnalytic.lean:392–410,481–524`). `TstepJ` being analytic on raw data does not by itself prove the off-fibre value identity.

## T2. Exact target and least definitions

**OPEN (target declaration; syntax to elaborate after leaf 1).** Use the section variables and opens of `StepComplexProp26.lean:350–374`, plus `Jr : S.JointRep eps pp`, `D : BgData S.G' N`, `hX : XiCData S.G' S.a S.ν (k+1) 1 eps D`, and the same `hC hMX hdm hα hsm ha₁ hc7 hR hsmR hβ hp₁ hδ₁` numerical hypotheses as `prop26C_step`. The following complete theorem *type* uses no new step-object definition. The direct `hreg`/`hnv` fields are the raw counterparts of the landed `StepRegularC`/`StepNonvanishingC`; the `if` in `hreg` restricts C¹ requirements to fluctuation support.

```lean
theorem JointRep.prop26J_step
    (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)
    (D : BgData S.G' N)
    (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (g : Fld d L N₁ m₁ (k + 1) N)
    (hreg : ∃ (U : Set ℝ) (W₁' W₂' : ℝ → S.E → ℂ),
      IsC1Family U
        (fun s x => if chiFl S.U N S.p₁ x = 1 then
          Jr.W1 C (rawOf D, (s : ℂ) • yhat x) else 0) W₁' ∧
      IsC1Family U
        (fun t x => if chiFl S.U N S.p₁ x = 1 then
          Jr.W2 C g (rawOf D, (t : ℂ) • yhat x) else 0) W₂')
    (hnv1 : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∫ x : S.E, Complex.exp
        (Jr.W1 C (rawOf D, (s : ℂ) • yhat x)) ∂S.nuFl) ≠ 0)
    (hnv2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∫ x : S.E, Complex.exp
        (Jr.W1 C (rawOf D, yhat x) +
          Jr.W2 C g (rawOf D, (t : ℂ) • yhat x)) ∂S.nuFl) ≠ 0) :
    Jr.TstepJ C g (rawOf D) = Complex.exp (
      -(S.β : ℂ) * actionRawC S.G' S.a S.ν D.Ψ D.h (Jr.F₀ (rawOf D)).1 +
      Jr.EJ C (rawOf D, 0) - (S.Eppp C : ℂ) * (S.nU : ℂ) +
      Jr.FcJ C g (rawOf D, 0) -
      (1 / 2 : ℂ) * ∑ y : S.U, ∑ i : Fin N,
        (decLog S.G' S.a S.a₁ S.ν (Jr.F₀ (rawOf D)).2 (fun _ => 1)
          (svec S.G' (Jr.F₀ (rawOf D)).1) (unitQ S.G') (unitP S.G'))
            (y, i) (y, i) +
      S.avgJ (fun _ => 0) (Jr.W1 C) (Jr.W1 C) (rawOf D) +
      S.avgJ (Jr.W1 C) (Jr.W2 C g) (Jr.W2 C g) (rawOf D))
```

**OPEN (meaning of the target).** `actionRawC` is `actionC` written on raw data (`PsiZeroAnalyticAction.lean:40–52`); `Jr.F₀ (rawOf D)` is the new-level complex solution (`StepComplexJoint.lean:180–195`). The trace is the existing analytic determinant branch `halfLogDetCC` (`StepComplexOut.lean:68–85`; `StepComplexCov.lean:303–310,361–364`), written inline to avoid a new `E0CH`. The two `avgJ` terms are the raw `E1` and `F0` values (`StepComplexOutAnalytic.lean:321–326,481–508`). In particular, replacing the trace by `Complex.log (Jr.Mx …).det` would introduce an unjustified branch choice.

**OPEN (minimal proof lemmas, no new definitions).** (1) `rawOf_dataUCH_psiHat`, `dataUCH_psi0C`, `compTangent_dataUCH` in/near `StepSettingH.lean:49–90`: extend the landed raw equality and transport the critical point/tangent proofs (about 75–110 lines). (2) `JointRep` at arbitrary `D`: `gJ`, `FJ`, `VJ`, `PJ`, `EJ`, `FcJ`, `W1`, `W2`, `tKJ`, `rhoJ` comparisons on the bounded path, obtained by generalizing `StepComplexJoint.lean:390–547` and making those fibre lemmas corollaries (about 150–220 moved/new lines). (3) Raw versions of `VkC_psi0C`, the plus-domain lemma, `quad_shiftUC`, `JbgC_expansion`, `integrandC_eq`, and the covariance determinant identity, generalizing `StepComplexAgree.lean:225–240`, `StepComplexProp26.lean:265–481`, `StepComplexCov.lean:361–364`; each old fibre theorem can call the general one via `dataUCH_fibre` (`StepSettingH.lean:82–90`) (about 250–360 lines, split). (4) A shared, *internal* interpolation/algebra theorem parameterized by the pointwise integrand and determinant equalities, regularity and nonvanishing; move the proof in `prop26C_step` (`StepComplexProp26.lean:491–610`) there and leave `prop26C_step` with exactly its old statement as a corollary. Instantiate it for `JointRep` to prove the displayed raw theorem (about 160–230 lines). This internal lemma may take proof-step equalities as hypotheses; it must not replace the source-facing theorem.

**OPEN (module-order constraint).** Presently `StepComplexJoint → StepComplexSource → StepComplexObs → StepComplexLocal → StepComplexSmall → StepComplexProp26` in the import graph; `StepSettingH` also imports `StepComplexProp26`. Consequently `StepComplexProp26` cannot import `JointRep` or `StepSettingH` to make its fibre theorem a direct corollary of `prop26J_step`. Put the shared interpolation lemma below `StepComplexProp26` (for example in a small module importing `StepComplexCov`), retain the old public statement, and let both old and raw proofs invoke that lemma. Move the three datum helpers into a lower module before using them in any generalized local lemma. This is a move-and-corollary of the algebraic proof, with no cyclic import and no duplicated step objects.

## T3. Coefficient value clauses

**OPEN (source coefficient).** Replace each value equality to `((S.withDatum D' hDh).E1locC C z)` (for example `Inhabited/E1CoeffFamily.lean:400–418`, `RenormE1SiteRecord.lean:66–80`) by an equality to a raw localized derivative evaluated at `Θ = rawOf D'`, using `Jr.W1 C (Θ, ·)` and the existing mask `S.maskUC z`. Concretely, the derivative direction in hat coordinates is `(Jr.Mx Θ)⁻¹ *ᵥ S.maskUC z (Jr.Mx Θ *ᵥ yhat x)`, so the unscaled local energy is the `s`-average of `fderiv ℂ (fun u => Jr.W1 C (Θ,u)) ((s:ℂ) • yhat x)` applied to that direction. A comparison theorem must use invertibility of `Mx` on the chart, the open `p⁺` margin, and `avgJ_congr` to recover `E1locC` on the fibre (`StepComplexOut.lean:166–184`; `StepComplexOutAnalytic.lean:352–366`). `JointRep` currently has no localized `E1locJ`; the inline formula is a value target, not yet a proved comparison or a new permanent object.

**OPEN (source coefficient).** Replace a value equality to `((S.withDatum D' hDh).M0C C g y i)` by the already landed raw expression `((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * S.avgJ (Jr.W1 C) (Jr.W2 C g) (Jr.McJ C g y i) (rawOf D')` (`StepComplexOutAnalytic.lean:515–527,763–769`). Generalize `McJ_withDatum`/`M0J_withDatum` from `:606–612,515–527` using `rawOf_dataUCH`; their old fibre statements become corollaries. This changes the **value clause only**: analyticity, marking, decay and support obligations remain separate.

## T4. Ordered leaves and cost

**OPEN.** Leaf A (≤180 lines): move/use the `StepSettingH` datum comparisons and critical-point/tangent facts; no new `…H` object. Leaf B (≤260 lines): raw `JointRep` path comparisons, `W1/W2/PJ/McJ` and fibre corollaries. Leaf C (≤260 lines): raw action expansion, Gaussian quadratic, determinant and integrand identities, splitting if needed. Leaf D (≤240 lines): shared interpolation algebra plus old `prop26C_step` proof-body refactor, keeping its statement byte-for-byte. Leaf E (≤240 lines): `prop26J_step`, raw class-regularity-to-step implication and optional analytic corollary via `analyticAt_TstepJ`. Leaf F (≤260 lines): `M0` and localized `E1` value comparisons. Total estimate 1,100–1,400 proof lines, zero new permanent step-object definitions; local theorem `let`/lambda expressions only. The localized energy comparison is the least certain estimate and may need its own extra ≤300-line leaf.

**REFUTED.** The OFFFIBRE2 proposal that a dozen parallel `…H` step definitions are necessary is stronger than the source demands. The raw lane already exists. What remains open is the proof of its off-fibre value identity and the localized derivative transport, not the construction of another set of integral and exponent objects.
