# OFFFIBRE4 — free-datum activity bound for the zero class (W672 plan)
1. The polymer expansion is datum-generic: `sourceDirectTerms_scale_fromTower_rho` supplies direct terms on `physSΛEta`; `hI` is used at both scaled points of any `e ∈ physVRho`.
2. The domain family, thick labels, decoupling, measurability, decay, and amplitude bounds in `SourceExponentFamily.lean:173–285` use `XiCData` and the source ball; they do not use `e.1.2 = h₀`.
3. `W2_eq_physVal_sub_rho` already gives the source value bridge for every `e ∈ physVRho` with no field equation.
4. The `W1_eq_physVal_rho` bridge requires `D.h = h₀` to invoke `S.withDatum D hD`; this is the first true obstruction. `StepSettingH.dataUCH` and `JointRep.W1_dataUCH` already represent the same interaction at free `D`.
5. Leaf A (≤300 Lean lines): prove the critical ray value and first two jets at `H.D'`, then its cubic Taylor remainder, using `StepSettingH` and the common `StepTaylorComplex` core; retain the existing fibre statement verbatim.
6. Leaf B (≤300 lines): identify `Jr.W1` with `s²` times the physical hat remainder at arbitrary `D`, and make the existing `W1_eq_physVal_rho` a fibre application. No parallel `…H` definitions.
7. Leaf C (≤300 lines): give the `SourceExponentFamily` activity construction on `physVRho`; reuse its direct terms, `segAct`, and labels, with the free-datum `W1` bridge and existing `W2` bridge. Keep the landed fibre theorem statement unchanged as a restriction.
8. Leaf D (≤300 lines): specialize the activity family to `(rawOf D,g)` for arbitrary `XiCData D`, transfer its numerical fields from the same tower record, and obtain the raw `StepActivityBoundC`-type activity identity on both `stepSegments`.
9. Leaf E (≤200 lines): apply `labelAct_integral_eq_exp` to the raw activity identity to obtain both nonvanishing integrals; combine this with `isC1Family_zeroClass_freeDatum` and `prop26J_step_unbounded` to prove `prop26J_step_zeroClass`.
10. The admissible chart `XiCData` and numerical margin premises remain explicit; the public target receives no `D.h = h₀`, regularity, nonvanishing, or activity premise.
