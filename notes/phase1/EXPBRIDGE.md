# EXPBRIDGE: the zero-class exponent on the complex chart

**PROVED.** This is a read-only audit of `/home/scott/Balaban` at `54bb6a0f6b618b1706699e9dc5a7d873bc2c5bfa`. The requested full-chart identity is not a landed theorem. “NEW” below denotes a proposed
declaration, and every other Lean declaration named here was checked in the source tree.

## 1. The two expressions

**PROVED.** Fix a step `S`, `C = zeroClass`, a `JointRep` `Jr`, and an admissible raw datum `q = rawOf D` with `XiCData D`. Write `z` for the complex hat variable. The chart pair is
`(q,z)`; `Jr.gJ (q,z)` keeps the actual complex field `D.h`, `Jr.FJ (q,z)` is the lower complex small solution, and `Jr.VJ (q,z)` is `interactionV` with background `Jr.F₀ q` and tangent
formed using `Jr.Mx q`.

**PROVED.** The definitions in `StepComplexJoint.lean` are, verbatim, `Jr.W1 C (q,z) = -(S.β : ℂ) * Jr.VJ (q,z) + (Jr.EJ C (q,z) - Jr.EJ C (q,0))` and `Jr.W2 C g (q,z) = Jr.FcJ C g
(q,z) - Jr.FcJ C g (q,0)`. Here `EJ` sums the old `Edens` terms over `Finset.Icc 1 k`; `FcJ` sums `g y i * svec ... (Jr.FJ (q,z)).1 y i` and old `Floc` terms. `Jr.PJ` passes the same
complex `h` to those old terms.

**PROVED.** At `zeroClass`, old `Edens` and `Floc` contributions vanish. Thus `W1` is `-β VJ`, and `W2` is the pairing of `g` with `svec (Jr.FJ (q,z)).1 - svec (Jr.FJ (q,0)).1`. The
fixed-step counterpart of the latter is `WtwoC_zeroClass_eq`; `WtwoC_eq_sum`, `McompAtC_zero_eq`, and `dFC_zeroClass` give related algebraic reductions.

**PROVED.** Let `val` be the witness in `sourceDirectTerms_slice`, at `η = 1/S.β`, evaluated at `Θ = (q,g/S.β)` and diagonal hat arguments `(x,x)`. Its interaction part is exactly `-β
raySrc3 (hatFun ... interactionOne) taylorWeight x x σ q`. Its source part is exactly `β Σ_a (g_a/β) dirTermSrc (hatFun ... (onXi ... (svec (flFieldOne ...) a))) 1 x x σ q`. The same
`val`, domains, labels, terms, `DiagCont`, and `DirectTerms` instances are supplied for all points of the eta slice; no datum-dependent selection is needed.

**PROVED.** `SourceFamilyRelative.lean` now supplies `physInclScaled`, `physVq_one`, `directTermsFamilyOn_scaled`, and `sourceFamilyRelative_scale`: the same eta-slice witness is
already a `DirectTermsFamilyOn` on `physV` after `Jβ`, with joint analytic label activity and the exact `labelActFamilyOn_eq_dtAct` identification.

**PROVED.** For the two step segments, define `I_q(s,x) = val (x,x) (x,x) s (q,0)` and `F_q,g(t,x) = val (x,x) (x,x) t (q,g/S.β) - val (x,x) (x,x) t (q,0)`. The proposed exact value
statement is `Jr.W1 C (q,s • x) = s² I_q(s,x)` and `Jr.W2 C g (q,t • x) = F_q,g(t,x)`. In particular, `val` at one parameter does not itself equal the two-segment exponent when the
interaction is at `s` and the source is at `t`.

## 2. Interaction: what the real proof uses

**PROVED.** `Wone_zeroClass_eq_hat` proves the first identity for the real physical step, with `x = S.hatC ψ̂`, `χ_fl(ψ̂)=1`, and `s∈[0,1]`. Its displayed `s²` is essential: `raySrc3`
carries one power of `s`, whereas the cubic Taylor remainder of the potential carries `s³`.

**PROVED.** The proof first uses `RayData.hχu` and its real-domain fields to identify `S.psiAtC r ψ̂` with the real ray and `S.VkC` with `S.Vk`. This is the point where realness enters;
`RayData.hD'R` is an `InDomainR` premise, so it is not available at an arbitrary complex `D`. The proof then invokes `Vk_ray_taylor_of_baseDomain` through the real ray and translates
its third real derivative to `dirS3` using `iteratedDeriv_comp_ofReal` and `analyticAt_interactionOne_hatRay`.

**PROVED.** The complex cancellation is already established for a fixed `StepSetting` datum in `StepTaylorComplex.lean`. `lower_bg_psi0C` follows from `criticalPoint_complex`;
`hasDerivAt_bgC_rayC` applies `theorem72_linearResponse` at the base. `VkC_ray_eq` writes the potential as a cubic first term plus a quadratic form in the response error.
`isLittleO_VkC_ray_of_baseDomain` proves that error is `o(s)`, hence the entire interaction is `o(s²)`. `VkC_ray_vanish_of_baseDomain` gives its zero, first, and second jets;
`VkC_ray_taylor_of_baseDomain` gives the cubic integral remainder.

**PROVED.** The absorbed Gaussian quadratic is already absent from the definition of `interactionV`; its subtraction is encoded by `phiOne` and the response-error square in
`VkC_ray_eq`. `withDatum_covSqrtC` only identifies the square root used by a changed step datum. It is not itself a theorem about the second variation. The complex second-jet assertion
is proved by the cited response and splitting argument, without a separate covariance-normalization premise.

**PROVED CONDITIONAL ON.** To use that argument at every `q∈physV`, replace the fixed `S.D'` in the `StepTaylorComplex` proof by `D=bgOfRaw q` and the fixed ray by `Jr.gJ (q, s • x)`.
`Jr.F₀_eq`, `Jr.Mx_eq`, `Jr.Pc_eq`, `Jr.Fb_eq`, and `Jr.dom` identify its backgrounds, tangent and lower solution. The needed base-domain and ray-domain witnesses must be extracted from
`XiCData D`, `Jr.dom`, and the same `FlCore` margins; they are not a consequence of `withDatum_covSqrtC` alone. This instantiation is NEW.

**PROVED CONDITIONAL ON.** The proof also needs a complex chart version of `VkC_psiAtC_eq_hatFun`: at `q=rawOf D`, the `hatFun` interaction at `s • x` equals `Jr.VJ (q,s • x)`. Its
fixed-step proof uses `hatFun_rawOf`, `onXi_rawOf`, and the tangent equality. `analyticAt_interactionOne_hatRay` plus the strict fluctuation-disc bound gives a neighbourhood of each ray
point, so `dirS3` is the complex third derivative. The proposed NEW `scale_markedDisc_margin` inequality is stronger than the unmarked ray requirement but is not the domain proof by
itself.

**OPEN.** The missing Lean package is this full-datum specialization of the complex Taylor proof and the exact `hatFun`/`Jr.VJ` comparison. No new mathematical second-variation identity
needs to be assumed. The proof must keep the existing base-domain and open-neighbourhood premises visible instead of asserting Taylor from `XiCData` without a bridge.

## 3. Continuation and the required domain

**REFUTED.** `ae_exponentsC_eq` at the central real datum implies equality on the full relative complex chart. A single point is not a uniqueness set. The theorem also supplies an
almost-everywhere equality, whereas an identity theorem for each fixed configuration needs a common pointwise equality set.

**PROVED CONDITIONAL ON.** The real points of the affine `h=h₀` slice would be a totally real set of full dimension in that slice if the `Ψ` part of `rawSub` is the complexification of
its conjugation-fixed part. `rawSub` is defined by complex-linear block constraints, making this plausible, but the real-form and connected-component checks are NEW. One would still
need pointwise equality on a real-open set of such data. `W1_withDatum` and `W2_withDatum` identify chart and step formulae there; they do not supply `RayData` or the hat expansion for
every real datum.

**REFUTED.** Even a successful identity theorem on the fixed-`h₀` slice proves an identity on all of `physV`. Its `h` directions are omitted from that slice; points of `physV` can have
complex, site-dependent `h`. A full real-form continuation would need a real-open identity with varying site-dependent `h`, which no `RayData` theorem gives. The full chart is required for
`SFTermClauses.analyticE/analyticM` and the parameter-family `holA`/`holG` fields. Thus DIRECT is the chosen full-chart proof route; continuation is at most an optional slice proof.

**PROVED.** The identity actually consumed by `StepActivityBoundC.hW` is only at the datum of that `StepSetting` and is `S.nuFl`-a.e. for each point of `stepSegments`. `E1MarksC.hW` is
source-free `S.WoneC C`, so it uses the common activity at `g=0`. `ObsMarks.hW` is for its supplied `W`; a source tilt needs its own complex source parameter and `holt`, `holσ`, and
`zero` fields. Full-chart exponent equality is a useful stronger theorem for all fibres, while chart analyticity must remain full.

**PROVED CONDITIONAL ON.** A minimal consumer theorem can require the pointwise exponent comparison on the physical fixed-`h₀` fibre, with full-`physV` analyticity of the same label
family. At `q₀`, it yields the original `StepActivityBoundC.hW`; at other admissible fibre points, `W1_withDatum` and `W2_withDatum` yield the changed-step identity. It does not provide
an exponent theorem at varying complex `h`.

## 4. Source difference

**PROVED.** `bgFieldC_sub_eq_flFieldOne_hatLift` is already stated for a complex `XiCData D'` and a lower datum with the same `h`; its conclusion identifies the lower-field difference
with `flFieldOne` at the hat lift. `Jr.gJ` uses `q.h` at every ray point, so the same-`h` premise is natural even when `h` is complex and site-dependent.

**PROVED.** `analyticAt_flFieldOne_hatRay` applies at a complex datum under the strict hat radius. `dirTermSrc_ray` then gives exactly the value at `t` minus the value at zero. The
factor `β` in `val` cancels the source coordinate `g/β`; there is no factor `t²`.

**PROVED CONDITIONAL ON.** For every `q`, instantiate `bgFieldC_sub_eq_flFieldOne_hatLift` with the lower data represented by `Jr.gJ (q,t • x)` and `Jr.gJ (q,0)`; identify both lower
solutions via `Jr.Fb_eq` and the tangent via `Jr.Pc_eq` and `Jr.Mx_eq`. The complex-source formula then follows by finite-sum algebra and the zero-class old-term equations. The
chart-wide instantiation is NEW.

**OPEN.** `Wtwo_zeroClass_eq_hat` proves this at the original real step, but its proof uses `RayData` to compare real and complex exponents and to prove `flFieldOne_ray_eq`; that latter
lemma calls the generic complex field-difference theorem. Therefore the generic source ingredient has landed, while its `JointRep` chart substitution has not.

## 5. Exact proposed statements and bounded leaves

**OPEN (NEW `sourcePhysVal_jointRep`).** Given the `sourceDirectTerms_slice` value witness, `Jr : S.JointRep eps pp`, `q∈physV S 1 ν eps`, `D=bgOfRaw q` with `XiCData D`, `g∈l1Ball`,
`1≤S.β`, `χ_fl(ψ̂)=1`, `s,t∈[0,1]`, and the explicit ray/domain and hat-radius premises above, put `x=S.hatC ψ̂` and `Θβ=(q,g/S.β)`. Then `Jr.W1 C (q,s • x) = s² * val (x,x) (x,x) s
(q,0)` and `Jr.W2 C g (q,t • x) = val (x,x) (x,x) t Θβ - val (x,x) (x,x) t (q,0)` for `C=zeroClass`. The statement is pointwise on the cutoff event and has no old-term matching
hypothesis; old energy and observable sums vanish for this `C`.

**OPEN (NEW `sourceExponent_family`).** Use the landed `directTermsFamilyOn_scaled` under the complex-linear inclusion `Jβ(q,g)=(q,g/S.β)`, with its fixed `BlockSplit`, labels and
terms. For every `e=(q,g)∈V=physV S 1 ν eps` and `p=(s,t)∈stepSegments`, construct one zero-extended label activity `A_e(p)` such that, for `S.nuFl`-a.e. `ψ̂`, `Σ_y (A_e(p)).H_y
(BS.restr ψ̂) = Jr.W1 C (q,s • S.hatC ψ̂) + Jr.W2 C g (q,t • S.hatC ψ̂)`. If `A⁰` is the activity at source zero and `Aᵍ` at source `g/β`, use `s² A⁰(s)` on the first segment and `A⁰(1)-A⁰(t)+Aᵍ(t)` on the second; their sums are `s² I_q(s,ψ̂)` and `I_q(1,ψ̂)+F_q,g(t,ψ̂)`.

**PROVED CONDITIONAL ON.** The family proof uses `labelActFamilyOn_eq_dtAct`, the `DirectTerms` finite-sum identity, `sourcePhysVal_jointRep`, `sourceSlice_mem`, `ae_ball`,
`ae_hatOf_restr`, and the zero-extension lemmas in `LabelExtend.lean`. Pointwise equality on `χ_fl=1` passes to a.e. equality by `ae_ball`; there is no parameter-dependent null-set
issue because each comparison is pointwise. Quantifiers over `e` and `p` precede that a.e. clause.

**OPEN (NEW leaf 1, Sonnet, start now, ≤220 lines).** Prove the complex source comparison for `Jr.FJ` using `Jr.dom`, `bgFieldC_sub_eq_flFieldOne_hatLift`, `dirTermSrc_ray`, and
`analyticAt_flFieldOne_hatRay`. Output the second equality of `sourcePhysVal_jointRep` with its exact radius and same-`h` premises.

**OPEN (NEW leaf 2, strong, start now, ≤290 lines).** Reuse `VkC_ray_eq`, `isLittleO_VkC_ray_of_baseDomain`, `VkC_ray_taylor_of_baseDomain`, `criticalPoint_complex`, and
`theorem72_linearResponse` at `D=bgOfRaw q`; prove chart-wide first/second jet vanishing with explicit base and ray-domain witnesses.

**OPEN (NEW leaf 3, strong, after leaf 2, ≤260 lines).** Identify the ray potential with `hatFun ... interactionOne` and `Jr.VJ`; apply `analyticAt_interactionOne_hatRay`, `dirS3`, and
the cubic remainder to output the first equality of `sourcePhysVal_jointRep`.

**OPEN (NEW leaf 4, strong, after leaves 1–3, ≤280 lines).** Package both value identities with the landed `directTermsFamilyOn_scaled` under `Jβ`; use `labelActFamilyOn_eq_dtAct`, one
label union and zero extension for `sourceExponent_family`, then specialize to the physical fibre using `W1_withDatum` and `W2_withDatum`.

**PROVED.** No Lean build is claimed: this file is a source-level proof plan with explicit NEW obligations. The central `sourceActivityC_scale` is already a complex activity bound at
the original real datum and does not discharge the chart-wide equalities above.
