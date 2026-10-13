# OBSPHYS — physical observable activity at one shared tower

Read-only Lean paths below are relative to /home/scott/Balaban/Balaban. `PROVED` refers to the exact cited declaration; `PROVED CONDITIONAL ON` names a landed implication whose hypotheses are still open; `OPEN` is a proposed leaf. All formulas here use d=L=3, N=2, the mark-block scale m₀=1 and the zero class C (whose own class field C.m₀ is 0) unless stated otherwise.

## 1. The exponent and its complex parameter

**PROVED.** `Fluctuation/StepComplexThm31.lean:187–205` applies `thm31bC_of_input_M0` to one `ObsMarks` record whose exponent is exactly
$$W(r,x)=S.WoneC\ C\ 1\ x+S.WtwoC\ C\ g\ r\ x.$$
Here `S:=T.step k hk N₁ ν β p₁`, `C:=zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)`, and the integrand is the derivative in r of `McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataUC (S.psiAtC r x)) g y i`. The consumer quantifies over one record for each fixed S, g, y, i; it has no datum-family binder.

**PROVED.** `Thm31b.lean:46–66,303–310` requires an open complex t-set 𝒰 containing [0,1], a fixed label system, an activity `A(t,σ)` holomorphic in t at σ=1 and in σ on a disc of radius Rσ>1, zero at σ=0, and representing W almost everywhere at σ=1. `ObsScalarTilt.lean:70–129,312–350` constructs the σ tilt once a physical complex-t family `Aphys(t)` with the right W identity is supplied. The σ variable of that artificial tilt is a scalar multiplier of Aphys; it is a proof device, not a new physical source.

**PROVED.** `Inhabited/SourceFamilyRelativeFromTower.lean:38–98` supplies one `DirectTerms` family I with common domains 𝒴 and terms Tt, at all points e=(datum,g) in `physVq S 1 ν T.t q`, and `labelActFamilyOn` analytic in (e,u) on `physVq ×ˢ ball 0 2`. Its displayed term is `I.T Y (ψ̂,ψ̂) (ψ̂,ψ̂) u (physInclScaled e)`; u is the expansion's σ/ray-integral argument with the hat pair held fixed. The source g is a coordinate of e and is divided by β by `physInclScaled` (lines 57–76). At fixed e=(S.D′,g), varying u does not by itself vary the hat field as required by observable r. The theorem also does not expose the physical formula for its val; its proof obtains that formula from sourceDirectTerms_slice and then omits it from the conclusion. A same-witness strengthening is needed before the W identity can be used.

**REFUTED as an immediate application.** Substituting u=r in `labelActFamilyOn_analytic` (ParamActivitySubspace.lean:129–144) does not prove holomorphy of the observable exponent: `StepActivityDirectGeneral.lean:263–266` represents W₂(r) by evaluating val at r·ψ̂ with σ=1. The landed `LocInt.analytic` (InteractionLoc.lean:41–43) varies (datum,σ) for fixed hat pair; it does not assert analyticity as the pair varies. No landed equality identifies `Tt Y (r·ψ̂,r·ψ̂) 1 e` with `Tt Y (ψ̂,ψ̂) r e`.

**OPEN-OBS-RAY-ACT.** At fixed source points e₀=(S.D′,0) and e_g=(S.D′,g), define B₀(z) and B_g(z) on the *same* thick labels by the terms Tt evaluated at the complex scaled hat pair z·ψ̂ with σ=1. Set the activity to zero outside 𝒰 and prove these are global `LabelAct` families with prefactor at most 2εU, rate κH=2κdec−1, entropy constant K0(κ0)+1, whose coefficients are differentiable on 𝒰:=ball 0 (3/2). The analytic input must be proved from the physical sharp-hat terms or a stronger ray-analytic localization theorem; neither `DirectTermsFamilyOn` nor `labelActFamilyOn_analytic` has that conclusion. For the geometric inclusion, use the exact identity r=lvR T.κ T.t b p₁=cψ/(2p₁)−4: (4+r)(3/2)p₁=3cψ/4<cψ. This strengthens the bare inequality in `D.ray_margin` and permits `hatRaysO_pair` with radius (3/2)p₁; the inclusion still needs a Lean lemma.

**OPEN-OBS-W-IDENTITY.** Put
$$A_{\rm phys}(z)=\bigl(B_0(1)-B_0(z)\bigr)\oplus B_g(z).$$
The first summand uses `LabelAct.sub`; the direct sum uses `LabelAct.sum` (Polymer/LabelSum.lean:76–109,176–184). `StepActivityDirectGeneral.lean:263–266,318–333` gives the real ray identities for val₀ and val_g, but its activity constructor uses `u.re` and is not holomorphic in z. Re-run those identities with B₀,B_g and `StepSetting.ae_WoneC_add_WtwoC_eq` (StepComplexAgree.lean:193–198), obtaining for every r∈[0,1]
$$W(r,x)=\sum_\ell A_{\rm phys}(r).H_\ell((S.blockSplit\ 1\ hp).restr\,x)\quad\text{for }\nu_{p_1}\text{-a.e. }x.$$
The zero-class source expansion is affine in g: `sourceDirectTerms_slice` (SourceDirectTermsScale.lean:193–217) gives val = −β·raySrc3 + βΣ f·dirTermSrc. **OPEN-OBS-VAL-FAMILY:** retain this hval clause in a strengthened `sourceFamilyRelative_scale_fromTower` conclusion, for the same I,𝒴,Tt; its present conclusion does not contain hval. The two source evaluations therefore cancel the potential at r and leave W₂(r). This real identity and the complex ray holomorphy are separate proof obligations.

**OPEN-OBS-F-BRIDGE.** `obsMarks_of_tilt` (ObsMarksAssembly.lean:304–366) constructs the record with integrand `obsRayFun S F x r`, where F is the site value of `flFieldOne` along the hat ray. The exact `thm31bC_of_input_M0` integrand is the derivative of `McompAtC` above. Prove these derivatives equal on the measure support, or strengthen the assembler to use that exact integrand. `McompAtC_zero_eq` (StepComplexSource.lean:54–62), `StepSetting.compTangent_psiHat` (StepComplexJoint.lean:135–140), and `bgFieldC_sub_eq_flFieldOne_hatLift` (StepActivityHatFlRay.lean:56) are the landed ingredients. An almost-everywhere equality alone does not automatically cast the *type* of an `ObsMarks` record; a transport lemma for its `hF` field is needed.

## 2. The exact label transport

**PROVED CONDITIONAL ON OPEN-OBS-RAY-ACT.** Let L:=`thickLabels I.𝒴 I.dom` and choose the two copies in `Aphys` on `Lab₀:=L.sum L`. Each B has prefactor 2εU. The subtraction has 4εU and `LabelAct.sum` takes the maximum with 2εU, hence εb=4εU. Give each copy entropy constant K0(κ0)+1; thus the base constant is 2(K0+1). The common I,𝒴,Tt are chosen before g in `sourceFamilyRelative_scale_fromTower`; the copy labels and block split do not change with r.

**PROVED.** The sharp-hat observable domain family is `𝒴obs:=obsDomains S X₁f 1 (k+1) 𝒦X`, with `hdj:=obsDomains_isDj` (ObsMarksAssembly.lean:170–198). Its `obsLab Lab₀ hdj` is definitionally `(Lab₀.sum (thickLabels 𝒴obs hdj)).sum (cubeLabels (k+1))` (lines 53–66). Extend every Aphys(z) by zero first to the domain labels, then to single-cube labels using `LabelAct.extendZero` (Polymer/LabelExtend.lean:48–72). `extendZero_H_inl` and `extendZero_H_inr` (lines 80–85) make the old coefficients unchanged and the new ones zero, so differentiability in z transfers label by label. `extendZero_hW_interp` (lines 110–121) transfers the physical W identity; alternatively tilt first and use `extendZero_hW_obs` (lines 123–140). The latter is the exact landed lemma for `ObsMarks.hW` after a two-parameter tilt.

**PROVED numerical entropy.** `entropy_thick` (HatLabelsAct.lean:48–53) and `cubeLabels_entropy` (Polymer/LabelExtend.lean:199–205) each charge K0(κ0), under 3∣N₁ and aEnt+1≤κ0. The final constant is exactly
$$K_{\rm obs}=2(K_0(3,3,\kappa_0)+1)+K_0+K_0=4K_0(3,3,\kappa_0)+2.$$
The old `StepActivityBound.Kc=2(K0+1)` cannot be reused as the final observable Kc. Positivity of εb and aEnt+1≤κ0 give the `extendZero` premises. The observable labels need only aEnt+1≤κ0; the unrelated all-root entropy `rootUnion_entropy` (Polymer/LabelRootUnion.lean:194–203) needs aEnt+2≤κ0. The currently landed `StepTower.κ0_eq` is aEnt+1 (StepTower.lean:34–38); the planned +2 retuning preserves every observable inequality below.

## 3. Numerics and scale thresholds

Write κ0:=T.κ0, κdec:=T.κdec, κ′:=T.κ′, κH:=2κdec−1, κh:=2κdec, b:=β3^k, w:=(log b)^p, κ1:=lvKappa T.κ T.t>0, r_src:=lvR T.κ T.t b p₁, Q:=cK2′ 3 3 2 (famConst 3 3 T.BG₂ T.κ)>0, and Θobs:=stepTheta 3 3 Kobs κH κ0 κ′. Here cψ=κ1√b by `lvCpsi_eq` (LevelRayTower.lean:116), and n*:=2·3^{3(T.m₁+2)} is the landed m₀=1 value in `obsMarks_of_tilt`. These quantities depend on T,A₁,p and the chosen CR,s, never on k,N₁,ν,β,p₁,g,y,i.

**PROVED rate arithmetic from the tower equations.** `StepTower.κ′_eq,κdec_eq,κ0_nonneg` yield 0≤κ′, κ0≤κ′ and κ0≤2κdec. Also κH≤2κdec and κH≤κG on choosing κG=κH. The main inequality
$$\kappa'+3\kappa_0+c_1+\tfrac32\le\kappa_H
\quad\Longleftrightarrow\quad
\tfrac12\kappa_{\rm dec}\ge4\kappa_0+c_1+\tfrac72$$
follows from κdec=100(κ0+c1+10), κ0≥0 and c1≥1. `obsMarks_of_tilt` assumes exactly these inequalities (ObsMarksAssembly.lean:334–343), plus K0+1≤Kobs, which follows from K0>0. Its `hεpos` needs 0<εU; prove this from the positive q=1 source term Q·T.t/r_src in the landed `prop33EpsEtaScaled` formula, rather than from a nonnegative upper bound alone. `D.ray_margin` implies (4+r_src)p₁<cψ, hence p₁/cψ<1/4, the assembler's `hq`.

**PROVED CONDITIONAL ON OPEN-OBS-RAY-ACT and OPEN-OBS-W-IDENTITY.** Set q=1 in `sourceFamilyRelative_scale_fromTower`: its estimate is 4εU≤CE w^{3}/√b+CF w/√b when w=(log b)^p (the Lean statement writes w^{3p} and w^p in terms of log b). For b≥e, w≥1, so εb=4εU≤CU w³/√b with CU:=CE+CF>0. Fix CR>0 and 0<s<1/2, let Rg:=obsRg CR s p b=b^s/(CR w³), and choose
$$b_0\ge e,\qquad b^s\ge2C_Rw^3,\qquad
\frac{C_U}{C_R}b^{s-1/2}\le\Theta_{\rm obs}
\quad(b\ge b_0).$$
Then Rg>1 and εH=Rg εb≤Θobs, which is exactly `obsMarks_of_tilt.hε` at Kobs. `exists_one_lt_obsRg` (ObsScalarTilt.lean:163), `exists_obsRg_mul_le` (line 196) and `obsTilt_of_physAct` (line 312) prove existence of such a uniform b₀ once Θobs>0. Choose β₀≥b₀ and above the thresholds of `T.scale` and `sourceFamilyRelative_scale_fromTower`; then b=β3^k≥β₀. The open set 𝒰=ball 0 (3/2) is contained in the assembler's disc and contains [0,1].

**PROVED CONDITIONAL ON the assembled activity.** `obsMarks_of_tilt` returns, with CPE:=CPE 3 3 Kobs κH κ0 κ′ and n* as above,
$$B_2\le CPE\cdot8QT.t(p_1/c_\psi)^2(K_0+1),$$
$$B_1=(QT.t/c_\psi)(CPE\,p_1/R_g)(n_*c_1)K_{\rm obs}^2
       \exp((\min(2\kappa_{\rm dec},\kappa')-\kappa_0)c_G).$$
Since κ′<2κdec, p₁≤A₁w, cψ=κ1√b and Rg^{-1}=CRw³/b^s, the explicit scale constants may be chosen as
$$C_1=\frac{QT.t}{\kappa_1}CPE\,A_1C_R\,n_*c_1K_{\rm obs}^2e^{(\kappa'-\kappa_0)c_G},
\qquad C_2=8CPE\,QT.t(A_1/\kappa_1)^2(K_0+1),$$
giving B₁≤C₁w⁴b^{-1/2-s} and B₂≤C₂w²/b. The factor CR is in the numerator of C₁. No extra scale threshold is needed for these two inequalities beyond b>1, the p₁ cap, and the assembler hypotheses. For the class comparison at 0≤δ<s, `obsAmp_le_class` (ObsScalarTilt.lean:231) supplies a β threshold for B₁; B₂ is smaller once b^{1/2−δ}≥C₂3^{1/2+δ}w², possible because δ<1/2. Take the maximum of these thresholds before k.

## 4. Fixed-datum target and leaves

**OPEN exact target, after the proposed leaves.** For each tower T and choices A₁,p,CR,s with A₁,CR>0 and 0<s<1/2, choose β₀,C₁,C₂ once. For every k≥1, 3∣N₁>5, 0<ν with ν3^{2(k+1)}≤1, β≥β₀, 0<p₁≤pLog A₁ p b, and `D : StepScaleData T k hk N₁ ν β p₁`, set S:=T.step and C:=zeroClass. For each g∈l1Ball and every site y, spin i, the conclusion is one
`I : ObsMarks S.nuFl (S.blockSplit 1 hp)
  (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
  (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
    (S.dataUC (S.psiAtC z x)) g y i) r)
  (rootCube (m₀ := 1) (blockIndex y))`
with `I.κ0=κ0, I.κH=κH, I.κ′=κ′, I.Kc=Kobs, I.Rσ=Rg, I.κh=2κdec` and the B₁/B₂ bounds above. This binder order is the intended `obsMarks_zeroClass_family` statement; it is **not landed**. `T.scale` makes the StepScaleData premise available uniformly after a threshold. The record is only at the fixed datum S.D′. `thm31bC_of_input_M0` consumes precisely such a fixed-datum record for each g,y,i; no jointly analytic chart-family of records is demanded by that theorem. Analyticity in the datum for a later class theorem is a separate OPEN assertion.

The following Lean-shaped statement fixes the quantifier order and the exact consumer types; it is OPEN:

```lean
theorem obsMarks_zeroClass_family {κmin : ℝ} (T : StepTower κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) {CR s : ℝ}
    (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
  ∃ β₀ C₁ C₂ : ℝ, 2 ≤ β₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (h3N : 3 ∣ N₁), 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * 3 ^ k) →
  StepScaleData T k hk N₁ ν β p₁ →
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
    g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2),
    let S := T.step k hk N₁ ν β p₁;
    let C := zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁);
    ∃ I : ObsMarks S.nuFl (S.blockSplit 1 hp)
      (fun r x => S.WoneC C 1 x + S.WtwoC C g r x)
      (fun r x => deriv (fun z => McompAtC C.m₀ C.Tm S.a S.ν
        (Nat.le_succ k) (S.dataUC (S.psiAtC z x)) g y i) r)
      (rootCube (m₀ := 1) (blockIndex y)),
      I.Kc = 4 * K0 3 3 T.κ0 + 2 ∧ I.κ0 = T.κ0 ∧
      I.κH = 2 * T.κdec - 1 ∧ I.κ' = T.κ' ∧
      I.κh = 2 * T.κdec ∧ I.Rσ = obsRg CR s p (β * 3 ^ k) ∧
      I.B1 ≤ C₁ * obsW p (β * 3 ^ k) ^ 4 *
        (β * 3 ^ k) ^ (-(1 / 2 : ℝ) - s) ∧
      I.B2 ≤ C₂ * obsW p (β * 3 ^ k) ^ 2 / (β * 3 ^ k) := by
  sorry
```

| Order | Leaf, status, inputs and size | Assignment |
|---|---|---|
| 1 | **OPEN** `obsSourceFamily_val`: restate the from-tower source-family conclusion with the physical hval formula from its existing `sourceDirectTerms_slice` call, for the same witnesses. ≤120 lines. | Sonnet; start now |
| 1 | **OPEN** `obsRayAct_terms`: fixed 𝒴,Tt; construct B_e(z) from Tt at z·hatΦ, σ=1 on ball 0 (3/2); prove label bounds and ray holomorphy. Use sharp-hat analytic input and `HatRaysO` margin. ≤280 lines. | strong; start now |
| 1 | **OPEN** `obsMarks_numeric_fromTower`: prove rate ledger, Kobs entropy budget, Θobs positivity and uniform β₀ from `obsTilt_of_physAct`; then B₁/B₂ scale formulas. ≤220 lines. | Sonnet; start now |
| 1 | **OPEN** `obsRayFun_eq_McompAtC_zero`: prove the derivative match using `McompAtC_zero_eq` and the fluctuation-field bridge; add `ObsMarks` transport of `hF`. ≤200 lines. | strong; start now |
| 1 | **OPEN** `obsRootInputs_fromTower`: give `obsMarks_of_tilt` its site cover, row and ray hypotheses from D and the local-cover lemmas, with m₀=1. ≤250 lines. | strong; start now |
| 2 | **OPEN** `obsPhysAct_W_zeroClass`: form B₀(1)−B₀(z) ⊕ B_g(z), prove real W identity using `sourceDirectTerms_slice` and `StepComplexAgree`, with common labels from the landed family. ≤250 lines. | strong; after ray leaf |
| 2 | **OPEN** `obsPhysAct_extendZero`: two zero extensions, entropy Kobs, pointwise holomorphy and `hW` via `extendZero_hW_interp`. ≤150 lines. | Sonnet; after ray leaf |
| 3 | **OPEN** `obsMarks_zeroClass_family`: combine leaves 1–2, `obsTilt_of_physAct` and `obsMarks_of_tilt`; use one β₀ before all scale quantifiers. ≤260 lines. | strong; final |

**Status.** `obsMarkHalves_of_sharpHat` and `obsMarks_of_tilt` are PROVED implications; retaining the source val formula, the physical ray activity and W identity, the exact derivative bridge and the tower root wrapper remain OPEN. Consequently the unconditional family and its use in `thm31bC_of_input_M0` remain OPEN.
