# RENPHYS: the renormalization record on the class fibre

Source snapshot: read-only `/home/scott/Balaban/Balaban`, inspected at commit `1bed014` (2026-10-13). Status words below refer to the **stated Lean declarations** or to the explicitly named remaining mathematical assertion. No claim here identifies a determinant term with the full renormalized energy.

## T1. The largest present assembly at $e=t/2$

**PROVED (assembly of landed results; the proposed single conjunction has not itself been added to Lean).** Fix `R : StepTowerTheta κmin`, `hR : renDetFibreMin ≤ κmin`, $k\geq1$, `N₁` with `3 ∣ N₁` and `5 < N₁`, $\nu\geq0$ with $\nu3^{2(k+1)}\leq1$, and arbitrary real $\beta,p_1$. Put

\[
 S=R.toStepTower.step\ k\ hk\ N_1\ \nu\ \beta\ p_1,\quad
 G=S.G',\quad e=R.t/2,\quad r=R.r_0,\quad
 \kappa_a=\kappa_b=3R.\kappa_{\rm dec}/2,\quad
 c_K=\operatorname{renCK}(3,3,2,R.BG,R.\kappa),\quad B=8e.
\]

Let $Z=\operatorname{Torus}(3,N_1 3^{R.m_1}3^{k+1-(k+1)})$, $B_z=\operatorname{blockSites}(3,3,N_1,R.m_1,k+1,k,z)$, $X_z=\operatorname{X1}(G,1,k,\operatorname{fam}(1,\operatorname{blockSite}(k,z)))$, and $\mathcal Y_z=\operatorname{renYs}(\operatorname{renCube}(G,X_z),G,1,X_z)$. For $p:G.\Omega(1)\times\operatorname{Fin}(2)$ put $X_p=\operatorname{X1}(G,1,k,\operatorname{fam}(1,p.1))$ and $\mathcal Y_p=\operatorname{renYs}(\operatorname{renCube}(G,X_p),G,1,X_p)$. Fix any cut root $X_{\rm cut}:\operatorname{Set}(\operatorname{CTorus}(3,3,N_1,R.m_1,k+1))$. Write $d_Y=\operatorname{renDY}(G,1)$ and

\[
 H_{\rm det}=\operatorname{hullConst}(3,3,\operatorname{towerDetRate}(R.\kappa),
 \operatorname{towerDetConst}(R.\kappa))
 e^{c_1(3,3)\log2}e^{\operatorname{hullRate}(3,3,\operatorname{towerDetRate}(R.\kappa))}.
\]

The present fibre is `Dom D := XiCOneReal G S.a S.ν e D ∧ ∀ x i, D.h x i = (S.h₀ i : ℂ)`. With `E0det z D ξ := renE0θ_det e E z D ξ`, the Lean statement to package is the following **typed schema** (the definitions above expand the long types of `blk`, `Ys`, `YsM`, and `dY`):

```lean
∃ E : ∀ z : Z,
    DetExpansionLocC S 1 z (2 * R.t)
      (towerDetRate R.κ) (towerDetConst R.κ),
∃ F, ∃ Fcut,
  IsRenSol (N := 2) G (compWeight 3 1) ν e e r (8 * e) F ∧
  AnalyticOnNhd ℂ (fun q => Fcut q.1 q.2)
    (expDom G (XiCOneReal G (compWeight 3 1) ν e) r ×ˢ
      polydisc 0 (fun _ => Real.exp R.κ)) ∧
  (∀ D, XiCOneReal G (compWeight 3 1) ν e D →
    ∀ ξ, ‖ξ‖ < r → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ)) ∧
  RenormExpInputOn G (compWeight 3 1) ν e r cK (8 * e) F
    (fun z => blockSites 3 3 N₁ R.m₁ (k + 1) k z)
    Ys YsM dY κa κb 1 Hdet 0 0 0
    (renE0θ_det e E) (fun _ _ _ => 0)
    (fun _ _ _ => 0) (fun _ _ _ => 0) Dom ∧
  (∀ z, ∃ term, IsLocExp (N := 2) G Dom r (Ys z) dY κa Hdet
    (renE0θ_det e E z) term) ∧
  (∀ z, renE0θ_det e E z S.D' 0 =
    -(1 / 2 : ℂ) * ∑ y ∈ S.blockU z, ∑ i : Fin 2,
      S.logAC (y, i) (y, i)) ∧
  Dom S.D' ∧
  (∀ D, Dom D → ∀ ξ, ‖ξ‖ < r →
    XiCData G S.a S.ν (k + 1) 1 R.t (renThetaDatum S e D ξ))
```

Here `Ys z` and `YsM p` abbreviate $\mathcal Y_z$ and $\mathcal Y_p$. In literal Lean, `F` has the function type displayed in `renLoc_fields_scale_of_tower_at`; `Fcut` has the function type displayed in `renDec_one_unique_sharp_scale_of_tower_at` with `X₁ := Xcut`, so the unannotated existentials above are abbreviations for those explicit types. The three full-domain localization principles are **inside the record**, namely `I.locC1`, `I.locC2`, and `I.locDφ`. The predicate `Dom S.D'` supplies nonemptiness, separately from record inhabitation.

**Proof.** `R.t_pos` gives $0<e\leq R.t$. `R.κdec_lower` gives $\kappa_a=\kappa_b\leq2R.\kappa_{\rm dec}$. Apply `renLoc_fields_scale_of_tower_at R.toStepTowerRenSol` once to get **one** $F$, its `IsRenSol`, and all three localization fields. Feed that particular solution to `renDec_one_unique_sharp_scale_of_tower_at R.toStepTowerRenEnd` with `rF=r`; the resulting $F_{\rm cut}$ has the displayed endpoint for the **same** $F$. Apply `expE0_det_scale_of_tower_at R hR` at $e$, obtaining $E$, its determinant trace identity, and an `IsLocExp` on the full `XiCOneReal` domain at rate $3R.\kappa_{\rm dec}/2$ and constant $H_{\rm det}$. Apply `IsLocExp.mono_dom` with projection `Dom D → XiCOneReal ... D`. The zero mass expansion is `isLocExp_zero_cover`; `renormExpInputOn_zero_of_fields` assembles these five fields and the zero old terms. `exists_xiCOneReal_fibre_step R.toStepTower` proves `Dom S.D'`. Finally `StepTowerTheta.renDatum_half_mem_xiCData` applied to `Dom D`. Each cited declaration exists in the files named above.

**PROVED (consequences of the assembled record).** For every root $z$ and $0\leq\varepsilon_R\leq r$, `thm31g_C1_on` and `thm31g_C2_on` give `IsLocExp` on `Dom` with the exact constants

\[
 B_{C_1}(z)=9(c_Ke)^2\operatorname{blockWeight}(G,B_z)\varepsilon_R,
\qquad
 B_{C_2}(z)=\frac{17}{32}\,2\,(3+A)(c_Kc_{K2}B)^2
 \operatorname{blockWeight}(G,B_z)\varepsilon_R^2,
\]

where $A=\operatorname{bgK1}(3,3,2)\operatorname{xiC1}(3)e+c_Kc_{K2}Br+2$ and $c_{K2}=\operatorname{cK2}(3,3,2)$. The hypotheses `BgHyp`, smallness, `xiC1 e ≤ bgC1`, `r≤1/16`, and `1≤cK` are supplied as in the proofs of `thm31g_C1_scale_of_tower_at` and `thm31g_C2_scale_of_tower_at` in `RenormRadiusInput.lean`. This `_on` route is shorter once the record is built and retains the **same $F$** in $C_2$. Directly applying the two `_at` wrappers and then `mono_dom` is shorter for **two separate expansion statements**, but the C₂ wrapper existentially chooses its own $F$; it does not expose the $F$ chosen for the endpoint.

**REFUTED (physical-record identification).** Name the assembled proposition `renormDetOnlyZeroMOnFibreHalf`, not `renormExpInputOn_physical`. Its `E0θ` is solely `renE0θ_det`; its `M0θ` is the zero function and both old differences are set to zero. It is a valid `RenormExpInputOn` of exactly those functions. It is **not** a record for the physical $E''_0$ or the physical $\mathcal M''_0$, since the marked summands and, outside a genuine zero old-term case, the old differences are absent. The four `_on` consumers cannot repair missing input by themselves.

## T2. Marked energy at the renormalized datum

Define the intended $E^{\rm mark}_{0,\theta}(z,D,\xi)$ as the step's $E^{(k+1)}_{1,\mathrm{loc}}(z)$ evaluated with block datum `renThetaDatum S e D ξ`. **OPEN** is its analytic, local, bounded coefficient family; pointwise `e1locC_expansion_of_input` gives only an existential expansion after an `E1MarksC` input is provided. `StepPiecesJoint` and `ActivityOfWitness` expose useful activity and mark hypotheses, but do not themselves furnish the needed parameter family of `E1MarksC` coefficients.

1. **OPEN — physical marked input.** For every datum $D'$ in the step chart `XiCData G S.a S.ν (k+1) 1 R.t`, construct the physically specified `E1MarksC (S.withDatum D' hD') C BS z` (or a single uniform source record yielding these) with matched label, activity, mark, and `DetExpansionC` data. The conclusion is the pointwise identity $E_{1,\mathrm{loc}}^S(z;D')=\sum_T\operatorname{interpCoeff}(I_{D'},T)$ and the coefficient bound
   $\|\operatorname{interpCoeff}(I_{D'},T)\|\leq H_Me^{-\kappa' d_{\rm Ext}(T)}$,
   $H_M=\operatorname{CPE}(3,3,I.K_c,I.\kappa_H,I.\kappa_0,I.\kappa')\sum_i I.F_0(i)e^{-I.\kappa_0 I.Lab.dl(I.y_0i)}$.
   This is conditional on `E1MarksC`; `thm31aC_coeff` proves the corresponding $E_0$ identity with `e1CoeffC = det.term + gsumCoeff`, whereas `e1locC_expansion_of_input` isolates the marked $E_1$ part. This leaf cannot finish before the physical marks are assembled.

2. **OPEN but startable conditionally on `ParamMarkFamily` — analytic raw coefficient.** On an **open** raw neighborhood $V$ of the chart slice at radius $t$, construct a `ParamMarkFamily μ Lab A y0 G κG F0 V 𝒰 Q` whose activity and marks represent those of the step for every point of the fibre. Verify its exact `bound`, `holA`, `holG`, `contA`, `contG`, support dependence on the enlarged mark read set $\widehat Y(\operatorname{sitesOf}T)$, and the numerical hypotheses of `paramMarked_analytic_local_bound`: $\kappa'+3\kappa_0+c_1+3/2\leq\kappa_H$, $\kappa_H\leq\kappa_G$, $\varepsilon_H\leq[8K_c^3c_1e^{(\kappa_H-2\kappa_0)c_G+c_1+\kappa'c_G}]^{-1}$, plus its other stated positivity and geometry assumptions. That theorem then supplies **all three** conclusions: `AnalyticOnNhd` of $q_T(\Theta)=\operatorname{gsumCoeff}(\Theta,T)$ on $V$, equality when the restriction maps $\pi_T\Theta$ agree, and $\|q_T\|\leq H_Me^{-\kappa'd_{\rm Ext}(T)}$. `gsumCoeff_analyticOnNhd` is its analytic component. This abstract implication can be proved now with a *hypothesized* family; constructing the physical `ParamMarkFamily` remains open. A family merely indexed by real chart points is insufficient for `AnalyticOnNhd`.

3. **PROVED composition rule, OPEN physical application.** `analyticOnNhd_renThetaRaw` proves that $(\operatorname{rawOf}D,\xi)\mapsto\operatorname{rawOf}(\operatorname{renThetaDatum}S e D\xi)$ is analytic everywhere; `renThetaRaw_rawAgree` preserves raw agreement on any read set. `renDatum_half_mem_xiCData` puts its values in the step chart at $t$. If $V$ above contains these values with an open neighborhood, composition gives `AnalyticOnNhd` of $q_T\circ\operatorname{renThetaRaw}$ on the corresponding open source neighborhood, and locality on the same read set. The input `ParamMarkFamily` plus chart inclusion suffices for this conditional lemma; no finished physical `E1MarksC` is needed.

4. **OPEN but startable under a coefficient support/size hypothesis — fibre regrouping.** For each marked coefficient $q_T$, define its **actual** raw read set $X_T$ (including the mark's halo and the root), prove $X_T$ is an admissible connected polymer meeting $X_z$, and prove agreement on $X_T$ implies equality of $q_T$. Only then set $Y_T=\operatorname{renFibreMap}(G,1,X_z,X_T)$ and $q'_Y=\sum_{T:Y_T=Y}q_T$. `renFibreMap_mem_renYs`, `subset_renFibreMap`, `renDY_renFibreMap_le`, `renRegroup_norm_le`, and `sum_renRegroup` provide the cover, locality, size, coefficient bound, and sum identity **if** the coefficients are indexed by suitable polymer supports and satisfy its exact zero-off-root and size bound. In the landed geometry, $A=\operatorname{renDetA}(3,3,1)$ and a bound $\|q_X\|\leq H e^{-\lambda\operatorname{sizeJ}X}$ gives, when $\kappa_a\leq\lambda/A-c_1(3,3)\log2$,
   $\|q'_Y\|\leq H e^{c_1(3,3)\log2}e^\lambda e^{-\kappa_a\operatorname{renDY}Y}$.
   The displayed $d_{\rm Ext}(T)$ bound **does not by itself imply** the required `sizeJ X_T` bound; a mark read-set comparison and counting/possible rate loss are separate inputs. An abstract regrouping lemma can start now under those explicit hypotheses. It does not require the physical `E1MarksC` construction.

5. **PROVED base identity once input exists.** `renThetaDatum_zero` gives `renThetaDatum S e D 0 = D`. Hence at $D=S.D'$, `StepSetting.withDatum_self` and `e1locC_expansion_of_input` give $E^{\rm mark}_{0,\theta}(z,S.D',0)=S.E1locC(C,z)=\sum_T\operatorname{interpCoeff}(I_{S.D'},T)$. For general $D\in\mathrm{Dom}$, the right side is the expansion of the step **with datum $D$**, not a constant independent of $D$. The equality of the proposed regrouped coefficients at $\xi=0$ follows from the finite regrouping identity once Leaf 4 is established. This leaf is conditional on the pointwise `E1MarksC` input, and the final regrouped version is conditional on Leaf 4.

**OPEN — final physical record.** Add the marked-energy expansion to the determinant expansion using `IsLocExp.add` only after its coefficient bound has been converted to the same `renYs`, $d_Y$, and activity rate. Separately construct the physical $M0θ$ expansion and the old differences (or prove their genuine zero-class vanishing). The chart inclusion is a domain input, not such an expansion.

## T3. The fibre predicate and the nonzero-class interface

**REFUTED for a proper $\Omega_1$ and nonzero $h_0$.** `BgData.h_zero` (`Background/Data.lean:119`) and the `BgData.clip` constructor (`:219`) give $D.h(x)=0$ when $x\notin G.\Omega(1)$. Thus the current global predicate $\forall x,i, D.h(x,i)=h_0(i)$ has no datum if $G.\Omega(1)$ is proper and any component of $h_0$ is nonzero. `nonempty_renormExpInputOn_fibre` alone does not contradict this: its record may have an empty domain.

**OPEN generalization; mathematically correct replacement.** Define

```lean
def RenDom (G) (a) (ν e : ℝ) (h₀ : Fin N → ℝ) (D : BgData G N) : Prop :=
  XiCOneReal G a ν e D ∧
    ∀ x, x ∈ G.Ω 1 → ∀ i, D.h x i = (h₀ i : ℂ)
```

Equivalently the second field is $D.h(x,i)=\mathbf1_{G.\Omega(1)}(x)h_0(i)$; this agrees with `BgData.clip` off $\Omega_1$. There are **four direct fibre theorem statements** to reconsider: `nonempty_renormExpInputOn_fibre` and the three declarations in `RenFibreDatum.lean` (`exists_xiCOneReal_fibre`, `nonempty_renormExpInputOn_fibre_datum`, `exists_xiCOneReal_fibre_step`). The first record restriction changes without new analysis; the next two should drop the full-torus hypothesis `hΩ` and prove a clipped witness; the step theorem may remain as a stronger whole-torus specialization, although its advertised target predicate should use `RenDom`. Thus only **three require a new general conclusion**; the fourth is a compatibility specialization.

The marked-family path has a further **five named interfaces at minimum**: `StepSetting.hh₀` (`StepObjects.lean:245`), `StepSetting.withDatum` (`StepComplexAnalytic.lean:324`), `paramSlice`, `rawOf_mem_paramSlice`, and `thm31aC_coeff_withDatum` (`ParamDatumFamily.lean:151,160,265`). They currently demand equality at every site; dependent `withDatum` lemmas and the `JointRep.withDatum` method also inherit it. Replacing only `RenDom` would leave the marked energy unformulable on a proper $\Omega_1$. Since the currently used tower has $\Omega_1$ equal to the whole torus, changing the four direct fibre statements now is small, but changing `StepSetting` and its family downstream is a separate, larger migration. Keeping the present whole-torus specializations while introducing `RenDom` as the public general predicate avoids falsely claiming that the existing marked family already treats nonzero classes on proper domains.

## T4. Ordered worker targets (each bounded by 300 new lines)

1. **PROVED inputs; start now (≤220 lines):** add `renormDetOnlyZeroMOnFibreHalf` to a scratch Lean module: the one-$F$ record, matching endpoint, determinant `expE0`, `Dom S.D'`, and chart inclusion. Prove C₁/C₂ corollaries from `_on`. This packages T1 without a new analytic estimate.
2. **PROVED inputs; start now (≤120 lines):** define `RenDom` and prove its equivalence to the clipped equality; add restricted versions of the three reusable fibre statements, preserving the old whole-torus theorem names as specializations. Do not change `StepSetting` in this target.
3. **Conditional on an explicit `ParamMarkFamily`; start now (≤250 lines):** prove an abstract analytic/local/bounded coefficient theorem on an open raw neighborhood and its composition with `renThetaRaw`; make the activity/mark agreement map and numerical assumptions explicit. The output is a conditional reusable theorem, not the physical marked energy.
4. **Conditional on explicit mark read sets; start now (≤250 lines):** prove the generic rooted fibre regrouping statement with `IsPolyDom`, zero-off-root, `sizeJ` decay, and read-set locality as hypotheses. Instantiate the existing `renRegroup_norm_le` and `sum_renRegroup`; keep the physical mark support comparison open.
5. **OPEN physical source work (≤300 lines per later module):** construct the physical `E1MarksC` and `ParamMarkFamily` at the step, then prove the read-set/size comparison and the $\xi=0$ identification. Only afterward assemble physical `E0θ`, `M0θ`, and old differences in `RenormExpInputOn`.
