# The cut family for the last integral

**Status and scope.** PROVED refers to an existing Lean declaration or a formula checked on the cited PDF page. PROVED CONDITIONAL ON gives the needed open premises. OPEN is a proposed
mathematical or Lean result. REFUTED identifies an implication contradicted by the definitions. All Lean files cited below were read only. P3 and P4 formulas were checked on PDF images; P7
§4 was checked on pp. 529–531.

## 1. What the step actually cuts

**PROVED (the step mechanism, one paragraph).** `Localization/DecoupledSolve.lean:187` defines `decG G a ν s := fun α => Gs G a ν α (extS G s)`. Unfolding
`Localization/Decoupled.lean:70–96`, `cubeG_z=(cubeH_z)⁻¹ c_z`, `K_z=χ_z H-Hχ_z`, `G*_s=∑_z sProd_z χ_z cubeG_z`, `𝒦_s=∑_z sProd_z K_z cubeG_z`, and `G_s=G*_s(1-𝒦_s)⁻¹`;
`Localization/Cover.lean:930–945` has `sProd_z=∏_{P∈Qset(z)}s_P`, `|Qset(z)|≤N0(d,L)`. Thus the parameters multiply localized parametrix terms, and expanding the last inverse gives
generalized walks through overlapping cubes. They do **not** multiply every entry of the original operator. `Localization/DecoupledBounds.lean:298–456` proves `Kz_cube_weighted ≤ B_K C/M₁`
using the partition derivative and local Green estimate, then `dg1` sums at most `3·5^d` contributing centers and obtains `‖𝒦_s‖_{2,w}≤1/4` from `M₁=L^{m₁}≥c_*e^{N0κ}`.
`Localization/DecoupledField.lean:355–369` defines `FamSpec`: for every `DGSetting`, parameter disc, and `N`, it asserts `GreenFamily` with `famConst=1+L(B_Ge^{N0κ})+4L(B_Ge^{N0κ})/γ₁`,
`SupBounds`, and `IsUnit(1-𝒦_s)`; **spatial decay is separate**, `Localization/DecoupledMain.lean:380:dg3`. Entry analyticity on the strict disc is
`Localization/DecoupledAnalytic.lean:240:dg4_analytic`, packaged as `DecoupledSolveAnalytic.lean:101:AnSpec`; `i4a_analytic` at line 135 consumes `FamSpec`, `AnSpec`, and `hM`.

**PROVED.** `Background/AbstractGreen.lean:136:GreenFamily` has `bound` and `diff` fields in `StarBound`; it does not itself say `G_s` is the inverse of a cut operator. At `s=1`,
`Localization/DecoupledMain.lean:283:Gs_one` gives the ordinary inverse. For complex `s`, the useful object is the analytic parametrix family and its Neumann expansion.
`Localization/DecoupledField.lean:408:decGreenFamily` proves that some constants satisfy `FamSpec`; `DecoupledSolveAnalytic.lean:anSpec_exists` supplies analytic constants.

## 2. What the papers say about the last covariance

**PROVED (P3, pp. 36–39).** P3 p. 37 (2.2) has a partition with `|∂h_z|<2/M`; p. 38 (2.6)–(2.8) writes the commutator `K_z` and the generalized random walk series
`G(α)=∑_ω h_{ω₀}G_{ω₀}h_{ω₀}K_{ω₁}G_{ω₁}h_{ω₁}⋯`. P3 p. 39 (2.10) charges each inserted `K_zG_z` by `4dB₀/M`; the displayed estimate after (2.11) assumes a constant times `M⁻¹≤1`. P3 p.
36 says the interpolating parameters are based on this expansion. This is the source of the step design above.

**PROVED (P4, pp. 719–720).** P4 §6 (6.4)–(6.5) expands about the constant saddle and gives a positive quadratic form with mass lower bound. P4 p. 720 then says the covariance decays
exponentially and instructs the reader to repeat the general fluctuation-integral procedure, with `ψ'=β_k^{-1/2} C_k^{1/2}ψ`. It does not give a formula for final cut parameters or identify
a multiplication of Schur-complement entries.

**PROVED (P7, pp. 529–531).** P7 §4 (4.1)–(4.3) follows the earlier steps but omits the new P5 (2.6) partition; (4.4)–(4.6) uses the massive variational problem with no next-scale averaging
mass, and p. 531 says the fluctuation integral is analyzed as in P5 §3. It then applies part of P6 §2, omitting P6 (2.1) so `S_{k+1}=∅`, and obtains (4.7)–(4.9). Neither these pages nor P4
§6 define a final localization-parameter family. The paper therefore supports reuse of the *procedure*, but does not settle which operator-level family implements it.

**REFUTED as a source identification.** `Green/FinalCutComplex.lean:183:finalOpCutC` multiplies entries of the coarse Schur complement across cells by `s(c x)s(c y)`. That formula is absent
from the cited last-step pages, while P3's displayed family cuts parametrix walk factors. It is unjustified to call `finalOpCutC` “the papers' cut family.” The stronger assertion that P7
*explicitly prescribes* the same generalized-walk family is also unsupported; the exact last-step implementation is OPEN.

## 3. Reuse and the radius obstruction

**PROVED.** `Green/FinalMassGreen.lean:79–83:finalOp` is `U=aI-a²Q(H_0+aQ^*Q)⁻¹Q^*` on the coarse unit torus, where `H_0=(L^k)^2(-Δ)+v`; `Green/FinalHessian.lean:191:finalHessian_eq_split`
splits longitudinal `aP_h` and transverse `U(1-P_h)`. By contrast, `Localization/Decoupled.lean:70–96` fixes `dirichletOperator G a ν α` on `G.Ω 1`, its cube cuts, and `DGSetting`;
`FamSpec` quantifies over such `GeneratingSet` data only. **REFUTED:** there is no definitional `GeneratingSet` or one-level instantiation making this particular long-range `U` the landed
`dirichletOperator`. The final step has no next-scale averaging term (P7 p. 530 and `FINALMAP.md`), so one must generalize the parametrix hypotheses or build a separate final-mass
instance.

**PROVED.** `Green/KF0WalkSeries.lean` treats `(-Δ+ν)⁻¹` by nearest-neighbor adjacency; `Green/KernelSeriesGeneral.lean:532–566` gives `walkPieces`, `genKernel_walkPieces`,
`walkPieces_rowBound`, and `walkPieces_range`. These are for a lattice covariance, whereas `finalOp` is a Schur complement and `finalHessian_inv` contains `U⁻¹`. **REFUTED:** substituting
`walkPieces` directly for the final covariance is not an identity.

**PROVED (why a bare nearest-neighbor cut is too narrow).** For `K=(-Δ+v)=(2d+v)I-A`, weighting every cross-cell adjacency by at most `ρ²` gives the absolute Neumann condition
`ρ²·2d/(2d+v)<1`, or $\log\rho<\tfrac12\log(1+v/(2d))$. At `d=L=3`, `v>7/72` allows only about `0.0081` at the lower endpoint, and even `v=1` allows less than `0.078`. Adjacent `M` cells
share distance-one bonds; crossing their boundary costs one walk step, independent of `M`. The claim that each crossing automatically earns `e^{-cM}` is **REFUTED**.
For the actual fine operator `H_0=(L^k)^2(-Δ)+v`, the analogous absolute ratio is `2d(L^k)^2/[2d(L^k)^2+v]`, which gives a still narrower edge-cut disc.

**PROVED (the actual localization price).** `Localization/I5Param.lean:259:abstract_expansion_on` requires parameter radius `e^{κ₁}` with `κ₁≥1`, and returns a coefficient bound
`B e^{-(κ₁-1)|C|}`. `Localization/I5Expansion.lean:107:localization_expansion` additionally requires `4d(2L+1)^d κ≤κ₁` and the displayed `h1,hlog` entropy inequalities to deliver
`e^{-κ₀ treeLenCovOne-2κ treeLenCov}`. Thus the preceding bare-walk radius cannot feed the *landed* expansion at any stopping mass. A custom small-radius expansion would need new entropy
and rate estimates; P7's (4.13) bound does not follow from `logρ≈0.008`.

## 4. Corrected FINALMAP S2 specification

**OPEN (recommended family: path-tagged macroblock parametrix of `U+t`).** Work on `V=L1Torus d N₀` and fix `M` scale cores `C_z`, enlarged boxes `B_z`, and a partition `χ_z` supported
in the interiors of `B_z`, with `∑χ_z=1`, overlap at most `J_d`, and `|χ_z(x)-χ_z(y)|≤C_{χ,d}dist(x,y)/M`. For arbitrary torus side, include a one-box case when `N₀\lesssim M`. Choose
deterministic shortest paths and a set `V_z(x,y)` of parameter cells meeting `B_z` or that path, with `|V_z(x,y)|≤H_d+C_{p,d}dist(x,y)/M`. These geometry lemmas are OPEN;
`J_d,C_{χ,d},H_d,C_{p,d}` must be positive and fixed independently of the volume and `k`.

**OPEN (exact algebraic definition).** Let `P_z` project to `B_z`, `H_z(t)=P_z(U+t)P_z+(1-P_z)`, `G_z(t)=H_z(t)^{-1}P_z`, and `R_z(t)=χ_z-(U+t)χ_zG_z(t)=-[U,χ_z]G_z(t)`. For
`τ_z(x,y;s)=∏_{P∈V_z(x,y)}s_P`, define entrywise `G_*(s,t)_{xy}=∑_z τ_z(x,y;s)(χ_zG_z(t))_{xy}`, `K(s,t)_{xy}=∑_z τ_z(x,y;s)R_z(t)_{xy}`, and
`G_{\rm fin}(s,t)=G_*(s,t)(1-K(s,t))^{-1}`. At `s=1`, `(U+t)G_*(1,t)=1-K(1,t)`, hence `G_{\rm fin}(1,t)=(U+t)^{-1}`. The family is *not claimed* to be the inverse of any entrywise-cut
operator at `s≠1`. The path tags are needed because `U` has infinite range: `[U,χ_z]` can jump across many cells, so tagging only `z` would fail exact parameter locality.

**PROVED input, OPEN macroblock estimate.** `FinalMassGreen.lean:finalMass_isCoercive` gives `g=finalGap d L=7/[8L²(8d+3)]`, `finalMass_entry_decay` gives `C₀e^{-δ₀dist}` with
`δ₀=blockDecayRate d`, and `finalMass_resolvent_decay` gives `2/(g+t)e^{-r_*dist}` with `r_*=finalRate d L`. `FinalCutFamily.lean:finalOpCut_isCoercive`, `finalOpCut_resolvent_decay`,
and `finalOpCut_resolvent_eq_on` apply to the two-cell compression `B_z,B_z^c`, supplying the gap `g+t` on the `B_z` block and the inverse bound for `G_z(t)` (the auxiliary complement has
gap `1`). The new proof must sum the commutator; no `finalCutBoundary` smallness is used.

**OPEN (explicit admissible radius and bounds).** Put $r=\tfrac14\min(δ_0,r_*)$, $B_0=\mathrm{ballConst}(d,r_*/2)$, $B_1=(4/δ_0)\mathrm{ballConst}(d,δ_0/4)$, and
$$
 B_{d,L}=2J_dC_{χ,d}C_0 B_1\,(2/g)B_0,\quad
 κ_{\max}(d,L,M)=\min\left\{\frac{rM}{2C_{p,d}},\frac1{H_d}\log\frac{M}{4B_{d,L}}\right\},\qquad
 R_{\rm fin}(v,d,L,M)=e^{κ_{\max}} .
$$
The notation `R_fin(v,d,L,M)` is uniform in `v∈(7/(8L²),1]`; its displayed lower bound uses the landed fixed `g`. For `M>4B_{d,L}` and `0≤κ<κ_max`, the proposed weighted row and column
estimate is `q(M,κ)=B_{d,L}e^{H_dκ}/M<1/4`, after absorbing `e^{C_{p,d}κ dist/M}` into the available entry decay. Then `1-K(s,t)` is invertible for `‖s‖_∞<e^κ`, and the family is analytic
there with
$$
 \sup_x\sum_y e^{r\,dist(x,y)}|G_{\rm fin}(s,t)_{xy}|
 \le \frac{J_d e^{H_dκ}}{1-q(M,κ)}\frac{2B_0}{g+t},
 \qquad t\ge0 ,
$$
and the same column bound. This is a **specification**, not a landed estimate; the path-tagged summation and column argument are OPEN.

**OPEN (square root and locality).** Define `C_{\rm fin}(s)=π^{-1}∫_0^∞t^{-1/2}G_{\rm fin}(s,t)dt`. Uniform domination above gives an analytic family and the same weighted row/column bound
with `2B_0/√g` replacing `2B_0/(g+t)`; at `s=1` it equals `Localization.sqrtMat U` by `FinalMassSqrt.lean:finalMass_resOK` and the definition of `sqrtMat`. The tagged Neumann series must
prove that changing parameters outside visited cells leaves each localized coefficient unchanged. This is the replacement for `finalCutComplex_*` in FINALMAP S2; the gap belongs to `U+t` and
each real block compression, while the complex family has a defect-inverse bound, not a separately asserted coercive cut operator. Extending it to the physical `h,E(z)` chart remains
conditional on OPEN `FINAL-COMPLEX-DOMAIN`.
For a unit real `h`, `finalHessian_eq_split` and `finalHessian_inv` then combine the scalar family with the constant longitudinal term $a^{-1}P_h$; the inverse square root combines $a^{-1/2}P_h$ with $C_{\rm fin}(1)(1-P_h)$. Complex `h` requires the landed `projHC` chart and the same open physical-domain bridge.

**PROVED reuse and limits.** `FinalCutFamily.lean` retains the real block-compression gap, resolvent, square-root decay and exact cut-locality; `FinalCutComplex.lean:cutMatC_entry_analytic`
is useful algebra, and its `finalCutWeightedBound` is valid under its own margin. The proof of `finalCutBoundary_le_sep` can be adapted to a separately defined long-hop tail; its stated
hypothesis requires **every** pair of differing cells to be separated by `M`, so it does not apply to an ordinary partition. `FinalCutComplex.lean:finalCutComplex_isCoercive` and its inverse/square-root conclusions stay conditional on
`(ρ²+1)S_∂<g`; `finalCutBoundary_le` alone supplies no such inequality.

## 5. Bounded Lean leaves and the source question

**OPEN leaf 1 (strong, start now, ≤300 lines).** `finalMacroCover`: cores, enlarged boxes, `χ_z`, bounded overlap, Lipschitz bound, deterministic path tags and `|V_z(x,y)|` estimate on
every torus, including `N₀<M`. Inputs: torus geometry, `ballConst`.

**OPEN leaf 2 (Sonnet, start now, 100–180 lines).** `finalLocalBoxResolvent`: define `H_z(t),G_z(t)`; prove `IsUnit H_z(t)`, the gap `g+t` on the `B_z` block, and local entry bound
`2/(g+t)e^{-r_*dist}`. Inputs: `finalOpCut_isCoercive`, `finalOpCut_resolvent_decay`, `finalOpCut_resolvent_eq_on`.

**OPEN leaf 3 (strong, after 1–2, ≤300 lines).** `finalPathDefect_weighted`: exact `R_z=-[U,χ_z]G_z`, first-moment bound `B_1`, path-factor bound, `q(M,κ)<1/4` for both rows and columns.
Inputs: `finalMass_entry_decay`, leaf 1, leaf 2. Split the column proof if it exceeds 300 lines.

**OPEN leaf 4 (Sonnet, after 3, 150–240 lines).** `finalWalkResolvent`: define `G_fin`, show `G_fin(1,t)=(U+t)⁻¹`, `AnalyticOnNhd` on `‖s‖<R_fin`, and the displayed resolvent bound.
Inputs: `Localization/DecoupledGs.lean:neumann_isUnit`, leaf 3.

**OPEN leaf 5 (strong, after 4, ≤300 lines).** `finalWalkLocality`: each series term has exactly its visited-cell dependency and connected cut coefficients satisfy a `LocalityAEOn`
analogue. The nonlocal entry of `U` is why this is a separate mathematical proof, not an application of `DecoupledFieldLocal`.

**OPEN leaf 6 (Sonnet, after 4–5, 160–260 lines).** `finalWalkSqrt`: Stieltjes integration, analyticity, `C_fin(1)=sqrtMat U`, and weighted bounds. Then a separate ≤300-line FINALMAP
consumer checks the `abstract_expansion_on` radius `κ₁≥1`, entropy inequality, `P7` polymer rate and physical `FINAL-HESSIAN-BRIDGE` /`FINAL-COMPLEX-DOMAIN` premises; none is supplied by
leaves 1–6.

**OPEN (text-ready author question; do not send).** “In P7 §4, when the final fluctuation covariance of P4 (6.4)–(6.6) is localized, is the intended complex interpolation the P3 (2.8)
generalized-walk parametrix applied to the massive final operator, with parameters on visited localization cubes? If so, what precise local operator or path rule handles the long-range
coarse Schur complement, and where is the `M^{-1}` defect and the radius required by P6 localization established? We find no formula for this family in P7 pp. 529–531 or P4 pp. 719–720.”

**Confidence.** High on the landed step mechanism, the source silence in P7 §4, and failure of the entrywise-cut bound. Medium on the path-tagged coarse parametrix: the algebra and
quantitative route are sound, but the uniform macrocover, path estimate and exact locality need proofs. No physical final-density localization or P7 closure is claimed.
