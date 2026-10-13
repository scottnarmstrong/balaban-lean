# AUDIT-4 — final tagged integral and observable families

Source snapshot: `/home/scott/Balaban` main at `340e13ec99c68a7855bd83907417fecce319090f` (later than `681a364`), read only. Both `FinalTagSupport.lean` and `FinalTaggedSqrt.lean` were present. Verdicts below assess the cited declarations and their scopes, not unproved physical handoffs.

## D1. Tagged rows and the last integral

**FAITHFUL —** `Balaban/Green/FinalTaggedRow.lean:76-121,235-255`. The generic inverse lemma assumes `w≥1`, `w(x,x)=1`, and `w(x,y)≤w(x,u)w(u,y)`. For `w=e^{r dist}` these follow from `r≥0`, `dist(x,x)=0`, and the triangle inequality of the actual `L1Torus` metric; the proof explicitly constructs all three. The Neumann factor is `1/(1-q)` with `q=1/4`, giving `4/3`.

**FAITHFUL —** `Balaban/Green/FinalTaggedRow.lean:129-131,143-150,209-215,220-228,284-315`; `Balaban/Green/FinalTaggedSqrt.lean:119-156,180-199,225-252`. The row constant is `2 exp(pdH d·κ) ballConst d (pdEps d L/2)/(finalGap d L+t)`, multiplied by `4/3` for `Gfin`; the integrated `Cfin` bound replaces the denominator by `sqrt(finalGap d L)`. None contains torus volume `N₀` or `M` after its two explicit largeness inequalities (`FinalTaggedRow.lean:220-225`), and `t≥0` appears only through the resolvent denominator. Column estimates incur `r'<r` and `ballConst d (r-r')`; they are not same-rate row estimates (`FinalTaggedRow.lean:284-295`; `FinalTaggedSqrt.lean:225-252`).

**FAITHFUL, with scope limit —** `Balaban/Green/FinalTaggedSqrt.lean:45-52,254-265,267-300`; `Balaban/Localization/DecoupledCovPrincipal.lean:183-185,688-691`; `Balaban/Green/FinalMassSqrt.lean:51-56`. `taggedCfin(1)` equals the campaign's `sqrtMat(finalOp)`, namely the **principal inverse square root**, whose square is `finalOp⁻¹`. This is the inverse-square-root object requested by FINALMAP S2, but the tagged file itself gives neither a square-root identity for `s≠1` nor the determinant and physical-Hessian handoff. Entry analyticity is stated only for the finite-dimensional **open** cell polydisc `∀p, ‖s p‖<exp κ`. **WEAKER THAN CLAIMED if used as analyticity at the physical base for every `κ≥0` —** the theorem permits `κ=0` (`FinalTaggedSqrt.lean:112-115,269-271`); then `s≡1` lies on the boundary. `κ>0` is needed for that use.

## D2. Tagged support

**FAITHFUL —** `Balaban/Green/FinalTagSupport.lean:150-182`. `boxG` reads `U` on `B_z×B_z`. `boxR` additionally reads `U(x,w)` for `w∈B_z`; the row index `x` need not be in `B_z`. Agreement on those entries gives equality of the matrices *before* taking inverses, so the statement uses the same total `Matrix` inverse on both sides even at singular inputs. No invertibility premise is smuggled into the support congruence.

**FAITHFUL —** `Balaban/Green/FinalTagSupport.lean:46-49,54-98,121-142,198-224`; `Balaban/Localization/AbstractExpansion.lean:92,109-145,295-317`. `supportedOn C` means every coordinate outside `C` is zero, exactly the set used by the coefficient congruence consumer. A tag monomial vanishes unless its tags are contained in `C`. For the macro cover, contained tags put the entire box and both endpoints in `macRegion C`, so region agreement supplies both the `B_z×B_z` entries and the possibly external row `U(x,B_z)`. `taggedGfin_congr_of_agree_on_region` proves equality of `taggedG`, `taggedK`, and the *same* `taggedGfin` inverse convention.

## D3. One observable family

**FAITHFUL —** `Balaban/Inhabited/ObsTiltFamily.lean:213-249,261-296`. After the scale, `q`, `StepScaleData`, step setting, and `Kc` binders, the theorem chooses `Lb, Lab, εH, A` **before** universally quantifying the fibre datum `D'`, source `g`, and `t`. The `∀ᵐ x` precedes all three universal quantifiers, hence a single exceptional null set works for every admissible fibre datum, every `‖g‖₁<q`, and every `t∈[0,1]`. The proof combines its two source identities by intersecting their a.e. sets (`:279-294`).

**FAITHFUL, conditional on the fibre —** `Balaban/Inhabited/ObsTiltFamily.lean:46-60,223-259`; `Balaban/Inhabited/SourceExponentFamily.lean:60-65`. `A` lives on the selected `CubeLabels` system `Lab`; `physAct` and `tiltAct` live on `Lab.sum Lab`, with amplitudes `max(2εH,εH)` and `Rg·max(2εH,εH)` and a uniform bound on `2εH` independent of the datum and source (`ObsTiltFamily.lean:226-229`). The displayed holomorphy is of the **label activity** in physical parameter, interpolation variable, and tilt; the theorem contains no analyticity conclusion for the observable `M0C` in `g` (`:230-259`). Fibre identities require global `hDh` (`:237-249`); on a proper `Ω 1` with nonzero `h₀` that fibre is empty by `Balaban/Background/Data.lean:119`. The tower's own `lvTop` step datum has a separate inhabitance result (`Balaban/Inhabited/RenFibreDatum.lean:62-79`).

## D4. Remainder mark congruence

**FAITHFUL —** `Balaban/Fluctuation/ObsRemainderFamily.lean:44-78,237-250`. `gsumCoeff_congr_ae` assumes a.e. equality separately for every real `s∈[0,1]` and index, allowing the null set to depend on `s`. Its proof first applies `Gst_congr_ae` to the **inner block-configuration integral at each fixed `s`**, then uses pointwise interval-integral congruence; no joint null set in `(s,Φ)` is required. `gsumCoeff_obsGr_eq_obsGrFam` uses precisely the same `Act`, labels, index map, and test set on both sides; only the mark family changes.

**FAITHFUL —** `Balaban/Fluctuation/ObsRemainderClamp.lean:165-185`; `Balaban/Fluctuation/ObsRemainderFamily.lean:226-232`. A stronger, single block-product a.e. statement equates clamped and original marks for every raw datum, index and complex `u`; specializing `rawOf D` gives the a.e. hypothesis for the coefficient equality. `obsGrFam` is evaluated only where its raw datum belongs to the chosen chart set (`ObsRemainderFamily.lean:226-250`).

## D5. Corrected rooted count

**FAITHFUL —** `Balaban/Fluctuation/DecMarkCorrCount.lean:111-126,197-230,241-248,294-319`. All four conclusions use one `F₁,Sol`, one `decMarkCorrTerm`, and the same `markedOutDec`. The term is `t↦t·(-β·decMarkCorr)`; its derivative is `-β·decMarkCorr` (`:129-146`). The resummation proof invokes `sum_markedOutDec_eq_sum_of_vanishing` for that exact term and rewrites by its derivative theorem (`:294-319`).

**FAITHFUL, with hypothesis precision —** `Balaban/Inhabited/DecMarkCorrCountFromTower.lean:42-60,90-106,115-158`; `Balaban/Inhabited/MarkCorrBudget.lean:60-66,147-149`. The tower wrapper explicitly sets `cψ=p₁`, proves the `markedRad=decMR` radius inequality, constructs `MarkedEvJointPhysV` for **each** block at that same radius, and chooses a family of pairs (`DecMarkCorrCountFromTower.lean:124-150`). Thus the numerical-to-pair gap noted in AUDIT-3 is closed by this later declaration. `hRU` is the only *new radius-budget* input, and `exists_beta0_corrR` discharges it under its polylogarithmic `p₁` condition. **WEAKER THAN CLAIMED if “only hypothesis beyond scale data” is literal —** the theorem also explicitly assumes `5<N₁`, mass and β positivity/bounds, `p₁>0`, the step equality, and `S.p₁>0` (`:42-49`).

## D6. Leading caveats

For D1, state `κ>0` when using `taggedCfin_analyticOnNhd` at `s≡1`; the proved open domain excludes that point when `κ=0`, and `taggedCfin(s)` is not identified as a square root away from the base (`FinalTaggedSqrt.lean:254-271`). For D3, preserve the global `hDh` fibre condition when transporting the observable identity beyond the whole-torus tower step: on a proper `Ω 1` with nonzero `h₀`, it has no data to test (`ObsTiltFamily.lean:237-249`; `Background/Data.lean:119`; `RenFibreDatum.lean:62-79`).
