# R8 part 1: audit packet (W1129, 2026-10-19)

Ruling R8 (AGENTS.md, 2026-10-18): the step's mark objects become generic in a background generating set `Gb`, and the
step's own objects are the instance `Gb = S.G'`. Source: P3 pp. 78-79, (4.44)-(4.47). The expansion (cubes, connected
families, labels `Y ∈ 𝒟(𝔹_{k+1})`) is the step's expansion on `S.G'`. Inside each term the generating set is replaced by
`𝔹_{k+1}(Y)` (background, cover, `C^{1/2}`, fluctuation field, block energy), with the parameters kept on the cubes in
`Y₁` and set to 0 outside. The hat variable `ψ̂`, the fluctuation blocks and their measure are the step's.

**Transport** `BgTransport Gp Gb N` (`Fluctuation/BgTransport.lean`) is data, not a hypothesis. It has three fields:
`par : DecParams Gp → DecParams Gb`, the linear `lift` from the unit lattice of `Gb` to fine fields, and the linear `res`
from the hat of `Gp` to the hat of `Gb`. `BgTransport.self hG'` = `(id, liftC hG', LinearMap.id)` for a level set.
`BgTransport.canon Gp Gb N` gives the maps of P3. A cube of `Gb` based in `Ω_{k+1}(Gb)` gets `Dec2.extS (coverOf Gp) s
P.1` and every other cube gets 0. The lift is `liftZ Gb` (extension by zero off the unit blocks of `Gb`) and the
restriction is `resZ Gp Gb`. These are the inline forms of `coef_eTermFun_replacement_localB` and
`zeroSourceTerm_localB_hat`. `canon_eq_self` proves that at a level set `canon Gp Gp N = self hG'`.

**Generic definitions.** Each landed definition is now its instance at `Gb = S.G'`, `T = BgTransport.self S.hG'`, by
`rfl`. The old body is kept as an `rfl` lemma, named in the last column.

| generic | source object | landed instance (`rfl` lemma for the old body) |
|---|---|---|
| `markedHatPsiFBg Gb a₁ ν lift …` | marked hat field `u·lift(cc C^{1/2}_Gb(s)ψ̂) + t·lift(M_Z(cc C^{1/2}_Gb(s)ψ̂))`, P3 (4.46) | `markedHatPsiF` = core at `liftC hG'` (`markedHatPsiF_eq_hatPsiF_add`) |
| `FFmarkedBg Gp X₁f Gb a₁ ν T …` | cut-parameter functional of a term on `Gb`: `σ = T.par (extParams Gp X₁f s)`, `F₁/Sol/Φ` of `Gb` | `FFmarked` = core at `(Gp, self)` (`FFmarked_apply`) |
| `evDecBg` (abbrev) | `evTerm` over the step's families of `FFmarkedBg`: the term `𝓔(X,Y)` recomputed on `Gb` | `evDec` (body unchanged, `evDec_eq_evDecBg`) |
| `decMarkGBg S Gb T …` | `∂_t evDecBg … (Θ, T.res ψ̂(Φ))` at `t = 0`, `Θ` a datum of `Gb` | `decMarkG` (`decMarkG_eq_deriv_evDec`) |
| `decMarkCorrBg` | first-order Taylor remainder in `um` of `decMarkGBg` | `decMarkCorr` (`decMarkCorr_eq_decMarkG`) |
| `decMarkCorrTermBg` | `t ↦ t(−β decMarkCorrBg)`, with block energy `blockEnergyFun Gb Hm …` | `decMarkCorrTerm` (`decMarkCorrTerm_apply`) |
| `e1MarkGParamGBg S Gb T Zb …` | rooted corrected output at `θ ∈ rawSub Gb × sources`, gated on the chart `XiCRaw Gb …` | `e1MarkGParamG` at mask `Zb = S.blockU z` |
| `physParamBg N Gb`, `physInclBg`, `physSΛBg`, `physVBg` | parameter space and admissible set of the chart of `Gb` | `physParam`, `physIncl`, `physV` (`physV_eq_preimage`); `physSΛ` unchanged, `= physSΛBg S.G'` by `rfl` |

Why `Gb = S.G'` gives the landed objects: `self.par s ≡ s`, `self.lift ≡ liftC hG'`, `self.res ψ ≡ ψ` and
`(u.1, u.2) ≡ u`, so every landed body is the core body after δβη.

**Points for the auditor.** (1) `evDec` keeps its own body `evTerm … (FFmarked …)` and is the instance only by `rfl`, because its reducible
unfolding is used in 88 files.
(2) The mask of `markedHatPsiFBg` acts on the unit lattice of `Gb` before the lift, as in `markedHatPsiF`. The local
marked forms of `LocalClassDensityMarks` put `1[unitPt y ∈ Zm]` on the fine site instead. The two agree for `Zb` = the
unit points of `Gb` over `Zm`; this is not formalised.
(3) The lemma layer takes clause hypotheses on the terms on `Gb`: `hloc` (with `AgHatDir S.hG'` on the step's hat),
`hcau`, `hJ2`, and `hJ4` on `physVBg`. For the local `Gb` these are open, as (A1)-(A5) of the next waves.

## R8 part 2 (W1139): the determinant record and the direct terms

The step's expansion (cubes, polymers `T`, root `z`) is on `S.G'`; inside a term the generating set is `Gb`, the datum read through
`Tr : BgTransport S.G' Gb N`. Typing datum `Tr.Reads` (`T.dat (rawOf D)` is a datum of `Gb` for every datum `D` of the step); then
`Tr.gdat hT D : BgData Gb N` (`BgTransport.gdat`, `gdat_self` is `rfl`, `reads_self`).

| generic | source object | landed instance |
|---|---|---|
| `DetExpansionLocCBg S Gb Tr hT Zb m₀ z ε κ'' c` (DetOutputTerms) | terms of `-½ ∑_{y∈B(z)} tr 𝕃(y,y)` by polymers `T`, P3 (4.44)-(4.47), P4 (2.56): rooted trace on `Gb` over the mask `Zb ⊆ unitPts Gb` at the background of `Tr.gdat hT D`; chart `Ξ^c(Gb;1,ε)` at that datum; locality on `resDep Gb`; analyticity in the raw datum of the step | `DetExpansionLocC S m₀ z ε κ'' c` is an `abbrev` at `Gb = S.G'`, `Tr = self`, `Zb = S.blockU z` (fields defeq, since `self.gdat D = D` by structure eta) |
| `DetExpansionLocCBg.detGrouped`, `detGroupedC` and `_sum/_bound/_anchor/_local/_analyticOnNhd_rawSub/_physParam` | collar-hull regrouping | landed defs/lemmas are one-line instances (bodies call the generic ones) |
| `exists_detExpansionLocCBg_of_chart` | inhabitation (rule 10): `FlCore` of `Gb`, mask with `rootIdxOf y = z`, `|Zb| ≤ L^d` | `exists_detExpansionLocC_of_chart` is the call at `self` |
| `detTermLoc` (family `E T` on `Gb T`) | term of the polymer `T` recomputed on `𝔹_{k+1}(T)` | `detTermLoc_const` (`rfl`) |
| `DirectTermsBg S m₀ hp Gb Tr embB …` (DirectTermsBg) | direct terms with expansion variables `embB (Tr.res ψ̂)` | `DirectTerms` (`directTermsBg_self`, `rfl`) |
| `physInclTr`, `physVTr`, `isOpen_physVTr`, `physical_directTermsFamilyOn_Tr` | parameter `θ` of the step read as the datum `(Tr.dat θ.1, θ.2)` of `Gb`; admissible set `physSΛBg Gb` | `physInclTr_self = physIncl`, `physVTr_self = physV` (propositional; `physIncl` is a CLM, not unfolded) |

Why `Gb = S.G'` recovers the landed objects: `self.dat = id`, so `self.gdat D = D`; every generic field is the landed field after
unfolding. `DirectTerms` was already generic in the hat embedding and `DirectTermsFamilyOn` in the parameter map; `Gb` enters only through
`embB ∘ Tr.res` and `physInclTr Tr`, so the lemma layer (`labelAct_of_directTerms`, `dtAct`, `labelActFamilyOn`, `paramMarkFamilyOn_of_marks`)
applies unchanged and is not copied.

Points for the auditor. (1) Fields of `DetExpansionLocCBg` ask the chart of `Gb` at `Tr.gdat hT D`, not the step's chart; at `self` they coincide.
(2) The dependency-radius lemmas (`term_eq_of_agree_near`, `_cellNear`, `detGrouped_local`, `detGroupedC_local`) need `IsLevel Gb (k+1)`: the radius
lemmas of `FootprintMargin` are for level sets only; for a local `Gb` (not a level set) locality comes from the field `local_resDep` and the margin.
(3) `Tr.Reads` is not proved for `BgTransport.canon`: the clipped datum is layer-constant for `Gb` only under conditions on the layers of `Gb`.
(4) `physical_directTermsFamilyOn` (landed) was not rewritten as the instance, because `ParamActivitySubspace` is imported by `DirectTermsBg`.
