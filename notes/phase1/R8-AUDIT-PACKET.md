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
