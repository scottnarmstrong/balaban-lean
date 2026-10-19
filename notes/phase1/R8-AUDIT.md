# R8 part 1 audit (W1137, refute-first), at c72c2144

Method: compared every body at `6fe02c98` with the new instance bodies (`git diff 6fe02c98 c72c2144`: only proofs
changed, no landed statement changed); compiled `example`s (scratch, deleted); read P3 pp. 78-79 (4.44)-(4.47) and
`coef_eTermFun_replacement_localB`, `localB`-marked form of `LocalClassDensityMarks.lean` (l. 1387-1660).

## Verdict table
| object | (1) fidelity at `Gb = S.G'`, `self` | (2) fidelity at a local `Gb`, `canon` | (3) clause hypotheses |
|---|---|---|---|
| `markedHatPsiFBg` | OK (`markedHatPsiF` is the body at `liftC`; `markedHatPsiF_eq_hatPsiF_add` is rfl) | OK, see (4) | n/a |
| `FFmarkedBg`, `evDecBg` | OK (`FFmarked_apply`, `evDec_eq_evDecBg` rfl) | OK: `T.par (extParams ..)` is the `τ w` of `coef_eTermFun_replacement_localB`, fluctuation data `flEdat Gb Hm (F₁ (σ,Θ)) Θ.1 ..` is the local one | n/a |
| `decMarkGBg`, `decMarkCorrBg`, `decMarkCorrTermBg` | OK (compiled `example`: `decMarkG = decMarkGBg S S.G' (self S.hG')`, same for Corr, CorrTerm) | OK | UNCLEAR, see D2 |
| `e1MarkGParamGBg` | OK at `Zb = S.blockU z` (compiled `example`) | UNCLEAR, see D1 | see D2 |
| `physParamBg/InclBg/SΛBg/VBg` | OK (`physV = physVBg N S.G'`, `physSΛ = physSΛBg S.G'` by `rfl`, compiled) | OK as spaces | n/a |
| `BgTransport.canon` | n/a | OK with the caveat C1 | n/a |
| `canon_eq_self` | OK (see (5)) | n/a | n/a |

## (1) Fidelity at the step's set
`decMarkG`, `decMarkCorr`, `decMarkCorrTerm`, `e1MarkGParamG`, `physV`, `physSΛ` are the instances by `rfl`
(compiled in a scratch file against the built branch, all closed). The `rfl` lemmas for the old bodies exist and state
the old bodies: `decMarkG_eq_deriv_evDec` (DecMarkBlocks), `decMarkCorr_eq_decMarkG`, `decMarkCorrTerm_apply`
(DecMarkCorrCount.lean:386), `FFmarked_apply`, `evDec_eq_evDecBg`, `physV_eq_preimage`, `markedHatPsiF_eq_hatPsiF_add`.
Not stated as lemmas (only by the definition body): `markedHatPsiF = markedHatPsiFBg .. (liftC _)`, `decMarkG = decMarkGBg ..`,
`e1MarkGParamG = e1MarkGParamGBg ..`; harmless (checked here), but a one-line `rfl` lemma each would pin the instance.
No landed theorem statement changed (the diff in all 20 files shows only definition bodies, new theorems, and proofs).

## (2) Fidelity at a local set
- Parameters: `canon.par P = if P.1.2 ∈ Gb.Ω(k+1) then extS (coverOf Gp) s P.1 else 0` is literally the `τ w` of
  `coef_eTermFun_replacement_localB` (LocalPairReplacementLocalB.lean ~l. 280-300). Source (p. 79): "s' = 0 outside Y₁, s inside
  Y₁". Landed: s on every cube based in the top layer of `Gb`, 0 below. This is NOT the source's Y₁; it is what the landed lemma
  proves equal (coefficient in the cubes of `𝒞`, other cubes at 0, margin hypothesis `hmar`). So "top layer of Gb" is Y₁ only
  through that lemma. C1: `canon Gp Gb N` is defined for every `Gb`, but the identity with the ambient term holds only for
  `Gb = localB (k+1) .. Y⁺` with the margin `hmar`; the docstring "for any Gb" should say so.
- Lift: `liftZ Gb` is exactly the `if h : unitBlock x ∈ unitPts Gb then .. else 0` of the local marked form. Restriction `resZ`
  is exactly the `if p.1.1 ∈ unitPts Gp then ψh .. else 0` of that form (always true for a level `Gp`).
- Hat variable: `hatSqrtF Gb .. = decCovSqrt Gb (compWeight L a₁) a₁ ν (F₁ (s,Θ)).2 (extS Gb s) (barField Gb Θ.1 ..) (unitQ Gb) (unitP Gb)`
  is the local form's covariance square root with the local background at the clipped datum. Fluctuation blocks, measure, `Sol`
  and `Hm` enter as parameters (free `Hm`; the caller must take `Hm = localB k .. Ω_k(Gb)`, as in the landed lemma; nothing ties
  `Hm` to `Gb`, which is a caller obligation, not a defect).
- No datum transport: `u.1`/`Θ` is passed to `F₁`, `Sol` unchanged and must lie in `XiCRaw Gb`; the landed local identity uses
  `localBRestrict D` (= `clipRaw Gb (rawOf D)`, `rawOf_localBRestrict`). See D1.

## (3) Hidden steps
`hloc`, `hcau`, `hJ2`, `hJ4` are statements about the terms `evDecBg` on `Gb` (locality in the step's hat on the unit points of
`Y`, Cauchy bound, joint analyticity, analyticity of the derivative on `physVBg`): the source properties of P3 p. 78-79 and
Lemma 4.2, not steps of the lemma layer. The lemma layer's own steps (hat-field membership, `agHatFDir_hatOf`, Taylor remainder,
sums) are proved. Verdict OK on shape; open obligations for (A1)-(A5). Two points:
- D2 (UNCLEAR, possibly false as stated): `hloc`, `hcau`, `hJ2` quantify `∀ Y` for one fixed `Gb`, and on the whole chart
  `XiCRaw Gb .. eps` times the box. Locality "exact on `Y`" is true only for labels `Y` whose cubes and the cubes meeting `X₁f`
  lie in the top layer of `Gb` with the margin; for other `Y` the term on `Gb` is a coefficient over families with cubes outside
  the top layer, which `canon.par` fixes at 0, so it is 0 or reads only the top layer: probably still true, but nobody has
  checked it, and it is not a consequence of the landed replacement lemmas, which are for data of the form `clipRaw` of a datum of
  the ambient chart only (W1075: extending a local datum to the ambient chart fails at radius C·ε, C > 1.7). The clauses on the full
  local chart must be proved on `Gb` directly (P3 Lemma 4.2 with `𝔹_{k+1}(Y)`). Smallest fix: state `hloc/hcau/hJ2` for `Y ⊆ Gb.Ω(k+1)`
  (or index them by the pair `(Gb, Y)`), so that the premise is the source's clause and cannot be refuted by a far label.
- The hat clause `AgHatDir S.hG' Y u u'` asks agreement of `u.1` only on `thickSet S.G' Y` and of the hat on the unit points of `Y`.
  For the canonical `Gb` this is the right set: cubes with `s ≠ 0` lie in `Y` and `C^{1/2}_Gb(σ)` is block-decoupled elsewhere
  (this is the ambient `eTermFun_level_hat_congr` + `localHatLift_eq_hatPsiF_localB` reading), so `AgHatDir S.hG'` on the step's hat
  is not false for `canon`; it is also not proved.

## (4) The mask
Proved (scratch, compiled, deleted): for `Gp` a level set, `Zm : Finset (unitPts Gp)` and
`Zb := univ.filter (fun q : unitPts Gb => ⟨q.1, mem_unitPts_of_isLevel hG' q.1⟩ ∈ Zm)`,
`markedHatPsiFBg Gb a₁ ν (liftZ Gb) cc F₁ Zb u t s Θ ψh x i = (u + if unitPt hG' x ∈ Zm then t else 0) *
 (if h : unitBlock x ∈ unitPts Gb then (cc • (hatSqrtF Gb a₁ ν F₁ s Θ *ᵥ ψh)) (⟨unitBlock x, h⟩, i) else 0)`
for all `x i` (proof: unfold, `liftZ_apply`, case split on `unitBlock x ∈ unitPts Gb` and `unitPt hG' x ∈ Zm`, `ring`). So the Bg
mask (on `Gb`'s unit lattice before the lift) equals the local marked form of `LocalClassDensityMarks` (`1[unitPt x ∈ Zm]` on the
fine site, 0 off the unit blocks of `Gb`) for `Zb` = the preimage of `Zm` in `unitPts Gb`, for every `Zm`; no condition on the
masks of the chain. Fix to record: `e1MarkGParamGBg` takes `Zb` free; the consumer must pass this `Zb`, not e.g. `Gb`-blocks of `z`;
add the lemma to `BgTransport.lean` as `markedHatPsiFBg_liftZ_preimage_mask`.

## (5) `canon_eq_self`
Hypothesis: only `hG' : IsLevel Gp (k+1)`; statement `canon Gp Gp N = self hG'` (equality of structures, so `par`, `lift`, `res`
agree: `P.1.2 ∈ Gp.Ω(k+1)` by the level property, `extS` on `cubeIdx` is `s`, `liftZ` is `liftC` as every unit block is a unit
point). It covers exactly the step's own set (`Gp = S.G'`, `hG' = S.hG'`); it does not say `canon Gp Gb = self` for another level
set `Gb` (the types differ), nor is it used by the landed instances, which use `self` directly. OK.

## Defects
- D1 (design gap, UNCLEAR whether it blocks): `e1MarkGParamGBg` has one `Gb` and `θ : physParamBg N Gb` for ALL bridge labels `i`.
  The source recomputes each label `Y′` on `𝔹_{k+1}(Y′)`, so at local sets the family over labels has `Gb` depending on `Y′`
  and `θ` must stay in the step's `physParam S` with the datum clipped inside (`clipRaw Gb`, linear, at radius `ε′ ≥ ε(1 + (2K₁+1)C₁)`
  as in `coef_eTermFun_replacement_localB_restrict`). `BgTransport` has no datum map. Smallest fix: add a field
  `dat : RawData →ₗ[ℂ] RawData` to `BgTransport` (`self`: id; `canon`: `clipRaw Gb`) and let `FFmarkedBg`/`decMarkGBg`/`e1MarkGParamGBg`
  read `T.dat Θ`, or add a lemma that the clip is continuous linear `physParam S → physParamBg Gb` mapping `physV S .. eps` into
  `physVBg Gb .. eps′`, so the composite is analytic; without one of them the generic marks cannot be assembled in a `ParamMarkFamily`
  over `physV S`. Only definitions at `Gb = S.G'` are unaffected.
- D2 above (quantifier `∀ Y` for fixed `Gb` in `hloc/hcau/hJ2`).
- C1 above (`canon` doc), and the three missing one-line `rfl` instance lemmas.
No refutation of (1), of the parameters/lift/restriction of (2), or of the mask (4).
