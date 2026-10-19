/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalHatTerm
public import Balaban.Fluctuation.MarkedEvJoint
public import Balaban.Fluctuation.LocalClassTau

/-!
# The marked terms recomputed on a background generating set: bound and analyticity

P3 Lemma 4.2 and P6 Lemma 4.1 (analyticity and bounds of the localized terms on a modified
generating set) for the marked terms `evDecBg` of the step's expansion recomputed on a background
generating set `Gb` with the canonical transport (ruling R8; P3 pp. 78-79, (4.44)-(4.47)), on the
chart `Ξ^c(Gb; 1, ε)` of `Gb` itself.  The expansion is the step's (`S.G'`, cover data
`(m₀, j, 𝒦_X)`, region `X₁`), the parameters are transported by `BgTransport.canon` (kept on the
cubes based in the top layer of `Gb`, `0` on the others), the hat variable is the restriction of
the step's hat variable, and the tangent is the marked local hat field of `Gb`.  Only (AE1) of
Theorem I-5 is used (the Cauchy bound of the coefficients and the Peierls sum over the connected
families), not the locality (AE2).

* `clipRaw_of_mem_rawSub`: the cut-off to the data of `G` is the identity on the data of `G`;
* `FFmarkedBg_canon_apply`: the functional of a term with the canonical transport, unfolded;
* `norm_deriv_mark_le_of_joint`: the Cauchy estimate of the mark derivative from joint analyticity
  and a bound;
* `evDecBg_canon_bound_analytic`: for a functional `Φ` analytic and bounded on the realizable
  triples `FlRealLC Gb H⁻ … X₁g …` of `Gb` (frozen region `X₁g` in `X₁` and in the top layer of
  `Gb`), every term `evDecBg … um tm Y (Θ, res ψ̂)` is bounded by
  `E_b e^{-κ₀ d^{cov,1}_j(X) - 2 κ_dec d̃^{cov}(Y)}` and analytic in `((Θ, ψ̂), (um, tm))` on
  `(Ξ^c(Gb; 1, ε) × B̂) × W`, `W = {(u, t) | (‖u‖ + ‖t‖) m_R < δ₁}`;
* `evDecBg_canon_fields`: the hypotheses `hcau`, `hJ2`, `hJ4` of the field lemmas of the marks on
  `Gb` (`deriv_evDecBg_hatOf_fields_gen`, `decMarkCorrBg_fields_of_gen`) on the chart of `Gb`
  (`Gg = Gb`): the Cauchy estimate of the mark derivatives, the joint analyticity, and the
  analyticity of the derivative marks on `physVBg Gb × {‖u‖ < a}`.
-/





@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Finset Matrix

section ClipRaw

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The cut-off to the data of `G` is the identity on the data of `G`**: a raw datum of a datum of
`G` (zero off the data sites, `h̃` zero off `Ω₁`) is unchanged by `clipRaw G`. -/
theorem clipRaw_of_mem_rawSub (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    {r : RawData d L (N₁ * L ^ m₁) K N} (hr : r ∈ rawSub N G) : clipRaw G r = r := by
  classical
  obtain ⟨-, -, h1, h2⟩ := hr
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · by_cases hx : x ∈ dataSites G
    · simp [clipRaw, hx]
    · simp [clipRaw, hx, h1 x hx]
  · by_cases hx : x ∈ G.Ω 1
    · simp [clipRaw, hx]
    · simp [clipRaw, hx, h2 x hx]

end ClipRaw

section Cauchy

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- **The Cauchy estimate of the mark derivative from joint analyticity.**  If `Ev um tm u` is
analytic in `(u, (um, tm))` at every point of `S × W`, `W = {(u, t) | (‖u‖ + ‖t‖) m_R < δ₁}`,
`δ₁ > 0`, and bounded by `B` there, then `‖∂_t Ev um t u|_{t=0}‖ ≤ B / t₀` for `u ∈ S`,
`‖um‖ ≤ a`, `0 < t₀ ≤ b`, `(a + b) m_R < δ₁` (`norm_deriv_mark_le` on the slice at `u`). -/
theorem norm_deriv_mark_le_of_joint {S : Set U} {mR δ₁ : ℝ} (hδ₁ : 0 < δ₁) {Ev : ℂ → ℂ → U → ℂ}
    {B : ℝ}
    (hJ : AnalyticOnNhd ℂ (fun p : U × (ℂ × ℂ) => Ev p.2.1 p.2.2 p.1)
      (S ×ˢ {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * mR < δ₁}))
    (hB : ∀ p ∈ S ×ˢ {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * mR < δ₁}, ‖Ev p.2.1 p.2.2 p.1‖ ≤ B)
    {a b t₀ : ℝ} (ht : 0 < t₀) (htb : t₀ ≤ b) (hab : (a + b) * mR < δ₁) {um : ℂ}
    (hum : ‖um‖ ≤ a) {u : U} (hu : u ∈ S) :
    ‖deriv (fun t : ℂ => Ev um t u) 0‖ ≤ B / t₀ := by
  have hg : AnalyticOnNhd ℂ (fun w : ℂ × ℂ => Ev w.1 w.2 u)
      {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * mR < δ₁} :=
    hJ.comp (f := fun w : ℂ × ℂ => (u, w)) (fun _ _ => analyticAt_const.prod analyticAt_id)
      (fun w hw => ⟨hu, hw⟩)
  exact norm_deriv_mark_le hg (fun w hw => hB (u, w) ⟨hu, hw⟩) ht htb
    (fun t htt => mem_markedRadiusSet_of_pos hδ₁ hab hum htt)

end Cauchy

section Terms

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱb ϱm : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ}

/-- **The functional of a term recomputed on `Gb` with the canonical transport**, unfolded: the
datum is the cut-off `clipRaw Gb Θ`, the parameters are the transported `canon.par`, the lift is the
extension by zero and the hat variable is the restriction `resZ`. -/
theorem FFmarkedBg_canon_apply {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb)
    (a₁ ν : ℝ) (cc : ℂ)
    (F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (Φ : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (Zm : Finset (unitPts Gb)) (um tm : ℂ)
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ))
    (s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) :
    FFmarkedBg Gp X₁f Gb a₁ ν (BgTransport.canon Gp Gb N) cc F₁ Sol Φ Zm um tm
        (u.1, (BgTransport.canon Gp Gb N).res u.2) s =
      Φ (F₁ ((BgTransport.canon Gp Gb N).par
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s), clipRawL Gb u.1))
        (Sol ((BgTransport.canon Gp Gb N).par
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s),
          flEdat Gb Hm (F₁ ((BgTransport.canon Gp Gb N).par
            (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s), clipRawL Gb u.1))
            (clipRawL Gb u.1).1
            (markedHatPsiFBg Gb a₁ ν (liftZ Gb) cc F₁ Zm um tm
              ((BgTransport.canon Gp Gb N).par
                (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s))
              (clipRawL Gb u.1) (resZ Gp Gb u.2)))).1
        (clipRawL Gb u.1, markedHatPsiFBg Gb a₁ ν (liftZ Gb) cc F₁ Zm um tm
          ((BgTransport.canon Gp Gb N).par (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s))
          (clipRawL Gb u.1) (resZ Gp Gb u.2)) := rfl

/-- **The marked terms recomputed on a background generating set are bounded and analytic on its
chart** (P3 Lemma 4.2 at `Gb`, (AE1); P3 pp. 78-79, (4.44)-(4.47)).  Let `Gb` carry a cover base
for the decoupled background (`Sb`), `H⁻ ≺ Gb` without layer `k + 1`, and `(F₁, Sol)` an analytic
decoupling pair of `(Gb, H⁻)` with its defining properties.  Let the step's expansion of an old
polymer `X` (cover data `(m₀, j, 𝒦_X)`, `X₁f = X₁`) satisfy the entropy conditions, and let the
functional `Φ` be analytic on the realizable triples `FlRealLC Gb H⁻ … X₁g …` and bounded there by
`E_b e^{-(κ_dec - 1) d^{cov,1}_j(X)}`, for a frozen region `X₁g ⊆ X₁f` in the top layer of `Gb`.
Then every term `evDecBg … um tm Y (Θ, res ψ̂)` of the canonical transport (the datum `Θ` of the
chart `Ξ^c(Gb; 1, ε)`, the restriction `res ψ̂` of a hat variable of the step with `|ψ̂| ≤ c_ψ`,
marks with `(‖um‖ + ‖tm‖) m_R < δ₁`):

1. is bounded by `E_b e^{-κ₀ d^{cov,1}_j(X) - 2 κ_dec d̃^{cov}(Y)}`;
2. is analytic in `((Θ, ψ̂), (um, tm))` at every point of `(Ξ^c(Gb) × B̂) × W`. -/
theorem evDecBg_canon_bound_analytic (hk1 : 1 ≤ k) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L a₁) ν Kc Cx)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁) (hPmp : Precedes Hm Gb) (hHm : Hm.Ω (k + 1) = ∅)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gb) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    -- the step's expansion of the old polymer
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb)
    -- the frozen region of `Gb` and the functional
    {X₁g : Finset (CTorus d L N₁ m₁ (k + 1))} (hX₁g : ∀ x ∈ X₁g, x ∈ X₁f)
    (hX₁gtop : ∀ x ∈ X₁g, x ∈ Gb.Ω (k + 1))
    {Φ : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gb Hm a₁ ν BG κ eps X₁g BG₂ δ₁))
    (hΦbd : ∀ t ∈ FlRealLC Gb Hm a₁ ν BG κ eps X₁g BG₂ δ₁,
      ‖Φ t.1 t.2.1 t.2.2‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (Zb : Finset (unitPts Gb)) :
    (∀ Y, ∀ p ∈ (XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁},
      ‖evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon S.G' Gb N) cc F₁ Sol Φ Zb p.2.1 p.2.2 Y
          (p.1.1, (BgTransport.canon S.G' Gb N).res p.1.2)‖ ≤
        Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov S.G' m₀ Y)) ∧
    (∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon S.G' Gb N) cc F₁ Sol Φ Zb p.2.1 p.2.2
            Y (p.1.1, (BgTransport.canon S.G' Gb N).res p.1.2))
        ((XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) := by
  classical
  -- the transported parameters
  set σ : (ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) →
      Dec2.DecParams (coverOf Gb) := fun w =>
    (BgTransport.canon S.G' Gb N).par (extParams S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w)
    with hσdef
  have hσan : ∀ w, AnalyticAt ℂ σ w := fun w => tauExt_analyticAt (Gl := Gb) _ w
  have hσκ : ∀ w ∈ polydisc (0 : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
      (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ := tauExt_norm_lt (Gl := Gb) _ hκ
  have hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gb).cubeIdx),
      P ∉ (coverOf Gb).parCubes X₁g → σ w ⟨P, hP⟩ = 1 :=
    tauExt_eq_one (Gl := Gb) S.hG' (X₁ := (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))) hX₁g hX₁gtop
  -- the functional of the expansion, as a function of the data, the marks and the parameters
  set F : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) →
      (ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) → ℂ := fun u s =>
    FFmarkedBg S.G' X₁f Gb a₁ ν (BgTransport.canon S.G' Gb N) cc F₁ Sol Φ Zb u.2.1 u.2.2
      (u.1.1, (BgTransport.canon S.G' Gb N).res u.1.2) s with hFdef
  -- the map to the chart of `Gb`
  set g : ((RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ)) ×
      (ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) →
      ((RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gb × Fin N → ℂ)) × (ℂ × ℂ)) ×
      (ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) := fun q =>
    (((clipRawL Gb q.1.1.1, resZ (N := N) S.G' Gb q.1.1.2), q.1.2), q.2) with hgdef
  have hgan : ∀ q, AnalyticAt ℂ g q := by
    intro q
    have h1 : AnalyticAt ℂ (fun q : ((RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ)) ×
        (ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) => clipRawL Gb q.1.1.1) q :=
      ((LinearMap.toContinuousLinearMap (clipRawL (N := N) Gb)).analyticAt _).comp
        (analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst))
    have h2 : AnalyticAt ℂ (fun q : ((RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ)) ×
        (ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) =>
        resZ (N := N) S.G' Gb q.1.1.2) q :=
      ((LinearMap.toContinuousLinearMap (resZ (N := N) S.G' Gb)).analyticAt _).comp
        (analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst))
    exact ((h1.prod h2).prod (analyticAt_snd.comp analyticAt_fst)).prod analyticAt_snd
  have hgmem : ∀ q ∈ ((XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}) ×ˢ
        polydisc (0 : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ),
      g q ∈ ((XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gb × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
          (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁}) ×ˢ
        polydisc (0 : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ) := by
    rintro q ⟨⟨⟨hΘ, hψ⟩, hW⟩, hw⟩
    refine ⟨⟨⟨?_, fun r => ?_⟩, hW⟩, hw⟩
    · show clipRaw Gb q.1.1.1 ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps
      rw [clipRaw_of_mem_rawSub Gb (XiCRaw_subset_rawSub _ _ _ _ _ _ hΘ)]
      exact hΘ
    · show ‖resZ (N := N) S.G' Gb q.1.1.2 r‖ ≤ cψ
      rw [resZ_apply]
      split_ifs
      · exact hψ _
      · rw [norm_zero]; exact hcψ
  -- (AE1): analyticity and the bound of the functional
  have hana : AnalyticOnNhd ℂ (fun q : ((RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ)) ×
      (ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) => F q.1 q.2)
      (((XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}) ×ˢ
        polydisc (0 : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ)) := by
    intro q hq
    have hcore := fanLocalHatMarked_analytic_cover (Gp := Gb) hk1 ha₁ ha₂ hS Sb HBb hκ hM hMX
      hCx heps hsmall hc7 hphi hmarD hαD hsm cc hcψ hδ₁0 hPmp hHm hF₁an hF₁ hSolan hSol hσan hσκ
      hσ1 Zb hΦ (g q) (hgmem q hq)
    refine (hcore.comp_of_eq (hgan q) rfl).congr (Filter.Eventually.of_forall fun q' => ?_)
    exact (FFmarkedBg_canon_apply X₁f Gb a₁ ν cc F₁ Sol Φ Zb q'.1.2.1 q'.1.2.2 q'.1.1 q'.2).symm
  have hbd : ∀ u ∈ (XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁},
      ∀ s ∈ polydisc (0 : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ),
      ‖F u s‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X) := fun u hu s hs =>
    fanLocalHatMarked_norm_le_cover (Gp := Gb) hk1 ha₁ ha₂ hS Sb HBb hκ hM hMX hCx heps hsmall
      hc7 hphi hmarD hαD hsm cc hcψ hδ₁0 hPmp hHm hF₁ hSol hσκ hσ1 Zb hΦbd (g (u, s))
      (hgmem (u, s) ⟨hu, hs⟩)
  -- the terms: Cauchy bound of the coefficients and the Peierls sum
  have hc : ∀ i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))), i.1.1 ∈ cubeIdx S.G' :=
    fun i => i.1.2
  have hcinj : Function.Injective
      (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) :=
    fun i i' h => Subtype.ext (Subtype.ext h)
  have hdisj : ∀ i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))),
      Disjoint (Pset m₁ i.1.1) (X1 S.G' m₀ j 𝒦X) := fun i => hX₁ ▸ i.2
  obtain ⟨hB, hA⟩ := evTerm_bound_analyticOnNhd_of_bd hcov HBb.hd HBb.hL hc hcinj hdisj hopt hκ₀
    hκdec hκκ h1 hlog hEb hana hbd
  exact ⟨fun Y p hp => hB Y p hp, fun Y => hA Y⟩

/-- **The fields of the marked terms on the chart of `Gb`** (the hypotheses `hcau`, `hJ2`, `hJ4` of
`deriv_evDecBg_hatOf_fields_gen` and `decMarkCorrBg_fields_of_gen` at `Gg = Gb` with the canonical
transport).  Under the hypotheses of `evDecBg_canon_bound_analytic`, with
`B Y = E_b e^{-κ₀ d^{cov,1}_j(X) - 2 κ_dec d̃^{cov}(Y)}`:

1. (`hcau`) the Cauchy estimate `‖∂_t evDecBg … um t Y (Θ, res ψ̂)|_{t=0}‖ ≤ B Y / t₀` for
   `0 < t₀ ≤ b`, `‖um‖ ≤ a`, `(a + b) m_R < δ₁`, on the chart of `Gb` times the box;
2. (`hJ2`) the joint analyticity in `((Θ, ψ̂), (um, tm))` on `(Ξ^c(Gb) × B̂) × W`;
3. (`hJ4`) for `|ψ̂| ≤ c_ψ`, `a ≥ 0`, `b > 0`, `(a + b) m_R < δ₁`, the derivative mark
   `(θ, u) ↦ ∂_t evDecBg … u t Y (θ.1, res ψ̂)|_{t=0}` is analytic on `physVBg Gb × {‖u‖ < a}`. -/
theorem evDecBg_canon_fields (hk1 : 1 ≤ k) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L a₁) ν Kc Cx)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁) (hPmp : Precedes Hm Gb) (hHm : Hm.Ω (k + 1) = ∅)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gb) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    -- the step's expansion of the old polymer
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {m₀ j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb)
    -- the frozen region of `Gb` and the functional
    {X₁g : Finset (CTorus d L N₁ m₁ (k + 1))} (hX₁g : ∀ x ∈ X₁g, x ∈ X₁f)
    (hX₁gtop : ∀ x ∈ X₁g, x ∈ Gb.Ω (k + 1))
    {Φ : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gb Hm a₁ ν BG κ eps X₁g BG₂ δ₁))
    (hΦbd : ∀ t ∈ FlRealLC Gb Hm a₁ ν BG κ eps X₁g BG₂ δ₁,
      ‖Φ t.1 t.2.1 t.2.2‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (Zb : Finset (unitPts Gb)) :
    (∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Y, ∀ u ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖deriv (fun t : ℂ => evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon S.G' Gb N) cc F₁
          Sol Φ Zb um t Y (u.1, (BgTransport.canon S.G' Gb N).res u.2)) 0‖ ≤
        Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov S.G' m₀ Y) / t₀) ∧
    (∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon S.G' Gb N) cc F₁ Sol Φ Zb p.2.1 p.2.2
            Y (p.1.1, (BgTransport.canon S.G' Gb N).res p.1.2))
        ((XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) ∧
    (∀ Y, ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ cψ) →
        ∀ a b : ℝ, 0 ≤ a → 0 < b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParamBg N Gb × ℂ => deriv (fun t : ℂ =>
          evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon S.G' Gb N) cc F₁ Sol Φ Zb p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N),
              (BgTransport.canon S.G' Gb N).res ψh)) 0)
          (physVBg N Gb a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) := by
  obtain ⟨hB, hA⟩ := evDecBg_canon_bound_analytic S hk1 ha₁ ha₂ hS Sb HBb hκ hM hMX hCx heps hsmall
    hc7 hphi hmarD hαD hsm cc hcψ hδ₁0 hPmp hHm hF₁an hF₁ hSolan hSol hcov hX₁ hopt hκ₀ hκdec hκκ
    h1 hlog hEb hX₁g hX₁gtop hΦ hΦbd Zb
  have hbd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um tm : ℂ, ‖um‖ ≤ a → ‖tm‖ ≤ b →
      ∀ Y, ∀ u ∈ XiCRaw Gb (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ},
      ‖evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon S.G' Gb N) cc F₁ Sol Φ Zb um tm Y
          (u.1, (BgTransport.canon S.G' Gb N).res u.2)‖ ≤
        Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov S.G' m₀ Y) :=
    fun a b ha hb hab um tm hum htm Y u hu =>
      hB Y (u, (um, tm)) ⟨hu, mem_markedRadiusSet_of_pos hδ₁0 hab hum htm⟩
  refine ⟨fun a b t₀ ha hb ht htb hab um hum Y u hu => ?_, hA, fun Y ψh hψh a b ha hb hab => ?_⟩
  · exact norm_deriv_mark_le_of_joint (Ev := fun um tm
      (v : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) =>
      evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon S.G' Gb N) cc F₁ Sol Φ Zb um tm Y
        (v.1, (BgTransport.canon S.G' Gb N).res v.2)) hδ₁0 (hA Y) (hB Y) ht htb hab hum hu
  · exact (markedEv_physVBg_of_joint (Gg := Gb) (Ev := fun Y um tm
      (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) =>
      evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon S.G' Gb N) cc F₁ Sol Φ Zb um tm Y
        (u.1, (BgTransport.canon S.G' Gb N).res u.2)) HBb hδ₁0 hA hbd).2.1 Y ψh hψh a b ha hb hab

end Terms

end Balaban.Localization
