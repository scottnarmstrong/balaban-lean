/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelTermsBgRot
public import Balaban.Fluctuation.NewLevelOldTermsBgSetting

/-!
# Spin covariance of the terms of the old terms recomputed on a background generating set

P3 pp. 78-79 (route R-LOC, the form of (A4)) for the old labels: the terms `evDecBg` of an old term
recomputed on a background generating set `Gb` with the canonical transport, with its functional
`eTermFun Gb …`, are invariant under the simultaneous real rotation of the datum and of the hat
variable, for every label with the margin in `Gb`, when the old term `E` is invariant on its chart.

When the frozen region `X₁` of the old term lies in the label, it lies in the top layer of `Gb`, the
old term has the step's settings on `Gb` (`bgSetting_of_top`, `flSetting_of_top`), its functional
is invariant on the realizable triples of `Gb` (`eTermFun_rot_cover`) and the terms are covariant
(`evDecBg_canon_rot`); otherwise the terms vanish (`evDecBg_eq_zero_of_not_subset`).

* `evDecBg_canon_rot_eTerm`: the hypothesis `holdrot` of `NewLevelSystem.coeffLoc_rot_of`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Finset Matrix

section Rot

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱb ϱm ϱs ϱ₁ ϱ₂ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hs : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱs}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
  {a₁ ν Kc Cx : ℝ}

open Classical in
/-- **Spin covariance of the terms of an old term recomputed on `Gb`** (P3 pp. 78-79; the form of
(A4) for the old labels).  Let `(Gb, H⁻)` carry a cover base, the fluctuation core with the old
term's constants, `Gb` cube aligned and sup-separated, and let the old term have the step's settings
`BgSetting N S.G' Gk Gj`, `FlSetting N S.G' Gk H_s` (`H_s` of level `k`, any constants of its
cover), its functional `eTermFun Gb Gk Gj H⁻ … Fk E` recomputed on `Gb`, and `E` invariant under
the real rotation `Q` on its chart.  For every label `Y` with the margin in `Gb`, a datum `D` of
the chart of `Gb` and a hat variable with `|ψ̂| ≤ c_ψ`, the term at the rotated datum and hat
variable equals the term at `D`, `ψ̂`. -/
theorem evDecBg_canon_rot_eTerm {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L a₁) ν Kc Cx)
    {κ eps c₂ BG₂ δ₁ : ℝ} (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hHm : Hm.Ω (k + 1) = ∅) (hdk : Hm.Ω k = Gb.Ω k)
    (hA : CubeAligned Gb m₁) (hSS : SupSep Gb m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    {F₁ : DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gb) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ), IsDecBg Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
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
    {cB r₀ δ₃ δfl Kf Cf c₂f : ℝ} {X₀ : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hB : BgSetting N S.G' Gk Gj a₁ ν cB BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N S.G' Gk Hs a₁ ν κ BG eps δ₃ Kf Cf c₂f BG₂ δ₁ δfl X₁f) (hGs : IsLevel Hs k)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν) (hrb : r₀ * (L : ℝ) ^ m₁ ≤ ϱb - 1)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ} {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (hEr : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), E (rotRaw (cmat Q) r) = E r)
    (Zb : Finset (unitPts Gb)) {um tm : ℂ}
    (hW : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hYm : LabelMargin Gb Y) {D : BgData Gb N}
    (hD : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D) {ψh : unitPts S.G' × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon S.G' Gb N) cc F₁ Sol
        (eTermFun Gb Gk Gj Hm (compWeight L a₁) Fk E) Zb um tm Y
        (rotRaw (cmat Q) (rawOf D), (BgTransport.canon S.G' Gb N).res (rotFld (cmat Q) ψh)) =
      evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon S.G' Gb N) cc F₁ Sol
        (eTermFun Gb Gk Gj Hm (compWeight L a₁) Fk E) Zb um tm Y
        (rawOf D, (BgTransport.canon S.G' Gb N).res ψh) := by
  by_cases hsub : ∀ x ∈ X₁f, x ∈ Y
  · -- the frozen region lies in the top layer of `Gb`: the old term has its settings on `Gb`
    have htop : ∀ x ∈ X₁f, x ∈ Gb.Ω (k + 1) := fun x hx => hYm.subset x (hsub x hx)
    have hdsTop : ∀ x ∈ dataSites Gk, x ∈ Gb.Ω (k + 1) := fun x hx =>
      htop x (hB.dep x hx x (self_mem_composeDep x))
    have hB' := bgSetting_of_top hB S.hG' hC.Sp HBb hrb hdsTop
    have hF' := flSetting_of_top_gen hF hGs hk hC hdk hHm hdsTop
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱb - 1 := by
      have h0 : 0 ≤ 4 * d * (L : ℝ) ^ 3 := by positivity
      have h1 : 0 ≤ (L : ℝ) ^ m₁ := by positivity
      have hr0 : 0 ≤ r₀ - 4 * d * (L : ℝ) ^ 3 := by linarith [hB.hr₀]
      calc (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L
          ≤ (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ :=
            div_le_self (mul_nonneg hr0 h1) hL1
        _ ≤ r₀ * (L : ℝ) ^ m₁ := mul_le_mul_of_nonneg_right (by linarith) h1
        _ ≤ ϱb - 1 := hrb
    exact evDecBg_canon_rot S hS Sb hC hk hHm cc hcψ hMX hmar hα hsm hF₁ hSol htop hQ
      (fun bg δφ u ht ht' => eTermFun_rot_cover (t := (bg, δφ, u)) hb₁ hbC hS Sb hA hSS hMM
        hB'.ha₁ hB'.HBp hB'.HBk hB'.HBj hB'.hP hB'.hq hB'.colk hB'.colj hB'.hκ hC.hM hB'.num
        hB'.dsX₀ hB'.hN hT hB'.hr₀ hB'.hj hF' hFk hQ hEr ht ht') Zb hW Y hD hψh
  · rw [evDecBg_eq_zero_of_not_subset _ hX₁ hsub, evDecBg_eq_zero_of_not_subset _ hX₁ hsub]

end Rot

end Balaban.Inhabited
