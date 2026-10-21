/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.E0CoeffFamilyRotMark
public import Balaban.Fluctuation.NewLevelTermsBgAnalytic
public import Balaban.Fluctuation.NewLevelTermsBgLocal
public import Balaban.Fluctuation.LocalClassRot

/-!
# Spin covariance of the terms of the new level recomputed on a background generating set

P3 pp. 78-79 (route R-LOC, the form of (A4)): the terms `evDecBg` of the step's expansion recomputed
on a background generating set `Gb` with the canonical transport are invariant under the
simultaneous real rotation of the datum and of the hat variable, when the functional expanded is
invariant on the realizable triples of `Gb`.

* `liftZ_rotFld`, `resZ_rotFld`: the extension by zero and the restriction of hat variables commute
  with the spin rotation;
* `evDecBg_canon_rot`: the covariance of the terms (`evTerm_congr_polydisc`; the datum read by the
  canonical transport is the rotated datum, the marked local hat field of the rotated data is the
  rotated field, `markedHatPsiFBg_rot`, and the fan composite is invariant, `fanLC_rot_cover`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix

section Lift

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱb : ℝ}

/-- The extension by zero commutes with the spin rotation. -/
theorem liftZ_rotFld (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb)
    (R : Matrix (Fin N) (Fin N) ℂ) (w : unitPts Gb × Fin N → ℂ) :
    liftZ Gb (rotFld R w) = DecEquiv.rotSite R (liftZ Gb w) := by
  funext x i
  by_cases h : unitBlock x ∈ unitPts Gb
  · simp [liftZ_apply, h, rotFld, DecEquiv.rotSite, Matrix.mulVec, dotProduct]
  · simp [liftZ_apply, h, DecEquiv.rotSite, Matrix.mulVec, dotProduct]

/-- The restriction of hat variables commutes with the spin rotation. -/
theorem resZ_rotFld (Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) (R : Matrix (Fin N) (Fin N) ℂ)
    (ψh : unitPts Gp × Fin N → ℂ) :
    resZ (N := N) Gp Gb (rotFld R ψh) = rotFld R (resZ Gp Gb ψh) := by
  funext p
  rw [resZ_apply]
  by_cases h : p.1.1 ∈ unitPts Gp
  · simp only [h, ↓reduceDIte, rotFld]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [resZ_apply]
    simp [h]
  · simp only [h, ↓reduceDIte, rotFld]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [resZ_apply]
    simp [h]

end Lift

section Rot

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱb ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a₁ ν Kc Cx : ℝ}

open Classical in
/-- **The terms recomputed on `Gb` with the canonical transport are spin invariant** (P3 pp. 78-79;
the form of (A4)).  Let `Gb` carry a cover base for the decoupled background and the fluctuation
core with `H⁻`, `(F₁, Sol)` a decoupling pair of `(Gb, H⁻)` with its defining properties, and let the
frozen region `X₁` of the step's expansion lie in the top layer of `Gb`.  If the functional `Φ` is
invariant under `(R φ, α; R δφ; R u)` on the realizable triples `FlRealLC Gb H⁻ … X₁ …` whose
rotation is again realizable, then for a datum `D` of the chart of `Gb`, a hat variable `ψ̂` of the
step with `|ψ̂| ≤ c_ψ` and marks of the radius set,
`evDecBg … Y (R Θ, res (R ψ̂)) = evDecBg … Y (Θ, res ψ̂)` with `Θ = rawOf D`. -/
theorem evDecBg_canon_rot {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L a₁) ν Kc Cx)
    {κ eps c₂ BG₂ δ₁ Kf Cf : ℝ} (hC : FlCore N Gb Hm a₁ ν c BG κ eps Kf Cf c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hHm : Hm.Ω (k + 1) = ∅) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
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
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {m₀ j : ℕ} {𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hX₁top : ∀ x ∈ X₁f, x ∈ Gb.Ω (k + 1))
    {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    {Φ : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) δφ u,
      (bg, δφ, u) ∈ FlRealLC Gb Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      ((rotFld (cmat Q) bg.1, bg.2), rotFld (cmat Q) δφ, rotU (cmat Q) u) ∈
        FlRealLC Gb Hm a₁ ν BG κ eps X₁f BG₂ δ₁ →
      Φ (rotFld (cmat Q) bg.1, bg.2) (rotFld (cmat Q) δφ) (rotU (cmat Q) u) = Φ bg δφ u)
    (Zb : Finset (unitPts Gb)) {um tm : ℂ}
    (hW : (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) {D : BgData Gb N}
    (hD : XiCData Gb (compWeight L a₁) ν (k + 1) 1 eps D) {ψh : unitPts S.G' × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon S.G' Gb N) cc F₁ Sol Φ Zb um tm Y
        (rotRaw (cmat Q) (rawOf D), (BgTransport.canon S.G' Gb N).res (rotFld (cmat Q) ψh)) =
      evDecBg S.G' X₁f m₀ j 𝒦X Gb a₁ ν (BgTransport.canon S.G' Gb N) cc F₁ Sol Φ Zb um tm Y
        (rawOf D, (BgTransport.canon S.G' Gb N).res ψh) := by
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  refine evTerm_congr_polydisc _ hE1 _ Y fun w hw => ?_
  -- the transported parameters
  have hσκ : ∀ P, ‖(BgTransport.canon S.G' Gb N).par
      (extParams S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) P‖ < Real.exp κ :=
    tauExt_norm_lt (Gp := S.G') (Gl := Gb) _ hC.hκ w hw
  have hσ1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gb).cubeIdx),
      P ∉ (coverOf Gb).parCubes X₁f → (BgTransport.canon S.G' Gb N).par
        (extParams S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) ⟨P, hP⟩ = 1 :=
    tauExt_eq_one (Gp := S.G') (Gl := Gb) S.hG' (fun x hx => hx) hX₁top w
  -- the datum and the hat variable read by the canonical transport
  have hΘ : clipRawL Gb (rawOf D) = rawOf D :=
    clipRaw_of_mem_rawSub Gb (rawOf_mem_rawSub D)
  have hΘr : clipRawL Gb (rotRaw (cmat Q) (rawOf D)) = rotRaw (cmat Q) (rawOf D) := by
    show clipRaw Gb (rotField (cmat Q) (rawOf D).1, rotField (cmat Q) (rawOf D).2) = _
    rw [clipRaw_rot]
    exact congrArg (rotRaw (cmat Q)) hΘ
  have hres : resZ (N := N) S.G' Gb (rotFld (cmat Q) ψh) = rotFld (cmat Q) (resZ S.G' Gb ψh) :=
    resZ_rotFld S.G' Gb (cmat Q) ψh
  have hψb : ∀ p, ‖resZ (N := N) S.G' Gb ψh p‖ ≤ cψ := fun p => by
    rw [resZ_apply]
    split_ifs
    · exact hψh _
    · rw [norm_zero]; exact hcψ
  have hrot := markedHatPsiFBg_rot hC hk (liftZ Gb) (liftZ_rotFld Gb) cc hMX hmar hα hsm hF₁ hσκ hD
    hQ Zb um tm (resZ S.G' Gb ψh)
  have hball := markedHatPsiFBg_liftZ_mem_flBallLC_core hC hk hHm cc hcψ hMX hmar hα hsm hF₁ hσκ hD
    hψb Zb hW
  have hF₁' : ∀ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α) := fun s D hs hDd φ α hI =>
    hF₁ s D hs hDd φ α ((dec2_isDecBg_iff Gb _ _ _ s D φ α).1 hI)
  have hfan := fanLC_rot_cover hS Sb hC.HBp hC.hκ hC.hM hC.eps_pos hC.small1 hC.c7le hC.phi_lt
    hC.δ₁_pos hC.hPmp hF₁' hSol hQ hΦ hσκ hσ1 hD hball
  rw [FFmarkedBg_canon_apply X₁f Gb a₁ ν cc F₁ Sol Φ Zb um tm
      (rotRaw (cmat Q) (rawOf D), rotFld (cmat Q) ψh) w,
    FFmarkedBg_canon_apply X₁f Gb a₁ ν cc F₁ Sol Φ Zb um tm (rawOf D, ψh) w]
  simp only
  rw [hres, hΘr, hΘ, hrot]
  exact hfan

end Rot

end Balaban.Inhabited
