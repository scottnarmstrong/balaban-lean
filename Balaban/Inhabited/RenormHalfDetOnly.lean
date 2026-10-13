/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RenormRadiusInput
public import Balaban.Inhabited.RenormRadiusDec
public import Balaban.Inhabited.RenormE0FibreDetRadius
public import Balaban.Inhabited.RenFibreDatum
public import Balaban.Fluctuation.RenormExpInputOn
public import Balaban.Inhabited.RenormRadiusLoc
public import Balaban.Inhabited.RenormE0FibreDetG
public import Balaban.Inhabited.StepTowerRadius
public import Balaban.Inhabited.StepTowerCoreMono
public import Balaban.Inhabited.RenormLocC2ZeroTower
public import Balaban.Inhabited.LevelStepSettingGeneral

/-!
# The determinant-only renormalization record at class radius `t / 2` on the fibre

For `R : StepTowerTheta κmin` with `renDetFibreMin ≤ κmin` and `e = R.t / 2`, on the fibre
`Dom D := XiCOneReal G a ν e D ∧ (the field of D is the step's constant h₀)`:

* `renormDetOnlyZeroM_onFibre_half`: one solution map `F` of `IsRenSol … e e r₀ (8 e)`, its cut map
  with the endpoint identity, the record `RenormExpInputOn` whose energy function is the
  determinant summand `renE0θ_det e E` and whose observable and old terms are zero, the localized
  expansion of the determinant summand, its value at `ξ = 0`, a datum of the fibre, and the
  inclusion of the renormalized datum in the step chart of radius `t`;
* `renormDetOnlyZeroM_onFibre_half_C12`: Theorem 3.1 (g) `C₁`, `C₂` on the fibre for the same `F`.

**This is a determinant-only record with zero observable and zero old terms.  It is NOT the
physical record of Theorem 3.1 (g), (h): the marked energy and the observable are absent.**
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

/-- **Core of the determinant-only record, for any generating set.**  Given the three localization
principles on the full domain `XiCOneReal G a ν ε`, the expansion of the energy function `E0θ` on
the full domain, and a sub-domain `Dom ⊆ XiCOneReal G a ν ε`, the energy expansion holds on `Dom`
and `RenormExpInputOn` holds on `Dom` with zero old terms and zero observable. -/
theorem renormDetOnlyZero_expInput_core {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν ε r₀ cK B : ℝ}
    {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    {ι : Type*} {blk : ι → Finset (Torus d (N₀ * L ^ k))}
    {Ys : ι → Finset (Finset (Torus d (N₀ * L ^ k)))}
    {YsM : G.Ω 1 × Fin N → Finset (Finset (Torus d (N₀ * L ^ k)))}
    {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ} {κa κb Kloc BE0 : ℝ}
    {E0θ : ι → BgData G N → (Fin 3 → ℂ) → ℂ} {Dom : BgData G N → Prop}
    (sub : ∀ D : BgData G N, Dom D → XiCOneReal G a ν ε D)
    (locC1 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Kloc
      (fun D _ => bgClass G ν (cK * ε) D) (fun D φ ξ => renC1On G a ν ε (blk z) D.Ψ D.h φ ξ)
      (fun D _ => bgFieldC G a ν (bgC0 d L N) D))
    (locC2 : ∀ z, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa Kloc
      (fun _ ξ => pertClass G (cK * (cK2 d L N * (B * ‖ξ‖)))
        (bgK1 d L N * (xiC1 d * ε) + cK * cK2 d L N * B * r₀ + 2) (renMassU ν ξ))
      (fun _ v ξ => renC2On G a (blk z) ξ (renMassU ν ξ) v.2 v.1)
      (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1, bgMultC G a ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2)))
    (hE : ∀ z, ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) r₀ (Ys z) dY κa BE0 (E0θ z) term)
    (locDφ : ∀ p, HasLocPrinciple (N := N) G (XiCOneReal G a ν ε) r₀ (YsM p) dY κb Kloc
      (fun _ ξ => {v | SupBounds G v (cK * (cK2 d L N * (B * ‖ξ‖)))}) (fun _ v _ => v p)
      (fun D ξ => (F ((D.Ψ, D.h), ξ)).1)) :
    RenormExpInputOn G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 0 0 0 E0θ
        (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) Dom ∧
      ∀ z, ∃ term, IsLocExp (N := N) G Dom r₀ (Ys z) dY κa BE0 (E0θ z) term := by
  have hE' := fun z => (hE z).imp fun _ h => h.mono_dom sub
  exact ⟨renormExpInputOn_zero_of_fields sub locC1 locC2 hE' locDφ
    (fun _ => ⟨_, isLocExp_zero_cover _ _⟩), hE'⟩

/-- Core of `renormDetOnlyZeroM_onFibre_half` over a free separation parameter `ϱ = rhoSepG d L m₁`. -/
private theorem StepTowerThetaG.renormDetOnlyZeroM_onFibre_half_core {d L N : ℕ} [NeZero L] {κmin : ℝ} (R : StepTowerThetaG d L N κmin) {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L R.m₁)
    (hhull : 2 * d * L * (1 + collarB d L) *
        (renDetA d L 1 * (3 / 2 * R.κdec + c1 d L * Real.log 2) + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ R.κ) (hm₀ : R.m₀ = 1) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (Xcut : Set (CTorus d L N₁ R.m₁ (k + 1))) :
    ∃ E : ∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)) 1 z (2 * R.t)
          ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))),
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (ϱ)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (ϱ)).Ω 1 → ℂ),
    ∃ Fcut : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        (RenLabel (lvTopG d L N₁ R.m₁ k (ϱ)) Xcut → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (ϱ)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (ϱ)).Ω 1 → ℂ),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (ϱ)) (compWeight L 1) ν (R.t / 2) (R.t / 2)
        R.r₀ (8 * (R.t / 2)) F ∧
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ)) ×
          (RenLabel (lvTopG d L N₁ R.m₁ k (ϱ)) Xcut → ℂ) => Fcut p.1 p.2)
        (expDom (lvTopG d L N₁ R.m₁ k (ϱ))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (ϱ)) (compWeight L 1) ν (R.t / 2)) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (ϱ)) Xcut → ℂ)
            (fun _ => Real.exp R.κ)) ∧
      (∀ D : BgData (lvTopG d L N₁ R.m₁ k (ϱ)) N,
        XiCOneReal (lvTopG d L N₁ R.m₁ k (ϱ)) (compWeight L 1) ν (R.t / 2) D →
        ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ)) ∧
      RenormExpInputOn (N := N) (lvTopG d L N₁ R.m₁ k (ϱ)) (compWeight L 1) ν (R.t / 2)
        R.r₀ (renCK d L N R.BG R.κ) (8 * (R.t / 2)) F
        (fun z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))) =>
          blockSites d L N₁ R.m₁ (k + 1) k z)
        (fun z => renYs (renCube (lvTopG d L N₁ R.m₁ k (ϱ))
            (X1 (lvTopG d L N₁ R.m₁ k (ϱ)) 1 k (fam 1 (blockSite k z))))
          (lvTopG d L N₁ R.m₁ k (ϱ)) 1
          (X1 (lvTopG d L N₁ R.m₁ k (ϱ)) 1 k (fam 1 (blockSite k z))))
        (fun p => renYs (renCube (lvTopG d L N₁ R.m₁ k (ϱ))
            (X1 (lvTopG d L N₁ R.m₁ k (ϱ)) 1 k
              (fam 1 (p.1 : CTorus d L N₁ R.m₁ (k + 1)))))
          (lvTopG d L N₁ R.m₁ k (ϱ)) 1
          (X1 (lvTopG d L N₁ R.m₁ k (ϱ)) 1 k
            (fam 1 (p.1 : CTorus d L N₁ R.m₁ (k + 1)))))
        (renDY (lvTopG d L N₁ R.m₁ k (ϱ)) 1) (3 / 2 * R.κdec) (3 / 2 * R.κdec) 1
        (hullConst d L ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))) *
            Real.exp (c1 d L * Real.log 2) * Real.exp (hullRate d L ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))))
        0 0 0 (renE0θ_det (R.t / 2) E) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun D => XiCOneReal ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).G'
            ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).a ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).h₀ i : ℝ) : ℂ)) ∧
      (∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))), ∃ term,
        IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (ϱ))
          (fun D => XiCOneReal ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).G'
              ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).a ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).ν
              (R.t / 2) D ∧
            ∀ x i, D.h x i = ((((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).h₀ i : ℝ) : ℂ)) R.r₀
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (ϱ))
              (X1 (lvTopG d L N₁ R.m₁ k (ϱ)) 1 k (fam 1 (blockSite k z))))
            (lvTopG d L N₁ R.m₁ k (ϱ)) 1
            (X1 (lvTopG d L N₁ R.m₁ k (ϱ)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTopG d L N₁ R.m₁ k (ϱ)) 1) (3 / 2 * R.κdec)
          (hullConst d L ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))) *
            Real.exp (c1 d L * Real.log 2) * Real.exp (hullRate d L ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))))
          (renE0θ_det (R.t / 2) E z) term) ∧
      (∀ z, renE0θ_det (R.t / 2) E z ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).D' 0 =
        -(1 / 2 : ℂ) * ∑ y ∈ ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).blockU z, ∑ i : Fin N,
          ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).logAC (y, i) (y, i)) ∧
      (XiCOneReal ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).G'
          ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).a ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).ν
          (R.t / 2) ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).D' ∧
        ∀ x i, ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).D'.h x i =
          ((((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).h₀ i : ℝ) : ℂ)) ∧
      (∀ D : BgData ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).G' N,
        (XiCOneReal ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).G'
            ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).a ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = ((((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).h₀ i : ℝ) : ℂ)) →
        ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ →
          XiCData ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).G'
            ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).a ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).ν
            (k + 1) 1 R.t (renThetaDatum ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)) (R.t / 2) D ξ)) := by
  subst hϱ
  have ht := R.t_pos
  have he : 0 < R.t / 2 := by positivity
  have het : R.t / 2 ≤ R.t := by linarith
  have hκ : 0 ≤ R.κdec := by have := R.κdec_lower; have := R.κ0_nonneg; linarith
  have hκa : 3 / 2 * R.κdec ≤ 2 * R.κdec := by linarith
  have hN₀ : L ^ R.m₀ ∣ N₁ := by rw [hm₀]; simpa using hLN
  obtain ⟨F, hF, h1, h2, h3⟩ :=
    renLoc_fields_scale_of_towerG_at R.toStepTowerRenSolG k hk N₁ hN₀ hN hν0 hν he het hκa hκa
  rw [hm₀] at h1 h2 h3
  obtain ⟨Fcut, hFa, hFe⟩ := renDec_one_unique_sharp_scale_of_towerG_at R.toStepTowerRenEndG k hk
    N₁ hN hν0 hν he het Xcut hF le_rfl
  obtain ⟨E, hE0, hE⟩ := R.expE0_det_scale_of_tower_at hhull he het k hk N₁ hLN hN hν0 hν β p₁
  have hI := renormDetOnlyZero_expInput_core
    (Dom := fun D => XiCOneReal (R.step k hk N₁ ν β p₁).G'
          (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν
          (R.t / 2) D ∧
        ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ))
    (fun D hD => hD.1) h1 h2 (fun z => (hE z).imp fun _ h => h) h3
  exact ⟨E, F, Fcut, hF, hFa, hFe, hI.1, hI.2, hE0,
    R.toStepTowerG.exists_xiCOneReal_fibre_step k hk N₁ ν β p₁ hν0 hν he,
    fun D hD ξ hξ => R.renDatum_half_mem_xiCData k hk N₁ hν0 hν β p₁ D hD.1 ξ hξ⟩

/-- **Determinant-only record with zero observable and zero old terms, at class radius `t / 2`, on
the fibre.**  This is NOT the physical record of Theorem 3.1 (g), (h): the energy function of the
record is only the determinant summand `renE0θ_det`, the observable function and both old-term
differences are zero, and the marked energy and the observable are absent.  What is proved: one
solution map `F` with `IsRenSol`, a cut map `Fcut` whose value at `s = 1` is this `F`, the record
`RenormExpInputOn` on the fibre domain, the localized expansion of the determinant summand, its
value at `ξ = 0` at the step datum, that the step datum lies in the fibre, and that the
renormalized datum lies in the step chart of radius `t`. -/
theorem StepTowerThetaG.renormDetOnlyZeroM_onFibre_half {d L N : ℕ} [NeZero L] {κmin : ℝ} (R : StepTowerThetaG d L N κmin)
    (hhull : 2 * d * L * (1 + collarB d L) *
        (renDetA d L 1 * (3 / 2 * R.κdec + c1 d L * Real.log 2) + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ R.κ) (hm₀ : R.m₀ = 1) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (Xcut : Set (CTorus d L N₁ R.m₁ (k + 1))) :
    ∃ E : ∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))),
        DetExpansionLocC (R.step k hk N₁ ν β p₁) 1 z (2 * R.t)
          ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))),
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
    ∃ Fcut : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) Xcut → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (R.t / 2) (R.t / 2)
        R.r₀ (8 * (R.t / 2)) F ∧
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ)) ×
          (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) Xcut → ℂ) => Fcut p.1 p.2)
        (expDom (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (R.t / 2)) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) Xcut → ℂ)
            (fun _ => Real.exp R.κ)) ∧
      (∀ D : BgData (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N,
        XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (R.t / 2) D →
        ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ)) ∧
      RenormExpInputOn (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (R.t / 2)
        R.r₀ (renCK d L N R.BG R.κ) (8 * (R.t / 2)) F
        (fun z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))) =>
          blockSites d L N₁ R.m₁ (k + 1) k z)
        (fun z => renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1 k (fam 1 (blockSite k z))))
          (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1 k (fam 1 (blockSite k z))))
        (fun p => renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1 k
              (fam 1 (p.1 : CTorus d L N₁ R.m₁ (k + 1)))))
          (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1
          (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1 k
            (fam 1 (p.1 : CTorus d L N₁ R.m₁ (k + 1)))))
        (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1) (3 / 2 * R.κdec) (3 / 2 * R.κdec) 1
        (hullConst d L ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))) *
            Real.exp (c1 d L * Real.log 2) * Real.exp (hullRate d L ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))))
        0 0 0 (renE0θ_det (R.t / 2) E) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun D => XiCOneReal (R.step k hk N₁ ν β p₁).G'
            (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) ∧
      (∀ z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1))), ∃ term,
        IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (fun D => XiCOneReal (R.step k hk N₁ ν β p₁).G'
              (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν
              (R.t / 2) D ∧
            ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) R.r₀
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1) (3 / 2 * R.κdec)
          (hullConst d L ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLogMax d L R.κ / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ)))) *
            Real.exp (c1 d L * Real.log 2) * Real.exp (hullRate d L ((R.κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))))
          (renE0θ_det (R.t / 2) E z) term) ∧
      (∀ z, renE0θ_det (R.t / 2) E z (R.step k hk N₁ ν β p₁).D' 0 =
        -(1 / 2 : ℂ) * ∑ y ∈ (R.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin N,
          (R.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      (XiCOneReal (R.step k hk N₁ ν β p₁).G'
          (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν
          (R.t / 2) (R.step k hk N₁ ν β p₁).D' ∧
        ∀ x i, (R.step k hk N₁ ν β p₁).D'.h x i =
          (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) ∧
      (∀ D : BgData (R.step k hk N₁ ν β p₁).G' N,
        (XiCOneReal (R.step k hk N₁ ν β p₁).G'
            (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) →
        ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ →
          XiCData (R.step k hk N₁ ν β p₁).G'
            (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν
            (k + 1) 1 R.t (renThetaDatum (R.step k hk N₁ ν β p₁) (R.t / 2) D ξ)) := by
  exact R.renormDetOnlyZeroM_onFibre_half_core rfl hhull hm₀ k hk N₁ hLN hN hν0 hν β p₁ Xcut
/-- Core of `renormDetOnlyZeroM_onFibre_half_C12` over a free separation parameter `ϱ = rhoSepG d L m₁`. -/
private theorem StepTowerThetaG.renormDetOnlyZeroM_onFibre_half_C12_core {d L N : ℕ} [NeZero L] {κmin : ℝ} (R : StepTowerThetaG d L N κmin) {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L R.m₁)
    (hhull : 2 * d * L * (1 + collarB d L) *
        (renDetA d L 1 * (3 / 2 * R.κdec + c1 d L * Real.log 2) + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ R.κ) (hm₀ : R.m₀ = 1) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (Xcut : Set (CTorus d L N₁ R.m₁ (k + 1))) :
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (ϱ)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (ϱ)).Ω 1 → ℂ),
    ∃ Fcut : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        (RenLabel (lvTopG d L N₁ R.m₁ k (ϱ)) Xcut → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (ϱ)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (ϱ)).Ω 1 → ℂ),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (ϱ)) (compWeight L 1) ν (R.t / 2) (R.t / 2)
        R.r₀ (8 * (R.t / 2)) F ∧
      (∀ D : BgData (lvTopG d L N₁ R.m₁ k (ϱ)) N,
        XiCOneReal (lvTopG d L N₁ R.m₁ k (ϱ)) (compWeight L 1) ν (R.t / 2) D →
        ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ)) ∧
      ∀ (z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1)))) (εR : ℝ), 0 ≤ εR → εR ≤ R.r₀ →
        (∃ term, IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (ϱ))
          (fun D => XiCOneReal ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).G'
              ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).a ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).ν
              (R.t / 2) D ∧
            ∀ x i, D.h x i = ((((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).h₀ i : ℝ) : ℂ)) εR
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (ϱ))
              (X1 (lvTopG d L N₁ R.m₁ k (ϱ)) 1 k (fam 1 (blockSite k z))))
            (lvTopG d L N₁ R.m₁ k (ϱ)) 1
            (X1 (lvTopG d L N₁ R.m₁ k (ϱ)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTopG d L N₁ R.m₁ k (ϱ)) 1) (3 / 2 * R.κdec)
          (1 * ((d + 6) * (renCK d L N R.BG R.κ * (R.t / 2)) ^ 2 *
            blockWeight (lvTopG d L N₁ R.m₁ k (ϱ))
              (blockSites d L N₁ R.m₁ (k + 1) k z)) * εR ^ 1)
          (fun D ξ => renC1On (lvTopG d L N₁ R.m₁ k (ϱ)) (compWeight L 1) ν (R.t / 2)
            (blockSites d L N₁ R.m₁ (k + 1) k z) D.Ψ D.h
            (bgFieldC (lvTopG d L N₁ R.m₁ k (ϱ)) (compWeight L 1) ν (bgC0 d L N) D) ξ)
          term) ∧
        (∃ term, IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (ϱ))
          (fun D => XiCOneReal ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).G'
              ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).a ((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).ν
              (R.t / 2) D ∧
            ∀ x i, D.h x i = ((((hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) R.hN k R.m₁ ϱ hk ν β p₁ R.δ)).h₀ i : ℝ) : ℂ)) εR
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (ϱ))
              (X1 (lvTopG d L N₁ R.m₁ k (ϱ)) 1 k (fam 1 (blockSite k z))))
            (lvTopG d L N₁ R.m₁ k (ϱ)) 1
            (X1 (lvTopG d L N₁ R.m₁ k (ϱ)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTopG d L N₁ R.m₁ k (ϱ)) 1) (3 / 2 * R.κdec)
          (1 * (17 / 32 * ((N : ℕ) * ((3 + (bgK1 d L N * (xiC1 d * (R.t / 2)) +
            renCK d L N R.BG R.κ * cK2 d L N * (8 * (R.t / 2)) * R.r₀ + 2)) *
            (renCK d L N R.BG R.κ * cK2 d L N * (8 * (R.t / 2))) ^ 2)) *
            blockWeight (lvTopG d L N₁ R.m₁ k (ϱ))
              (blockSites d L N₁ R.m₁ (k + 1) k z)) * εR ^ 2)
          (fun D ξ => renC2On (lvTopG d L N₁ R.m₁ k (ϱ)) (compWeight L 1)
            (blockSites d L N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
            (bgMultC (lvTopG d L N₁ R.m₁ k (ϱ)) (compWeight L 1) ν (bgC0 d L N) D +
              (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term) := by
  subst hϱ
  obtain ⟨E, F, Fcut, hF, hFa, hFe, I, -⟩ :=
    R.renormDetOnlyZeroM_onFibre_half hhull hm₀ k hk N₁ hLN hN hν0 hν β p₁ Xcut
  have ht := R.t_pos
  have he : 0 < R.t / 2 := by positivity
  have het : R.t / 2 ≤ R.t := by linarith
  have hC := R.toStepTowerG.flCore_scale_mono k hk N₁ hN hν0 hν he het he het
  have hHB := bgHyp_lvG (k := k) R.hd R.hL (bgR0_le_rhoSepG R.m₁ R.hd R.hL) hν0 hν
  refine ⟨F, Fcut, hF, hFe, fun z εR hεR0 hεR => ⟨?_, ?_⟩⟩
  · exact thm31g_C1_on hHB he hC.small1 (hC.c7le.trans (c7_le_bgC1 d L N R.BG R.κ)) R.r₀_le I
      zero_le_one R.toStepTowerRenG.renCK_facts.1 hεR z
  · exact thm31g_C2_on hHB he R.r₀_le I zero_le_one (by positivity)
      R.toStepTowerRenG.renCK_facts.1 hεR0 hεR z

/-- **`C₁` and `C₂` of Theorem 3.1 (g) on the fibre, for the solution map of the determinant-only
record at class radius `t / 2`.**  As for `renormDetOnlyZeroM_onFibre_half`, the record used is
determinant-only with zero observable and zero old terms; it is NOT the physical record.  The
solution map `F` is the one of the endpoint identity and of the record, and the `C₂` expansion is
that of this `F`.  Constants: `C₁`: `9 (c_K e)² W(B_z) ε_R`; `C₂`: `(17/32) · 2 · (3 + A)
(c_K c_{K2} B)² W(B_z) ε_R²`, with `e = t / 2`, `B = 8 e`. -/
theorem StepTowerThetaG.renormDetOnlyZeroM_onFibre_half_C12 {d L N : ℕ} [NeZero L] {κmin : ℝ} (R : StepTowerThetaG d L N κmin)
    (hhull : 2 * d * L * (1 + collarB d L) *
        (renDetA d L 1 * (3 / 2 * R.κdec + c1 d L * Real.log 2) + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ R.κ) (hm₀ : R.m₀ = 1) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (hLN : L ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (Xcut : Set (CTorus d L N₁ R.m₁ (k + 1))) :
    ∃ F : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
    ∃ Fcut : RawData d L (N₁ * L ^ R.m₁) (k + 1) N × (Fin 3 → ℂ) →
        (RenLabel (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) Xcut → ℂ) →
        ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 × Fin N → ℂ) ×
          ((lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (R.t / 2) (R.t / 2)
        R.r₀ (8 * (R.t / 2)) F ∧
      (∀ D : BgData (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) N,
        XiCOneReal (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (R.t / 2) D →
        ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ)) ∧
      ∀ (z : Torus d (N₁ * L ^ R.m₁ * L ^ (k + 1 - (k + 1)))) (εR : ℝ), 0 ≤ εR → εR ≤ R.r₀ →
        (∃ term, IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (fun D => XiCOneReal (R.step k hk N₁ ν β p₁).G'
              (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν
              (R.t / 2) D ∧
            ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) εR
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1) (3 / 2 * R.κdec)
          (1 * ((d + 6) * (renCK d L N R.BG R.κ * (R.t / 2)) ^ 2 *
            blockWeight (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (blockSites d L N₁ R.m₁ (k + 1) k z)) * εR ^ 1)
          (fun D ξ => renC1On (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (R.t / 2)
            (blockSites d L N₁ R.m₁ (k + 1) k z) D.Ψ D.h
            (bgFieldC (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (bgC0 d L N) D) ξ)
          term) ∧
        (∃ term, IsLocExp (N := N) (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
          (fun D => XiCOneReal (R.step k hk N₁ ν β p₁).G'
              (R.step k hk N₁ ν β p₁).a (R.step k hk N₁ ν β p₁).ν
              (R.t / 2) D ∧
            ∀ x i, D.h x i = (((R.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) εR
          (renYs (renCube (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1
            (X1 (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) 1) (3 / 2 * R.κdec)
          (1 * (17 / 32 * ((N : ℕ) * ((3 + (bgK1 d L N * (xiC1 d * (R.t / 2)) +
            renCK d L N R.BG R.κ * cK2 d L N * (8 * (R.t / 2)) * R.r₀ + 2)) *
            (renCK d L N R.BG R.κ * cK2 d L N * (8 * (R.t / 2))) ^ 2)) *
            blockWeight (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁))
              (blockSites d L N₁ R.m₁ (k + 1) k z)) * εR ^ 2)
          (fun D ξ => renC2On (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1)
            (blockSites d L N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
            (bgMultC (lvTopG d L N₁ R.m₁ k (rhoSepG d L R.m₁)) (compWeight L 1) ν (bgC0 d L N) D +
              (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term) := by
  exact R.renormDetOnlyZeroM_onFibre_half_C12_core rfl hhull hm₀ k hk N₁ hLN hN hν0 hν β p₁ Xcut
/-- **Determinant-only record with zero observable and zero old terms, at class radius `t / 2`, on
the fibre.**  This is NOT the physical record of Theorem 3.1 (g), (h): the energy function of the
record is only the determinant summand `renE0θ_det`, the observable function and both old-term
differences are zero, and the marked energy and the observable are absent.  What is proved: one
solution map `F` with `IsRenSol`, a cut map `Fcut` whose value at `s = 1` is this `F`, the record
`RenormExpInputOn` on the fibre domain, the localized expansion of the determinant summand, its
value at `ξ = 0` at the step datum, that the step datum lies in the fibre, and that the
renormalized datum lies in the step chart of radius `t`. -/
theorem renormDetOnlyZeroM_onFibre_half {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (Xcut : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (R.toStepTower.step k hk N₁ ν β p₁) 1 z (2 * R.t)
          (towerDetRate R.κ) (towerDetConst R.κ),
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
    ∃ Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) (R.t / 2)
        R.r₀ (8 * (R.t / 2)) F ∧
      AnalyticOnNhd ℂ (fun p : (RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ)) ×
          (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ) => Fcut p.1 p.2)
        (expDom (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)) R.r₀ ×ˢ
          polydisc (0 : RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ)
            (fun _ => Real.exp R.κ)) ∧
      (∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) D →
        ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ)) ∧
      RenormExpInputOn (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)
        R.r₀ (renCK 3 3 2 R.BG R.κ) (8 * (R.t / 2)) F
        (fun z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))) =>
          blockSites 3 3 N₁ R.m₁ (k + 1) k z)
        (fun z => renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
        (fun p => renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
              (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
          (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
          (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k
            (fam 1 (p.1 : CTorus 3 3 N₁ R.m₁ (k + 1)))))
        (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec) (3 / 2 * R.κdec) 1
        (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)))
        0 0 0 (renE0θ_det (R.t / 2) E) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)
        (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) ∧
      (∀ z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1))), ∃ term,
        IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
              (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
              (R.t / 2) D ∧
            ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) R.r₀
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec)
          (hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) *
            Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate R.κ)))
          (renE0θ_det (R.t / 2) E z) term) ∧
      (∀ z, renE0θ_det (R.t / 2) E z (R.toStepTower.step k hk N₁ ν β p₁).D' 0 =
        -(1 / 2 : ℂ) * ∑ y ∈ (R.toStepTower.step k hk N₁ ν β p₁).blockU z, ∑ i : Fin 2,
          (R.toStepTower.step k hk N₁ ν β p₁).logAC (y, i) (y, i)) ∧
      (XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
          (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
          (R.t / 2) (R.toStepTower.step k hk N₁ ν β p₁).D' ∧
        ∀ x i, (R.toStepTower.step k hk N₁ ν β p₁).D'.h x i =
          (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) ∧
      (∀ D : BgData (R.toStepTower.step k hk N₁ ν β p₁).G' 2,
        (XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (R.t / 2) D ∧
          ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) →
        ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ →
          XiCData (R.toStepTower.step k hk N₁ ν β p₁).G'
            (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
            (k + 1) 1 R.t (renThetaDatum (R.toStepTower.step k hk N₁ ν β p₁) (R.t / 2) D ξ)) := by
  have h := R.toG.renormDetOnlyZeroM_onFibre_half_core (ϱ := rhoSep R.m₁)
    (rhoSepG_three _).symm (R.toStepTower.hhull_renDetFibre_toG hR) rfl k hk N₁ h3N hN hν0
    (by exact_mod_cast hν) β p₁ Xcut
  have e2 : towerDetConst R.κ = ((3 : ℕ) : ℝ) ^ 3 * ((1 / 2 : ℝ) * ((2 : ℕ) : ℝ) *
      covBLogMax 3 3 R.κ / (1 - ((detDeg 3 3 + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp R.κ))) := by
    unfold towerDetConst; push_cast; ring
  rw [e2, ← detRateG_three]
  exact h

/-- **`C₁` and `C₂` of Theorem 3.1 (g) on the fibre, for the solution map of the determinant-only
record at class radius `t / 2`.**  As for `renormDetOnlyZeroM_onFibre_half`, the record used is
determinant-only with zero observable and zero old terms; it is NOT the physical record.  The
solution map `F` is the one of the endpoint identity and of the record, and the `C₂` expansion is
that of this `F`.  Constants: `C₁`: `9 (c_K e)² W(B_z) ε_R`; `C₂`: `(17/32) · 2 · (3 + A)
(c_K c_{K2} B)² W(B_z) ε_R²`, with `e = t / 2`, `B = 8 e`. -/
theorem renormDetOnlyZeroM_onFibre_half_C12 {κmin : ℝ} (R : StepTowerTheta κmin)
    (hR : renDetFibreMin ≤ κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (hN : 5 < N₁) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ : ℝ)
    (Xcut : Set (CTorus 3 3 N₁ R.m₁ (k + 1))) :
    ∃ F : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
    ∃ Fcut : RawData 3 3 (N₁ * 3 ^ R.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
        (RenLabel (lvTop N₁ R.m₁ k (rhoSep R.m₁)) Xcut → ℂ) →
        ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 × Fin 2 → ℂ) ×
          ((lvTop N₁ R.m₁ k (rhoSep R.m₁)).Ω 1 → ℂ),
      IsRenSol (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) (R.t / 2)
        R.r₀ (8 * (R.t / 2)) F ∧
      (∀ D : BgData (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 2,
        XiCOneReal (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2) D →
        ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < R.r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ)) ∧
      ∀ (z : Torus 3 (N₁ * 3 ^ R.m₁ * 3 ^ (k + 1 - (k + 1)))) (εR : ℝ), 0 ≤ εR → εR ≤ R.r₀ →
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
              (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
              (R.t / 2) D ∧
            ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec)
          (1 * ((3 + 6) * (renCK 3 3 2 R.BG R.κ * (R.t / 2)) ^ 2 *
            blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) * εR ^ 1)
          (fun D ξ => renC1On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (R.t / 2)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) D.Ψ D.h
            (bgFieldC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) ξ)
          term) ∧
        (∃ term, IsLocExp (N := 2) (lvTop N₁ R.m₁ k (rhoSep R.m₁))
          (fun D => XiCOneReal (R.toStepTower.step k hk N₁ ν β p₁).G'
              (R.toStepTower.step k hk N₁ ν β p₁).a (R.toStepTower.step k hk N₁ ν β p₁).ν
              (R.t / 2) D ∧
            ∀ x i, D.h x i = (((R.toStepTower.step k hk N₁ ν β p₁).h₀ i : ℝ) : ℂ)) εR
          (renYs (renCube (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1
            (X1 (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1 k (fam 1 (blockSite k z))))
          (renDY (lvTop N₁ R.m₁ k (rhoSep R.m₁)) 1) (3 / 2 * R.κdec)
          (1 * (17 / 32 * ((2 : ℕ) * ((3 + (bgK1 3 3 2 * (xiC1 3 * (R.t / 2)) +
            renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2)) * R.r₀ + 2)) *
            (renCK 3 3 2 R.BG R.κ * cK2 3 3 2 * (8 * (R.t / 2))) ^ 2)) *
            blockWeight (lvTop N₁ R.m₁ k (rhoSep R.m₁))
              (blockSites 3 3 N₁ R.m₁ (k + 1) k z)) * εR ^ 2)
          (fun D ξ => renC2On (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1)
            (blockSites 3 3 N₁ R.m₁ (k + 1) k z) ξ (renMassU ν ξ)
            (bgMultC (lvTop N₁ R.m₁ k (rhoSep R.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
              (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term) := by
  have h := R.toG.renormDetOnlyZeroM_onFibre_half_C12_core (ϱ := rhoSep R.m₁)
    (rhoSepG_three _).symm (R.toStepTower.hhull_renDetFibre_toG hR) rfl k hk N₁ h3N hN hν0
    (by exact_mod_cast hν) β p₁ Xcut
  exact h

end Balaban.Inhabited
