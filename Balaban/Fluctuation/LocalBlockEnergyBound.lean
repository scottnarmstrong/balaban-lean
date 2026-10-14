/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.FlCoreCover
public import Balaban.Fluctuation.InteractionVBlock
public import Balaban.Fluctuation.Prop33Nu

/-!
# The block-energy bound at the local generator

`localB_blockEnergyFun_bound`: the bound of `blockEnergyFun_bound` for the literal local generator
`𝔹_{k+1}(Y) = localB (k + 1) … Y` in the role of `Gp`, from the numerical facts alone
(`blockEnergyFun_bound_of_num`).  The proof of the bound uses of the fluctuation core only
`0 ≤ BG`, `0 ≤ BG₂`, `3 ≤ d`, `0 < δ₁`, `0 ≤ ν` and the admissible weights, so neither
`DGSetting` nor `IsLevel` of `localB` is needed.

`localB_nuBlockFun_bound`: the bound of `nuBlockFun_bound` at the local generator, without
`IsLevel (n + 1)` (false for `localB`): the level property was used only to know that a site of the
block lies in `Ω_1`; off `Ω_1` the background `svec` vanishes and the bound is the bound of the
external field (`flReal_phiSub_bound_of_bg`).  The decoupled background is the cover form
`coverBg_exists` with the cover data `localB_coverData`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix
  Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.LargeField

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱm : ℝ}

/-- **The block energy is bounded on the realizable triples at the local generator.** -/
theorem localB_blockEnergyFun_bound {k : ℕ} (hk : k + 1 ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm} {a₁ ν c BG κ eps c₂ BG₂ δ₁ : ℝ}
    {X₁f : Finset (CTorus d L N₁ m₁ K)}
    (HBp : BgHyp d L K (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (hS2 : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂) (hδ₁ : 0 < δ₁)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n + 1 ≤ K) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    {t : ((((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1) × Fin N → ℂ) ×
        (((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1) → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))}
    (ht : t ∈ FlReal (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) Hm a₁ ν BG κ eps
      X₁f BG₂ δ₁) :
    ‖blockEnergyFun (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) Hm
        (compWeight L a₁) ν n z t.1 t.2.1 t.2.2‖ ≤
      energyBd d L N (compWeight L a₁) ν n (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
        (rho4 d L N BG κ) :=
  blockEnergyFun_bound_of_num (by have := HBp.hd; omega) hS.fam.2.1 hS2.fam.2.1 hδ₁ HBp.mass
    HBp.weights hn1 hn z ht

/-- **The block functional is bounded on the realizable triples at the local generator**, with no
level hypothesis. -/
theorem localB_nuBlockFun_bound {k : ℕ} (hk : k + 1 ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm} {a₁ ν c BG κ eps c₂ BG₂ δ₁ : ℝ}
    {X₁f : Finset (CTorus d L N₁ m₁ K)}
    (HBp : BgHyp d L K (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (hS2 : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂) (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (heps : 0 < eps)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) (hc7 : xiC1 d * eps ≤ c7 d L N BG κ)
    (hδ₁ : 0 < δ₁) {n : ℕ} (hp : n + 1 ≤ K) {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) N,
      XiCData (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν K 1
        eps D → ∀ x i, ‖D.h x i‖ ≤ Bh)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    {t : ((((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1) × Fin N → ℂ) ×
        (((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1) → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))}
    (ht : t ∈ FlReal (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) Hm a₁ ν BG κ eps
      X₁f BG₂ δ₁) :
    ‖nuBlockFun (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) Hm n z t.1 t.2.1
        t.2.2‖ ≤
      nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
        (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) :=
  nuBlockFun_bound_of_num (by have := HBp.hd; omega) hS.fam.2.1 hS2.fam.2.1 hδ₁ HBp heps hsmall
    (fun _ hs _ hD => coverBg_exists hS (localB_coverData hk Y hN₁ hMM hag HBp).1 HBp hκ.le hM
      heps hsmall hc7 hs hD) hp hBh0 hBh z ht

end Balaban.Localization
