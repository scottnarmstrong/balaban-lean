/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSymRoom
public import Balaban.Inhabited.StepTowerNewLevelSymMain
public import Balaban.Inhabited.StepTowerNewLevelSymM

/-!
# `hDzfull` and `hDMfull` of the step densities from the room (`StepTowerNewLevelSymRoomMain`)

`densE0_fullJSymGroup` and `densM0_fullJSymGroup` with the premise `hdom` replaced by the room
`ε + K₂ δ₃ + K₂ δ_fl ≤ ε'_j` of the chain of the old terms at the old levels `1 ≤ j ≤ k`
(`hdom_of_room`, from `hdom_of_pathMem` and `pathMem_of_room`).
-/

@[expose] public section

namespace Balaban.Inhabited.StepSym

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Matrix Filter Topology

section RoomMain

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ eps pp : ℝ} {P : Consts}
  {a' : ℕ → ℝ} {μ' : ℝ} {ε' : ℕ → ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ}
variable {c BG κ Kc Cx c₂ BG₂ δ₁ δc δ₃ δfl r₀ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)
variable (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
  (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hδ₁ : Real.sqrt N * (S.betaU ^ (-(1 / 2 : ℝ)) *
    (covSupConstC d L N (compWeight L S.a₁ k) κ * pp)) < δ₁)

include Jr hC hMX hdm hα hsm hδ₁ in
/-- **The premise `hdom` of `densE0_fullJSymGroup`, `densM0_fullJSymGroup` from the room**: the old
composed pairs of the shifted data near each point of the interpolation path lie in the old
domain `Ξ_j(𝔹_j; ε'_j)`, `1 ≤ j ≤ k`, when the chain of the old terms is set up at the levels and
`ε + K₂ δ₃ + K₂ δ_fl ≤ ε'_j`. -/
theorem hdom_of_room (hβ : 0 < S.β) (hle : S.p₁ ≤ pp)
    (ha' : a' = S.a) (hμ' : μ' = S.ν)
    (hB : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      BgSetting N S.G' (stepG d L N₁ m₁ k ϱ) (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
      c₂ BG₂ δ₁ δfl X₁f)
    (hroom : ∀ j ∈ Finset.Icc 1 k, eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl ≤ ε' j) :
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ < S.p₁ →
      ∀ᶠ w in 𝓝 ((s : ℂ) • S.hatField (hatCovSqrt S.G' S.a₁ S.ν D) (yhat x)),
        ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
        (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
          (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).1
          (composedPairAtC S.a S.ν (Nat.le_succ k) j
            ((S.withDatumH D).dataUCH ((S.withDatumH D).psi0H + w))).2 := by
  intro D hD
  have hBg : BgHyp d L (k + 1) ϱ a' μ' := by
    subst ha' hμ'; exact hC.HBp
  exact hdom_of_pathMem Jr hC hMX hdm hα hsm hβ hle hBg hD
    (pathMem_of_room Jr hC hMX hdm hα hsm hδ₁ hβ hle ha' hμ' hB hF hroom hD)

include hC hMX hdm hα hsm hδ₁ in
/-- **`hDzfull` for the step density from the room**: `densE0_fullJSymGroup` with `hdom` replaced
by the room `ε + K₂ δ₃ + K₂ δ_fl ≤ ε'_j` at the old levels. -/
theorem densE0_fullJSymGroup_of_room (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (hE : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    (hcl : SFTermClauses P (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ) C.Tm)
    (hm : P.m₀ = C.m₀)
    (ha' : a' = S.a) (hμ' : μ' = S.ν)
    (hB : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      BgSetting N S.G' (stepG d L N₁ m₁ k ϱ) (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
      c₂ BG₂ δ₁ δfl X₁f)
    (hroom : ∀ j ∈ Finset.Icc 1 k, eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl ≤ ε' j)
    (hG : S.G' = levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
    (hε : P.eps d L (k + 1) ≤ eps) :
    ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ y (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1))) q.1 q.2 →
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Jr.densE0 C (r y) (actField r q.1, actField r q.2) = Jr.densE0 C y q :=
  densE0_fullJSymGroup Jr C hC hMX hdm hα hsm hβ hp₁ hle hE hcl hm
    (hdom_of_room Jr hC hMX hdm hα hsm hδ₁ hβ hle ha' hμ' hB hF hroom) hG hε

include hC hMX hdm hα hsm hδ₁ in
/-- **`hDMfull` for the step source density from the room**: `densM0_fullJSymGroup` with `hdom`
replaced by the room `ε + K₂ δ₃ + K₂ δ_fl ≤ ε'_j` at the old levels. -/
theorem densM0_fullJSymGroup_of_room (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    (hcl : SFTermClauses P (xiFieldDom a' μ' ε' : FieldDom d L N₁ m₁ (k + 1) N ϱ) C.Tm)
    (hm : P.m₀ = C.m₀)
    (ha' : a' = S.a) (hμ' : μ' = S.ν)
    (hB : ∀ j ∈ Finset.Icc 1 k, ∀ hjk : j ≤ k + 1,
      BgSetting N S.G' (stepG d L N₁ m₁ k ϱ) (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) j hjk)
        S.a₁ S.ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N S.G' (stepG d L N₁ m₁ k ϱ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx
      c₂ BG₂ δ₁ δfl X₁f)
    (hroom : ∀ j ∈ Finset.Icc 1 k, eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl ≤ ε' j)
    (hG : S.G' = levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
    (hε : P.eps d L (k + 1) ≤ eps) :
    ∀ r ∈ fullJSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L (k + 1),
      ∀ x (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) g,
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1))) q.1 q.2 →
      (xiFieldDom S.a S.ν (P.eps d L) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1)
        (levelGS (ϱ := ϱ) (N₁ := N₁) (m₁ := m₁) (k + 1) (le_refl (k + 1)))
        (actField r q.1) (actField r q.2) →
      Jr.densM0 C (r x) ((actField r q.1, actField r q.2), actField r g) =
        Jr.densM0 C x (q, g) :=
  densM0_fullJSymGroup Jr C hC hMX hdm hα hsm hp₁ hle hcl hm
    (hdom_of_room Jr hC hMX hdm hα hsm hδ₁ hβ hle ha' hμ' hB hF hroom) hG hε

end RoomMain

end Balaban.Inhabited.StepSym
