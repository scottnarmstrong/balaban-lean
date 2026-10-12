/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Background
public import Balaban.Localization.Decoupled2FieldLocal
public import Balaban.Localization.DecoupledBackgroundLocal

/-!
# Theorem I-4b (iv): locality of the decoupled background field, for a cover `C` and an operator `H`

The comparison form of the locality (`i4b_local`) and the support (`i4b_vanish`).  The dependency
sets of the approximate field and the residual (`approxDep`, `resDep`) involve the operator `H`
only.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

variable {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **Theorem I-4b (iv): locality in comparison form.**  Let `𝒞 ⊂ 𝔓`-data, `Y` a union of
nearest-neighbour components of `V(𝒞) ∩ Ω₁`, `S_Y`, `Core_Y` as in I-4a (e), `s, s'` vanishing on
`𝔓 ∖ 𝒞`, equal to `1` off `𝔓` and agreeing on the cubes of `𝒞` inside `Y`, and two data
`D, D₂` of `Ψ̃^c(δ, ε)` whose raw data `(Ψ + Ψ', h + h')` agree on the dependency sets
`resDep x` (the blocks active at the block and neighbours of `x`) for the sites `x` of `Y ∩ Ω₁`.
Then the decoupled background fields satisfy `α_k(s) = α_k(s')` on `S_Y` and
`φ_k(s) = φ_k(s')` on `Y ∩ Ω₁`, in particular on `Core_Y`. -/
theorem i4b_local {c BG : ℝ} (hS : DecSpecs d L Kc Cx c BG) (S : CoverLocal C H a ν Kc Cx) (hconn : HatConn C H)
    (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s s' : DecParams C}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D D₂ : BgData H N}
    (hD : InDomainC H ν δ ε D) (hD₂ : InDomainC H ν δ ε D₂)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ H.Ω 1) Y)
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → extS C s P = 1 ∧ extS C s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → extS C s P = 0 ∧ extS C s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI H (cubeP P) Y → extS C s P = extS C s' P)
    (hdata : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y →
      ∀ y ∈ resDep H (x : CTorus d L N₁ m₁ K), D.Ψ y = D₂.Ψ y ∧ (y ∈ H.Ω 1 → D.h y = D₂.h y))
    {φ φ₂ : H.Ω 1 × Fin N → ℂ} {α α₂ : H.Ω 1 → ℂ}
    (h : IsDecBg C H a ν (rho4 d L N BG κ) s D φ α)
    (h₂ : IsDecBg C H a ν (rho4 d L N BG κ) s' D₂ φ₂ α₂) :
    (∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY C H X₁ 𝒞 Y → α x = α₂ x) ∧
    (∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N, φ (y, i) = φ₂ (y, i)) := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hBG := hS.fam.2.1
  obtain ⟨W⟩ := DataWit.exists hD
  obtain ⟨W₂⟩ := DataWit.exists hD₂
  have Hd := decHyp_of_data (N := N) HB hBG hδ0 hδε hε hδ hνε W
  have Hd₂ := decHyp_of_data (N := N) HB hBG hδ0 hδε hε hδ hνε W₂
  obtain ⟨-, h2, -⟩ := c7_facts (L := L) (N := N) hd0 hBG hδ0.le hδ
  have hCδ : 0 < lemma53Const d L * δ := mul_pos (lemma53Const_pos d L) hδ0
  have hdc := deltaClose_le_deltaStar' (d := d) (L := L) (N := N) (BG := BG) (κ := κ)
  have hdcp := deltaClose_pos (d := d) (L := L) (N := N) (κ := κ) hd0 hBG
  have hle : lemma53Const d L * δ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) := by
    linarith
  have hfix : DecFixed C H a ν s true (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
      (pertSource H a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual H a ν D (approxField H a ν D.Ψ D.h))) α := by
    rw [pertSource_zeroΨ]; exact h.fixed
  have hfix₂ : DecFixed C H a ν s' true (0 : H.Ω 1 → ℂ) (approxField H a ν D₂.Ψ D₂.h)
      (pertSource H a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual H a ν D₂ (approxField H a ν D₂.Ψ D₂.h))) α₂ := by
    rw [pertSource_zeroΨ]; exact h₂.fixed
  have hphi : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y →
      approxField H a ν D.Ψ D.h x = approxField H a ν D₂.Ψ D₂.h x := by
    intro x hx
    exact approxField_congr fun z hz => hdata x hx z
      (approxDep_subset_resDep (mem_resSites_self _) hz)
  have hDA : DataAgree H N Y (0 : H.Ω 1 → ℂ) 0 (approxField H a ν D.Ψ D.h)
      (approxField H a ν D₂.Ψ D₂.h) (0 : CTorus d L N₁ m₁ K → Fin N → ℂ) 0
      (residual H a ν D (approxField H a ν D.Ψ D.h))
      (residual H a ν D₂ (approxField H a ν D₂.Ψ D₂.h)) := by
    exact ⟨fun _ _ => rfl, hphi, fun _ _ => rfl, fun _ _ _ => rfl,
      fun x hx i => residual_congr x i (hdata x hx)⟩
  obtain ⟨hα, hφ⟩ := i4a_local hS.fam S hconn hκ hM hs hs' Hd Hd₂ hle hle hY hs1 hs0 hag hDA
    hfix h.small hfix₂ h₂.small
  refine ⟨hα, fun y hy i => ?_⟩
  have e := hφ y hy i
  rw [pertSource_zeroΨ, pertSource_zeroΨ] at e
  rw [h.field, h₂.field]
  simp only
  rw [hphi y hy, e]

/-- **Theorem I-4b (iv), support**: `φ_k(s) - φ₀ = δφ(s)` vanishes outside `Core(ℛ)`, the union of
the cubes `C_z` of the centres `z` with all factors `s_P ≠ 0` (DG5). -/
theorem i4b_vanish (S : CoverLocal C H a ν Kc Cx) {ρ : ℝ} {s : DecParams C} {D : BgData H N} {φ : H.Ω 1 × Fin N → ℂ}
    {α : H.Ω 1 → ℂ} (h : IsDecBg C H a ν ρ s D φ α) (x : H.Ω 1)
    (hx : (x : CTorus d L N₁ m₁ K) ∉ Core C (extS C s)) (i : Fin N) :
    φ (x, i) = approxField H a ν D.Ψ D.h x i := by
  rw [h.field]
  show approxField H a ν D.Ψ D.h x i + dphi H (decG C H a ν s) (0 : H.Ω 1 → ℂ)
    (approxField H a ν D.Ψ D.h) (residual H a ν D (approxField H a ν D.Ψ D.h)) α (x, i) = _
  have : dphi H (decG C H a ν s) (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
      (residual H a ν D (approxField H a ν D.Ψ D.h)) α (x, i) = 0 := by
    unfold dphi
    rw [liftOp_mulVec]
    by_contra hne
    exact hx (dg5_support S (extS C s) _ x hne)
  rw [this, add_zero]


end Balaban.Localization.Dec2
