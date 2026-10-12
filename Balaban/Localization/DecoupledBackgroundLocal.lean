/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledBackground
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem I-4b (iv): locality of the decoupled background field

* `approxDep`, `resDep`: the sites where the data `(Ψ, h̃)` enter the approximate field `φ₀` and
  the residual `f₀` of Lemma 5.3 at a site (the blocks active at the site, and the block, the
  neighbours and the collar neighbours for the residual);
* `approxField_congr`, `residual_congr`: `φ₀(x)` and `f₀(x)` only depend on the data on these sets;
* `i4b_local`: the comparison form of the locality of the decoupled background field.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Dep

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

variable (G) in
/-- The sites whose data enter `φ₀(x)`: `x` and the base points of the blocks active at `x`. -/
noncomputable def approxDep (x : Torus d (N₀ * L ^ k)) : Finset (Torus d (N₀ * L ^ k)) := by
  classical
  exact insert x ((active G x).image Prod.snd)

variable (G) in
/-- The sites where `φ₀` is read by the residual `f₀(x)`: the block of `x`, `x` and its
neighbours. -/
noncomputable def resSites (x : Torus d (N₀ * L ^ k)) : Finset (Torus d (N₀ * L ^ k)) := by
  classical
  exact insert x (G.blk (G.layerIndex x) x ∪ (Finset.univ.image fun μ : Fin d => x + Pi.single μ 1) ∪
    (Finset.univ.image fun μ : Fin d => x - Pi.single μ 1))

variable (G) in
/-- The sites whose data enter the residual `f₀(x)` of the approximate field. -/
noncomputable def resDep (x : Torus d (N₀ * L ^ k)) : Finset (Torus d (N₀ * L ^ k)) := by
  classical
  exact (resSites G x).biUnion (approxDep G)

theorem mem_approxDep_self (x : Torus d (N₀ * L ^ k)) : x ∈ approxDep G x := by
  classical
  unfold approxDep; exact Finset.mem_insert_self _ _

theorem mem_resSites_self (x : Torus d (N₀ * L ^ k)) : x ∈ resSites G x := by
  classical
  unfold resSites; exact Finset.mem_insert_self _ _

theorem approxDep_subset_resDep {x y : Torus d (N₀ * L ^ k)} (hy : y ∈ resSites G x) :
    approxDep G y ⊆ resDep G x := by
  classical
  intro z hz
  unfold resDep
  exact Finset.mem_biUnion.2 ⟨y, hy, hz⟩

/-- **Locality of the approximate field**: `φ₀(x)` depends only on the data on `approxDep x`. -/
theorem approxField_congr {Ψ Ψ₂ h h₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {x : Torus d (N₀ * L ^ k)}
    (hag : ∀ y ∈ approxDep G x, Ψ y = Ψ₂ y ∧ (y ∈ G.Ω 1 → h y = h₂ y)) :
    approxField G a ν Ψ h x = approxField G a ν Ψ₂ h₂ x := by
  classical
  have hloc : ∀ y ∈ approxDep G x, locSol G a ν Ψ h y = locSol G a ν Ψ₂ h₂ y := by
    intro y hy
    unfold locSol
    by_cases hyΩ : y ∈ G.Ω 1
    · simp only [hyΩ, ↓reduceIte]
      rw [(hag y hy).1, (hag y hy).2 hyΩ]
    · simp only [hyΩ, ↓reduceIte]
      rw [(hag y hy).1]
  have hint : interp G (locSol G a ν Ψ h) x = interp G (locSol G a ν Ψ₂ h₂) x := by
    unfold interp
    refine Finset.sum_congr rfl fun q hq => ?_
    by_cases hqa : q ∈ active G x
    · have : q.2 ∈ approxDep G x := by
        unfold approxDep
        exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨q, hqa, rfl⟩)
      rw [hloc q.2 this]
    · rw [weight_eq_zero G hq hqa]; simp
  unfold approxField
  by_cases hxΩ : x ∈ G.Ω 1
  · simp only [hxΩ, ↓reduceIte]
    by_cases hl : G.layerIndex x ≤ 1
    · simp only [hl, ↓reduceIte]
      exact hloc x (mem_approxDep_self x)
    · simp only [hl, ↓reduceIte]
      rw [hint]
  · by_cases hc : x ∈ collar G
    · simp only [hxΩ, hc, ↓reduceIte]
      exact hloc x (mem_approxDep_self x)
    · simp only [hxΩ, hc, ↓reduceIte]

/-- **Locality of the residual**: `f₀(x, i)` depends only on the data on `resDep x`. -/
theorem residual_congr {D D₂ : BgData G N} (x : G.Ω 1) (i : Fin N)
    (hag : ∀ y ∈ resDep G (x : Torus d (N₀ * L ^ k)),
      D.Ψ y = D₂.Ψ y ∧ (y ∈ G.Ω 1 → D.h y = D₂.h y)) :
    residual G a ν D (approxField G a ν D.Ψ D.h) (x, i) =
      residual G a ν D₂ (approxField G a ν D₂.Ψ D₂.h) (x, i) := by
  classical
  have hS : ∀ y ∈ resSites G (x : Torus d (N₀ * L ^ k)),
      approxField G a ν D.Ψ D.h y = approxField G a ν D₂.Ψ D₂.h y := fun y hy =>
    approxField_congr fun z hz => hag z (approxDep_subset_resDep hy hz)
  have hxs := mem_resSites_self (G := G) (x : Torus d (N₀ * L ^ k))
  have hxd : (x : Torus d (N₀ * L ^ k)) ∈ resDep G (x : Torus d (N₀ * L ^ k)) :=
    approxDep_subset_resDep hxs (mem_approxDep_self _)
  have hblk : ∀ y ∈ G.blk (G.layerIndex (x : Torus d (N₀ * L ^ k))) (x : Torus d (N₀ * L ^ k)),
      approxField G a ν D.Ψ D.h y = approxField G a ν D₂.Ψ D₂.h y := fun y hy => hS y (by
    unfold resSites
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hy)))
  have hp : ∀ μ : Fin d, approxField G a ν D.Ψ D.h ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) =
      approxField G a ν D₂.Ψ D₂.h ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) := fun μ => hS _ (by
    unfold resSites
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨μ, Finset.mem_univ _, rfl⟩))))
  have hm : ∀ μ : Fin d, approxField G a ν D.Ψ D.h ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) =
      approxField G a ν D₂.Ψ D₂.h ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) := fun μ => hS _ (by
    unfold resSites
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨μ, Finset.mem_univ _, rfl⟩)))
  have hΨx := (hag _ hxd).1
  have hhx := (hag _ hxd).2 x.2
  have hΨp : ∀ μ : Fin d, D.Ψ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) =
      D₂.Ψ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) := fun μ => (hag _ (by
    refine approxDep_subset_resDep (y := (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) ?_
      (mem_approxDep_self _)
    unfold resSites
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨μ, Finset.mem_univ _, rfl⟩))))).1
  have hΨm : ∀ μ : Fin d, D.Ψ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) =
      D₂.Ψ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) := fun μ => (hag _ (by
    refine approxDep_subset_resDep (y := (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) ?_
      (mem_approxDep_self _)
    unfold resSites
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image.2 ⟨μ, Finset.mem_univ _, rfl⟩)))).1
  rw [residual_apply, residual_apply]
  have hsum : ∑ y ∈ G.blk (G.layerIndex (x : Torus d (N₀ * L ^ k))) (x : Torus d (N₀ * L ^ k)),
      approxField G a ν D.Ψ D.h y i = ∑ y ∈ G.blk (G.layerIndex (x : Torus d (N₀ * L ^ k)))
        (x : Torus d (N₀ * L ^ k)), approxField G a ν D₂.Ψ D₂.h y i :=
    Finset.sum_congr rfl fun y hy => by rw [hblk y hy]
  rw [hsum, hΨx, hhx, hS _ hxs]
  simp only [hp, hm, hΨp, hΨm]

end Dep


section Local

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **Theorem I-4b (iv): locality in comparison form.**  Let `𝒞 ⊂ 𝔓`-data, `Y` a union of
nearest-neighbour components of `V(𝒞) ∩ Ω₁`, `S_Y`, `Core_Y` as in I-4a (e), `s, s'` vanishing on
`𝔓 ∖ 𝒞`, equal to `1` off `𝔓` and agreeing on the cubes of `𝒞` inside `Y`, and two data
`D, D₂` of `Ψ̃^c(δ, ε)` whose raw data `(Ψ + Ψ', h + h')` agree on the dependency sets
`resDep x` (the blocks active at the block and neighbours of `x`) for the sites `x` of `Y ∩ Ω₁`.
Then the decoupled background fields satisfy `α_k(s) = α_k(s')` on `S_Y` and
`φ_k(s) = φ_k(s')` on `Y ∩ Ω₁`, in particular on `Core_Y`. -/
theorem i4b_local {c BG : ℝ} (hS : DecSpecs d L c BG) (S : DGSetting G a ν) (hconn : HatConn G)
    (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s s' : DecParams G}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D D₂ : BgData G N}
    (hD : InDomainC G ν δ ε D) (hD₂ : InDomainC G ν δ ε D₂)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx G, P ∉ parCubes G X₁ → extS G s P = 1 ∧ extS G s' P = 1)
    (hs0 : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → extS G s P = 0 ∧ extS G s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI G (cubeP P) Y → extS G s P = extS G s' P)
    (hdata : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y →
      ∀ y ∈ resDep G (x : CTorus d L N₁ m₁ K), D.Ψ y = D₂.Ψ y ∧ (y ∈ G.Ω 1 → D.h y = D₂.h y))
    {φ φ₂ : G.Ω 1 × Fin N → ℂ} {α α₂ : G.Ω 1 → ℂ}
    (h : IsDecBg G a ν (rho4 d L N BG κ) s D φ α)
    (h₂ : IsDecBg G a ν (rho4 d L N BG κ) s' D₂ φ₂ α₂) :
    (∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → α x = α₂ x) ∧
    (∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N, φ (y, i) = φ₂ (y, i)) := by
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
  have hfix : DecFixed G a ν s true (0 : G.Ω 1 → ℂ) (approxField G a ν D.Ψ D.h)
      (pertSource G a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual G a ν D (approxField G a ν D.Ψ D.h))) α := by
    rw [pertSource_zeroΨ]; exact h.fixed
  have hfix₂ : DecFixed G a ν s' true (0 : G.Ω 1 → ℂ) (approxField G a ν D₂.Ψ D₂.h)
      (pertSource G a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual G a ν D₂ (approxField G a ν D₂.Ψ D₂.h))) α₂ := by
    rw [pertSource_zeroΨ]; exact h₂.fixed
  have hphi : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y →
      approxField G a ν D.Ψ D.h x = approxField G a ν D₂.Ψ D₂.h x := by
    intro x hx
    exact approxField_congr fun z hz => hdata x hx z
      (approxDep_subset_resDep (mem_resSites_self _) hz)
  have hDA : DataAgree G N Y (0 : G.Ω 1 → ℂ) 0 (approxField G a ν D.Ψ D.h)
      (approxField G a ν D₂.Ψ D₂.h) (0 : CTorus d L N₁ m₁ K → Fin N → ℂ) 0
      (residual G a ν D (approxField G a ν D.Ψ D.h))
      (residual G a ν D₂ (approxField G a ν D₂.Ψ D₂.h)) := by
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
theorem i4b_vanish {ρ : ℝ} {s : DecParams G} {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ}
    {α : G.Ω 1 → ℂ} (h : IsDecBg G a ν ρ s D φ α) (x : G.Ω 1)
    (hx : (x : CTorus d L N₁ m₁ K) ∉ Core G (extS G s)) (i : Fin N) :
    φ (x, i) = approxField G a ν D.Ψ D.h x i := by
  rw [h.field]
  show approxField G a ν D.Ψ D.h x i + dphi G (decG G a ν s) (0 : G.Ω 1 → ℂ)
    (approxField G a ν D.Ψ D.h) (residual G a ν D (approxField G a ν D.Ψ D.h)) α (x, i) = _
  have : dphi G (decG G a ν s) (0 : G.Ω 1 → ℂ) (approxField G a ν D.Ψ D.h)
      (residual G a ν D (approxField G a ν D.Ψ D.h)) α (x, i) = 0 := by
    unfold dphi
    rw [liftOp_mulVec]
    by_contra hne
    exact hx (dg5_support (G := G) (a := a) (ν := ν) (α := (0 : G.Ω 1 → ℂ) + α) (extS G s) _ x hne)
  rw [this, add_zero]

end Local

end Balaban.Localization
