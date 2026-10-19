/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusGenCube
public import Balaban.LargeField.Background.TwoTorusReg
public import Balaban.LargeField.Background.TwoTorusBgPiece
public import Balaban.LargeField.Characteristic.Functions

/-!
# The characteristic functions of cubes on two tori

For corresponding cubes `a_i = zcast n_i (bidx P w₀)` with `w₀` in the box with margin `5 P + 2`
and block fields that agree at the blocks of corresponding sites, the characteristic functions
`χ_q(□)` (`chiK`) and `χ'_{k+1}(□')` (`chiPrimeNew`) of the two tori agree
(`chiK_corr`, `chiPrimeNew_corr`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField

theorem charFn_eq_of_iff {X Y : Type*} {P : X → Prop} {Q : Y → Prop} {x : X} {y : Y}
    (h : P x ↔ Q y) : charFn P x = charFn Q y := by
  classical
  rw [charFn_apply, charFn_apply]
  simp only [h]

section Single

variable {d L N₁ N₂ k Nv : ℕ} [NeZero N₁] [NeZero N₂] [NeZero L] {ϱ₁ ϱ₂ : ℝ}
  {G₁ : GeneratingSet d L N₁ k ϱ₁} {G₂ : GeneratingSet d L N₂ k ϱ₂} {cc : Fin d → ℤ}

/-- The data of the single lift agree when `ψ` agrees at the `k`-blocks of corresponding sites. -/
theorem dataAgree_liftSingle (hA : GenAgree G₁ G₂ cc)
    (ψ₁ : Torus d (N₁ * L ^ (k - k)) → Fin Nv → ℂ) (ψ₂ : Torus d (N₂ * L ^ (k - k)) → Fin Nv → ℂ)
    (h : Fin Nv → ℂ)
    (hψ : ∀ w, InBox (N₁ * L ^ k) (N₂ * L ^ k) cc w →
      ∀ i, ψ₁ (jBlock d L N₁ k k (zcast (N₁ * L ^ k) w)) i =
        ψ₂ (jBlock d L N₂ k k (zcast (N₂ * L ^ k) w)) i) :
    DataAgree G₁ G₂ cc (liftSingle G₁ ψ₁ h) (liftSingle G₂ ψ₂ h) where
  psi w hw hdata i := by
    have hdata2 : zcast (N₂ * L ^ k) w ∈ dataSites G₂ :=
      (hA.dataSites_ptCorr (ptCorr_zcast hw)).1 hdata
    rw [liftSingle_Ψ _ _ _ hdata, liftSingle_Ψ _ _ _ hdata2]
    exact hψ w hw i
  h w _ hmem i := by
    have hmem2 : zcast (N₂ * L ^ k) w ∈ G₂.Ω 1 := by
      have := (hA.agree 1 le_rfl (by omega) w ‹_›).1 hmem
      exact this
    rw [liftSingle_h _ _ _ hmem, liftSingle_h _ _ _ hmem2]

end Single

section ChiK

variable {d M1 c L q n₁ n₂ Nv : ℕ} [NeZero M1] [NeZero c] [NeZero L] [NeZero n₁] [NeZero n₂]

/-- **`χ_q(□)` of corresponding cubes of two tori agree** when the block fields agree at the
blocks of corresponding sites. -/
theorem chiK_corr (hc : 14 ≤ c) (hL : 2 ≤ L) {cc w₀ : Fin d → ℤ} (hn₁ : 12 ≤ n₁)
    (hn₂ : 12 ≤ n₂)
    (hw₀ : InBoxK (5 * (L ^ q * (c * M1)) + 2) (M1 * (c * n₁) * L ^ q) (M1 * (c * n₂) * L ^ q)
      cc w₀) (a : ℕ → ℝ) (μ δ : ℝ) (h : Fin Nv → ℝ)
    (ψ₁ : BlockCfg d (M1 * (c * n₁)) L q q Nv) (ψ₂ : BlockCfg d (M1 * (c * n₂)) L q q Nv)
    (hψ : ∀ w, InBox (M1 * (c * n₁) * L ^ q) (M1 * (c * n₂) * L ^ q) cc w →
      ∀ i, ψ₁ (jBlock d L (M1 * (c * n₁)) q q (zcast (M1 * (c * n₁) * L ^ q) w)) i =
        ψ₂ (jBlock d L (M1 * (c * n₂)) q q (zcast (M1 * (c * n₂) * L ^ q) w)) i) :
    chiK (M1 := M1) (N₁ := c * n₁) (L := L) (q := q) (N := Nv) a μ δ h c n₁
        (zcast n₁ (bidx (L ^ q * (c * M1)) w₀)) ψ₁ =
      chiK (M1 := M1) (N₁ := c * n₂) (L := L) (q := q) (N := Nv) a μ δ h c n₂
        (zcast n₂ (bidx (L ^ q * (c * M1)) w₀)) ψ₂ := by
  have hA := genAgree_genCube hc hL hn₁ hn₂ hw₀
  have hN₁ : 2 ≤ M1 * (c * n₁) := by
    have h1 : 1 ≤ M1 := Nat.pos_of_ne_zero (NeZero.ne _)
    have := Nat.mul_le_mul h1 (Nat.mul_le_mul hc hn₁)
    omega
  have hN₂ : 2 ≤ M1 * (c * n₂) := by
    have h1 : 1 ≤ M1 := Nat.pos_of_ne_zero (NeZero.ne _)
    have := Nat.mul_le_mul h1 (Nat.mul_le_mul hc hn₂)
    omega
  have hD := dataAgree_liftSingle hA ψ₁.toC ψ₂.toC (fun i => (h i : ℂ)) (fun w hw i => by
    simp only [BlockCfg.toC]
    exact_mod_cast hψ w hw i)
  have hT := setCorr_cubeNbhd (r := 1) hc (by omega) (n₁ := n₁) (n₂ := n₂) (L := L) (q := q)
    (M1 := M1) (by omega) (by omega) hw₀
  unfold chiK
  refine charFn_eq_of_iff ?_
  unfold ChiKProp cubeData
  exact hA.reg_iff hD hN₁ hN₂ a hT hT μ δ

end ChiK

section ChiPrime

variable {d M1 c L k n₁ n₂ Nv : ℕ} [NeZero M1] [NeZero c] [NeZero L] [NeZero n₁] [NeZero n₂]

/-- **`χ'_{k+1}(□')` of corresponding cubes of two tori agree** when `Ω_{k+1}` and the block fields
agree at corresponding sites. -/
theorem chiPrimeNew_corr (hc : 14 ≤ c) (hL : 2 ≤ L) {cc w₀ : Fin d → ℤ} (hn₁ : 12 ≤ n₁)
    (hn₂ : 12 ≤ n₂)
    (hw₀ : InBoxK (5 * (L ^ (k + 1) * (c * M1)) + 2) (M1 * (c * n₁) * L ^ (k + 1))
      (M1 * (c * n₂) * L ^ (k + 1)) cc w₀) (a : ℕ → ℝ) (μ δ νk : ℝ) (h : Fin Nv → ℝ)
    (hm₁ : (c * n₁) * L ^ (k + 1 - (k + 1)) = c * n₁)
    (hm₂ : (c * n₂) * L ^ (k + 1 - (k + 1)) = c * n₂)
    (Om₁ : Finset (Torus d (M1 * (c * n₁) * L ^ (k + 1))))
    (Om₂ : Finset (Torus d (M1 * (c * n₂) * L ^ (k + 1))))
    (hOm₁ : IsBlockUnion L (M1 * (c * n₁)) (k + 1) (k + 1) Om₁)
    (hOm₂ : IsBlockUnion L (M1 * (c * n₂)) (k + 1) (k + 1) Om₂)
    (hOm : SetIff cc (Om₁ : Set (Torus d (M1 * (c * n₁) * L ^ (k + 1))))
      (Om₂ : Set (Torus d (M1 * (c * n₂) * L ^ (k + 1)))))
    (ψ₁ : BlockCfg d (M1 * (c * n₁)) L (k + 1) k Nv)
    (θ₁ : BlockCfg d (M1 * (c * n₁)) L (k + 1) (k + 1) Nv)
    (ψ₂ : BlockCfg d (M1 * (c * n₂)) L (k + 1) k Nv)
    (θ₂ : BlockCfg d (M1 * (c * n₂)) L (k + 1) (k + 1) Nv)
    (hψ : ∀ w, InBox (M1 * (c * n₁) * L ^ (k + 1)) (M1 * (c * n₂) * L ^ (k + 1)) cc w →
      ∀ i, ψ₁ (jBlock d L (M1 * (c * n₁)) (k + 1) k (zcast (M1 * (c * n₁) * L ^ (k + 1)) w)) i =
        ψ₂ (jBlock d L (M1 * (c * n₂)) (k + 1) k (zcast (M1 * (c * n₂) * L ^ (k + 1)) w)) i)
    (hϑ : ∀ w, InBox (M1 * (c * n₁) * L ^ (k + 1)) (M1 * (c * n₂) * L ^ (k + 1)) cc w →
      ∀ i, θ₁ (jBlock d L (M1 * (c * n₁)) (k + 1) (k + 1)
          (zcast (M1 * (c * n₁) * L ^ (k + 1)) w)) i =
        θ₂ (jBlock d L (M1 * (c * n₂)) (k + 1) (k + 1)
          (zcast (M1 * (c * n₂) * L ^ (k + 1)) w)) i) :
    chiPrimeNew (M1 := M1) (N₁ := c * n₁) (L := L) (N := Nv) (k := k) a μ δ νk h hm₁
        (zcast n₁ (bidx (L ^ (k + 1) * (c * M1)) w₀)) Om₁ hOm₁ (ψ₁, θ₁) =
      chiPrimeNew (M1 := M1) (N₁ := c * n₂) (L := L) (N := Nv) (k := k) a μ δ νk h hm₂
        (zcast n₂ (bidx (L ^ (k + 1) * (c * M1)) w₀)) Om₂ hOm₂ (ψ₂, θ₂) := by
  have hOmw : ∀ w, InBox (M1 * (c * n₁) * L ^ (k + 1)) (M1 * (c * n₂) * L ^ (k + 1)) cc w →
      (zcast (M1 * (c * n₁) * L ^ (k + 1)) w ∈ Om₁ ↔
        zcast (M1 * (c * n₂) * L ^ (k + 1)) w ∈ Om₂) := fun w hw =>
    hOm _ _ (by rw [hw.liftNear_zcast₁, hw.liftNear_zcast₂])
  have hA := genAgree_genCubeMixed hc hL hn₁ hn₂ hw₀ hm₁ hm₂ Om₁ Om₂ hOm₁ hOm₂ hOmw
  have hN₁ : 2 ≤ M1 * (c * n₁) := by
    have h1 : 1 ≤ M1 := Nat.pos_of_ne_zero (NeZero.ne _)
    have := Nat.mul_le_mul h1 (Nat.mul_le_mul hc hn₁)
    omega
  have hN₂ : 2 ≤ M1 * (c * n₂) := by
    have h1 : 1 ≤ M1 := Nat.pos_of_ne_zero (NeZero.ne _)
    have := Nat.mul_le_mul h1 (Nat.mul_le_mul hc hn₂)
    omega
  have hD := dataAgree_liftMixed hA hOm₁ hOm₂ (genCubeMixed_top_subset hm₁ _ _ hOm₁)
    (genCubeMixed_top_subset hm₂ _ _ hOm₂) ψ₁.toC θ₁.toC ψ₂.toC θ₂.toC (fun i => (h i : ℂ))
    (fun w hw _ => hOmw w hw)
    (fun w hw i => by simp only [BlockCfg.toC]; exact_mod_cast hψ w hw i)
    (fun w hw i => by simp only [BlockCfg.toC]; exact_mod_cast hϑ w hw i)
  have hT := setCorr_cubeNbhd (r := 1) hc (by omega) (n₁ := n₁) (n₂ := n₂) (L := L) (q := k + 1)
    (M1 := M1) (by omega) (by omega) hw₀
  have hTf : SetCorr cc
      ((cubeNbhd M1 (c * n₁) L (k + 1) c n₁ 1 (zcast n₁ (bidx (L ^ (k + 1) * (c * M1)) w₀)) \ Om₁ :
        Finset (Torus d (M1 * (c * n₁) * L ^ (k + 1)))) : Set (Torus d (M1 * (c * n₁) * L ^ (k + 1))))
      ((cubeNbhd M1 (c * n₂) L (k + 1) c n₂ 1 (zcast n₂ (bidx (L ^ (k + 1) * (c * M1)) w₀)) \ Om₂ :
        Finset (Torus d (M1 * (c * n₂) * L ^ (k + 1)))) : Set (Torus d (M1 * (c * n₂) * L ^ (k + 1)))) := by
    rw [Finset.coe_sdiff, Finset.coe_sdiff]
    exact hT.sdiff_iff hOm
  have hTn : SetCorr cc
      ((cubeNbhd M1 (c * n₁) L (k + 1) c n₁ 1 (zcast n₁ (bidx (L ^ (k + 1) * (c * M1)) w₀)) ∩ Om₁ :
        Finset (Torus d (M1 * (c * n₁) * L ^ (k + 1)))) : Set (Torus d (M1 * (c * n₁) * L ^ (k + 1))))
      ((cubeNbhd M1 (c * n₂) L (k + 1) c n₂ 1 (zcast n₂ (bidx (L ^ (k + 1) * (c * M1)) w₀)) ∩ Om₂ :
        Finset (Torus d (M1 * (c * n₂) * L ^ (k + 1)))) : Set (Torus d (M1 * (c * n₂) * L ^ (k + 1)))) := by
    rw [Finset.coe_inter, Finset.coe_inter]
    exact hT.inter_iff hOm
  unfold chiPrimeNew
  refine charFn_eq_of_iff ?_
  unfold ChiPrimeNewProp mixedData
  rw [hA.inUnionDomainR_iff hN₁ hN₂ hD, hA.regMixedIneq_iff hD hN₁ hN₂ a hTf hTn hT μ _ νk δ]

end ChiPrime

end Balaban.RootFSpine
