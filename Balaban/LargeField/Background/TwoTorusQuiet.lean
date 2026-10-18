/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusMainActionCorr
public import Balaban.LargeField.Background.TwoTorusChiNewFinal
public import Balaban.LargeField.Background.TwoTorusGauss
public import Balaban.LargeField.Background.TwoTorusChiProd

/-!
# The quiet kernel on two tori

`quietKernel_twoTorus`: at corresponding configurations (`CfgCorr`), corresponding output
configurations (`OutCorr`) and corresponding localized histories (`HistCorr`) of the components
`Zc₁`, `Zc₂`, with the same constants `(M₁, c)` on both tori, the quiet kernels agree.  Each of the
eight factors of the kernel is handled by its own lemma: `gaussProd_corr`, `factor_chiK_k`,
`cubeProd_chiPrimeNew_corr` (twice), `cubeProd_chiK_corr`, `chiNew_corr`, `factor_domain`,
`mainActionLoc_corr`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField RegionHistory

section Quiet

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {k0 K M N : ℕ} [NeZero M] [NeZero S.L] {k : ℕ}

open Classical in
/-- **The quiet kernel agrees on two tori.**  At corresponding localized histories of
corresponding components, corresponding output configurations and corresponding configurations of
the new internal variables, the quiet kernels (Definition II.5.6) agree, for the same direction
`hv` and the same constants. -/
theorem quietKernel_twoTorus (g₁ : Geo S n₁ R M) (g₂ : Geo S n₂ R M) (h1 : g₂.M1 = g₁.M1)
    (h2 : g₂.c = g₁.c) (Hl₁ : RegionHistory S n₁ R k0 K) (Hl₂ : RegionHistory S n₂ R k0 K)
    (hrem₁ : ∀ j, Hl₁.rem j = ∅) (hrem₂ : ∀ j, Hl₂.rem j = ∅) (hk : k + 1 ≤ K)
    (Zc₁ : Finset (Torus S.d (n₁ (k + 1)))) (Zc₂ : Finset (Torus S.d (n₂ (k + 1))))
    (hZc₁ : Zc₁ ∈ comps (S.omega (k + 1)) (Hl₁.F.Zp (k + 1)))
    (hZc₂ : Zc₂ ∈ comps (S.omega (k + 1)) (Hl₂.F.Zp (k + 1))) {cc : Fin S.d → ℤ}
    (hH : HistCorr cc (locHist Hl₁ M K (k + 1) Zc₁) (locHist Hl₂ M K (k + 1) Zc₂))
    (hV : SetCorr cc (Vsites R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1))
      (Vsites R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)))
    (cs : OpConsts) (hv : EuclideanSpace ℝ (Fin N))
    {o₁ : OutT N R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)}
    {o₂ : OutT N R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)}
    {x₁ : NewCfg N (locHist Hl₁ M K (k + 1) Zc₁) k} {x₂ : NewCfg N (locHist Hl₂ M K (k + 1) Zc₂) k}
    (hout : OutCorr cc (k + 1) o₁ o₂) (hcfg : CfgCorr cc x₁ x₂) :
    quietKernel g₁ Hl₁ k Zc₁ hZc₁ hk cs hrem₁ o₁ x₁ hv =
      quietKernel g₂ Hl₂ k Zc₂ hZc₂ hk cs hrem₂ o₂ x₂ hv := by
  have hL : 2 ≤ S.L := Hl₁.F.ok.two_le_L
  have hρk := g₁.three_L_le_floor Hl₁ k
  have hR6 : 6 ≤ ⌊R k⌋₊ := by omega
  have hω₁ := (Hl₁.F.stepGeom (by omega : k < K)).rad.omega_rho
  have hω₂ := (Hl₂.F.stepGeom (by omega : k < K)).rad.omega_rho
  have h32₁ : 32 ≤ n₁ (k + 1) := room_of_V Hl₁ hrem₁ hk g₁.hM g₁.hc hρk Zc₁ hZc₁ hV.1
  have h32₂ : 32 ≤ n₂ (k + 1) :=
    room_of_V Hl₂ hrem₂ hk g₂.hM g₂.hc (g₂.three_L_le_floor Hl₂ k) Zc₂ hZc₂
      (fun y hy => (hV.2.1 y hy).symm)
  have hkK : k ≤ K := (Nat.le_succ k).trans hk
  have hq₁ : ∀ j, j ≤ k + 1 → 4 ≤ M * n₁ K * S.L ^ (K - j) := fun j hj =>
    four_le_block Hl₁.F.hnn hk h32₁ hj
  have hq₂ : ∀ j, j ≤ k + 1 → 4 ≤ M * n₂ K * S.L ^ (K - j) := fun j hj =>
    four_le_block Hl₂.F.hnn hk h32₂ hj
  have hZ₁ : ∀ x ∈ (locHist Hl₁ M K (k + 1) Zc₁).Z (k + 1),
      cubeMap n₁ S.L M K (k + 1) x ∈ (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) := fun x hx => hx.2
  have hΩ₁ : ∀ x ∈ (locHist Hl₁ M K (k + 1) Zc₁).Omega k,
      cubeMap n₁ S.L M K (k + 1) x ∈ (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) := fun x hx => hx.2
  have hZone : ∀ w, InBox (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc w →
      cubeMap n₁ S.L M K (k + 1) (zcast (M * n₁ K * S.L ^ K) w) ∈
        (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) →
        InBoxK (6 * (S.L ^ (k + 1) * M)) (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) cc w := by
    intro w hw hc
    have hm := margin₁ Hl₁ Hl₂ hrem₁ hk Zc₁ Zc₂ hZc₁ hV (r := 0) (m := 6) (by omega)
      (by omega) (zcast _ w) (subset_nbhd _ _ hc)
    rwa [hw.liftNear_zcast₁] at hm
  have hψ : ∀ y₁ y₂, BlkCorr cc k k y₁ y₂ →
      subVarField N x₁ k y₁ = subVarField N x₂ k y₂ := fun y₁ y₂ h =>
    subVarField_corr hH hcfg (fun p₁ p₂ h => newVars_iff p₁ p₂ h) hkK (hq₁ k (by omega))
      (hq₂ k (by omega)) h
  have hθ : ∀ y₁ y₂, BlkCorr cc (k + 1) (k + 1) y₁ y₂ →
      cs.z (k + 1) • outField N o₁ y₁ = cs.z (k + 1) • outField N o₂ y₂ := fun y₁ y₂ h => by
    rw [hout y₁ y₂ h]
  have h12₁ : 12 ≤ n₁ (k + 1) := by omega
  have h12₂ : 12 ≤ n₂ (k + 1) := by omega
  unfold quietKernel
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_
  · exact gaussProd_corr hH hcfg hk hq₁ hq₂ cs hout
  · exact factor_chiK_k g₁ g₂ h1 h2 hL Hl₁.F.hnn Hl₂.F.hnn hk cs hv hH h32₁ h32₂ hZ₁ hZone hcfg
  · unfold cubeProd cubeFin
    refine cubeProd_chiPrimeNew_corr g₁ g₂ h1 h2 hL Hl₁.F.hnn Hl₂.F.hnn hk h12₁ h12₂ cs.aw
      (cs.mu (k + 1)) (cs.delta k) (cs.nu k) hv hH
      (cSetCorr_quietA2 Hl₁.F.hnn Hl₂.F.hnn hk hH (by omega) (by omega)) ?_ _ _ _ _ hψ hθ
    intro w₀ hw hy
    exact margin_cube Hl₁.F.hnn hL hk (j := k + 1) le_rfl hZ₁ hZone hw (fun x hx => (hy.1 x hx).1)
  · unfold cubeProd cubeFin
    refine cubeProd_chiPrimeNew_corr g₁ g₂ h1 h2 hL Hl₁.F.hnn Hl₂.F.hnn hk h12₁ h12₂ cs.aw
      (cs.mu (k + 1)) (cs.delta k) (cs.nu k) hv hH
      (cSetCorr_quietA3 Hl₁.F.hnn Hl₂.F.hnn hk hH (by omega) (by omega)) ?_ _ _ _ _ hψ hθ
    intro w₀ hw hy
    exact margin_cube Hl₁.F.hnn hL hk (j := k + 1) le_rfl hΩ₁ hZone hw hy.1
  · unfold cubeProd cubeFin
    refine cubeProd_chiK_corr g₁ g₂ h1 h2 hL Hl₁.F.hnn Hl₂.F.hnn (q := k + 1) hk h12₁ h12₂ cs.aw
      (cs.mu (k + 1)) (cs.delta (k + 1)) hv
      (cSetCorr_quietA4 Hl₁.F.hnn Hl₂.F.hnn hk hH (by omega) (by omega)) ?_ _ _ ?_
    · intro w₀ hw hy
      exact margin_cube Hl₁.F.hnn hL hk (j := k + 1) le_rfl hZ₁ hZone hw hy.1
    · intro y₁ y₂ h
      exact hout y₁ y₂ h
  · exact chiNew_corr Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hL
      (fun j _ _ => g₁.hRlow j) (fun j _ _ => g₂.hRlow j) hω₁ hω₂ hR6 hout hcfg cs
  · exact factor_domain g₁ g₂ h1 h2 Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV cs hv hout hcfg
  · exact congrArg Real.exp (congrArg Neg.neg
      (mainActionLoc_corr g₁ g₂ h1 h2 Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV cs hv hout hcfg))

end Quiet

end Balaban.RootFSpine
