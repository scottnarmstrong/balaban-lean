/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusLocData
public import Balaban.LargeField.Background.TwoTorusCast
public import Balaban.LargeField.Background.TwoTorusQuietCubes

/-!
# The local generating set and its data on two tori, from the correspondence of histories

For corresponding localized histories of a component and corresponding variables, the local
generating sets `G^{Z'}_{k+1}` (`locGen`) of the two tori agree on the box and so do the data
`lift_{k,k+1}(ψ_k, ψ_{k+1})` (`locData`) of the local backgrounds of the main action and of the
indicator of the real domain.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField RegionHistory

section Loc

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {k0 K M N : ℕ} [NeZero M] [NeZero S.L] {k : ℕ}

/-- The fine sets of the components correspond, on the level torus. -/
theorem setCorr_levelZ {c M1 : ℕ} [NeZero c] [NeZero M1] (hM : M = c * M1)
    (Hl₁ : RegionHistory S n₁ R k0 K) (Hl₂ : RegionHistory S n₂ R k0 K)
    (hrem₁ : ∀ j, Hl₁.rem j = ∅) (hrem₂ : ∀ j, Hl₂.rem j = ∅) (hk : k + 1 ≤ K)
    (Zc₁ : Finset (Torus S.d (n₁ (k + 1)))) (Zc₂ : Finset (Torus S.d (n₂ (k + 1))))
    (hZc₁ : Zc₁ ∈ comps (S.omega (k + 1)) (Hl₁.F.Zp (k + 1)))
    (hZc₂ : Zc₂ ∈ comps (S.omega (k + 1)) (Hl₂.F.Zp (k + 1))) {cc : Fin S.d → ℤ}
    (hH : HistCorr cc (locHist Hl₁ M K (k + 1) Zc₁) (locHist Hl₂ M K (k + 1) Zc₂)) :
    SetCorr cc
      ((fineK1 M1 c (n₁ (k + 1)) S.L k (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) : Finset _) :
        Set (Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))))
      ((fineK1 M1 c (n₂ (k + 1)) S.L k (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) : Finset _) :
        Set (Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)))) := by
  have e₁ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₁) hM Hl₁.F.hnn hk
  have e₂ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₂) hM Hl₂.F.hnn hk
  subst hM
  rw [coe_fineK1_eq_preimage e₁, coe_fineK1_eq_preimage e₂]
  have := hH.Z_corr (k + 1)
  rw [locHist_Z_top Hl₁ hrem₁ Zc₁ hZc₁, locHist_Z_top Hl₂ hrem₂ Zc₂ hZc₂] at this
  exact setCorr_preimage_cast e₁ e₂ this

/-- The fine sets of `Z_k ∩ Z'` correspond, on the level torus. -/
theorem setCorr_levelK {c M1 : ℕ} [NeZero c] [NeZero M1] (hM : M = c * M1)
    (Hl₁ : RegionHistory S n₁ R k0 K) (Hl₂ : RegionHistory S n₂ R k0 K) (hk : k + 1 ≤ K)
    (Zc₁ : Finset (Torus S.d (n₁ (k + 1)))) (Zc₂ : Finset (Torus S.d (n₂ (k + 1))))
    {cc : Fin S.d → ℤ}
    (hH : HistCorr cc (locHist Hl₁ M K (k + 1) Zc₁) (locHist Hl₂ M K (k + 1) Zc₂)) :
    SetCorr cc
      (((fineK M1 c (n₁ (k + 1)) S.L k (n₁ k) (Hl₁.step k).Z : Finset _) :
          Set (Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1)))) ∩
        ((fineK1 M1 c (n₁ (k + 1)) S.L k (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) : Finset _) :
          Set (Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1)))))
      (((fineK M1 c (n₂ (k + 1)) S.L k (n₂ k) (Hl₂.step k).Z : Finset _) :
          Set (Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)))) ∩
        ((fineK1 M1 c (n₂ (k + 1)) S.L k (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) : Finset _) :
          Set (Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1))))) := by
  have e₁ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₁) hM Hl₁.F.hnn hk
  have e₂ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₂) hM Hl₂.F.hnn hk
  subst hM
  rw [coe_fineK1_eq_preimage e₁, coe_fineK1_eq_preimage e₂, coe_fineK_eq_preimage e₁,
    coe_fineK_eq_preimage e₂, ← Set.preimage_inter, ← Set.preimage_inter]
  exact setCorr_preimage_cast e₁ e₂ (hH.Z_corr k)

/-- The fine sets of `Ω_{k+1} ∩ Z'` correspond, on the level torus. -/
theorem setCorr_levelO {c M1 : ℕ} [NeZero c] [NeZero M1] (hM : M = c * M1)
    (Hl₁ : RegionHistory S n₁ R k0 K) (Hl₂ : RegionHistory S n₂ R k0 K) (hk : k + 1 ≤ K)
    (Zc₁ : Finset (Torus S.d (n₁ (k + 1)))) (Zc₂ : Finset (Torus S.d (n₂ (k + 1))))
    {cc : Fin S.d → ℤ}
    (hH : HistCorr cc (locHist Hl₁ M K (k + 1) Zc₁) (locHist Hl₂ M K (k + 1) Zc₂)) :
    SetCorr cc
      (((fineK1 M1 c (n₁ (k + 1)) S.L k (Hl₁.step k).Omega : Finset _) :
          Set (Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1)))) ∩
        ((fineK1 M1 c (n₁ (k + 1)) S.L k (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) : Finset _) :
          Set (Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1)))))
      (((fineK1 M1 c (n₂ (k + 1)) S.L k (Hl₂.step k).Omega : Finset _) :
          Set (Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)))) ∩
        ((fineK1 M1 c (n₂ (k + 1)) S.L k (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) : Finset _) :
          Set (Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1))))) := by
  have e₁ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₁) hM Hl₁.F.hnn hk
  have e₂ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₂) hM Hl₂.F.hnn hk
  subst hM
  rw [coe_fineK1_eq_preimage e₁, coe_fineK1_eq_preimage e₂, coe_fineK1_eq_preimage e₁,
    coe_fineK1_eq_preimage e₂, ← Set.preimage_inter, ← Set.preimage_inter]
  exact setCorr_preimage_cast e₁ e₂ (hH.Omega_corr k)

/-- **The local generating sets and the data of the local backgrounds agree on the box.** -/
theorem locGen_agree (g₁ : Geo S n₁ R M) (g₂ : Geo S n₂ R M) (h1 : g₂.M1 = g₁.M1)
    (h2 : g₂.c = g₁.c) (Hl₁ : RegionHistory S n₁ R k0 K) (Hl₂ : RegionHistory S n₂ R k0 K)
    (hrem₁ : ∀ j, Hl₁.rem j = ∅) (hrem₂ : ∀ j, Hl₂.rem j = ∅) (hk : k + 1 ≤ K)
    (Zc₁ : Finset (Torus S.d (n₁ (k + 1)))) (Zc₂ : Finset (Torus S.d (n₂ (k + 1))))
    (hZc₁ : Zc₁ ∈ comps (S.omega (k + 1)) (Hl₁.F.Zp (k + 1)))
    (hZc₂ : Zc₂ ∈ comps (S.omega (k + 1)) (Hl₂.F.Zp (k + 1))) {cc : Fin S.d → ℤ}
    (hH : HistCorr cc (locHist Hl₁ M K (k + 1) Zc₁) (locHist Hl₂ M K (k + 1) Zc₂))
    (hV : SetCorr cc (Vsites R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1))
      (Vsites R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)))
    (hv : EuclideanSpace ℝ (Fin N)) {o₁ : OutT N R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)}
    {o₂ : OutT N R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)}
    {x₁ : NewCfg N (locHist Hl₁ M K (k + 1) Zc₁) k} {x₂ : NewCfg N (locHist Hl₂ M K (k + 1) Zc₂) k}
    (hout : OutCorr cc (k + 1) o₁ o₂) (hcfg : CfgCorr cc x₁ x₂) :
    GenAgree (locGen g₁ Hl₁ k Zc₁ hZc₁ hk) (locGen g₂ Hl₂ k Zc₂ hZc₂ hk) cc ∧
      DataAgree (locGen g₁ Hl₁ k Zc₁ hZc₁ hk) (locGen g₂ Hl₂ k Zc₂ hZc₂ hk) cc
        (locData g₁ Hl₁ k Zc₁ hZc₁ hk o₁ x₁ hv) (locData g₂ Hl₂ k Zc₂ hZc₂ hk o₂ x₂ hv) := by
  obtain ⟨M1, c, neM1, nec, hM, hc, hRlow, hRmono⟩ := g₁
  obtain ⟨M1', c', neM1', nec', hM', hc', hRlow', hRmono'⟩ := g₂
  simp only at h1 h2 ⊢
  have h1' := h1.symm
  have h2' := h2.symm
  subst h1' h2'
  have hd : 0 < S.d := by have := Hl₁.F.ok.three_le_d; omega
  have hn₁ := Hl₁.F.hnn k (by omega)
  have hn₂ := Hl₂.F.hnn k (by omega)
  have e₁ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₁) hM Hl₁.F.hnn hk
  have e₂ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₂) hM Hl₂.F.hnn hk
  have hZcc := setCorr_levelZ hM Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH
  have hKcc := setCorr_levelK hM Hl₁ Hl₂ hk Zc₁ Zc₂ hH
  have hOcc := setCorr_levelO hM Hl₁ Hl₂ hk Zc₁ Zc₂ hH
  have hV₁ : ∀ x ∈ (fineK1 M1 c (n₁ (k + 1)) S.L k
        (nbhd 1 (thick ⌊R k⌋₊ (Zc₁ : Set (Torus S.d (n₁ (k + 1)))))) : Finset _),
      InBox (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1)) (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)) cc
        (liftNear cc x) := fun x hx =>
    (inBox_cast rfl e₂).2 (inBox_levelV Hl₁ hrem₁ hk hM Zc₁ hZc₁ hV.1 x hx)
  have hV₂ : ∀ x ∈ (fineK1 M1 c (n₂ (k + 1)) S.L k
        (nbhd 1 (thick ⌊R k⌋₊ (Zc₂ : Set (Torus S.d (n₂ (k + 1)))))) : Finset _),
      InBox (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1)) (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)) cc
        (liftNear cc x) := fun x hx =>
    (inBox_cast e₁ rfl).2 (inBox_levelV Hl₂ hrem₂ hk hM Zc₂ hZc₂
      (fun y hy => (hV.2.1 y hy).symm) x hx).symm
  let g : Geo S n₁ R M := ⟨M1, c, neM1, nec, hM, hc, hRlow, hRmono⟩
  let g' : Geo S n₂ R M := ⟨M1, c, neM1', nec', hM', hc', hRlow', hRmono'⟩
  have hρ := g.three_L_le_floor Hl₁ (k - 1)
  have hρk := g.three_L_le_floor Hl₁ k
  have hmono := hRmono k
  have hω := (Hl₁.F.stepGeom (by omega : k < K)).rad.omega_rho
  have h32₁ : 32 ≤ n₁ (k + 1) := room_of_V Hl₁ hrem₁ hk hM hc hρk Zc₁ hZc₁ hV.1
  have h32₂ : 32 ≤ n₂ (k + 1) :=
    room_of_V Hl₂ hrem₂ hk hM hc (g'.three_L_le_floor Hl₂ k) Zc₂ hZc₂ (fun y hy => (hV.2.1 y hy).symm)
  have hq₁ : ∀ j, j ≤ k + 1 → 4 ≤ M * n₁ K * S.L ^ (K - j) := fun j hj =>
    four_le_block Hl₁.F.hnn hk h32₁ hj
  have hq₂ : ∀ j, j ≤ k + 1 → 4 ≤ M * n₂ K * S.L ^ (K - j) := fun j hj =>
    four_le_block Hl₂.F.hnn hk h32₂ hj
  refine ⟨genAgree_genBoundaryLocal hd (Hl₁.step k) (Hl₂.step k) hc hn₁ hn₂
      Hl₁.F.ok.two_le_L hρ hmono hω (Omega_compl_subset_Zpre' k (Hl₁.step k) _ _)
      (Omega_compl_subset_Zpre' k (Hl₂.step k) _ _) hZc₁ hZc₂ cc hZcc hKcc hOcc hV₁ hV₂, ?_⟩
  refine dataAgree_locLift hd (Hl₁.step k) (Hl₂.step k) hc hn₁ hn₂ Hl₁.F.ok.two_le_L hρ hmono hω
    (Omega_compl_subset_Zpre' k (Hl₁.step k) _ _) (Omega_compl_subset_Zpre' k (Hl₂.step k) _ _)
    hZc₁ hZc₂ cc hZcc hKcc hOcc hV₁ hV₂ _ _ _ _ _ ?_ ?_
  · intro w hw i
    have hwf := (inBox_cast e₁ e₂).1 hw
    simp only [BlockCfg.toC, locLiftPsi]
    rw [blockCfgOf_zcast_block g, blockCfgOf_zcast_block g']
    have := subVarField_corr hH hcfg (fun p₁ p₂ h => newVars_iff p₁ p₂ h) (by omega : k ≤ K)
      (hq₁ k (by omega)) (hq₂ k (by omega))
      ((blkCorr_iff_ccorr (by omega : k ≤ K)).2 ⟨w, hwf, rfl, rfl⟩)
    rw [this]
  · intro w hw i
    have hwf := (inBox_cast e₁ e₂).1 hw
    simp only [BlockCfg.toC, locLiftTheta]
    rw [blockCfgOf_zcast_block g, blockCfgOf_zcast_block g']
    have := hout _ _ ((blkCorr_iff_ccorr hk).2 ⟨w, hwf, rfl, rfl⟩)
    rw [this]

open Classical in
/-- **The indicator of the real domains in the quiet kernel agrees on two tori.** -/
theorem factor_domain (g₁ : Geo S n₁ R M) (g₂ : Geo S n₂ R M) (h1 : g₂.M1 = g₁.M1)
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
    (if InUnionDomainR (locGen g₁ Hl₁ k Zc₁ hZc₁ hk) (bgC1 S.d S.L N) (cs.mu (k + 1))
        (locData g₁ Hl₁ k Zc₁ hZc₁ hk o₁ x₁ hv) ∧
      InUnionDomainR (locGen g₁ Hl₁ k Zc₁ hZc₁ hk) (bgC1 S.d S.L N) (cs.muBg (k + 1))
        (locData g₁ Hl₁ k Zc₁ hZc₁ hk o₁ x₁ hv) then (1 : ℝ) else 0) =
    (if InUnionDomainR (locGen g₂ Hl₂ k Zc₂ hZc₂ hk) (bgC1 S.d S.L N) (cs.mu (k + 1))
        (locData g₂ Hl₂ k Zc₂ hZc₂ hk o₂ x₂ hv) ∧
      InUnionDomainR (locGen g₂ Hl₂ k Zc₂ hZc₂ hk) (bgC1 S.d S.L N) (cs.muBg (k + 1))
        (locData g₂ Hl₂ k Zc₂ hZc₂ hk o₂ x₂ hv) then (1 : ℝ) else 0) := by
  obtain ⟨hA, hD⟩ := locGen_agree g₁ g₂ h1 h2 Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV hv
    hout hcfg
  have hN : ∀ {n : ℕ → ℕ} [∀ k, NeZero (n k)] (g : Geo S n R M), 2 ≤ g.M1 * (g.c * n (k + 1)) := by
    intro n _ g
    have h1 : 1 ≤ g.M1 := Nat.pos_of_ne_zero (NeZero.ne _)
    have h2 : 1 ≤ n (k + 1) := Nat.pos_of_ne_zero (NeZero.ne _)
    have := g.hc
    have := Nat.mul_le_mul h1 (Nat.mul_le_mul this h2)
    omega
  have e1 := hA.inUnionDomainR_iff (hN g₁) (hN g₂) hD (c₁ := bgC1 S.d S.L N) (ν := cs.mu (k + 1))
  have e2 := hA.inUnionDomainR_iff (hN g₁) (hN g₂) hD (c₁ := bgC1 S.d S.L N)
    (ν := cs.muBg (k + 1))
  exact if_congr (and_congr e1 e2) rfl rfl

end Loc

end Balaban.RootFSpine
