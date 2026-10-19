/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusMainAction

/-!
# The level torus near a component, on two tori

Transport of the correspondence of sites from the history torus to the level-`(k+1)` torus
(`ptCorr_torusCast`), the margin of the box and the neighbourhoods of the components for level
sites (`level_margin₁`, `level_margin₂`, `level_cube_iff`), and the set `X_{Z'}` of fine sites of
the main action (`mem_Xfine`, `xfine_iff`, `xfine_margin₁`, `xfine_margin₂`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField RegionHistory

section Cast

variable {d : ℕ} {c : Fin d → ℤ}

theorem ptCorr_torusCast {m₁ m₂ m₁' m₂' : ℕ} [NeZero m₁] [NeZero m₂] [NeZero m₁'] [NeZero m₂']
    (e₁ : m₁ = m₁') (e₂ : m₂ = m₂') {x₁ : Torus d m₁} {x₂ : Torus d m₂} (h : PtCorr c x₁ x₂) :
    PtCorr c (torusCast e₁ x₁) (torusCast e₂ x₂) := by
  subst e₁ e₂; exact h

end Cast

section Level

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {k0 K M N : ℕ} [NeZero M] [NeZero S.L] {k : ℕ} {cc : Fin S.d → ℤ} {M1 c : ℕ} [NeZero M1]
  [NeZero c] (hM : M = c * M1)
  (Hl₁ : RegionHistory S n₁ R k0 K) (Hl₂ : RegionHistory S n₂ R k0 K)
  (hrem₁ : ∀ j, Hl₁.rem j = ∅) (hrem₂ : ∀ j, Hl₂.rem j = ∅) (hk : k + 1 ≤ K)
  (Zc₁ : Finset (Torus S.d (n₁ (k + 1)))) (Zc₂ : Finset (Torus S.d (n₂ (k + 1))))
  (hZc₁ : Zc₁ ∈ comps (S.omega (k + 1)) (Hl₁.F.Zp (k + 1)))
  (hZc₂ : Zc₂ ∈ comps (S.omega (k + 1)) (Hl₂.F.Zp (k + 1)))
  (hH : HistCorr cc (locHist Hl₁ M K (k + 1) Zc₁) (locHist Hl₂ M K (k + 1) Zc₂))
  (hV : SetCorr cc (Vsites R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1))
    (Vsites R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)))
  (h32₁ : 32 ≤ n₁ (k + 1)) (h32₂ : 32 ≤ n₂ (k + 1))

include hM hrem₁ hk hZc₁ hV in
/-- The margin of the box at the level sites near `Zc₁`. -/
theorem level_margin₁ {r m : ℕ} (hr : r + m ≤ ⌊R k⌋₊ + 2) (hm : 4 * m ≤ n₁ (k + 1))
    (x : Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1)))
    (hx : blockMap (S.L ^ (k + 1) * M) (n₁ (k + 1)) x ∈ nbhd r (Zc₁ : Set (Torus S.d (n₁ (k + 1))))) :
    InBoxK (m * (S.L ^ (k + 1) * M)) (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))
      (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)) cc (liftNear cc x) := by
  have e₁ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₁) hM Hl₁.F.hnn hk
  have e₂ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₂) hM Hl₂.F.hnn hk
  have := margin₁ (M := M) (k := k) (cc := cc) Hl₁ Hl₂ hrem₁ hk Zc₁ Zc₂ hZc₁ hV hr hm
    (torusCast e₁ x) (by
      show blockMap (S.L ^ (k + 1) * M) (n₁ (k + 1)) (torusCast e₁ x) ∈ _
      rw [blockMap_torusCast]; exact hx)
  rw [liftNear_torusCast] at this
  exact (inBoxK_cast e₁ e₂).2 this

include hM hrem₂ hk hZc₂ hV in
/-- The margin of the box at the level sites near `Zc₂`. -/
theorem level_margin₂ {r m : ℕ} (hr : r + m ≤ ⌊R k⌋₊ + 2) (hm : 4 * m ≤ n₂ (k + 1))
    (x : Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)))
    (hx : blockMap (S.L ^ (k + 1) * M) (n₂ (k + 1)) x ∈ nbhd r (Zc₂ : Set (Torus S.d (n₂ (k + 1))))) :
    InBoxK (m * (S.L ^ (k + 1) * M)) (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))
      (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)) cc (liftNear cc x) := by
  have e₁ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₁) hM Hl₁.F.hnn hk
  have e₂ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₂) hM Hl₂.F.hnn hk
  have := margin₂ (M := M) (k := k) (cc := cc) Hl₁ Hl₂ hrem₂ hk Zc₁ Zc₂ hZc₂ hV hr hm
    (torusCast e₂ x) (by
      show blockMap (S.L ^ (k + 1) * M) (n₂ (k + 1)) (torusCast e₂ x) ∈ _
      rw [blockMap_torusCast]; exact hx)
  rw [liftNear_torusCast] at this
  exact (inBoxK_cast e₁ e₂).2 this

include hM hrem₁ hrem₂ hk hZc₁ hZc₂ hH hV h32₁ h32₂ in
/-- **Corresponding level sites are near corresponding components together.** -/
theorem level_cube_iff {r : ℕ} (hr : r ≤ 3) (hR6 : 6 ≤ ⌊R k⌋₊)
    {x₁ : Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))}
    {x₂ : Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1))} (hp : PtCorr cc x₁ x₂) :
    blockMap (S.L ^ (k + 1) * M) (n₁ (k + 1)) x₁ ∈ nbhd r (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) ↔
      blockMap (S.L ^ (k + 1) * M) (n₂ (k + 1)) x₂ ∈ nbhd r (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) := by
  have e₁ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₁) hM Hl₁.F.hnn hk
  have e₂ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₂) hM Hl₂.F.hnn hk
  have := cube_nbhd_iff Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hr hR6
    (ptCorr_torusCast e₁ e₂ hp)
  simpa only [cubeMap, blockMap_torusCast] using this

include hM hrem₁ hrem₂ hk hZc₁ hZc₂ hH in
/-- **The cube predicate of the layers of the generating set agrees at corresponding level
sites.** -/
theorem cubeOmega_iff (i : ℕ) {x₁ : Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))}
    {x₂ : Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1))} (hp : PtCorr cc x₁ x₂) :
    (blockMap (S.L ^ (k + 1) * M) (n₁ (k + 1)) x₁ ∉ (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) ∨
        blockMap (S.L ^ (i + 1) * M) (n₁ (i + 1)) x₁ ∈ (Hl₁.step i).Omega) ↔
      (blockMap (S.L ^ (k + 1) * M) (n₂ (k + 1)) x₂ ∉ (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) ∨
        blockMap (S.L ^ (i + 1) * M) (n₂ (i + 1)) x₂ ∈ (Hl₂.step i).Omega) := by
  have e₁ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₁) hM Hl₁.F.hnn hk
  have e₂ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₂) hM Hl₂.F.hnn hk
  have h1 := lhOmega_iff_cubes (M := M) Hl₁ hrem₁ Zc₁ hZc₁ (torusCast e₁ x₁) i
  have h2 := lhOmega_iff_cubes (M := M) Hl₂ hrem₂ Zc₂ hZc₂ (torusCast e₂ x₂) i
  have h3 := hH.lhOmega_iff (k + 1) (i + 1) (torusCast e₁ x₁) (torusCast e₂ x₂)
    (by rw [liftNear_torusCast, liftNear_torusCast]; exact hp.1)
  simp only [cubeMap, blockMap_torusCast] at h1 h2
  simp only [Finset.mem_coe]
  rw [← h1, ← h2]
  exact h3

include hM hrem₁ hrem₂ hk hZc₁ hZc₂ hH in
/-- The sites of the set `X_{Z'}` of the main action correspond. -/
theorem xfine_iff {X₁ : Finset (Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1)))}
    {X₂ : Finset (Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)))}
    (hX₁ : ∀ x, x ∈ X₁ ↔ x ∈ fineK1 M1 c (n₁ (k + 1)) S.L k (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) ∧
      x ∉ fineK M1 c (n₁ (k + 1)) S.L k (n₁ k) (Hl₁.step k).Z)
    (hX₂ : ∀ x, x ∈ X₂ ↔ x ∈ fineK1 M1 c (n₂ (k + 1)) S.L k (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) ∧
      x ∉ fineK M1 c (n₂ (k + 1)) S.L k (n₂ k) (Hl₂.step k).Z)
    {x₁ : Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))}
    {x₂ : Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1))} (hp : PtCorr cc x₁ x₂) :
    x₁ ∈ X₁ ↔ x₂ ∈ X₂ := by
  have hZ := (setCorr_levelZ hM Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH).2.2 x₁ x₂ hp.1
  have hK := (setCorr_levelK hM Hl₁ Hl₂ hk Zc₁ Zc₂ hH).2.2 x₁ x₂ hp.1
  simp only [Finset.mem_coe, Set.mem_inter_iff] at hZ hK
  rw [hX₁, hX₂]
  tauto

include hM hrem₁ hk hZc₁ hV in
/-- The sites of `X_{Z'}` of the first torus have the margin `2 L^{k+1} M`. -/
theorem xfine_margin₁ (h32₁ : 32 ≤ n₁ (k + 1)) {x : Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))}
    (hx : x ∈ fineK1 M1 c (n₁ (k + 1)) S.L k (Zc₁ : Set (Torus S.d (n₁ (k + 1))))) :
    InBoxK (2 * (S.L ^ (k + 1) * M)) (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))
      (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)) cc (liftNear cc x) := by
  refine level_margin₁ hM Hl₁ Hl₂ hrem₁ hk Zc₁ Zc₂ hZc₁ hV (r := 0) (m := 2) (by omega)
    (by omega) x (subset_nbhd _ _ ?_)
  have := mem_fineK1.1 hx
  rw [hM]; exact this

include hM hrem₂ hk hZc₂ hV in
/-- The sites of `X_{Z'}` of the second torus have the margin `2 L^{k+1} M`. -/
theorem xfine_margin₂ (h32₂ : 32 ≤ n₂ (k + 1)) {x : Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1))}
    (hx : x ∈ fineK1 M1 c (n₂ (k + 1)) S.L k (Zc₂ : Set (Torus S.d (n₂ (k + 1))))) :
    InBoxK (2 * (S.L ^ (k + 1) * M)) (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))
      (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)) cc (liftNear cc x) := by
  refine level_margin₂ hM Hl₁ Hl₂ hrem₂ hk Zc₁ Zc₂ hZc₂ hV (r := 0) (m := 2) (by omega)
    (by omega) x (subset_nbhd _ _ ?_)
  have := mem_fineK1.1 hx
  rw [hM]; exact this

include hM hrem₁ hrem₂ hk hZc₁ hZc₂ hH hV h32₁ h32₂ in
/-- **The layers of the level generating sets of the two histories correspond near the
components.** -/
theorem layer_iff (hL : 2 ≤ S.L) (hR₁ : ∀ j, 1 ≤ j → j < k + 1 → S.Rb ≤ R j)
    (hR₂ : ∀ j, 1 ≤ j → j < k + 1 → S.Rb ≤ R j)
    (hω₁ : 2 * ⌊R k⌋₊ + S.L + 11 ≤ S.omega (k + 1)) (hω₂ : 2 * ⌊R k⌋₊ + S.L + 11 ≤ S.omega (k + 1))
    (hR6 : 6 ≤ ⌊R k⌋₊) (e₁' : M * n₁ (k + 1) = M1 * (c * n₁ (k + 1)))
    (e₂' : M * n₂ (k + 1) = M1 * (c * n₂ (k + 1))) {m : ℕ} (hm : 1 ≤ m)
    {x₁ : Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))}
    {x₂ : Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1))} (hp : PtCorr cc x₁ x₂)
    (hx : blockMap (S.L ^ (k + 1) * M) (n₁ (k + 1)) x₁ ∈
      nbhd 0 (Zc₁ : Set (Torus S.d (n₁ (k + 1))))) :
    x₁ ∈ (castGen e₁' (Hl₁.histGen (M := M) (K' := k + 1) hk hrem₁ hL hR₁)).layer m ↔
      x₂ ∈ (castGen e₂' (Hl₂.histGen (M := M) (K' := k + 1) hk hrem₂ hL hR₂)).layer m := by
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  have hx₂ := (level_cube_iff hM Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂
    (r := 0) (by omega) hR6 hp).1 hx
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer,
    castHistGen_mem_near Hl₁ hrem₁ hk hL hR₁ e₁' Zc₁ hZc₁ hω₁ (r := 0) (by omega) x₁ hx i,
    castHistGen_mem_near Hl₁ hrem₁ hk hL hR₁ e₁' Zc₁ hZc₁ hω₁ (r := 0) (by omega) x₁ hx (i + 1),
    castHistGen_mem_near Hl₂ hrem₂ hk hL hR₂ e₂' Zc₂ hZc₂ hω₂ (r := 0) (by omega) x₂ hx₂ i,
    castHistGen_mem_near Hl₂ hrem₂ hk hL hR₂ e₂' Zc₂ hZc₂ hω₂ (r := 0) (by omega) x₂ hx₂ (i + 1),
    cubeOmega_iff hM Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH i hp,
    cubeOmega_iff hM Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH (i + 1) hp]

end Level

section CastCorr

variable {d : ℕ} {c : Fin d → ℤ}

theorem ccorr_torusCast {ℓ₁ ℓ₂ ℓ₁' ℓ₂' P q₁ q₂ q₁' q₂' : ℕ} (eℓ₁ : ℓ₁ = ℓ₁') (eℓ₂ : ℓ₂ = ℓ₂')
    (eq₁ : q₁ = q₁') (eq₂ : q₂ = q₂') {y₁ : Torus d q₁} {y₂ : Torus d q₂}
    (h : CCorr c ℓ₁ ℓ₂ P q₁ q₂ y₁ y₂) :
    CCorr c ℓ₁' ℓ₂' P q₁' q₂' (torusCast eq₁ y₁) (torusCast eq₂ y₂) := by
  subst eℓ₁ eℓ₂ eq₁ eq₂; exact h

end CastCorr

section Psi

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {k0 K M N : ℕ} [NeZero M] [NeZero S.L] {k : ℕ} {cc : Fin S.d → ℤ} {M1 c : ℕ} [NeZero M1]
  [NeZero c] (hM : M = c * M1)
  (Hl₁ : RegionHistory S n₁ R k0 K) (Hl₂ : RegionHistory S n₂ R k0 K) (hk : k + 1 ≤ K)
  (Zc₁ : Finset (Torus S.d (n₁ (k + 1)))) (Zc₂ : Finset (Torus S.d (n₂ (k + 1))))
  (hH : HistCorr cc (locHist Hl₁ M K (k + 1) Zc₁) (locHist Hl₂ M K (k + 1) Zc₂))
  (h32₁ : 32 ≤ n₁ (k + 1)) (h32₂ : 32 ≤ n₂ (k + 1))
  {x₁ : NewCfg N (locHist Hl₁ M K (k + 1) Zc₁) k} {x₂ : NewCfg N (locHist Hl₂ M K (k + 1) Zc₂) k}
  {o₁ : OutT N R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)}
  {o₂ : OutT N R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)}
  (hout : OutCorr cc (k + 1) o₁ o₂) (hcfg : CfgCorr cc x₁ x₂)

omit [NeZero M1] [NeZero c] in
include hM hk hH h32₁ h32₂ hout hcfg in
/-- **The multiscale field agrees at corresponding blocks of the level torus.** -/
theorem psiLevel_corr {m : ℕ} (hm : m ≤ k + 1)
    {y₁ : Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1 - m))}
    {y₂ : Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1 - m))}
    (hy : CCorr cc (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1)) (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1))
      (S.L ^ m) _ _ y₁ y₂) :
    subMultiscaleField N (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)
        (Vblk R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)) x₁ o₁ m
        (torusCast (histScale_eq hM Hl₁.F.hnn hm hk) y₁) =
      subMultiscaleField N (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)
        (Vblk R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)) x₂ o₂ m
        (torusCast (histScale_eq hM Hl₂.F.hnn hm hk) y₂) := by
  have e₁ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₁) hM Hl₁.F.hnn hk
  have e₂ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₂) hM Hl₂.F.hnn hk
  refine subMultiscaleField_corr hH hcfg (fun p₁ p₂ h => newVars_iff p₁ p₂ h) hk
    (fun j hj => four_le_block Hl₁.F.hnn hk h32₁ hj)
    (fun j hj => four_le_block Hl₂.F.hnn hk h32₂ hj) hout m _ _
    ((blkCorr_iff_ccorr (by omega : m ≤ K)).2 ?_)
  exact ccorr_torusCast e₁ e₂ (histScale_eq hM Hl₁.F.hnn hm hk) (histScale_eq hM Hl₂.F.hnn hm hk) hy

end Psi


section Main

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {k0 K M N : ℕ} [NeZero M] [NeZero S.L] {k : ℕ}

/-- **The main action `𝒜_{k+1}(Z'; ψ)` of the quiet kernel agrees on two tori.** -/
theorem mainActionLoc_corr (g₁ : Geo S n₁ R M) (g₂ : Geo S n₂ R M) (h1 : g₂.M1 = g₁.M1)
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
    mainActionLoc g₁ Hl₁ k Zc₁ hZc₁ hk cs hrem₁ o₁ x₁ hv =
      mainActionLoc g₂ Hl₂ k Zc₂ hZc₂ hk cs hrem₂ o₂ x₂ hv := by
  obtain ⟨hA, hD⟩ := locGen_agree g₁ g₂ h1 h2 Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV hv
    hout hcfg
  obtain ⟨M1, c, neM1, nec, hM, hc, hRlow, hRmono⟩ := g₁
  obtain ⟨M1', c', neM1', nec', hM', hc', hRlow', hRmono'⟩ := g₂
  simp only at h1 h2 ⊢
  have h1' := h1.symm
  have h2' := h2.symm
  subst h1' h2'
  have hd : 0 < S.d := by have := Hl₁.F.ok.three_le_d; omega
  have e₁ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₁) hM Hl₁.F.hnn hk
  have e₂ := site_eq (c := c) (M1 := M1) (L := S.L) (q := k + 1) (n := n₂) hM Hl₂.F.hnn hk
  let g : Geo S n₁ R M := ⟨M1, c, neM1, nec, hM, hc, hRlow, hRmono⟩
  let g' : Geo S n₂ R M := ⟨M1, c, neM1', nec', hM', hc', hRlow', hRmono'⟩
  have hρk := g.three_L_le_floor Hl₁ k
  have hL : 2 ≤ S.L := Hl₁.F.ok.two_le_L
  have hR6 : 6 ≤ ⌊R k⌋₊ := by omega
  have hω₁ := (Hl₁.F.stepGeom (by omega : k < K)).rad.omega_rho
  have hω₂ := (Hl₂.F.stepGeom (by omega : k < K)).rad.omega_rho
  have h32₁ : 32 ≤ n₁ (k + 1) := room_of_V Hl₁ hrem₁ hk hM hc hρk Zc₁ hZc₁ hV.1
  have h32₂ : 32 ≤ n₂ (k + 1) :=
    room_of_V Hl₂ hrem₂ hk hM hc (g'.three_L_le_floor Hl₂ k) Zc₂ hZc₂ (fun y hy => (hV.2.1 y hy).symm)
  have hLpos : 0 < S.L := by omega
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne _)
  have hAM : 1 ≤ S.L ^ (k + 1) * M := Nat.mul_pos (pow_pos hLpos _) hMpos
  -- the set `X`
  have hX₁ : ∀ x, x ∈ Xfine g Hl₁ k Zc₁ ↔
      x ∈ fineK1 M1 c (n₁ (k + 1)) S.L k (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) ∧
        x ∉ fineK M1 c (n₁ (k + 1)) S.L k (n₁ k) (Hl₁.step k).Z := by
    intro x; simp only [Xfine, Finset.mem_sdiff]; exact Iff.rfl
  have hX₂ : ∀ x, x ∈ Xfine g' Hl₂ k Zc₂ ↔
      x ∈ fineK1 M1 c (n₂ (k + 1)) S.L k (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) ∧
        x ∉ fineK M1 c (n₂ (k + 1)) S.L k (n₂ k) (Hl₂.step k).Z := by
    intro x; simp only [Xfine, Finset.mem_sdiff]; exact Iff.rfl
  have hiffX : ∀ {s₁ : Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))}
      {s₂ : Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1))}, PtCorr cc s₁ s₂ →
      (s₁ ∈ Xfine g Hl₁ k Zc₁ ↔ s₂ ∈ Xfine g' Hl₂ k Zc₂) := fun hp =>
    xfine_iff hM Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hX₁ hX₂ hp
  have hm₁ : ∀ x ∈ Xfine g Hl₁ k Zc₁, InBoxK (2 * (S.L ^ (k + 1) * M))
      (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1)) (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)) cc
      (liftNear cc x) := fun x hx =>
    xfine_margin₁ hM Hl₁ Hl₂ hrem₁ hk Zc₁ Zc₂ hZc₁ hV h32₁ ((hX₁ x).1 hx).1
  have hm₂ : ∀ x ∈ Xfine g' Hl₂ k Zc₂, InBoxK (2 * (S.L ^ (k + 1) * M))
      (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1)) (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)) cc
      (liftNear cc x) := fun x hx =>
    xfine_margin₂ hM Hl₁ Hl₂ hrem₂ hk Zc₁ Zc₂ hZc₂ hV h32₂ ((hX₂ x).1 hx).1
  have hX2₁ : ∀ x ∈ Xfine g Hl₁ k Zc₁, InBoxK 2 (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))
      (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)) cc (liftNear cc x) := fun x hx =>
    (hm₁ x hx).mono (by omega)
  have hX2₂ : ∀ x ∈ Xfine g' Hl₂ k Zc₂, InBoxK 2 (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))
      (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)) cc (liftNear cc x) := fun x hx =>
    (hm₂ x hx).mono (by omega)
  -- the field
  have hN : ∀ {n : ℕ → ℕ} [∀ k, NeZero (n k)], 2 ≤ M1 * (c * n (k + 1)) := by
    intro n _
    have h1 : 1 ≤ M1 := Nat.pos_of_ne_zero (NeZero.ne _)
    have h2 : 1 ≤ n (k + 1) := Nat.pos_of_ne_zero (NeZero.ne _)
    have := Nat.mul_le_mul h1 (Nat.mul_le_mul hc h2)
    omega
  have hφ : ∀ {s₁ : Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))}
      {s₂ : Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1))}, PtCorr cc s₁ s₂ →
      locPhi g Hl₁ k Zc₁ hZc₁ hk cs o₁ x₁ hv s₁ = locPhi g' Hl₂ k Zc₂ hZc₂ hk cs o₂ x₂ hv s₂ := by
    intro s₁ s₂ hp
    have := hA.barVec_ptCorr hD hN hN cs.aw (cs.muBg (k + 1)) (bgC0 S.d S.L N) hp
    unfold locPhi
    congr 1
    funext i
    exact congrArg Complex.re (congrFun this i).symm
  have hiffX' : ∀ s₁ s₂, PtCorr cc s₁ s₂ → (s₁ ∈ Xfine g Hl₁ k Zc₁ ↔ s₂ ∈ Xfine g' Hl₂ k Zc₂) :=
    fun _ _ hp => hiffX hp
  have hφ' : ∀ s₁ s₂, PtCorr cc s₁ s₂ → locPhi g Hl₁ k Zc₁ hZc₁ hk cs o₁ x₁ hv s₁ =
      locPhi g' Hl₂ k Zc₂ hZc₂ hk cs o₂ x₂ hv s₂ := fun _ _ hp => hφ hp
  have hStar := starBondE_corr hX2₁ hX2₂ hiffX' hφ'
  have hAct : actionG (histGenLevel g Hl₁ k hk hrem₁) cs.aw (cs.muAct (k + 1)) hv
      (Xfine g Hl₁ k Zc₁) (psiLevel g Hl₁ k hk
        (subMultiscaleField N (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)
          (Vblk R (locHist Hl₁ M K (k + 1) Zc₁) (k + 1)) x₁ o₁))
      (locPhi g Hl₁ k Zc₁ hZc₁ hk cs o₁ x₁ hv) =
    actionG (histGenLevel g' Hl₂ k hk hrem₂) cs.aw (cs.muAct (k + 1)) hv
      (Xfine g' Hl₂ k Zc₂) (psiLevel g' Hl₂ k hk
        (subMultiscaleField N (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)
          (Vblk R (locHist Hl₂ M K (k + 1) Zc₂) (k + 1)) x₂ o₂))
      (locPhi g' Hl₂ k Zc₂ hZc₂ hk cs o₂ x₂ hv) := by
    unfold actionG
    rw [bondE_corr hX2₁ hX2₂ hiffX' hφ', sumNorm_corr hX2₁ hX2₂ hiffX' hφ' hv]
    congr 3
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmk⟩ := Finset.mem_Icc.1 hm
    have hP : 0 < S.L ^ m := pow_pos hLpos _
    have hℓ : ∀ N₁ : ℕ, N₁ * S.L ^ (k + 1) = S.L ^ m * (N₁ * S.L ^ (k + 1 - m)) := fun N₁ => by
      rw [show S.L ^ (k + 1) = S.L ^ m * S.L ^ (k + 1 - m) by rw [← pow_add]; congr 1; omega]
      ring
    have hq₁ : 4 ≤ M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1 - m) := by
      rw [histScale_eq hM Hl₁.F.hnn hmk hk]; exact four_le_block Hl₁.F.hnn hk h32₁ hmk
    have hq₂ : 4 ≤ M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1 - m) := by
      rw [histScale_eq hM Hl₂.F.hnn hmk hk]; exact four_le_block Hl₂.F.hnn hk h32₂ hmk
    have hm0 : m ≠ 0 := by omega
    have hl₁ : lam (histGenLevel g Hl₁ k hk hrem₁) m = (histGenLevel g Hl₁ k hk hrem₁).layer m := by
      simp only [lam, hm0, ↓reduceIte]
    have hl₂ : lam (histGenLevel g' Hl₂ k hk hrem₂) m = (histGenLevel g' Hl₂ k hk hrem₂).layer m := by
      simp only [lam, hm0, ↓reduceIte]
    have hB : S.L ^ m + 1 ≤ 2 * (S.L ^ (k + 1) * M) := by
      have := (Nat.pow_le_pow_right hLpos hmk).trans (Nat.le_mul_of_pos_right (S.L ^ (k + 1)) hMpos)
      omega
    have e₁' : M * n₁ (k + 1) = M1 * (c * n₁ (k + 1)) := by rw [hM]; ring
    have e₂' : M * n₂ (k + 1) = M1 * (c * n₂ (k + 1)) := by rw [hM]; ring
    have hnb : ∀ {s : Torus S.d (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))},
        s ∈ Xfine g Hl₁ k Zc₁ →
        blockMap (S.L ^ (k + 1) * M) (n₁ (k + 1)) s ∈ nbhd 0 (Zc₁ : Set (Torus S.d (n₁ (k + 1)))) :=
      fun hs => subset_nbhd _ _ (by rw [hM]; exact mem_fineK1.1 ((hX₁ _).1 hs).1)
    have hnb' : ∀ {s : Torus S.d (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1))},
        s ∈ Xfine g' Hl₂ k Zc₂ →
        blockMap (S.L ^ (k + 1) * M) (n₂ (k + 1)) s ∈ nbhd 0 (Zc₂ : Set (Torus S.d (n₂ (k + 1)))) :=
      fun hs => subset_nbhd _ _ (by rw [hM]; exact mem_fineK1.1 ((hX₂ _).1 hs).1)
    simp only [tBlocks]
    rw [hl₁, hl₂]
    refine sum_blocks (cc := cc) hP (hℓ _) (hℓ _) hq₁ hq₂ ?_ ?_ ?_ _ _ ?_
    · intro s hs
      exact (hm₁ s (Finset.mem_inter.1 hs).2).mono hB
    · intro s hs
      exact (hm₂ s (Finset.mem_inter.1 hs).2).mono hB
    · intro s₁ s₂ hp
      rw [Finset.mem_inter, Finset.mem_inter]
      constructor
      · rintro ⟨hl, hx⟩
        exact ⟨(layer_iff hM Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hL
          (fun j _ _ => hRlow j) (fun j _ _ => hRlow' j) hω₁ hω₂ hR6 e₁' e₂' hm1 hp (hnb hx)).1 hl,
          (hiffX hp).1 hx⟩
      · rintro ⟨hl, hx⟩
        have hx₁ := (hiffX hp).2 hx
        exact ⟨(layer_iff hM Hl₁ Hl₂ hrem₁ hrem₂ hk Zc₁ Zc₂ hZc₁ hZc₂ hH hV h32₁ h32₂ hL
          (fun j _ _ => hRlow j) (fun j _ _ => hRlow' j) hω₁ hω₂ hR6 e₁' e₂' hm1 hp (hnb hx₁)).2 hl,
          hx₁⟩
    · intro y₁ y₂ hy hex
      obtain ⟨x₀, hx₀, hx₀y⟩ := hex
      have hx₀m : InBoxK (S.L ^ m + 1) (M1 * (c * n₁ (k + 1)) * S.L ^ (k + 1))
          (M1 * (c * n₂ (k + 1)) * S.L ^ (k + 1)) cc (liftNear cc x₀) :=
        (hm₁ x₀ (Finset.mem_inter.1 hx₀).2).mono hB
      have hψ := psiLevel_corr hM Hl₁ Hl₂ hk Zc₁ Zc₂ hH h32₁ h32₂ hout hcfg hmk hy
      have hb := bavg_corr hP (hℓ _) (hℓ _) hq₁ hq₂ hy hx₀m hx₀y hφ'
      simp only [psiLevel, hmk, ↓reduceDIte, bavgL]
      rw [hψ, hb]
  unfold mainActionLoc
  rw [hAct, hStar]

end Main

end Balaban.RootFSpine
