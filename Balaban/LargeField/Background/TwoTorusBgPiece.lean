/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusBoundaryGen
public import Balaban.LargeField.Background.StepBackgrounds

/-!
# The local piece background on two tori

`bgLocPiece_twoTorus`: for two tori with components `Z'` whose fine sets, `Z_k ∩ Z'`,
`Ω_{k+1} ∩ Z'` correspond on a box that contains `V = (Z'^≈)^∼` (with room), and lifted data
`ψ`, `ϑ`, `h` that correspond at corresponding blocks, the local piece backgrounds `φ^loc_{k+1}`
(Definition II.2.7 (iv)) of the two tori agree at corresponding sites of `Ω₁`. The background reads
only the box: the generating set `G^{Z'}_{k+1}` agrees on the box (`genAgree_genBoundaryLocal`),
and so do the operator, the source and the spacing (`GenAgree.bgFieldC_eq`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField

set_option linter.unusedSectionVars false

section Own

variable {d M1 c n1 L k n0 : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} {ω : ℕ} {Zp : Set (Torus d n1)} {Z' : Finset (Torus d n1)}

/-- A data site is close to `Z'`. -/
theorem near_of_dataSite (st : RegionStep d L n0 n1 Rprev Rk) (hc : 14 ≤ c) (hn : n0 = L * n1)
    (hL : 2 ≤ L) (hρ : 3 * L ≤ ⌊Rprev⌋₊)
    (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω) (hZ : st.Omegaᶜ ⊆ Zp) (hZ' : Z' ∈ comps ω (finOf Zp))
    {w : Fin d → ℤ}
    (hw : zcast (M1 * (c * n1) * L ^ (k + 1)) w ∈
      dataSites (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ')) :
    w ∈ dilZ (L ^ (k + 1) * (c * M1)) (⌊Rk⌋₊ + 2)
      (pbZ (M1 * (c * n1) * L ^ (k + 1))
        ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
          Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))) := by
  have hBP := twelve_le_P1 (M1 := M1) (L := L) (k := k) hc
  have hRz : ((12 * (L ^ (k + 1) * M1) + (L ^ (k + 1) * (c * M1)) * (⌊Rk⌋₊ + 1) : ℕ) : ℤ) + 1 ≤
      ((L ^ (k + 1) * (c * M1) : ℕ) : ℤ) * ((⌊Rk⌋₊ + 2 : ℕ) : ℤ) := by
    have hBP' : ((12 * (L ^ (k + 1) * M1) : ℕ) : ℤ) + 2 ≤ ((L ^ (k + 1) * (c * M1) : ℕ) : ℤ) := by
      exact_mod_cast hBP
    push_cast at hBP' ⊢
    nlinarith
  rcases (mem_dataSites _).1 hw with hΩ | hcol
  · obtain ⟨z'', hz''Z, hz''d⟩ := near_of_Ω1 st hc hn hL hρ hω hZ hZ' hΩ
    refine mem_dilZ_of_close P1_pos cubeConst_zZ hz''Z (fun μ => ?_)
    have := hz''d μ
    linarith
  · obtain ⟨-, z, hz, hadj⟩ := (mem_collar _).1 hcol
    obtain ⟨μ₀, hμ | hμ⟩ := hadj
    · have hz' : zcast (M1 * (c * n1) * L ^ (k + 1)) (w - (Pi.single μ₀ 1 : Fin d → ℤ)) ∈
          (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ').Ω 1 := by
        rw [zcast_sub_single, hμ, add_sub_cancel_right]; exact hz
      obtain ⟨z'', hz''Z, hz''d⟩ := near_of_Ω1 st hc hn hL hρ hω hZ hZ' hz'
      refine mem_dilZ_of_close P1_pos cubeConst_zZ hz''Z (fun μ => ?_)
      have h1 := hz''d μ
      have h2 : |z'' μ - w μ| ≤ |z'' μ - (w - (Pi.single μ₀ 1 : Fin d → ℤ)) μ| + 1 := by
        have := abs_sub_le (z'' μ) ((w - (Pi.single μ₀ 1 : Fin d → ℤ)) μ) (w μ)
        have h3 : |(w - (Pi.single μ₀ 1 : Fin d → ℤ)) μ - w μ| ≤ 1 := by
          by_cases h : μ = μ₀
          · subst h; simp
          · simp [h]
        linarith
      linarith
    · have hz' : zcast (M1 * (c * n1) * L ^ (k + 1)) (w + (Pi.single μ₀ 1 : Fin d → ℤ)) ∈
          (genBoundaryLocal M1 c n1 L k st hc hn hL hρ hω hZ hZ').Ω 1 := by
        rw [zcast_add_single, ← hμ]; exact hz
      obtain ⟨z'', hz''Z, hz''d⟩ := near_of_Ω1 st hc hn hL hρ hω hZ hZ' hz'
      refine mem_dilZ_of_close P1_pos cubeConst_zZ hz''Z (fun μ => ?_)
      have h1 := hz''d μ
      have h2 : |z'' μ - w μ| ≤ |z'' μ - (w + (Pi.single μ₀ 1 : Fin d → ℤ)) μ| + 1 := by
        have := abs_sub_le (z'' μ) ((w + (Pi.single μ₀ 1 : Fin d → ℤ)) μ) (w μ)
        have h3 : |(w + (Pi.single μ₀ 1 : Fin d → ℤ)) μ - w μ| ≤ 1 := by
          by_cases h : μ = μ₀
          · subst h; simp
          · simp [h]
        linarith
      linarith

/-- Near `Z'`, `Ω_{k+1}` is the complement of `Z'` together with `Ω_{k+1} ∩ Z'`. -/
theorem mem_Om_iff_near (st : RegionStep d L n0 n1 Rprev Rk) (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω)
    (hZ : st.Omegaᶜ ⊆ Zp) (hZ' : Z' ∈ comps ω (finOf Zp)) {w : Fin d → ℤ}
    (hw : w ∈ dilZ (L ^ (k + 1) * (c * M1)) (⌊Rk⌋₊ + 2)
      (pbZ (M1 * (c * n1) * L ^ (k + 1))
        ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
          Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))))) :
    w ∈ pbZ (M1 * (c * n1) * L ^ (k + 1))
        ((fineK1 M1 c n1 L k st.Omega : Finset _) : Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))) ↔
      (w ∉ pbZ (M1 * (c * n1) * L ^ (k + 1))
        ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
          Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))) ∨
        w ∈ pbZ (M1 * (c * n1) * L ^ (k + 1))
          ((fineK1 M1 c n1 L k st.Omega : Finset _) :
            Set (Torus d (M1 * (c * n1) * L ^ (k + 1)))) ∩
        pbZ (M1 * (c * n1) * L ^ (k + 1))
          ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
            Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))) := by
  constructor
  · intro h
    by_cases hz : w ∈ pbZ (M1 * (c * n1) * L ^ (k + 1))
        ((fineK1 M1 c n1 L k (Z' : Set (Torus d n1)) : Finset _) :
          Set (Torus d (M1 * (c * n1) * L ^ (k + 1))))
    · exact Or.inr ⟨h, hz⟩
    · exact Or.inl hz
  · rintro (h | h)
    · exact mem_Omega_of_not_mem_near st hZ hZ' (D := ⌊Rk⌋₊ + 2) (by omega) hw h
    · exact h.1

end Own

theorem setCorr_pbZ_iff {d m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂] {c : Fin d → ℤ} {A₁ : Set (Torus d m₁)}
    {A₂ : Set (Torus d m₂)} (hA : SetCorr c A₁ A₂) {w : Fin d → ℤ} (hw : InBox m₁ m₂ c w) :
    w ∈ pbZ m₁ A₁ ↔ w ∈ pbZ m₂ A₂ :=
  hA.2.2 _ _ (by rw [hw.liftNear_zcast₁, hw.liftNear_zcast₂])

section Data

variable {d L N₁ N₂ k N : ℕ} [NeZero N₁] [NeZero N₂] [NeZero L] {ϱ₁ ϱ₂ : ℝ}

/-- **The mixed-lift data of two backgrounds agree on the box** when the generating sets agree,
`Ω_{k+1}` agrees on the data sites, and `ψ`, `ϑ` agree at the `k`-, `(k+1)`-blocks of corresponding
sites. -/
theorem dataAgree_liftMixed {G₁ : GeneratingSet d L N₁ (k + 1) ϱ₁}
    {G₂ : GeneratingSet d L N₂ (k + 1) ϱ₂} {cc : Fin d → ℤ} (hA : GenAgree G₁ G₂ cc)
    {Om₁ : Finset (Torus d (N₁ * L ^ (k + 1)))} {Om₂ : Finset (Torus d (N₂ * L ^ (k + 1)))}
    (hΩ₁ : IsBlockUnion L N₁ (k + 1) (k + 1) Om₁) (hΩ₂ : IsBlockUnion L N₂ (k + 1) (k + 1) Om₂)
    (ht₁ : G₁.Ω (k + 1) ⊆ Om₁) (ht₂ : G₂.Ω (k + 1) ⊆ Om₂)
    (ψ₁ : Torus d (N₁ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ₁ : Torus d (N₁ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ)
    (ψ₂ : Torus d (N₂ * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ₂ : Torus d (N₂ * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ)
    (hOm : ∀ w, InBox (N₁ * L ^ (k + 1)) (N₂ * L ^ (k + 1)) cc w →
      zcast (N₁ * L ^ (k + 1)) w ∈ dataSites G₁ →
        (zcast (N₁ * L ^ (k + 1)) w ∈ Om₁ ↔ zcast (N₂ * L ^ (k + 1)) w ∈ Om₂))
    (hψ : ∀ w, InBox (N₁ * L ^ (k + 1)) (N₂ * L ^ (k + 1)) cc w →
      ∀ i, ψ₁ (jBlock d L N₁ (k + 1) k (zcast (N₁ * L ^ (k + 1)) w)) i =
        ψ₂ (jBlock d L N₂ (k + 1) k (zcast (N₂ * L ^ (k + 1)) w)) i)
    (hϑ : ∀ w, InBox (N₁ * L ^ (k + 1)) (N₂ * L ^ (k + 1)) cc w →
      ∀ i, ϑ₁ (jBlock d L N₁ (k + 1) (k + 1) (zcast (N₁ * L ^ (k + 1)) w)) i =
        ϑ₂ (jBlock d L N₂ (k + 1) (k + 1) (zcast (N₂ * L ^ (k + 1)) w)) i) :
    DataAgree G₁ G₂ cc (liftMixed G₁ hΩ₁ ht₁ ψ₁ ϑ₁ h) (liftMixed G₂ hΩ₂ ht₂ ψ₂ ϑ₂ h) where
  psi w hw hdata i := by
    have hw1 : InBoxK 1 (N₁ * L ^ (k + 1)) (N₂ * L ^ (k + 1)) cc w := by
      have := hA.inBoxK1_of_dataSites hdata
      rwa [hw.liftNear_zcast₁] at this
    have hdata2 : zcast (N₂ * L ^ (k + 1)) w ∈ dataSites G₂ := (hA.dataSites_iff hw1).1 hdata
    rw [liftMixed_Ψ _ _ _ _ _ _ hdata, liftMixed_Ψ _ _ _ _ _ _ hdata2]
    unfold mixedLift
    by_cases h₁ : zcast (N₁ * L ^ (k + 1)) w ∈ Om₁
    · have h₂ := (hOm w hw hdata).1 h₁
      simp only [h₁, h₂, ↓reduceIte, blockLift]
      exact hϑ w hw i
    · have h₂ : zcast (N₂ * L ^ (k + 1)) w ∉ Om₂ := fun h' => h₁ ((hOm w hw hdata).2 h')
      simp only [h₁, h₂, ↓reduceIte, blockLift]
      exact hψ w hw i
  h w _ hmem i := by
    have hmem2 : zcast (N₂ * L ^ (k + 1)) w ∈ G₂.Ω 1 := by
      have := (hA.agree 1 le_rfl (by omega) w ‹_›).1 hmem
      exact this
    rw [liftMixed_h _ _ _ _ _ _ hmem, liftMixed_h _ _ _ _ _ _ hmem2]

end Data

section Final

variable {d M1 c L k ω n1₁ n0₁ n1₂ n0₂ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0₁]
  [NeZero n1₁] [NeZero n0₂] [NeZero n1₂] {Rprev Rk : ℝ} {Zp₁ : Set (Torus d n1₁)}
  {Zp₂ : Set (Torus d n1₂)} {Z'₁ : Finset (Torus d n1₁)} {Z'₂ : Finset (Torus d n1₂)}

/-- **Two-torus transport of the local piece background** (Definition II.2.7 (iv)): the local
background `bgLocPiece` of two tori agrees at corresponding sites, when the fine sets of `Z'`,
`Z_k ∩ Z'`, `Ω_{k+1} ∩ Z'` correspond, `V = (Z'^≈)^∼` lies in the box of both tori (with the room
`size`), and the lifted data `ψ`, `ϑ` agree at the `k`-blocks, `(k+1)`-blocks of corresponding
sites. -/
theorem bgLocPiece_twoTorus {N : ℕ} (st₁ : RegionStep d L n0₁ n1₁ Rprev Rk)
    (st₂ : RegionStep d L n0₂ n1₂ Rprev Rk) (hc : 14 ≤ c) (hn₁ : n0₁ = L * n1₁)
    (hn₂ : n0₂ = L * n1₂) (hL : 2 ≤ L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hmono : ⌊Rprev⌋₊ ≤ ⌊Rk⌋₊)
    (hω : 2 * ⌊Rk⌋₊ + L + 11 ≤ ω) (hZ₁ : st₁.Omegaᶜ ⊆ Zp₁) (hZ₂ : st₂.Omegaᶜ ⊆ Zp₂)
    (hZ'₁ : Z'₁ ∈ comps ω (finOf Zp₁)) (hZ'₂ : Z'₂ ∈ comps ω (finOf Zp₂)) (cc : Fin d → ℤ)
    (hZc : SetCorr cc
      ((fineK1 M1 c n1₁ L k (Z'₁ : Set (Torus d n1₁)) : Finset _) :
        Set (Torus d (M1 * (c * n1₁) * L ^ (k + 1))))
      ((fineK1 M1 c n1₂ L k (Z'₂ : Set (Torus d n1₂)) : Finset _) :
        Set (Torus d (M1 * (c * n1₂) * L ^ (k + 1)))))
    (hKc : SetCorr cc
      (((fineK M1 c n1₁ L k n0₁ st₁.Z : Finset _) : Set (Torus d (M1 * (c * n1₁) * L ^ (k + 1)))) ∩
        ((fineK1 M1 c n1₁ L k (Z'₁ : Set (Torus d n1₁)) : Finset _) :
          Set (Torus d (M1 * (c * n1₁) * L ^ (k + 1)))))
      (((fineK M1 c n1₂ L k n0₂ st₂.Z : Finset _) : Set (Torus d (M1 * (c * n1₂) * L ^ (k + 1)))) ∩
        ((fineK1 M1 c n1₂ L k (Z'₂ : Set (Torus d n1₂)) : Finset _) :
          Set (Torus d (M1 * (c * n1₂) * L ^ (k + 1))))))
    (hOc : SetCorr cc
      (((fineK1 M1 c n1₁ L k st₁.Omega : Finset _) : Set (Torus d (M1 * (c * n1₁) * L ^ (k + 1)))) ∩
        ((fineK1 M1 c n1₁ L k (Z'₁ : Set (Torus d n1₁)) : Finset _) :
          Set (Torus d (M1 * (c * n1₁) * L ^ (k + 1)))))
      (((fineK1 M1 c n1₂ L k st₂.Omega : Finset _) : Set (Torus d (M1 * (c * n1₂) * L ^ (k + 1)))) ∩
        ((fineK1 M1 c n1₂ L k (Z'₂ : Set (Torus d n1₂)) : Finset _) :
          Set (Torus d (M1 * (c * n1₂) * L ^ (k + 1))))))
    (hV₁ : ∀ x ∈ (fineK1 M1 c n1₁ L k (nbhd 1 (thick ⌊Rk⌋₊ (Z'₁ : Set (Torus d n1₁)))) : Finset _),
      InBox (M1 * (c * n1₁) * L ^ (k + 1)) (M1 * (c * n1₂) * L ^ (k + 1)) cc (liftNear cc x))
    (hV₂ : ∀ x ∈ (fineK1 M1 c n1₂ L k (nbhd 1 (thick ⌊Rk⌋₊ (Z'₂ : Set (Torus d n1₂)))) : Finset _),
      InBox (M1 * (c * n1₁) * L ^ (k + 1)) (M1 * (c * n1₂) * L ^ (k + 1)) cc (liftNear cc x))
    (hsize₁ : 4 * (12 * (L ^ (k + 1) * M1) + (L ^ (k + 1) * (c * M1)) * (⌊Rk⌋₊ + 1)) + 8 ≤
      M1 * (c * n1₁) * L ^ (k + 1))
    (hsize₂ : 4 * (12 * (L ^ (k + 1) * M1) + (L ^ (k + 1) * (c * M1)) * (⌊Rk⌋₊ + 1)) + 8 ≤
      M1 * (c * n1₂) * L ^ (k + 1))
    (a : ℕ → ℝ) (μ c₀ : ℝ)
    (ψ₁ : Torus d (M1 * (c * n1₁) * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ₁ : Torus d (M1 * (c * n1₁) * L ^ (k + 1 - (k + 1))) → Fin N → ℂ)
    (ψ₂ : Torus d (M1 * (c * n1₂) * L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ₂ : Torus d (M1 * (c * n1₂) * L ^ (k + 1 - (k + 1))) → Fin N → ℂ) (h : Fin N → ℂ)
    (hψ : ∀ w, InBox (M1 * (c * n1₁) * L ^ (k + 1)) (M1 * (c * n1₂) * L ^ (k + 1)) cc w →
      ∀ i, ψ₁ (jBlock d L (M1 * (c * n1₁)) (k + 1) k (zcast (M1 * (c * n1₁) * L ^ (k + 1)) w)) i =
        ψ₂ (jBlock d L (M1 * (c * n1₂)) (k + 1) k (zcast (M1 * (c * n1₂) * L ^ (k + 1)) w)) i)
    (hϑ : ∀ w, InBox (M1 * (c * n1₁) * L ^ (k + 1)) (M1 * (c * n1₂) * L ^ (k + 1)) cc w →
      ∀ i, ϑ₁ (jBlock d L (M1 * (c * n1₁)) (k + 1) (k + 1)
          (zcast (M1 * (c * n1₁) * L ^ (k + 1)) w)) i =
        ϑ₂ (jBlock d L (M1 * (c * n1₂)) (k + 1) (k + 1)
          (zcast (M1 * (c * n1₂) * L ^ (k + 1)) w)) i)
    {w : Fin d → ℤ} (hw : InBox (M1 * (c * n1₁) * L ^ (k + 1)) (M1 * (c * n1₂) * L ^ (k + 1)) cc w)
    (hw₁ : zcast (M1 * (c * n1₁) * L ^ (k + 1)) w ∈
      (genBoundaryLocal M1 c n1₁ L k st₁ hc hn₁ hL hρ hω hZ₁ hZ'₁).Ω 1)
    (hw₂ : zcast (M1 * (c * n1₂) * L ^ (k + 1)) w ∈
      (genBoundaryLocal M1 c n1₂ L k st₂ hc hn₂ hL hρ hω hZ₂ hZ'₂).Ω 1) (i : Fin N) :
    bgLocPiece st₂ hc hn₂ hL hρ hω hZ₂ a μ c₀ hZ'₂ ψ₂ ϑ₂ h
        (⟨zcast (M1 * (c * n1₂) * L ^ (k + 1)) w, hw₂⟩, i) =
      bgLocPiece st₁ hc hn₁ hL hρ hω hZ₁ a μ c₀ hZ'₁ ψ₁ ϑ₁ h
        (⟨zcast (M1 * (c * n1₁) * L ^ (k + 1)) w, hw₁⟩, i) := by
  have hA := genAgree_genBoundaryLocal st₁ st₂ hc hn₁ hn₂ hL hρ hmono hω hZ₁ hZ₂ hZ'₁ hZ'₂ cc hZc
    hKc hOc hV₁ hV₂ hsize₁ hsize₂
  have hM1 : 0 < M1 := Nat.pos_of_ne_zero (NeZero.ne M1)
  have hN₁ : 2 ≤ M1 * (c * n1₁) := by
    have : 0 < n1₁ := Nat.pos_of_ne_zero (NeZero.ne n1₁)
    calc 2 ≤ c := by omega
      _ = 1 * (c * 1) := by ring
      _ ≤ M1 * (c * n1₁) := Nat.mul_le_mul hM1 (Nat.mul_le_mul le_rfl this)
  have hN₂ : 2 ≤ M1 * (c * n1₂) := by
    have : 0 < n1₂ := Nat.pos_of_ne_zero (NeZero.ne n1₂)
    calc 2 ≤ c := by omega
      _ = 1 * (c * 1) := by ring
      _ ≤ M1 * (c * n1₂) := Nat.mul_le_mul hM1 (Nat.mul_le_mul le_rfl this)
  have hOm : ∀ w, InBox (M1 * (c * n1₁) * L ^ (k + 1)) (M1 * (c * n1₂) * L ^ (k + 1)) cc w →
      zcast (M1 * (c * n1₁) * L ^ (k + 1)) w ∈
        dataSites (genBoundaryLocal M1 c n1₁ L k st₁ hc hn₁ hL hρ hω hZ₁ hZ'₁) →
        (zcast (M1 * (c * n1₁) * L ^ (k + 1)) w ∈ fineK1 M1 c n1₁ L k st₁.Omega ↔
          zcast (M1 * (c * n1₂) * L ^ (k + 1)) w ∈ fineK1 M1 c n1₂ L k st₂.Omega) := by
    intro w hw hdata
    have hw1 : InBoxK 1 (M1 * (c * n1₁) * L ^ (k + 1)) (M1 * (c * n1₂) * L ^ (k + 1)) cc w := by
      have := hA.inBoxK1_of_dataSites hdata
      rwa [hw.liftNear_zcast₁] at this
    have hdata2 := (hA.dataSites_iff hw1).1 hdata
    have om₁ := mem_Om_iff_near st₁ hω hZ₁ hZ'₁ (near_of_dataSite st₁ hc hn₁ hL hρ hω hZ₁ hZ'₁ hdata)
    have om₂ := mem_Om_iff_near st₂ hω hZ₂ hZ'₂ (near_of_dataSite st₂ hc hn₂ hL hρ hω hZ₂ hZ'₂ hdata2)
    have e1 := setCorr_pbZ_iff hZc hw
    have e2 := setCorr_pbZ_iff hOc hw
    have e3 : w ∈ pbZ (M1 * (c * n1₁) * L ^ (k + 1))
          ((fineK1 M1 c n1₁ L k st₁.Omega : Finset _) : Set _) ↔
        w ∈ pbZ (M1 * (c * n1₂) * L ^ (k + 1))
          ((fineK1 M1 c n1₂ L k st₂.Omega : Finset _) : Set _) := by
      rw [om₁, om₂]
      exact or_congr (not_congr e1) e2
    exact e3
  have hD := dataAgree_liftMixed hA ((isCubeUnion_fineK1 st₁.Omega).isBlockUnion (le_refl _))
    ((isCubeUnion_fineK1 st₂.Omega).isBlockUnion (le_refl _))
    (genBoundaryLocal_top_subset st₁ hc hn₁ hL hρ hω hZ₁ hZ'₁)
    (genBoundaryLocal_top_subset st₂ hc hn₂ hL hρ hω hZ₂ hZ'₂) ψ₁ ϑ₁ ψ₂ ϑ₂ h hOm hψ hϑ
  have hx₂ : hA.equiv ⟨zcast (M1 * (c * n1₁) * L ^ (k + 1)) w, hw₁⟩ =
      ⟨zcast (M1 * (c * n1₂) * L ^ (k + 1)) w, hw₂⟩ := by
    apply Subtype.ext
    rw [GenAgree.equiv_coe]
    simp only
    rw [hw.liftNear_zcast₁]
  have := hA.bgFieldC_eq hD hN₁ hN₂ a μ c₀ ⟨zcast (M1 * (c * n1₁) * L ^ (k + 1)) w, hw₁⟩ i
  rw [hx₂] at this
  exact this

end Final

end Balaban.RootFSpine
