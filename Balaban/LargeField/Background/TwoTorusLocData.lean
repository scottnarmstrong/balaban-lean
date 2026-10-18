/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusBgPieceFinal

/-!
# The data of the local background on two tori

`dataAgree_locLift`: under the hypotheses of `bgLocPiece_twoTorus`, the data `lift_{k,k+1}(ψ, ϑ)`
of the local backgrounds of two tori (`liftMixed` on the generating sets `G^{Z'}_{k+1}`) agree on
the box (`DataAgree`); the generating sets agree (`genAgree_genBoundaryLocal`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField

set_option linter.unusedSectionVars false

section LocData

variable {d M1 c L k ω n1₁ n0₁ n1₂ n0₂ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0₁]
  [NeZero n1₁] [NeZero n0₂] [NeZero n1₂] {Rprev Rk : ℝ} {Zp₁ : Set (Torus d n1₁)}
  {Zp₂ : Set (Torus d n1₂)} {Z'₁ : Finset (Torus d n1₁)} {Z'₂ : Finset (Torus d n1₂)}

/-- **The data of the local backgrounds of two tori agree on the box.** -/
theorem dataAgree_locLift {N : ℕ} (hd : 0 < d) (st₁ : RegionStep d L n0₁ n1₁ Rprev Rk)
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
          (zcast (M1 * (c * n1₂) * L ^ (k + 1)) w)) i) :
    DataAgree (genBoundaryLocal M1 c n1₁ L k st₁ hc hn₁ hL hρ hω hZ₁ hZ'₁)
      (genBoundaryLocal M1 c n1₂ L k st₂ hc hn₂ hL hρ hω hZ₂ hZ'₂) cc
      (liftMixed (genBoundaryLocal M1 c n1₁ L k st₁ hc hn₁ hL hρ hω hZ₁ hZ'₁)
        ((isCubeUnion_fineK1 st₁.Omega).isBlockUnion (le_refl _))
        (genBoundaryLocal_top_subset st₁ hc hn₁ hL hρ hω hZ₁ hZ'₁) ψ₁ ϑ₁ h)
      (liftMixed (genBoundaryLocal M1 c n1₂ L k st₂ hc hn₂ hL hρ hω hZ₂ hZ'₂)
        ((isCubeUnion_fineK1 st₂.Omega).isBlockUnion (le_refl _))
        (genBoundaryLocal_top_subset st₂ hc hn₂ hL hρ hω hZ₂ hZ'₂) ψ₂ ϑ₂ h) := by
  have hA := genAgree_genBoundaryLocal hd st₁ st₂ hc hn₁ hn₂ hL hρ hmono hω hZ₁ hZ₂ hZ'₁ hZ'₂ cc
    hZc hKc hOc hV₁ hV₂
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
  exact dataAgree_liftMixed hA ((isCubeUnion_fineK1 st₁.Omega).isBlockUnion (le_refl _))
    ((isCubeUnion_fineK1 st₂.Omega).isBlockUnion (le_refl _))
    (genBoundaryLocal_top_subset st₁ hc hn₁ hL hρ hω hZ₁ hZ'₁)
    (genBoundaryLocal_top_subset st₂ hc hn₂ hL hρ hω hZ₂ hZ'₂) ψ₁ ϑ₁ ψ₂ ϑ₂ h hOm hψ hϑ

end LocData

end Balaban.RootFSpine
