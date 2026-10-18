/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusSize
public import Balaban.LargeField.Background.TwoTorusBgPiece

/-!
# The local piece background reads only the box

`genAgree_genBoundaryLocal` and `bgLocPiece_twoTorus`: the conditional versions
`genAgree_genBoundaryLocal_of_size`, `bgLocPiece_twoTorus_of_size` with the room of the box
derived from the containment of `V` in the box (`size_of_V`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField

set_option linter.unusedSectionVars false

section Final

variable {d M1 c L k ω n1₁ n0₁ n1₂ n0₂ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0₁]
  [NeZero n1₁] [NeZero n0₂] [NeZero n1₂] {Rprev Rk : ℝ} {Zp₁ : Set (Torus d n1₁)}
  {Zp₂ : Set (Torus d n1₂)} {Z'₁ : Finset (Torus d n1₁)} {Z'₂ : Finset (Torus d n1₂)}

theorem size_of_V_of_hV {n1 : ℕ} [NeZero n1] {Z' : Finset (Torus d n1)} (hd : 0 < d)
    (hc : 14 ≤ c) (ρ : ℕ) {Zp : Set (Torus d n1)}
    (hZ' : Z' ∈ comps ω (finOf Zp)) {m' : ℕ} [NeZero m'] {cc : Fin d → ℤ}
    (hV : ∀ x ∈ (fineK1 M1 c n1 L k (nbhd 1 (thick ρ (Z' : Set (Torus d n1)))) : Finset _),
      InBox (M1 * (c * n1) * L ^ (k + 1)) m' cc (liftNear cc x)) :
    4 * (12 * (L ^ (k + 1) * M1) + (L ^ (k + 1) * (c * M1)) * (ρ + 1)) + 8 ≤
      M1 * (c * n1) * L ^ (k + 1) := by
  have h1 := size_of_V (L := L) (k := k) hd hc ρ hZ' hV
  have h2 := twelve_le_P1 (M1 := M1) (L := L) (k := k) hc
  nlinarith

/-- **The local boundary generating sets of two tori agree on a box**: the containment of `V` in
the box gives its room. -/
theorem genAgree_genBoundaryLocal (hd : 0 < d) (st₁ : RegionStep d L n0₁ n1₁ Rprev Rk)
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
      InBox (M1 * (c * n1₁) * L ^ (k + 1)) (M1 * (c * n1₂) * L ^ (k + 1)) cc (liftNear cc x)) :
    GenAgree (genBoundaryLocal M1 c n1₁ L k st₁ hc hn₁ hL hρ hω hZ₁ hZ'₁)
      (genBoundaryLocal M1 c n1₂ L k st₂ hc hn₂ hL hρ hω hZ₂ hZ'₂) cc :=
  genAgree_genBoundaryLocal_of_size st₁ st₂ hc hn₁ hn₂ hL hρ hmono hω hZ₁ hZ₂ hZ'₁ hZ'₂ cc hZc hKc
    hOc hV₁ hV₂ (size_of_V_of_hV hd hc _ hZ'₁ hV₁)
    (by
      have := size_of_V_of_hV (L := L) (k := k) hd hc ⌊Rk⌋₊ hZ'₂
        (fun x hx => (hV₂ x hx).symm)
      exact this)

/-- **Two-torus transport of the local piece background** (Definition II.2.7 (iv)): the local
background `bgLocPiece` of two tori agrees at corresponding sites, when the fine sets of `Z'`,
`Z_k ∩ Z'`, `Ω_{k+1} ∩ Z'` correspond, `V = (Z'^≈)^∼` lies in the box of both tori, and the
lifted data `ψ`, `ϑ` agree at the `k`-blocks, `(k+1)`-blocks of corresponding sites. -/
theorem bgLocPiece_twoTorus {N : ℕ} (hd : 0 < d) (st₁ : RegionStep d L n0₁ n1₁ Rprev Rk)
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
  exact bgLocPiece_twoTorus_of_size st₁ st₂ hc hn₁ hn₂ hL hρ hmono hω hZ₁ hZ₂ hZ'₁ hZ'₂ cc hZc hKc
    hOc hV₁ hV₂ (size_of_V_of_hV hd hc _ hZ'₁ hV₁)
    (by
      have := size_of_V_of_hV (L := L) (k := k) hd hc ⌊Rk⌋₊ hZ'₂
        (fun x hx => (hV₂ x hx).symm)
      exact this) a μ c₀ ψ₁ ϑ₁ ψ₂ ϑ₂ h hψ hϑ hw hw₁ hw₂ i

end Final

end Balaban.RootFSpine
