/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairDecBg
public import Balaban.Fluctuation.InteractionHatE
public import Balaban.Fluctuation.InteractionVBlock
public import Balaban.Fluctuation.InteractionFPart
public import Balaban.Fluctuation.Prop33Nu

/-!
# CrossCompose: the compositions of a term at two generating sets

The last input of the replacement of P3 pp. 78-79: a term of the step reads the decoupled
background field `φ` (on `Ω₁(𝔹_{k+1})`) and the fluctuation field `δφ` (on `Ω₁(𝔹_k)`) only through
their zero extensions `svec` at finitely many sites, and the two generating sets only through their
layers there.  So the composed field `ψ(𝔹_k(X), 𝔹_{k+1}; Θ)` (`composeField`) is the same for the
ambient `𝔹_{k+1}` and for `𝔹_{k+1}(Y)` at a site whose layers agree and whose read blocks carry the
same field, and the old-term functional `eTermFun`, the block energy `blockEnergyFun`, the site
functional `siteFun` and the block functional `nuBlockFun` take the same value at the two pairs.

* `layerIndex_cross'`, `svec_cross`, `zeroExt_cross`, `barField_eq_svec`: the reading maps;
* `composeField_cross`: the composed field (6.2);
* `d1Triple_cross`, `eTermFun_cross`: the old-term functional;
* `energyDensity_cross`, `blockEnergyFun_cross`, `siteFun_cross`, `nuDensity_cross`,
  `nuBlockFun_cross`: the other summands of the step.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix

section Read

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}

/-- The layer index agrees at every site whose layers agree (both are `0` off `Ω₁`). -/
theorem layerIndex_cross' {x : CTorus d L N₁ m₁ K}
    (hlx : ∀ n, 1 ≤ n → n ≤ K → (x ∈ H.layer n ↔ x ∈ H'.layer n)) :
    H'.layerIndex x = H.layerIndex x := by
  classical
  by_cases hx : x ∈ H.Ω 1
  · exact layerIndex_cross hx hlx
  · have hx' : x ∉ H'.Ω 1 := fun h => hx ((mem_Ω_one_cross hlx).2 h)
    have h1 : ¬ ∃ j, 1 ≤ j ∧ j ≤ K ∧ x ∈ H.layer j := fun ⟨j, hj1, hjK, hxj⟩ =>
      hx (H.layer_subset hj1 hjK hxj)
    have h2 : ¬ ∃ j, 1 ≤ j ∧ j ≤ K ∧ x ∈ H'.layer j := fun ⟨j, hj1, hjK, hxj⟩ =>
      hx' (H'.layer_subset hj1 hjK hxj)
    unfold GeneratingSet.layerIndex
    rw [dite_eq_right h1, dite_eq_right h2]

/-- **The zero extensions of two fields agree at a site** that lies in both `Ω₁` or in neither,
if the fields agree there. -/
theorem svec_cross {φ : H.Ω 1 × Fin N → ℂ} {φ' : H'.Ω 1 × Fin N → ℂ} {y : CTorus d L N₁ m₁ K}
    (hy : y ∈ H.Ω 1 ↔ y ∈ H'.Ω 1)
    (hφ : ∀ (h : y ∈ H.Ω 1) (h' : y ∈ H'.Ω 1) (i : Fin N), φ (⟨y, h⟩, i) = φ' (⟨y, h'⟩, i)) :
    svec H φ y = svec H' φ' y := by
  funext i
  by_cases h : y ∈ H.Ω 1
  · rw [svec_of_mem H φ ⟨y, h⟩ i, svec_of_mem H' φ' ⟨y, hy.1 h⟩ i]
    exact hφ h (hy.1 h) i
  · rw [svec_of_not_mem H φ h i, svec_of_not_mem H' φ' (fun h' => h (hy.2 h')) i]

/-- **The zero extensions of two potentials agree at a site** that lies in both `Ω₁` or in neither,
if the potentials agree there. -/
theorem zeroExt_cross {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} {y : CTorus d L N₁ m₁ K}
    (hy : y ∈ H.Ω 1 ↔ y ∈ H'.Ω 1)
    (hα : ∀ (h : y ∈ H.Ω 1) (h' : y ∈ H'.Ω 1), α ⟨y, h⟩ = α' ⟨y, h'⟩) :
    zeroExt (H.Ω 1) α y = zeroExt (H'.Ω 1) α' y := by
  by_cases h : y ∈ H.Ω 1
  · rw [zeroExt_mem' α h, zeroExt_mem' α' (hy.1 h)]
    exact hα h (hy.1 h)
  · rw [zeroExt_not_mem _ _ h, zeroExt_not_mem _ _ (fun h' => h (hy.2 h'))]

end Read

section Compose

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
variable {G₁ : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁} {G₂ : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂}

/-- The extension `φ̄` of a field by the data is `svec` on `Ω₁` and the data off `Ω₁`. -/
theorem barField_eq_svec (Ψ : CTorus d L N₁ m₁ K → Fin N → ℂ) (φ : G₁.Ω 1 × Fin N → ℂ)
    (x : CTorus d L N₁ m₁ K) (i : Fin N) :
    barField G₁ Ψ φ x i = if x ∈ G₁.Ω 1 then svec G₁ φ x i else Ψ x i := by
  classical
  unfold barField
  by_cases h : x ∈ G₁.Ω 1
  · rw [dite_eq_left h, ite_eq_left h, svec_of_mem G₁ φ ⟨x, h⟩ i]
  · rw [dite_eq_right h, ite_eq_right h]

variable (G) in
/-- **CrossCompose, the composed field (6.2).**  The composed fields `ψ(𝔹, 𝔹₁; Ψ)` and
`ψ(𝔹, 𝔹₂; Ψ)` agree at a site `x` where the layers of `𝔹₁` and `𝔹₂` agree, if the zero extensions
of `φ₁`, `φ₂` agree at `x` and on the blocks through `x` read by the block means (the block of `𝔹`
and that of `𝔹₁` through `x`). -/
theorem composeField_cross (a : ℕ → ℝ) {φ₁ : G₁.Ω 1 × Fin N → ℂ} {φ₂ : G₂.Ω 1 × Fin N → ℂ}
    (Ψ : CTorus d L N₁ m₁ K → Fin N → ℂ) {x : CTorus d L N₁ m₁ K} (i : Fin N)
    (hlx : ∀ n, 1 ≤ n → n ≤ K → (x ∈ G₁.layer n ↔ x ∈ G₂.layer n))
    (hφ : ∀ y : CTorus d L N₁ m₁ K,
      (y = x ∨ y ∈ G.blk (G.layerIndex x) x ∨ y ∈ G₁.blk (G₁.layerIndex x) x) →
        svec G₁ φ₁ y = svec G₂ φ₂ y) :
    composeField G G₂ a φ₂ Ψ x i = composeField G G₁ a φ₁ Ψ x i := by
  classical
  have hli : G₂.layerIndex x = G₁.layerIndex x := layerIndex_cross' hlx
  have hbG : ∀ n : ℕ, n = G.layerIndex x →
      blockMean G n (fun y => svec G₂ φ₂ y i) x = blockMean G n (fun y => svec G₁ φ₁ y i) x := by
    rintro n rfl
    unfold blockMean
    congr 1
    exact Finset.sum_congr rfl fun y hy => (congrFun (hφ y (Or.inr (Or.inl hy))) i).symm
  have hb1 : blockMean G₂ (G₂.layerIndex x) (fun y => svec G₂ φ₂ y i) x =
      blockMean G₁ (G₁.layerIndex x) (fun y => svec G₁ φ₁ y i) x := by
    rw [hli]
    unfold blockMean
    congr 1
    exact Finset.sum_congr rfl fun y hy => (congrFun (hφ y (Or.inr (Or.inr hy))) i).symm
  unfold composeField
  by_cases hx : x ∈ G.Ω 1
  · simp only [hx, ↓reduceIte]
    rw [hbG _ rfl, hb1, hli]
  · simp only [hx, ↓reduceIte]
    split_ifs
    · rw [barField_eq_svec, barField_eq_svec, hφ x (Or.inl rfl)]
      simp only [(mem_Ω_one_cross hlx).symm]
    · rfl

end Compose

section Terms

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' ϱ₁ ϱ₂ ϱm ϱm' : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gp' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {Hm' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm'}

/-- **CrossCompose, the composed datum of an old term.**  The raw data
`ψ(𝔹_k(X), 𝔹_{k+1}; Θ) + δψ(𝔹_k(X), 𝔹_k; ψ')` (`d1Triple`) at the pairs `(𝔹_{k+1}, 𝔹_k)` and
`(𝔹'_{k+1}, 𝔹'_k)` are equal if, at every data site `x` of `𝔹_k(X)`, the layers of `𝔹_{k+1}`,
`𝔹'_{k+1}` and of `𝔹_k`, `𝔹'_k` agree and the zero extensions of `φ`, `φ'` and of `δφ`, `δφ'` agree
at `x` and on the blocks through `x` read by `composeField`. -/
theorem d1Triple_cross (a : ℕ → ℝ) {φ : Gp.Ω 1 × Fin N → ℂ} {φ' : Gp'.Ω 1 × Fin N → ℂ}
    {δφ : Hm.Ω 1 × Fin N → ℂ} {δφ' : Hm'.Ω 1 × Fin N → ℂ}
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))
    (hp : ∀ x ∈ dataSites Gk,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ Gp.layer n ↔ x ∈ Gp'.layer n)) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ Gp.blk (Gp.layerIndex x) x) →
          svec Gp φ y = svec Gp' φ' y)
    (hm : ∀ x ∈ dataSites Gk,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ Hm.layer n ↔ x ∈ Hm'.layer n)) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ Hm.blk (Hm.layerIndex x) x) →
          svec Hm δφ y = svec Hm' δφ' y) :
    d1Triple Gp' Gk Hm' a φ' δφ' u = d1Triple Gp Gk Hm a φ δφ u := by
  unfold d1Triple
  congr 1
  funext x i
  by_cases hx : x ∈ dataSites Gk
  · rw [composeField_cross Gk a u.1.1 i (hp x hx).1 (hp x hx).2,
      composeField_cross Gk a u.2 i (hm x hx).1 (hm x hx).2]
  · rw [composeField_of_not_mem a _ _ hx, composeField_of_not_mem a _ _ hx,
      composeField_of_not_mem a _ _ hx, composeField_of_not_mem a _ _ hx]

/-- **CrossCompose, the old-term functional** `Φ_E(φ, δφ, (Θ, ψ')) = E(D2raw Fk (d1Triple …))`
takes the same value at the two pairs under the hypotheses of `d1Triple_cross`. -/
theorem eTermFun_cross (a : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {pa : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)} {pa' : (Gp'.Ω 1 × Fin N → ℂ) × (Gp'.Ω 1 → ℂ)}
    {δφ : Hm.Ω 1 × Fin N → ℂ} {δφ' : Hm'.Ω 1 × Fin N → ℂ}
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))
    (hp : ∀ x ∈ dataSites Gk,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ Gp.layer n ↔ x ∈ Gp'.layer n)) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ Gp.blk (Gp.layerIndex x) x) →
          svec Gp pa.1 y = svec Gp' pa'.1 y)
    (hm : ∀ x ∈ dataSites Gk,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ Hm.layer n ↔ x ∈ Hm'.layer n)) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ Hm.blk (Hm.layerIndex x) x) →
          svec Hm δφ y = svec Hm' δφ' y) :
    eTermFun Gp' Gk Gj Hm' a Fk E pa' δφ' u = eTermFun Gp Gk Gj Hm a Fk E pa δφ u := by
  unfold eTermFun
  rw [d1Triple_cross a u hp hm]

end Terms

section Summands

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' ϱm ϱm' : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gp' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {Hm' : GeneratingSet d L (N₁ * L ^ m₁) K ϱm'}

/-- **The energy density** at two pairs agrees at a site `x` that lies in both `Ω₁` of the
fluctuation generators or in neither, if the zero extensions of the fluctuation fields agree at
`x`, its right neighbours and the `n`-block through `x`, and those of the multipliers agree at
`x`. -/
theorem energyDensity_cross (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) {α : Gp.Ω 1 → ℂ} {α' : Gp'.Ω 1 → ℂ}
    {δφ : Hm.Ω 1 × Fin N → ℂ} {δφ' : Hm'.Ω 1 × Fin N → ℂ} (ψ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    {x : CTorus d L N₁ m₁ K} (hxm : x ∈ Hm.Ω 1 ↔ x ∈ Hm'.Ω 1)
    (hα : zeroExt (Gp.Ω 1) α x = zeroExt (Gp'.Ω 1) α' x)
    (hδ : ∀ y : CTorus d L N₁ m₁ K,
      (y = x ∨ (∃ μ : Fin d, y = x + Pi.single μ 1) ∨ y ∈ Hm.blk n x) →
        svec Hm δφ y = svec Hm' δφ' y) :
    energyDensity Gp' Hm' a ν n α' δφ' ψ x = energyDensity Gp Hm a ν n α δφ ψ x := by
  classical
  have hbm : ∀ i, blockMean Hm' n (fun y => svec Hm' δφ' y i) x =
      blockMean Hm n (fun y => svec Hm δφ y i) x := by
    intro i
    unfold blockMean
    congr 1
    exact Finset.sum_congr rfl fun y hy => (congrFun (hδ y (Or.inr (Or.inr hy))) i).symm
  have h0 : ∀ i, svec Hm' δφ' x i = svec Hm δφ x i := fun i => by rw [hδ x (Or.inl rfl)]
  have h1 : ∀ (μ : Fin d) i, svec Hm' δφ' (x + Pi.single μ 1) i =
      svec Hm δφ (x + Pi.single μ 1) i := fun μ i => by
    rw [hδ (x + Pi.single μ 1) (Or.inr (Or.inl ⟨μ, rfl⟩))]
  unfold energyDensity
  simp only [hbm, h0, h1, hα, hxm]

/-- **The block energy** `blockEnergyFun` at two pairs agrees under the hypotheses of
`energyDensity_cross` at every site of the block `B_{n+1}(z)`. -/
theorem blockEnergyFun_cross (a : ℕ → ℝ) (ν : ℝ) (n : ℕ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    {pa : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)} {pa' : (Gp'.Ω 1 × Fin N → ℂ) × (Gp'.Ω 1 → ℂ)}
    {δφ : Hm.Ω 1 × Fin N → ℂ} {δφ' : Hm'.Ω 1 × Fin N → ℂ}
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))
    (h : ∀ x ∈ blockSites d L N₁ m₁ K n z, (x ∈ Hm.Ω 1 ↔ x ∈ Hm'.Ω 1) ∧
      zeroExt (Gp.Ω 1) pa.2 x = zeroExt (Gp'.Ω 1) pa'.2 x ∧
      ∀ y : CTorus d L N₁ m₁ K,
        (y = x ∨ (∃ μ : Fin d, y = x + Pi.single μ 1) ∨ y ∈ Hm.blk n x) →
          svec Hm δφ y = svec Hm' δφ' y) :
    blockEnergyFun Gp' Hm' a ν n z pa' δφ' u = blockEnergyFun Gp Hm a ν n z pa δφ u := by
  unfold blockEnergyFun energyBlock
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨h1, h2, h3⟩ := h x hx
  exact energyDensity_cross a ν n u.2 h1 h2 h3

/-- **The site functional** `siteFun` at two pairs agrees when the zero extensions of the
fluctuation fields agree at the site. -/
theorem siteFun_cross (y : CTorus d L N₁ m₁ K) (i : Fin N)
    (pa : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) (pa' : (Gp'.Ω 1 × Fin N → ℂ) × (Gp'.Ω 1 → ℂ))
    {δφ : Hm.Ω 1 × Fin N → ℂ} {δφ' : Hm'.Ω 1 × Fin N → ℂ}
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))
    (h : svec Hm δφ y = svec Hm' δφ' y) :
    siteFun Gp' Hm' y i pa' δφ' u = siteFun Gp Hm y i pa δφ u := by
  unfold siteFun
  rw [h]

/-- **The density of `V_{ν,1}`** at two pairs agrees at a site where the zero extensions of the
fluctuation fields and of the background fields agree. -/
theorem nuDensity_cross {δφ : Hm.Ω 1 × Fin N → ℂ} {δφ' : Hm'.Ω 1 × Fin N → ℂ}
    {φ₁ : Gp.Ω 1 × Fin N → ℂ} {φ₁' : Gp'.Ω 1 × Fin N → ℂ}
    (hh : CTorus d L N₁ m₁ K → Fin N → ℂ) {x : CTorus d L N₁ m₁ K}
    (hδ : svec Hm δφ x = svec Hm' δφ' x) (hφ : svec Gp φ₁ x = svec Gp' φ₁' x) :
    nuDensity Gp' Hm' δφ' φ₁' hh x = nuDensity Gp Hm δφ φ₁ hh x := by
  unfold nuDensity
  rw [hδ, hφ]

/-- **The block functional of `V_{ν,1}`** at two pairs agrees when the zero extensions agree on
the block `B_{n+1}(z)`. -/
theorem nuBlockFun_cross (n : ℕ) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    {pa : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)} {pa' : (Gp'.Ω 1 × Fin N → ℂ) × (Gp'.Ω 1 → ℂ)}
    {δφ : Hm.Ω 1 × Fin N → ℂ} {δφ' : Hm'.Ω 1 × Fin N → ℂ}
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))
    (h : ∀ x ∈ blockSites d L N₁ m₁ K n z,
      svec Hm δφ x = svec Hm' δφ' x ∧ svec Gp pa.1 x = svec Gp' pa'.1 x) :
    nuBlockFun Gp' Hm' n z pa' δφ' u = nuBlockFun Gp Hm n z pa δφ u := by
  unfold nuBlockFun
  exact Finset.sum_congr rfl fun x hx => nuDensity_cross _ (h x hx).1 (h x hx).2

end Summands

end Balaban.Localization
