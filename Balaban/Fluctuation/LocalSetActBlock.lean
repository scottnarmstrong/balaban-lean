/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairReplacement
import Mathlib.Tactic.Linarith

/-!
# The zero-source activity of a domain recomputed on a local generating set: the block energy

P6 §4.1, Lemma 4.1 (pp. 22-31): the localization expansion (4.24) of the interaction potential
(4.1) has terms `U(Y; ψ)` depending only on the fields restricted to the domain `Y`; P3 pp. 78-79
recompute each term with the generating set `𝔹_{k+1}(Y)`.  In the formalization the term of a
domain `Y` at zero source is (`zeroSourceActivity_common_fromTowerG_core`, clause of the direct
terms) `-β ∑_z [Y ∈ polyDom_z] rayTerm (∂³ evTerm_z(Y))`, where `evTerm_z(Y)` is the term of the
localization expansion of the block energy `blockEnergyFun … z` at the decoupled background and
fluctuation fields of the step.  This file proves the replacement identity for the block energy at
one point (`blockEnergyFun_replacement_cross_of_agree`): at two pairs of generating sets
`(𝔹, 𝔹⁻)`, `(𝔹', 𝔹'⁻)` (the step and a local generating set with its fluctuation set), with the
component hypotheses of the landed `fieldsCross_of_agree` and the block `B_{k+1}(z)` read inside the
components, the block energy takes the same value on the two sides (`blockEnergyFun_cross` with the
fields of `fieldsCross_of_agree` and the multipliers of `Dec2.decBg_value_cross`).

* `blockEnergyFun_congr_psi`: the block energy reads the fluctuation variable only on the block;
* `blockEnergyFun_replacement_cross_of_agree`: the replacement identity at one point, with two
  fluctuation variables agreeing on the rows of `T_f` and on the block;
* `coef_blockEnergyFun_replacement_cross`: the coefficient equality of Lemma AE (`coef_congr_near`),
  hence the equality of the terms `evTerm_z(Y)` of the localization expansions of the two block
  energies (sums of coefficients over the same connected families).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix

section Psi

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

/-- **The block energy reads the fluctuation variable only on the block** `B_{n+1}(z)`. -/
theorem blockEnergyFun_congr_psi (a : ℕ → ℝ) (ν : ℝ) (n : ℕ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) (pa : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (δφ : Hm.Ω 1 × Fin N → ℂ)
    {u u' : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (h : ∀ x ∈ blockSites d L N₁ m₁ K n z, u.2 x = u'.2 x) :
    blockEnergyFun Gp Hm a ν n z pa δφ u = blockEnergyFun Gp Hm a ν n z pa δφ u' := by
  unfold blockEnergyFun energyBlock
  refine Finset.sum_congr rfl fun x hx => ?_
  unfold energyDensity
  rw [h x hx]

end Psi

section Cross

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl ϱm ϱh : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {Hl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱh}
variable {a : ℕ → ℝ} {ν : ℝ}

/-- **The replacement identity for the block energy at one point.**  Under the component
hypotheses of `fieldsCross_of_agree` for the background pairs `(coverOf 𝔹, 𝔹)`, `(coverOf 𝔹', 𝔹')`
(sets `T_b ⊆ Y_b`) and the fluctuation pairs `(coverOf 𝔹, 𝔹⁻)`, `(coverOf 𝔹', 𝔹'⁻)` (sets
`T_f ⊆ Y_f`), if every site `x` of the block `B_{n+1}(z)` lies in `T_b` and in `Ω₁` of both
fluctuation sets or of neither, its right neighbours and its `n`-block lie in `Y_f`, and the two
fluctuation variables agree on the block, then the block energy at the decoupled multiplier, the
fluctuation field and the fluctuation variable is the same on the two sides. -/
theorem blockEnergyFun_replacement_cross_of_agree
    {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gp) Gp a ν Kc Cx) (Sb' : Dec2.CoverBase (coverOf Gl) Gl a ν Kc Cx)
    (HB : BgHyp d L (k + 1) ϱ a ν) (HB' : BgHyp d L (k + 1) ϱl a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp a ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl a ν (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {Kc₂ Cx₂ c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L Kc₂ Cx₂ c₂ BG₂)
    (Sf : Dec2.CoverBase (coverOf Gp) Hm a ν Kc₂ Cx₂)
    (Sf' : Dec2.CoverBase (coverOf Gl) Hl a ν Kc₂ Cx₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf Gl) × Edat Hl N → (Hl.Ω 1 × Fin N → ℂ) × (Hl.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm a ν p.1) p.2.2.1 p.2.1
          (pertSource Hm a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm a ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm a ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf Gl) × Edat Hl N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hl N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi Hl (Dec2.decG (coverOf Gl) Hl a ν p.1) p.2.2.1 p.2.1
          (pertSource Hl a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf Gl) Hl a ν p.1 false p.2.2.1 p.2.1
          (pertSource Hl a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small Hl (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hl (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hl (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hl.Ω 1 → ℂ, Small Hl δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Hl a ν p.1 false p.2.2.1 p.2.1
            (pertSource Hl a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {s : Dec2.DecParams (coverOf Gp)} {s' : Dec2.DecParams (coverOf Gl)}
    (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D : BgData Gp N} {D' : BgData Gl N}
    (hDd : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDd' : InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D')
    (ψ₁ ψ₂ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (he : StrictDataM Hm N false δ₀ δ₁ (flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ₁))
    (he' : StrictDataM Hl N false δ₀ δ₁ (flEdat Gl Hl (F₁' (s', rawOf D')) D'.Ψ ψ₂))
    -- the background component
    {Yb Tb : Finset (CTorus d L N₁ m₁ (k + 1))} (hTYb : Tb ⊆ Yb)
    (hYlayb : ∀ y ∈ Yb, ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ Gp.layer n ↔ y ∈ Gl.layer n))
    (hdichb : ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
      SubI Gp (intBox q) Tb ∨ DisjI Gp (intBox q) Tb)
    (hdichb' : ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) s') q ≠ 0 →
        SubI Gl (intBox q) Tb ∨ DisjI Gl (intBox q) Tb)
    (hrowb : ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
      ∀ x ∈ Yb, x ∈ intBox q → x ∈ Tb)
    (hrowb' : ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) s') q ≠ 0 → ∀ x ∈ Yb, x ∈ intBox q → x ∈ Tb)
    (hinb : ∀ q ∈ Dec2.innerCentres (coverOf Gp) Gp Tb,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
        q ∈ Dec2.innerCentres (coverOf Gl) Gl Tb ∧
        (coverOf Gl).sProd (Dec2.extS (coverOf Gl) s') q =
          (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ∧
        (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ Gp.layer n ↔ y ∈ Gl.layer n)) ∧
        (∀ x ∈ intBox q, (coverOf Gp).chi q x = (coverOf Gl).chi q x))
    (hinb' : ∀ q ∈ Dec2.innerCentres (coverOf Gl) Gl Tb,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) s') q ≠ 0 →
        q ∈ Dec2.innerCentres (coverOf Gp) Gp Tb ∧
          (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0)
    (hresb : ∀ x ∈ Tb, x ∈ Gp.Ω 1 → ∀ y ∈ resSites Gp x, y ∈ Gp.Ω 1 ∧ y ∈ Yb)
    (hactb : ∀ y ∈ Yb, y ∈ Gp.Ω 1 → ∀ q : ℕ × CTorus d L N₁ m₁ (k + 1), 1 ≤ q.1 →
      q.1 ≤ k + 1 → bump q.1 q.2 y ≠ 0 →
        ∀ n, 1 ≤ n → n ≤ k + 1 → (q.2 ∈ Gp.layer n ↔ q.2 ∈ Gl.layer n))
    (hdatb : ∀ y ∈ Yb, y ∈ Gp.Ω 1 → ∀ z ∈ approxDep Gp y, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)
    (hΨYb : ∀ y ∈ Yb, D.Ψ y = D'.Ψ y)
    -- the fluctuation component
    {Yf Tf : Finset (CTorus d L N₁ m₁ (k + 1))} (hTYf : Tf ⊆ Yf) (hTfb : Tf ⊆ Tb)
    (hYΩf : ∀ x ∈ Yf, (x ∈ Hm.Ω 1 ↔ x ∈ Hl.Ω 1))
    (hdichf : ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
      SubI Hm (intBox q) Tf ∨ DisjI Hm (intBox q) Tf)
    (hdichf' : ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) s') q ≠ 0 →
        SubI Hl (intBox q) Tf ∨ DisjI Hl (intBox q) Tf)
    (hrowf : ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
      ∀ x ∈ Yf, x ∈ intBox q → x ∈ Tf)
    (hrowf' : ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) s') q ≠ 0 → ∀ x ∈ Yf, x ∈ intBox q → x ∈ Tf)
    (hinf : ∀ q ∈ Dec2.innerCentres (coverOf Gp) Hm Tf,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
        q ∈ Dec2.innerCentres (coverOf Gl) Hl Tf ∧
        (coverOf Gl).sProd (Dec2.extS (coverOf Gl) s') q =
          (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ∧
        (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ Hm.layer n ↔ y ∈ Hl.layer n)) ∧
        (∀ x ∈ intBox q, (coverOf Gp).chi q x = (coverOf Gl).chi q x))
    (hinf' : ∀ q ∈ Dec2.innerCentres (coverOf Gl) Hl Tf,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) s') q ≠ 0 →
        q ∈ Dec2.innerCentres (coverOf Gp) Hm Tf ∧
          (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0)
    (hresf : ∀ x ∈ Tf, x ∈ Hm.Ω 1 → ∀ y ∈ resSites Hm x,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ Hm.layer n ↔ y ∈ Hl.layer n)) ∧ (y ∈ Hm.Ω 1 → y ∈ Yf) ∧
        y ∈ Yb)
    (hψrow : ∀ x ∈ Tf, x ∈ Hm.Ω 1 → ∀ y ∈ resSites Hm x, ψ₁ y = ψ₂ y)
    (n : ℕ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (n + 1))))
    (Θ₁ Θ₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N)
    (hblk : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) n z, x ∈ Tb ∧ (x ∈ Hm.Ω 1 ↔ x ∈ Hl.Ω 1) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ (∃ μ : Fin d, y = x + Pi.single μ 1) ∨ y ∈ Hm.blk n x) → y ∈ Yf)
    (hψblk : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) n z, ψ₁ x = ψ₂ x) :
    blockEnergyFun Gl Hl a ν n z (F₁' (s', rawOf D'))
        (Sol' (s', flEdat Gl Hl (F₁' (s', rawOf D')) D'.Ψ ψ₂)).1 (Θ₂, ψ₂) =
      blockEnergyFun Gp Hm a ν n z (F₁ (s, rawOf D))
        (Sol (s, flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ₁)).1 (Θ₁, ψ₁) := by
  classical
  obtain ⟨-, hsvf⟩ := fieldsCross_of_agree hS Sb Sb' HB HB' hκ hM hF₁ hF₁' hF₂ Sf Sf' hM₂ h0 h1
    hδ₀ hδ₁ hSol hSol' hs hs' hDd hDd' ψ₁ ψ₂ he he' hTYb hYlayb hdichb hdichb' hrowb hrowb' hinb
    hinb' hresb hactb hdatb hΨYb hTYf hTfb hYΩf hdichf hdichf' hrowf hrowf' hinf hinf' hresf hψrow
  obtain ⟨hbα, -⟩ := Dec2.decBg_value_cross hS Sb Sb' HB HB' hκ hM hF₁ hF₁' hs hs' hDd hDd'
    hTYb hYlayb hdichb hdichb' hrowb hrowb' hinb hinb' hresb hactb hdatb
  rw [blockEnergyFun_congr_psi a ν n z _ _ (u := (Θ₂, ψ₂)) (u' := (Θ₁, ψ₂)) fun _ _ => rfl,
    blockEnergyFun_congr_psi a ν n z (F₁ (s, rawOf D)) _ (u := (Θ₁, ψ₁)) (u' := (Θ₁, ψ₂))
      fun x hx => hψblk x hx]
  refine blockEnergyFun_cross a ν n z (Θ₁, ψ₂) fun x hx => ?_
  obtain ⟨hxT, hxm, hxY⟩ := hblk x hx
  refine ⟨hxm, zeroExt_cross (mem_Ω_one_cross (hYlayb x (hTYb hxT))) fun h h' => ?_,
    fun y hy => hsvf y (hxY y hy)⟩
  exact (hbα x h h' hxT).symm

/-- **The coefficient equality for the block energy** (Lemma AE).  For parameters `w : ι → ℂ` with
maps `σ`, `τ` to the cut parameters of the two sides and fluctuation variables `ψ₁ w`, `ψ₂ w`
agreeing on the rows of `T_f` and on the block, if the hypotheses of
`blockEnergyFun_replacement_cross_of_agree` hold at every `w` supported on `C` in the polydisc of
radius `R > 1`, then the coefficients `coef (·) C` of the two block energies are equal. -/
theorem coef_blockEnergyFun_replacement_cross
    {Kc Cx c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gp) Gp a ν Kc Cx) (Sb' : Dec2.CoverBase (coverOf Gl) Gl a ν Kc Cx)
    (HB : BgHyp d L (k + 1) ϱ a ν) (HB' : BgHyp d L (k + 1) ϱl a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf Gl) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp a ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf Gl)) (D : BgData Gl N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gl) Gl a ν (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {Kc₂ Cx₂ c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L Kc₂ Cx₂ c₂ BG₂)
    (Sf : Dec2.CoverBase (coverOf Gp) Hm a ν Kc₂ Cx₂)
    (Sf' : Dec2.CoverBase (coverOf Gl) Hl a ν Kc₂ Cx₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf Gl) × Edat Hl N → (Hl.Ω 1 × Fin N → ℂ) × (Hl.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm a ν p.1) p.2.2.1 p.2.1
          (pertSource Hm a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm a ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm a ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf Gl) × Edat Hl N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hl N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi Hl (Dec2.decG (coverOf Gl) Hl a ν p.1) p.2.2.1 p.2.1
          (pertSource Hl a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf Gl) Hl a ν p.1 false p.2.2.1 p.2.1
          (pertSource Hl a p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small Hl (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hl (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hl (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hl.Ω 1 → ℂ, Small Hl δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl) Hl a ν p.1 false p.2.2.1 p.2.1
            (pertSource Hl a p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Finset ι) {R : ℝ} (hR : 1 < R)
    (σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)) (τ : (ι → ℂ) → Dec2.DecParams (coverOf Gl))
    (hs : ∀ w ∈ supN C R, ∀ P, ‖σ w P‖ < Real.exp κ)
    (hs' : ∀ w ∈ supN C R, ∀ P, ‖τ w P‖ < Real.exp κ)
    {D : BgData Gp N} {D' : BgData Gl N}
    (hDd : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDd' : InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D')
    (ψ₁ ψ₂ : (ι → ℂ) → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (he : ∀ w ∈ supN C R,
      StrictDataM Hm N false δ₀ δ₁ (flEdat Gp Hm (F₁ (σ w, rawOf D)) D.Ψ (ψ₁ w)))
    (he' : ∀ w ∈ supN C R,
      StrictDataM Hl N false δ₀ δ₁ (flEdat Gl Hl (F₁' (τ w, rawOf D')) D'.Ψ (ψ₂ w)))
    -- the background component
    {Yb Tb : Finset (CTorus d L N₁ m₁ (k + 1))} (hTYb : Tb ⊆ Yb)
    (hYlayb : ∀ y ∈ Yb, ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ Gp.layer n ↔ y ∈ Gl.layer n))
    (hdichb : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
      SubI Gp (intBox q) Tb ∨ DisjI Gp (intBox q) Tb)
    (hdichb' : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) (τ w)) q ≠ 0 →
        SubI Gl (intBox q) Tb ∨ DisjI Gl (intBox q) Tb)
    (hrowb : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
      ∀ x ∈ Yb, x ∈ intBox q → x ∈ Tb)
    (hrowb' : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) (τ w)) q ≠ 0 → ∀ x ∈ Yb, x ∈ intBox q → x ∈ Tb)
    (hinb : ∀ w ∈ supN C R, ∀ q ∈ Dec2.innerCentres (coverOf Gp) Gp Tb,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
        q ∈ Dec2.innerCentres (coverOf Gl) Gl Tb ∧
        (coverOf Gl).sProd (Dec2.extS (coverOf Gl) (τ w)) q =
          (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ∧
        (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ Gp.layer n ↔ y ∈ Gl.layer n)) ∧
        (∀ x ∈ intBox q, (coverOf Gp).chi q x = (coverOf Gl).chi q x))
    (hinb' : ∀ w ∈ supN C R, ∀ q ∈ Dec2.innerCentres (coverOf Gl) Gl Tb,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) (τ w)) q ≠ 0 →
        q ∈ Dec2.innerCentres (coverOf Gp) Gp Tb ∧
          (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0)
    (hresb : ∀ x ∈ Tb, x ∈ Gp.Ω 1 → ∀ y ∈ resSites Gp x, y ∈ Gp.Ω 1 ∧ y ∈ Yb)
    (hactb : ∀ y ∈ Yb, y ∈ Gp.Ω 1 → ∀ q : ℕ × CTorus d L N₁ m₁ (k + 1), 1 ≤ q.1 →
      q.1 ≤ k + 1 → bump q.1 q.2 y ≠ 0 →
        ∀ n, 1 ≤ n → n ≤ k + 1 → (q.2 ∈ Gp.layer n ↔ q.2 ∈ Gl.layer n))
    (hdatb : ∀ y ∈ Yb, y ∈ Gp.Ω 1 → ∀ z ∈ approxDep Gp y, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)
    (hΨYb : ∀ y ∈ Yb, D.Ψ y = D'.Ψ y)
    -- the fluctuation component
    {Yf Tf : Finset (CTorus d L N₁ m₁ (k + 1))} (hTYf : Tf ⊆ Yf) (hTfb : Tf ⊆ Tb)
    (hYΩf : ∀ x ∈ Yf, (x ∈ Hm.Ω 1 ↔ x ∈ Hl.Ω 1))
    (hdichf : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
      SubI Hm (intBox q) Tf ∨ DisjI Hm (intBox q) Tf)
    (hdichf' : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) (τ w)) q ≠ 0 →
        SubI Hl (intBox q) Tf ∨ DisjI Hl (intBox q) Tf)
    (hrowf : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
      ∀ x ∈ Yf, x ∈ intBox q → x ∈ Tf)
    (hrowf' : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) (τ w)) q ≠ 0 → ∀ x ∈ Yf, x ∈ intBox q → x ∈ Tf)
    (hinf : ∀ w ∈ supN C R, ∀ q ∈ Dec2.innerCentres (coverOf Gp) Hm Tf,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
        q ∈ Dec2.innerCentres (coverOf Gl) Hl Tf ∧
        (coverOf Gl).sProd (Dec2.extS (coverOf Gl) (τ w)) q =
          (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ∧
        (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ (k + 1),
          (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
            ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ Hm.layer n ↔ y ∈ Hl.layer n)) ∧
        (∀ x ∈ intBox q, (coverOf Gp).chi q x = (coverOf Gl).chi q x))
    (hinf' : ∀ w ∈ supN C R, ∀ q ∈ Dec2.innerCentres (coverOf Gl) Hl Tf,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) (τ w)) q ≠ 0 →
        q ∈ Dec2.innerCentres (coverOf Gp) Hm Tf ∧
          (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0)
    (hresf : ∀ x ∈ Tf, x ∈ Hm.Ω 1 → ∀ y ∈ resSites Hm x,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ Hm.layer n ↔ y ∈ Hl.layer n)) ∧ (y ∈ Hm.Ω 1 → y ∈ Yf) ∧
        y ∈ Yb)
    (n : ℕ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (n + 1))))
    (Θ₁ Θ₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N)
    (hblk : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) n z, x ∈ Tb ∧ (x ∈ Hm.Ω 1 ↔ x ∈ Hl.Ω 1) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ (∃ μ : Fin d, y = x + Pi.single μ 1) ∨ y ∈ Hm.blk n x) → y ∈ Yf)
    (hψrow : ∀ w ∈ supN C R, ∀ x ∈ Tf, x ∈ Hm.Ω 1 → ∀ y ∈ resSites Hm x, ψ₁ w y = ψ₂ w y)
    (hψblk : ∀ w ∈ supN C R, ∀ x ∈ blockSites d L N₁ m₁ (k + 1) n z, ψ₁ w x = ψ₂ w x) :
    coef (fun w => blockEnergyFun Gp Hm a ν n z (F₁ (σ w, rawOf D))
        (Sol (σ w, flEdat Gp Hm (F₁ (σ w, rawOf D)) D.Ψ (ψ₁ w))).1 (Θ₁, ψ₁ w)) C =
      coef (fun w => blockEnergyFun Gl Hl a ν n z (F₁' (τ w, rawOf D'))
        (Sol' (τ w, flEdat Gl Hl (F₁' (τ w, rawOf D')) D'.Ψ (ψ₂ w))).1 (Θ₂, ψ₂ w)) C :=
  coef_congr_near hR fun w hw => (blockEnergyFun_replacement_cross_of_agree hS Sb Sb' HB HB' hκ
    hM hF₁ hF₁' hF₂ Sf Sf' hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' (hs w hw) (hs' w hw) hDd hDd' (ψ₁ w)
    (ψ₂ w) (he w hw) (he' w hw) hTYb hYlayb (hdichb w hw) (hdichb' w hw) (hrowb w hw)
    (hrowb' w hw) (hinb w hw) (hinb' w hw) hresb hactb hdatb hΨYb hTYf hTfb hYΩf (hdichf w hw)
    (hdichf' w hw) (hrowf w hw) (hrowf' w hw) (hinf w hw) (hinf' w hw) hresf (hψrow w hw) n z
    Θ₁ Θ₂ hblk (hψblk w hw)).symm

end Cross

end Balaban.Localization
