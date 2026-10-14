/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairCompose

/-!
# The replacement identity of P3 pp. 78-79 for two pairs of generating sets (abstract form)

P3 pp. 78-79 replaces the ambient generating set `𝔹_{k+1}` by `𝔹_{k+1}(Y)` inside every term of
(4.45): the term computed with the decoupled background field of `(coverOf 𝔹_{k+1}, 𝔹_{k+1})` and
the fluctuation field of `(coverOf 𝔹_{k+1}, 𝔹_k)` equals the term computed with those of
`(coverOf 𝔹_{k+1}(Y), 𝔹_{k+1}(Y))` and `(coverOf 𝔹_{k+1}(Y), 𝔹_k(Y))`, when the cut parameters vanish
off the cubes inside `Y` and the data agree on `Y`.  Here this is proved for the old-term functional
`eTermFun` and any two quadruples `(𝔹, 𝔹⁻)`, `(𝔹', 𝔹'⁻)` (background and fluctuation generating sets
of the two sides) under explicit hypotheses: the component hypotheses of the background comparison
(`Dec2.decBg_value_cross`, sets `T_b ⊆ Y_b`) and of the fluctuation comparison
(`Dec2.decSol_value_cross`, sets `T_f ⊆ Y_f`, with `T_f ⊆ T_b` and the rows of `T_f` in `Y_b`), and
the reading hypotheses of the composition (`eTermFun_cross`) at the data sites of `𝔹_k(X)`.

* `composeField_congr_raw`, `d1Triple_congr_raw`, `eTermFun_congr_raw`: the old term only reads the
  raw datum at the data sites of `𝔹_k(X)`;
* `eTermFun_replacement_cross`: the replacement identity at one point `(s, s', D, D', ψ')`;
* `coef_eTermFun_replacement_cross`: the coefficient equality, from the identity at all parameters
  supported on `𝒞` in the polydisc (`coef_congr_near`).

The instance `𝔹' = 𝔹_{k+1}(Y) = localB (k + 1) … Y`, `𝔹'⁻ = 𝔹_k(Y)` requires the geometric
hypotheses at the local generator (the inner-cube and stencil conditions of
`LocalPairIndexMatch.lean`, `LocalPairCubeOps.lean` on a component at depth inside `Y`), the
membership of the restricted datum in the local union domain and the transport `τ` of the
parameters; these are not proved here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix

section Raw

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}

/-- The composed field reads the datum `Ψ'` only at the site itself. -/
theorem composeField_congr_raw {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    {G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (a : ℕ → ℝ) (φ' : G'.Ω 1 × Fin N → ℂ)
    {Ψ₁ Ψ₂ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {x : CTorus d L N₁ m₁ (k + 1)}
    (h : Ψ₁ x = Ψ₂ x) (i : Fin N) :
    composeField G G' a φ' Ψ₁ x i = composeField G G' a φ' Ψ₂ x i := by
  unfold composeField barField
  rw [h]

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

/-- `d1Triple` only reads the raw datum `(Θ, ψ')` at the data sites of `𝔹_k(X)` (and `h` on
`Ω₁(𝔹_k(X))`). -/
theorem d1Triple_congr_raw (a : ℕ → ℝ) (φ : Gp.Ω 1 × Fin N → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ)
    {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (hu : ∀ x ∈ dataSites Gk, u.1.1 x = u'.1.1 x ∧ (x ∈ Gk.Ω 1 → u.1.2 x = u'.1.2 x) ∧
      u.2 x = u'.2 x) :
    d1Triple Gp Gk Hm a φ δφ u = d1Triple Gp Gk Hm a φ δφ u' := by
  classical
  unfold d1Triple
  refine Prod.ext ?_ ?_
  · funext x i
    simp only
    by_cases hx : x ∈ dataSites Gk
    · rw [composeField_congr_raw a φ (hu x hx).1 i,
        composeField_congr_raw a δφ (hu x hx).2.2 i]
    · rw [composeField_of_not_mem a _ _ hx, composeField_of_not_mem a _ _ hx,
        composeField_of_not_mem a _ _ hx, composeField_of_not_mem a _ _ hx]
  · funext x i
    simp only
    by_cases hx : x ∈ Gk.Ω 1
    · have hxd : x ∈ dataSites Gk := (mem_dataSites Gk).2 (Or.inl hx)
      rw [ite_eq_left hx, ite_eq_left hx, (hu x hxd).2.1 hx]
    · rw [ite_eq_right hx, ite_eq_right hx]

theorem eTermFun_congr_raw (a : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (pa : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (δφ : Hm.Ω 1 × Fin N → ℂ)
    {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    (hu : ∀ x ∈ dataSites Gk, u.1.1 x = u'.1.1 x ∧ (x ∈ Gk.Ω 1 → u.1.2 x = u'.1.2 x) ∧
      u.2 x = u'.2 x) :
    eTermFun Gp Gk Gj Hm a Fk E pa δφ u = eTermFun Gp Gk Gj Hm a Fk E pa δφ u' := by
  unfold eTermFun
  rw [d1Triple_congr_raw a pa.1 δφ hu]

end Raw

section Replacement

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱl ϱm ϱh ϱ₁ ϱ₂ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {Hl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱh}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {a : ℕ → ℝ} {ν : ℝ}

/-- **The replacement identity (abstract form), at one point.**  Let `(𝔹, 𝔹⁻)` and `(𝔹', 𝔹'⁻)` be
the background and fluctuation generating sets of two sides, with the covers `coverOf 𝔹`,
`coverOf 𝔹'`; let `F₁`, `F₁'` (decoupled background fields) and `Sol`, `Sol'` (decoupled fluctuation
fields, mode P) be maps with the defining properties of the pairs.  At parameters
`|s_P|, |s'_P| < e^κ`, data `D`, `D'` in the union domains of Theorem I-4b and a fluctuation `ψ'` with
the fluctuation data in `StrictDataM` on both sides, suppose:

* the hypotheses of `Dec2.decBg_value_cross` for the background pairs, with sets `T_b ⊆ Y_b`;
* the hypotheses of `Dec2.decSol_value_cross` on the geometry for the fluctuation pairs, with sets
  `T_f ⊆ Y_f`, `T_f ⊆ T_b`, the rows `resSites` of `T_f` in `Y_b`, and `Ψ = Ψ'` on `Y_b`;
* at every data site `x` of `𝔹_k(X)`: the layers of `𝔹`, `𝔹'` and of `𝔹⁻`, `𝔹'⁻` agree at `x`, the
  sites read by `composeField` lie in `Y_b` (background) and `Y_f` (fluctuation), and the raw data
  agree at `x` (`h` on `Ω₁(𝔹_k(X))`).

Then the old-term functional `Φ_E` at the background field, the fluctuation field and `(Θ, ψ')`
takes the same value on the two sides. -/
theorem eTermFun_replacement_cross
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
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {s : Dec2.DecParams (coverOf Gp)} {s' : Dec2.DecParams (coverOf Gl)}
    (hs : ∀ P, ‖s P‖ < Real.exp κ) (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D : BgData Gp N} {D' : BgData Gl N}
    (hDd : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDd' : InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D')
    (ψ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (he : StrictDataM Hm N false δ₀ δ₁ (flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ'))
    (he' : StrictDataM Hl N false δ₀ δ₁ (flEdat Gl Hl (F₁' (s', rawOf D')) D'.Ψ ψ'))
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
    -- the composition
    (hcp : ∀ x ∈ dataSites Gk,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ Gp.layer n ↔ x ∈ Gl.layer n)) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ Gp.blk (Gp.layerIndex x) x) → y ∈ Yb)
    (hcm : ∀ x ∈ dataSites Gk,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ Hm.layer n ↔ x ∈ Hl.layer n)) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ Hm.blk (Hm.layerIndex x) x) → y ∈ Yf)
    (hdk : ∀ x ∈ dataSites Gk, D.Ψ x = D'.Ψ x ∧ (x ∈ Gk.Ω 1 → D.h x = D'.h x)) :
    eTermFun Gl Gk Gj Hl ac Fk E (F₁' (s', rawOf D'))
        (Sol' (s', flEdat Gl Hl (F₁' (s', rawOf D')) D'.Ψ ψ')).1 (rawOf D', ψ') =
      eTermFun Gp Gk Gj Hm ac Fk E (F₁ (s, rawOf D))
        (Sol (s, flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ')).1 (rawOf D, ψ') := by
  classical
  -- the background fields
  obtain ⟨hbα, hbφ⟩ := Dec2.decBg_value_cross hS Sb Sb' HB HB' hκ hM hF₁ hF₁' hs hs' hDd hDd'
    hTYb hYlayb hdichb hdichb' hrowb hrowb' hinb hinb' hresb hactb hdatb
  have hΩb : ∀ y ∈ Yb, (y ∈ Gp.Ω 1 ↔ y ∈ Gl.Ω 1) := fun y hy => mem_Ω_one_cross (hYlayb y hy)
  have hsvb : ∀ y ∈ Yb, svec Gp (F₁ (s, rawOf D)).1 y = svec Gl (F₁' (s', rawOf D')).1 y :=
    fun y hy => svec_cross (hΩb y hy) fun h h' i => (hbφ y h h' hy i).symm
  -- the data of the fluctuation problems
  have hα0 : ∀ (x : CTorus d L N₁ m₁ (k + 1)) (hx : x ∈ Hm.Ω 1) (hx' : x ∈ Hl.Ω 1), x ∈ Tf →
      (flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ').2.1 ⟨x, hx⟩ =
        (flEdat Gl Hl (F₁' (s', rawOf D')) D'.Ψ ψ').2.1 ⟨x, hx'⟩ := by
    intro x hx hx' hxT
    have hxb : x ∈ Tb := hTfb hxT
    have hΩx := hΩb x (hTYb hxb)
    simp only [flEdat, flAlpha]
    by_cases hp : x ∈ Gp.Ω 1
    · rw [dite_eq_left hp, dite_eq_left (hΩx.1 hp)]
      exact (hbα x hp (hΩx.1 hp) hxb).symm
    · rw [dite_eq_right hp, dite_eq_right (fun h => hp (hΩx.2 h))]
  have hφ0 : ∀ x ∈ Tf, x ∈ Hm.Ω 1 → ∀ y ∈ resSites Hm x,
      (flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ').1 y =
        (flEdat Gl Hl (F₁' (s', rawOf D')) D'.Ψ ψ').1 y := by
    intro x hxT hx y hy
    have hyb : y ∈ Yb := (hresf x hxT hx y hy).2.2
    simp only [flEdat]
    funext i
    rw [barField_eq_svec, barField_eq_svec, hsvb y hyb, hΨYb y hyb]
    simp only [(hΩb y hyb)]
  obtain ⟨-, hfφ⟩ := Dec2.decSol_value_cross hF₂ Sf Sf' hκ hM₂ false h0 h1 hδ₀ hδ₁ hSol hSol' hs
    hs' he he' hTYf hYΩf hdichf hdichf' hrowf hrowf' hinf hinf'
    (fun x hx hxΩ y hy => ⟨(hresf x hx hxΩ y hy).1, (hresf x hx hxΩ y hy).2.1⟩) hα0 hφ0
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
  have hsvf : ∀ y ∈ Yf,
      svec Hm (Sol (s, flEdat Gp Hm (F₁ (s, rawOf D)) D.Ψ ψ')).1 y =
        svec Hl (Sol' (s', flEdat Gl Hl (F₁' (s', rawOf D')) D'.Ψ ψ')).1 y :=
    fun y hy => svec_cross (hYΩf y hy) fun h h' i => (hfφ y h h' hy i).symm
  -- the composition
  rw [eTermFun_congr_raw (Gk := Gk) (Gj := Gj) ac Fk E _ _ (u := (rawOf D', ψ'))
    (u' := (rawOf D, ψ')) fun x hx => ⟨(hdk x hx).1.symm, fun h => ((hdk x hx).2 h).symm, rfl⟩]
  exact eTermFun_cross ac Fk E (rawOf D, ψ')
    (fun x hx => ⟨(hcp x hx).1, fun y hy => hsvb y ((hcp x hx).2 y hy)⟩)
    (fun x hx => ⟨(hcm x hx).1, fun y hy => hsvf y ((hcm x hx).2 y hy)⟩)

/-- **The coefficient equality.**  For a parameter index `ι`, maps `σ`, `τ` from the parameters
`w : ι → ℂ` to the cut parameters of the two sides (e.g. `extParams` and its transport) and a
fluctuation `ψ' w` depending on `w`, if the hypotheses of `eTermFun_replacement_cross` hold at
every `w` supported on `C` in the polydisc of radius `R > 1` (those depending on `w` are quantified),
then the coefficients `coef (·) C` of Lemma AE of the two terms are equal (`coef_congr_near`). -/
theorem coef_eTermFun_replacement_cross
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
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (C : Finset ι) {R : ℝ} (hR : 1 < R)
    (σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)) (τ : (ι → ℂ) → Dec2.DecParams (coverOf Gl))
    (hs : ∀ w ∈ supN C R, ∀ P, ‖σ w P‖ < Real.exp κ)
    (hs' : ∀ w ∈ supN C R, ∀ P, ‖τ w P‖ < Real.exp κ)
    {D : BgData Gp N} {D' : BgData Gl N}
    (hDd : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDd' : InUnionDomainC Gl (bgC0 d L N) (c7 d L N BG κ) ν D')
    (ψ' : (ι → ℂ) → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (he : ∀ w ∈ supN C R,
      StrictDataM Hm N false δ₀ δ₁ (flEdat Gp Hm (F₁ (σ w, rawOf D)) D.Ψ (ψ' w)))
    (he' : ∀ w ∈ supN C R,
      StrictDataM Hl N false δ₀ δ₁ (flEdat Gl Hl (F₁' (τ w, rawOf D')) D'.Ψ (ψ' w)))
    -- the background component
    {Yb Tb : Finset (CTorus d L N₁ m₁ (k + 1))} (hTYb : Tb ⊆ Yb)
    (hYlayb : ∀ y ∈ Yb, ∀ n, 1 ≤ n → n ≤ k + 1 → (y ∈ Gp.layer n ↔ y ∈ Gl.layer n))
    (hdichb : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
      SubI Gp (intBox q) Tb ∨ DisjI Gp (intBox q) Tb)
    (hdichb' : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) (τ w)) q ≠ 0 →
        SubI Gl (intBox q) Tb ∨ DisjI Gl (intBox q) Tb)
    (hrowb : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
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
    (hdichf : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
      SubI Hm (intBox q) Tf ∨ DisjI Hm (intBox q) Tf)
    (hdichf' : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gl).cubeIdx,
      (coverOf Gl).sProd (Dec2.extS (coverOf Gl) (τ w)) q ≠ 0 →
        SubI Hl (intBox q) Tf ∨ DisjI Hl (intBox q) Tf)
    (hrowf : ∀ w ∈ supN C R, ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
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
    -- the composition
    (hcp : ∀ x ∈ dataSites Gk,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ Gp.layer n ↔ x ∈ Gl.layer n)) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ Gp.blk (Gp.layerIndex x) x) → y ∈ Yb)
    (hcm : ∀ x ∈ dataSites Gk,
      (∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ Hm.layer n ↔ x ∈ Hl.layer n)) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ y ∈ Gk.blk (Gk.layerIndex x) x ∨ y ∈ Hm.blk (Hm.layerIndex x) x) → y ∈ Yf)
    (hdk : ∀ x ∈ dataSites Gk, D.Ψ x = D'.Ψ x ∧ (x ∈ Gk.Ω 1 → D.h x = D'.h x)) :
    coef (fun w => eTermFun Gp Gk Gj Hm ac Fk E (F₁ (σ w, rawOf D))
        (Sol (σ w, flEdat Gp Hm (F₁ (σ w, rawOf D)) D.Ψ (ψ' w))).1 (rawOf D, ψ' w)) C =
      coef (fun w => eTermFun Gl Gk Gj Hl ac Fk E (F₁' (τ w, rawOf D'))
        (Sol' (τ w, flEdat Gl Hl (F₁' (τ w, rawOf D')) D'.Ψ (ψ' w))).1 (rawOf D', ψ' w)) C :=
  coef_congr_near hR fun w hw => (eTermFun_replacement_cross hS Sb Sb' HB HB' hκ hM hF₁ hF₁' hF₂
    Sf Sf' hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E (hs w hw) (hs' w hw) hDd hDd' (ψ' w) (he w hw)
    (he' w hw) hTYb hYlayb (hdichb w hw) (hdichb' w hw) (hrowb w hw) (hrowb' w hw) (hinb w hw)
    (hinb' w hw) hresb hactb hdatb hΨYb hTYf hTfb hYΩf (hdichf w hw) (hdichf' w hw) (hrowf w hw)
    (hrowf' w hw) (hinf w hw) (hinf' w hw) hresf hcp hcm hdk).symm

end Replacement

end Balaban.Localization
