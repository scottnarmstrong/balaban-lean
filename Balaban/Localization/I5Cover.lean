/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Fan
public import Balaban.Localization.SharpX0Distance
public import Balaban.Localization.Decoupled2Background
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The background part of Lemma DL in cover form (WIDEGEN route A)

The landed chain of Lemma DL (`composed_close_X0`, `i5_stage1`, `point_facts`) is stated for a
parent generating set `𝔹_{k+1}` with the standing hypotheses `DGSetting` (`ℓ¹` cover separation
`4 d L M₁ ≤ ϱ`) and the collar condition `r₀ M₁ ≤ ϱ - 1`.  Both fail for the literal local generator
`𝔹 = localB …` at the separation `5 L M₁` of P3 (4.4)-(4.6).  Here the same statements are proved
for the decoupled background field of the pair `(coverOf 𝔹, 𝔹)` (Theorem I-4b in cover form,
`Dec2.i4b_exists_unique`, `Dec2.i4b_one`, `Dec2.i4b_close`), from the cover base
`Dec2.CoverBase (coverOf 𝔹) 𝔹 …`, the sup-separation `SupSep`, cube alignment `CubeAligned` and the
target bound `T = ((r₀ - 4 d L³)/L) M₁ ≤ ϱ - 1` only.

* `Dec2.i4b_compose_close`: Theorem I-4b (v), closeness of the decoupled composition, for a cover
  (`composeField_sub_close` applied to `Dec2.i4b_close`);
* `composed_close_X0_sup`: the closeness of the composed datum on `X₀` for a sup-separated,
  cube-aligned parent (`le_composedCloseBound_of_dist` applied to `siteSetDist_X0_sup`);
* `i5_stage1_sup_of_one_le`: stage 1 of Lemma DL for such a parent (`i5_stage1_of_close` applied
  to `Dec2.i4b_one` and `composed_close_X0_sup`);
* `point_facts_sup_of_one_le`: the point facts of Lemma DL for such a parent
  (`point_facts_of_stage1` applied to `Dec2.i4b_exists_unique` and `i5_stage1_sup_of_one_le`).

The instance `𝔹_{k+1} = localB …` with the chart test of P3 (4.37) is
`Fluctuation/SharpChartTestSup.lean`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix

namespace Dec2

section Compose

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {C : DecCover d L N₁ m₁ K} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
  {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'} {a : ℕ → ℝ} {ν Kc Cx : ℝ}

/-- **Theorem I-4b (v) for a cover: closeness of the decoupled composition (P3 (2.60)).**  For the
decoupled background field of the pair `(C, 𝔹'_k)` the composed fields `ψ(𝔹_j, 𝔹'_k; s)` at `s`
and at `s ≡ 1` differ at `x` by at most `10 e^{2dγ_w} closeConst · e^{-γ_w d(x, W)}`, where `W`
contains the thickened interaction cubes of the cover cubes with `s_z ≠ 1`. -/
theorem i4b_compose_close {c BG : ℝ} (hS : DecSpecs d L Kc Cx c BG) (S : CoverBase C G' a ν Kc Cx)
    (HB : BgHyp d L K ϱ' a ν) (hP : Precedes G G') {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams C}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {W : Finset (CTorus d L N₁ m₁ K)}
    (hW : ∀ z ∈ C.cubeIdx, C.sProd (extS C s) z ≠ 1 → intBox z ⊆ W)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D' : BgData G' N}
    (hD : InDomainC G' ν δ ε D') {φ φ1 : G'.Ω 1 × Fin N → ℂ} {α α1 : G'.Ω 1 → ℂ}
    (h : IsDecBg C G' a ν (rho4 d L N BG κ) s D' φ α)
    (h1 : IsDecBg C G' a ν (rho4 d L N BG κ) (fun _ => 1) D' φ1 α1)
    (x : CTorus d L N₁ m₁ K) (i : Fin N) :
    ‖composeField G G' a φ D'.Ψ x i - composeField G G' a φ1 D'.Ψ x i‖ ≤
      10 * Real.exp (gammaW d * (2 * d)) *
        closeConst d L N BG κ (lemma53Const d L * δ) * decay (gammaW d) (siteSetDist G' W x) := by
  have hd0 : 0 < d := by have := HB.hd; omega
  obtain ⟨-, hval, -, -⟩ := i4b_close hS S HB hκ hM hs hW hδ0 hδε hε hδ hνε hD h h1
  have hcc := closeConst_nonneg (d := d) (L := L) (κ := κ) (N := N) hS.fam.2.1
    (mul_nonneg (lemma53Const_pos d L).le hδ0.le) hd0
  exact composeField_sub_close hP HB.weights (gammaW_nonneg hd0) hcc hval D'.Ψ x i

end Compose

end Dec2

section CloseX0

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
variable {a : ℕ → ℝ} {ν Kc Cx : ℝ}

/-- **Closeness of the composed datum on `X₀` for a sup-separated parent** (cover form of
`composed_close_X0`).  For the decoupled background field of the pair `(coverOf 𝔹, 𝔹)`, `𝔹`
sup-separated and cube aligned (`L ≥ 3`, `M₁ ≥ 4 L²`), with the parameters equal to `1` off the
parameter cubes of `X₁`, the physical `r₀ M₁ ℓ(x)`-collar of `X₀ ∩ Ω₁` inside `X₁`, `4 d L³ ≤ r₀`
and the target bound `T = ((r₀ - 4 d L³)/L) M₁ ≤ ϱ - 1`, the composed data at `s` and at `s ≡ 1`
differ on `X₀ ∩ Ω₁` by at most `composedCloseBound`.  No `ℓ¹` cover separation and no
`r₀ M₁ ≤ ϱ - 1` is assumed. -/
theorem composed_close_X0_sup {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf G) G a ν Kc Cx) (hG : CubeAligned G m₁) (hSS : SupSep G m₁)
    (hMM : 4 * L ^ 2 ≤ L ^ m₁) (HB : BgHyp d L K ϱ a ν) (hP : Precedes G' G) {κ : ℝ}
    (hκ : 0 ≤ κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : Dec2.DecParams (coverOf G)} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    {X₀ X₁ : Finset (CTorus d L N₁ m₁ K)} {r₀ : ℝ}
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ (coverOf G).cubeIdx),
      P ∉ (coverOf G).parCubes X₁ → s ⟨P, hP⟩ = 1)
    (hN : ∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * G.spacing x → y ∈ X₁)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData G N} (hD : InDomainC G ν δ ε D)
    {φ φ1 : G.Ω 1 × Fin N → ℂ} {α α1 : G.Ω 1 → ℂ}
    (h : Dec2.IsDecBg (coverOf G) G a ν (rho4 d L N BG κ) s D φ α)
    (h1 : Dec2.IsDecBg (coverOf G) G a ν (rho4 d L N BG κ) (fun _ => 1) D φ1 α1)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ X₀) (hxΩ : x ∈ G.Ω 1) (i : Fin N) :
    ‖composeField G' G a φ D.Ψ x i - composeField G' G a φ1 D.Ψ x i‖ ≤
      composedCloseBound d L N m₁ BG κ δ r₀ :=
  le_composedCloseBound_of_dist hS.fam.2.1 hδ0.le (by have := HB.hd; omega) hr₀
    ((siteSetDist_X0_sup hG hSS S.hL hMM (HB.green (G := G)).sep_gt_one.le hN hT hx hxΩ).trans
      (siteSetDist_Wpar_le_Wcover X₁ x))
    (Dec2.i4b_compose_close hS S HB hP hκ hM hs (hW_of_par_cover hs1) hδ0 hδε hε hδ hνε hD h h1
      x i)

end CloseX0

section Stages

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {a₁ ν Kc Cx : ℝ}

/-- **Stage 1 of Lemma DL for a sup-separated parent** (cover form of `i5_stage1_of_one_le`).  For
the decoupled background field of the pair `(coverOf 𝔹_{k+1}, 𝔹_{k+1})`, `𝔹_{k+1}` sup-separated
and cube aligned (no `DGSetting`), with the target bound `T = ((r₀ - 4 d L³)/L) M₁ ≤ ϱ - 1` in
place of `r₀ M₁ ≤ ϱ - 1`, the composed datum `ψ(𝔹_k(X), 𝔹_{k+1}; Θ, s)` lies in
`Ξ^c_K(𝔹_k(X); 1, b² ε' + K₂' δ₃)` (`1 ≤ b ≤ C₀`). -/
theorem i5_stage1_sup_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx) (hG : CubeAligned Gp m₁)
    (hSS : SupSep Gp m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) (HBk : BgHyp d L K ϱ₁ (compWeight L a₁) ν)
    (hP : Precedes Gk Gp) (hcol : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1) {κ r₀ eps δ₃ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃)
    {X₀ X₁ : Finset (CTorus d L N₁ m₁ K)} (hX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x → y ∈ X₁)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) {s : Dec2.DecParams (coverOf Gp)}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁ → s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D)
    {φ φ1 : Gp.Ω 1 × Fin N → ℂ} {α α1 : Gp.Ω 1 → ℂ}
    (h : Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α)
    (h1 : Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) (fun _ => 1) D
      φ1 α1) :
    XiCData Gk (compWeight L a₁) ν K 1 (b ^ 2 * eps + xiK2 d L N * δ₃)
      (composeData hP (compWeight L a₁) φ D) := by
  obtain ⟨hδ0, hδ0', hδ1, hνε, hDom, -⟩ := hnum.domain HBp hD
  exact i5_stage1_of_close hb₁ hbC hS.fam.2.1 ha₁ HBp HBk hP hcol hnum hD
    (Dec2.i4b_one hS S HBp hκ hM hδ0 le_rfl hδ0' hδ1 hνε hDom h1).2.1 fun x hx i =>
      composed_close_X0_sup hS S hG hSS hMM HBp hP hκ hM hs hs1 hN hT hr₀ hδ0 le_rfl hδ0' hδ1
        hνε hDom h h1 (hX₀ x hx) (mem_Ω1_of_mem_dataSites hP hcol hx) i

/-- **The point facts of Lemma DL for a sup-separated parent** (cover form of
`point_facts_of_one_le`).  For realizable data `Θ = D ∈ Ξ^c_K(𝔹_{k+1}; 1, ε')` and `s` in the
polydisc (`‖s_P‖ < e^κ`, `s = 1` off the parameter cubes of the cover of `𝔹_{k+1}`) the composite
is computed through the analytic functions `F₁` (Theorem I-4b for the pair
`(coverOf 𝔹_{k+1}, 𝔹_{k+1})`, `Dec2.i4b_analytic`) and `F_k`, and its argument lies in
`Ξ^c_j(𝔹_j(X); b, b² ε' + K₂' δ₃)`, `1 ≤ b ≤ C₀`.  The hypotheses are those of `BgSetting` with
the cover data `Dec2.DecSpecs`, `Dec2.CoverBase (coverOf 𝔹_{k+1}) 𝔹_{k+1}`, `SupSep`, `CubeAligned`
in place of `DecSpecs`, `DGSetting`, and the target bound `T ≤ ϱ - 1` in place of
`r₀ M₁ ≤ ϱ - 1`. -/
theorem point_facts_sup_of_one_le {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx) (hG : CubeAligned Gp m₁)
    (hSS : SupSep Gp m₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁) (ha₁ : 0 < a₁)
    (HBp : BgHyp d L K ϱ (compWeight L a₁) ν) (HBk : BgHyp d L K ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L K ϱ₂ (compWeight L a₁) ν) (hP : Precedes Gk Gp) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ r₀ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃) {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)}
    (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x →
        y ∈ X₁f)
    (hT : (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L ≤ ϱ - 1)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) {j : ℕ} (hj : j ≤ K)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D) :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
      Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧
      F₁ (s, rawOf D) = (φ, α) ∧
      XiCData Gk (compWeight L a₁) ν K 1 (b ^ 2 * eps + xiK2 d L N * δ₃)
        (composeData hP (compWeight L a₁) φ D) ∧
      D1raw Gp Gk (compWeight L a₁) F₁ (s, rawOf D) =
        rawOf (composeData hP (compWeight L a₁) φ D) ∧
      D2raw Gk Gj (compWeight L a₁) Fk (rawOf (composeData hP (compWeight L a₁) φ D)) =
        rawOf (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) (composeData hP (compWeight L a₁) φ D))
          (composeData hP (compWeight L a₁) φ D)) ∧
      XiCData Gj (compWeight L a₁) ν j b (b ^ 2 * eps + xiK2 d L N * δ₃)
        (composeData hq (compWeight L a₁)
          (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) (composeData hP (compWeight L a₁) φ D))
          (composeData hP (compWeight L a₁) φ D)) := by
  obtain ⟨hδ0, hδ0', hδ1, hνε, hDom, hU⟩ := hnum.domain HBp hD
  have hsle : ∀ P, ‖s P‖ ≤ Real.exp κ := fun P => (hs P).le
  have hone : ∀ P : ↥(coverOf Gp).cubeIdx,
      ‖(fun _ : ↥(coverOf Gp).cubeIdx => (1 : ℂ)) P‖ ≤ Real.exp κ :=
    fun P => by simpa using Real.one_le_exp hκ.le
  obtain ⟨φ, α, hI, -⟩ := Dec2.i4b_exists_unique hS S HBp hκ.le hM hsle hδ0 le_rfl hδ0' hδ1 hνε
    hDom
  obtain ⟨φ1, α1, hI1, -⟩ := Dec2.i4b_exists_unique hS S HBp hκ.le hM hone hδ0 le_rfl hδ0' hδ1
    hνε hDom
  have hst := i5_stage1_sup_of_one_le hb₁ hbC hS S hG hSS hMM ha₁ HBp HBk hP colk hκ.le hM hnum
    dsX₀ hN hT hr₀ hsle hs1 hD hI hI1
  have hFeq : F₁ (s, rawOf D) = (φ, α) := hF₁ s D hs hU φ α hI
  exact ⟨φ, α, hI, hFeq, hst, point_facts_of_stage1 hb₁ hbC ha₁ HBk HBj hP hq colj hnum hj hFk
    hFeq hst⟩

end Stages

end Balaban.Localization
