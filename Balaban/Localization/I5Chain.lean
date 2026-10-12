/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Close
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma DL (LOCALIZATION.md §4.3), the chain of the analyticity spaces

The composite function of Lemma DL, for the background part, is
`𝒯(s; Θ) = 𝓔(X; ψ(𝔹_j(X), 𝔹_k(X); ψ(𝔹_k(X), 𝔹_{k+1}; Θ, s)))`.  This file proves that its
argument stays in a space `Ξ^c_j(𝔹_j(X); C₀, ε₂)`, for every `s` in the polydisc:

* `XiCData`, `XiCRaw`: the data (and raw data) of `Ξ^c_n(𝔹; σ, ε)` with a realization by a
  `BgData`;
* `xiCData_compose`: (Ξ3) at the level of realizations;
* `i5_stage1`: `ψ(𝔹_k(X), 𝔹_{k+1}; Θ, s) ∈ Ξ^c_{k+1}(𝔹_k(X); 1, ε₂)`, from (Ξ3), the rescaling
  `Ξ^c(σ, ε) ⊆ Ξ^c(1, σ² ε)`, closeness on `X₀` and (Ξ2);
* `i5_stage2`: its composition with `𝔹_j(X) ≺ 𝔹_k(X)` lies in `Ξ^c_j(𝔹_j(X); C₀, ε₂)`.

Constants (differing from LOCALIZATION.md §4.3 where `σ = 1`): the landed (Ξ3) maps
`Ξ^c(𝔹'; 1, ε)` into `Ξ^c(𝔹; C₀ θ, ε)` with `C₀ = 8d + 12`; the factor `C₀` is absorbed by
`ε₁ = C₀² ε'` before (Ξ2) and `ε₂ = ε₁ + K₂' δ₃` is the final radius.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix

section Defs

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ : ℝ}

/-- The raw data `(Ψ, h̃)` of a datum. -/
def rawOf {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (D : BgData G N) :
    RawData d L (N₁ * L ^ m₁) K N := (D.Ψ, D.h)

theorem BgData.eq_of_raw {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {D D' : BgData G N}
    (h : rawOf D = rawOf D') : D = D' := by
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 h
  cases D; cases D'
  simp only [rawOf] at h1 h2
  subst h1; subst h2; rfl

theorem BgData.eq_of_realizesC {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {D D' : BgData G N}
    {Ψ₀ : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ} (h1 : RealizesC D Ψ₀ h₀ Ψ'' h'')
    (h2 : RealizesC D' Ψ₀ h₀ Ψ'' h'') : D = D' := by
  classical
  refine BgData.eq_of_raw (Prod.ext ?_ ?_)
  · funext x i
    by_cases hx : x ∈ dataSites G
    · exact (h1.1 x hx i).trans (h2.1 x hx i).symm
    · show D.Ψ x i = D'.Ψ x i
      rw [D.Ψ_zero x hx, D'.Ψ_zero x hx]
  · funext x i
    by_cases hx : x ∈ G.Ω 1
    · exact (h1.2 x hx i).trans (h2.2 x hx i).symm
    · show D.h x i = D'.h x i
      rw [D.h_zero x hx, D'.h_zero x hx]

variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ) (n : ℕ) (σ ε : ℝ)

/-- `D` realizes a member of `Ξ^c_n(𝔹; σ, ε)`. -/
def XiCData (D : BgData G N) : Prop :=
  ∃ (Ψ₀ : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (Ψ'' h'' : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ),
    XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'' ∧ RealizesC D Ψ₀ h₀ Ψ'' h''

/-- **The space `Ξ^c_n(𝔹; σ, ε)` as a set of raw data `(Ψ, h̃)`.** -/
def XiCRaw : Set (RawData d L (N₁ * L ^ m₁) K N) :=
  {p | ∃ D : BgData G N, XiCData G a ν n σ ε D ∧ p = rawOf D}

end Defs

section Chain

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {a₁ ν : ℝ}

/-- (Ξ3) for realizations (with `θ = 1`, level = depth): `Ξ^c_K(𝔹'; 1, ε) ⟶ Ξ^c_K(𝔹; C₀, ε)`. -/
theorem xiCData_compose (ha₁ : 0 < a₁) (H : BgHyp d L K ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L K ϱ₁ (compWeight L a₁) ν) (h : Precedes G G') {ε : ℝ}
    (hcol : ∀ z ∈ collar G, z ∈ G'.Ω 1)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hth : xiC1 d * ε ≤ thm73C1 d L N)
    {D : BgData G' N} (hX : XiCData G' (compWeight L a₁) ν K 1 ε D) :
    XiCData G (compWeight L a₁) ν K (scaledC0 d * 1) ε
      (composeData h (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D) := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', ⟨-, hε, Dr, Dc, hXr, hC, hDcU, hb⟩, hRD⟩ := hX
  have hDc : Dc = D := BgData.eq_of_realizesC hC hRD
  subst hDc
  obtain ⟨h1, h2, h3, h4, -⟩ := xiC_compose_at (G := G) (G' := G') (j := K) (ha₁ := ha₁) H H' h hε
    one_pos (by simp) (scaleGap_one h) (fun z hz => ⟨hcol z hz, by
      have := G'.spacing_ge_one z; linarith⟩) hsmall hth hXr hC hDcU hb
  have hc1 := one_le_scaledC0 d
  exact ⟨_, h₀, _, _, ⟨by positivity, hε, _, _, h1, h2, h3, h4⟩, h2⟩

end Chain

section Stages

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {a₁ ν : ℝ}

/-- The numerical conditions of the chain (all smallness conditions on `ε'`, `δ₃` of Lemma DL;
`ε₁ = C₀² ε'`, `ε₂ = ε₁ + K₂' δ₃`). -/
structure ChainNum (d L N m₁ : ℕ) [NeZero L] (BG κ r₀ eps δ₃ : ℝ) : Prop where
  eps_pos : 0 < eps
  small1 : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1
  th1 : xiC1 d * eps ≤ thm73C1 d L N
  c7le : xiC1 d * eps ≤ c7 d L N BG κ
  small₁ : (4 * d + 6) * ((2 * d + 1) * (scaledC0 d ^ 2 * eps)) ≤ 1
  δ₃_nn : 0 ≤ δ₃
  δ₃_le_one : δ₃ ≤ 1
  c1 : xiC1 d * (scaledC0 d ^ 2 * eps) + 5 * δ₃ ≤ bgC1 d L N
  star : δ₃ ≤ deltaStar d L N
  K1s : bgK1 d L N * (xiC1 d * (scaledC0 d ^ 2 * eps)) ≤ deltaStar d L N
  sm : bgK1 d L N * (xiC1 d * (scaledC0 d ^ 2 * eps)) + cK2 d L N * δ₃ < bgC0 d L N
  small₂ : (4 * d + 6) * ((2 * d + 1) * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃)) ≤ 1
  th2 : xiC1 d * (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃) ≤ thm73C1 d L N
  close : N * composedCloseBound d L N m₁ BG κ (xiC1 d * eps) r₀ ≤ δ₃

theorem c7_le_bgC1 (d L N : ℕ) [NeZero L] (BG κ : ℝ) : c7 d L N BG κ ≤ bgC1 d L N :=
  min_le_left _ _

/-- `Ξ^c_K(𝔹; 1, ε')` data lie in the data domain `Ψ̃^c(δ, δ)`, `δ = C₁ ε'`. -/
theorem xiCData_inDomainC (H : BgHyp d L K ϱ (compWeight L a₁) ν) {eps : ℝ}
    (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1) {D : BgData Gp N}
    (hX : XiCData Gp (compWeight L a₁) ν K 1 eps D) :
    InDomainC Gp ν (xiC1 d * eps) (xiC1 d * eps) D := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hC⟩ := hX
  exact ⟨Ψ₀, h₀, Ψ'', h'', xiC_one_subset H hsmall hX, hC.1, hC.2⟩

theorem inUnionDomainC_of_inDomainC (H : BgHyp d L K ϱ (compWeight L a₁) ν) {δ c₁ : ℝ}
    (hδ0 : 0 < δ) (hδ0' : δ ≤ bgC0 d L N) (hδ1 : δ ≤ c₁) {D : BgData Gp N}
    (hD : InDomainC Gp ν δ δ D) : InUnionDomainC Gp (bgC0 d L N) c₁ ν D :=
  ⟨δ, δ, hδ0, le_rfl, hδ0', hδ1, by
    have := H.massLe; nlinarith [sq_nonneg δ], hD⟩

theorem isLayerConstant_zero (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) :
    IsLayerConstant G (0 : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ) :=
  fun _ _ _ _ _ _ _ => rfl

/-- **Stage 1 of Lemma DL**: the composed datum `ψ(𝔹_k(X), 𝔹_{k+1}; Θ, s)` of the decoupled
background field lies in `Ξ^c_{K}(𝔹_k(X); 1, ε₂)`. -/
theorem i5_stage1 {c BG : ℝ} (hS : DecSpecs d L c BG) (S : DGSetting Gp (compWeight L a₁) ν)
    (ha₁ : 0 < a₁) (HBp : BgHyp d L K ϱ (compWeight L a₁) ν)
    (HBk : BgHyp d L K ϱ₁ (compWeight L a₁) ν) (hP : Precedes Gk Gp)
    (hcol : ∀ z ∈ collar Gk, z ∈ Gp.Ω 1) {κ r₀ eps δ₃ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hnum : ChainNum d L N m₁ BG κ r₀ eps δ₃)
    {X₀ X₁ : Finset (CTorus d L N₁ m₁ K)} (hX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ Gp.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * Gp.spacing x → y ∈ X₁)
    (hr : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1) (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) {s : DecParams Gp} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁ →
      s ⟨P, hP⟩ = 1)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D)
    {φ φ1 : Gp.Ω 1 × Fin N → ℂ} {α α1 : Gp.Ω 1 → ℂ}
    (h : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α)
    (h1 : IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) (fun _ => 1) D φ1 α1) :
    XiCData Gk (compWeight L a₁) ν K 1 (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃)
      (composeData hP (compWeight L a₁) φ D) := by
  have hd0 : 0 < d := by have := HBp.hd; omega
  have hε := hnum.eps_pos
  have hc1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC HBp hnum.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hnum.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  -- `s = 1` is the background field
  obtain ⟨-, hφ1, -⟩ := i4b_one hS S HBp hκ hM hδ0 le_rfl hδ0' hδ1 hνε hDom h1
  -- (Ξ3), rescaling
  have hDk1 := xiCData_compose ha₁ HBk HBp hP hcol hnum.small1 hnum.th1 hD
  rw [hφ1] at hDk1
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := hDk1
  have hσ : (1 : ℝ) ≤ scaledC0 d * 1 := by rw [mul_one]; exact one_le_scaledC0 d
  have hX1 := xiC_scale hσ hX
  have e1 : (scaledC0 d * 1) ^ 2 * eps = scaledC0 d ^ 2 * eps := by rw [mul_one]
  rw [e1] at hX1
  -- the difference of the composed data
  set δΨ : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ := fun x i =>
    composeField Gk Gp (compWeight L a₁) φ D.Ψ x i - composeField Gk Gp (compWeight L a₁) φ1 D.Ψ x i
    with hδΨ
  have hδΨc : IsLayerConstant Gk δΨ := by
    have e : δΨ = fun x i => composeField Gk Gp (compWeight L a₁) (φ - φ1)
        (0 : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ) x i := by
      funext x i; exact composeField_sub_zero (G := Gk) (G' := Gp) _ φ φ1 D.Ψ x i
    rw [e]
    exact composeField_layerConst hP _ _ (isLayerConstant_zero Gp)
  have hδΨb : ∀ x ∈ dataSites Gk, vn (δΨ x) ≤ δ₃ := by
    intro x hx
    have hxΩ : x ∈ Gp.Ω 1 := by
      rcases (mem_dataSites Gk).1 hx with h' | h'
      · exact hP.mem_Ω1 h'
      · exact hcol x h'
    have hB := composedCloseBound_nonneg (d := d) (L := L) (N := N) (m₁ := m₁)
      (κ := κ) (r₀ := r₀) hS.fam.2.1 hδ0.le hd0
    refine (vn_le_card_mul hB fun i => ?_).trans hnum.close
    exact composed_close_X0 hS S HBp hP hκ hM hs hs1 hN hr hr₀ hδ0 le_rfl hδ0' hδ1 hνε
      hDom h h1 (hX₀ x hx) hxΩ i
  have hX2 := xiC_perturb HBk hnum.δ₃_nn hnum.δ₃_le_one hnum.small₁ hnum.c1 hnum.star hnum.K1s
    hnum.sm hδΨc hδΨb hX1
  refine ⟨Ψ₀, h₀, fun x i => Ψ'' x i + δΨ x i, h'', hX2, ⟨fun x hx i => ?_, fun x hx i => ?_⟩⟩
  · have := hR.1 x hx i
    show composeField Gk Gp (compWeight L a₁) φ D.Ψ x i = _
    have e2 : composeField Gk Gp (compWeight L a₁) φ D.Ψ x i =
        composeField Gk Gp (compWeight L a₁) φ1 D.Ψ x i + δΨ x i := by simp [hδΨ]
    rw [e2]
    have e3 : composeField Gk Gp (compWeight L a₁) φ1 D.Ψ x i = _ := this
    rw [e3]; ring
  · have := hR.2 x hx i
    simpa [composeData, hx] using this

theorem xiCData_unionC {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {n : ℕ} {σ ε : ℝ}
    {D : BgData G N} (hX : XiCData G a ν n σ ε D) :
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', ⟨-, -, Dr, Dc, -, hC, hU, -⟩, hR⟩ := hX
  have : Dc = D := BgData.eq_of_realizesC hC hR
  subst this; exact hU

theorem xiCData_level_mono {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {n n' : ℕ}
    {σ ε : ℝ} (hn : n' ≤ n) (hν : 0 ≤ ν) {D : BgData G N}
    (hX : XiCData G a ν n σ ε D) : XiCData G a ν n' σ ε D := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := hX
  exact ⟨Ψ₀, h₀, Ψ'', h'', xiC_level_mono hn hν (by
    have := NeZero.ne L; omega) hX, hR⟩

/-- **Stage 2 of Lemma DL**: the composition of a member of `Ξ^c_K(𝔹_k(X); 1, ε₂)` with
`𝔹_j(X) ≺ 𝔹_k(X)` lies in `Ξ^c_{j'}(𝔹_j(X); C₀, ε₂)`, `j' ≤ K`. -/
theorem i5_stage2 (ha₁ : 0 < a₁) (HBk : BgHyp d L K ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L K ϱ₂ (compWeight L a₁) ν) (hq : Precedes Gj Gk)
    (hcol : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1) {ε₂ : ℝ}
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε₂) ≤ 1) (hth : xiC1 d * ε₂ ≤ thm73C1 d L N)
    {j' : ℕ} (hj' : j' ≤ K) {Dk : BgData Gk N} (hD : XiCData Gk (compWeight L a₁) ν K 1 ε₂ Dk) :
    XiCData Gj (compWeight L a₁) ν j' (scaledC0 d)  ε₂
      (composeData hq (compWeight L a₁) (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) Dk) Dk) := by
  have h := xiCData_compose ha₁ HBj HBk hq hcol hsmall hth hD
  rw [mul_one] at h
  exact xiCData_level_mono hj' HBj.mass h

end Stages

end Balaban.Localization
