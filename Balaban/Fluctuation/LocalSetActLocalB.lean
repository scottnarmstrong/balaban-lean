/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalSetActBlock
public import Balaban.Fluctuation.LocalPairReplacementLocalB

/-!
# The block energy recomputed on the local generating set

P6 §4.1, Lemma 4.1 and P3 pp. 78-79 for the zero-source part of the activities: the term of a
domain at zero source is built from the block energy `blockEnergyFun 𝔹 𝔹⁻ … n z` of the block
`B_{n+1}(z)` at the decoupled background of `(coverOf 𝔹, 𝔹)` and the fluctuation field of
`(coverOf 𝔹, 𝔹⁻)` (`zeroSourceActivity_common_fromTowerG_core`).  Here the ambient level sets
`𝔹 = 𝔹_{k+1}`, `𝔹⁻ = 𝔹_k` are replaced by the local generating sets
`𝔹_{k+1}(Y) = localB (k + 1) … Y` and `𝔹_k(Y) = localB k … Ω_k(𝔹_{k+1}(Y))`, with the transported
parameters `τ w` of `coef_eTermFun_replacement_localB`.

* `block_read_of_near`: the reading hypothesis of `blockEnergyFun_replacement_cross_of_agree` (the
  block, its right neighbours and its `n`-blocks lie in the `M₁ L^{k+1}`-neighbourhood of the read
  region) when the block lies in the read region;
* `coef_blockEnergyFun_replacement_localB`: the coefficient equality of Lemma AE between the ambient
  block energy (parameters `σ w = extParams 𝔹_{k+1} X₁ w`, fluctuation variable `ψ₁(w)`) and the
  block energy recomputed on `(𝔹_{k+1}(Y), 𝔹_k(Y))` (parameters `τ w`, fluctuation variable
  `ψ₂(w)`), when the read region `R` (the cubes of `𝒞`, the cubes meeting `X₁` and the block
  `B_{n+1}(z)`) has the margin `2 M₁ L^{k+1}` in the top layer of `𝔹_{k+1}(Y)` and the two
  fluctuation variables agree within `L^{k+1}` of `R`.  The component hypotheses are discharged by
  the depth lemmas of `LocalPairDepth.lean` and the inner-cube lemmas of `LocalPairLevelInner.lean`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.Fluctuation

section Read

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱm ϱh : ℝ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

/-- **The reading hypothesis of the block energy from the read region.**  If the block
`B_{n+1}(z)` (`n ≤ k + 1`) lies in `R`, the sites of `R` are in `Ω₁` of both fluctuation sets or of
neither, and `Y_b` contains the `M₁ L^{k+1}`-neighbourhood of `R`, then every site of the block lies
in `R`, in `Ω₁` of both sets or of neither, and its right neighbours and its `n`-block lie in
`Y_b`. -/
theorem block_read_of_near {Hl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱh}
    {R Yb : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRY : ∀ x ∈ R, ∀ y, supDist x y ≤ L ^ (k + 1 + m₁) → y ∈ Yb)
    (hΩ : ∀ x ∈ R, (x ∈ Hm.Ω 1 ↔ x ∈ Hl.Ω 1)) {n : ℕ} (hn : n ≤ k + 1)
    {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (n + 1)))}
    (hRz : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) n z, x ∈ R) :
    ∀ x ∈ blockSites d L N₁ m₁ (k + 1) n z, x ∈ R ∧ (x ∈ Hm.Ω 1 ↔ x ∈ Hl.Ω 1) ∧
      ∀ y : CTorus d L N₁ m₁ (k + 1),
        (y = x ∨ (∃ μ : Fin d, y = x + Pi.single μ 1) ∨ y ∈ Hm.blk n x) → y ∈ Yb := by
  intro x hx
  have hxR := hRz x hx
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨hxR, hΩ x hxR, fun y hy => hRY x hxR y ?_⟩
  rcases hy with rfl | ⟨μ, rfl⟩ | hy
  · rw [supDist_self]; exact Nat.zero_le _
  · exact (supDist_add_single_le x μ).trans (Nat.one_le_pow _ _ hL)
  · exact (supDist_le_of_mem_blk hn hy).trans (Nat.pow_le_pow_right hL (by omega))

end Read

section Assembly

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a : ℕ → ℝ} {ν : ℝ}

/-- **The block energy recomputed on a local generating set `Gl`, core** (P3 pp. 78-79, P6 Lemma
4.1).  The statement of `coef_blockEnergyFun_replacement_localB` for an arbitrary cube-aligned,
sup-separated generating set `Gl` in place of `𝔹_{k+1}(Y)` and `Gd ≺ Gl` (the layer `k` of `Gl`, no
layer `k + 1`) in place of `𝔹_k(Y)`, with the defining property of the recomputed fluctuation map
asked at its own level `δ₀'`.  The landed `localB` statement is its instance. -/
theorem coef_blockEnergyFun_replacement_gen (hG' : IsLevel Gp (k + 1)) (hG : IsLevel Hm k)
    (hk1 : 1 ≤ k) {ϱl ϱl' : ℝ} {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
    {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}
    (hA : CubeAligned Gl m₁) (hSS : SupSep Gl m₁) (hPd : Precedes Gd Gl)
    (hdk : Gd.Ω k = Gl.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl - 1))
    (hagd : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl' - 1))
    {c BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ a ν) (HB' : BgHyp d L (k + 1) ϱl a ν)
    {κ : ℝ} (hκ : 0 ≤ κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf Gl) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) ×
        (Gl.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp a ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf Gl))
      (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gl)
          Gl a ν (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₀' δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h0' : 0 ≤ δ₀')
    (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₀' : δ₀' ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf Gl) ×
        Edat Gd N →
      (Gd.Ω 1 × Fin N → ℂ) ×
        (Gd.Ω 1 → ℂ)}
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
    (hSol' : ∀ p : Dec2.DecParams (coverOf Gl) ×
        Edat Gd N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀' δ₁ p.2 →
        (Sol' p).1 = dphi Gd
          (Dec2.decG (coverOf Gl)
            Gd a ν p.1)
          p.2.2.1 p.2.1
          (pertSource Gd a p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf Gl)
          Gd a ν p.1 false
          p.2.2.1 p.2.1
          (pertSource Gd a p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small Gd (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ,
          Small Gd δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl)
            Gd a ν p.1 false
            p.2.2.1 p.2.1
            (pertSource Gd a p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx Gp X₁)) {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {D : BgData Gp N} {D' : BgData Gl N}
    (hDd : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDd' : InUnionDomainC Gl (bgC0 d L N)
      (c7 d L N BG κ) ν D')
    (hD' : ∀ x ∈ Gl.Ω (k + 1),
      D'.Ψ x = D.Ψ x ∧ D'.h x = D.h x)
    (ψ₁ ψ₂ : (ParIdx Gp X₁ → ℂ) → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (he : ∀ w ∈ supN C R', StrictDataM Hm N false δ₀ δ₁
      (flEdat Gp Hm (F₁ (extParams Gp X₁ w, rawOf D)) D.Ψ (ψ₁ w)))
    (he' : ∀ w ∈ supN C R', StrictDataM Gd N false δ₀' δ₁
      (flEdat Gl
        Gd
        (F₁' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D'))
        D'.Ψ (ψ₂ w)))
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    {n : ℕ} (hn : n ≤ k + 1) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (n + 1))))
    (hRz : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) n z, x ∈ R)
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ Gl.Ω (k + 1))
    (hψ : ∀ w ∈ supN C R', ∀ x ∈ R, ∀ y, supDist x y ≤ L ^ (k + 1) → ψ₁ w y = ψ₂ w y)
    (Θ₁ Θ₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N) :
    coef (fun w => blockEnergyFun Gp Hm a ν n z (F₁ (extParams Gp X₁ w, rawOf D))
        (Sol (extParams Gp X₁ w,
          flEdat Gp Hm (F₁ (extParams Gp X₁ w, rawOf D)) D.Ψ (ψ₁ w))).1 (Θ₁, ψ₁ w)) C =
      coef (fun w => blockEnergyFun Gl
        Gd a ν n z
        (F₁' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D'))
        (Sol' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0),
          flEdat Gl
            Gd
            (F₁' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D'))
            D'.Ψ (ψ₂ w))).1 (Θ₂, ψ₂ w)) C := by
  classical
  obtain ⟨Sb, Sb', Sf, Sf'⟩ := replacement_coverBases hG' Hm hA hSS hPd hN hm₁ hM HB hag hagm hagl hagd
  set Y₀ : Finset (CTorus d L N₁ m₁ (k + 1)) :=
    Finset.univ.filter (fun y => ∃ x ∈ R, supDist x y ≤ L ^ (k + 1 + m₁)) with hY₀
  have hRY : ∀ x ∈ R, ∀ y, supDist x y ≤ L ^ (k + 1 + m₁) → y ∈ Y₀ := fun x hx y h =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx, h⟩
  have hYR : ∀ y ∈ Y₀, ∃ x ∈ R, supDist x y ≤ L ^ (k + 1 + m₁) := fun y hy =>
    (Finset.mem_filter.1 hy).2
  have hRY₀ : ∀ x ∈ R, x ∈ Y₀ := fun x hx => hRY x hx x (by rw [supDist_self]; exact Nat.zero_le _)
  have hM2 : 2 ≤ L ^ m₁ := by
    have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    nlinarith [Nat.one_le_pow 2 L hL1]
  have htop : ∀ y ∈ Y₀, y ∈ Gl.Ω (k + 1) :=
    fun y hy => topLayer_of_mem hmar hYR hy
  have hU : ∀ x y : CTorus d L N₁ m₁ (k + 1), SameCell (L ^ (k + 1 + m₁)) x y →
      (x ∈ Gl.Ω (k + 1) ↔ y ∈ Gl.Ω (k + 1)) :=
    fun x y h => hA.union (k + 1) (by omega) le_rfl x y h
  have hstb := fun y (hy : y ∈ Gl.Ω (k + 1)) =>
    level_layer_iff_of_top hG' hy
  have hstf := fun y (hy : y ∈ Gl.Ω (k + 1)) =>
    drop_layer_iff_of_top (Hm := Hm) hG hk1 hdk hdtop hy
  have hHb : ∀ x, x ∈ Gp.Ω 1 := fun x => (hG' x).1
  have hHf : ∀ x, x ∈ Hm.Ω 1 := fun x => (hG x).1
  have hH'b : ∀ x ∈ Gl.Ω k,
      x ∈ Gl.Ω 1 := fun x hx =>
    Gl.Ω_antitone le_rfl hk1 (by omega) hx
  have hH'f := fun x (hx : x ∈ Gl.Ω k) =>
    drop_Ω_one_of_mem hdk hk1 hx
  have hΩY : ∀ x ∈ Y₀, (x ∈ Hm.Ω 1 ↔ x ∈ Gd.Ω 1) := fun x hx =>
    iff_of_true (hHf x) (hH'f x (Gl.Ω_antitone
      hk1 (Nat.le_succ k) (by omega) (htop x hx)))
  have hs'0 := fun w : ParIdx Gp X₁ → ℂ =>
    tau_off_top (Gl := Gl) (extParams Gp X₁ w)
  have hsτ := fun w : ParIdx Gp X₁ → ℂ =>
    tau_top (Gl := Gl) hG' (extParams Gp X₁ w)
  have hhat := fun w : ParIdx Gp X₁ → ℂ =>
    hat_of_active (Gp := Gp) hSS hA hk1 hM (hs'0 w)
  have hsσ : ∀ w ∈ supN C R', ∀ P, ‖extParams Gp X₁ w P‖ < Real.exp κ := fun w hw P =>
    (norm_extParams_lt hR' hw.2 P).trans_le hRκ
  have hdichb := fun w (hw : w ∈ supN C R') => localB_depth_dich hG' hm₁ hRC hRX Gp hw.1
  have hdichf := fun w (hw : w ∈ supN C R') => localB_depth_dich hG' hm₁ hRC hRX Hm hw.1
  have hrow := fun w (hw : w ∈ supN C R') => localB_depth_row hG' hm₁ hRC hRX Y₀ hw.1
  exact coef_blockEnergyFun_replacement_cross_sep hS Sb Sb' HB HB' hκ hMc hF₁ hF₁' hF₂ Sf Sf' hM₂
    h0 h1 h0' h1 hδ₀ hδ₁ hδ₀' hδ₁ hSol hSol' C hR' (extParams Gp X₁)
    (fun w P => if P.1.2 ∈ Gl.Ω (k + 1)
      then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0)
    hsσ (fun w hw => tau_norm_lt (Gl := Gl) (hsσ w hw) (hR'.trans_le hRκ))
    hDd hDd' ψ₁ ψ₂ he he' hRY₀ (fun y hy => hstb y (htop y hy)) hdichb
    (fun w hw => level_dich_cross hSS hG' hk1 hHb hH'b (hs'0 w) (hhat w) (hsτ w)
      (hdichb w hw))
    hrow
    (fun w hw => level_row_cross hSS hG' hk1 (hs'0 w) (hhat w) (hsτ w) (hrow w hw))
    (fun w hw => level_inner_cross hG' hHb
      (depth_deep hU hG' hm₁ hRC hRX hmar hstb hw.1) (hsτ w))
    (fun w _ => level_inner_cross' hSS hG' hk1 hH'b (hs'0 w) (hhat w) (hsτ w))
    (localB_depth_res_bg hG' hRY) (depth_act hG' hM2 hmar hYR)
    (fun y hy _ y' hy' => by
      have ht := depth_approxDep (Gp := Gp) hM2 hmar hYR y hy y' hy'
      exact ⟨(hD' y' ht).1.symm, (hD' y' ht).2.symm⟩)
    (fun y hy => (hD' y (htop y hy)).1.symm)
    hRY₀ (fun _ hx => hx) hΩY
    hdichf
    (fun w hw => level_dich_cross hSS hG' hk1 hHf hH'f (hs'0 w) (hhat w) (hsτ w)
      (hdichf w hw))
    hrow
    (fun w hw => level_row_cross hSS hG' hk1 (hs'0 w) (hhat w) (hsτ w) (hrow w hw))
    (fun w hw => level_inner_cross hG' hHf
      (depth_deep hU hG' hm₁ hRC hRX hmar hstf hw.1) (hsτ w))
    (fun w _ => level_inner_cross' hSS hG' hk1 hH'f (hs'0 w) (hhat w) (hsτ w))
    (depth_res_fl hmar hRY hYR hstf) n z Θ₁ Θ₂
    (block_read_of_near hRY (fun x hx => hΩY x (hRY₀ x hx)) hn hRz)
    (fun w hw x hx _ y hy => hψ w hw x hx y (supDist_le_of_mem_resSites hy))
    (fun w hw x hx => hψ w hw x (hRz x hx) x (by rw [supDist_self]; exact Nat.zero_le _))

/-- **The block energy recomputed on the local generating set (P3 pp. 78-79, P6 Lemma 4.1).**  Let
`𝔹_{k+1}`, `𝔹_k` be level sets (`k ≥ 1`), `𝔹_{k+1}(Y) = localB (k + 1) … Y`,
`𝔹_k(Y) = localB k … Ω_k(𝔹_{k+1}(Y))`, `𝒞` a family of cubes of the cover of `𝔹_{k+1}` disjoint
from `X₁`, and `R` a set of sites containing the cubes of `𝒞`, the cubes meeting `X₁` and the block
`B_{n+1}(z)`, with the margin: every site within `2 M₁ L^{k+1}` of `R` lies in
`Ω_{k+1}(𝔹_{k+1}(Y))`.  With the constants, the maps `F₁, F₁'` and `Sol, Sol'` of the ambient and
the local pairs, a datum `D'` of `𝔹_{k+1}(Y)` agreeing with `D` on the top layer, and fluctuation
variables `ψ₁(w)`, `ψ₂(w)` with the strict data inequalities on their sides that agree within
`L^{k+1}` of `R`: the coefficient `coef (·) 𝒞` of the ambient block energy with the parameters
`σ w = extParams 𝔹_{k+1} X₁ w` equals that of the block energy recomputed on `(𝔹_{k+1}(Y), 𝔹_k(Y))`
with the transported parameters `τ w`. -/
theorem coef_blockEnergyFun_replacement_localB (hG' : IsLevel Gp (k + 1)) (hG : IsLevel Hm k)
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1) (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ a ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁)) a ν)
    {κ : ℝ} (hκ : 0 ≤ κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf Gp) Gp a ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) a ν (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 ≤ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
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
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) a ν p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) a p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) a ν p.1 false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) a p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) a ν p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) a p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx Gp X₁)) {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {D : BgData Gp N} {D' : BgData (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) N}
    (hDd : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDd' : InUnionDomainC (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
      (c7 d L N BG κ) ν D')
    (hD' : ∀ x ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1),
      D'.Ψ x = D.Ψ x ∧ D'.h x = D.h x)
    (ψ₁ ψ₂ : (ParIdx Gp X₁ → ℂ) → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (he : ∀ w ∈ supN C R', StrictDataM Hm N false δ₀ δ₁
      (flEdat Gp Hm (F₁ (extParams Gp X₁ w, rawOf D)) D.Ψ (ψ₁ w)))
    (he' : ∀ w ∈ supN C R', StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁
      (flEdat (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D'))
        D'.Ψ (ψ₂ w)))
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    {n : ℕ} (hn : n ≤ k + 1) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (n + 1))))
    (hRz : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) n z, x ∈ R)
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1))
    (hψ : ∀ w ∈ supN C R', ∀ x ∈ R, ∀ y, supDist x y ≤ L ^ (k + 1) → ψ₁ w y = ψ₂ w y)
    (Θ₁ Θ₂ : RawData d L (N₁ * L ^ m₁) (k + 1) N) :
    coef (fun w => blockEnergyFun Gp Hm a ν n z (F₁ (extParams Gp X₁ w, rawOf D))
        (Sol (extParams Gp X₁ w,
          flEdat Gp Hm (F₁ (extParams Gp X₁ w, rawOf D)) D.Ψ (ψ₁ w))).1 (Θ₁, ψ₁ w)) C =
      coef (fun w => blockEnergyFun (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) a ν n z
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D'))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D'))
            D'.Ψ (ψ₂ w))).1 (Θ₂, ψ₂ w)) C :=
  coef_blockEnergyFun_replacement_gen hG' hG hk1 (localB_cubeAligned hk Y _ hm₁)
    (localB_supSep hk Y _) (localB_drop_precedes hk (Nat.le_succ k) Y _ _)
    (localB_drop_Ω hk (Nat.le_succ k) Y _ _ (le_refl k)) (localB_drop_top hk (Nat.le_succ k) Y _ _)
    hN hm₁ hM hag hagm hagl hagl hS HB HB' hκ hMc hF₁ hF₁' hF₂ hM₂ h0 h0 h1 hδ₀ hδ₀ hδ₁ hSol hSol' C
    hR' hRκ hDd hDd' hD' ψ₁ ψ₂ he he' hRC hRX hn z hRz hmar hψ Θ₁ Θ₂

end Assembly

end Balaban.Localization
