/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairBaseHat
public import Balaban.Localization.Decoupled2One
public import Balaban.Localization.Decoupled2Background
public import Balaban.Fluctuation.CubeActionRealStar
public import Balaban.Fluctuation.Theorem42WireStep

/-!
# The decoupled solutions at `s ≡ 1` for the P6 mixed pair (VMOD-11 §3, row 8)

* `Dec2.decBgField_one`, `Dec2.decBgMult_one`: the decoupled background field and multiplier
  (`decBgField`, `decBgMult`, defined through `∃!`) at `s ≡ 1` are the ordinary `bgFieldC`, `bgMultC`
  (Theorem I-4b, `i4b_exists_unique` + `i4b_one`);
* `Dec2.cubeDiffStar_dec_one`: the cube action difference of the decoupled backgrounds of a nested
  pair `G0 ≺ G1` at `s ≡ 1` is the cube action difference of the ordinary backgrounds, which is the
  expression `realStepAct` of `Theorem42WireAct.lean` (the star convention, the composition
  `composed_change` supplying the background of the composed datum);
* `p6_dec_bg_one_*`, `p6_dec_fl_one_*`: these for `(C♯, H^∂)` and `(C♯, H⁻)`;
* `p6_action_at_one`: the action identity for the P6 comparison `H^∂` vs `H⁻`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ}

/-- **Theorem I-4b (i), `s ≡ 1`, for the `∃!`-defined fields**: `decBgField` and `decBgMult` at
`s ≡ 1` are `bgFieldC` and `bgMultC` (the ordinary solution of Theorem 5.2). -/
theorem decBg_one {c BG : ℝ} (hS : DecSpecs d L Kc Cx c BG) (S : CoverBase C H a ν Kc Cx)
    (HB : BgHyp d L K ϱ a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε)
    (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData H N} (hD : InDomainC H ν δ ε D) :
    decBgField C H a ν (rho4 d L N BG κ) (fun _ => 1) D = bgFieldC H a ν (bgC0 d L N) D ∧
      decBgMult C H a ν (rho4 d L N BG κ) (fun _ => 1) D = bgMultC H a ν (bgC0 d L N) D := by
  obtain ⟨φ, α, hI, huniq, -⟩ := i4b_exists_unique hS S HB hκ hM
    (s := fun _ => (1 : ℂ)) (fun _ => by simpa using Real.one_le_exp hκ) hδ0 hδε hε hδ hνε hD
  obtain ⟨-, h1, h2⟩ := i4b_one hS S HB hκ hM hδ0 hδε hε hδ hνε hD hI
  obtain ⟨e1, e2⟩ := decBg_eq hI huniq
  exact ⟨e1.trans h1.symm, e2.trans h2.symm⟩

/-- **The cube action difference at `s ≡ 1`** for a nested pair `G0 ≺ G1` on the cover torus: the
difference of the star cube actions of the decoupled backgrounds, the boundary one restricted to
`Ω₁(G0)`, is that of the ordinary backgrounds (the expression `realStepAct`). -/
theorem cubeDiffStar_dec_one {ϱ0 ϱ1 : ℝ} {c BG : ℝ} {G0 : GeneratingSet d L (N₁ * L ^ m₁) K ϱ0}
    {G1 : GeneratingSet d L (N₁ * L ^ m₁) K ϱ1} (hprec : Precedes G0 G1)
    (hS : DecSpecs d L Kc Cx c BG) (S0 : CoverBase C G0 a ν Kc Cx) (S1 : CoverBase C G1 a ν Kc Cx)
    (H0 : BgHyp d L K ϱ0 a ν) (H1 : BgHyp d L K ϱ1 a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ0 ε0 δ1 ε1 : ℝ}
    (hδ0 : 0 < δ0) (hδε0 : δ0 ≤ ε0) (hε0 : ε0 ≤ bgC0 d L N) (hc0 : δ0 ≤ c7 d L N BG κ)
    (hν0 : ν * ((L : ℝ) ^ K) ^ 2 * ε0 ^ 2 ≤ δ0 ^ 2)
    (hδ1 : 0 < δ1) (hδε1 : δ1 ≤ ε1) (hε1 : ε1 ≤ bgC0 d L N) (hc1 : δ1 ≤ c7 d L N BG κ)
    (hν1 : ν * ((L : ℝ) ^ K) ^ 2 * ε1 ^ 2 ≤ δ1 ^ 2)
    {D0 : BgData G0 N} (hD0 : InDomainC G0 ν δ0 ε0 D0)
    {D1 : BgData G1 N} (hD1 : InDomainC G1 ν δ1 ε1 D1) (β : ℝ)
    (Q : Finset (Torus d ((N₁ * L ^ m₁) * L ^ K))) :
    (β : ℂ) * (Fluctuation.cubeActionStar G0 a ν Q D0.Ψ D0.h
        (hprec.restrictφ (decBgField C G1 a ν (rho4 d L N BG κ) (fun _ => 1) D1)) -
      Fluctuation.cubeActionStar G0 a ν Q D0.Ψ D0.h
        (decBgField C G0 a ν (rho4 d L N BG κ) (fun _ => 1) D0)) =
    (β : ℂ) * (Fluctuation.cubeActionStar G0 a ν Q D0.Ψ D0.h
        (hprec.restrictφ (bgFieldC G1 a ν (bgC0 d L N) D1)) -
      Fluctuation.cubeActionStar G0 a ν Q D0.Ψ D0.h (bgFieldC G0 a ν (bgC0 d L N) D0)) := by
  rw [(decBg_one hS S1 H1 hκ hM hδ1 hδε1 hε1 hc1 hν1 hD1).1,
    (decBg_one hS S0 H0 hκ hM hδ0 hδε0 hε0 hc0 hν0 hD0).1]

end Balaban.Localization.Dec2
