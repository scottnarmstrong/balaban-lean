/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairLocBase

/-!
# The composed background change of the real step, and the `s ≡ 1` identification (VMOD-11 row 8)

* `p6_composed_change`: `Theorem42WireStep.composed_change` at the pair `(locGen, bdGen)` with the
  data `locDataC`, `bdDataC` (the agreement `locData_eq_bd` and the layer agreement `locGen_bd_agree`
  on `E_{Z'}` discharged): the composed datum is in `𝒟`, has background `φ^∂|`, differs from `ψ̃`
  by `δΨ` vanishing on `E_{Z'}`, has the same `h`, and obeys the H7 bound `(2d + 2) K₁ δ'`;
* `realStepAct_eq_composed`: `realStepAct` is the star cube action difference of the local family at the
  composed background and at `φ^loc`, the expression bounded in `realStep_cubeDiffStar_bound`;
* `p6_action_at_one_composed`: the decoupled expression at `s ≡ 1` equals that composed expression.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.Multiscale.GeneratingSet RegionHistory

set_option linter.unusedSectionVars false

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hk : k + 1 ≤ K) {m₁ : ℕ}

include Hl in
/-- **`composed_change` at the pair `(locGen, bdGen)` of the real step.** -/
theorem p6_composed_change {a₁ ν δ' ε' : ℝ} (ha₁ : 0 < a₁)
    (H0 H1 : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν) (hδ0 : 0 < δ')
    (hδε : δ' ≤ ε') (hε : ε' ≤ bgC0 S.d S.L N) (hδc : δ' ≤ thm73C1 S.d S.L N)
    (hνε : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε' ^ 2 ≤ δ' ^ 2)
    (ψ : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - k)) → Fin N → ℂ)
    (ϑ : Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1 - (k + 1))) → Fin N → ℂ)
    (hC : Fin N → ℂ) (hD' : InDomainC (bdGen g Hl k hk) ν δ' ε' (bdDataC g Hl k hk ψ ϑ hC)) :
    InUnionDomainC (locGen g Hl k Zc hZc hk) (bgC0 S.d S.L N) (bgC1 S.d S.L N) ν
        (composeData (locGen_precedes_bd g Hl k Zc hZc hk) (compWeight S.L a₁)
          (bgFieldC (bdGen g Hl k hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
            (bdDataC g Hl k hk ψ ϑ hC)) (bdDataC g Hl k hk ψ ϑ hC)) ∧
      bgFieldC (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
        (composeData (locGen_precedes_bd g Hl k Zc hZc hk) (compWeight S.L a₁)
          (bgFieldC (bdGen g Hl k hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
            (bdDataC g Hl k hk ψ ϑ hC)) (bdDataC g Hl k hk ψ ϑ hC)) =
        (locGen_precedes_bd g Hl k Zc hZc hk).restrictφ
          (bgFieldC (bdGen g Hl k hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
            (bdDataC g Hl k hk ψ ϑ hC)) ∧
      (∀ y ∈ {x | blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈
          nbhd ⌊R k⌋₊ (Zc : Set (Torus S.d (n (k + 1))))}, ∀ i,
        (composeData (locGen_precedes_bd g Hl k Zc hZc hk) (compWeight S.L a₁)
          (bgFieldC (bdGen g Hl k hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
            (bdDataC g Hl k hk ψ ϑ hC)) (bdDataC g Hl k hk ψ ϑ hC)).Ψ y i -
          (locDataC g Hl k Zc hZc hk ψ ϑ hC).Ψ y i = 0) ∧
      (∀ x i, (composeData (locGen_precedes_bd g Hl k Zc hZc hk) (compWeight S.L a₁)
          (bgFieldC (bdGen g Hl k hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
            (bdDataC g Hl k hk ψ ϑ hC)) (bdDataC g Hl k hk ψ ϑ hC)).h x i =
        (locDataC g Hl k Zc hZc hk ψ ϑ hC).h x i) ∧
      (∀ x ∈ dataSites (locGen g Hl k Zc hZc hk),
        vn (fun i => (composeData (locGen_precedes_bd g Hl k Zc hZc hk) (compWeight S.L a₁)
          (bgFieldC (bdGen g Hl k hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
            (bdDataC g Hl k hk ψ ϑ hC)) (bdDataC g Hl k hk ψ ϑ hC)).Ψ x i -
          (locDataC g Hl k Zc hZc hk ψ ϑ hC).Ψ x i) ≤
        (2 * S.d + 2) * (bgK1 S.d S.L N * δ')) := by
  obtain ⟨hΨ, hh⟩ := locData_eq_bd g Hl k Zc hZc hk ψ ϑ hC
  exact composed_change ha₁ H0 H1 (locGen_precedes_bd g Hl k Zc hZc hk) hδ0 hδε hε hδc hνε hD' hΨ hh
    (E := {x | blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x ∈
      nbhd ⌊R k⌋₊ (Zc : Set (Torus S.d (n (k + 1))))})
    (fun x hx m _ _ => locGen_bd_agree g Hl k Zc hZc hk hx m)

include Hl in
/-- **`realStepAct` as the composed-background difference**: the boundary background restricted to
`Ω₁(G^{Z'})` is the background of the composed datum (`composed_change`), so `realStepAct` is the
expression bounded in `realStep_cubeDiffStar_bound`. -/
theorem realStepAct_eq_composed {a₁ ν δ' ε' : ℝ} (β : ℝ) (ha₁ : 0 < a₁)
    (H0 H1 : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν) (hδ0 : 0 < δ')
    (hδε : δ' ≤ ε') (hε : ε' ≤ bgC0 S.d S.L N) (hδc : δ' ≤ thm73C1 S.d S.L N)
    (hνε : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε' ^ 2 ≤ δ' ^ 2)
    (Q : Finset (Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))))
    (u : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N)
    (hD' : InDomainC (bdGen g Hl k hk) ν δ' ε' (bdDataC g Hl k hk u.1 u.2.1 u.2.2)) :
    realStepAct g Hl k Zc hZc hk a₁ ν β Q u =
      (β : ℂ) * (cubeActionStar (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν Q
          (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).Ψ (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).h
          (bgFieldC (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
            (composeData (locGen_precedes_bd g Hl k Zc hZc hk) (compWeight S.L a₁)
              (bgFieldC (bdGen g Hl k hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
                (bdDataC g Hl k hk u.1 u.2.1 u.2.2)) (bdDataC g Hl k hk u.1 u.2.1 u.2.2))) -
        cubeActionStar (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν Q
          (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).Ψ (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).h
          (bgFieldC (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
            (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2))) := by
  rw [(p6_composed_change g Hl k Zc hZc hk ha₁ H0 H1 hδ0 hδε hε hδc hνε u.1 u.2.1 u.2.2 hD').2.1]
  rfl

/-- **The decoupled expression at `s ≡ 1` is the composed-background difference of the real step.** -/
theorem p6_action_at_one_composed (hM1 : g.M1 = S.L ^ m₁) (hm₁ : 2 ≤ m₁) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁)
    (hN : 5 < g.c * n (k + 1)) {a₁ ν β : ℝ} (hd : 3 ≤ S.d) (hL3 : 3 ≤ S.L) (hν : 0 ≤ ν)
    (hνL : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) (compWeight S.L a₁))
    (hsep : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1))
    {c' BG : ℝ} (hS : Dec2.DecSpecs S.d S.L (Dec2.mixedKc S.d S.L) (Cchi S.d S.L) c' BG)
    (H0 : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν)
    {κ : ℝ} (hκ : 0 ≤ κ) (hMκ : c' * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁)
    {δ0 ε0 δ1 ε1 : ℝ}
    (hδ0 : 0 < δ0) (hδε0 : δ0 ≤ ε0) (hε0 : ε0 ≤ bgC0 S.d S.L N) (hc0 : δ0 ≤ c7 S.d S.L N BG κ)
    (hν0 : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε0 ^ 2 ≤ δ0 ^ 2)
    (hδ1 : 0 < δ1) (hδε1 : δ1 ≤ ε1) (hε1 : ε1 ≤ bgC0 S.d S.L N) (hc1 : δ1 ≤ c7 S.d S.L N BG κ)
    (hν1 : ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε1 ^ 2 ≤ δ1 ^ 2)
    (ha₁ : 0 < a₁) (hδ1c : δ1 ≤ thm73C1 S.d S.L N)
    (u : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N)
    (hD0 : InDomainC (locGen g Hl k Zc hZc hk) ν δ0 ε0 (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2))
    (hD1 : InDomainC (bdGen g Hl k hk) ν δ1 ε1 (bdDataC g Hl k hk u.1 u.2.1 u.2.2))
    (Q : Finset (Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)))) :
    (β : ℂ) * (cubeActionStar (castN (p6_side hM1) (locGen g Hl k Zc hZc hk)) (compWeight S.L a₁) ν
        (castCube (p6_side hM1) Q)
        (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)).Ψ
        (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)).h
        ((castN_precedes (p6_side hM1) (locGen_precedes_bd g Hl k Zc hZc hk)).restrictφ
          (Dec2.decBgField (realCover g Hl k hk hM1)
            (castN (p6_side hM1) (bdGen g Hl k hk)) (compWeight S.L a₁) ν
            (rho4 S.d S.L N BG κ) (fun _ => 1)
            (castBg (p6_side hM1) (bdDataC g Hl k hk u.1 u.2.1 u.2.2)))) -
      cubeActionStar (castN (p6_side hM1) (locGen g Hl k Zc hZc hk)) (compWeight S.L a₁) ν
        (castCube (p6_side hM1) Q)
        (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)).Ψ
        (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)).h
        (Dec2.decBgField (realCover g Hl k hk hM1)
          (castN (p6_side hM1) (locGen g Hl k Zc hZc hk)) (compWeight S.L a₁) ν
          (rho4 S.d S.L N BG κ) (fun _ => 1)
          (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)))) =
    (β : ℂ) * (cubeActionStar (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν Q
          (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).Ψ (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).h
          (bgFieldC (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
            (composeData (locGen_precedes_bd g Hl k Zc hZc hk) (compWeight S.L a₁)
              (bgFieldC (bdGen g Hl k hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
                (bdDataC g Hl k hk u.1 u.2.1 u.2.2)) (bdDataC g Hl k hk u.1 u.2.1 u.2.2))) -
        cubeActionStar (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν Q
          (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).Ψ (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2).h
          (bgFieldC (locGen g Hl k Zc hZc hk) (compWeight S.L a₁) ν (bgC0 S.d S.L N)
            (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2))) :=
  (p6_action_at_one_real' g Hl k Zc hZc hk hM1 hm₁ hM hN hd hL3 hν hνL ha hsep hS H0 hκ hMκ hδ0
    hδε0 hε0 hc0 hν0 hδ1 hδε1 hε1 hc1 hν1 u hD0 hD1 Q).trans
    (realStepAct_eq_composed g Hl k Zc hZc hk β ha₁ H0 H0 hδ1 hδε1 hε1 hδ1c hν1 Q u hD1)

end Balaban.Fluctuation
