/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.DeltaPhi
public import Balaban.Background.Theorem73
import Mathlib.Tactic.Ring

/-!
# Definition III.6.1: the backgrounds of the window (P7 (2.40), (2.46), (2.50), (2.52))

LF-RECONSTRUCTION §III.6.1.  The multiscale background `ψ⁰_{k₁,k} = ψ(𝔹_{k₁,k}, 𝔹_k(U_k); ψ̃⁰_k)` of
Definition III.6.1 **is** the landed `psiZeroWin` (`composeField` of the lift `psiZeroData` of `ψ̃⁰_k`
through the massless background of `𝔹_k(U_k)`), `δψ` is `deltaPsi`, the window datum is `windowData` and
`δφ_{k₁,k}` is `deltaPhi`.  No second definition of these objects is made; the only new definitions are
the single-scale background `φ⁰_k` (`phiZero`, with multiplier `alphaZero`) and the residual `r`
(`resZero`, `r_z = ψ⁰_k(z) - (Q_k φ⁰_k)(z)` of III.6.1).

Identification lemmas proved here:

* `windowData_eq_composeData`: the window datum is the composed datum of BG (6.2) (`composeData`);
* `isEL_bgField_real`, `isEL_phiZero`: the Euler-Lagrange system of the massless background;
* `isEL_phiZero_window`: `φ⁰_k` restricted to `Ω₁(𝔹_{k₁,k})` solves (EL) for `𝔹_{k₁,k}` with the datum
  `ψ⁰_{k₁,k}` (the second sentence of III.6.1: I-2, `isEL_compose`);
* `bgField_windowData`: `φ_k(𝔹_{k₁,k}; ψ⁰_{k₁,k}) = φ⁰_k` on `Ω₁(𝔹_{k₁,k})` (P7 (2.50); `theorem73_real`);
* `psiZeroWin_sub_blockAvg`: BG (6.2) in the form `ψ⁰_{k₁,k} - Q φ⁰ = (a_p/a_n) L^{2(n-p)} r`, and its
  corollary (2.52): `ψ⁰_{k₁,k} - Q(𝔹_{k₁,k}) φ⁰_k = 0` on every site whose `k`-block has `r = 0`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section Defs

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-- **`φ⁰_k`** (Definition III.6.1): the massless Def-5 background `φ_k(𝔹_k(U_k); ψ̃⁰_k)` of the lift of the
block field `ψ̃⁰_k` of Lemma III.3.3. -/
noncomputable def phiZero (G' : GeneratingSet d L N₀ k ϱ') (a : ℕ → ℝ)
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) : G'.Ω 1 × Fin N → ℂ :=
  bgField G' a 0 (psiZeroData G' ψ0 h)

/-- **`α⁰_k`** (Definition III.6.1): the multiplier of `φ⁰_k`. -/
noncomputable def alphaZero (G' : GeneratingSet d L N₀ k ϱ') (a : ℕ → ℝ)
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) : G'.Ω 1 → ℂ :=
  bgMult G' a 0 (psiZeroData G' ψ0 h)

/-- **`r`** (Definition III.6.1): `r(x) = ψ⁰_k(z) - (Q_k φ⁰_k)(z)` for the `k`-block `z ∋ x` of the
generating set `𝔹_k(U_k)`, written at a site `x`. -/
noncomputable def resZero (G' : GeneratingSet d L N₀ k ϱ') (a : ℕ → ℝ)
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (x : Torus d (N₀ * L ^ k)) (i : Fin N) : ℂ :=
  (psiZeroData G' ψ0 h).Ψ x i - blockAvg G' (phiZero G' a ψ0 h) x i

end Defs

section Ident

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- The window datum of the landed `windowData` is the composed datum of BG (6.2). -/
theorem windowData_eq_composeData (hprec : Precedes G G') (a : ℕ → ℝ)
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ) :
    windowData G G' hprec a ψ0 h =
      composeData hprec a (phiZero G' a ψ0 h) (psiZeroData G' ψ0 h) := by
  classical
  have hΨ : (windowData G G' hprec a ψ0 h).Ψ =
      (composeData hprec a (phiZero G' a ψ0 h) (psiZeroData G' ψ0 h)).Ψ := by
    funext x
    by_cases hx : x ∈ dataSites G
    · simp [windowData, BgData.clip, hx, composeData, psiZeroWin, phiZero]
    · rw [(windowData G G' hprec a ψ0 h).Ψ_zero x hx,
        (composeData hprec a (phiZero G' a ψ0 h) (psiZeroData G' ψ0 h)).Ψ_zero x hx]
  have hh : (windowData G G' hprec a ψ0 h).h =
      (composeData hprec a (phiZero G' a ψ0 h) (psiZeroData G' ψ0 h)).h := by
    funext x
    by_cases hx : x ∈ G.Ω 1
    · have hx' : x ∈ G'.Ω 1 := hprec.mem_Ω1 hx
      simp [windowData, BgData.clip, hx, composeData, psiZeroData, liftSingle_h G' _ _ hx']
    · rw [(windowData G G' hprec a ψ0 h).h_zero x hx,
        (composeData hprec a (phiZero G' a ψ0 h) (psiZeroData G' ψ0 h)).h_zero x hx]
  generalize windowData G G' hprec a ψ0 h = A at hΨ hh ⊢
  generalize composeData hprec a (phiZero G' a ψ0 h) (psiZeroData G' ψ0 h) = B at hΨ hh ⊢
  cases A; cases B
  simp only at hΨ hh
  subst hΨ hh
  rfl

/-- **(EL) for the real background** (I-2, Def-5): for real data in the union domain, `bgField` and
`bgMult` solve the Euler-Lagrange system. -/
theorem isEL_bgField_real {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ' a ν) {D : BgData G' N}
    (hD : InUnionDomainR G' (bgC1 d L N) ν D) :
    IsEL G' a ν D (bgField G' a ν D) (bgMult G' a ν D) := by
  obtain ⟨δ₀, hδ₀, hδ₀c, hD₀⟩ := hD
  obtain ⟨φ, α, hs, -, -, -, hmin, hmu⟩ := bg_real H hδ₀ hδ₀c hD₀
  have hf' : bgField G' a ν D = φ := bgField_eq hmin hmu
  have hm' : bgMult G' a ν D = α := by
    funext x
    unfold bgMult
    rw [hf']
    exact mult_formula hs.1 x
  rw [hf', hm']
  exact hs.1

/-- `(φ⁰_k, α⁰_k)` solves (EL) for `𝔹_k(U_k)` with the datum `lift_k ψ̃⁰_k` (massless). -/
theorem isEL_phiZero {a : ℕ → ℝ} (H : BgHyp d L k ϱ' a 0) {ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)}
    {h : Fin N → ℝ} (hD : InUnionDomainR G' (bgC1 d L N) 0 (psiZeroData G' ψ0 h)) :
    IsEL G' a 0 (psiZeroData G' ψ0 h) (phiZero G' a ψ0 h) (alphaZero G' a ψ0 h) :=
  isEL_bgField_real H hD

/-- **The second sentence of Definition III.6.1** (I-2, `isEL_compose`): the restriction of `φ⁰_k` solves
(EL) for `𝔹_{k₁,k}` with the datum `ψ⁰_{k₁,k}` (`windowData`). -/
theorem isEL_phiZero_window (hprec : Precedes G G') {a : ℕ → ℝ} (ha : ∀ j, 1 ≤ j → j ≤ k → a j ≠ 0)
    (H : BgHyp d L k ϱ' a 0) {ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)} {h : Fin N → ℝ}
    (hD : InUnionDomainR G' (bgC1 d L N) 0 (psiZeroData G' ψ0 h)) :
    IsEL G a 0 (windowData G G' hprec a ψ0 h) (hprec.restrictφ (phiZero G' a ψ0 h))
      (hprec.restrictα (alphaZero G' a ψ0 h)) := by
  rw [windowData_eq_composeData]
  exact isEL_compose hprec a ha 0 _ (isEL_phiZero H hD)

/-- **P7 (2.50), I-2** (`theorem73_real`): `φ_k(𝔹_{k₁,k}; ψ⁰_{k₁,k}) = φ⁰_k` on `Ω₁(𝔹_{k₁,k})`, together
with the multipliers. -/
theorem bgField_windowData {a₁ : ℝ} (ha₁ : 0 < a₁) (H : BgHyp d L k ϱ (compWeight L a₁) 0)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) 0) (hprec : Precedes G G')
    {ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)} {h : Fin N → ℝ}
    (hD : InUnionDomainR G' (thm73C1 d L N) 0 (psiZeroData G' ψ0 h)) :
    bgField G (compWeight L a₁) 0 (windowData G G' hprec (compWeight L a₁) ψ0 h) =
        hprec.restrictφ (phiZero G' (compWeight L a₁) ψ0 h) ∧
      bgMult G (compWeight L a₁) 0 (windowData G G' hprec (compWeight L a₁) ψ0 h) =
        hprec.restrictα (alphaZero G' (compWeight L a₁) ψ0 h) := by
  rw [windowData_eq_composeData]
  exact (theorem73_real ha₁ H H' hprec hD).2.2

/-- **BG (6.2) for the window background (P7 (2.52), second form)**: at `x ∈ Ω₁(𝔹_{k₁,k})`, with `n`, `p`
the layers of `𝔹_{k₁,k}`, `𝔹_k(U_k)` at `x`,
`ψ⁰_{k₁,k}(x) - (Q(𝔹_{k₁,k}) φ⁰_k)(x) = (a_p/a_n) L^{2(n-p)} r(x)`. -/
theorem psiZeroWin_sub_blockAvg (hprec : Precedes G G') (a : ℕ → ℝ)
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (i : Fin N) :
    psiZeroWin G G' a ψ0 h x i - blockAvg G (hprec.restrictφ (phiZero G' a ψ0 h)) x i =
      ((a (G'.layerIndex x) / a (G.layerIndex x) *
          (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G'.layerIndex x) ^ 2) : ℝ) : ℂ) *
        resZero G' a ψ0 h x i := by
  have e1 : blockAvg G (hprec.restrictφ (phiZero G' a ψ0 h)) x i =
      blockMean G (G.layerIndex x) (fun y => svec G' (phiZero G' a ψ0 h) y i) x := by
    unfold blockAvg blockMean
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨hy1, -⟩ := hprec.block_compat hx hy
    have hy2 : y ∈ G'.Ω 1 := hprec.mem_Ω1 hy1
    have s1 := svec_of_mem G (hprec.restrictφ (phiZero G' a ψ0 h)) ⟨y, hy1⟩ i
    have s2 := svec_of_mem G' (phiZero G' a ψ0 h) ⟨y, hy2⟩ i
    exact s1.trans s2.symm
  have e2 : blockAvg G' (phiZero G' a ψ0 h) x i =
      blockMean G' (G'.layerIndex x) (fun y => svec G' (phiZero G' a ψ0 h) y i) x := rfl
  have e3 : psiZeroWin G G' a ψ0 h x i = composeField G G' a (phiZero G' a ψ0 h)
      (psiZeroData G' ψ0 h).Ψ x i := rfl
  rw [e3, composeField_of_mem a _ _ hx i, e1]
  unfold resZero
  rw [e2]
  ring

/-- **(2.52)**: `ψ⁰_{k₁,k} - Q(𝔹_{k₁,k}) φ⁰_k = 0` at a site `x` of `Ω₁(𝔹_{k₁,k})` where `ψ⁰_k - Q_kφ⁰_k`
vanishes (in P7 this is the set `Z_0`, where the stationarity of (2.34) gives `r = 0`). -/
theorem psiZeroWin_sub_blockAvg_eq_zero (hprec : Precedes G G') (a : ℕ → ℝ)
    (ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hr : ∀ i, resZero G' a ψ0 h x i = 0) (i : Fin N) :
    psiZeroWin G G' a ψ0 h x i - blockAvg G (hprec.restrictφ (phiZero G' a ψ0 h)) x i = 0 := by
  rw [psiZeroWin_sub_blockAvg hprec a ψ0 h hx i, hr i, mul_zero]

end Ident

end Balaban.LargeField
