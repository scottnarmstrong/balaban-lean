/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42WireAct

/-!
# Aggregation of the cube action differences of the real step over the cubes `b ∈ 𝒬`

FLUCTUATION §4.2, Steps 3-4.  The undecoupled cube differences `act b = F_{Q_b}` of the real step
(`realStepAct`) for a finite family `𝒬` of action cubes `Q_b`, each lying in one `π_{k+1}`-cube
`y0 b` of the component `Z'` with `(y0 b)^{∼4} ⊂ Ω_{k+1}` (the bulk cubes of H7), with *different*
cubes `y0 b`.  On a set `Sdom` of complex fields, all of whose members have their top-layer field in
`Δ^c_{k+1}(y0 b; 1, r)` and the data of the local, cube and boundary families in the domain `𝒟`:

* `realStepAct_bound_agg`: `|F_{Q_b}(u)| ≤ C_F β |Q|_max (r + shift)² e^{-γ_w D}` for all `b ∈ 𝒬`;
* `realStepAct_analytic_agg`: each `F_{Q_b}` is holomorphic on an open `Sdom`.

The mixed cubes `Δ'` near `∂Ω_{k+1}` and the level-`k` cubes off `Ω_{k+1}` are NOT covered: their
regularity transfer is not an instance of `regIneq_transfer` (see `notes` in the ledger row).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.LargeField
  RegionHistory

set_option linter.unusedSectionVars false

section Agg

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hk : k + 1 ≤ K)

include Hl hZc hk in
/-- **The bound on the cube action differences of the real step, over a family `𝒬` of bulk cubes
with different `y0_b`** (Theorem 4.2, Step 3 for all `b ∈ 𝒬`). -/
theorem realStepAct_bound_agg (hd : 3 ≤ S.d) (hL : 3 ≤ S.L) {Cδ : ℝ} (hCδ : 0 ≤ Cδ) :
    ∃ CF Kw δw : ℝ, 0 < CF ∧ 0 < Kw ∧ 0 < δw ∧
      ∀ {B : Type*} {a₁ ν r δ1 ε1 δ0 ε0 δb εb β Qmax : ℝ} (𝒬 : Finset B)
        (y0 : B → Torus S.d (n (k + 1)))
        (Qs : B → Finset (Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))))
        (Sdom : Set (StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N)),
        0 < a₁ →
        BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν →
        2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1) → 0 ≤ r →
        (∀ b ∈ 𝒬, y0 b ∈ (Zc : Set (Torus S.d (n (k + 1))))) →
        (∀ b ∈ 𝒬, nbhd 4 {y0 b} ⊆ (Hl.step k).Omega) →
        0 < δ1 → δ1 ≤ ε1 → ε1 ≤ bgC0 S.d S.L N → δ1 ≤ thm73C1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε1 ^ 2 ≤ δ1 ^ 2 →
        0 < δ0 → δ0 ≤ ε0 → ε0 ≤ bgC0 S.d S.L N → δ0 ≤ bgC1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε0 ^ 2 ≤ δ0 ^ 2 →
        0 < δb → δb ≤ εb → εb ≤ bgC0 S.d S.L N → δb ≤ thm73C1 S.d S.L N →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * εb ^ 2 ≤ δb ^ 2 →
        (∀ u ∈ Sdom,
          InDomainC (locGen g Hl k Zc hZc hk) ν δ1 ε1 (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2) ∧
          InDomainC (bdGen g Hl k hk) ν δb εb (bdDataC g Hl k hk u.1 u.2.1 u.2.2)) →
        (∀ u ∈ Sdom, ∀ b ∈ 𝒬,
          u.2.1 ∈ DeltaC (q := k + 1) (M1 := g.M1) (N₁ := g.c * n (k + 1))
            (L := S.L) (compWeight S.L a₁) ν r u.2.2 g.c (n (k + 1)) (y0 b) ∧
          InDomainC (genCubeLoc g k (y0 b)) ν δ0 ε0
            (liftSingle (genCubeLoc g k (y0 b)) u.2.1 u.2.2)) →
        bgK1 S.d S.L N * δ0 ≤ deltaStar S.d S.L N → bgK1 S.d S.L N * δ0 ≤ δw →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δ1) ≤ deltaStar S.d S.L N →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δ1) ≤ δw →
        bgK1 S.d S.L N * δ1 ≤ deltaStar S.d S.L N → bgK1 S.d S.L N * δ1 ≤ δw →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δb) ≤ deltaStar S.d S.L N →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δb) ≤ δw →
        (∀ b ∈ 𝒬, ∀ x ∈ Qs b, blockMap (S.L ^ (k + 1) * (g.c * g.M1)) (n (k + 1)) x = y0 b) →
        (∀ b ∈ 𝒬, ((Qs b).card : ℝ) ≤ Qmax) →
        (2 * S.d + 2) * (bgK1 S.d S.L N * δb) ≤ Cδ * (r + transferShift S.d S.L N (k + 1) ν Kw δ1
          (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1))) →
        0 ≤ β →
        ∀ b ∈ 𝒬, ∀ u ∈ Sdom,
          ‖realStepAct g Hl k Zc hZc hk a₁ ν β (Qs b) u‖ ≤
            CF * β * Qmax * (r + transferShift S.d S.L N (k + 1) ν Kw δ1
              (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1))) ^ 2 *
              Real.exp (-(gammaW S.d * stepDist S.L g.M1 g.c k ⌊R k⌋₊ (minSep S.L g.M1))) := by
  obtain ⟨CF, Kw, δw, hCF, hKw, hδw, hmain⟩ := realStepAct_bound g Hl k Zc hZc hk hd hL hCδ
  refine ⟨CF, Kw, δw, hCF, hKw, hδw, ?_⟩
  intro B a₁ ν r δ1 ε1 δ0 ε0 δb εb β Qmax 𝒬 y0 Qs Sdom ha₁ H hsep hr hy0 hΩ hδ10 hδε1 hε1 hδ1c hνε1
    hδ00 hδε0 hε0 hδ0c hνε0 hδb0 hδεb hεb hδbc hνεb hDom hDelta hK0 hKw0 hK1 hKw1 hK11 hKw11 hKb
    hKwb hQ hcard hCr hβ b hb u hu
  have h := hmain u (Qs b) ha₁ H hsep (hy0 b hb) (hΩ b hb) hr (hDelta u hu b hb).1 hδ10 hδε1 hε1
    hδ1c hνε1 (hDom u hu).1 hδ00 hδε0 hε0 hδ0c hνε0 (hDelta u hu b hb).2 hδb0 hδεb hεb hδbc hνεb
    (hDom u hu).2 hK0 hKw0 hK1 hKw1 hK11 hKw11 hKb hKwb (hQ b hb) hCr hβ
  refine h.trans ?_
  have h0 : 0 ≤ CF * β := mul_nonneg hCF.le hβ
  have h1 : 0 ≤ (r + transferShift S.d S.L N (k + 1) ν Kw δ1
      (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1))) ^ 2 * Real.exp (-(gammaW S.d *
        stepDist S.L g.M1 g.c k ⌊R k⌋₊ (minSep S.L g.M1))) := by positivity
  have := mul_le_mul_of_nonneg_right (hcard b hb) h1
  have h2 := mul_le_mul_of_nonneg_left this h0
  calc _ = CF * β * ((Qs b).card * ((r + transferShift S.d S.L N (k + 1) ν Kw δ1
          (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1))) ^ 2 * Real.exp (-(gammaW S.d *
            stepDist S.L g.M1 g.c k ⌊R k⌋₊ (minSep S.L g.M1))))) := by ring
    _ ≤ CF * β * (Qmax * ((r + transferShift S.d S.L N (k + 1) ν Kw δ1
          (stepDist S.L g.M1 g.c k 1 (minSep S.L g.M1))) ^ 2 * Real.exp (-(gammaW S.d *
            stepDist S.L g.M1 g.c k ⌊R k⌋₊ (minSep S.L g.M1))))) := by
        rw [← mul_assoc, ← mul_assoc] at *
        exact h2
    _ = _ := by ring

include Hl hZc hk in
/-- **Holomorphy of the cube action differences of the real step on `Sdom`** (open, with local and
boundary data in `𝒟`), for every family of cubes. -/
theorem realStepAct_analytic_agg {a₁ ν β : ℝ}
    (H : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν)
    {B : Type*} (𝒬 : Finset B)
    (Qs : B → Finset (Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1))))
    {Sdom : Set (StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N)} (hs : IsOpen Sdom)
    (hloc : ∀ u ∈ Sdom, InUnionDomainC (locGen g Hl k Zc hZc hk) (bgC0 S.d S.L N)
      (bgC1 S.d S.L N) ν (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2))
    (hbd : ∀ u ∈ Sdom, InUnionDomainC (bdGen g Hl k hk) (bgC0 S.d S.L N) (bgC1 S.d S.L N) ν
      (bdDataC g Hl k hk u.1 u.2.1 u.2.2)) :
    ∀ b ∈ 𝒬, AnalyticOnNhd ℂ (realStepAct g Hl k Zc hZc hk a₁ ν β (Qs b)) Sdom :=
  fun b _ => realStepAct_analytic g Hl k Zc hZc hk H (Qs b) hs hloc hbd

end Agg

end Balaban.Fluctuation
