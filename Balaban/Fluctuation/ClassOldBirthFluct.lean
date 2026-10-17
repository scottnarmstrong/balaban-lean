/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.ClassOldBirthDelta
public import Balaban.Fluctuation.ScaleUniform
import Mathlib.Tactic.Positivity

/-!
# The fluctuation radius `δ₁` is a small multiple of `ε_k`

The fluctuation chart asks `√N ‖cc‖ C c_ψ < δ₁` (`C = covSupConstC`).  The amplitude is
`‖cc‖ ≤ β_k^{-1/2}` and the cutoff is `c_ψ = A₁ (log β_k)^p`.  Since `(log x)^p ≤ (p/u)^p x^u`,
the product is at most `A₁ (p/u)^p β_k^{-(1/2-u)}`.  With `β_k ≥ M L^{(d-2)k}` and
`α ≤ (d-2)(1/2-u)` this is at most `A₁ (p/u)^p M^{-(1/2-u)} L^{-αk} ≤ A₁ (p/u)^p M^{-(1/2-u)} ε_k/α₀`,
so the choice `δ₁ = 2 √N ‖cc‖ C c_ψ` satisfies `δ₁ ≤ c_δ ε_k` as soon as
`2 √N C A₁ (p/u)^p ≤ c_δ α₀ M^{1/2-u}`, a lower bound on `M ≍ β`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

/-- `(log x)^p ≤ (p/u)^p x^u` for `x ≥ 1`, `u > 0`, `p ≥ 1`. -/
theorem log_pow_le_rpow {x u : ℝ} {p : ℕ} (hx : 1 ≤ x) (hu : 0 < u) (hp : 1 ≤ p) :
    Real.log x ^ p ≤ ((p : ℝ) / u) ^ p * x ^ u := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have ht : 0 < u / p := by positivity
  have h1 := Real.log_le_rpow_div (by linarith : 0 ≤ x) ht
  have h0 := Real.log_nonneg hx
  calc Real.log x ^ p ≤ (x ^ (u / p) / (u / p)) ^ p := pow_le_pow_left₀ h0 h1 p
    _ = ((p : ℝ) / u) ^ p * x ^ u := by
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        have : u / p * p = u := by field_simp
        rw [this, div_eq_mul_inv, ← inv_pow, inv_div]
        ring

/-- **The amplitude product is at most `K L^{-αk}`.** -/
theorem amp_le_decay {d L k : ℕ} [NeZero L] {α u A₁ C βk M : ℝ} {p : ℕ} {cc : ℂ} {cψ : ℝ}
    (hL : 1 ≤ (L : ℝ)) (hp : 1 ≤ p) (hu : 0 < u) (hu2 : u < 1 / 2) (hA₁ : 0 ≤ A₁) (hC : 0 ≤ C)
    (hM : 1 < M) (hβk : M * (L : ℝ) ^ (((d : ℝ) - 2) * k) ≤ βk)
    (hcc : ‖cc‖ ≤ βk ^ (-(1 / 2 : ℝ))) (hcψ : cψ = A₁ * Real.log βk ^ p)
    (hαu : α ≤ ((d : ℝ) - 2) * (1 / 2 - u)) (hd : 2 ≤ d) :
    ‖cc‖ * (C * cψ) ≤ C * A₁ * ((p : ℝ) / u) ^ p * M ^ (-(1 / 2 - u)) * (L : ℝ) ^ (-α * k) := by
  have hR : 1 ≤ (L : ℝ) ^ (((d : ℝ) - 2) * k) := by
    apply Real.one_le_rpow hL
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hR0 : 0 < (L : ℝ) ^ (((d : ℝ) - 2) * k) := by linarith
  have hM0 : 0 < M := by linarith
  have hβ1 : 1 ≤ βk := by nlinarith
  have hβ0 : 0 < βk := by linarith
  have hq : 0 < 1 / 2 - u := by linarith
  have hlog := log_pow_le_rpow hβ1 hu hp
  -- ‖cc‖ * cψ ≤ A₁ (p/u)^p βk^{-(1/2-u)}
  have h1 : ‖cc‖ * cψ ≤ A₁ * ((p : ℝ) / u) ^ p * βk ^ (-(1 / 2 - u)) := by
    rw [hcψ]
    calc ‖cc‖ * (A₁ * Real.log βk ^ p) ≤ βk ^ (-(1 / 2 : ℝ)) * (A₁ * (((p : ℝ) / u) ^ p * βk ^ u)) :=
          mul_le_mul hcc (mul_le_mul_of_nonneg_left hlog hA₁) (mul_nonneg hA₁ (pow_nonneg (Real.log_nonneg hβ1) _)) (by positivity)
      _ = A₁ * ((p : ℝ) / u) ^ p * βk ^ (-(1 / 2 - u)) := by
          have : βk ^ (-(1 / 2 : ℝ)) * βk ^ u = βk ^ (-(1 / 2 - u)) := by
            rw [← Real.rpow_add hβ0]; ring_nf
          rw [← this]; ring
  have h2 : βk ^ (-(1 / 2 - u)) ≤ M ^ (-(1 / 2 - u)) * (L : ℝ) ^ (-α * k) := by
    have e1 : βk ^ (-(1 / 2 - u)) ≤ (M * (L : ℝ) ^ (((d : ℝ) - 2) * k)) ^ (-(1 / 2 - u)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hβk (by linarith)
    rw [Real.mul_rpow hM0.le hR0.le, ← Real.rpow_mul (by linarith)] at e1
    refine e1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    apply Real.rpow_le_rpow_of_exponent_le hL
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  calc ‖cc‖ * (C * cψ) = C * (‖cc‖ * cψ) := by ring
    _ ≤ C * (A₁ * ((p : ℝ) / u) ^ p * βk ^ (-(1 / 2 - u))) := mul_le_mul_of_nonneg_left h1 hC
    _ ≤ C * (A₁ * ((p : ℝ) / u) ^ p * (M ^ (-(1 / 2 - u)) * (L : ℝ) ^ (-α * k))) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

theorem one_le_epsTail (j : ℕ) : 1 ≤ epsTail j := by
  unfold epsTail
  have : 0 ≤ ∑' m : ℕ, if j ≤ m then ((m : ℝ) ^ 2)⁻¹ else 0 :=
    tsum_nonneg fun m => by split_ifs <;> positivity
  linarith

/-- **`δ₁ = 2 √N ‖cc‖ C c_ψ` is admissible and at most `c_δ ε_k`.**  Conditions: `L ≥ 1`, `p ≥ 1`,
`0 < u < 1/2`, `‖cc‖ ≤ β_k^{-1/2}`, `c_ψ = A₁ (log β_k)^p`, `β_k ≥ M L^{(d-2)k}`, `M > 1`,
`α ≤ (d-2)(1/2-u)`, and the single size condition `2 √N C A₁ (p/u)^p ≤ c_δ α₀ M^{1/2-u}`
(a lower bound on `M`, that is on `β`).  Here `W = √N ‖cc‖ C c_ψ > 0` is the hypothesis of the
fluctuation chart, and `δ₁` is any number with `δ₁ = 2 W`. -/
theorem delta1_le_of_amp {d L k N : ℕ} [NeZero L] {α α₀ u A₁ C βk M cδ δ₁ : ℝ} {p : ℕ} {cc : ℂ}
    {cψ : ℝ}
    (hL : 1 ≤ (L : ℝ)) (hp : 1 ≤ p) (hu : 0 < u) (hu2 : u < 1 / 2) (hA₁ : 0 ≤ A₁) (hC : 0 ≤ C)
    (hM : 1 < M) (hβk : M * (L : ℝ) ^ (((d : ℝ) - 2) * k) ≤ βk)
    (hcc : ‖cc‖ ≤ βk ^ (-(1 / 2 : ℝ))) (hcψ : cψ = A₁ * Real.log βk ^ p)
    (hαu : α ≤ ((d : ℝ) - 2) * (1 / 2 - u)) (hd : 2 ≤ d) (hα₀ : 0 ≤ α₀) (hcδ : 0 ≤ cδ)
    (hsize : 2 * Real.sqrt N * C * A₁ * ((p : ℝ) / u) ^ p ≤ cδ * α₀ * M ^ (1 / 2 - u))
    (hW : 0 < Real.sqrt N * (‖cc‖ * (C * cψ)))
    (hδ₁ : δ₁ = 2 * (Real.sqrt N * (‖cc‖ * (C * cψ)))) :
    Real.sqrt N * (‖cc‖ * (C * cψ)) < δ₁ ∧ 0 ≤ δ₁ ∧ δ₁ ≤ cδ * epsSeq L α α₀ k := by
  refine ⟨by rw [hδ₁]; linarith, by rw [hδ₁]; linarith, ?_⟩
  have h := amp_le_decay (d := d) (L := L) (k := k) (u := u) (A₁ := A₁) (C := C) (M := M)
    hL hp hu hu2 hA₁ hC hM hβk hcc hcψ hαu hd
  have hM0 : 0 < M := by linarith
  have hMq : 0 < M ^ (1 / 2 - u) := Real.rpow_pos_of_pos hM0 _
  have hEq : (L : ℝ) ^ (-α * k) = ((L : ℝ) ^ (-α)) ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  have hE0 : 0 ≤ ((L : ℝ) ^ (-α)) ^ k := by positivity
  have hneg : M ^ (-(1 / 2 - u)) = (M ^ (1 / 2 - u))⁻¹ := Real.rpow_neg hM0.le _
  have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hK : 2 * Real.sqrt N * (C * A₁ * ((p : ℝ) / u) ^ p * M ^ (-(1 / 2 - u))) ≤ cδ * α₀ := by
    rw [hneg]
    have : 2 * Real.sqrt N * (C * A₁ * ((p : ℝ) / u) ^ p * (M ^ (1 / 2 - u))⁻¹) =
        (2 * Real.sqrt N * C * A₁ * ((p : ℝ) / u) ^ p) / M ^ (1 / 2 - u) := by
      field_simp
    rw [this, div_le_iff₀ hMq]
    exact hsize
  have hep : α₀ * ((L : ℝ) ^ (-α)) ^ k ≤ epsSeq L α α₀ k := by
    unfold epsSeq
    have := one_le_epsTail k
    nlinarith [mul_nonneg hα₀ hE0]
  rw [hδ₁]
  calc 2 * (Real.sqrt N * (‖cc‖ * (C * cψ)))
      ≤ 2 * (Real.sqrt N * (C * A₁ * ((p : ℝ) / u) ^ p * M ^ (-(1 / 2 - u)) * (L : ℝ) ^ (-α * k))) := by
        gcongr
    _ = (2 * Real.sqrt N * (C * A₁ * ((p : ℝ) / u) ^ p * M ^ (-(1 / 2 - u)))) * ((L : ℝ) ^ (-α * k)) := by
        ring
    _ ≤ (cδ * α₀) * ((L : ℝ) ^ (-α * k)) := by
        rw [hEq]; exact mul_le_mul_of_nonneg_right hK hE0
    _ = cδ * (α₀ * ((L : ℝ) ^ (-α)) ^ k) := by rw [hEq]; ring
    _ ≤ cδ * epsSeq L α α₀ k := mul_le_mul_of_nonneg_left hep hcδ

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ : Finset (CTorus d L N₁ m₁ (k + 1))}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {X : Set (CTorus d L N₁ m₁ (k + 1))}

open Classical in
/-- **The birth-domain old-cover expansion with the fluctuation radius `δ₁` chosen.**  The radius
`δ₁ = 2 √N ‖cc‖ C c_ψ` replaces `hδ₁` and `δ₁ ≤ c_δ ε_k`; the hypotheses added are the amplitude
`‖cc‖ ≤ β_k^{-1/2}`, `c_ψ = A₁ (log β_k)^p`, `β_k ≥ M L^{(d-2)k}`, `α ≤ (d-2)(1/2-u)`, and the size
condition `2 √N C A₁ (p/u)^p ≤ c_δ α₀ M^{1/2-u}`. -/
theorem classOldDec_expansion_cover_birth_consts_fluct [NeZero N] {P : Consts} {μ : ℝ}
    {α α₀ c₃ cfl A cδ : ℝ}
    {u A₁ βk M : ℝ} {p : ℕ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀)
    {j : ℕ} {y : CTorus d L N₁ m₁ (k + 1)}
    (hgs : X ⊆ ↑((C.Tm.gs j X).Ω 1) ∧ ∀ i, j < i → (C.Tm.gs j X).Ω i = ∅)
    (hAn : AnalyticOnNhd ℂ
      (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => C.Tm.E j y X p.1 p.2)
      {p | (xiFieldDom (compWeight L a₁) μ (epsSeq L α α₀) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
        (C.Tm.gs j X) p.1 p.2})
    (hBd : ∀ Ψ h, (xiFieldDom (compWeight L a₁) μ (epsSeq L α α₀) : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom j
      (C.Tm.gs j X) Ψ h → ‖C.Tm.E j y X Ψ h‖ ≤ P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X))
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) (hN : L ^ C.m₀ ∣ N₁) (hjk : j ≤ k)
    (hXp : IsPolyDom C.m₀ j X)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    {K : ℕ} {ξ : ℕ → Fin 3 → ℂ} {q c₈ r : ℝ}
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (H' : BgHyp d L (k + 1) ϱ (compWeight L a₁) μ)
    (heps : 0 < eps)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : 0 ≤ c₈) (hs : c₈ * q ≤ 1 - q)
    (hξ : ∀ n, ‖ξ n‖ ≤ c₈ / 4 * q ^ (n + 1))
    (hμ : (μ : ℂ) = ν * ∏ n ∈ Ico j K, ((1 + ξ n 2) / (1 + ξ n 1)))
    (hτr : Real.exp (3 * (c₈ / 4 * (q ^ (j + 1) / (1 - q)))) - 1 < r) (hr : r ≤ 1 / 16)
    (hα₀ : 0 ≤ α₀) (hα0 : 0 ≤ α) (hBG : 0 ≤ BG) (hBG₂ : 0 ≤ BG₂) (hd : 0 < d) (hcδ : 0 ≤ cδ)
    (hLge : 3 ≤ L) (ha : 0 < compWeight L a₁ k) (hp1 : 1 ≤ p) (hu : 0 < u) (hu2 : u < 1 / 2)
    (hA₁ : 0 ≤ A₁) (hM : 1 < M) (hβk : M * (L : ℝ) ^ (((d : ℝ) - 2) * k) ≤ βk)
    (hccβ : ‖cc‖ ≤ βk ^ (-(1 / 2 : ℝ))) (hcψdef : cψ = A₁ * Real.log βk ^ p)
    (hαu : α ≤ ((d : ℝ) - 2) * (1 / 2 - u)) (hd2 : 2 ≤ d)
    (hsize : 2 * Real.sqrt N * covSupConstC d L N (compWeight L a₁ k) κ * A₁ * ((p : ℝ) / u) ^ p ≤
      cδ * α₀ * M ^ (1 / 2 - u))
    (hW : 0 < Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)))
    (hδ₁def : δ₁ = 2 * (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))))
    (hδ₃def : δ₃ = N * composedCloseBound d L N m₁ BG κ (xiC1 d * eps) r₀)
    (hδfldef : δfl = N * (5 * (cK2' d L N (famConst d L BG₂ κ) * δ₁) + δ₁))
    (hc₃def : c₃ = N * (xiC1 d * (L : ℝ) ^ (-α)) * composedCloseBound d L N m₁ BG κ 1 r₀)
    (hcfldef : cfl = N * (5 * cK2' d L N (famConst d L BG₂ κ) + 1) * cδ)
    (hepsK : eps ≤ epsSeq L α α₀ (k + 1)) (hLα : 16 * scaledC0 d ^ 4 ≤ (L : ℝ) ^ α)
    (hcc : 16 * scaledC0 d ^ 2 * xiK2 d L N * (c₃ + cfl) ≤ 1)
    (hAdef : A = α₀ * epsTail 0)
    (hAK : ((N : ℝ) + 1) * cK2 d L N * A ≤ 4)
    (hrK : (1 + 16 * ((N : ℝ) + 1) * cK2 d L N) * r ≤ 1)
    (hsmA : (4 * d + 6) * ((2 * d + 1) * A) ≤ 1) (hc1A : 4 * (xiC1 d * A) ≤ bgC1 d L N)
    (hKA : bgK1 d L N * (xiC1 d * A) + 3 * r ≤ deltaStar d L N)
    (hζA : 8 * A * r ≤ deltaStar d L N) :
    ∃ 𝒦X : Set (CTorus d L N₁ m₁ (k + 1)),
      ∀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1)),
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp C.m₀ j 𝒦X →
        ∀ (hB : BgSetting N Gp Gk (C.Tm.gs j X) a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j) (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f),
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
          RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
        (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
          ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
          flComp hB hF (fun r => (β : ℂ)⁻¹ * C.Tm.E j y X r.1 r.2)
            (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
          ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
            Gp C.m₀ (X1 Gp C.m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
        (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
          Ev Y u = Ev Y u') ∧
        (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
          ‖Ev Y u‖ ≤ (β⁻¹ * P.E₀) *
            Real.exp (-κ₀ * treeLenCovOne C.m₀ j X - 2 * κdec * treeLenCov Gp C.m₀ Y)) ∧
        (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  have hC := covSupConstC_nonneg (N := N) (d := d) (L := L) hd hLge ha κ
  have hL1 : 1 ≤ (L : ℝ) := by
    have : (3 : ℝ) ≤ L := by exact_mod_cast hLge
    linarith
  obtain ⟨hlt, h0, hle⟩ := delta1_le_of_amp (d := d) (L := L) (k := k) (N := N) (α := α)
    (α₀ := α₀) (u := u) (A₁ := A₁) (βk := βk) (M := M) (cδ := cδ) (p := p) hL1 hp1 hu hu2 hA₁
    hC hM hβk hccβ hcψdef hαu hd2 hα₀ hcδ hsize hW hδ₁def
  exact classOldDec_expansion_cover_birth_consts_delta C hm hgs hAn hBd hβ hE₀ hN hjk hXp hk hG hG'
    cc hcψ hMX hdm hα hsm hlt hconn hrow hκ₀ hκdec hκ h1 hlog hκP H H' heps hq0 hq1 hc hs hξ hμ hτr
    hr hα₀ hα0 hBG hBG₂ h0 hd hcδ hδ₃def hδfldef hle hc₃def hcfldef hepsK hLα hcc hAdef hAK hrK
    hsmA hc1A hKA hζA

end Balaban.Fluctuation
