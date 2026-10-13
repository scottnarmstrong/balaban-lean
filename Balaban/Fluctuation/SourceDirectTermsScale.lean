/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SourceSliceScaled
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The direct terms of the zero class on a source slice, and the activity bound at a source

Zero class, central real datum.  The assembler `stepActivityBound_zeroClass_source_of_directTerms`
of the step activity bound at a source `g` needs two `DirectTerms` instances of the physical
expansion: one at the source parameter `0` and one at `g/β`, with their value identities
(`stepActivityBound_zeroClass_source_scale_of_directTerms` states exactly this).  This file
constructs them and removes the condition.

* `sourceDirectTerms_scale`: for the zero class (no old energy terms, no observable terms, no
  `ν`-part) and a slice `η > 0` of sources (`physSΛEta`: data in the chart `Ξ^c`, sources of
  `ℓ¹`-size `≤ η` in the strict unit ball), ONE family of labels `𝒴` and terms `T`, sharply local
  on the slice, and an expanded function `val` with the exact formula

  `val x w σ (D, f) = -β raySrc3(V̂)(x₁, w₁; σ; D) + β ∑_s f_s dirTermSrc(φ̂_s)(x₂, w₂; σ; D)`

  such that at EVERY point `Θ` of the slice there is a `DirectTerms` instance with these labels and
  terms and amplitude `ε_U ≥ prop33EpsEtaScaled(η) · β`.  The labels and the terms do not depend on
  the point of the slice (in particular not on the source); the expanded function is affine in the
  source `f`.  The construction is one call of `interaction_expansion_hat_dm_core_dir_eta_scaled`.
  The slice contains complex data `D` of the chart; only the instances at the real datum
  `rawOf S.D'` are used below.  That each term `T_Y` is affine in the source is NOT stated: the
  landed expansion theorem does not expose it.
* `stepActivityBound_zeroClass_source_scaled`: for a source `g` with `∑ |g| < q ≤ 1` and `β ≥ 1`,
  the two instances at `(rawOf D', 0)` and `(rawOf D', g/β)` on the slice `η = q/β`
  (`sourceSlice_mem_restricted`) give, by the conditional theorem, a `StepActivityBound` of the
  zero class at the source `g` with `κ_H = 2κ_dec - 1`, `K_c = 2K_c'` and
  `ε_H = 4 (β E_sc / r³ + q K / r)`, `E_sc = 3 c₁ (L^{m₀+m₁})^d ‖energyBdScaled‖`, `K = cK2' δ₁`.
  The value identities are the formula of `val` (at the source `0` the source sum vanishes).
* `beta_mul_potentialAmp_le`: `β E_sc / r³ ≤ β_k · 3 c₁ M^d L^d C / r³` with the scale-free
  constant `C = (N/2)(2(1+Q)² + (d+1+ρ₄)Q²) δ₁²` (`a_k ≤ 2`, `L ≥ 3`, `d ≥ 2`).

What is proved: the activity bound of the zero class at every source of the strict `ℓ¹` ball, at
the central real datum `rawOf S.D'`, under the hypotheses of the landed zero-source theorem
`stepActivityBound_zeroClass_direct_scaled` (covers, `FlCore`, `HatConn`, `RowInHat`, radii,
`RayData`) and the doubled smallness.  What is NOT proved here: the family over the relative
complex chart of data (the instances here are at the real datum; the exact identity of the complex
exponents `WoneC + WtwoC` off real data is open), general classes, and the output terms of the
step.  The class enters only through `S.Wone`, `S.Wtwo` of the zero class; no generating set of
class terms appears, so the statements are independent of such a choice.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Metric

section Amplitude

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **The potential part of the physical amplitude is scale-uniform.**  With `a_k ≤ 2`, `L ≥ 3`,
`d ≥ 2`: `β · 3 c₁ M^d ‖energyBdScaled‖ / r³ ≤ β_k · 3 c₁ M^d L^d C / r³`, where
`C = (N/2)(2(1+Q)² + (d+1+ρ)Q²) δ²` and `β_k = S.betaU`. -/
theorem beta_mul_potentialAmp_le (S : StepSetting d L N₁ m₁ k N ϱ) (hd : 2 ≤ d) (hL3 : 3 ≤ L)
    (hak : compWeight L S.a₁ k ≤ 2) (ha0 : 0 ≤ compWeight L S.a₁ k) (hβ : 0 ≤ S.β)
    {Q δ ρ r : ℝ} (hQ : 0 ≤ Q) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hr : 0 < r) (m : ℕ) :
    S.β * (3 * c1 d L * ((L : ℝ) ^ m) ^ d *
        ‖energyBdScaled d L N (compWeight L S.a₁) k (Q * δ) δ ρ‖ / r ^ 3) ≤
      S.betaU * ((3 * c1 d L * ((L : ℝ) ^ m) ^ d *
        ((L : ℝ) ^ d * ((N / 2 : ℝ) * (2 * (1 + Q) ^ 2 + (d + 1 + ρ) * Q ^ 2) * δ ^ 2))) /
          r ^ 3) := by
  have hEb0 := energyBdScaled_nonneg (d := d) (L := L) (N := N) ha0 (mul_nonneg hQ hδ) hδ hρ
  have hbU : 0 ≤ S.betaU := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    unfold StepSetting.betaU
    positivity
  have hE := energyConstScaled_le (N := N) hd hL3 hak (Q := Q) (δ := δ) hρ
  have hM0 : 0 ≤ 3 * c1 d L * ((L : ℝ) ^ m) ^ d / r ^ 3 := by
    have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  have hbm := beta_mul_energyBdScaled S (compWeight L S.a₁) (Q * δ) δ ρ
  rw [Real.norm_of_nonneg hEb0]
  calc S.β * (3 * c1 d L * ((L : ℝ) ^ m) ^ d *
          energyBdScaled d L N (compWeight L S.a₁) k (Q * δ) δ ρ / r ^ 3)
      = (3 * c1 d L * ((L : ℝ) ^ m) ^ d / r ^ 3) *
          (S.β * energyBdScaled d L N (compWeight L S.a₁) k (Q * δ) δ ρ) := by ring
    _ = S.betaU * ((3 * c1 d L * ((L : ℝ) ^ m) ^ d / r ^ 3) *
          energyConstScaled d L N (compWeight L S.a₁) k (Q * δ) δ ρ) := by rw [hbm]; ring
    _ ≤ S.betaU * ((3 * c1 d L * ((L : ℝ) ^ m) ^ d / r ^ 3) *
          ((L : ℝ) ^ d * ((N / 2 : ℝ) * (2 * (1 + Q) ^ 2 + (d + 1 + ρ) * Q ^ 2) * δ ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE hM0) hbU
    _ = _ := by ring

end Amplitude

section Witness

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {c BG κ eps : ℝ}

variable (S : StepSetting d L N₁ m₁ k N ϱ)
    {ρ εU : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsmX : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ)) < δ₁)
    (ha₁ : 0 < S.a₁)
    (H : BgHyp d L (k + 1) ϱ (compWeight L S.a₁) S.ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    -- the covers of the blocks of the potential
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovV : ∀ z, CovSetup S.G' (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZV : ∀ z, readSites (stepG d L N₁ m₁ k ϱ) k z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin S.G' (X₁V z)
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    -- the covers of the sites of the source
    {jF : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {XF 𝒦XF : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁F : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcovF : ∀ s, CovSetup S.G' (m₀) (jF s) (XF s) (𝒦XF s))
    (hX₁F : ∀ s, (↑(X₁F s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' (m₀) (jF s) (𝒦XF s))
    (hoptF : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XF s) ∧ MeetsOne (m₀) (jF s) (𝒦XF s) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jF s)) E₀ = treeLenCovOne (m₀) (jF s) (XF s))
    (hΔF : ∀ s, treeLenCovOne (m₀) (jF s) (XF s) = 0)
    (hlogF : ∀ _s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hyF : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁F s)
    -- the bound on the external field and the block margin of the blocks
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁V z))
    (hN : L ^ m₀ ∣ N₁) (hp : 0 < S.p₁)

include hC hconn hrow hκ₀ hκdec hκ h1 hR₁ hr hcψ hMX hdm hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum' hsm hcovV hX₁V hoptV hΔV hlogV hZV hmarV hcovF hX₁F hoptF hΔF hlogF hyF hBh0 hBh hZν hN

/-- **The direct terms of the zero class on a source slice: one family of labels and terms for
every datum and source of the slice.**  Under the hypotheses of the landed zero-source theorem
that concern the expansion (`FlCore`, `HatConn`, `RowInHat`, the rooted covers of the blocks and
of the source sites, the radii), for a slice `η > 0` and an amplitude
`ε_U ≥ prop33EpsEtaScaled(ρ_E = ρ_M = 0, η) · |β|`:

there are an expanded function `val`, a finite family `𝒴` of domains and terms `T` such that

* `val x w σ (D, f) = -β raySrc3(V̂)(x₁, w₁; σ; D) + β ∑_s f_s dirTermSrc(φ̂_s)(x₂, w₂; σ; D)`
  (the potential part and the source part; affine in the source `f`);
* the terms are sharply local on the slice (`PhysicalSharpLocEta`), and their diagonal values
  `ψ ↦ T_Y((ψ,ψ), (ψ,ψ); σ; Θ)` are continuous at every point `Θ` of the slice (`DiagCont`);
* at every point `Θ` of the slice `physSΛEta S a₁ ν ε η` there is a `DirectTerms` instance for
  `val` with domains `𝒴`, terms `T`, rate `2κ_dec - 1` and amplitude `ε_U`.

The family `(𝒴, T)` is chosen before the point `Θ`: it does not depend on the source. -/
theorem sourceDirectTerms_scale {η : ℝ} (hη0 : 0 < η) (hRσ : 0 < Rσ)
    (hc : (Rσ * R₁ + r) * ρ < cψ)
    (hεb : prop33EpsEtaScaled d L N m₁ k m₀ S.a₁ BG BG₂ κ δ₁ r 0 0 η * ‖(S.β : ℂ)‖ ≤ εU) :
    ∃ (val : ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ℂ → (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : Set (CTorus d L N₁ m₁ (k + 1)) → ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) →
        ((S.U × Fin N → ℂ) × (S.U × Fin N → ℂ)) → ℂ →
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) → ℂ),
      (∀ x w σ p, val x w σ p =
        (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight x.1 w.1 σ p.1 +
        (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
          dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi S.G' S.a₁ S.ν eps
              (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
                (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ p.1)) ∧
      PhysicalSharpLocEta S cψ R₁ Rσ r S.a₁ S.ν eps η 𝒴 T ∧
      DiagCont (fun ψ : S.U × Fin N → ℂ => (ψ, ψ)) (physXW S cψ R₁ Rσ r)
        (physSΛEta S S.a₁ S.ν eps η) Rσ 𝒴 T ∧
      ∀ Θ ∈ physSΛEta S S.a₁ S.ν eps η,
        ∃ I : DirectTerms S m₀ hp (fun ψ => (ψ, ψ)) ρ Rσ εU (2 * κdec - 1) Θ
            (physSΛEta S S.a₁ S.ν eps η) (physXW S cψ R₁ Rσ r) val (physAgΘ S) (AgFDirPair S),
          I.𝒴 = 𝒴 ∧ I.T = T := by
  classical
  obtain ⟨𝒴, T, hD0⟩ := interaction_expansion_hat_dm_core_dir_eta_scaled
    (Kc := Kc) (Cx := Cx) (c₂ := c₂) (BG₂ := BG₂) (δ₁ := δ₁) (hC := hC) (cβ := (S.β : ℂ))
    (hconn := hconn) (hrow := hrow) (κdec := κdec) (κ₀ := κ₀) (hκ₀ := hκ₀) (hκdec := hκdec)
    (hκ := hκ) (h1 := h1) (R₁ := R₁) (hR₁ := hR₁) (r := r) (Rσ := Rσ) (hr := hr) (η := η)
    (hη0 := hη0) (hk := S.hk1) (hG := S.hG) (hG' := S.hG')
    (cc := ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) (cψ := cψ) (hcψ := hcψ) (hMX := hMX) (δc := δc)
    (hdm := hdm) (hα := hα) (hsmX := hsmX) (hδ₁ := hδ₁) (ha₁ := ha₁) (H := H) (hc7 := hc7)
    (R := R) (hR := hR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum')
    (hsm := hsm) (m₀ := m₀) (jV := jV) (XV := XV) (𝒦XV := 𝒦XV) (X₁V := X₁V) (hcovV := hcovV)
    (hX₁V := hX₁V) (hoptV := hoptV) (hΔV := hΔV) (hlogV := hlogV) (hZV := hZV) (hmarV := hmarV)
    (τι := PEmpty.{1}) (𝒯E := (∅ : Finset PEmpty.{1})) (ϱ₁ := fun _ => 0) (ϱ₂ := fun _ => 0)
    (GkE := fun τ => PEmpty.elim τ) (GjE := fun τ => PEmpty.elim τ) (r₀ := 0) (δ₃ := 0)
    (δfl := 0) (X₀E := fun _ => ∅) (X₁E := fun _ => ∅) (jE := fun _ => 0) (XE := fun _ => ∅)
    (𝒦XE := fun _ => ∅) (EbE := fun _ => 0) (EE := fun _ _ => 0)
    (hBE := fun τ hτ => absurd hτ (by simp)) (hFE := fun τ hτ => absurd hτ (by simp))
    (hcovE := fun τ hτ => absurd hτ (by simp)) (hX₁E := fun τ hτ => absurd hτ (by simp))
    (hoptE := fun τ hτ => absurd hτ (by simp)) (hlogE := fun τ hτ => absurd hτ (by simp))
    (hEbE := fun τ hτ => absurd hτ (by simp)) (hEanE := fun τ hτ => absurd hτ (by simp))
    (hEbdE := fun τ hτ => absurd hτ (by simp))
    (jF := jF) (XF := XF) (𝒦XF := 𝒦XF) (X₁F := X₁F) (hcovF := hcovF) (hX₁F := hX₁F)
    (hoptF := hoptF) (hΔF := hΔF) (hlogF := hlogF) (hyF := hyF)
    (μι := PEmpty.{1}) (𝒯M := (∅ : Finset PEmpty.{1})) (ϱ₁M := fun _ => 0) (ϱ₂M := fun _ => 0)
    (GkM := fun τ => PEmpty.elim τ) (GjM := fun τ => PEmpty.elim τ)
    (X₀M := fun _ => ∅) (X₁M := fun _ => ∅) (jM := fun _ => 0) (XM := fun _ => ∅)
    (𝒦XM := fun _ => ∅) (EbM := fun _ => 0) (EM := fun _ _ => 0)
    (ys := fun τ => PEmpty.elim τ) (is := fun τ => PEmpty.elim τ)
    (hys := fun τ hτ => absurd hτ (by simp))
    (hBM := fun τ hτ => absurd hτ (by simp)) (hFM := fun τ hτ => absurd hτ (by simp))
    (hcovM := fun τ hτ => absurd hτ (by simp)) (hX₁M := fun τ hτ => absurd hτ (by simp))
    (hoptM := fun τ hτ => absurd hτ (by simp)) (hlogM := fun τ hτ => absurd hτ (by simp))
    (hEbM := fun τ hτ => absurd hτ (by simp)) (hEanM := fun τ hτ => absurd hτ (by simp))
    (hEbdM := fun τ hτ => absurd hτ (by simp))
    (rE := fun τ => PEmpty.elim τ) (hrE := fun τ hτ => absurd hτ (by simp))
    (ρE := 0) (hρE0 := le_rfl) (hρE := fun x => by simp) (ρM := 0) (hρM0 := le_rfl)
    (hρM := fun p => by simp) (Bh := Bh) (hBh0 := hBh0) (hBh := hBh) (cν := (0 : ℂ)) (hZν := hZν)
  have hS : PhysicalSharpLocEta S cψ R₁ Rσ r S.a₁ S.ν eps η 𝒴 T :=
    fun Y hY xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' hag h1' h2' =>
      hD0.loc.loc Y hY xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' hag h1' h2'
  have hD1 := (hD0.congr_val (val' := fun x w σ p =>
      (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
        (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν eps)) taylorWeight x.1 w.1 σ p.1 +
      (S.β : ℂ) * (∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N, p.2 s.1 s.2 *
        dirTermSrc (hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (onXi S.G' S.a₁ S.ν eps
            (fun D ψ' => svec (stepG d L N₁ m₁ k ϱ)
              (flFieldOne S.G' (stepG d L N₁ m₁ k ϱ) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
          (fun _ => (1 : ℂ)) x.2 w.2 σ p.1))
      (fun xw _ σ _ Θ _ => by
        simp only [Finset.sum_empty, mul_zero, add_zero, zero_mul])).mono
    (b' := fun Y : Set (CTorus d L N₁ m₁ (k + 1)) =>
      prop33EpsEtaScaled d L N m₁ k m₀ S.a₁ BG BG₂ κ δ₁ r 0 0 η * ‖(S.β : ℂ)‖ *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
    (fun Y => by simp only [norm_zero, zero_mul, add_zero]; exact le_rfl)
  have hD := hD1.comap (F' := (unitPts S.G' × Fin N → ℂ) × (unitPts S.G' × Fin N → ℂ)) id
    (XW' := physXW S cψ R₁ Rσ r) (fun xw h => h) (AgF' := AgFPair S)
    (fun Y a a' h => agFDirPair_of_agFPair S h) (e' := fun ψ => (ψ, ψ)) (fun _ => rfl)
  refine ⟨_, 𝒴, T, fun x w σ p => rfl, hS, hD.cont, fun Θ hΘ => ⟨
    { 𝒴 := 𝒴
      T := T
      b := fun Y : Set (CTorus d L N₁ m₁ (k + 1)) =>
        prop33EpsEtaScaled d L N m₁ k m₀ S.a₁ BG BG₂ κ δ₁ r 0 0 η * ‖(S.β : ℂ)‖ *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y)
      loc := { hD.loc with loc := hS }
      dom := hD.dom
      bd := fun Y _ => mul_le_mul_of_nonneg_right hεb (Real.exp_pos _).le
      mem := hΘ
      agΘ := fun Y => ⟨fun x _ => ⟨rfl, rfl⟩, fun x _ => rfl⟩
      xw := fun ψ hψ => ⟨hatRaysO_pair S hψ hRσ.le (by linarith) hr.le hc,
        hatRaysO_pair S hψ hRσ.le (by linarith) hr.le hc⟩
      ag := fun Y hY Φ Φ' h => by
        have h' := S.agHatFDir_hatOf m₀ (cell_subset_of_isDj hN (hD.dom Y hY)) ρ hp Φ Φ' h
        exact ⟨h', h'⟩
      meas := fun Y hY σ hσ => by
        have hcont := hD.cont Y hY σ hσ Θ hΘ
        refine (continuousOn_iff_continuous_domRestrict.1 (hcont.mono ?_)).measurable
        intro ψ hψ
        exact ⟨hatRaysO_pair S hψ hRσ.le (by linarith) hr.le hc,
          hatRaysO_pair S hψ hRσ.le (by linarith) hr.le hc⟩ }, rfl, rfl⟩⟩

variable (hD : XiCData S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps S.D')
    (hpρ : S.p₁ ≤ ρ) (hεpos : 0 < εU)
    {κ0 κ' Kc' : ℝ}
    (hκE : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc') (hκ' : 0 ≤ κ')
    (hκa : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1)
    (hDA : 2 * (2 * εU) ≤ 1 / (8 * (2 * Kc') ^ 3 * c1 d L *
      Real.exp ((2 * κdec - 1 - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    {pp : ℝ} (R0 : S.RayData pp) (hlt : S.p₁ < pp)

include hp hD hpρ hεpos hκE hKc hκ' hκa hDA R0 hlt

/-- **The step activity bound of the zero class at a physical source.**  Under the hypotheses of
the landed zero-source theorem `stepActivityBound_zeroClass_direct_scaled` (with `R_σ = 2`, no
amplitude hypothesis on an auxiliary slice), for `β ≥ 1` and every source `g` with
`∑ |g| < q ≤ 1` (complex `g`; `q = 1` is the whole strict `ℓ¹` ball): if `ε_U` is the physical
amplitude `β · prop33EpsEtaScaled(η = q/β)` and the doubled smallness
`2 (2 ε_U) ≤ 1 / (8 (2K_c')³ c₁ exp((2κ_dec - 1 - 2κ₀) c_G + c₁ + κ' c_G))` holds, there is a step
activity bound of the zero class at the source `g`, with `κ_H = 2κ_dec - 1`, `K_c = 2K_c'` and
`ε_H = 4 (β E_sc / r³ + q K / r)`, `E_sc = 3 c₁ (L^{m₀+m₁})^d ‖energyBdScaled‖`, `K = cK2' δ₁`.
Central real datum `rawOf S.D'`; zero class. -/
theorem stepActivityBound_zeroClass_source_scaled (g : Fld d L N₁ m₁ (k + 1) N) {q : ℝ}
    (hg : ∑ x, ∑ i, ‖g x i‖ < q) (hq : q ≤ 1) (hβ : 1 ≤ S.β)
    (hc : ((2 : ℝ) * R₁ + r) * ρ < cψ)
    (hεU : εU = S.β * prop33EpsEtaScaled d L N m₁ k m₀ S.a₁ BG BG₂ κ δ₁ r 0 0 (q / S.β)) :
    ∃ B : StepActivityBound S (zeroClass d L N₁ m₁ k N ϱ) g,
      B.κH = 2 * κdec - 1 ∧ B.Kc = 2 * Kc' ∧
      B.εH = 4 * (S.β * (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
          (rho4 d L N BG κ)‖ / r ^ 3) +
        q * (cK2' d L N (famConst d L BG₂ κ) * δ₁) / r) := by
  have hβ0 : 0 < S.β := by linarith
  have hq0 : 0 < q := lt_of_le_of_lt
    (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => norm_nonneg _) hg
  have hη0 : 0 < q / S.β := div_pos hq0 hβ0
  have hnβ : ‖(S.β : ℂ)‖ = S.β := by rw [Complex.norm_real, Real.norm_of_nonneg hβ0.le]
  obtain ⟨val, 𝒴, T, hval, -, -, hI⟩ := sourceDirectTerms_scale S (ρ := ρ) (εU := εU) hC hconn hrow
    hκ₀ hκdec hκ h1 hR₁ hr hcψ hMX hdm hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum' hsm hcovV
    hX₁V hoptV hΔV hlogV hZV hmarV hcovF hX₁F hoptF hΔF hlogF hyF hBh0 hBh hZν hN hp hη0
    (by norm_num : (0 : ℝ) < 2) hc (by rw [hnβ, hεU, mul_comm])
  obtain ⟨I₀, -, -⟩ := hI _ (mk_mem_physSΛEta S S.a₁ S.ν eps hη0.le hD)
  obtain ⟨Ig, -, -⟩ := hI (rawOf S.D', fun y i => g y i / (S.β : ℂ))
    ⟨⟨S.D', hD, rfl⟩, sourceSlice_mem_restricted hβ hg hq⟩
  exact stepActivityBound_zeroClass_source_scale_of_directTerms S hC hR₁ hr hcψ hMX hdm hα hsmX
    hδ₁ hc7 hR hRs hsmall hnum hnum' hsm (by norm_num : (0 : ℝ) < 2) hc hD hN hp hpρ hεpos hκE
    hKc hκ' hκa hDA R0 hlt (by norm_num : (1 : ℝ) < 2) g I₀ Ig
    (fun x u => by rw [hval]; simp)
    (fun x u => hval _ _ _ _) rfl hβ0.ne' hεU

end Witness

end Balaban.Fluctuation
