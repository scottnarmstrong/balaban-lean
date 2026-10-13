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

* `sourceDirectTerms_slice`: for the zero class (no old energy terms, no observable terms, no
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
* `Balaban.Inhabited.sourceDirectTerms_scale`: the statement of `sourceDirectTerms_slice` at the
  step `hatStepK k m₁ hk ν β p₁ δ` of every scale (`d = L = 3`, `N = 2`), on the slice `η = q/β`
  with the physical amplitude `β · prop33EpsEtaScaled(η = q/β)`, with the constants `m₁, t, δ, β₀`
  and `BG, BG₂, κ` chosen before the scale, the torus, the mass, `β`, the cutoff, `q` and the
  source; the slice contains `(rawOf S.D', 0)` and `(rawOf S.D', g/β)` for `∑ |g| < q ≤ 1`.  These
  are the two witnesses of the conditional theorem, with one family of domains and terms.

What is proved: zero class; the activity bound at every source of the strict `ℓ¹` ball, at the
central real datum `rawOf S.D'` only, under the hypotheses of the landed zero-source theorem
`stepActivityBound_zeroClass_direct_scaled` (covers, `FlCore`, `HatConn`, `RowInHat`, radii,
`RayData`) and the doubled smallness.  What is NOT proved here: the family of activities over the
relative complex chart of data (leaves 5, 9, 10 of `notes/phase1/SRCACT.md`) and the uniform chart
(STEPOUT package 1).  The `DirectTerms` instances exist at every datum of the chart, but the
identification of `val` with the step exponents is used, and landed, at the real datum only; the
identity for the complex exponents `WoneC + WtwoC` off real data is open.  Also not proved:
general classes and the output terms of the step.  The class enters only through `S.Wone`,
`S.Wtwo` of the zero class; no generating set of class terms appears, so the statements are
independent of the choice of generating sets for class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.Analysis Finset Matrix Set
  Metric

section RadiusSlice

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L]

/-- **The scaled source slice at radius `ρ`.**  `∑ |g| < q ≤ ρ` and `max 1 ρ ≤ β` give
`g/β ∈ l1BallEta (q/β)`.  (This is the statement of `sourceSlice_mem_restricted_rho` of
`Balaban.Fluctuation.SourceRadius`, which cannot be imported here: that file depends on this one.) -/
theorem sourceSlice_mem_restricted_radius {ρ β q : ℝ} (hβ : max 1 ρ ≤ β)
    {g : CTorus d L N₁ m₁ K → Fin N → ℂ} (hg : ∑ x, ∑ i, ‖g x i‖ < q) (hq : q ≤ ρ) :
    (fun y i => g y i / (β : ℂ)) ∈ l1BallEta d L N₁ m₁ K N (q / β) := by
  have hβ1 : 1 ≤ β := le_trans (le_max_left _ _) hβ
  have hβρ : ρ ≤ β := le_trans (le_max_right _ _) hβ
  have hβ0 : 0 < β := by linarith
  have hsum : ∑ x, ∑ i, ‖g x i / (β : ℂ)‖ = (∑ x, ∑ i, ‖g x i‖) / β := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hβ0.le]
  have h1 : (∑ x, ∑ i, ‖g x i‖) / β < q / β := div_lt_div_of_pos_right hg hβ0
  have h2 : q / β ≤ 1 := by
    rw [div_le_one hβ0]; linarith
  exact ⟨by rw [l1Ball, Set.mem_ofPred_eq, hsum]; exact lt_of_lt_of_le h1 h2, by rw [hsum]; exact h1.le⟩

end RadiusSlice

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

The family `(𝒴, T)` is chosen before the point `Θ`: it does not depend on the source.

The last conjunct is the differentiability of the terms along the complex hat ray `ζ ↦ ζ ψ̂` on
`‖ζ‖ < 3/2`, at every datum of the slice and every hat field `ψ̂` with
`(R₁ + r) (3/2) ‖ψ̂‖ ≤ cψ`. -/

theorem sourceDirectTerms_slice_ray {η : ℝ} (hη0 : 0 < η) (hRσ : 0 < Rσ)
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
      (∀ Θ ∈ physSΛEta S S.a₁ S.ν eps η,
        ∃ I : DirectTerms S m₀ hp (fun ψ => (ψ, ψ)) ρ Rσ εU (2 * κdec - 1) Θ
            (physSΛEta S S.a₁ S.ν eps η) (physXW S cψ R₁ Rσ r) val (physAgΘ S) (AgFDirPair S),
          I.𝒴 = 𝒴 ∧ I.T = T) ∧
      ∀ (Y : Set (CTorus d L N₁ m₁ (k + 1)))
        (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)),
        Θ ∈ physSΛEta S S.a₁ S.ν eps η → ∀ ψ : S.U × Fin N → ℂ,
        (∀ p, (R₁ + r) * (3 / 2) * ‖ψ p‖ ≤ cψ) →
        DifferentiableOn ℂ (fun ζ : ℂ => T Y (ζ • ψ, ζ • ψ) (ζ • ψ, ζ • ψ) 1 Θ)
          (ball (0 : ℂ) (3 / 2)) := by
  classical
  obtain ⟨𝒴, T, hD0, hrayD⟩ := interaction_expansion_hat_dm_core_dir_eta_scaled_ray
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
          hatRaysO_pair S hψ hRσ.le (by linarith) hr.le hc⟩ }, rfl, rfl⟩,
    fun Y Θ hΘ ψ hψ => hrayD Y Θ hΘ ψ hψ⟩

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
theorem sourceDirectTerms_slice {η : ℝ} (hη0 : 0 < η) (hRσ : 0 < Rσ)
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
  exact (sourceDirectTerms_slice_ray S (hC := hC) (hconn := hconn) (hrow := hrow) (hκ₀ := hκ₀) (hκdec := hκdec) (hκ := hκ) (h1 := h1) (hR₁ := hR₁) (hr := hr) (hcψ := hcψ) (hMX := hMX) (hdm := hdm) (hα := hα) (hsmX := hsmX) (hδ₁ := hδ₁) (ha₁ := ha₁) (H := H) (hc7 := hc7) (hR := hR) (hRs := hRs) (hsmall := hsmall) (hnum := hnum) (hnum' := hnum') (hsm := hsm) (hcovV := hcovV) (hX₁V := hX₁V) (hoptV := hoptV) (hΔV := hΔV) (hlogV := hlogV) (hZV := hZV) (hmarV := hmarV) (hcovF := hcovF) (hX₁F := hX₁F) (hoptF := hoptF) (hΔF := hΔF) (hlogF := hlogF) (hyF := hyF) (hBh0 := hBh0) (hBh := hBh) (hZν := hZν) (hN := hN) (hp := hp) hη0 hRσ hc hεb).imp fun _ => Exists.imp fun _ => Exists.imp fun _ h =>
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

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
amplitude hypothesis on an auxiliary slice), for `β ≥ max 1 ρs` and every source `g` with
`∑ |g| < q ≤ ρs` (complex `g`; `q = 1` is the whole strict `ℓ¹` ball): if `ε_U` is the physical
amplitude `β · prop33EpsEtaScaled(η = q/β)` and the doubled smallness
`2 (2 ε_U) ≤ 1 / (8 (2K_c')³ c₁ exp((2κ_dec - 1 - 2κ₀) c_G + c₁ + κ' c_G))` holds, there is a step
activity bound of the zero class at the source `g`, with `κ_H = 2κ_dec - 1`, `K_c = 2K_c'` and
`ε_H = 4 (β E_sc / r³ + q K / r)`, `E_sc = 3 c₁ (L^{m₀+m₁})^d ‖energyBdScaled‖`, `K = cK2' δ₁`.
Central real datum `rawOf S.D'`; zero class. -/
theorem stepActivityBound_zeroClass_source_scaled_rho (g : Fld d L N₁ m₁ (k + 1) N) {q : ℝ}
    (hg : ∑ x, ∑ i, ‖g x i‖ < q) {ρs : ℝ} (hq : q ≤ ρs) (hβ : max 1 ρs ≤ S.β)
    (hc : ((2 : ℝ) * R₁ + r) * ρ < cψ)
    (hεU : εU = S.β * prop33EpsEtaScaled d L N m₁ k m₀ S.a₁ BG BG₂ κ δ₁ r 0 0 (q / S.β)) :
    ∃ B : StepActivityBound S (zeroClass d L N₁ m₁ k N ϱ) g,
      B.κH = 2 * κdec - 1 ∧ B.Kc = 2 * Kc' ∧
      B.εH = 4 * (S.β * (3 * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
          (rho4 d L N BG κ)‖ / r ^ 3) +
        q * (cK2' d L N (famConst d L BG₂ κ) * δ₁) / r) := by
  have hβ1 : 1 ≤ S.β := le_trans (le_max_left _ _) hβ
  have hβ0 : 0 < S.β := by linarith
  have hq0 : 0 < q := lt_of_le_of_lt
    (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => norm_nonneg _) hg
  have hη0 : 0 < q / S.β := div_pos hq0 hβ0
  have hnβ : ‖(S.β : ℂ)‖ = S.β := by rw [Complex.norm_real, Real.norm_of_nonneg hβ0.le]
  obtain ⟨val, 𝒴, T, hval, -, -, hI⟩ := sourceDirectTerms_slice S (ρ := ρ) (εU := εU) hC hconn hrow
    hκ₀ hκdec hκ h1 hR₁ hr hcψ hMX hdm hα hsmX hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum' hsm hcovV
    hX₁V hoptV hΔV hlogV hZV hmarV hcovF hX₁F hoptF hΔF hlogF hyF hBh0 hBh hZν hN hp hη0
    (by norm_num : (0 : ℝ) < 2) hc (by rw [hnβ, hεU, mul_comm])
  obtain ⟨I₀, -, -⟩ := hI _ (mk_mem_physSΛEta S S.a₁ S.ν eps hη0.le hD)
  obtain ⟨Ig, -, -⟩ := hI (rawOf S.D', fun y i => g y i / (S.β : ℂ))
    ⟨⟨S.D', hD, rfl⟩, sourceSlice_mem_restricted_radius hβ hg hq⟩
  exact stepActivityBound_zeroClass_source_scale_of_directTerms S hC hR₁ hr hcψ hMX hdm hα hsmX
    hδ₁ hc7 hR hRs hsmall hnum hnum' hsm (by norm_num : (0 : ℝ) < 2) hc hD hN hp hpρ hεpos hκE
    hKc hκ' hκa hDA R0 hlt (by norm_num : (1 : ℝ) < 2) g I₀ Ig
    (fun x u => by rw [hval]; simp)
    (fun x u => hval _ _ _ _) rfl hβ0.ne' hεU

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
  have hβ' : max 1 (1 : ℝ) ≤ S.β := by rw [max_self]; exact hβ
  apply stepActivityBound_zeroClass_source_scaled_rho (ρs := 1) (g := g) (hg := hg)
    (κ₀ := κ₀) (κ0 := κ0) (κ' := κ') (Kc' := Kc') (Bh := Bh) (hq := hq) (hβ := hβ') (hc := hc) (hεU := hεU) <;> assumption


end Witness

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology

open Classical in
/-- **The direct terms of the zero class at every scale, on the source slice `η = q/β`: the two
witnesses of the source assembler.**  With `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`: there
are `m₁, t, δ, β₀` and the tower constants `BG, BG₂, κ` such that for every scale `k ≥ 1`, torus
parameter `3 ∣ N₁ > 5`, mass `0 < ν`, `ν · 3^{2(k+1)} ≤ 1`, `β ≥ β₀`, `max 1 ρ ≤ β`, cutoff
`0 < p₁ ≤ A₁ (log β_k)^p` and `0 < q ≤ ρ`, at the step `S = hatStepK k m₁ hk ν β p₁ δ`, with
`c_ψ = lvCpsi κ t β_k`, `r = lvR κ t β_k p₁`, `R_σ = R₁ = 2`, cover scale `m₀ = 1` and the physical
amplitude `ε_U = β · prop33EpsEtaScaled(ρ_E = ρ_M = 0, η = q/β)`:

there are an expanded function `val`, domains `𝒴` and terms `T` such that

* `val x w σ (D, f) = -β raySrc3(V̂)(x₁, w₁; σ; D) + β ∑_s f_s dirTermSrc(φ̂_s)(x₂, w₂; σ; D)`;
* the terms are sharply local and diagonally continuous on the slice;
* at every point `Θ` of the slice there is a `DirectTerms` instance for `val` with domains `𝒴`,
  terms `T`, rate `2κ_dec - 1` and amplitude `ε_U`;
* the slice contains `(rawOf S.D', 0)` and, for every complex source `g` with `∑ |g| < q`,
  `(rawOf S.D', g/β)`.

Hence the two witnesses `I₀` (source parameter `0`) and `I_g` (source parameter `g/β`) of
`stepActivityBound_zeroClass_source_scale_of_directTerms` exist, with the same domains and terms,
and their value identities `hval₀`, `hvalg` are the formula of `val` at the diagonal hat variable
(at the source `0` the source sum vanishes).  The constants do not depend on `k`, `N₁`, `ν`, `β`,
`p₁`, `q`, `g`. -/
theorem sourceDirectTerms_scale_rho {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10)) :
    ∃ (m₁ : ℕ) (t δ β₀ BG BG₂ κ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β → ∀ ρ : ℝ, 0 < ρ → max 1 ρ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ ρ →
      ∀ S : StepSetting 3 3 N₁ m₁ k 2 (rhoSep m₁),
        S = hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ → ∀ hp : 0 < S.p₁,
        ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (𝒴 : Finset (Set (CTorus 3 3 N₁ m₁ (k + 1))))
          (T : Set (CTorus 3 3 N₁ m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
          (∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν t)) taylorWeight x.1 w.1 σ Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν t
                  (fun D ψ' => svec (stepG 3 3 N₁ m₁ k (rhoSep m₁))
                    (flFieldOne S.G' (stepG 3 3 N₁ m₁ k (rhoSep m₁)) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
          PhysicalSharpLocEta S (lvCpsi κ t (β * 3 ^ k)) 2 2 (lvR κ t (β * 3 ^ k) p₁) S.a₁ S.ν t
            (q / S.β) 𝒴 T ∧
          DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
            (physXW S (lvCpsi κ t (β * 3 ^ k)) 2 2 (lvR κ t (β * 3 ^ k) p₁))
            (physSΛEta S S.a₁ S.ν t (q / S.β)) 2 𝒴 T ∧
          (∀ Θ ∈ physSΛEta S S.a₁ S.ν t (q / S.β),
            ∃ I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 m₁ k 1 S.a₁ BG BG₂ κ t
                  (lvR κ t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * κdec - 1) Θ
                (physSΛEta S S.a₁ S.ν t (q / S.β))
                (physXW S (lvCpsi κ t (β * 3 ^ k)) 2 2 (lvR κ t (β * 3 ^ k) p₁)) val (physAgΘ S)
                (AgFDirPair S),
              I.𝒴 = 𝒴 ∧ I.T = T) ∧
          (rawOf S.D', (0 : CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) ∈
            physSΛEta S S.a₁ S.ν t (q / S.β) ∧
          ∀ g : Fld 3 3 N₁ m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
            (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν t (q / S.β) := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  have hc1 := one_le_c1 3 3
  have hent := aEnt_nonneg 3 3
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, δc, h4, ht0, ⟨hC₀⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ :=
    tower_core_rates 2 (κ0 := κ0) (κdec := κdec) (by rw [hκ0def]) (by rw [hκdecdef]; linarith)
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have hκdec0 : 0 ≤ κdec := by linarith
    have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := scale_C_items hA p m₁ h4 hbig κ ht0 hδ hsm hδ'0 hδ'a hδ'b hδ'c
  have hxi1 : xiC1 3 * t ≤ 1 := by
    have h1 := hC₀.c7le
    have h2 := c7_le_bgC1 3 3 2 BG κ
    have h3 := bgC1_le_small 3 3 2 (by norm_num)
    linarith
  refine ⟨m₁, t, δ, β₀t, BG, BG₂, κ, hβ₀t, ht0, hδ, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβt ρ hρ hβρ p₁ hp0 hp₁ q hq0 hq S hS hp
  subst hS
  have hν0 : 0 ≤ ν := hνpos.le
  have hβ1 : 1 ≤ β := le_trans (le_max_left _ _) hβρ
  have hβ0 : 0 < β := by linarith
  obtain ⟨hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems k hk N₁ hN ν hν0 hν β hβt p₁ hp0 hp₁
  have hSD := dgSetting_lv (N₁ := N₁) (k := k) h4 hN hν0 hν
  have hHB := bgHyp_lv (k := k) m₁ hν0 hν
  have hC : FlCore 2 (lvTop N₁ m₁ k (rhoSep m₁)) (lvLow N₁ m₁ k (rhoSep m₁)) 1 ν c BG κ t
      (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t :=
    flCore_level_transfer hC₀ hSD (opSetting_lv h4 hN hν0 hν) (isLevel_lvLow hk) isLevel_lvTop hHB
  have hBh := hBh_of_xi (N := 2) (Gp := lvTop N₁ m₁ k (rhoSep m₁)) hHB hνpos hC.small1
    hC.eps_pos hxi1
  have hD : XiCData (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1 t
      (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D' := by
    refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
      exists_xiC hHB (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (massLe_lv hν) ht0, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2)).h x i = _
      rw [this]; simp
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  obtain ⟨hV, hF⟩ := LocalCover.levelLocalCover (N := 2) (lvLow N₁ m₁ k (rhoSep m₁)) hSD
    (isLevel_lvTop (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := rhoSep m₁)) (m₀ := 1) le_rfl hN3
  have hBh0 : (0 : ℝ) ≤ 1 + 2 / ν := by positivity
  have hη0 : 0 < q / β := div_pos hq0 hβ0
  obtain ⟨val, 𝒴, T, hval, hloc, hcont, hI⟩ := sourceDirectTerms_slice
    (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ)
    (ρ := p₁) (εU := β * prop33EpsEtaScaled 3 3 2 m₁ k 1 1 BG BG₂ κ t
      (lvR κ t (β * 3 ^ k) p₁) 0 0 (q / β))
    (Rσ := 2) (R₁ := 2) (r := lvR κ t (β * 3 ^ k) p₁) (R := 2) (m₀ := 1) (κdec := κdec)
    (κ₀ := κ0) (Bh := 1 + 2 / ν) (δc := δc) (cψ := lvCpsi κ t (β * 3 ^ k))
    (jV := fun _ => k) (XV := fun z => LocalCover.cube 1 k (LocalCover.blockSite k z))
    (𝒦XV := fun z => LocalCover.fam 1 (LocalCover.blockSite k z))
    (X₁V := fun z => LocalCover.nbhdF 1 (LocalCover.blockSite k z))
    (jF := fun _ => k) (XF := fun s => LocalCover.cube 1 k s.1)
    (𝒦XF := fun s => LocalCover.fam 1 s.1) (X₁F := fun s => LocalCover.nbhdF 1 s.1)
    (hC := hC) (hconn := hatConn_lvTop) (hrow := rowInHat_lv hk h4 hN hν0 hν)
    (hκ₀ := hκ0) (hκdec := hκdec) (hκ := by exact_mod_cast hκ) (h1 := h1)
    (hR₁ := by norm_num) (hr := hr0) (hcψ := hcψ0.le) (hMX := hMX) (hdm := hdm) (hα := hα)
    (hsmX := hsmX) (hδ₁ := hδ₁) (ha₁ := one_pos) (H := hHB) (hc7 := hc7) (hR := le_rfl)
    (hRs := g1) (hsmall := g2) (hnum := g3) (hnum' := g4) (hsm := g5)
    (hcovV := fun z => (hV z).1) (hX₁V := fun z => (hV z).2.1)
    (hoptV := fun z => (hV z).2.2.1) (hΔV := fun z => (hV z).2.2.2.1)
    (hlogV := fun _ => hlog) (hZV := fun z => (hV z).2.2.2.2.1)
    (hmarV := fun z => (hV z).2.2.2.2.2.1)
    (hcovF := fun s => (hF s).1) (hX₁F := fun s => (hF s).2.1)
    (hoptF := fun s => (hF s).2.2.1) (hΔF := fun s => (hF s).2.2.2.1)
    (hlogF := fun _ => hlog) (hyF := fun s => (hF s).2.2.2.2)
    (hBh0 := hBh0) (hBh := hBh) (hZν := fun z => (hV z).2.2.2.2.2.2)
    (hN := hN3) (hp := hp) (η := q / β) (hη0 := hη0) (hRσ := by norm_num) (hc := hc)
    (hεb := by
      have hnβ : ‖(((hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).β : ℝ) : ℂ)‖ = β := by
        rw [Complex.norm_real]; exact Real.norm_of_nonneg hβ0.le
      rw [hnβ, mul_comm]
      exact le_of_eq rfl)
  exact ⟨val, 𝒴, T, hval, hloc, hcont, hI,
    mk_mem_physSΛEta (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t hη0.le hD,
    fun g hg => ⟨⟨_, hD, rfl⟩, sourceSlice_mem_restricted_radius hβρ hg hq⟩⟩

open Classical in
/-- **The direct terms of the zero class at every scale, on the source slice `η = q/β`: the two
witnesses of the source assembler.**  With `κ₀ = a_Ent + 1`, `κ_dec = 100 (κ₀ + c₁ + 10)`: there
are `m₁, t, δ, β₀` and the tower constants `BG, BG₂, κ` such that for every scale `k ≥ 1`, torus
parameter `3 ∣ N₁ > 5`, mass `0 < ν`, `ν · 3^{2(k+1)} ≤ 1`, `β ≥ β₀`, cutoff
`0 < p₁ ≤ A₁ (log β_k)^p` and `0 < q ≤ 1`, at the step `S = hatStepK k m₁ hk ν β p₁ δ`, with
`c_ψ = lvCpsi κ t β_k`, `r = lvR κ t β_k p₁`, `R_σ = R₁ = 2`, cover scale `m₀ = 1` and the physical
amplitude `ε_U = β · prop33EpsEtaScaled(ρ_E = ρ_M = 0, η = q/β)`:

there are an expanded function `val`, domains `𝒴` and terms `T` such that

* `val x w σ (D, f) = -β raySrc3(V̂)(x₁, w₁; σ; D) + β ∑_s f_s dirTermSrc(φ̂_s)(x₂, w₂; σ; D)`;
* the terms are sharply local and diagonally continuous on the slice;
* at every point `Θ` of the slice there is a `DirectTerms` instance for `val` with domains `𝒴`,
  terms `T`, rate `2κ_dec - 1` and amplitude `ε_U`;
* the slice contains `(rawOf S.D', 0)` and, for every complex source `g` with `∑ |g| < q`,
  `(rawOf S.D', g/β)`.

Hence the two witnesses `I₀` (source parameter `0`) and `I_g` (source parameter `g/β`) of
`stepActivityBound_zeroClass_source_scale_of_directTerms` exist, with the same domains and terms,
and their value identities `hval₀`, `hvalg` are the formula of `val` at the diagonal hat variable
(at the source `0` the source sum vanishes).  The constants do not depend on `k`, `N₁`, `ν`, `β`,
`p₁`, `q`, `g`. -/
theorem sourceDirectTerms_scale {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {κ0 κdec : ℝ} (hκ0def : κ0 = aEnt 3 3 + 1) (hκdecdef : κdec = 100 * (κ0 + c1 3 3 + 10)) :
    ∃ (m₁ : ℕ) (t δ β₀ BG BG₂ κ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ 0 < δ ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      ∀ S : StepSetting 3 3 N₁ m₁ k 2 (rhoSep m₁),
        S = hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ → ∀ hp : 0 < S.p₁,
        ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (𝒴 : Finset (Set (CTorus 3 3 N₁ m₁ (k + 1))))
          (T : Set (CTorus 3 3 N₁ m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2 × (CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) → ℂ),
          (∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν t)) taylorWeight x.1 w.1 σ Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν t
                  (fun D ψ' => svec (stepG 3 3 N₁ m₁ k (rhoSep m₁))
                    (flFieldOne S.G' (stepG 3 3 N₁ m₁ k (rhoSep m₁)) BG₂ κ S.a₁ S.ν D ψ') s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
          PhysicalSharpLocEta S (lvCpsi κ t (β * 3 ^ k)) 2 2 (lvR κ t (β * 3 ^ k) p₁) S.a₁ S.ν t
            (q / S.β) 𝒴 T ∧
          DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
            (physXW S (lvCpsi κ t (β * 3 ^ k)) 2 2 (lvR κ t (β * 3 ^ k) p₁))
            (physSΛEta S S.a₁ S.ν t (q / S.β)) 2 𝒴 T ∧
          (∀ Θ ∈ physSΛEta S S.a₁ S.ν t (q / S.β),
            ∃ I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 m₁ k 1 S.a₁ BG BG₂ κ t
                  (lvR κ t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * κdec - 1) Θ
                (physSΛEta S S.a₁ S.ν t (q / S.β))
                (physXW S (lvCpsi κ t (β * 3 ^ k)) 2 2 (lvR κ t (β * 3 ^ k) p₁)) val (physAgΘ S)
                (AgFDirPair S),
              I.𝒴 = 𝒴 ∧ I.T = T) ∧
          (rawOf S.D', (0 : CTorus 3 3 N₁ m₁ (k + 1) → Fin 2 → ℂ)) ∈
            physSΛEta S S.a₁ S.ν t (q / S.β) ∧
          ∀ g : Fld 3 3 N₁ m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
            (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∈ physSΛEta S S.a₁ S.ν t (q / S.β) := by
  obtain ⟨m₁, t, δ, β₀, BG, BG₂, κ, h1, h2, h3, H⟩ := sourceDirectTerms_scale_rho hA p hκ0def hκdecdef
  refine ⟨m₁, t, δ, β₀, BG, BG₂, κ, h1, h2, h3, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβt p₁ hp0 hp₁ q hq0 hq S hS hp
  exact H k hk N₁ h3N hN ν hνpos hν β hβt 1 one_pos (by rw [max_self]; linarith) p₁ hp0 hp₁ q hq0 hq S hS hp


end Balaban.Inhabited
