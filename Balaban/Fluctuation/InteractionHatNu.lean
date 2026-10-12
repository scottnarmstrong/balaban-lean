/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionHatF
public import Balaban.Fluctuation.Prop33Nu
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The `ν`-part of the localized interaction in the variable `ψ̂`

The hat version of `Prop33Nu`: the block functionals of the mass variation `V_{ν,1}` are expanded by
`i5_functional_hat` (terms local in `ψ̂`), and `nupart_locInt_phys_hat` is `nupart_locInt_phys`
with that locality, resummed over the blocks to the volume-independent bound
`C e^{-(2 κ_dec - 1) d^cov_{k+1}(Y)}`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix Set Metric

section NuHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The block functional of `V_{ν,1}` expands over the domains `Y ⊃ X₁`, with terms local in
`ψ̂`.** -/
theorem nublock_expansion_hat (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hZ : (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑X₁f) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        nuBlockFun Gp Hm k z (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D (hatLift Gp a₁ ν hG' cc D ψh))
          (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
          ∑ Y ∈ polyDom Gp X₁f m₀ j 𝒦X, Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHat hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hB1 : 0 ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by
    have hK4 : 0 < K4 d L N BG κ := K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0
    have hx1 := one_le_xiC1 d
    have hx2 := hC.eps_pos
    have hx3 : 0 ≤ xiC1 d * eps := by positivity
    have hx4 := mul_nonneg hK4.le hx3
    linarith
  have hEb : 0 ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) := by
    unfold nuBd; positivity
  obtain ⟨Ev, h1', h2', h3', h4'⟩ := i5_functional_hat hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov
    hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEb (Φ := nuBlockFun Gp Hm k z)
    ((nuBlockFun_analytic (Gp := Gp) (Hm := Hm) k z).mono (Set.subset_univ _))
    (fun t ht => by
      rw [hΔ]; simpa using nuBlockFun_bound hC le_rfl hG' hBh0 hBh z ht)
    (Z := ↑(blockSites d L N₁ m₁ (k + 1) k z)) (Zα := ∅) hZ
    (fun x hx => absurd hx (Set.notMem_empty x))
    (fun t _ t' _ hφ _ hδ hag _ => nuBlockFun_local k z hφ hδ hag)
  refine ⟨Ev, h1', h2', fun Y u hu => ?_, h4'⟩
  have := h3' Y u hu
  rw [hΔ] at this
  simpa using this

end NuHat

section NuPartHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
variable {j : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
variable {X 𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
variable {X₁z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ : ℕ}

/-- **The `ν`-part of the localized interaction in the variable `ψ̂`**: `σ ∫₀¹ ω(t') ∂_w V_{ν,1}`
along a `ψ̂`-ray, with `V_{ν,1}` along the decoupled fluctuation (`nuTotal`), is a localized
expansion over the domains `Y ⊃ X₁(z)`. -/
theorem nupart_locInt_hat_dm (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) T
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
          (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ'))) ω x₀ w σ Θ)
        (fun Y => Mω * ((∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
          nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  classical
  have hex : ∀ z, ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        nuBlockFun Gp Hm k z (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D (hatLift Gp a₁ ν hG' cc D ψh))
          (rawOf D, hatLift Gp a₁ ν hG' cc D ψh) =
          ∑ Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHat hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) :=
    fun z => nublock_expansion_hat hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hBh0 hBh (hcov z)
      (hX₁ z) hconn hrow (hopt z) (hΔ z) hκ₀ hκdec hκ h1 hlog z (hZ z)
  choose Ev hsum hloc hbd han using hex
  refine ⟨fun Y x₀ w σ Θ => dirTerm (fun u => ∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
    Ev z Y u else 0) ω x₀ w σ Θ, ?_⟩
  have hanO : ∀ z Y, AnalyticOnNhd ℂ (Ev z Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      hatBall (N := N) Gp cψ) := fun z Y =>
    (han z Y).mono (Set.prod_mono le_rfl (hatBall_subset cψ))
  have hd : 3 ≤ d := hC.HBp.hd
  have hanS : ∀ Y, AnalyticOnNhd ℂ
      (fun u => ∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then Ev z Y u else 0)
      (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ hatBall (N := N) Gp cψ) := by
    intro Y u hu
    refine Finset.analyticAt_fun_sum _ fun z _ => ?_
    by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
    · simpa only [hY, ite_true] using hanO z Y u hu
    · simp only [hY, ite_false]; exact analyticAt_const
  refine LocIntDm.mk (locInt_dir1 (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (B := hatBall (N := N) Gp cψ)
    (f := hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
      (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ')))
    (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z))
    (Evs := fun Y u => ∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then Ev z Y u else 0)
    (b := fun Y => ∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
      nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
        (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
        Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0)
    (AgΘ := fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
    (AgF := AgHatF Gp hG') (Rσ := Rσ) hR₁ hω hωc hMω hωb hr
    (isOpen_hatBall cψ) ?_ ?_ ?_ ?_ ?_) ?_ ?_
  · intro Y u hu
    refine Finset.analyticAt_fun_sum _ fun z _ => ?_
    by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
    · simpa only [hY, ite_true] using hanO z Y u hu
    · simp only [hY, ite_false]; exact analyticAt_const
  · intro Y u hu
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
    by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
    · simpa only [hY, ite_true] using hbd z Y u ⟨hu.1, hatBall_subset cψ hu.2⟩
    · simp [hY]
  · intro Y a a' c' c'' p q ha hb y hy i
    simp [ha y hy i, hb y hy i]
  · intro Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2'
    refine Finset.sum_congr rfl fun z'' _ => ?_
    by_cases hY : Y ∈ polyDom Gp (X₁z z'') m₀ (j z'') (𝒦X z'')
    · simp only [hY, ite_true]
      exact hloc z'' Y (Θ, z) ⟨hΘ, hatBall_subset cψ hz⟩ (Θ', z')
        ⟨hΘ', hatBall_subset cψ hz'⟩ ⟨h1', h2'⟩
    · simp [hY]
  · rintro Θ ⟨D, hD, rfl⟩ ψh hψ
    rw [hatFun_rawOf hG' cc _ hD, onXi_rawOf hD, ← sum_nuBlockFun (n := k) a₁ ν BG₂ κ D _,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hsum z D hD ψh (hatBall_subset cψ hψ), Finset.sum_ite_mem,
      Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem
        (fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) (Finset.mem_univ z))]
  · intro Y hY
    obtain ⟨z₀, -, hz₀⟩ := Finset.mem_biUnion.1 hY
    exact isDj_of_polyDom hG' (hcov z₀) hd (hopt z₀) hz₀
  · exact diagCont_dirTerm _ hR₁ hωc hr hanS

/-- **The `ν`-part of the localized interaction in the variable `ψ̂`**: `σ ∫₀¹ ω(t') ∂_w V_{ν,1}`
along a `ψ̂`-ray, with `V_{ν,1}` along the decoupled fluctuation (`nuTotal`), is a localized
expansion over the domains `Y ⊃ X₁(z)`. -/
theorem nupart_locInt_hat (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) T
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
          (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ'))) ω x₀ w σ Θ)
        (fun Y => Mω * ((∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
          nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  obtain ⟨T, h⟩ := nupart_locInt_hat_dm hC hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsm hδ₁ (Bh := Bh) hBh0 hBh hcov hX₁ hconn hrow hopt hΔ (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 hlog hZ (ω := ω) hωc (R₁ := R₁) hR₁ hω (Mω := Mω) hMω hωb (r := r) (Rσ := Rσ) hr
  exact ⟨T, h.loc⟩

end NuPartHat

section NuBoundHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
variable {j : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
variable {X 𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
variable {X₁z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ : ℕ}

/-- **The `ν`-part in the variable `ψ̂` with the volume-uniform bound**
`C e^{-(2 κ_dec - 1) d^cov_{k+1}(Y)}` (the hat version of `nupart_locInt_bound`). -/
theorem nupart_locInt_bound_hat_dm (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) T
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
          (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ'))) ω x₀ w σ Θ)
        (fun Y => Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
          nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hB1 : 0 ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by
    have hK4 : 0 < K4 d L N BG κ := K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0
    have hx1 := one_le_xiC1 d
    have hx2 := hC.eps_pos
    have hx3 : 0 ≤ xiC1 d * eps := by positivity
    have hx4 := mul_nonneg hK4.le hx3
    linarith
  have hEb : 0 ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) := by
    unfold nuBd; positivity
  obtain ⟨T, hT⟩ := nupart_locInt_hat_dm hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hBh0 hBh hcov hX₁
    hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog hZ hωc hR₁ hω hMω hωb hr (Rσ := Rσ)
  refine ⟨T, hT.mono_on fun Y hY => ?_⟩
  obtain ⟨z₀, -, hz₀⟩ := Finset.mem_biUnion.1 hY
  have hMD := polyDom_isMultiDom (hcov z₀) hd (hopt z₀) hz₀
  have hcard : ((Finset.univ.filter fun z => Y ∈ polyDom Gp (X₁z z) m₀ (j z)
      (𝒦X z)).card : ℝ) ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) := by
    refine card_blocks_filter_le hG' le_rfl (hcov z₀).hN hMD _ (fun z hz => ?_)
    have h1' := subset_polyDom (Finset.mem_filter.1 hz).2
    rw [← hX₁ z] at h1'
    exact fun x hx => h1' (hZ z hx)
  have ht0 := treeLenCov_nonneg Gp m₀ Y
  have hv : 0 ≤ nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
        Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) := by positivity
  have hs := sum_ite_card_le _ hv hcard
  rw [← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
  have key := one_add_mul_exp_le (treeLenCov Gp m₀ Y) κdec
  have hCn : 0 ≤ Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
      nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
        (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) := by positivity
  calc Mω * ((∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
          nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0) / r)
      ≤ Mω * ((c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) *
          (nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y))) / r) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs hr.le) hMω
    _ = (Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
          nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) *
          ((1 + treeLenCov Gp m₀ Y) * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key hCn

/-- **The `ν`-part in the variable `ψ̂` with the volume-uniform bound**
`C e^{-(2 κ_dec - 1) d^cov_{k+1}(Y)}` (the hat version of `nupart_locInt_bound`). -/
theorem nupart_locInt_bound_hat (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) T
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
          (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ'))) ω x₀ w σ Θ)
        (fun Y => Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
          nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  obtain ⟨T, h⟩ := nupart_locInt_bound_hat_dm hC hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsm hδ₁ (Bh := Bh) hBh0 hBh hcov hX₁ hconn hrow hopt hΔ (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 hlog hZ (ω := ω) hωc (R₁ := R₁) hR₁ hω (Mω := Mω) hMω hωb (r := r) (Rσ := Rσ) hr
  exact ⟨T, h.loc⟩

end NuBoundHat

section NuPhysHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
variable {j : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
variable {X 𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
variable {X₁z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
variable {m₀ : ℕ}

/-- **The mass variation `V_{ν,1}` in the hat variable is `nuTotal` along the decoupled
fluctuation**: on realizable data and a bounded hat variable,
`nuOne (Θ, ψ'(Θ, ψ̂)) = nuTotal (D, ψ'(D, ψ̂))`. -/
theorem hatFun_nuOne_eq (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (ha₁ : 0 < a₁) (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' le_rfl (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    {D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    hatFun Gp a₁ ν eps hG' cc (nuOne hG hG' le_rfl a₁ ν eps) (rawOf D', ψh) =
      hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
        (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ')) (rawOf D', ψh) := by
  classical
  have hmem := hatLift_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hD hψh
  rw [hatFun_rawOf hG' cc _ hD, hatFun_rawOf hG' cc _ hD]
  obtain ⟨D, hh, htan, hdisc⟩ := hreal D' hD _ hmem.1 hmem.2
  have hψ : compTangent hG hG' le_rfl (compWeight L a₁)
      (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D ∈ FlBall Hm δ₁ := by
    rw [htan]; exact hmem.1
  rw [onXi_rawOf hD, ← htan, nuOne_eq hG hG' le_rfl hD hh]
  exact massVar_one_eq_nuTotal hC hG hG' le_rfl ha₁ H D' hD hc7 D hh hψ hR hdisc hRs hsmall hnum
    hnum'

/-- **The `ν`-part of Proposition 3.3 in the variable `ψ̂`** (the hat version of
`nupart_locInt_phys`): the physical mass variation `V_{ν,1}` (`nuOne`, the exact `massVar`),
along a `ψ̂`-ray, `σ ∫₀¹ ω(t') ∂_w V_{ν,1}`, is a localized expansion over the domains `Y ⊃ X₁(z)`
with the bound `C e^{-(2 κ_dec - 1) d^cov_{k+1}(Y)}`; the terms are local in `ψ̂`. -/
theorem nupart_locInt_phys_hat (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (ha₁ : 0 < a₁) (H : BgHyp d L (k + 1) ϱm (compWeight L a₁) ν)
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' le_rfl (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' le_rfl) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))) ⊆
      ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ T : Set (CTorus d L N₁ m₁ (k + 1)) → (unitPts Gp × Fin N → ℂ) →
        (unitPts Gp × Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) T
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc
          (nuOne hG hG' le_rfl a₁ ν eps)) ω x₀ w σ Θ)
        (fun Y => Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
          nuBd d L N k (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  classical
  obtain ⟨T, hT⟩ := nupart_locInt_bound_hat hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hBh0 hBh hcov
    hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog hZ hωc hR₁ hω hMω hωb hr (Rσ := Rσ)
  refine ⟨T, hT.congr_val ?_⟩
  rintro ⟨x₀, w⟩ hxw σ hσ Θ ⟨D', hD, rfl⟩
  unfold dirTermSrc
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp only
  congr 1
  refine lineD_congr_line hr ?_
  intro τ hτ
  have ht' : ‖(t : ℂ)‖ < R₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  have hz1 : (σ * (t : ℂ)) • x₀ + τ • w ∈ hatBall (N := N) Gp cψ := hxw σ hσ t ht' τ hτ.le
  exact (hatFun_nuOne_eq hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ ha₁ H hc7 hR hRs hsmall hnum hnum'
    hreal hD (hatBall_subset cψ hz1))

end NuPhysHat

end Balaban.Localization
