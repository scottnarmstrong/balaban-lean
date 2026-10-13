/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedHatRows
public import Balaban.Fluctuation.HatEngineFan

/-!
# The masked decoupled tangent: ball, layer constancy and analyticity (`MARK-BALL`, `MARK-AN`)

For the decoupled hat construction (cut parameters `s`, `|s_P| < e^κ`) the masked tangent
`markedHatPsiF … Z u t s Θ ψ̂ = u • hatPsiF … + t • liftC (M_Z (cc • C^{1/2}(s) ψ̂))` is the lift of the
unit-lattice field `u • w + t • M_Z w`, `w = cc • C^{1/2}(s) ψ̂`.

* `markedHatPsiF_eq_liftC`, `norm_markedHatPsiF_le` (pointwise bound by `(|u| + |t|)` times the
  unmarked value), `hatSqrtF_coord_le` (the coordinate bound `|w(q)| ≤ |cc| · C_sup · c_ψ` proved in
  `hatPsiF_mem_flBallLC`, here as a separate lemma);
* `isLayerConstant_markedHatPsiF`: layer constancy;
* `markedHatPsiF_mem_flBallLC` (`MARK-BALL`): under the hypotheses of `hatPsiF_mem_flBallLC`, with its
  last inequality replaced by `(|u| + |t|) · √N · (|cc| · C_sup · c_ψ) < δ₁`, the masked tangent lies
  in `FlBallLC Hm δ₁` at every cut of the polydisc; `markedDisc_hatPsiF_mem_flBallLC` is the form
  for the discs `|u| < R_σ`, `|t| < t₁`, `|ρ| < R₁`, `|τ| ≤ r` of `markedDisc_mem_flBallLC`;
  `isOpen_markedRadiusSet` and `mem_markedRadiusSet` give the open neighbourhood of the circles;
  `markedHatPsiF_one_mem_flBallLC` is the check at the cut point `s ≡ 1`;
* `analyticAt_markedHatPsiF_of_decDom`, `analyticOnNhd_markedHatPsiF` (`MARK-AN`): joint analyticity
  in `(Θ, ψ̂, s, u, t)`.

`MARK-FAN`, `MARK-COUNT` (decoupled) and `MARK-PARAM` are NOT proved here; no mark family is
constructed; nothing depends on a choice of generating sets for the class terms.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section Ball

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- The masked tangent is the lift of `u • w + t • M_Z w`, `w = cc • C^{1/2}(s) ψ̂`. -/
theorem markedHatPsiF_eq_liftC (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Z : Finset (unitPts Gp)) (u t : ℂ) (s : DecParams Gp)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gp × Fin N → ℂ) :
    markedHatPsiF a₁ ν hG' cc F₁ Z u t s Θ ψh =
      liftC hG' (u • (cc • (hatSqrtF Gp a₁ ν F₁ s Θ *ᵥ ψh)) +
        t • maskBlock Z (cc • (hatSqrtF Gp a₁ ν F₁ s Θ *ᵥ ψh))) := by
  unfold markedHatPsiF hatPsiF
  simp only [map_add, map_smul]

/-- A scalar multiple of the masked tangent is the masked tangent with scaled parameters. -/
theorem smul_markedHatPsiF (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Z : Finset (unitPts Gp)) (σ u t : ℂ) (s : DecParams Gp)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gp × Fin N → ℂ) :
    σ • markedHatPsiF a₁ ν hG' cc F₁ Z u t s Θ ψh =
      markedHatPsiF a₁ ν hG' cc F₁ Z (σ * u) (σ * t) s Θ ψh := by
  unfold markedHatPsiF
  rw [smul_add, smul_smul, smul_smul]

/-- **Pointwise bound (T1).**  At every site and coordinate the masked tangent is at most
`(|u| + |t|)` times the unmarked tangent. -/
theorem norm_markedHatPsiF_le (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Z : Finset (unitPts Gp)) (u t : ℂ) (s : DecParams Gp)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gp × Fin N → ℂ)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    ‖markedHatPsiF a₁ ν hG' cc F₁ Z u t s Θ ψh y i‖ ≤
      (‖u‖ + ‖t‖) * ‖hatPsiF Gp a₁ ν hG' cc F₁ s Θ ψh y i‖ := by
  rw [markedHatPsiF_apply, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  by_cases hy : unitPt hG' y ∈ Z
  · simpa [hy] using norm_add_le u t
  · simp [hy]

/-- The Euclidean norm at a unit point does not increase under the mask. -/
theorem vn_maskBlock_le (Z : Finset (unitPts Gp)) (w : unitPts Gp × Fin N → ℂ) (b : unitPts Gp) :
    vn (fun i => maskBlock Z w (b, i)) ≤ vn (fun i => w (b, i)) := by
  classical
  unfold maskBlock
  by_cases h : b ∈ Z
  · simp [h]
  · simp only [h, ite_false]
    have : (fun i : Fin N => (0 : ℂ)) = 0 := rfl
    simp only [this, vn_zero]
    exact vn_nonneg _

/-- The Euclidean norm of the masked field at a unit point is at most `|u| + |t|` times that of `w`. -/
theorem vn_marked_le (Z : Finset (unitPts Gp)) (u t : ℂ) (w : unitPts Gp × Fin N → ℂ)
    (b : unitPts Gp) :
    vn (fun i => (u • w + t • maskBlock Z w) (b, i)) ≤ (‖u‖ + ‖t‖) * vn (fun i => w (b, i)) := by
  have h1 : (fun i => (u • w + t • maskBlock Z w) (b, i)) =
      u • (fun i => w (b, i)) + t • (fun i => maskBlock Z w (b, i)) := by
    funext i; simp
  rw [h1]
  refine (vn_add _ _).trans ?_
  rw [vn_smul', vn_smul']
  have := vn_maskBlock_le Z w b
  have h0 := vn_nonneg (fun i => w (b, i))
  nlinarith [norm_nonneg u, norm_nonneg t, mul_le_mul_of_nonneg_left this (norm_nonneg t)]

/-- **Layer constancy (T2).**  The masked tangent is layer-constant (the mask acts on the unit
lattice before the lift). -/
theorem isLayerConstant_markedHatPsiF (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Z : Finset (unitPts Gp)) (u t : ℂ) (s : DecParams Gp)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gp × Fin N → ℂ) :
    IsLayerConstant Hm (markedHatPsiF a₁ ν hG' cc F₁ Z u t s Θ ψh) := by
  rw [markedHatPsiF_eq_liftC]
  exact isLayerConstant_liftC hG hG' _

/-- **Coordinate bound** (the intermediate estimate of `hatPsiF_mem_flBallLC`): on the cut polydisc
and for `|ψ̂| ≤ c_ψ`, every coordinate of the unit field `cc • C^{1/2}(s) ψ̂` is at most
`|cc| · C_sup · c_ψ`. -/
theorem hatSqrtF_coord_le (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) {ψh : unitPts Gp × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (q : unitPts Gp × Fin N) :
    ‖(cc • (hatSqrtF Gp a₁ ν F₁ s (rawOf D) *ᵥ ψh)) q‖ ≤
      ‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ) := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  obtain ⟨φ, α, hI, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hs P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D :=
    inUnionDomainC_of_inDomainC hC.HBp hδ0 hδ0' hδ1 hDom
  have hFeq := hF₁ s D hs hU φ α hI
  have hdec := decDom_of_isDecBg hC hs hD hI hmar hα
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin d L N BG κ (xiC1 d * eps) := by
      have : 0 < K4 d L N BG κ := K4_pos hC.hS.fam.2.1 hd0
      unfold decDomMargin; positivity
    linarith
  have hX : XSetting Gp (compWeight L a₁) a₁ ν := xSetting_of_flCore hC hk
  have hsup := decCovSqrt_supNorm (N := N) hX hC.hκ.le hMX hδc hsm hdec ψh (c := cψ) hcψ hψh
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have := hsup q
  unfold hatSqrtF
  rw [hFeq]
  exact this

/-- **`MARK-BALL`.**  Under the hypotheses of `hatPsiF_mem_flBallLC` (with its last inequality
replaced by the radius inequality below) the masked decoupled tangent lies in `FlBallLC Hm δ₁` at
every cut `s` of the polydisc `|s_P| < e^κ`, for all complex `u, t` with
`(|u| + |t|) · √N · (|cc| · C_sup · c_ψ) < δ₁`. -/
theorem markedHatPsiF_mem_flBallLC (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1))
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) {ψh : unitPts Gp × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (Z : Finset (unitPts Gp)) {u t : ℂ}
    (hδ : (‖u‖ + ‖t‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁) :
    markedHatPsiF a₁ ν hG' cc F₁ Z u t s (rawOf D) ψh ∈ FlBallLC Hm δ₁ := by
  rw [markedHatPsiF_eq_liftC]
  refine liftC_mem_flBallLC hG hG' fun b => ?_
  set w := cc • (hatSqrtF Gp a₁ ν F₁ s (rawOf D) *ᵥ ψh) with hw
  have hcoord := hatSqrtF_coord_le hC hk cc hcψ hMX hmar hα hsm hF₁ hs hD hψh
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : vn (fun i : Fin 0 => (u • w + t • maskBlock Z w) (b, i)) = 0 := by
      rw [vn_eq_sqrt]; simp
    rw [this]; exact hC.δ₁_pos
  · have hV : 0 ≤ ‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ) :=
      (norm_nonneg _).trans (hcoord ⟨b, ⟨0, hN⟩⟩)
    have h1 := vn_le_sqrt_mul hV (fun i => hcoord (b, i))
    refine lt_of_le_of_lt ((vn_marked_le Z u t w b).trans ?_) hδ
    exact mul_le_mul_of_nonneg_left h1 (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- **`MARK-BALL`, discs of the Cauchy estimate** (the arrangement of `markedDisc_mem_flBallLC`):
if `(R₁ + r)(R_σ + t₁) · B < δ₁`, `B = √N · (|cc| · C_sup · c_ψ)`, then for `|u| < R_σ`, `|t| < t₁`,
`|ρ| < R₁`, `|τ| ≤ r` and every cut of the polydisc, `(ρ + τ) • markedHatPsiF … ∈ FlBallLC Hm δ₁`. -/
theorem markedDisc_hatPsiF_mem_flBallLC (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1))
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) {ψh : unitPts Gp × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (Z : Finset (unitPts Gp))
    {R₁ r Rσ t₁ : ℝ}
    (hB : 0 ≤ Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)))
    (h : (R₁ + r) * (Rσ + t₁) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    {u t ρ τ : ℂ} (hu : ‖u‖ < Rσ) (ht : ‖t‖ < t₁) (hρ : ‖ρ‖ < R₁) (hτ : ‖τ‖ ≤ r) :
    (ρ + τ) • markedHatPsiF a₁ ν hG' cc F₁ Z u t s (rawOf D) ψh ∈ FlBallLC Hm δ₁ := by
  rw [smul_markedHatPsiF]
  refine markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hmar hα hsm hF₁ hs hD hψh Z ?_
  have hsτ : ‖(ρ + τ) * u‖ + ‖(ρ + τ) * t‖ ≤ (R₁ + r) * (Rσ + t₁) := by
    rw [norm_mul, norm_mul, ← mul_add]
    have h1 : ‖ρ + τ‖ ≤ R₁ + r := (norm_add_le _ _).trans (add_le_add hρ.le hτ)
    exact mul_le_mul h1 (add_le_add hu.le ht.le) (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (by linarith [norm_nonneg ρ, norm_nonneg τ, hρ, hτ])
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hsτ hB) h

/-- **The open radius set**: `{(u, t) : (|u| + |t|) · B < δ₁}` is open. -/
theorem isOpen_markedRadiusSet (B δ₁ : ℝ) :
    IsOpen {p : ℂ × ℂ | (‖p.1‖ + ‖p.2‖) * B < δ₁} :=
  isOpen_lt (by fun_prop) continuous_const

/-- The radius set contains every closed bidisc `|u| ≤ a`, `|t| ≤ b` with `(a + b) · B < δ₁`
(`B ≥ 0`); in particular the Cauchy circle `|t| = t₀` for `t₀ < t₁` when `(a + t₁) B < δ₁`. -/
theorem mem_markedRadiusSet {B δ₁ a b : ℝ} (hB : 0 ≤ B) (h : (a + b) * B < δ₁) {u t : ℂ}
    (hu : ‖u‖ ≤ a) (ht : ‖t‖ ≤ b) : (u, t) ∈ {p : ℂ × ℂ | (‖p.1‖ + ‖p.2‖) * B < δ₁} :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right (add_le_add hu ht) hB) h

end Ball

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Finset Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **Consistency at the physical cut point (T5).**  At `s ≡ 1` and `Z = S.blockU z` the masked
decoupled tangent is the lift of `markedTangentC`, so the ball statement is the undecoupled
`liftC_markedTangentC_mem_flBallLC` (with `Y` a bound for the unit field `shiftUC x`). -/
theorem markedHatPsiF_one_mem_flBallLC
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hG : IsLevel Hm k)
    {F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (u t : ℂ) (x : S.E) {Y : ℝ}
    (hY : ∀ b : S.U, vn (fun i => S.shiftUC x (b, i)) ≤ Y) (h : (‖u‖ + ‖t‖) * Y < δ₁) :
    markedHatPsiF S.a₁ S.ν S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) F₁ (S.blockU z) u t
        (fun _ => 1) (rawOf S.D') (yhat x) ∈ FlBallLC Hm δ₁ := by
  rw [S.markedHatPsiF_one z hC hF₁ hD]
  exact S.liftC_markedTangentC_mem_flBallLC hG hY h

end StepSetting

end Balaban.Fluctuation
