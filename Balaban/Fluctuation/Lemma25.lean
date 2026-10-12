/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Lemma25Xi
public import Balaban.Fluctuation.Lemma25Domain
public import Balaban.Fluctuation.Covariance
public import Balaban.Fluctuation.MeasureAbsorb
public import Balaban.SmallField.XiD2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Lemma 2.5 (only `χ_fl` remains), source form (FLUCTUATION.md §2.5, v2.2)

On `{χ_{k+1,u} = 1}`, for `ψ = ψ^{(k)}(θ) + β^{-1/2} C^{(k)1/2} ψ̂` with real `ψ̂`,
`χ_k(ψ) χ_{(2.2)}(θ, ψ) χ_fl(ψ̂) = χ_fl(ψ̂)` (`lemma25`).

The three internal inputs of `chiFl_absorbs_of` are discharged from the landed theorems:
Lemma 2.2 at `ψ̂ = 0` (`criticalPoint_real`, through `composeData_inDomainR`, `psiK_domain`),
Lemma 2.3 (d) (`expansion_bounds`, through `psiK_expansion`, whose disc hypothesis is derived in
`Lemma25Domain`) and Lemma 2.4 (c), the sup bound `lemma24_c_sup`.  `χ_k` is the indicator of the
landed `Xi` (`chiXi`), each test being checked against its own threshold (`xiBounds_of_perturb`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization Finset Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}

/-- The unit-lattice point (block of side `L ^ k`) of a site, when `G'` is of level `k + 1`. -/
def unitPt (hG' : IsLevel G' (k + 1)) (x : CTorus d L N₁ m₁ (k + 1)) : unitPts G' :=
  ⟨unitBlock x, (mem_unitPts G').2 ⟨x, hG'.mem_layer x, rfl⟩⟩

open Classical in
/-- `χ_{k+1,u}(θ)`: the indicator of the tests `ChiUBounds` for the background of `θ`. -/
noncomputable def chiU (G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ') (a : ℕ → ℝ) (ν δ : ℝ)
    (D' : BgData G' N) : ℝ :=
  if ChiUBounds G' ν δ D' (bgField G' a ν D') (bgMult G' a ν D') then 1 else 0

open Classical in
/-- `χ_k(ψ)`: the indicator of `Ξ_k(𝔹; 1, δ)` (landed `Xi`, level `n = k`). -/
noncomputable def chiXi (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (δ : ℝ) (Ψ₀ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) (h₀ : Fin N → ℝ) : ℝ :=
  if Xi G a ν k 1 δ Ψ₀ h₀ then 1 else 0

open Classical in
/-- `χ_{(2.2)}(θ, ψ)`: the indicator of `|θ - Q_{k+1} ψ| < 2 δ`. -/
noncomputable def chi22 (G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ') (δ : ℝ)
    (D' : BgData G' N) (Ψ₀ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ) : ℝ :=
  if ∀ x, vn (fun i => D'.Ψ x i - blockMean G' (k + 1) (fun y => (Ψ₀ y i : ℂ)) x) < 2 * δ
  then 1 else 0

theorem chiU_eq_one_iff (a : ℕ → ℝ) (ν δ : ℝ) (D' : BgData G' N) :
    chiU G' a ν δ D' = 1 ↔ ChiUBounds G' ν δ D' (bgField G' a ν D') (bgMult G' a ν D') := by
  unfold chiU
  by_cases h : ChiUBounds G' ν δ D' (bgField G' a ν D') (bgMult G' a ν D')
  · simp [h]
  · simp [h]


theorem isConstraintField_of_chiU {n : ℕ} (hG' : IsLevel G' n) {ν δ : ℝ} {D' : BgData G' N}
    {φ₁ : G'.Ω 1 × Fin N → ℂ} {α₁ : G'.Ω 1 → ℂ} (hχ : ChiUBounds G' ν δ D' φ₁ α₁)
    (hδ : 0 ≤ δ) (hu : IsRealUnitField G' φ₁) : IsConstraintField G' δ (svec G' φ₁) := by
  have hsp : ∀ x : CTorus d L N₁ m₁ (k + 1), 0 < G'.spacing x := fun x => by
    rw [hG'.spacing_eq]
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hdiv : ∀ x : CTorus d L N₁ m₁ (k + 1), δ / 2 / G'.spacing x ≤ δ / G'.spacing x := fun x =>
    div_le_div_of_nonneg_right (by linarith) (hsp x).le
  have hdiv2 : ∀ x : CTorus d L N₁ m₁ (k + 1), δ / 2 / G'.spacing x ^ 2 ≤ δ / G'.spacing x ^ 2 :=
    fun x => div_le_div_of_nonneg_right (by linarith) (by have := hsp x; positivity)
  have hvn : ∀ x : CTorus d L N₁ m₁ (k + 1), vn (svec G' φ₁ x) = 1 := by
    intro x
    obtain ⟨hre, hsq⟩ := hu ⟨x, (hG' x).1⟩
    have e : svec G' φ₁ x = fun i => φ₁ (⟨x, (hG' x).1⟩, i) := by
      funext i; exact svec_eq_apply hG' φ₁ x i
    rw [e, vn_eq_sqrt, hsq, Real.sqrt_one]
  refine ⟨⟨fun x hx μ => ?_, fun x hx => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨g1, g2⟩ := hχ.grad x hx μ
    simp only [barField_eq_svec hG'] at g1 g2
    exact ⟨(g1.le.trans (hdiv x)), (g2.le.trans (hdiv x))⟩
  · have g := hχ.lap x hx
    simp only [barField_eq_svec hG'] at g
    exact g.le.trans (hdiv2 x)
  · rw [hvn]; norm_num
  · have hre := (hu ⟨x, (hG' x).1⟩).1
    have hsq := (hu ⟨x, (hG' x).1⟩).2
    have e : ∑ i, svec G' φ₁ x i * svec G' φ₁ x i = 1 := by
      have : ∀ i, svec G' φ₁ x i * svec G' φ₁ x i = ((‖φ₁ (⟨x, (hG' x).1⟩, i)‖ ^ 2 : ℝ) : ℂ) := by
        intro i
        rw [svec_eq_apply hG' φ₁ x i]
        set z := φ₁ (⟨x, (hG' x).1⟩, i) with hz
        have him : z.im = 0 := hre i
        have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
        rw [this]
        simp [Complex.norm_real, sq_abs]
        ring
      simp only [this]
      rw [← Complex.ofReal_sum, hsq]; simp
    rw [e]; simpa using hδ


/-- The radius of Lemma 2.5: `t = B₅ β^{-1/2} p₁` must not exceed it (the "β large" of the source:
`B₅ β_k^{-1/2} p₁ ≤ ½ C₃ c₇`, the radius of Lemma 2.3 (d), in the landed constants). -/
noncomputable def fluctRadius (d L N : ℕ) [NeZero L] : ℝ :=
  min (min (deltaStar d L N / 2) (bgC0 d L N / (5 * cK2 d L N)))
    (min (bgC1 d L N * (3 / 40)) (bgC1 d L N ^ 2 / 16))

theorem fluctRadius_le (d L N : ℕ) [NeZero L] (hd : 0 < d) :
    2 * fluctRadius d L N ≤ deltaStar d L N ∧
    cK2 d L N * (2 * fluctRadius d L N) < bgC0 d L N / 2 ∧
    10 * fluctRadius d L N ≤ 3 / 4 * bgC1 d L N ∧
    16 * fluctRadius d L N ≤ bgC1 d L N ^ 2 := by
  have hc0 := bgC0_pos d L N hd
  have hK := cK2_pos d L N
  have h1 : fluctRadius d L N ≤ deltaStar d L N / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have h2 : fluctRadius d L N ≤ bgC0 d L N / (5 * cK2 d L N) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have h3 : fluctRadius d L N ≤ bgC1 d L N * (3 / 40) := (min_le_right _ _).trans (min_le_left _ _)
  have h4 : fluctRadius d L N ≤ bgC1 d L N ^ 2 / 16 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨by linarith, ?_, by linarith, by linarith⟩
  have : cK2 d L N * fluctRadius d L N ≤ bgC0 d L N / 5 := by
    calc _ ≤ cK2 d L N * (bgC0 d L N / (5 * cK2 d L N)) := mul_le_mul_of_nonneg_left h2 hK.le
      _ = bgC0 d L N / 5 := by field_simp
  linarith


theorem bgC1_le_small (d L N : ℕ) [NeZero L] (hd : 0 < d) : bgC1 d L N ≤ 1 / 1024 := by
  have := (bgC1_facts (d := d) (L := L) (N := N) hd (le_refl (bgC1 d L N))).1
  exact (approxDelta_le d L this).1

/-- `ψ^{(k)}(θ)`, the critical point (2.1): the composed datum of `θ` and its background. -/
noncomputable def psiK (hG : IsLevel G k) (hG' : IsLevel G' (k + 1)) (a : ℕ → ℝ) (ν : ℝ)
    (D' : BgData G' N) : BgData G N :=
  composeData (hG.precedes hG' (le_refl (k + 1))) a (bgField G' a ν D') D'

theorem theta_consts (hd : 0 < d) {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2) :
    δ' ≤ thm73C1 d L N ∧ δ' ≤ thm73C3 d L N ∧ δ' ≤ bgC1 d L N ∧
      compC4 d * (bgK1 d L N * δ') ≤ bgC1 d L N / 4 := by
  have hC32 : thm73C3 d L N ≤ thm73C2 d L N := thm73C3_le_thm73C2 d L N
  have hC21 : thm73C2 d L N ≤ thm73C1 d L N := thm73C2_le_thm73C1 d L N
  have h3 : δ' ≤ thm73C3 d L N := by linarith
  have h1 : δ' ≤ thm73C1 d L N := by linarith
  refine ⟨h1, h3, (thm73_small (L := L) (N := N) hd hδ'0 h1).1, ?_⟩
  have hK1 := bgK1_ge_one d L N
  have hC4 := compC4_ge d
  have h4 : 2 * δ' ≤ thm73C2 d L N := by linarith
  have h2 : thm73C2 d L N = bgC2 d L N / (2 * (compC4 d * bgK1 d L N)) := rfl
  rw [h2, le_div_iff₀ (by positivity)] at h4
  have h5 := bgC2_le_bgC1 (d := d) (L := L) (N := N)
  nlinarith

section Core

variable (hk1 : 1 ≤ k) (hL3 : 3 ≤ L) {a₁ : ℝ} (ha₁ : 0 < a₁) {ν : ℝ} (hν0 : 0 ≤ ν)
  (hν1 : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (hG : IsLevel G k) (hG' : IsLevel G' (k + 1))
  (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (H' : BgHyp d L (k + 1) ϱ' (compWeight L a₁) ν)
  {D' : BgData G' N} {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2)
  (hD'R : InDomainR G' ν δ' D')

include hG hG' H H' hδ'0 hδ' hD'R ha₁ in
/-- The composed datum `ψ^{(k)}(θ)` is real, in `Ψ̃(𝔹; C₄ K₁ δ')`. -/
theorem psiK_domain :
    InDomainR G ν (compC4 d * (bgK1 d L N * δ')) (psiK hG hG' (compWeight L a₁) ν D') := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨h1, -, -, -⟩ := theta_consts hd0 hδ'0 hδ'
  exact composeData_inDomainR ha₁ H H' (hG.precedes hG' (le_refl (k + 1))) hδ'0 h1 hD'R

variable {h₀ : Fin N → ℝ} (hh₀ : ∀ x i, D'.h x i = (h₀ i : ℂ))
  {Ψ₀ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ} (hconst : IsLayerConstant G Ψ₀)
  {t tc : ℝ} (ht0 : 0 ≤ t) (htc0 : 0 ≤ tc) (hsqrt : Real.sqrt N * tc ≤ t)
  (hrad : t ≤ fluctRadius d L N)
  (htang : ∀ x i, ‖(Ψ₀ x i : ℂ) - (psiK hG hG' (compWeight L a₁) ν D').Ψ x i‖ ≤ tc)

include hν0 hν1 hG hG' H H' hδ'0 hδ' hD'R ha₁ hh₀ ht0 htc0 hsqrt hrad htang in
/-- The datum of `ψ = ψ^{(k)} + ψ'` lies in the real data domain `𝒟_ℝ(c₁)`. -/
theorem psiK_realDomain :
    InUnionDomainR G (bgC1 d L N) ν (realData G Ψ₀ h₀ hconst) := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨hrad1, hrad2, hrad3, hrad4⟩ := fluctRadius_le d L N hd0
  obtain ⟨-, -, -, hδb4⟩ := theta_consts hd0 hδ'0 hδ'
  have hBR := psiK_domain ha₁ hG hG' H H' hδ'0 hδ' hD'R
  have hK1 := bgK1_ge_one d L N
  have hC4 := compC4_ge d
  have hδb0 : 0 < compC4 d * (bgK1 d L N * δ') := by positivity
  have hc1small := bgC1_le_small d L N hd0
  obtain ⟨ΨB, h, hPB, hΨB, hhB⟩ := hBR
  have hhh : ∀ i, h i = h₀ i := by
    intro i
    have h1 := hhB (0 : CTorus d L N₁ m₁ (k + 1)) (hG 0).1 i
    have h2 : (psiK hG hG' (compWeight L a₁) ν D').h 0 i = D'.h 0 i :=
      composeData_h hG hG' (le_refl (k + 1)) _ _ D' 0 i
    rw [h2, hh₀] at h1
    exact_mod_cast h1.symm
  have hheq : h = h₀ := funext hhh
  rw [hheq] at hPB
  have hsmall_d : compC4 d * (bgK1 d L N * δ') ≤ 1 / 8 := by linarith
  have ht8 : t ≤ 1 / 8 := by linarith
  have he : ∀ x ∈ dataSites G, rn (fun i => Ψ₀ x i - ΨB x i) ≤ t := by
    intro x hx
    rw [← vn_ofReal]
    have e : (fun i => (((Ψ₀ x i - ΨB x i : ℝ)) : ℂ)) =
        fun i => (Ψ₀ x i : ℂ) - (psiK hG hG' (compWeight L a₁) ν D').Ψ x i := by
      funext i; rw [hΨB x hx i]; push_cast; ring
    rw [e]
    exact (vn_le_sqrt_mul htc0 fun i => htang x i).trans hsqrt
  have hlay : ∀ x ∈ dataSites G, G.layerIndex x ≤ k + 1 := fun x _ => by
    rw [(hG x).2]; omega
  have hPD := inPsiTilde_perturb hPB hconst hδb0.le hsmall_d ht0 ht8 hν0 hν1 hlay he
  have hsqt : 3 * Real.sqrt t ≤ 3 / 4 * bgC1 d L N := by
    have hc1p : 0 < bgC1 d L N := by linarith
    have : Real.sqrt t ≤ bgC1 d L N / 4 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith⟩
    linarith
  have hD_R := realData_realizes (G := G) (h₀ := h₀) hconst
  exact ⟨compC4 d * (bgK1 d L N * δ') + 3 * Real.sqrt t, by positivity, by linarith, Ψ₀, h₀, hPD,
    hD_R.1, hD_R.2⟩

include hν0 hν1 hG hG' H H' hδ'0 hδ' hD'R ha₁ hh₀ ht0 htc0 hsqrt hrad htang in
/-- Lemma 2.3 (d) for `ψ = ψ^{(k)} + ψ'`: `‖φ_k(ψ) - φ_{k+1}‖_*, |α_k(ψ) - α_{k+1}|₂ ≤ K₂ t`. -/
theorem psiK_expansion :
    SupBounds G (bgField G (compWeight L a₁) ν (realData G Ψ₀ h₀ hconst) -
        (hG.precedes hG' (le_refl (k + 1))).restrictφ (bgField G' (compWeight L a₁) ν D'))
      (cK2 d L N * t) ∧
    Small G (bgMult G (compWeight L a₁) ν (realData G Ψ₀ h₀ hconst) -
        (hG.precedes hG' (le_refl (k + 1))).restrictα (bgMult G' (compWeight L a₁) ν D'))
      (cK2 d L N * t) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hp : k + 1 ≤ k + 1 := le_refl _
  obtain ⟨hrad1, hrad2, hrad3, hrad4⟩ := fluctRadius_le d L N hd0
  obtain ⟨hδ'1, hδ'3, hδ'c1, hδb4⟩ := theta_consts hd0 hδ'0 hδ'
  have hDU' : InUnionDomainR G' (bgC1 d L N) ν D' := ⟨δ', hδ'0, hδ'c1, hD'R⟩
  have hDomR := psiK_realDomain ha₁ hν0 hν1 hG hG' H H' hδ'0 hδ' hD'R hh₀ hconst ht0 htc0 hsqrt hrad
    htang
  have hBR2 := psiK_domain ha₁ hG hG' H H' hδ'0 hδ' hD'R
  have hK1 := bgK1_ge_one d L N
  have hC4 := compC4_ge d
  have hδb0 : 0 < compC4 d * (bgK1 d L N * δ') := by positivity
  have hc1small := bgC1_le_small d L N hd0
  have hD_R := realData_realizes (G := G) (h₀ := h₀) hconst
  have hdata : ∀ x : CTorus d L N₁ m₁ (k + 1), x ∈ dataSites G := fun x =>
    (mem_dataSites G).2 (Or.inl (hG x).1)
  have hh : ∀ x i, (realData G Ψ₀ h₀ hconst).h x i = D'.h x i := fun x i => by
    rw [hD_R.2 x (hG x).1 i, hh₀]
  have hDC' : InUnionDomainC G' (bgC0 d L N) (thm73C3 d L N) ν D' := by
    obtain ⟨Ψ', h', hP', hΨ', hh'⟩ := hD'R
    refine ⟨δ', δ', hδ'0, le_rfl, hδ'c1.trans (bgC1_le_bgC0 d L N hd0), hδ'3, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_right hν1 (sq_nonneg δ')
      nlinarith [sq_nonneg δ']
    · exact ⟨Ψ', h', fun _ _ => 0, fun _ _ => 0,
        (DataWit.ofReal (ν := ν) hδ'0 hδ'0 hP' D' hΨ' hh').P, by simpa using hΨ', by simpa using hh'⟩
  obtain ⟨hf, hm⟩ := theorem72_real H' hDU'
  obtain ⟨hfD, hmD⟩ := theorem72_real H hDomR
  have hE : ∀ x, vn (fun i => (realData G Ψ₀ h₀ hconst).Ψ x i -
      (psiK hG hG' (compWeight L a₁) ν D').Ψ x i) ≤ t := by
    intro x
    have : (fun i => (realData G Ψ₀ h₀ hconst).Ψ x i - (psiK hG hG' (compWeight L a₁) ν D').Ψ x i) =
        fun i => (Ψ₀ x i : ℂ) - (psiK hG hG' (compWeight L a₁) ν D').Ψ x i := by
      funext i; rw [hD_R.1 x (hdata x) i]
    rw [this]
    exact (vn_le_sqrt_mul htc0 fun i => htang x i).trans hsqrt
  have hψs : ∀ x, vn (compTangent hG hG' hp (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν
      (bgC0 d L N) D') D' (realData G Ψ₀ h₀ hconst) x) ≤ t := by
    intro x
    simp only [hf]
    exact hE x
  have hdisc : ∀ τ : ℂ, ‖τ‖ < 2 → InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν
      ((composeData (hG.precedes hG' hp) (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν
        (bgC0 d L N) D') D').lineAt
        (tangentData (realData G Ψ₀ h₀ hconst) (composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D')) τ) := by
    intro τ hτ
    rw [hf]
    exact disc_inUnionDomainC (t := t) (R := 2) (E := tangentData (realData G Ψ₀ h₀ hconst)
      (psiK hG hG' (compWeight L a₁) ν D')) hd0 hBR2 hδb0 (by linarith) ht0 (by norm_num)
      (by linarith) (fun x i => rfl) (fun x _ => hE x) hν1 (by linarith) hτ
  have hsmallR : cK2 d L N * (2 * t) < bgC0 d L N / 2 := by
    have := mul_le_mul_of_nonneg_left hrad (cK2_pos d L N).le
    nlinarith
  obtain ⟨hs1, hs2, -, -, -, -⟩ := expansion_bounds ha₁ hG hG' hp H H' D' hDC'
    (realData G Ψ₀ h₀ hconst) hh ht0 (by norm_num : (2 : ℝ) ≤ 2) hψs hdisc (by linarith) hsmallR
  rw [hf, hfD] at hs1
  rw [hm, hmD] at hs2
  exact ⟨hs1, hs2⟩

variable {δ : ℝ} (hδ0 : 0 < δ)
  (hχ : ChiUBounds G' ν δ D' (bgField G' (compWeight L a₁) ν D') (bgMult G' (compWeight L a₁) ν D'))
  {K₂ : ℝ} (hK2a : cK2 d L N ≤ K₂) (hK2b : Real.sqrt N * cK2 d L N ≤ K₂) (hK2c : 1 ≤ K₂)
  (hKt : K₂ * t ≤ δ / 3)

include hk1 hL3 hν0 hν1 hG hG' H H' hδ'0 hδ' hD'R ha₁ hh₀ hconst ht0 htc0 hsqrt hrad htang hδ0 hχ hK2a hK2b
  hK2c hKt in
/-- **The tests of `χ_k`**: `ψ ∈ Ξ_k(𝔹; 1, δ)` (landed `Xi`), given the tests of `χ_{k+1,u}` for
`θ` and the h-test `hnorm`. -/
theorem psiK_xi
    (hnorm : ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < (1 * δ) ^ 2) :
    Xi G (compWeight L a₁) ν k 1 δ Ψ₀ h₀ := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hDomR := psiK_realDomain ha₁ hν0 hν1 hG hG' H H' hδ'0 hδ' hD'R hh₀ hconst ht0 htc0 hsqrt hrad
    htang
  obtain ⟨hs1, hs2⟩ := psiK_expansion ha₁ hν0 hν1 hG hG' H H' hδ'0 hδ' hD'R hh₀ hconst ht0 htc0
    hsqrt hrad htang
  have hD_R := realData_realizes (G := G) (h₀ := h₀) hconst
  have hdata : ∀ x : CTorus d L N₁ m₁ (k + 1), x ∈ dataSites G := fun x =>
    (mem_dataSites G).2 (Or.inl (hG x).1)
  have hE : ∀ x, vn (fun i => (realData G Ψ₀ h₀ hconst).Ψ x i -
      (psiK hG hG' (compWeight L a₁) ν D').Ψ x i) ≤ t := by
    intro x
    have : (fun i => (realData G Ψ₀ h₀ hconst).Ψ x i - (psiK hG hG' (compWeight L a₁) ν D').Ψ x i) =
        fun i => (Ψ₀ x i : ℂ) - (psiK hG hG' (compWeight L a₁) ν D').Ψ x i := by
      funext i; rw [hD_R.1 x (hdata x) i]
    rw [this]
    exact (vn_le_sqrt_mul htc0 fun i => htang x i).trans hsqrt
  have hcKt : cK2 d L N * t ≤ δ / 3 := by
    have := mul_le_mul_of_nonneg_right hK2a ht0
    linarith
  have hsqKt : Real.sqrt N * (cK2 d L N * t) ≤ δ / 3 := by
    have := mul_le_mul_of_nonneg_right hK2b ht0
    nlinarith
  have htδ : t ≤ δ / 3 := by
    have := mul_le_mul_of_nonneg_right hK2c ht0
    linarith
  have hXi := xiBounds_of_perturb (D := realData G Ψ₀ h₀ hconst) hL3 hk1 ha₁ hG hG' le_rfl hχ hδ0
    (mul_nonneg (cK2_pos d L N).le ht0) hν0 hν1 hh₀ hs1 hs2 hsqKt hcKt hE htδ hnorm
  exact ⟨one_pos, hδ0, realData G Ψ₀ h₀ hconst, hD_R, hDomR, hXi⟩

end Core

section Chi22

variable (hk1 : 1 ≤ k) (hL3 : 3 ≤ L) {a₁ : ℝ} (ha₁ : 0 < a₁) {ν : ℝ}
  (hG : IsLevel G k) (hG' : IsLevel G' (k + 1)) {D' : BgData G' N}
  {Ψ₀ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ} {δ t tc : ℝ}
  (hχ : ChiUBounds G' ν δ D' (bgField G' (compWeight L a₁) ν D') (bgMult G' (compWeight L a₁) ν D'))
  (htc0 : 0 ≤ tc) (hsqrt : Real.sqrt N * tc ≤ t) (htδ : t ≤ δ / 3)
  (htang : ∀ x i, ‖(Ψ₀ x i : ℂ) - (psiK hG hG' (compWeight L a₁) ν D').Ψ x i‖ ≤ tc)

include hk1 hL3 ha₁ hG hG' hχ htc0 hsqrt htδ htang in
/-- **The test (2.2)**: `|θ - Q_{k+1} ψ| < 2 δ` for `ψ = ψ^{(k)} + ψ'`. -/
theorem psiK_chi22 :
    ∀ x, vn (fun i => D'.Ψ x i - blockMean G' (k + 1) (fun y => (Ψ₀ y i : ℂ)) x) < 2 * δ := by
  have hp : k + 1 ≤ k + 1 := le_refl _
  obtain ⟨hk0, hk1'⟩ := kappa_bounds hL3 hk1 ha₁
  have hL0 : (3 : ℝ) ≤ L := by exact_mod_cast hL3
  have hL2 : (9 : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  intro x
  have hθc : ∀ y ∈ G'.blk (k + 1) x, D'.Ψ y = D'.Ψ x := fun y hy =>
    D'.Ψ_layerConst (k + 1) (by omega) le_rfl x (hG'.mem_layer x) y hy
  have hBQ : ∀ i, blockMean G' (k + 1) (fun y => (psiK hG hG' (compWeight L a₁) ν D').Ψ y i) x =
      blockAvg G' (bgField G' (compWeight L a₁) ν D') x i +
        ((compWeight L a₁ (k + 1) / compWeight L a₁ k *
          (((L : ℝ) ^ k) ^ 2 / ((L : ℝ) ^ (k + 1)) ^ 2) : ℝ) : ℂ) *
          (D'.Ψ x i - blockAvg G' (bgField G' (compWeight L a₁) ν D') x i) := by
    intro i
    have e1 : (fun y => (psiK hG hG' (compWeight L a₁) ν D').Ψ y i) = fun y =>
        blockMean G k (fun z => svec G' (bgField G' (compWeight L a₁) ν D') z i) y +
        ((compWeight L a₁ (k + 1) / compWeight L a₁ k *
          (((L : ℝ) ^ k) ^ 2 / ((L : ℝ) ^ (k + 1)) ^ 2) : ℝ) : ℂ) *
          (D'.Ψ y i - blockMean G' (k + 1)
            (fun z => svec G' (bgField G' (compWeight L a₁) ν D') z i) y) := by
      funext y
      exact composeData_Ψ_eq_psiStar hG hG' hp (compWeight L a₁) (bgField G' (compWeight L a₁) ν D')
        D' y i
    have e3 : blockMean G' (k + 1) (blockMean G k
        (fun z => svec G' (bgField G' (compWeight L a₁) ν D') z i)) x =
        blockMean G' (k + 1) (fun z => svec G' (bgField G' (compWeight L a₁) ν D') z i) x :=
      blockMean_nested (G := G') (Nat.le_succ k) hp _ x
    rw [e1, blockMean_add, blockMean_smul, e3]
    have e2 : blockMean G' (k + 1) (fun y => D'.Ψ y i -
        blockMean G' (k + 1) (fun z => svec G' (bgField G' (compWeight L a₁) ν D') z i) y) x =
        D'.Ψ x i - blockMean G' (k + 1)
          (fun z => svec G' (bgField G' (compWeight L a₁) ν D') z i) x := by
      refine blockMean_of_blk_const hp _ x fun y hy => ?_
      rw [hθc y hy, blockMean_blk_const _ x y hy]
    rw [e2, blockAvg_eq_blockMean hG']
  set κ : ℝ := compWeight L a₁ (k + 1) / compWeight L a₁ k *
    (((L : ℝ) ^ k) ^ 2 / ((L : ℝ) ^ (k + 1)) ^ 2) with hκ
  have e : (fun i => D'.Ψ x i - blockMean G' (k + 1) (fun y => (Ψ₀ y i : ℂ)) x) =
      (fun i => (1 - (κ : ℂ)) * (D'.Ψ x i - blockAvg G' (bgField G' (compWeight L a₁) ν D') x i)) +
        fun i => -(blockMean G' (k + 1) (fun y => (Ψ₀ y i : ℂ) -
          (psiK hG hG' (compWeight L a₁) ν D').Ψ y i) x) := by
    funext i
    have h1 : blockMean G' (k + 1) (fun y => (Ψ₀ y i : ℂ)) x =
        blockMean G' (k + 1) (fun y => (psiK hG hG' (compWeight L a₁) ν D').Ψ y i) x +
          blockMean G' (k + 1) (fun y => (Ψ₀ y i : ℂ) -
            (psiK hG hG' (compWeight L a₁) ν D').Ψ y i) x := by
      rw [← blockMean_add]
      congr 1
      funext y; ring
    rw [Pi.add_apply, h1, hBQ i]
    ring
  rw [e]
  refine lt_of_le_of_lt (vn_add _ _) ?_
  have hw : vn (fun i => D'.Ψ x i - blockAvg G' (bgField G' (compWeight L a₁) ν D') x i) <
      3 / 2 * δ := hχ.close x (hG' x).1
  have hκ9 : κ ≤ 1 / 9 := by
    refine hk1'.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h3 : vn (fun i => (1 - (κ : ℂ)) * (D'.Ψ x i - blockAvg G' (bgField G' (compWeight L a₁) ν D')
      x i)) ≤ 3 / 2 * δ := by
    have e' : (1 - (κ : ℂ)) = ((1 - κ : ℝ) : ℂ) := by push_cast; ring
    rw [e', vn_smul_real, abs_of_nonneg (by linarith)]
    have := vn_nonneg (fun i => D'.Ψ x i - blockAvg G' (bgField G' (compWeight L a₁) ν D') x i)
    nlinarith
  have h4 : vn (fun i => -(blockMean G' (k + 1) (fun y => (Ψ₀ y i : ℂ) -
      (psiK hG hG' (compWeight L a₁) ν D').Ψ y i) x)) ≤ t := by
    rw [vn_neg]
    refine (vn_le_sqrt_mul htc0 fun i => ?_).trans hsqrt
    exact norm_blockMean_le' hp _ x fun y _ => htang y i
  have hδ0 : 0 < δ := by
    have := hχ.close x (hG' x).1
    have := vn_nonneg (fun i => D'.Ψ x i - blockAvg G' (bgField G' (compWeight L a₁) ν D') x i)
    linarith
  linarith

end Chi22

/-- **The fluctuation shift** `β^{-1/2} C^{(k)1/2} ψ̂` (Lemma 2.4 (c)), evaluated at the fine site `x`
(through its unit block): `C^{(k)1/2} = decCovSqrt` of the data `(α_{k+1}, φ_{k+1})` of `θ`. -/
noncomputable def fluctShift (hG' : IsLevel G' (k + 1)) (a : ℕ → ℝ) (aT ν : ℝ) (D' : BgData G' N)
    (β : ℝ) (ψh : unitPts G' → Rn N) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) : ℂ :=
  ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    (decCovSqrt G' a aT ν (bgMult G' a ν D') (fun _ => 1) (svec G' (bgField G' a ν D'))
      (unitQ G') (unitP G') *ᵥ (fun q : unitPts G' × Fin N => (ψh q.1 q.2 : ℂ))) (unitPt hG' x, i)

section Main

variable {a₁ : ℝ} (ha₁ : 0 < a₁) {ν : ℝ} (hG : IsLevel G k) (hG' : IsLevel G' (k + 1))
  (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (H' : BgHyp d L (k + 1) ϱ' (compWeight L a₁) ν)
  {D' : BgData G' N} {δ' : ℝ} (hδ'0 : 0 < δ') (hδ' : δ' ≤ thm73C3 d L N / 2)
  (hD'R : InDomainR G' ν δ' D') {h₀ : Fin N → ℝ} (hh₀ : ∀ x i, D'.h x i = (h₀ i : ℂ))
  {Ψ₀ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℝ} (hconst : IsLayerConstant G Ψ₀)

include ha₁ hG hG' H H' hδ'0 hδ' hD'R hh₀ hconst in
/-- **Lemma 2.5 (only `χ_fl` remains; P4 (2.31), (2.39)--(2.40) at `λ = ∞`).**

`θ` is a real datum of `Ψ̃(𝔹'_k; δ')` (`δ' ≤ thm73C3 / 2`), `χ_{k+1,u}(θ) = 1` (the tests of
`ChiUBounds` for its background, threshold `δ = δ_k`), `ψ̂` real and
`ψ = ψ^{(k)}(θ) + β^{-1/2} C^{(k)1/2} ψ̂` a real block-spin field (`hψ`).  Then
`χ_k(ψ) χ_{(2.2)}(θ, ψ) χ_fl(ψ̂) = χ_fl(ψ̂)`, with `χ_k` the indicator of the landed
`Ξ_k(𝔹; 1, δ)`.  Premises: the ratio `p₁ / p₀ ≤ (3 B₅ K₂)⁻¹`, `p₀ = β^{1/2} δ` (P4 (2.40)); the
upper-bound constants `B₅ ≥ max(1, √N B_∞)`, `K₂ ≥ max(1, K₂^{BG}, √N K₂^{BG})` (enlarged); the
radius `B₅ β^{-1/2} p₁ ≤ fluctRadius` (`β` large); the standing hypotheses of Lemma 2.4 (`hfam`,
`hsm`); the h-test `hnorm` of `χ_k`, which involves `h` only. -/
theorem lemma25
    {δ : ℝ} (hδ0 : 0 < δ) {aT : ℝ}
    (hfam : ∀ x, 0 ≤ x → XData G' (compWeight L a₁) aT ν x (bgMult G' (compWeight L a₁) ν D') 0
      (fun _ => 1))
    (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (hχu : chiU G' (compWeight L a₁) ν δ D' = 1)
    (hnorm : ν * ((L : ℝ) ^ k) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < (1 * δ) ^ 2)
    {β p₁ B₅ K₂ : ℝ} (hβ : 0 < β) (hp₁ : 0 < p₁)
    (hB5 : max 1 (Real.sqrt N * covSupConst d L N (compWeight L a₁ k)) ≤ B₅)
    (hK2 : max (max 1 (cK2 d L N)) (Real.sqrt N * cK2 d L N) ≤ K₂)
    (hp40 : p₁ / (β ^ (1 / 2 : ℝ) * δ) ≤ (3 * B₅ * K₂)⁻¹)
    (hrad : B₅ * β ^ (-(1 / 2 : ℝ)) * p₁ ≤ fluctRadius d L N)
    (ψh : unitPts G' → Rn N)
    (hψ : ∀ x i, (Ψ₀ x i : ℂ) = (psiK hG hG' (compWeight L a₁) ν D').Ψ x i +
      fluctShift hG' (compWeight L a₁) aT ν D' β ψh x i) :
    chiXi G (compWeight L a₁) ν δ Ψ₀ h₀ * chi22 G' δ D' Ψ₀ * chiFl (unitPts G') N p₁ ψh =
      chiFl (unitPts G') N p₁ ψh := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hL3 : 3 ≤ L := H.hL
  have hν0 : 0 ≤ ν := H.mass
  have hν1 : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1 := H.massLe
  have hk1 : 1 ≤ k := (hfam 0 le_rfl).st.hk
  rcases chiFl_eq_zero_or_one p₁ ψh with h0 | h1
  · rw [h0, mul_zero]
  rw [h1, mul_one]
  have hq : ∀ q, ‖ψh q‖ < p₁ := (pi_norm_lt_iff hp₁).1 ((chiFl_eq_one_iff hp₁ ψh).1 h1)
  obtain ⟨-, -, hδ'c1, -⟩ := theta_consts hd0 hδ'0 hδ'
  have hDU' : InUnionDomainR G' (bgC1 d L N) ν D' := ⟨δ', hδ'0, hδ'c1, hD'R⟩
  obtain ⟨-, hunit, -, -⟩ := theorem71 H' hDU'
  have hχ := (chiU_eq_one_iff _ _ _ _).1 hχu
  have hcf := isConstraintField_of_chiU hG' hχ hδ0.le hunit
  have hv : ∀ p : unitPts G' × Fin N, ‖(fun q : unitPts G' × Fin N => (ψh q.1 q.2 : ℂ)) p‖ ≤ p₁ := by
    intro p
    show ‖((ψh p.1 p.2 : ℝ) : ℂ)‖ ≤ p₁
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hcomp : |ψh p.1 p.2| ≤ ‖ψh p.1‖ := by
      have := PiLp.norm_apply_le (ψh p.1) p.2
      simpa [Real.norm_eq_abs] using this
    exact hcomp.trans (hq p.1).le
  have hC := fun p => lemma24_c_sup hfam hcf hδ0.le hsm (fun q : unitPts G' × Fin N => (ψh q.1 q.2 : ℂ))
    hp₁.le hv p
  have hB5pos : 1 ≤ B₅ := (le_max_left _ _).trans hB5
  have hB5S : Real.sqrt N * covSupConst d L N (compWeight L a₁ k) ≤ B₅ := (le_max_right _ _).trans hB5
  have hK2a : cK2 d L N ≤ K₂ := ((le_max_right _ _).trans (le_max_left _ _)).trans hK2
  have hK2b : Real.sqrt N * cK2 d L N ≤ K₂ := (le_max_right _ _).trans hK2
  have hK2c : 1 ≤ K₂ := ((le_max_left _ _).trans (le_max_left _ _)).trans hK2
  have hβc : 0 < β ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hβ _
  have hβs : 0 < β ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hβ _
  have hcs : β ^ (-(1 / 2 : ℝ)) * β ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hβ]; simp
  set t : ℝ := B₅ * β ^ (-(1 / 2 : ℝ)) * p₁ with ht_def
  have ht0 : 0 ≤ t := by positivity
  set tc : ℝ := max 0 (β ^ (-(1 / 2 : ℝ)) * (covSupConst d L N (compWeight L a₁ k) * p₁)) with htc_def
  have htc0 : 0 ≤ tc := le_max_left _ _
  have hsqrt : Real.sqrt N * tc ≤ t := by
    rcases le_total 0 (β ^ (-(1 / 2 : ℝ)) * (covSupConst d L N (compWeight L a₁ k) * p₁)) with h | h
    · rw [htc_def, max_eq_right h]
      calc Real.sqrt N * (β ^ (-(1 / 2 : ℝ)) * (covSupConst d L N (compWeight L a₁ k) * p₁))
          = (Real.sqrt N * covSupConst d L N (compWeight L a₁ k)) * (β ^ (-(1 / 2 : ℝ)) * p₁) := by
            ring
        _ ≤ B₅ * (β ^ (-(1 / 2 : ℝ)) * p₁) :=
            mul_le_mul_of_nonneg_right hB5S (by positivity)
        _ = t := by rw [ht_def]; ring
    · rw [htc_def, max_eq_left h, mul_zero]; exact ht0
  have htang : ∀ x i, ‖(Ψ₀ x i : ℂ) - (psiK hG hG' (compWeight L a₁) ν D').Ψ x i‖ ≤ tc := by
    intro x i
    have e : (Ψ₀ x i : ℂ) - (psiK hG hG' (compWeight L a₁) ν D').Ψ x i =
        fluctShift hG' (compWeight L a₁) aT ν D' β ψh x i := by rw [hψ x i]; ring
    rw [e]
    unfold fluctShift
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβc]
    refine (le_max_right _ _).trans' ?_
    exact mul_le_mul_of_nonneg_left (hC _) hβc.le
  have hKt : K₂ * t ≤ δ / 3 := by
    have h1 : p₁ ≤ (3 * B₅ * K₂)⁻¹ * (β ^ (1 / 2 : ℝ) * δ) := by
      rwa [div_le_iff₀ (by positivity)] at hp40
    have h2 : K₂ * (B₅ * β ^ (-(1 / 2 : ℝ)) * p₁) ≤
        K₂ * (B₅ * β ^ (-(1 / 2 : ℝ)) * ((3 * B₅ * K₂)⁻¹ * (β ^ (1 / 2 : ℝ) * δ))) := by
      gcongr
    refine h2.trans (le_of_eq ?_)
    field_simp
    exact hcs
  have htδ : t ≤ δ / 3 := by
    have := mul_le_mul_of_nonneg_right hK2c ht0
    linarith
  have hX := psiK_xi hk1 hL3 ha₁ hν0 hν1 hG hG' H H' hδ'0 hδ' hD'R hh₀ hconst ht0 htc0 hsqrt hrad
    htang hδ0 hχ hK2a hK2b hK2c hKt hnorm
  have h22 := psiK_chi22 hk1 hL3 ha₁ hG hG' hχ htc0 hsqrt htδ htang
  unfold chiXi chi22
  simp [hX, h22]

end Main

end Balaban.Fluctuation
