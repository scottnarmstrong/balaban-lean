/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Fluct
public import Balaban.Fluctuation.InteractionLoc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One old term along the fluctuation: the `δ𝓔'`-part of the localized interaction

FLUCTUATION §3.3, proof of Proposition 3.3, "the `δ𝓔`-part" (P6 (4.13)-(4.21)).  For one term
`E = 𝓔(X; ·)` of the old effective action (the hypotheses of Theorem I-5 with `ψ'`, `i5_fluct`)
let `f(Θ, z) = E(ψ(𝔹_j(X), 𝔹_k(X); ψ(𝔹_k(X), 𝔹_{k+1}; Θ) + δψ(𝔹_k(X), 𝔹_k; z)))` be the
composite (`flComp`), for block fields `z` of `𝔹_k`; the composed fluctuation `δψ` contains the
direct term `κ z` besides the response through `δφ(z)` (P3 (4.17)).  By `i5_fluct`, `f = ∑_Y Ev_Y`
with analytic, bounded, local terms; the term of `𝒰` built from `E` is
`σ ∫₀¹ ω(t') ∂_w f(Θ, σ t' x₀) dt'` (`dirTermSrc`; in (3.3) `ω = 1`, `x₀ = ψ'(tψ̂)`,
`w = C^{1/2} t ψ̂`, block fields of `𝔹_k`).  `eterm_locInt` proves that it is a localized expansion
(`LocInt`) with the bound `|σ| M_ω E e^{-κ₀ d_j(X) - 2κ d̃^cov_{k+1}(Y)} / r`, where `r` is the
radius of the Cauchy estimate in the direction `w` (P6 (4.15)).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix
  Balaban.Fluctuation Set Metric

section ETerm

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

theorem continuous_vn : Continuous (fun v : Fin N → ℂ => vn v) := by
  unfold vn
  exact continuous_norm.comp (PiLp.continuous_toLp 2 _)

/-- The ball of fluctuations is open. -/
theorem isOpen_flBall (Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm) (δ₁ : ℝ) :
    IsOpen (FlBall (N := N) Hm δ₁) := by
  have : FlBall (N := N) Hm δ₁ = ⋂ x ∈ (dataSites Hm : Finset (CTorus d L N₁ m₁ K)),
      {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ | vn (ψ' x) < δ₁} := by
    ext ψ'; simp [FlBall]
  rw [this]
  exact isOpen_biInter_finset fun x _ => isOpen_lt
    (continuous_vn.comp (continuous_apply x)) continuous_const

variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

open Classical in
/-- **The composite of an old term with the fluctuation**, as a function of the raw data `Θ` and
the fluctuation `z` (a block field of `𝔹_k`):
`E(ψ(𝔹_j, 𝔹_k; ψ(𝔹_k, 𝔹_{k+1}; Θ) + δψ(𝔹_k, 𝔹_k; z)))` (the left side of `i5_fluct`, with the
datum `flDatumOne` of P3 (4.16), (4.17)); `0` if `Θ` is not realizable or `z` is not a block
field of `𝔹_k`. -/
noncomputable def flComp (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (E : RawData d L (N₁ * L ^ m₁) K N → ℂ)
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) : ℂ :=
  if h : (∃ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D ∧ u.1 = rawOf D) ∧
      IsLayerConstant Hm u.2 then
    E (rawOf (composeData hB.hq (compWeight L a₁)
      (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
        (flDatumOne Hm BG₂ κ hB.hP hF.hPm a₁ ν h.1.choose u.2 h.2))
      (flDatumOne Hm BG₂ κ hB.hP hF.hPm a₁ ν h.1.choose u.2 h.2)))
  else 0

theorem flComp_rawOf (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (E : RawData d L (N₁ * L ^ m₁) K N → ℂ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D) {z : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hz : IsLayerConstant Hm z) :
    flComp hB hF E (rawOf D, z) =
      E (rawOf (composeData hB.hq (compWeight L a₁)
        (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
          (flDatumOne Hm BG₂ κ hB.hP hF.hPm a₁ ν D z hz))
        (flDatumOne Hm BG₂ κ hB.hP hF.hPm a₁ ν D z hz))) := by
  classical
  have h : (∃ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D' ∧
      rawOf D = rawOf D') ∧ IsLayerConstant Hm z := ⟨⟨D, hD, rfl⟩, hz⟩
  unfold flComp
  rw [dite_eq_left h]
  have := BgData.eq_of_raw h.1.choose_spec.2
  rw [← this]

/-- The admissible directions of the `δ𝓔'`-part: block fields `x₀`, `w` of `𝔹_k` whose Cauchy discs
`(σ t) x₀ + τ w` stay in the ball of fluctuations. -/
theorem flBallLC_of_disc {Rσ R₁ r : ℝ} {x₀ w : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hxw : ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
      (σ * t) • x₀ + τ • w ∈ FlBall Hm δ₁)
    (hx₀ : IsLayerConstant Hm x₀) (hw : IsLayerConstant Hm w) {σ : ℂ} (hσ : ‖σ‖ < Rσ) {t : ℂ}
    (ht : ‖t‖ < R₁) {τ : ℂ} (hτ : ‖τ‖ ≤ r) : (σ * t) • x₀ + τ • w ∈ FlBallLC Hm δ₁ :=
  ⟨hxw σ hσ t ht τ hτ, isLayerConstant_line (isLayerConstant_smul hx₀ _) hw τ⟩

/-- **The `δ𝓔'`-term of one old term** (FLUCTUATION Prop. 3.3, the `δ𝓔`-part).  Under the
hypotheses of `i5_fluct`, with `ω` continuous on `[0,1]`-rays, analytic on the disc `|t| < R₁`
(`R₁ > 1`) and bounded by `M_ω` on `[0,1]`, and directions `(x₀, w)` for which the Cauchy discs
`(σ t) x₀ + τ w`, `|σ| < R_σ`, `|t| < R₁`, `|τ| ≤ r`, stay in the ball of fluctuations,
`σ ∫₀¹ ω(t') ∂_w f(Θ, σ t' x₀) dt'` is a localized expansion over the domains `Y ⊃ X₁`, for block
fields `x₀`, `w` of `𝔹_k`. -/
theorem eterm_locInt (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {E : RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hEan : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ K) →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
          IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2} Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (flComp hB hF E) ω x₀ w σ Θ)
        (fun Y => Mω * ((Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X
          - 2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  obtain ⟨Ev, hsum, hloc, hbd, hanY⟩ := i5_fluct hB hF hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1
    hlog hEb hEan hEbd
  refine ⟨Ev, ?_⟩
  set XW := {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
          IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2} with hXW
  have hdisc : ∀ xw ∈ XW, ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
      (σ * t) • xw.1 + τ • xw.2 ∈ FlBallLC Hm δ₁ :=
    fun xw hxw σ hσ t ht τ hτ => flBallLC_of_disc hxw.1 hxw.2.1 hxw.2.2 hσ ht hτ
  have hdom0 : ∀ xw ∈ XW, ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ →
      (σ * t) • xw.1 ∈ FlBallLC Hm δ₁ :=
    fun xw hxw σ hσ t ht => by simpa using hdisc xw hxw σ hσ t ht 0 (by simp [hr.le])
  have hreal1 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R₁ := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  refine ⟨fun xw hxw σ hσ Θ hΘ => ?_, fun Y _ xw hxw => ?_, fun Y _ xw hxw σ hσ Θ hΘ => ?_,
    fun Y _ xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' h1' h2' h3' => ?_, fun Y _ xw hxw Θ hΘ => ?_⟩
  · -- the terms add up (along the lines of block fields)
    refine dirTermSrc_sum_line (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps) (B := FlBallLC Hm δ₁)
      _ (fun Y => hanY Y) (fun Θ hΘ z hz => ?_) hωc hΘ (fun t ht => ?_)
    · obtain ⟨D, hD, rfl⟩ := hΘ
      rw [flComp_rawOf hB hF E hD hz.2]
      exact (hsum D hD z hz)
    · filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hr] with τ hτ
      exact hdisc xw hxw σ hσ t (hreal1 t ht) τ (mem_closedBall_zero_iff.1 hτ)
  · exact dirTerm_analytic hR₁ hω (hanY Y) (hdom0 xw hxw)
  · refine (norm_dirTerm_le hr hMω hωb (hanY Y) (fun u hu => hbd Y u hu) hΘ (fun t ht τ hτ => ?_)).trans
      (le_of_eq ?_)
    · exact hdisc xw hxw σ hσ t (hreal1 t ht) τ hτ
    · ring
  · refine dirTerm_local (AgΘ := fun Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
      (AgF := fun z z' => ∀ y ∈ psiThick Y, z y = z' y) ?_ ?_ (hanY Y) hΘ hΘ' h1' h2' h3' hr ?_
    · intro a a' b b' c' d' ha hb y hy
      simp [ha y hy, hb y hy]
    · intro Θ hΘ Θ' hΘ' z hz z' hz' h1'' h2''
      exact hloc Y (Θ, z) ⟨hΘ, hz⟩ (Θ', z') ⟨hΘ', hz'⟩ h1'' h2''
    · intro t ht τ hτ
      exact ⟨hdisc xw hxw σ hσ t (hreal1 t ht) τ hτ, hdisc xw' hxw' σ hσ t (hreal1 t ht) τ hτ⟩
  · exact dirTerm_zero Θ

/-- **The `δ𝓔'`-part for a finite family of old terms** (FLUCTUATION Prop. 3.3, the sum over the
terms `𝓔_j(y, X)` of the old effective action, restricted to `Z_k^c`).  Each term has its own
generating sets `𝔹_k(X)`, `𝔹_j(X)`, cover data and bound. -/
theorem eterms_locInt {τι : Type*} [DecidableEq τι] (𝒯 : Finset τι) {ϱ₁ ϱ₂ : τι → ℝ}
    {Gk : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₁ τ)}
    {Gj : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) K (ϱ₂ τ)}
    {r₀ δ₃ : ℝ} {X₀ X₁f : τι → Finset (CTorus d L N₁ m₁ K)} {j m₀ : τι → ℕ}
    {X 𝒦X : τι → Set (CTorus d L N₁ m₁ K)} {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    (hB : ∀ τ ∈ 𝒯, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (j τ))
    (hF : ∀ τ ∈ 𝒯, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hcov : ∀ τ ∈ 𝒯, CovSetup Gp (m₀ τ) (j τ) (X τ) (𝒦X τ))
    (hX₁ : ∀ τ ∈ 𝒯, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀ τ) (j τ) (𝒦X τ))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ τ ∈ 𝒯, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X τ) ∧ MeetsOne (m₀ τ) (j τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L (m₀ τ) m₁ (j τ)) E₀ = treeLenCovOne (m₀ τ) (j τ) (X τ))
    {κdec κ₀ : ℝ} {Eb : τι → ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ τ ∈ 𝒯, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ τ) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hEb : ∀ τ ∈ 𝒯, 0 ≤ Eb τ) {E : τι → RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hEan : ∀ τ ∈ 𝒯, AnalyticOnNhd ℂ (E τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ ∈ 𝒯, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (j τ) (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖E τ r‖ ≤ Eb τ * Real.exp (-(κdec - 1) * treeLenCovOne (m₀ τ) (j τ) (X τ)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : τι → Finset (Set (CTorus d L N₁ m₁ K)))
      (T : τι → Set (CTorus d L N₁ m₁ K) → (CTorus d L N₁ m₁ K → Fin N → ℂ) →
        (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ → RawData d L (N₁ * L ^ m₁) K N → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
          IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2} Rσ
        (𝒯.biUnion 𝒴)
        (fun Y x₀ w σ Θ => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then T τ Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => ∑ τ ∈ 𝒯, if h : τ ∈ 𝒯 then
          dirTermSrc (flComp (hB τ h) (hF τ h) (E τ)) ω x₀ w σ Θ else 0)
        (fun Y => ∑ τ ∈ 𝒯, if Y ∈ 𝒴 τ then Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r) else 0)
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  have hex : ∀ τ, ∃ (Ev : Set (CTorus d L N₁ m₁ K) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ), τ ∈ 𝒯 →
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
          IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2} Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp
          (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => if h : τ ∈ 𝒯 then
          dirTermSrc (flComp (hB τ h) (hF τ h) (E τ)) ω x₀ w σ Θ else 0)
        (fun Y => Mω * ((Eb τ * Real.exp (-κ₀ * treeLenCovOne (m₀ τ) (j τ)
          (X τ) - 2 * κdec * treeLenCov Gp (m₀ τ) Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
    intro τ
    by_cases hτ : τ ∈ 𝒯
    · obtain ⟨Ev, hEv⟩ := eterm_locInt (hB τ hτ) (hF τ hτ) (hcov τ hτ) (hX₁ τ hτ) hconn hrow
        (hopt τ hτ) hκ₀ hκdec hκ h1 (hlog τ hτ) (hEb τ hτ) (hEan τ hτ) (hEbd τ hτ) hωc hR₁ hω hMω
        hωb hr (Rσ := Rσ)
      exact ⟨Ev, fun _ => by simpa [hτ] using hEv⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hτ⟩
  choose Ev hEv using hex
  exact ⟨fun τ => polymerDomains (fun i : ParIdx Gp (↑(X₁f τ) : Set (CTorus d L N₁ m₁ K)) => i.1.1)
      Gp (m₀ τ) (X1 Gp (m₀ τ) (j τ) (𝒦X τ)),
    fun τ Y x₀ w σ Θ => dirTerm (Ev τ Y) ω x₀ w σ Θ, LocInt.finsum 𝒯 (fun τ hτ => hEv τ hτ)⟩

end ETerm

end Balaban.Localization
