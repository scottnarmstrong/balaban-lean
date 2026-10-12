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
composite (`flComp`).  By `i5_fluct`, `f = ∑_Y Ev_Y` with analytic, bounded, local terms; the term
of `𝒰` built from `E` is `σ ∫₀¹ ω(t') ∂_w f(Θ, σ t' x₀) dt'` (`dirTermSrc`; in (3.3) `ω = 1`,
`x₀ = ψ'(tψ̂)`, `w = C^{1/2} t ψ̂`).  `eterm_locInt` proves that it is a localized expansion
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
the fluctuation `z`:
`E(ψ(𝔹_j, 𝔹_k; ψ(𝔹_k, 𝔹_{k+1}; Θ) + δψ(𝔹_k, 𝔹_k; z)))` (the left side of `i5_fluct`);
`0` if `Θ` is not realizable. -/
noncomputable def flComp (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (E : RawData d L (N₁ * L ^ m₁) K N → ℂ)
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) : ℂ :=
  if h : ∃ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D ∧ u.1 = rawOf D then
    E (rawOf (composeData hB.hq (compWeight L a₁)
      (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
        (flDatumOne Hm BG₂ κ hB.hP hF.hPm a₁ ν h.choose u.2))
      (flDatumOne Hm BG₂ κ hB.hP hF.hPm a₁ ν h.choose u.2)))
  else 0

theorem flComp_rawOf (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (E : RawData d L (N₁ * L ^ m₁) K N → ℂ) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D) (z : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    flComp hB hF E (rawOf D, z) =
      E (rawOf (composeData hB.hq (compWeight L a₁)
        (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N)
          (flDatumOne Hm BG₂ κ hB.hP hF.hPm a₁ ν D z))
        (flDatumOne Hm BG₂ κ hB.hP hF.hPm a₁ ν D z))) := by
  classical
  have h : ∃ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D' ∧ rawOf D = rawOf D' :=
    ⟨D, hD, rfl⟩
  unfold flComp
  simp only [h, dite_true]
  have := BgData.eq_of_raw h.choose_spec.2
  rw [← this]

/-- **The `δ𝓔'`-term of one old term** (FLUCTUATION Prop. 3.3, the `δ𝓔`-part).  Under the
hypotheses of `i5_fluct`, with `ω` continuous on `[0,1]`-rays, analytic on the disc `|t| < R₁`
(`R₁ > 1`) and bounded by `M_ω` on `[0,1]`, and directions `(x₀, w)` for which the Cauchy discs
`(σ t) x₀ + τ w`, `|σ| < R_σ`, `|t| < R₁`, `|τ| ≤ r`, stay in the ball of fluctuations,
`σ ∫₀¹ ω(t') ∂_w f(Θ, σ t' x₀) dt'` is a localized expansion over the domains `Y ⊃ X₁`. -/
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
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
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
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} with hXW
  have hdom0 : ∀ xw ∈ XW, ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → (σ * t) • xw.1 ∈ FlBall Hm δ₁ :=
    fun xw hxw σ hσ t ht => by simpa using hxw σ hσ t ht 0 (by simp [hr.le])
  have hBo := isOpen_flBall (N := N) Hm δ₁
  refine ⟨fun xw hxw σ hσ Θ hΘ => ?_, fun Y xw hxw => ?_, fun Y xw hxw σ hσ Θ hΘ => ?_,
    fun Y xw hxw xw' hxw' σ hσ Θ hΘ Θ' hΘ' h1' h2' h3' => ?_, fun Y xw hxw Θ hΘ => ?_⟩
  · -- the terms add up
    refine dirTermSrc_sum (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps) (B := FlBall Hm δ₁)
      _ hBo (fun Y => hanY Y) (fun Θ hΘ z hz => ?_) hωc hΘ (fun t ht => ?_)
    · obtain ⟨D, hD, rfl⟩ := hΘ
      rw [flComp_rawOf hB hF E hD z]
      exact (hsum D hD z hz)
    · exact hdom0 xw hxw σ hσ t (by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2])
  · exact dirTerm_analytic hR₁ hω (hanY Y) (hdom0 xw hxw)
  · refine (norm_dirTerm_le hr hMω hωb (hanY Y) (fun u hu => hbd Y u hu) hΘ (fun t ht τ hτ => ?_)).trans
      (le_of_eq ?_)
    · exact hxw σ hσ t (by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]) τ hτ
    · ring
  · refine dirTerm_local (AgΘ := fun Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
      (AgF := fun z z' => ∀ y ∈ psiThick Y, z y = z' y) ?_ ?_ (hanY Y) hΘ hΘ' h1' h2' h3' hr ?_
    · intro a a' b b' c' d' ha hb y hy
      simp [ha y hy, hb y hy]
    · intro Θ hΘ Θ' hΘ' z hz z' hz' h1'' h2''
      exact hloc Y (Θ, z) ⟨hΘ, hz⟩ (Θ', z') ⟨hΘ', hz'⟩ h1'' h2''
    · intro t ht τ hτ
      have ht' : ‖(t : ℂ)‖ < R₁ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
      exact ⟨hxw σ hσ t ht' τ hτ, hxw' σ hσ t ht' τ hτ⟩
  · exact dirTerm_zero Θ

end ETerm

end Balaban.Localization
