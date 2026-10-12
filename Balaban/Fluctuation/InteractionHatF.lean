/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatLocIntDm
public import Balaban.Fluctuation.HatPolyDom
public import Balaban.Fluctuation.InteractionHatV
public import Balaban.Fluctuation.InteractionFPart
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The source part of the localized interaction in the variable `ψ̂`

The hat version of `InteractionFPart`: each site functional `δφ(y, i)` of the decoupled objects is
expanded by `i5_functional_hat`, with terms local in `ψ̂` (`AgHat`), and `locInt_dir1` gives the
directional terms along `ψ̂`-rays.  The ball of admissible hat variables is taken open
(`|ψ̂| < cψ`) as `locInt_dir1` needs an open ball.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix Set Metric

section FHat

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

variable (Gp) in
/-- The open ball of hat variables `|ψ̂| < cψ`. -/
def hatBall (cψ : ℝ) : Set (unitPts Gp × Fin N → ℂ) := {ψh | ∀ p, ‖ψh p‖ < cψ}

theorem isOpen_hatBall (cψ : ℝ) : IsOpen (hatBall (N := N) Gp cψ) := by
  have : hatBall (N := N) Gp cψ = ⋂ p : unitPts Gp × Fin N,
      {ψh : unitPts Gp × Fin N → ℂ | ‖ψh p‖ < cψ} := by
    ext ψh; simp [hatBall]
  rw [this]
  exact isOpen_iInter_of_finite fun p => isOpen_lt
    ((continuous_norm).comp (continuous_apply p)) continuous_const

theorem hatBall_subset (cψ : ℝ) : hatBall (N := N) Gp cψ ⊆
    {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} := fun _ h p => (h p).le

variable (Gp) in
/-- The admissible rays in the open ball of hat variables. -/
def HatRaysO (cψ : ℝ) (R₁ Rσ r : ℝ) :
    Set ((unitPts Gp × Fin N → ℂ) × (unitPts Gp × Fin N → ℂ)) :=
  {xw | ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
    (σ * t) • xw.1 + τ • xw.2 ∈ hatBall (N := N) Gp cψ}

theorem hatRaysO_subset (cψ R₁ Rσ r : ℝ) :
    HatRaysO (N := N) Gp cψ R₁ Rσ r ⊆ HatRays Gp cψ R₁ Rσ r :=
  fun _ h σ hσ t ht τ hτ => hatBall_subset cψ (h σ hσ t ht τ hτ)

/-- **The site functional `δφ(y, i)` expands over the domains `Y ⊃ X₁`, with terms local in
`ψ̂`.** -/
theorem fsite_expansion_hat (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
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
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X₁f) (i : Fin N) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D (hatLift Gp a₁ ν hG' cc D ψh)) y i =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHat hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  obtain ⟨Ev, h1', h2', h3', h4'⟩ := i5_functional_hat hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov
    hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hV (Φ := siteFun Gp Hm y i)
    ((siteFun_analytic (Gp := Gp) (Hm := Hm) y i).mono (Set.subset_univ _))
    (fun t ht => by
      obtain ⟨-, hsup, -⟩ := flReal_facts ht
      rw [hΔ]; simpa [siteFun] using hsup.val y i)
    (Z := {y}) (Zα := ∅) (by simpa using hy) (fun x hx => absurd hx (Set.notMem_empty x))
    (fun t _ t' _ _ _ hδ _ _ => by
      unfold siteFun
      by_cases hyΩ : y ∈ Hm.Ω 1
      · rw [svec_of_mem' _ hyΩ, svec_of_mem' _ hyΩ]
        exact hδ ⟨y, hyΩ⟩ rfl i
      · rw [svec_of_not_mem Hm _ hyΩ, svec_of_not_mem Hm _ hyΩ])
  refine ⟨Ev, h1', h2', fun Y u hu => ?_, h4'⟩
  have := h3' Y u hu
  rw [hΔ] at this
  simpa using this

end FHat

section FSite

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The amplitude-free expansion of one site of `⟨g, δφ⟩`, in the variable `ψ̂`** (the base
of `fsite_locInt_hat`; hat version of `fsite_base_locInt`). -/
theorem fsite_base_locInt_hat_dm (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
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
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X₁f) (i : Fin N)
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
          (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') y i))) ω x₀ w σ Θ)
        (fun Y => Mω * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  classical
  obtain ⟨Ev, hsum, hloc, hbd, hanY⟩ := fsite_expansion_hat hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
    hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog y hy i
  have hd : 3 ≤ d := hC.HBp.hd
  refine ⟨Ev, ?_⟩
  have hbase := locInt_dir1 (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (B := hatBall (N := N) Gp cψ)
    (f := hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
      (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') y i)))
    (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
      (X1 Gp m₀ j 𝒦X)) (Evs := Ev)
    (b := fun Y => (cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y))
    (AgΘ := fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
    (AgF := AgHatF Gp hG') (Rσ := Rσ) hR₁ hω hωc hMω hωb hr
    (isOpen_hatBall cψ) (fun Y => (hanY Y).mono (Set.prod_mono le_rfl (hatBall_subset cψ)))
    (fun Y u hu => hbd Y u ⟨hu.1, hatBall_subset cψ hu.2⟩)
    (fun Y a a' c' c'' p q ha hb y hy i => by simp [ha y hy i, hb y hy i])
    (fun Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2' =>
      hloc Y (Θ, z) ⟨hΘ, hatBall_subset cψ hz⟩ (Θ', z') ⟨hΘ', hatBall_subset cψ hz'⟩ ⟨h1', h2'⟩)
    (fun Θ hΘ ψh hψ => by
      obtain ⟨D, hD, rfl⟩ := hΘ
      rw [hatFun_rawOf hG' cc _ hD, onXi_rawOf hD]
      exact hsum D hD ψh (hatBall_subset cψ hψ))
  exact LocIntDm.mk hbase (fun Y hY => isDj_of_polyDom hG' hcov hd hopt hY)
    (diagCont_dirTerm _ hR₁ hωc hr
      (fun Y => (hanY Y).mono (Set.prod_mono le_rfl (hatBall_subset cψ))))

/-- **The amplitude-free expansion of one site of `⟨g, δφ⟩`, in the variable `ψ̂`** (the base
of `fsite_locInt_hat`; hat version of `fsite_base_locInt`). -/
theorem fsite_base_locInt_hat (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
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
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X₁f) (i : Fin N)
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
          (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') y i))) ω x₀ w σ Θ)
        (fun Y => Mω * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ') (AgHatF Gp hG') := by
  obtain ⟨T, h⟩ := fsite_base_locInt_hat_dm hC hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hΔ (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 hlog y hy i (ω := ω) hωc (R₁ := R₁) hR₁ hω (Mω := Mω) hMω hωb (r := r) (Rσ := Rσ) hr
  exact ⟨T, h.loc⟩

/-- **The source part `⟨g, ∂_w δφ⟩` of the localized interaction, one site, in the variable
`ψ̂`.** -/
theorem fsite_locInt_hat_dm (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
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
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X₁f) (i : Fin N)
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      LocIntDm (IsDj m₀ (k + 1)) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ p => p.2 y i * dirTerm (Ev Y) ω x₀ w σ p.1)
        (fun x₀ w σ p => p.2 y i * dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
          (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') y i))) ω x₀ w σ p.1)
        (fun Y => 1 * (Mω * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r)))
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatF Gp hG') := by
  classical
  obtain ⟨Ev, hsum, hloc, hbd, hanY⟩ := fsite_expansion_hat hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁
    hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog y hy i
  have hd : 3 ≤ d := hC.HBp.hd
  refine ⟨Ev, ?_⟩
  have hbase := locInt_dir1 (S := XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (B := hatBall (N := N) Gp cψ)
    (f := hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
      (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') y i)))
    (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
      (X1 Gp m₀ j 𝒦X)) (Evs := Ev)
    (b := fun Y => (cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y))
    (AgΘ := fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
    (AgF := AgHatF Gp hG') (Rσ := Rσ) hR₁ hω hωc hMω hωb hr
    (isOpen_hatBall cψ) (fun Y => (hanY Y).mono (Set.prod_mono le_rfl (hatBall_subset cψ)))
    (fun Y u hu => hbd Y u ⟨hu.1, hatBall_subset cψ hu.2⟩)
    (fun Y a a' c' c'' p q ha hb y hy i => by simp [ha y hy i, hb y hy i])
    (fun Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2' =>
      hloc Y (Θ, z) ⟨hΘ, hatBall_subset cψ hz⟩ (Θ', z') ⟨hΘ', hatBall_subset cψ hz'⟩ ⟨h1', h2'⟩)
    (fun Θ hΘ ψh hψ => by
      obtain ⟨D, hD, rfl⟩ := hΘ
      rw [hatFun_rawOf hG' cc _ hD, onXi_rawOf hD]
      exact hsum D hD ψh (hatBall_subset cψ hψ))
  refine ((LocIntDm.mk (P := IsDj m₀ (k + 1)) (e := (id : (unitPts Gp × Fin N → ℂ) → _)) hbase
    (fun Y hY => isDj_of_polyDom hG' hcov hd hopt hY)
    (diagCont_dirTerm _ hR₁ hωc hr
      (fun Y => (hanY Y).mono (Set.prod_mono le_rfl (hatBall_subset cψ))))).mulAmp (SG := l1Ball d L N₁ m₁ (k + 1) N) (amp := fun g => g y i) (Ma := 1)
    ((analyticOnNhd_coord y i).mono (Set.subset_univ _)) (fun g hg => norm_le_of_mem_l1Ball hg y i)
    (AgG := fun Y g g' => ∀ x ∈ Y, g x = g' x) ?_)
  intro Y hY g _ g' _ hag
  have hyY : y ∈ Y := subset_of_mem_polymerDomains hY (by rw [← hX₁]; exact hy)
  exact congrFun (hag y hyY) i

/-- **The source part `⟨g, ∂_w δφ⟩` of the localized interaction, one site, in the variable
`ψ̂`.** -/
theorem fsite_locInt_hat (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
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
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X₁f) (i : Fin N)
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ p => p.2 y i * dirTerm (Ev Y) ω x₀ w σ p.1)
        (fun x₀ w σ p => p.2 y i * dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
          (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') y i))) ω x₀ w σ p.1)
        (fun Y => 1 * (Mω * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r)))
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatF Gp hG') := by
  obtain ⟨T, h⟩ := fsite_locInt_hat_dm hC hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsm hδ₁ hcov hX₁ hconn hrow hopt hΔ (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 hlog y hy i (ω := ω) hωc (R₁ := R₁) hR₁ hω (Mω := Mω) hMω hωb (r := r) (Rσ := Rσ) hr
  exact ⟨T, h.loc⟩

/-- **The source part `⟨g, ∂_w δφ⟩`, all sites, in the variable `ψ̂`.** -/
theorem fsites_locInt_hat_dm (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {m₀ j : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {X 𝒦X : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁f : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : ∀ s, CovSetup Gp (m₀ s) (j s) (X s) (𝒦X s))
    (hX₁ : ∀ s, (↑(X₁f s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ s) (j s) (𝒦X s))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X s) ∧ MeetsOne (m₀ s) (j s) (𝒦X s) W₀ ∧
        bondCost (scaleW L (m₀ s) m₁ (j s)) E₀ = treeLenCovOne (m₀ s) (j s) (X s))
    (hΔ : ∀ s, treeLenCovOne (m₀ s) (j s) (X s) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ s, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ s) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hy : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁f s)
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1)) →
        (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ),
      LocIntDm (fun Y => ∃ s, IsDj (m₀ s) (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion 𝒴)
        (fun Y x₀ w σ p => ∑ s, if Y ∈ 𝒴 s then T s Y x₀ w σ p else 0)
        (fun x₀ w σ p => ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
          p.2 s.1 s.2 * dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
            (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2))) ω x₀ w σ p.1)
        (fun Y => ∑ s, if Y ∈ 𝒴 s then 1 * (Mω * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ s) Y)) / r)) else 0)
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatF Gp hG') := by
  classical
  have hex : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, ∃ (Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ),
      LocIntDm (fun Y => ∃ s', IsDj (m₀ s') (k + 1) Y) (id : (unitPts Gp × Fin N → ℂ) → _)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f s) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp
          (m₀ s) (X1 Gp (m₀ s) (j s) (𝒦X s)))
        (fun Y x₀ w σ p => p.2 s.1 s.2 * dirTerm (Ev Y) ω x₀ w σ p.1)
        (fun x₀ w σ p => p.2 s.1 s.2 * dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
          (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2))) ω x₀ w σ p.1)
        (fun Y => 1 * (Mω * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ s) Y)) / r)))
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatF Gp hG') := fun s =>
    (fsite_locInt_hat_dm hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ (hcov s) (hX₁ s) hconn hrow (hopt s)
      (hΔ s) hκ₀ hκdec hκ h1 (hlog s) s.1 (hy s) s.2 hωc hR₁ hω hMω hωb hr).imp
      fun _ h => h.mono_P fun Y hY => ⟨s, hY⟩
  choose Ev hEv using hex
  exact ⟨fun s => polymerDomains (fun i : ParIdx Gp (↑(X₁f s) : Set (CTorus d L N₁ m₁ (k + 1))) =>
      i.1.1) Gp (m₀ s) (X1 Gp (m₀ s) (j s) (𝒦X s)),
    fun s Y x₀ w σ p => p.2 s.1 s.2 * dirTerm (Ev s Y) ω x₀ w σ p.1,
    LocIntDm.finsum Finset.univ (fun s _ => hEv s)⟩

/-- **The source part `⟨g, ∂_w δφ⟩`, all sites, in the variable `ψ̂`.** -/
theorem fsites_locInt_hat (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {m₀ j : CTorus d L N₁ m₁ (k + 1) × Fin N → ℕ}
    {X 𝒦X : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1))}
    {X₁f : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hcov : ∀ s, CovSetup Gp (m₀ s) (j s) (X s) (𝒦X s))
    (hX₁ : ∀ s, (↑(X₁f s) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp (m₀ s) (j s) (𝒦X s))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X s) ∧ MeetsOne (m₀ s) (j s) (𝒦X s) W₀ ∧
        bondCost (scaleW L (m₀ s) m₁ (j s)) E₀ = treeLenCovOne (m₀ s) (j s) (X s))
    (hΔ : ∀ s, treeLenCovOne (m₀ s) (j s) (X s) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ s, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ s) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hy : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N, s.1 ∈ X₁f s)
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : CTorus d L N₁ m₁ (k + 1) × Fin N → Finset (Set (CTorus d L N₁ m₁ (k + 1))))
      (T : CTorus d L N₁ m₁ (k + 1) × Fin N → Set (CTorus d L N₁ m₁ (k + 1)) →
        (unitPts Gp × Fin N → ℂ) → (unitPts Gp × Fin N → ℂ) → ℂ →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ l1Ball d L N₁ m₁ (k + 1) N)
        (HatRaysO Gp cψ R₁ Rσ r) Rσ
        (Finset.univ.biUnion 𝒴)
        (fun Y x₀ w σ p => ∑ s, if Y ∈ 𝒴 s then T s Y x₀ w σ p else 0)
        (fun x₀ w σ p => ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
          p.2 s.1 s.2 * dirTermSrc (hatFun Gp a₁ ν eps hG' cc (onXi Gp a₁ ν eps
            (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2))) ω x₀ w σ p.1)
        (fun Y => ∑ s, if Y ∈ 𝒴 s then 1 * (Mω * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ s) Y)) / r)) else 0)
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (AgHatF Gp hG') := by
  obtain ⟨a, T, h⟩ := fsites_locInt_hat_dm hC hk hG hG' cc (cψ := cψ) hcψ hMX (δc := δc) hdm hα hsm hδ₁ (m₀ := m₀) (j := j) (X := X) (𝒦X := 𝒦X) (X₁f := X₁f) hcov hX₁ hconn hrow hopt hΔ (κdec := κdec) (κ₀ := κ₀) hκ₀ hκdec hκ h1 hlog hy (ω := ω) hωc (R₁ := R₁) hR₁ hω (Mω := Mω) hMω hωb (r := r) (Rσ := Rσ) hr
  exact ⟨a, T, h.loc⟩

end FSite

end Balaban.Localization
