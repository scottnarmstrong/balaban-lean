/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionVBlock
public import Balaban.Fluctuation.InteractionLocDir
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The source part of the localized interaction (FLUCTUATION §3.3, "the `δ𝓕`-part")

`𝓕_k = ⟨g, φ_k⟩ + ∑ 𝓜^{(j)}(y, X)`.  Along the fluctuation `⟨g, φ_k⟩` contributes
`⟨g, δφ(ψ')⟩ = ∑_{y,i} g(y,i) δφ(ψ')(y,i)`; each site functional `Φ_{y,i} = δφ(y,i)` is a functional
of the decoupled objects with the single-site support `{y}`, so `i5_functional` expands it
(`fsite_expansion`) and `locInt_dir1` gives the directional terms; the amplitude `g(y,i)` is
analytic in the source (`LocInt.mulAmp`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

section FPart

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

open Classical in
/-- **A function of the datum and the fluctuation, as a function of the raw data** (`0` for
unrealizable data). -/
noncomputable def onXi (Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a₁ ν eps : ℝ)
    (G : BgData Gp N → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ)
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) : ℂ :=
  if h : ∃ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D ∧ u.1 = rawOf D then
    G h.choose u.2
  else 0

theorem onXi_rawOf {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D)
    (G : BgData Gp N → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ)
    (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) : onXi Gp a₁ ν eps G (rawOf D, ψ') = G D ψ' := by
  classical
  have h : ∃ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D' ∧ rawOf D = rawOf D' :=
    ⟨D, hD, rfl⟩
  unfold onXi
  simp only [h, dite_true]
  have := BgData.eq_of_raw h.choose_spec.2
  rw [← this]

/-- The site functional `δφ(y, i)`. -/
noncomputable def siteFun (Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm) (y : CTorus d L N₁ m₁ K) (i : Fin N) :
    ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ :=
  fun _ δφ _ => svec Hm δφ y i

theorem siteFun_analytic (y : CTorus d L N₁ m₁ K) (i : Fin N) :
    AnalyticOnNhd ℂ (fun t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) =>
      siteFun Gp Hm y i t.1 t.2.1 t.2.2) Set.univ := by
  intro t0 _
  exact analyticAt_svec' (Hm := Hm) (Q := ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) K N ×
        (CTorus d L N₁ m₁ K → Fin N → ℂ))) (fun t => t.2.1)
    (fun r => ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Hm.Ω 1 × Fin N => ℂ) r).analyticAt _).comp
      (analyticAt_fst.comp analyticAt_snd)) y i

/-- **The site functional expands over the domains `Y ⊃ X₁`.** -/
theorem fsite_expansion (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (y : CTorus d L N₁ m₁ K) (hy : y ∈ X₁f) (i : Fin N) :
    ∃ Ev : Set (CTorus d L N₁ m₁ K) →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁, svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') y i =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψ')) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet Gp Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  obtain ⟨Ev, h1', h2', h3', h4'⟩ := i5_functional hC hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog
    hV (Φ := siteFun Gp Hm y i) ((siteFun_analytic (Gp := Gp) (Hm := Hm) y i).mono (Set.subset_univ _))
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

variable (d L N₁ m₁ K N) in
/-- The unit ball of the sources `g` in `ℓ¹`: `∑_{x,i} |g(x,i)| < 1`. -/
def l1Ball : Set (CTorus d L N₁ m₁ K → Fin N → ℂ) := {g | ∑ x, ∑ i, ‖g x i‖ < 1}

theorem norm_le_of_mem_l1Ball {g : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hg : g ∈ l1Ball d L N₁ m₁ K N) (y : CTorus d L N₁ m₁ K) (i : Fin N) : ‖g y i‖ ≤ 1 := by
  have h1 : ‖g y i‖ ≤ ∑ i', ‖g y i'‖ :=
    Finset.single_le_sum (f := fun i' => ‖g y i'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have h2 : ∑ i', ‖g y i'‖ ≤ ∑ x, ∑ i', ‖g x i'‖ :=
    Finset.single_le_sum (f := fun x => ∑ i', ‖g x i'‖) (fun _ _ => Finset.sum_nonneg
      fun _ _ => norm_nonneg _) (Finset.mem_univ y)
  have : ∑ x, ∑ i', ‖g x i'‖ < 1 := hg
  linarith

theorem analyticOnNhd_coord (y : CTorus d L N₁ m₁ K) (i : Fin N) :
    AnalyticOnNhd ℂ (fun g : CTorus d L N₁ m₁ K → Fin N → ℂ => g y i) Set.univ := by
  intro g _
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt _).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ K => Fin N → ℂ)
      y).analyticAt g)

theorem subset_of_mem_polymerDomains {ι : Type*} [Fintype ι] [DecidableEq ι]
    {cc : ι → ℕ × CTorus d L N₁ m₁ K} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
    {X₁ Y : Set (CTorus d L N₁ m₁ K)} (hY : Y ∈ polymerDomains cc G m₀ X₁) : X₁ ⊆ Y := by
  classical
  unfold polymerDomains at hY
  obtain ⟨C, -, rfl⟩ := Finset.mem_image.1 hY
  exact Set.subset_union_left

/-- **The source part `⟨g, ∂_w δφ⟩` of the localized interaction, one site.** -/
theorem fsite_locInt (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (y : CTorus d L N₁ m₁ K) (hy : y ∈ X₁f) (i : Fin N)
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ K) →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ l1Ball d L N₁ m₁ K N)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ p => p.2 y i * dirTerm (Ev Y) ω x₀ w σ p.1)
        (fun x₀ w σ p => p.2 y i * dirTermSrc (onXi Gp a₁ ν eps
          (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') y i)) ω x₀ w σ p.1)
        (fun Y => 1 * (Mω * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r)))
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  obtain ⟨Ev, hsum, hloc, hbd, hanY⟩ := fsite_expansion hC hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ
    h1 hlog y hy i
  refine ⟨Ev, ?_⟩
  have hbase := locInt_dir1 (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps) (B := FlBall Hm δ₁)
    (f := onXi Gp a₁ ν eps (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') y i))
    (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
      (X1 Gp m₀ j 𝒦X)) (Evs := Ev)
    (b := fun Y => (cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y))
    (AgΘ := fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
    (AgF := fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) (Rσ := Rσ) hR₁ hω hωc hMω hωb hr
    (isOpen_flBall (N := N) Hm δ₁) hanY (fun Y u hu => hbd Y u hu)
    (fun Y a a' c' c'' p q ha hb y hy => by simp [ha y hy, hb y hy])
    (fun Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2' => hloc Y (Θ, z) ⟨hΘ, hz⟩ (Θ', z') ⟨hΘ', hz'⟩ h1' h2')
    (fun Θ hΘ ψ' hψ => by
      obtain ⟨D, hD, rfl⟩ := hΘ
      rw [onXi_rawOf hD]
      exact hsum D hD ψ' hψ)
  refine (hbase.mulAmp (SG := l1Ball d L N₁ m₁ K N) (amp := fun g => g y i) (Ma := 1)
    ((analyticOnNhd_coord y i).mono (Set.subset_univ _)) (fun g hg => norm_le_of_mem_l1Ball hg y i)
    (AgG := fun Y g g' => ∀ x ∈ Y, g x = g' x) ?_)
  intro Y hY g _ g' _ hag
  have hyY : y ∈ Y := subset_of_mem_polymerDomains hY (by rw [← hX₁]; exact hy)
  exact congrFun (hag y hyY) i

/-- **The source part `⟨g, ∂_w δφ⟩`, all sites.** -/
theorem fsites_locInt (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {m₀ j : CTorus d L N₁ m₁ K × Fin N → ℕ}
    {X 𝒦X : CTorus d L N₁ m₁ K × Fin N → Set (CTorus d L N₁ m₁ K)}
    {X₁f : CTorus d L N₁ m₁ K × Fin N → Finset (CTorus d L N₁ m₁ K)}
    (hcov : ∀ s, CovSetup Gp (m₀ s) (j s) (X s) (𝒦X s))
    (hX₁ : ∀ s, (↑(X₁f s) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀ s) (j s) (𝒦X s))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ s, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X s) ∧ MeetsOne (m₀ s) (j s) (𝒦X s) W₀ ∧
        bondCost (scaleW L (m₀ s) m₁ (j s)) E₀ = treeLenCovOne (m₀ s) (j s) (X s))
    (hΔ : ∀ s, treeLenCovOne (m₀ s) (j s) (X s) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ s, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ s) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hy : ∀ s : CTorus d L N₁ m₁ K × Fin N, s.1 ∈ X₁f s)
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : CTorus d L N₁ m₁ K × Fin N → Finset (Set (CTorus d L N₁ m₁ K)))
      (T : CTorus d L N₁ m₁ K × Fin N → Set (CTorus d L N₁ m₁ K) →
        (CTorus d L N₁ m₁ K → Fin N → ℂ) → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ l1Ball d L N₁ m₁ K N)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (Finset.univ.biUnion 𝒴)
        (fun Y x₀ w σ p => ∑ s, if Y ∈ 𝒴 s then T s Y x₀ w σ p else 0)
        (fun x₀ w σ p => ∑ s : CTorus d L N₁ m₁ K × Fin N,
          p.2 s.1 s.2 * dirTermSrc (onXi Gp a₁ ν eps
            (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2)) ω x₀ w σ p.1)
        (fun Y => ∑ s, if Y ∈ 𝒴 s then 1 * (Mω * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ s) Y)) / r)) else 0)
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  have hex : ∀ s : CTorus d L N₁ m₁ K × Fin N, ∃ (Ev : Set (CTorus d L N₁ m₁ K) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ l1Ball d L N₁ m₁ K N)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f s) : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp
          (m₀ s) (X1 Gp (m₀ s) (j s) (𝒦X s)))
        (fun Y x₀ w σ p => p.2 s.1 s.2 * dirTerm (Ev Y) ω x₀ w σ p.1)
        (fun x₀ w σ p => p.2 s.1 s.2 * dirTermSrc (onXi Gp a₁ ν eps
          (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') s.1 s.2)) ω x₀ w σ p.1)
        (fun Y => 1 * (Mω * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ s) Y)) / r)))
        (fun Y p p' => agreeOn (thickSet Gp Y) p.1 p'.1 ∧ ∀ x ∈ Y, p.2 x = p'.2 x)
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := fun s =>
    fsite_locInt hC (hcov s) (hX₁ s) hconn hrow (hopt s) (hΔ s) hκ₀ hκdec hκ h1 (hlog s) s.1
      (hy s) s.2 hωc hR₁ hω hMω hωb hr
  choose Ev hEv using hex
  exact ⟨fun s => polymerDomains (fun i : ParIdx Gp (↑(X₁f s) : Set (CTorus d L N₁ m₁ K)) =>
      i.1.1) Gp (m₀ s) (X1 Gp (m₀ s) (j s) (𝒦X s)),
    fun s Y x₀ w σ p => p.2 s.1 s.2 * dirTerm (Ev s Y) ω x₀ w σ p.1,
    LocInt.finsum Finset.univ (fun s _ => hEv s)⟩

end FPart

end Balaban.Localization
