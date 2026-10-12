/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionEnergy
public import Balaban.Fluctuation.InteractionDir3
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The potential part of the localized interaction, one block (FLUCTUATION §3.3, "the `V`-part")

For a block `B_{n+1}(z)` the block energy `energyBlock` is a function of the decoupled objects
`(α_{k+1}(s), δφ(s), ψ')`; `vblock_expansion` expands it at `s = 1` over the domains `Y ⊃ X₁` by
`i5_functional` (Lemma AE for functionals of the decoupled objects, with (AE1) from
`energyBlock_analytic`, `energyBlock_bound` and (AE2) from `energyDensity_congr`).  The third
directional derivative of its terms (`locInt_dir3`) is the block part of the potential part of
(3.3): `vblock_locInt`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

section VBlock

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **The chord-energy functional of a block.** -/
noncomputable def blockEnergyFun (Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm) (a : ℕ → ℝ) (ν : ℝ) (n : ℕ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ :=
  fun pa δφ u => energyBlock Gp Hm a ν n pa.2 δφ u.2 z

theorem blockEnergyFun_analytic (a : ℕ → ℝ) (ν : ℝ) (n : ℕ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) :
    AnalyticOnNhd ℂ (fun t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) =>
      blockEnergyFun Gp Hm a ν n z t.1 t.2.1 t.2.2) Set.univ := by
  intro t0 _
  refine analyticAt_energyBlock (Q := ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) ×
      (Hm.Ω 1 × Fin N → ℂ) × (RawData d L (N₁ * L ^ m₁) K N ×
        (CTorus d L N₁ m₁ K → Fin N → ℂ))) a ν n (fun t => t.1.2) (fun t => t.2.1)
    (fun t => t.2.2.2) ?_ ?_ ?_ z
  · intro r
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Gp.Ω 1 => ℂ) r).analyticAt _).comp
      (analyticAt_snd.comp analyticAt_fst)
  · intro r
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Hm.Ω 1 × Fin N => ℂ) r).analyticAt _).comp
      (analyticAt_fst.comp analyticAt_snd)
  · intro y i
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt _).comp
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ K =>
        Fin N → ℂ) y).analyticAt _).comp (analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)))

theorem flReal_facts {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))}
    (ht : t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    (∀ x : Gp.Ω 1, Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖t.1.2 x‖ ≤ rho4 d L N BG κ) ∧
    SupBounds Hm t.2.1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧ t.2.2.2 ∈ FlBall Hm δ₁ := by
  obtain ⟨s, D, ψ', δα, -, -, -, hψ, hI, ht22, -, -, -, -, hsup⟩ := ht
  refine ⟨hI.small, hsup, ?_⟩
  rw [ht22]; exact hψ

/-- **The block energy is bounded on the realizable triples.** -/
theorem blockEnergyFun_bound (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n + 1 ≤ K) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))}
    (ht : t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    ‖blockEnergyFun Gp Hm (compWeight L a₁) ν n z t.1 t.2.1 t.2.2‖ ≤
      energyBd d L N (compWeight L a₁) ν n (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
        (rho4 d L N BG κ) := by
  obtain ⟨hα, hsup, hψ⟩ := flReal_facts ht
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hρ : 0 ≤ rho4 d L N BG κ := by
    have hBG := hC.hS.fam.2.1
    have hB1 : 0 ≤ famConst d L BG κ := by
      have := famConst_ge_one (L := L) hBG κ hd0; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
  have ha : 0 ≤ compWeight L a₁ n :=
    (hC.HBp.weights n hn1 (by omega)).1.trans' (by norm_num)
  exact energyBlock_bound hn ha hC.HBp.mass hV hC.δ₁_pos.le hρ hsup.val hα
    (fun x hx i => by
      have hxd : x ∈ dataSites Hm := (mem_dataSites Hm).2 (Or.inl hx)
      exact (norm_le_vn _ i).trans (hψ x hxd).le) z

/-- **Locality of the block energy**: it reads the multiplier on the block, and the fluctuation
and the tangent on the sites `readSites`. -/
theorem blockEnergyFun_local (a : ℕ → ℝ) (ν : ℝ) (n : ℕ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    {t t' : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))}
    (hα : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ (↑(blockSites d L N₁ m₁ K n z) :
      Set (CTorus d L N₁ m₁ K)) → t.1.2 y = t'.1.2 y)
    (hδ : ∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ readSites Hm n z → ∀ i,
      t.2.1 (y, i) = t'.2.1 (y, i))
    (hψ : ∀ y ∈ psiThick (readSites Hm n z), t.2.2.2 y = t'.2.2.2 y) :
    blockEnergyFun Gp Hm a ν n z t.1 t.2.1 t.2.2 = blockEnergyFun Gp Hm a ν n z t'.1 t'.2.1 t'.2.2 := by
  classical
  unfold blockEnergyFun energyBlock
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxb : x ∈ blockSites d L N₁ m₁ K n z := hx
  have hxr : x ∈ readSites Hm n z := ⟨x, hxb, Or.inl rfl⟩
  refine energyDensity_congr (fun h => hα ⟨x, h⟩ (by simpa using hxb)) (fun y hy i => ?_)
    (hψ x (Or.inl hxr))
  have hyr : y ∈ readSites Hm n z := ⟨x, hxb, hy⟩
  by_cases hyΩ : y ∈ Hm.Ω 1
  · rw [svec_of_mem' _ hyΩ, svec_of_mem' _ hyΩ]
    exact hδ ⟨y, hyΩ⟩ hyr i
  · rw [svec_of_not_mem Hm _ hyΩ, svec_of_not_mem Hm _ hyΩ]

omit [NeZero L] in
theorem energyBd_nonneg {a : ℕ → ℝ} {ν : ℝ} {n : ℕ} (ha : 0 ≤ a n) (hν : 0 ≤ ν) {V δ ρ : ℝ}
    (hV : 0 ≤ V) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) : 0 ≤ energyBd d L N a ν n V δ ρ := by
  unfold energyBd
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  positivity

/-- **The block energy expands over the domains `Y ⊃ X₁`** (Lemma AE for the decoupled objects,
FLUCTUATION §3.3, "the `V`-part", (AE1) and (AE2) from `blockEnergyFun_analytic`,
`blockEnergyFun_bound`, `blockEnergyFun_local`; `d_j(X) = 0` since the cover of the block is one
cube). -/
theorem vblock_expansion (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
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
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n + 1 ≤ K) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (hZ : readSites Hm n z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K))) :
    ∃ Ev : Set (CTorus d L N₁ m₁ K) →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        energyBlock Gp Hm (compWeight L a₁) ν n (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') ψ' z =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψ')) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet Gp Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ‖Ev Y u‖ ≤ energyBd d L N (compWeight L a₁) ν n (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
          (rho4 d L N BG κ) * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hρ : 0 ≤ rho4 d L N BG κ := by
    have hBG := hC.hS.fam.2.1
    have hB1 : 0 ≤ famConst d L BG κ := by
      have := famConst_ge_one (L := L) hBG κ hd0; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
  have ha : 0 ≤ compWeight L a₁ n :=
    (hC.HBp.weights n hn1 (by omega)).1.trans' (by norm_num)
  have hEb := energyBd_nonneg (d := d) (L := L) (N := N) ha hC.HBp.mass hV hC.δ₁_pos.le hρ
  obtain ⟨Ev, h1', h2', h3', h4'⟩ := i5_functional hC hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog
    hEb (Φ := blockEnergyFun Gp Hm (compWeight L a₁) ν n z)
    ((blockEnergyFun_analytic _ ν n z).mono (Set.subset_univ _))
    (fun t ht => by
      rw [hΔ]; simpa using blockEnergyFun_bound hC hn1 hn z ht)
    (Z := readSites Hm n z) (Zα := ↑(blockSites d L N₁ m₁ K n z)) hZ hmar
    (fun t _ t' _ _ hα hδ _ hψ => blockEnergyFun_local _ ν n z hα hδ hψ)
  refine ⟨Ev, h1', h2', fun Y u hu => ?_, h4'⟩
  have := h3' Y u hu
  rw [hΔ] at this
  simpa using this

open Classical in
/-- **The block energy as a function of the raw data and the fluctuation** (`0` for
unrealizable data). -/
noncomputable def blockEnergyOne (Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm) (a₁ ν BG₂ κ eps : ℝ) (n : ℕ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) : ℂ :=
  if h : ∃ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D ∧ u.1 = rawOf D then
    energyBlock Gp Hm (compWeight L a₁) ν n (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) h.choose)
      (flFieldOne Gp Hm BG₂ κ a₁ ν h.choose u.2) u.2 z
  else 0

theorem blockEnergyOne_rawOf {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν K 1 eps D)
    (n : ℕ) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z (rawOf D, ψ') =
      energyBlock Gp Hm (compWeight L a₁) ν n (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
        (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') ψ' z := by
  classical
  have h : ∃ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D' ∧ rawOf D = rawOf D' :=
    ⟨D, hD, rfl⟩
  unfold blockEnergyOne
  simp only [h, dite_true]
  have := BgData.eq_of_raw h.choose_spec.2
  rw [← this]

/-- **The potential part of the localized interaction, one block** (Proposition 3.3, the
`V`-part): the third-derivative term `σ ∫₀¹ ω(t') ∂_w³ ℰ_z(Θ, σ t' x₀) dt'` of the block energy is
a localized expansion over the domains `Y ⊃ X₁` with the bound
`|σ| M_ω 6 E_z e^{-2 κ d̃^{cov}_{k+1}(Y)} / r³`, `E_z = energyBd`. -/
theorem vblock_locInt (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
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
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n + 1 ≤ K) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (hZ : readSites Hm n z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)))
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
        (fun Y x₀ w σ Θ => rayTerm (dl3 (Ev Y) w) ω x₀ σ Θ)
        (fun x₀ w σ Θ => raySrc3 (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z) ω x₀ w σ Θ)
        (fun Y => Mω * (6 * ‖energyBd d L N (compWeight L a₁) ν n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)‖ / r ^ 3))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  obtain ⟨Ev, hsum, hloc, hbd, hanY⟩ := vblock_expansion hC hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ
    h1 hlog hn1 hn z hZ hmar
  refine ⟨Ev, ?_⟩
  refine locInt_dir3 (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps) (B := FlBall Hm δ₁)
    (f := blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z) _ hR₁ hω hωc hMω hωb hr hanY
    (fun Y u hu => hbd Y u hu) ?_ ?_ ?_
  · intro Y a a' b b' p q ha hb y hy
    simp [ha y hy, hb y hy]
  · intro Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2'
    exact hloc Y (Θ, z) ⟨hΘ, hz⟩ (Θ', z') ⟨hΘ', hz'⟩ h1' h2'
  · intro Θ hΘ ψ' hψ
    obtain ⟨D, hD, rfl⟩ := hΘ
    rw [blockEnergyOne_rawOf hD n z ψ']
    exact hsum D hD ψ' hψ

/-- **The potential part of the localized interaction, all blocks.**  The block covers
(`m₀, j, X, 𝒦X, X₁`) are indexed by the block. -/
theorem vblocks_locInt {n : ℕ} (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {m₀ j : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → ℕ}
    {X 𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K)}
    {X₁f : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (CTorus d L N₁ m₁ K)}
    (hcov : ∀ z, CovSetup Gp (m₀ z) (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁f z) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀ z) (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne (m₀ z) (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L (m₀ z) m₁ (j z)) E₀ = treeLenCovOne (m₀ z) (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne (m₀ z) (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ z, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ z) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hn1 : 1 ≤ n) (hn : n + 1 ≤ K)
    (hZ : ∀ z, readSites Hm n z ⊆ ↑(X₁f z))
    (hmar : ∀ z, BlockMargin Gp (X₁f z) (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (Set (CTorus d L N₁ m₁ K)))
      (T : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K) →
        (CTorus d L N₁ m₁ K → Fin N → ℂ) → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ →
        RawData d L (N₁ * L ^ m₁) K N → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (Finset.univ.biUnion 𝒴)
        (fun Y x₀ w σ Θ => ∑ z, if Y ∈ 𝒴 z then T z Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => ∑ z, raySrc3 (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z) ω x₀ w σ Θ)
        (fun Y => ∑ z, if Y ∈ 𝒴 z then Mω * (6 * ‖energyBd d L N (compWeight L a₁) ν n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ z) Y)‖ / r ^ 3) else 0)
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  have hex : ∀ z, ∃ (Ev : Set (CTorus d L N₁ m₁ K) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp
          (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z)))
        (fun Y x₀ w σ Θ => rayTerm (dl3 (Ev Y) w) ω x₀ σ Θ)
        (fun x₀ w σ Θ => raySrc3 (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z) ω x₀ w σ Θ)
        (fun Y => Mω * (6 * ‖energyBd d L N (compWeight L a₁) ν n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ z) Y)‖ / r ^ 3))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := fun z =>
    vblock_locInt hC (hcov z) (hX₁ z) hconn hrow (hopt z) (hΔ z) hκ₀ hκdec hκ h1 (hlog z) hn1 hn z
      (hZ z) (hmar z) hωc hR₁ hω hMω hωb hr
  choose Ev hEv using hex
  exact ⟨fun z => polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ K)) =>
      i.1.1) Gp (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z)),
    fun z Y x₀ w σ Θ => rayTerm (dl3 (Ev z Y) w) ω x₀ σ Θ,
    LocInt.finsum Finset.univ (fun z _ => hEv z)⟩

end VBlock

end Balaban.Localization
