/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusObsActivity

/-!
# The source part of the activities of the observable on two tori: the site terms

At a parameter of nonzero source, the direct terms of the zero class have, besides the potential
part, the source part
`β ∑_s g(s) [Y ∈ polyDom_s] dirTerm (Ev_s Y) (fun _ => 1) x₂ w₂ σ Θ`
(the appended conjunct of `sourceDirectTerms_scale_fromTowerG_ray_rho`).  Here the terms `Ev_s` of the
expansion of the site functional `δφ(s)` are explicit, `Ev_s = evTerm … (siteFun …)`.  This file
compares this source part on two tori.

## Main statements

* `dirTerm_eq_of_line`: the directional Cauchy term reads its function only on the discs
  `{(Θ, σ t x₀ + τ w) : ‖τ‖ < 1}`, when the function is differentiable at the points `(Θ, σ t x₀)`.
* `mem_of_mem_polyDom_site`: the site `x` lies in each domain of the expansion with the local cover
  of `x`.
* `dirTerm_siteEv_twoTorus`: the terms `dirTerm (Ev Y) …` of the expansion of the site functional
  `δφ(xs, iy)` on the first torus and of `δφ(bm xs, iy)` on the second at `bm '' Y` and `Y` agree,
  for corresponding data.
* `sourcePart_twoTorus`: the source parts of the two tori agree for corresponding labels and
  sources.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale Filter Topology

/-! ### The directional Cauchy term reads the function on a line -/

section Germ

variable {Λ F Λ' F' : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup Λ'] [NormedSpace ℂ Λ']
  [NormedAddCommGroup F'] [NormedSpace ℂ F']

/-- **The directional Cauchy term reads its function only near the ray.**  If two functions `Ev`,
`Ev'` are differentiable at the points `(Θ, σ t x₀)`, `(Θ', σ t x₀')` and agree on the discs
`{(Θ, σ t x₀ + τ w) : ‖τ‖ < 1}`, `{(Θ', σ t x₀' + τ w')}` for every `t ∈ [0, 1]`, the terms
`σ ∫₀¹ ω(t) ∂_w Ev(Θ, σ t x₀) dt` agree. -/
theorem dirTerm_eq_of_line (Ev : Λ × F → ℂ) (Ev' : Λ' × F' → ℂ) (ω : ℂ → ℂ) (x₀ w : F)
    (x₀' w' : F') (σ : ℂ) (Θ : Λ) (Θ' : Λ')
    (hd : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → DifferentiableAt ℂ Ev (Θ, (σ * (t : ℂ)) • x₀))
    (hd' : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → DifferentiableAt ℂ Ev' (Θ', (σ * (t : ℂ)) • x₀'))
    (h : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ < 1 →
      Ev' (Θ', (σ * (t : ℂ)) • x₀' + τ • w') = Ev (Θ, (σ * (t : ℂ)) • x₀ + τ • w)) :
    dirTerm Ev' ω x₀' w' σ Θ' = dirTerm Ev ω x₀ w σ Θ := by
  unfold dirTerm
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  congr 1
  rw [dirD_eq_lineD _ (hd' t ht), dirD_eq_lineD _ (hd t ht)]
  unfold lineD
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with τ hτ
  exact h t ht τ (by simpa [Metric.mem_ball] using hτ)

end Germ

/-! ### The terms of the site functional on two tori -/

section SiteTerm

open Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
set_option hygiene false in
local notation "HA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "HB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  k (Nat.le_succ k)
set_option hygiene false in
local notation "ρ₁" => R + (3 * L ^ (k + 1 + m₁) + 3 * L ^ (k + 1 + 2)) + L ^ (k + 1 + m₁)
set_option hygiene false in
local notation "XA" => (↑(LocalCover.nbhdF m₀ xs) : Set (CTorus d L N₁ m₁ (k + 1)))
set_option hygiene false in
local notation "XB" => (↑(LocalCover.nbhdF m₀ (bm xs)) : Set (CTorus d L N₁' m₁ (k + 1)))

/-- **The site lies in each domain of its own expansion.**  A domain `Y` of the expansion with the
local cover of `x` contains the region `X₁` of `x`, in particular `x`. -/
theorem mem_of_mem_polyDom_site {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (x : CTorus d L N₁ m₁ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hY : Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ x) m₀ k (LocalCover.fam m₀ x)) : x ∈ Y := by
  have hsub := nbhd_subset_of_mem_polyDom hN x hY
  refine hsub ?_
  rw [← LocalCover.coe_nbhdF]
  exact Finset.mem_coe.2 (LocalCover.mem_nbhdF_self m₀ x)

/-- **D2 (site term): the terms `dirTerm (Ev Y) …` of the site functional on two tori.**  Let
`Ev = evTerm … (siteFun … xs iy)` on the first torus and `Ev' = evTerm … (siteFun … (bm xs) iy)`
on the second, for decoupled pairs, analytic on the data of the chart and the hat variables of
size `≤ c_ψ`.  If the neighbourhood of `xs` and the set `Y` lie in the box of radius `R`, then for
corresponding data (raw data agreeing on the box of radius `R + 3 L^(k+1)`, hat fields `x₀, w` and
`x₀', w'` of size `≤ ρ₀`, `2 ρ₀ ≤ c_ψ`, agreeing at corresponding unit points of the box) and
`‖σ‖ ≤ 1`, the terms `σ ∫₀¹ ∂_w Ev(Θ, σ t x₀) dt` of `bm '' Y` and of `Y` are equal.  At each point
of the disc `σ t x₀ + τ w`, `‖τ‖ < 1`, the terms agree by `siteEv_twoTorus`; the directional
derivative reads only that disc (`dirTerm_eq_of_line`). -/
theorem dirTerm_siteEv_twoTorus
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small (HA) (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' p).2 ∧
        Small (HB) (Sol' p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' p).2))
    {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁') (xs : CTorus d L N₁ m₁ (k + 1))
    (iy : Fin N) {R : ℕ}
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ xs, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hn : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 12 * L ^ (k + 1 + m₁) + 7 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnS : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnS' : 2 * (ρ₁) + 5 * (L * cellSide L 0 m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {D : BgData (GA) N} {D' : BgData (GB) N}
    (hD : XiCData (GA) (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData (GB) (compWeight L a₁) ν (k + 1) 1 eps D')
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (rawOf D) (rawOf D'))
    {x₀ w : unitPts (GA) × Fin N → ℂ} {x₀' w' : unitPts (GB) × Fin N → ℂ} {ρ₀ : ℝ}
    (hx₀ : ∀ p, ‖x₀ p‖ ≤ ρ₀) (hw : ∀ p, ‖w p‖ ≤ ρ₀) (hx₀' : ∀ p, ‖x₀' p‖ ≤ ρ₀)
    (hw' : ∀ p, ‖w' p‖ ≤ ρ₀) (hρ₀ : 2 * ρ₀ ≤ cψ)
    (hhx : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, x₀' (unitPt hGB (bm x), i) = x₀ (unitPt hGA x, i))
    (hhw : ∀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x →
      ∀ i, w' (unitPt hGB (bm x), i) = w (unitPt hGA x, i))
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁)
    {Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (GA) × Fin N → ℂ) → ℂ}
    {Ev' : Set (CTorus d L N₁' m₁ (k + 1)) →
      RawData d L (N₁' * L ^ m₁) (k + 1) N × (unitPts (GB) × Fin N → ℂ) → ℂ}
    (hEv : Ev = evTerm (fun i : ParIdx (GA) (XA) => i.1.1) (GA) m₀
        (X1 (GA) m₀ k (LocalCover.fam m₀ xs))
        (fun u s => siteFun (GA) (HA) xs iy (F₁ (extParams (GA) (XA) s, u.1))
          (Sol (extParams (GA) (XA) s,
            flEdat (GA) (HA) (F₁ (extParams (GA) (XA) s, u.1))
              u.1.1 (hatPsiF (GA) a₁ ν hGA cc F₁
                (extParams (GA) (XA) s) u.1 u.2))).1
          (u.1, hatPsiF (GA) a₁ ν hGA cc F₁
            (extParams (GA) (XA) s) u.1 u.2)))
    (hEv' : Ev' = evTerm (fun i : ParIdx (GB) (XB) => i.1.1) (GB)
        m₀ (X1 (GB) m₀ k (LocalCover.fam m₀ (bm xs)))
        (fun u s => siteFun (GB) (HB) (bm xs) iy
          (F₁' (extParams (GB) (XB) s, u.1))
          (Sol' (extParams (GB) (XB) s,
            flEdat (GB) (HB) (F₁' (extParams (GB)
              (XB) s, u.1)) u.1.1
              (hatPsiF (GB) a₁ ν hGB cc F₁'
                (extParams (GB) (XB) s) u.1 u.2))).1
          (u.1, hatPsiF (GB) a₁ ν hGB cc F₁'
            (extParams (GB) (XB) s) u.1 u.2)))
    (hanEv : AnalyticOnNhd ℂ (Ev Y) (XiCRaw (GA) (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      {ψh : unitPts (GA) × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    (hanEv' : AnalyticOnNhd ℂ (Ev' (bm '' Y)) (XiCRaw (GB) (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
      {ψh : unitPts (GB) × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}))
    {σ : ℂ} (hσ : ‖σ‖ ≤ 1) :
    dirTerm (Ev' (bm '' Y)) (fun _ => (1 : ℂ)) x₀' w' σ (rawOf D') =
      dirTerm (Ev Y) (fun _ => (1 : ℂ)) x₀ w σ (rawOf D) := by
  have hst : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖σ * (t : ℂ)‖ ≤ 1 := fun t ht => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    nlinarith [norm_nonneg σ, ht.2]
  have hpt : ∀ {U : Type} (z : U × Fin N → ℂ), (∀ p, ‖z p‖ ≤ ρ₀) → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ∀ p, ‖((σ * (t : ℂ)) • z) p‖ ≤ cψ := fun z hz t ht p => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    calc ‖σ * (t : ℂ)‖ * ‖z p‖ ≤ 1 * ρ₀ :=
          mul_le_mul (hst t ht) (hz p) (norm_nonneg _) zero_le_one
      _ ≤ cψ := by linarith
  refine dirTerm_eq_of_line _ _ _ x₀ w x₀' w' σ _ _ (fun t ht => ?_) (fun t ht => ?_)
    (fun t ht τ hτ => ?_)
  · exact (hanEv (rawOf D, (σ * (t : ℂ)) • x₀) ⟨⟨D, hD, rfl⟩, hpt x₀ hx₀ t ht⟩).differentiableAt
  · exact (hanEv' (rawOf D', (σ * (t : ℂ)) • x₀') ⟨⟨D', hD', rfl⟩, hpt x₀' hx₀' t ht⟩).differentiableAt
  · have hb : ∀ {U : Type} (z z' : U × Fin N → ℂ), (∀ p, ‖z p‖ ≤ ρ₀) → (∀ p, ‖z' p‖ ≤ ρ₀) →
        ∀ p, ‖((σ * (t : ℂ)) • z + τ • z') p‖ ≤ cψ := fun z z' hz hz' p =>
      (norm_ray_add_le hz hz' (hst t ht) hτ p).trans hρ₀
    rw [hEv, hEv']
    refine siteEv_twoTorus hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol' hN hN' xs
      iy hX₁R hYR hn hn' hnS hnS' hnF hnF' hD hD' hraw (hb x₀ w hx₀ hw) (hb x₀' w' hx₀' hw')
      (fun x hx i => ?_) hrad
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hhx x hx i, hhw x hx i]

/-- **D2 (source part): the sums over the source sites on two tori.**  For a set `Y` in the box of
radius `R` and summands `a`, `b` of the sites of the two tori with `b (bm x, i) = a (x, i)` whenever
the domain `Y` belongs to the expansion with the local cover of `x`, the sums over the sites whose
local cover has `bm '' Y` (resp. `Y`) as a domain agree.  The sites with this property lie in
`Y`, hence in the box; `bm` is a bijection of them (`mem_polyDom_site_boxMap`). -/
theorem sourceSum_twoTorus {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (a : CTorus d L N₁ m₁ (k + 1) × Fin N → ℂ) (b : CTorus d L N₁' m₁ (k + 1) × Fin N → ℂ)
    (hab : ∀ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1) →
        b (bm s.1, s.2) = a s) :
    (∑ s' : CTorus d L N₁' m₁ (k + 1) × Fin N,
      if bm '' Y ∈ polyDom (GB) (LocalCover.nbhdF m₀ s'.1) m₀ k (LocalCover.fam m₀ s'.1)
        then b s' else 0) =
    ∑ s : CTorus d L N₁ m₁ (k + 1) × Fin N,
      if Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1)
        then a s else 0 := by
  have hc1 : 1 ≤ 5 * (L * cellSide L m₀ m₁ (k + 1)) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by norm_num)
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ (k + 1))))
  have hsA : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hsB : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hYR' : ∀ y ∈ bm '' Y, InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) y := by
    rintro _ ⟨y, hy, rfl⟩
    exact inBox_boxMap hsB (hYR y hy)
  have hYY : bm' '' (bm '' Y) = Y := image_image_boxMap hsB hYR
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij' (fun s' _ => (bm' s'.1, s'.2)) (fun s _ => (bm s.1, s.2))
    (fun s' hs' => ?_) (fun s hs => ?_) (fun s' hs' => ?_) (fun s hs => ?_) (fun s' hs' => ?_)
  · rw [Finset.mem_filter] at hs' ⊢
    have h := (mem_polyDom_site_boxMap (ϱ := ϱ) hN' hN hnF' hnF s'.1 hYR' hs'.2).2
    rw [hYY] at h
    exact ⟨Finset.mem_univ _, h⟩
  · rw [Finset.mem_filter] at hs ⊢
    exact ⟨Finset.mem_univ _, (mem_polyDom_site_boxMap (ϱ := ϱ) hN hN' hnF hnF' s.1 hYR hs.2).2⟩
  · rw [Finset.mem_filter] at hs'
    have h := (mem_polyDom_site_boxMap (ϱ := ϱ) hN' hN hnF' hnF s'.1 hYR' hs'.2).1
    exact Prod.ext (boxMap_boxMap hsA h) rfl
  · rw [Finset.mem_filter] at hs
    have h := (mem_polyDom_site_boxMap (ϱ := ϱ) hN hN' hnF hnF' s.1 hYR hs.2).1
    exact Prod.ext (boxMap_boxMap hsB h) rfl
  · rw [Finset.mem_filter] at hs'
    have h := (mem_polyDom_site_boxMap (ϱ := ϱ) hN' hN hnF' hnF s'.1 hYR' hs'.2)
    rw [hYY] at h
    have e := hab (bm' s'.1, s'.2) h.2
    simp only at e
    rw [boxMap_boxMap hsA h.1] at e
    exact e

end SiteTerm

end Balaban.Polymer.TwoTorusStep
