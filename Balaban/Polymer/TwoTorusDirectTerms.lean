/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusE1Coef
public import Balaban.Fluctuation.ParamActivitySubspace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The direct terms of the zero class on two tori

For two step tori `CTorus d L N₁ m₁ (k + 1)` and `CTorus d L N₁' m₁ (k + 1)` identified on a centred
box by `boxMap` (`bm`; `bc` on the coarse tori of the blocks), this file compares the explicit
direct terms of the zero class at zero source and discharges, for them, the two hypotheses
`ψ₀` (correspondence of the domain labels) and `hA` (agreement of their activities) of
`gsumCoeff_e1_twoTorus_of_domainLabels`.

## The explicit form of the direct terms (what the landed chain does not export)

In the landed construction the `DirectTerms` witness `I` of the zero class comes from
`sourceDirectTerms_slice_ray`, which takes `𝒴`, `T` from the existential
`interaction_expansion_hat_dm_core_dir_eta_scaled_ray`; that theorem assembles the four parts and
the `ν`-part by `LocIntDm.assemble_ray` and `LocIntDm.addLift_ray`.  For the zero class the old-term
and observable families are empty and `cν = 0`, and at zero source the source part vanishes (its
terms are `∑_s g_s · (…)`, `LocIntDm.wsum`).  What remains at zero source is the potential part,
`-β ∑_z [Y ∈ polyDom_z] T_V(z, Y)`.  Its terms `T_V(z, Y) = σ ∫₀¹ ω(t) ∂_w³ Ev_z(Y)(Θ, σ t x₀) dt`
come from the existential `vpart_locInt_hat_dir_dm_scaled_ray`, whose `Ev_z` is chosen from
`vblock_locInt_hat_dir_scaled` (from `vblock_expansion_hat_rawY_scaled`,
`i5_functional_hat_rawY_of_fan`, `i5_functional_rel_of_fan`); there `Ev_z = evTerm … FF` with `FF`
built from a decoupled background map `F₁` (`i4b_analytic`) and a fluctuation map `Sol`
(`Dec2.i4a_analytic`) obtained existentially.  Hence the explicit form of the potential part is
`evDec … F₁ Sol (blockEnergyFun … z) ∅ 1 0` for SOME pair with the defining properties of
`F₁`, `Sol` (`FFmarked_one_zero`); these theorems are not in the chain of
`sourceDirectTerms_slice_ray`, and no conjunct is added to landed statements here.  The theorems
below take the explicit form as a hypothesis on the witness (`hI𝒴`, `hIT`).

## The third directional derivative reads one line

* `lineD_add_smul`, `lineD3_eq`, `dl3_eq_deriv3`: `dl3 Ev w (Θ, z)` is the third derivative at `0`
  of `τ ↦ Ev (Θ, z + τ w)`.
* `deriv3_eq_of_eqOn_ball`, `rayTerm_dl3_eq_of_line`: the ray term
  `σ ∫₀¹ ω(t) ∂_w³ Ev(Θ, σ t x₀) dt` depends on `Ev` only on the discs
  `{(Θ, σ t x₀ + τ w) : ‖τ‖ < 1}`, `t ∈ [0, 1]`.

## D2: two-torus locality of the explicit terms

* `vblockTerm_twoTorus`: the potential term of the block `bc b` at `bm '' Y` equals that of `b` at
  `Y` (`evDec_rootBlock_twoTorus` at each point of the discs).
* `mem_polyDom_blockSite_boxMap`, `mem_polyDom_site_boxMap`: a domain of the box of the expansion of
  a block (resp. a site) goes to a domain of the image block (resp. site).
* `vpartTerm_twoTorus`: the potential part `∑_z [Y ∈ polyDom_z] T_V(z, Y)` at `bm '' Y` on the
  second torus equals that at `Y` on the first, for `Y` in the box and corresponding data.
* `mem_vDomains_boxMap_iff`, `mem_fDomains_boxMap_iff`: the domains of the potential and of the
  source part correspond on the box.

## D3: the energy coefficient

* `gsumCoeff_e1_twoTorus_of_directTerms`: the energy coefficient `c θ T` of the zero class with the
  labels `thickLabels I.𝒴 I.dom` and the activity `zeroSourceAct (labelActFamilyOn … I hF) 2` of the
  landed construction agrees on two tori, for witnesses `I`, `I'` of the explicit form.  The
  hypotheses `ψ₀`, `hA` of `gsumCoeff_e1_twoTorus_of_domainLabels` are discharged.

Only labels and blocks of a common box are compared; labels that wind around a torus are not
covered.  Not done here: the explicit form of the landed witness (the conjuncts listed above), the
observable coefficient, the assembly of `E0`, the specialization to `T.step`, the last scales.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis
  Balaban.Polymer Balaban.Multiscale Filter Topology

/-! ### The third directional derivative reads the function on a line -/

section Germ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The directional derivative at a point of the line `p + τ v` is the derivative of the
restriction of the function to the line. -/
theorem lineD_add_smul (v : E) (f : E → ℂ) (p : E) (τ : ℂ) :
    lineD v f (p + τ • v) = deriv (fun t : ℂ => f (p + t • v)) τ := by
  unfold lineD
  have e : (fun t : ℂ => f (p + τ • v + t • v)) =
      fun t : ℂ => (fun t => f (p + t • v)) (τ + t) := by
    funext t; simp only [add_smul, add_assoc]
  rw [e]
  have := deriv_comp_const_add (f := fun t : ℂ => f (p + t • v)) (a := τ) (x := (0 : ℂ))
  rw [add_zero] at this
  exact this

/-- The third directional derivative is the third derivative of the restriction to the line. -/
theorem lineD3_eq (v : E) (f : E → ℂ) (p : E) :
    lineD v (lineD v (lineD v f)) p =
      deriv (deriv (deriv (fun t : ℂ => f (p + t • v)))) 0 := by
  have h1 : ∀ g : E → ℂ, (fun t : ℂ => lineD v g (p + t • v)) =
      deriv (fun t : ℂ => g (p + t • v)) := by
    intro g; funext t; exact lineD_add_smul v g p t
  show deriv (fun t : ℂ => lineD v (lineD v f) (p + t • v)) 0 = _
  simp only [h1]

/-- `dl3 Ev w (Θ, z)` is the third derivative at `0` of `τ ↦ Ev (Θ, z + τ w)`. -/
theorem dl3_eq_deriv3 {Λ F : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (Ev : Λ × F → ℂ) (w : F) (Θ : Λ) (z : F) :
    dl3 Ev w (Θ, z) = deriv (deriv (deriv (fun t : ℂ => Ev (Θ, z + t • w)))) 0 := by
  have hp : (fun t : ℂ => Ev (((Θ, z) : Λ × F) + t • ((0 : Λ), w))) =
      fun t : ℂ => Ev (Θ, z + t • w) := by
    funext t; congr 1; ext <;> simp
  unfold dl3
  rw [lineD3_eq, hp]

/-- Two functions of one complex variable that agree on a disc around `0` have the same third
derivative at `0`. -/
theorem deriv3_eq_of_eqOn_ball {g g' : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (h : ∀ t : ℂ, ‖t‖ < r → g' t = g t) :
    deriv (deriv (deriv g')) 0 = deriv (deriv (deriv g)) 0 := by
  have hev : ∀ t ∈ Metric.ball (0 : ℂ) r, g' =ᶠ[𝓝 t] g := by
    intro t ht
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
    exact h s (by simpa using hs)
  have hev1 : ∀ t ∈ Metric.ball (0 : ℂ) r, deriv g' =ᶠ[𝓝 t] deriv g := by
    intro t ht
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
    exact (hev s hs).deriv_eq
  have hev2 : ∀ t ∈ Metric.ball (0 : ℂ) r, deriv (deriv g') =ᶠ[𝓝 t] deriv (deriv g) := by
    intro t ht
    filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs
    exact (hev1 s hs).deriv_eq
  exact (hev2 0 (Metric.mem_ball_self hr)).deriv_eq

/-- **The ray term reads its function only near the ray.**  If two functions `Ev`, `Ev'` agree on
the discs `{(Θ, σ t x₀ + τ w) : ‖τ‖ < 1}` and `{(Θ', σ t x₀' + τ w')}` for every `t ∈ [0, 1]`, the
ray terms `σ ∫₀¹ ω(t) ∂_w³ Ev(Θ, σ t x₀) dt` agree. -/
theorem rayTerm_dl3_eq_of_line {Λ F Λ' F' : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup Λ'] [NormedSpace ℂ Λ']
    [NormedAddCommGroup F'] [NormedSpace ℂ F'] (Ev : Λ × F → ℂ) (Ev' : Λ' × F' → ℂ)
    (ω : ℂ → ℂ) (x₀ w : F) (x₀' w' : F') (σ : ℂ) (Θ : Λ) (Θ' : Λ')
    (h : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ < 1 →
      Ev' (Θ', (σ * (t : ℂ)) • x₀' + τ • w') = Ev (Θ, (σ * (t : ℂ)) • x₀ + τ • w)) :
    rayTerm (dl3 Ev' w') ω x₀' σ Θ' = rayTerm (dl3 Ev w) ω x₀ σ Θ := by
  unfold rayTerm
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  rw [dl3_eq_deriv3, dl3_eq_deriv3]
  congr 1
  exact deriv3_eq_of_eqOn_ball one_pos fun τ hτ => h t ht τ hτ

end Germ

/-! ### The potential term of one block on two tori -/

section VBlock

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
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
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))

/-- A point `σ t x₀ + τ w` of a ray stays in the polydisc of radius `2 ρ₀`. -/
theorem norm_ray_add_le {U : Type*} {x₀ w : U × Fin N → ℂ} {ρ₀ : ℝ}
    (hx₀ : ∀ p, ‖x₀ p‖ ≤ ρ₀) (hw : ∀ p, ‖w p‖ ≤ ρ₀) {σ τ : ℂ} (hσ : ‖σ‖ ≤ 1) (hτ : ‖τ‖ < 1)
    (p : U × Fin N) : ‖(σ • x₀ + τ • w) p‖ ≤ 2 * ρ₀ := by
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  have h1 : ‖σ * x₀ p‖ ≤ ρ₀ := by
    rw [norm_mul]
    calc ‖σ‖ * ‖x₀ p‖ ≤ 1 * ‖x₀ p‖ := mul_le_mul_of_nonneg_right hσ (norm_nonneg _)
      _ ≤ ρ₀ := by rw [one_mul]; exact hx₀ p
  have h2 : ‖τ * w p‖ ≤ ρ₀ := by
    rw [norm_mul]
    calc ‖τ‖ * ‖w p‖ ≤ 1 * ‖w p‖ := mul_le_mul_of_nonneg_right hτ.le (norm_nonneg _)
      _ ≤ ρ₀ := by rw [one_mul]; exact hw p
  linarith [norm_add_le (σ * x₀ p) (τ * w p)]

/-- **D2: the potential term of one block on two tori.**  For the block `B_{k+1}(b)` of the first
torus (`|b| ≤ r_c`, `L^(k+1) r_c ≤ R`) and the block `bc b` of the second, with their local covers,
a domain `Y` of the box of radius `R` and corresponding data (raw data agreeing on the box of
radius `R + 3 L^(k+1)`; hat fields `x₀, w` and `x₀', w'` of size `≤ ρ₀`, `2 ρ₀ ≤ c_ψ`, agreeing at
corresponding unit points of the box): the ray terms
`σ ∫₀¹ ω(t) ∂_w³ evDec(…)(Θ, σ t x₀) dt` of the block energy expansion (marks `(1, 0)`, no mask)
of `bc b` at `bm '' Y` and of `b` at `Y` are equal, for `‖σ‖ ≤ 1` and every weight `ω`.  At each
point of the disc `σ t x₀ + τ w`, `‖τ‖ < 1`, the terms agree by `evDec_rootBlock_twoTorus`; the
third derivative reads only that disc (`rayTerm_dl3_eq_of_line`). -/
theorem vblockTerm_twoTorus
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
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {rc R : ℕ}
    (hb : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) b) (hrc : L ^ (k + 1) * rc ≤ R)
    (hX₁R : ∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k b),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
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
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁) (ω : ℂ → ℂ) {σ : ℂ} (hσ : ‖σ‖ ≤ 1) :
    rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k (bc b))) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k (bc b))) a₁ ν hGB cc F₁' Sol'
        (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k (bc b)) ∅ 1 0 (bm '' Y)) w') ω x₀' σ
        (rawOf D') =
      rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k b)) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k b)) a₁ ν hGA cc F₁ Sol
        (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k b) ∅ 1 0 Y) w) ω x₀ σ (rawOf D) := by
  refine rayTerm_dl3_eq_of_line _ _ ω x₀ w x₀' w' σ _ _ fun t ht τ hτ => ?_
  have hst : ‖σ * (t : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    nlinarith [norm_nonneg σ, ht.2]
  refine evDec_rootBlock_twoTorus hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₁ hF₁' hSol hSol'
    hm₀ hN hN' b hb hrc hX₁R hYR hn hn' hnS hnS' hnF hnF' hD hD' hraw
    (fun p => (norm_ray_add_le hx₀ hw hst hτ p).trans hρ₀)
    (fun p => (norm_ray_add_le hx₀' hw' hst hτ p).trans hρ₀) (fun x hx i => ?_)
    (fun _ _ => by simp) (by simpa using hrad)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hhx x hx i, hhw x hx i]

/-- **The block domains of the box on two tori.**  If `Y` (in the box of radius `R`) is a domain of
the expansion of the block `B_{k+1}(z)` with its local cover (`X₁ = nbhdF m₀ (blockSite k z)`), then
`z` lies in the coarse box of radius `R / L^(k+1)`, the region `X₁` lies in the box of radius `R`
(`X₁ ⊆ Y`), and `bm '' Y` is a domain of the expansion of the block `bc z` of the second torus. -/
theorem mem_polyDom_blockSite_boxMap {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hY : Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
      (LocalCover.fam m₀ (LocalCover.blockSite k z))) :
    InBox d (R / L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z ∧
      (∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k z),
        InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) ∧
      bm '' Y ∈ polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k (bc z))) m₀ k
        (LocalCover.fam m₀ (LocalCover.blockSite k (bc z))) := by
  have hsub := nbhd_subset_of_mem_polyDom hN (LocalCover.blockSite k z) hY
  have hX : ∀ x ∈ LocalCover.nbhd m₀ (LocalCover.blockSite k z),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := fun x hx => hYR x (hsub hx)
  have hbs : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) (LocalCover.blockSite k z) :=
    hX _ (cell_subset_nbhd _ (LocalCover.mem_cell m₀ _))
  have hz := inBox_coarse_of_blockSite z hbs
  have hrc : L ^ (k + 1) * (R / L ^ (k + 1)) ≤ R := Nat.mul_div_le R _
  have hc1 : 1 ≤ 5 * (L * cellSide L m₀ m₁ (k + 1)) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by norm_num)
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ (k + 1))))
  have hs : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hbsB : LocalCover.blockSite k (bc z) = bm (LocalCover.blockSite k z) :=
    blockSite_boxMap le_rfl z hz hrc hs
  have hcs : (L - 1) * cellSide L m₀ m₁ (k + 1) ≤ L * cellSide L m₀ m₁ (k + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  obtain ⟨hcov, hX₁, hcov', hX₁'⟩ := covSetup_localCover_image (ϱ := ϱ) hN hN' (j := k) le_rfl
    (R := R) (by omega) (LocalCover.blockSite k z) hX
  have hF := nbhdF_image_finset hN hN' (R := R) (by omega) (LocalCover.blockSite k z) hX
  have hX₁R : ∀ x ∈ LocalCover.nbhdF m₀ (LocalCover.blockSite k z),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := fun x hx =>
    hX x (by rw [← LocalCover.coe_nbhdF]; exact hx)
  have hmem := mem_polyDom_boxMap_iff hcov hX₁ hcov' hX₁' hX₁R hnF hnF' Y hYR
  refine ⟨hz, hX, ?_⟩
  rw [hbsB, ← hF]
  exact hmem.2 hY

/-- **D2: the potential terms of all blocks at a domain of the box, on two tori.**  The potential
part of the direct terms at a domain `Y` is the sum over the blocks `z` of the coarse torus whose
expansion has `Y` as a domain of the ray terms of `vblockTerm_twoTorus`.  For `Y` in the box of
radius `R` and corresponding data, this sum at `bm '' Y` on the second torus equals the sum at `Y`
on the first: the blocks with `Y` (resp. `bm '' Y`) as a domain correspond by `bc`
(`mem_polyDom_blockSite_boxMap`, in both directions), and the terms agree
(`vblockTerm_twoTorus`). -/
theorem vpartTerm_twoTorus
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N (GA) (HA) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1)) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : TB → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    {Sol : TA →
      Dec2.DecParams (coverOf (GA)) × Edat (HA) N → ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : TB →
      Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (hSol' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2))
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    {R : ℕ} {Y : Set (CTorus d L N₁ m₁ (k + 1))}
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
    (hrad : markedRad d L N k a₁ κ cψ cc < δ₁) (ω : ℂ → ℂ) {σ : ℂ} (hσ : ‖σ‖ ≤ 1) :
    (∑ z' : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      if bm '' Y ∈ polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z')) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k z')) then
        rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k z')) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k z')) a₁ ν hGB cc (F₁' z') (Sol' z')
          (blockEnergyFun (GB) (HB) (compWeight L a₁) ν k z') ∅ 1 0 (bm '' Y)) w') ω x₀' σ
          (rawOf D')
      else 0) =
      ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        if Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
            (LocalCover.fam m₀ (LocalCover.blockSite k z)) a₁ ν hGA cc (F₁ z) (Sol z)
            (blockEnergyFun (GA) (HA) (compWeight L a₁) ν k z) ∅ 1 0 Y) w) ω x₀ σ (rawOf D)
        else 0 := by
  have hc1 : L ^ (k + 1) ≤ 5 * (L * cellSide L m₀ m₁ (k + 1)) := by
    have h1 : L ^ (k + 1) ≤ cellSide L m₀ m₁ (k + 1) := by
      unfold cellSide
      exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)
    have h2 : cellSide L m₀ m₁ (k + 1) ≤ L * cellSide L m₀ m₁ (k + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne L))
    omega
  have hcA := coarse_margin (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (r := R) (by omega)
  have hcB := coarse_margin (L := L) (N₁ := N₁') (m₁ := m₁) (k := k) (r := R) (by omega)
  have hsA : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  have hsB : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hYR' : ∀ y ∈ bm '' Y, InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) y := by
    rintro _ ⟨y, hy, rfl⟩
    exact inBox_boxMap hsB (hYR y hy)
  have hYY : boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) '' (bm '' Y) = Y :=
    image_image_boxMap hsB hYR
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun z => bc z)
    (fun z' => boxMap (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
      (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z') ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨Finset.mem_univ _,
      (mem_polyDom_blockSite_boxMap (ϱ := ϱ) hN hN' hnF hnF' z hYR hz.2).2.2⟩
  · intro z' hz'
    rw [Finset.mem_filter] at hz' ⊢
    have h := (mem_polyDom_blockSite_boxMap (ϱ := ϱ) hN' hN hnF' hnF z' hYR' hz'.2).2.2
    rw [hYY] at h
    exact ⟨Finset.mem_univ _, h⟩
  · intro z hz
    exact boxMap_boxMap hcB (mem_polyDom_blockSite_boxMap (ϱ := ϱ) hN hN' hnF hnF' z hYR
      (Finset.mem_filter.1 hz).2).1
  · intro z' hz'
    exact boxMap_boxMap hcA (mem_polyDom_blockSite_boxMap (ϱ := ϱ) hN' hN hnF' hnF z' hYR'
      (Finset.mem_filter.1 hz').2).1
  · intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hz0, hX, -⟩ := mem_polyDom_blockSite_boxMap (ϱ := ϱ) hN hN' hnF hnF' z hYR hz.2
    exact (vblockTerm_twoTorus hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm (hF₁ z) (hF₁' (bc z))
      (hSol z) (hSol' (bc z)) hm₀ hN hN' z hz0 (Nat.mul_div_le R _) hX hYR hn hn' hnS hnS' hnF
      hnF' hD hD' hraw hx₀ hw hx₀' hw' hρ₀ hhx hhw hrad ω hσ).symm

/-- **The site domains of the box on two tori.**  If `Y` (in the box of radius `R`) is a domain of
the expansion with the local cover of the site `x` (`X₁ = nbhdF m₀ x`), then `x` lies in the box
of radius `R` and `bm '' Y` is a domain of the expansion with the local cover of `bm x`. -/
theorem mem_polyDom_site_boxMap {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    (x : CTorus d L N₁ m₁ (k + 1)) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y)
    (hY : Y ∈ polyDom (GA) (LocalCover.nbhdF m₀ x) m₀ k (LocalCover.fam m₀ x)) :
    InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x ∧
      bm '' Y ∈ polyDom (GB) (LocalCover.nbhdF m₀ (bm x)) m₀ k (LocalCover.fam m₀ (bm x)) := by
  have hsub := nbhd_subset_of_mem_polyDom hN x hY
  have hX : ∀ y ∈ LocalCover.nbhd m₀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y :=
    fun y hy => hYR y (hsub hy)
  have hcs : (L - 1) * cellSide L m₀ m₁ (k + 1) ≤ L * cellSide L m₀ m₁ (k + 1) :=
    Nat.mul_le_mul_right _ (Nat.sub_le L 1)
  obtain ⟨hcov, hX₁, hcov', hX₁'⟩ := covSetup_localCover_image (ϱ := ϱ) hN hN' (j := k) le_rfl
    (R := R) (by omega) x hX
  have hF := nbhdF_image_finset hN hN' (R := R) (by omega) x hX
  have hX₁R : ∀ y ∈ LocalCover.nbhdF m₀ x, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y :=
    fun y hy => hX y (by rw [← LocalCover.coe_nbhdF]; exact hy)
  have hmem := mem_polyDom_boxMap_iff hcov hX₁ hcov' hX₁' hX₁R hnF hnF' Y hYR
  refine ⟨hX _ (cell_subset_nbhd _ (LocalCover.mem_cell m₀ _)), ?_⟩
  rw [← hF]
  exact hmem.2 hY

/-- **D2: the domains of the potential part on two tori.**  For `Y` in the box of radius `R`,
`bm '' Y` is a domain of the expansion of some block of the second torus iff `Y` is a domain of
the expansion of some block of the first (`mem_polyDom_blockSite_boxMap` in both directions). -/
theorem mem_vDomains_boxMap_iff {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    bm '' Y ∈ Finset.univ.biUnion (fun z' : Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        polyDom (GB) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z')) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k z'))) ↔
      Y ∈ Finset.univ.biUnion (fun z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) =>
        polyDom (GA) (LocalCover.nbhdF m₀ (LocalCover.blockSite k z)) m₀ k
          (LocalCover.fam m₀ (LocalCover.blockSite k z))) := by
  have hc1 : 1 ≤ 5 * (L * cellSide L m₀ m₁ (k + 1)) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by norm_num)
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ (k + 1))))
  have hsB : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hYR' : ∀ y ∈ bm '' Y, InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) y := by
    rintro _ ⟨y, hy, rfl⟩
    exact inBox_boxMap hsB (hYR y hy)
  have hYY : boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) '' (bm '' Y) = Y :=
    image_image_boxMap hsB hYR
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨z', hz'⟩
    have h := (mem_polyDom_blockSite_boxMap (ϱ := ϱ) hN' hN hnF' hnF z' hYR' hz').2.2
    rw [hYY] at h
    exact ⟨_, h⟩
  · rintro ⟨z, hz⟩
    exact ⟨_, (mem_polyDom_blockSite_boxMap (ϱ := ϱ) hN hN' hnF hnF' z hYR hz).2.2⟩

/-- **D2: the domains of the source part on two tori.**  For `Y` in the box of radius `R`,
`bm '' Y` is a domain of the expansion of some source site of the second torus iff `Y` is one of
the first (`mem_polyDom_site_boxMap` in both directions). -/
theorem mem_fDomains_boxMap_iff {m₀ R : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₁')
    (hnF : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hnF' : 2 * R + 5 * (L * cellSide L m₀ m₁ (k + 1)) < (N₁' * L ^ m₁) * L ^ (k + 1))
    {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    bm '' Y ∈ Finset.univ.biUnion (fun s' : CTorus d L N₁' m₁ (k + 1) × Fin N =>
        polyDom (GB) (LocalCover.nbhdF m₀ s'.1) m₀ k (LocalCover.fam m₀ s'.1)) ↔
      Y ∈ Finset.univ.biUnion (fun s : CTorus d L N₁ m₁ (k + 1) × Fin N =>
        polyDom (GA) (LocalCover.nbhdF m₀ s.1) m₀ k (LocalCover.fam m₀ s.1)) := by
  have hc1 : 1 ≤ 5 * (L * cellSide L m₀ m₁ (k + 1)) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by norm_num)
      (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ (k + 1))))
  have hsB : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hYR' : ∀ y ∈ bm '' Y, InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) y := by
    rintro _ ⟨y, hy, rfl⟩
    exact inBox_boxMap hsB (hYR y hy)
  have hYY : boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) '' (bm '' Y) = Y :=
    image_image_boxMap hsB hYR
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s', hs'⟩
    have h := (mem_polyDom_site_boxMap (ϱ := ϱ) hN' hN hnF' hnF s'.1 hYR' hs').2
    rw [hYY] at h
    exact ⟨(_, s'.2), h⟩
  · rintro ⟨s, hs⟩
    exact ⟨(bm s.1, s.2), (mem_polyDom_site_boxMap (ϱ := ϱ) hN hN' hnF hnF' s.1 hYR hs).2⟩

end VBlock

/-! ### D3: the energy coefficient of the zero class on two tori -/

section E1Coef

open MeasureTheory Balaban.Inhabited Balaban.Inhabited.LevelStep

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bc" => boxMap (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
  (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TA" => Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
set_option hygiene false in
local notation "TB" => Torus d (N₁' * L ^ m₁ * L ^ (k + 1 - (k + 1)))
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
local notation "SA" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁) hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "SB" => hatStepKG (d := d) (L := L) (N := N) (N₁ := N₁') hN2 k m₁ ϱ hk νS β p₁ δ
set_option hygiene false in
local notation "σc" => cubeMap (d := d) (L := L) (N₁ := N₁) (N₁' := N₁') (m₁ := m₁) (K := k + 1)
  (m₀ := 1) hN hN' (le_refl (k + 1))
set_option hygiene false in
local notation "ΛA" => RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
set_option hygiene false in
local notation "ΛB" => RawData d L (N₁' * L ^ m₁) (k + 1) N ×
  (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ)
set_option hygiene false in
local notation "FA" => ((SA).U × Fin N → ℂ) × ((SA).U × Fin N → ℂ)
set_option hygiene false in
local notation "FB" => ((SB).U × Fin N → ℂ) × ((SB).U × Fin N → ℂ)

/-- **D3: the energy coefficient of the zero class on two tori, for direct terms of the explicit
form.**  The hypotheses of `gsumCoeff_e1_twoTorus_of_domainLabels` without the domain labels and
their activities, which are now those of the landed construction: the labels are the domains of
`DirectTerms` instances `I`, `I'` of the two steps (`thickLabels I.𝒴 I.dom`), and the activity is
the zero-source family `zeroSourceAct (labelActFamilyOn … I hF) 2` of the relative family `hF`
over the parameters (scaled inclusion `physInclScaled … c`), with `(θ.1, 0) ∈ V`.  The direct
terms are assumed to have the explicit form of the zero class (the conjuncts that the existential
chain `sourceDirectTerms_slice_ray` does not yet export, see the report of `TwoTorusDirectTerms`):

* `hI𝒴`: the domains are those of the potential part (the polymer domains of the blocks `z` with
  the local covers `X₁ = nbhdF 1 (blockSite k z)`) and of the source part (the local covers of the
  sites);
* `hIT`: at zero source, the term of a domain `Y` is `-β ∑_z [Y ∈ polyDom_z] σ ∫₀¹ ω(t)
  ∂_w³ evDec_z(Y)(Θ, σ t x₀) dt`, the potential part of the expansion, with the localized block
  energy terms `evDec … F₂ Sol₂ … ∅ 1 0` of a pair `(F₂, Sol₂)` of decoupled background and
  fluctuation maps.

Then the energy coefficients agree: `c′ θ′ (cubeMap '' T) = c θ T`.  The domain labels correspond
by `bm` (`mem_vDomains_boxMap_iff`, `mem_fDomains_boxMap_iff`), and their activities by
`vpartTerm_twoTorus` at the clamped hat variables (`hatOf_boxMap`). -/
theorem gsumCoeff_e1_twoTorus_of_directTerms
    {c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} (hN2 : 2 ≤ N) (hk : 1 ≤ k) (νS β p₁ δ : ℝ)
    (hC : FlCore N (GA) (HA) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hC' : FlCore N (GB) (HB) 1 νS c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hGA : IsLevel (GA) (k + 1)) (hGB : IsLevel (GB) (k + 1))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαK : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : TA → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₁' : TB → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₁ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁ b (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₁' b (s, rawOf D) = (φ, α))
    {Sol : TA → Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol' : TB → Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol b p).2 ∧
        Small (HA) (Sol b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol b p).2))
    (hSol' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol' b p).2 ∧
        Small (HB) (Sol' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol' b p).2))
    (hN : L ^ 1 ∣ N₁) (hN' : L ^ 1 ∣ N₁') (hm₁ : 1 ≤ m₁)
    (z : TA) {rc R : ℕ} (hz : InBox d rc (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z)
    (hrc : L ^ (k + 1) * rc ≤ R)
    (hroot : ∀ x ∈ rootSet 1 z, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hn : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 4 * R + 19 * L ^ (k + 2 + 1 + m₁) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (θ : physParam N (SA)) (θ' : physParam N (SB))
    (hθ : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GA) (compWeight L 1) νS (k + 1) 1 eps)
    (hθ' : (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N) ∈
      XiCRaw (GB) (compWeight L 1) νS (k + 1) 1 eps)
    (hraw : RawBoxAgree {z | InBox d (R + 3 * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) z}
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N))
    {ρ : ℝ} (hρ : 0 < ρ) (hp : 0 < (SA).p₁) (hp' : 0 < (SB).p₁)
    (hum : ∀ u : ℂ, ‖u‖ ≤ 1 →
      ‖u‖ * markedRad d L N k 1 κ ρ (((SA).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (hGdep : ∀ (i : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ) (e1DomG (SA)) z}) (u : ℂ),
      DepOn (blocksOf 1 (k + 1) Set.univ i.1) (e1MarkGParamG (SA) F₁ Sol ρ hp z eps θ i u))
    (hL2 : 2 ≤ L) (hdom : ∀ b, ∀ Y ∈ e1DomG (SA) b, IsDj 1 (k + 1) Y)
    (hdom' : ∀ b, ∀ Y ∈ e1DomG (SB) b, IsDj 1 (k + 1) Y)
    {Lb Lb' : Type*} [Fintype Lb] [Fintype Lb']

    -- the direct terms of the two steps and their relative families
    {ρI Rσ εU a κ0 KcL : ℝ} {Θ₀ : ΛA} {Θ₀' : ΛB} {SΛ : Set ΛA} {SΛ' : Set ΛB}
    {XW : Set (FA × FA)} {XW' : Set (FB × FB)} {val : FA → FA → ℂ → ΛA → ℂ}
    {val' : FB → FB → ℂ → ΛB → ℂ} {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → ΛA → ΛA → Prop}
    {AgΘ' : Set (CTorus d L N₁' m₁ (k + 1)) → ΛB → ΛB → Prop}
    {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → FA → FA → Prop}
    {AgF' : Set (CTorus d L N₁' m₁ (k + 1)) → FB → FB → Prop}
    (I : DirectTerms (SA) 1 hp (fun ψ => (ψ, ψ)) ρI Rσ εU a Θ₀ SΛ XW val AgΘ AgF)
    (I' : DirectTerms (SB) 1 hp' (fun ψ => (ψ, ψ)) ρI Rσ εU a Θ₀' SΛ' XW' val' AgΘ' AgF')
    {cJ cJ' : ℂ} {V : Set (physParam N (SA))} {V' : Set (physParam N (SB))}
    (hF : DirectTermsFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I V)
    (hF' : DirectTermsFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' V')
    (hρI : 0 < ρI) (hRσ : 1 < Rσ) (hεU : 0 ≤ εU) (hκ0 : aEnt d L + 2 ≤ κ0)
    (hKc : K0 d L κ0 ≤ KcL)
    (hV : ((θ.1, 0) : physParam N (SA)) ∈ V) (hV' : ((θ'.1, 0) : physParam N (SB)) ∈ V')
    -- the explicit form of the direct terms at the zero source
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ) (hρc : 2 * ρI ≤ cψ)
    (hrad : markedRad d L N k 1 κ cψ cc < δ₁)
    {F₂ : TA → DecParams (GA) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GA).Ω 1 × Fin N → ℂ) × ((GA).Ω 1 → ℂ)}
    {F₂' : TB → DecParams (GB) × RawData d L (N₁' * L ^ m₁) (k + 1) N →
      ((GB).Ω 1 × Fin N → ℂ) × ((GB).Ω 1 → ℂ)}
    (hF₂ : ∀ (b : TA) (s : DecParams (GA)) (D : BgData (GA) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GA) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GA).Ω 1 × Fin N → ℂ)
        (α : (GA).Ω 1 → ℂ), IsDecBg (GA) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₂ b (s, rawOf D) = (φ, α))
    (hF₂' : ∀ (b : TB) (s : DecParams (GB)) (D : BgData (GB) N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (GB) (bgC0 d L N) (c7 d L N BG κ) νS D → ∀ (φ : (GB).Ω 1 × Fin N → ℂ)
        (α : (GB).Ω 1 → ℂ), IsDecBg (GB) (compWeight L 1) νS (rho4 d L N BG κ) s D φ α →
        F₂' b (s, rawOf D) = (φ, α))
    {Sol₂ : TA →
      Dec2.DecParams (coverOf (GA)) × Edat (HA) N →
      ((HA).Ω 1 × Fin N → ℂ) × ((HA).Ω 1 → ℂ)}
    {Sol₂' : TB →
      Dec2.DecParams (coverOf (GB)) × Edat (HB) N →
      ((HB).Ω 1 × Fin N → ℂ) × ((HB).Ω 1 → ℂ)}
    (hSol₂ : ∀ (b : TA) (p : Dec2.DecParams (coverOf (GA)) × Edat (HA) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HA) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂ b p).1 = dphi (HA) (Dec2.decG (coverOf (GA)) (HA) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ b p).2 ∧
        Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂ b p).2 ∧
        Small (HA) (Sol₂ b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HA) (Sol₂ b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HA) (Sol₂ b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HA).Ω 1 → ℂ, Small (HA) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GA)) (HA) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HA) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂ b p).2))
    (hSol₂' : ∀ (b : TB) (p : Dec2.DecParams (coverOf (GB)) × Edat (HB) N),
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (HB) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol₂' b p).1 = dphi (HB) (Dec2.decG (coverOf (GB)) (HB) (compWeight L 1) νS p.1) p.2.2.1
          p.2.1 (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
          (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) (Sol₂' b p).2 ∧
        Small (HB) (Sol₂' b p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (HB) (Sol₂' b p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (HB) (Sol₂' b p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (HB).Ω 1 → ℂ, Small (HB) δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GB)) (HB) (compWeight L 1) νS p.1 false p.2.2.1 p.2.1
            (pertSource (HB) (compWeight L 1) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol₂' b p).2))
    (hI𝒴 : I.𝒴 = (Finset.univ.biUnion fun z : TA =>
        polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁ m₁ (k + 1) × Fin N =>
        polyDom (GA) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    (hI𝒴' : I'.𝒴 = (Finset.univ.biUnion fun z : TB =>
        polyDom (GB) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
          (LocalCover.fam 1 (LocalCover.blockSite k z))) ∪
      Finset.univ.biUnion fun s : CTorus d L N₁' m₁ (k + 1) × Fin N =>
        polyDom (GB) (LocalCover.nbhdF 1 s.1) 1 k (LocalCover.fam 1 s.1))
    (hIT : ∀ (Y : Set (CTorus d L N₁ m₁ (k + 1))) (x w : FA) (σ : ℂ)
        (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N),
      I.T Y x w σ (Θ, 0) = -(((SA).β : ℝ) : ℂ) * ∑ z : TA,
        if Y ∈ polyDom (GA) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) 1 νS hGA cc (F₂ z) (Sol₂ z)
            (blockEnergyFun (GA) (HA) (compWeight L 1) νS k z) ∅ 1 0 Y) w.1) taylorWeight x.1 σ Θ
        else 0)
    (hIT' : ∀ (Y : Set (CTorus d L N₁' m₁ (k + 1))) (x w : FB) (σ : ℂ)
        (Θ : RawData d L (N₁' * L ^ m₁) (k + 1) N),
      I'.T Y x w σ (Θ, 0) = -(((SB).β : ℝ) : ℂ) * ∑ z : TB,
        if Y ∈ polyDom (GB) (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) then
          rayTerm (dl3 (evDec (LocalCover.nbhdF 1 (LocalCover.blockSite k z)) 1 k
            (LocalCover.fam 1 (LocalCover.blockSite k z)) 1 νS hGB cc (F₂' z) (Sol₂' z)
            (blockEnergyFun (GB) (HB) (compWeight L 1) νS k z) ∅ 1 0 Y) w.1) taylorWeight x.1 σ Θ
        else 0)
    (T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1) Set.univ))
    (hT : ∀ b ∈ T, ∀ x ∈ box b.1 (cellSide L 1 m₁ (k + 1)),
      InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    gsumCoeff ((SB).blockSplit 1 hp').μ
        (commonLabels (thickLabels I'.𝒴 I'.dom) hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom')
        (commonAct (zeroSourceAct (labelActFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' hF' hN'
            hρI (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
          hN' hL2 (fun _ => Set.univ) (e1DomG (SB)) hdom'
          (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ')
        (fun i' => commonAnchor {Y // Y ∈ I'.𝒴} (fun _ => Set.univ) (e1DomG (SB)) (bc z) i')
        (fun i' u Φ' => e1MarkGParamG (SB) F₁' Sol' ρ hp' (bc z) eps θ' i' u Φ') (T.image (σc)) =
      gsumCoeff ((SA).blockSplit 1 hp).μ
        (commonLabels (thickLabels I.𝒴 I.dom) hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom)
        (commonAct (zeroSourceAct (labelActFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I hF hN
            hρI (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
          hN hL2 (fun _ => Set.univ) (e1DomG (SA)) hdom
          (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0 θ)
        (fun i => commonAnchor {Y // Y ∈ I.𝒴} (fun _ => Set.univ) (e1DomG (SA)) z i)
        (fun i u Φ => e1MarkGParamG (SA) F₁ Sol ρ hp z eps θ i u Φ) T := by
  classical
  obtain ⟨⟨hn1, hnS, hnF, -, -⟩, ⟨hn1', hnS', hnF', -, -⟩⟩ :=
    twoTorus_margins_of_lt_min (R := R) (k := k) (m₀ := 1) (m₁ := m₁) hm₁ (lt_min hn hn')
  have hcs : cellSide L 1 m₁ (k + 1) ≤ L * cellSide L 1 m₁ (k + 1) := cellSide_le_mul
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hm : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ (k + 1) := by omega
  -- the labels with blocks in `T` lie in the box
  have hyR : ∀ y : {Y // Y ∈ I.𝒴}, blocksOf 1 (k + 1) Set.univ y.1 ⊆ T →
      ∀ x ∈ y.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro y hy x hx
    have hDj := I.dom y.1 y.2
    have hs := sitesOf_blocksOf hN (le_refl (k + 1)) isPiUnion_univ_aux hDj.2.1
    have hx' : x ∈ sitesOf (blocksOf 1 (k + 1) Set.univ y.1) := by rw [hs]; exact ⟨hx, trivial⟩
    obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx'
    exact hT b (hy hb) x hxb
  -- the domains of the box correspond
  have hmem𝒴 : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      (∀ x ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) → (bm '' Y ∈ I'.𝒴 ↔ Y ∈ I.𝒴) := by
    intro Y hY
    rw [hI𝒴, hI𝒴', Finset.mem_union, Finset.mem_union,
      mem_vDomains_boxMap_iff (ϱ := ϱ) hN hN' hnF hnF' hY,
      mem_fDomains_boxMap_iff (ϱ := ϱ) hN hN' hnF hnF' hY]
  refine gsumCoeff_e1_twoTorus_of_domainLabels hN2 hk νS β p₁ δ hC hC' hGA hGB hMX hmar hαK hsm
    hF₁ hF₁' hSol hSol' hN hN' hm₁ z hz hrc hroot hn hn' θ θ' hθ hθ' hraw hρ hp hp' hum hGdep
    hL2 hdom hdom' (thickLabels I.𝒴 I.dom) (thickLabels I'.𝒴 I'.dom)
    (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0
    (mul_nonneg (by norm_num) (mul_nonneg (by linarith) hεU)) hκ0
    (zeroSourceAct (labelActFamilyOn (SA) 1 (physInclScaled N (SA) cJ) I hF hN
      hρI (by linarith) hεU (by linarith) hKc) 2 (by norm_num))
    (zeroSourceAct (labelActFamilyOn (SB) 1 (physInclScaled N (SB) cJ') I' hF' hN'
      hρI (by linarith) hεU (by linarith) hKc) 2 (by norm_num)) T hT
    (fun y hy => ⟨bm '' y.1, (hmem𝒴 y.1 (hyR y hy)).2 y.2⟩) ?_ ?_ ?_ ?_
  · intro y hy
    exact blocksOf_image_boxMap hN hN' (by omega) (by omega) (hyR y hy)
  · intro y₁ hy₁ y₂ hy₂ h
    exact Subtype.ext (image_boxMap_inj (N₁' := N₁') hm' (hyR y₁ hy₁) (hyR y₂ hy₂)
      (congrArg Subtype.val h))
  · intro y' hy'
    change blocksOf 1 (k + 1) Set.univ y'.1 ⊆ T.image (σc) at hy'
    have hT' : ∀ x ∈ sitesOf T, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
      intro x hx
      obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx
      exact hT b hb x hxb
    have hsT := sitesOf_image_cubeMap hN hN' (le_refl (k + 1)) (r := R) (by omega) T hT'
    have hDj' := I'.dom y'.1 y'.2
    have hs' := sitesOf_blocksOf hN' (le_refl (k + 1)) isPiUnion_univ_aux hDj'.2.1
    have hy'R : ∀ x' ∈ y'.1, InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) x' := by
      intro x' hx'
      have h1 : x' ∈ sitesOf (blocksOf 1 (k + 1) Set.univ y'.1) := by
        rw [hs']; exact ⟨hx', trivial⟩
      obtain ⟨b', hb', hxb'⟩ := mem_sitesOf.1 h1
      have h2 : x' ∈ sitesOf (T.image (σc)) := mem_sitesOf.2 ⟨b', hy' hb', hxb'⟩
      rw [hsT] at h2
      obtain ⟨w, hw, rfl⟩ := h2
      exact inBox_boxMap hm' (hT' w hw)
    have hYR : ∀ x ∈ bm' '' y'.1, InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
      rintro _ ⟨x', hx', rfl⟩
      exact inBox_boxMap hm (hy'R x' hx')
    have hYimg : bm '' (bm' '' y'.1) = y'.1 :=
      image_image_boxMap (n' := (N₁ * L ^ m₁) * L ^ (k + 1)) hm hy'R
    have hYmem : bm' '' y'.1 ∈ I.𝒴 := (hmem𝒴 _ hYR).1 (by rw [hYimg]; exact y'.2)
    have hYT : blocksOf 1 (k + 1) Set.univ (bm' '' y'.1) ⊆ T := by
      intro b hb
      have hbimg : σc b ∈ blocksOf 1 (k + 1) Set.univ (bm '' (bm' '' y'.1)) := by
        rw [blocksOf_image_boxMap hN hN' (by omega) (by omega) hYR]
        exact Finset.mem_image_of_mem _ hb
      rw [hYimg] at hbimg
      obtain ⟨b₂, hb₂, he⟩ := Finset.mem_image.1 (hy' hbimg)
      have hb₂R := hT b₂ hb₂ b₂.1 (mem_box_self _ (cellSide_pos 1 m₁ (k + 1)))
      have hbR := hYR b.1 ((mem_blocksOf.1 hb) (mem_box_self _ (cellSide_pos 1 m₁ (k + 1))))
      have h1 := congrArg Subtype.val he
      rw [cubeMap_val, cubeMap_val] at h1
      have h2 : b₂ = b := Subtype.ext (boxMap_inj (hm' := hm') hb₂R hbR h1)
      exact h2 ▸ hb₂
    exact ⟨⟨_, hYmem⟩, hYT, Subtype.ext hYimg⟩
  · intro s hs y hy Φ Φ' hR
    have hs1 : ‖(s : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
    have hsR : ‖(s : ℂ)‖ < Rσ := lt_of_le_of_lt hs1 hRσ
    rw [zeroSourceAct_H, zeroSourceAct_H]
    congr 1
    rw [labelActFamilyOn_H (SB) 1 _ hF' hN' hρI _ hεU _ hKc hV' hsR,
      labelActFamilyOn_H (SA) 1 _ hF hN hρI _ hεU _ hKc hV hsR]
    have hJ : physInclScaled N (SA) cJ ((θ.1, 0) : physParam N (SA)) =
        ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), 0) := by
      rw [physInclScaled_apply]
      refine Prod.ext rfl ?_
      funext x i
      simp
    have hJ' : physInclScaled N (SB) cJ' ((θ'.1, 0) : physParam N (SB)) =
        ((θ'.1 : RawData d L (N₁' * L ^ m₁) (k + 1) N), 0) := by
      rw [physInclScaled_apply]
      refine Prod.ext rfl ?_
      funext x i
      simp
    rw [hJ, hJ', hIT, hIT']
    congr 1
    obtain ⟨D, hD, hDe⟩ := hθ
    obtain ⟨D', hD', hDe'⟩ := hθ'
    rw [hDe, hDe'] at hraw ⊢
    have hhat := hatOf_boxMap hGA hGB hN2 hk νS β p₁ δ 1 ρI hp hp' Φ Φ' hR
    exact vpartTerm_twoTorus hC hC' hk hGA hGB cc hcψ hMX hmar hαK hsm hF₂ hF₂' hSol₂ hSol₂' le_rfl
      hN hN' (hyR y hy) hn1 hn1' hnS hnS' hnF hnF' hD hD' hraw
      (fun p => (SA).hatOf_mem 1 hρI hp Φ p) (fun p => (SA).hatOf_mem 1 hρI hp Φ p)
      (fun p => (SB).hatOf_mem 1 hρI hp' Φ' p) (fun p => (SB).hatOf_mem 1 hρI hp' Φ' p) hρc
      hhat hhat hrad taylorWeight hs1

end E1Coef

end Balaban.Polymer.TwoTorusStep
