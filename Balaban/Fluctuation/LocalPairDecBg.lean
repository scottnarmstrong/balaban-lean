/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairDecFixed

/-!
# CrossI4b: the decoupled background fields of two pairs on one torus

The decoupled background field `(φ_k(s), α_k(s))` of Theorem I-4b (`Dec2.IsDecBg`) is the solution
of the decoupled perturbed system in mode U with `α₀ = 0`, the approximate field
`φ₀ = approxField H D` and the residual `f₀` of `φ₀`.  For two pairs `(C, H)`, `(C', H')` on one
torus, the approximate fields agree at a site of `Ω₁` where the layers of `H` and `H'` agree at the
site and at the bases of the blocks active there, and the data agree on `approxDep`; the residuals
agree at a site whose rows lie in `Ω₁` with the same layers.  With the component comparison of
`LocalPairDecFixed.lean` the decoupled background fields of the two pairs agree: the multipliers on
the block set `T`, the fields on `Y ⊇ T`.

* `mem_blockIdx_cross`, `active_cross`, `denom_cross`, `interp_cross`, `locSol_cross`,
  `approxField_cross`: the approximate field;
* `residual_cross`: the residual;
* `Dec2.decBg_component_cross`: two decoupled background fields;
* `Dec2.decBg_value_cross`: the values of maps with the defining property of the pair (the form of
  the hypothesis `hF₁` of the fluctuation core).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix Balaban.Polymer.TwoTorusStep

section Cross

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}

/-- A block index belongs to both index sets when the layers agree at its base. -/
theorem mem_blockIdx_cross {q : ℕ × CTorus d L N₁ m₁ K}
    (h : 1 ≤ q.1 → q.1 ≤ K → (q.2 ∈ H.layer q.1 ↔ q.2 ∈ H'.layer q.1)) :
    q ∈ blockIdx H ↔ q ∈ blockIdx H' := by
  rw [mem_blockIdx, mem_blockIdx]
  constructor
  · rintro ⟨⟨h1, h2⟩, hl, hb⟩; exact ⟨⟨h1, h2⟩, (h h1 h2).1 hl, hb⟩
  · rintro ⟨⟨h1, h2⟩, hl, hb⟩; exact ⟨⟨h1, h2⟩, (h h1 h2).2 hl, hb⟩

/-- The blocks active at `x` are the same when the layers agree at the bases of all the blocks
whose bump does not vanish at `x`. -/
theorem active_cross {x : CTorus d L N₁ m₁ K}
    (hact : ∀ q : ℕ × CTorus d L N₁ m₁ K, 1 ≤ q.1 → q.1 ≤ K → bump q.1 q.2 x ≠ 0 →
      (q.2 ∈ H.layer q.1 ↔ q.2 ∈ H'.layer q.1)) :
    active H' x = active H x := by
  ext q
  rw [mem_active, mem_active]
  constructor
  · rintro ⟨hq, hb⟩
    exact ⟨(mem_blockIdx_cross fun h1 h2 => hact q h1 h2 hb).2 hq, hb⟩
  · rintro ⟨hq, hb⟩
    exact ⟨(mem_blockIdx_cross fun h1 h2 => hact q h1 h2 hb).1 hq, hb⟩

theorem denom_cross {x : CTorus d L N₁ m₁ K}
    (hact : ∀ q : ℕ × CTorus d L N₁ m₁ K, 1 ≤ q.1 → q.1 ≤ K → bump q.1 q.2 x ≠ 0 →
      (q.2 ∈ H.layer q.1 ↔ q.2 ∈ H'.layer q.1)) :
    denom H' x = denom H x := by
  rw [denom_eq_sum_active, denom_eq_sum_active, active_cross hact]

/-- **The interpolation** agrees at `x` when the active blocks are the same and the vectors agree at
their bases. -/
theorem interp_cross {Φ Φ' : CTorus d L N₁ m₁ K → Fin N → ℂ} {x : CTorus d L N₁ m₁ K}
    (hact : ∀ q : ℕ × CTorus d L N₁ m₁ K, 1 ≤ q.1 → q.1 ≤ K → bump q.1 q.2 x ≠ 0 →
      (q.2 ∈ H.layer q.1 ↔ q.2 ∈ H'.layer q.1))
    (hΦ : ∀ q ∈ active H x, Φ' q.2 = Φ q.2) :
    interp H' Φ' x = interp H Φ x := by
  rw [interp_eq_sum_active, interp_eq_sum_active, active_cross hact, denom_cross hact]
  exact Finset.sum_congr rfl fun q hq => by rw [hΦ q hq]

/-- **The local solution** agrees at a site whose layers agree, for data agreeing there. -/
theorem locSol_cross (a : ℕ → ℝ) (ν : ℝ) {Ψ Ψ' h h' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {y : CTorus d L N₁ m₁ K} (hly : ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hΨ : Ψ y = Ψ' y) (hh : h y = h' y) :
    locSol H' a ν Ψ' h' y = locSol H a ν Ψ h y := by
  classical
  unfold locSol blockMass
  by_cases hy : y ∈ H.Ω 1
  · have hy' : y ∈ H'.Ω 1 := (mem_Ω_one_cross hly).1 hy
    simp only [hy, hy', ↓reduceIte, layerIndex_cross hy hly, hΨ, hh]
  · have hy' : y ∉ H'.Ω 1 := fun h => hy ((mem_Ω_one_cross hly).2 h)
    simp only [hy, hy', ↓reduceIte, hΨ]

/-- **The approximate field `φ₀`** of two generating sets agrees at a site of `Ω₁(H)` where the
layers agree at the site and at the bases of the blocks whose bump does not vanish there, for data
agreeing on `approxDep`. -/
theorem approxField_cross (a : ℕ → ℝ) (ν : ℝ) {Ψ Ψ' h h' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1)
    (hlx : ∀ n, 1 ≤ n → n ≤ K → (x ∈ H.layer n ↔ x ∈ H'.layer n))
    (hact : ∀ q : ℕ × CTorus d L N₁ m₁ K, 1 ≤ q.1 → q.1 ≤ K → bump q.1 q.2 x ≠ 0 →
      ∀ n, 1 ≤ n → n ≤ K → (q.2 ∈ H.layer n ↔ q.2 ∈ H'.layer n))
    (hdat : ∀ y ∈ approxDep H x, Ψ y = Ψ' y ∧ h y = h' y) :
    approxField H' a ν Ψ' h' x = approxField H a ν Ψ h x := by
  classical
  have hx' : x ∈ H'.Ω 1 := (mem_Ω_one_cross hlx).1 hx
  unfold approxField
  simp only [hx, hx', ↓reduceIte, layerIndex_cross hx hlx]
  split_ifs
  · exact locSol_cross a ν hlx (hdat x (mem_approxDep_self x)).1 (hdat x (mem_approxDep_self x)).2
  · congr 1
    refine interp_cross (fun q h1 h2 hb => hact q h1 h2 hb q.1 h1 h2) fun q hq => ?_
    obtain ⟨hqI, hb⟩ := (mem_active H).1 hq
    obtain ⟨⟨h1, h2⟩, -, -⟩ := (mem_blockIdx H).1 hqI
    have hqd : q.2 ∈ approxDep H x := by
      unfold approxDep
      exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨q, hq, rfl⟩)
    exact locSol_cross a ν (hact q h1 h2 hb) (hdat _ hqd).1 (hdat _ hqd).2

/-- **The residual** `f₀ = S(Ψ, h̃) - H_D(0) φ` of two generating sets agrees at a site of both
`Ω₁` whose row sites lie in `Ω₁(H)` with the same layers, for fields agreeing on the row sites and
data agreeing at the site. -/
theorem residual_cross (a : ℕ → ℝ) (ν : ℝ) {D : BgData H N} {D' : BgData H' N}
    {φ φ' : CTorus d L N₁ m₁ K → Fin N → ℂ} {x : CTorus d L N₁ m₁ K} (hx : x ∈ H.Ω 1)
    (hx' : x ∈ H'.Ω 1)
    (hres : ∀ y ∈ resSites H x, y ∈ H.Ω 1 ∧
      ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hφ : ∀ y ∈ resSites H x, φ y = φ' y) (hΨ : D.Ψ x = D'.Ψ x) (hh : D.h x = D'.h x)
    (i : Fin N) :
    residual H' a ν D' φ' (⟨x, hx'⟩, i) = residual H a ν D φ (⟨x, hx⟩, i) := by
  classical
  have hlx := (hres x (mem_resSites_self x)).2
  have hnc : ∀ z ∈ resSites H x, z ∉ collar H ∧ z ∉ collar H' := by
    intro z hz
    obtain ⟨hzΩ, hzl⟩ := hres z hz
    exact ⟨fun h => ((mem_collar H).1 h).1 hzΩ,
      fun h => ((mem_collar H').1 h).1 ((mem_Ω_one_cross hzl).1 hzΩ)⟩
  have hp : ∀ μ : Fin d, x + Pi.single μ 1 ∈ resSites H x := add_single_mem_resSites H x
  have hm : ∀ μ : Fin d, x - Pi.single μ 1 ∈ resSites H x := sub_single_mem_resSites H x
  rw [residual_apply, residual_apply]
  simp only
  rw [layerIndex_cross hx hlx, hΨ, hh, hφ x (mem_resSites_self x)]
  have hblk : ∑ y ∈ H'.blk (H.layerIndex x) x, φ' y i = ∑ y ∈ H.blk (H.layerIndex x) x, φ y i :=
    Finset.sum_congr rfl fun y hy => by
      rw [hφ y (mem_resSites_of_mem_blk H hy)]
  rw [hblk]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hφ _ (hp μ), hφ _ (hm μ)]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [(hnc _ (hp μ)).1, (hnc _ (hp μ)).2, (hnc _ (hm μ)).1, (hnc _ (hm μ)).2,
      ↓reduceIte]

end Cross

namespace Dec2

section Pair

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {C C' : DecCover d L N₁ m₁ K}
variable {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
variable {a : ℕ → ℝ} {ν Kc Cx : ℝ}

/-- **CrossI4b, component comparison.**  Let `(φ, α)` and `(φ', α')` be decoupled background
fields (`Dec2.IsDecBg` in the ball `ρ₄`) of data `D`, `D'` in the domains of Theorem I-4b for two
pairs `(C, H)`, `(C', H')` with `Dec2.CoverBase` and `BgHyp`, at parameters `|s_P|, |s'_P| ≤ e^κ`.
Let `T ⊆ Y` be sets of sites with: the layers of `H` and `H'` agree on `Y`; the dichotomy, row and
inner-cube hypotheses of `decFixed_rows_cross` for `T`, `Y`; the row sites of the sites of `T` lie
in `Ω₁(H)` and in `Y`; at the sites of `Y` the layers agree at the bases of the blocks whose bump
does not vanish, and the raw data agree on `approxDep`.  Then the multipliers agree on `T` and the
fields agree on `Y`. -/
theorem decBg_component_cross {c BG : ℝ} (hS : DecSpecs d L Kc Cx c BG)
    (S : CoverBase C H a ν Kc Cx) (S' : CoverBase C' H' a ν Kc Cx)
    (HB : BgHyp d L K ϱ a ν) (HB' : BgHyp d L K ϱ' a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : DecParams C} {s' : DecParams C'} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {δ ε δ' ε' : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hδ0' : 0 < δ') (hδε' : δ' ≤ ε')
    (hε' : ε' ≤ bgC0 d L N) (hδ' : δ' ≤ c7 d L N BG κ)
    (hνε' : ν * ((L : ℝ) ^ K) ^ 2 * ε' ^ 2 ≤ δ' ^ 2)
    {D : BgData H N} {D' : BgData H' N} (hDd : InDomainC H ν δ ε D)
    (hDd' : InDomainC H' ν δ' ε' D')
    {Y T : Finset (CTorus d L N₁ m₁ K)} (hTY : T ⊆ Y)
    (hYlay : ∀ y ∈ Y, ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd (extS C s) q ≠ 0 →
      SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd (extS C' s') q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hrow : ∀ q ∈ C.cubeIdx, C.sProd (extS C s) q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ C'.cubeIdx, C'.sProd (extS C' s') q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd (extS C s) q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd (extS C' s') q = C.sProd (extS C s) q ∧
      (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
        (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x ∈ intBox q, C.chi q x = C'.chi q x))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd (extS C' s') q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd (extS C s) q ≠ 0)
    (hres : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x, y ∈ H.Ω 1 ∧ y ∈ Y)
    (hact : ∀ y ∈ Y, y ∈ H.Ω 1 → ∀ q : ℕ × CTorus d L N₁ m₁ K, 1 ≤ q.1 → q.1 ≤ K →
      bump q.1 q.2 y ≠ 0 → ∀ n, 1 ≤ n → n ≤ K → (q.2 ∈ H.layer n ↔ q.2 ∈ H'.layer n))
    (hdat : ∀ y ∈ Y, y ∈ H.Ω 1 → ∀ z ∈ approxDep H y, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)
    {φ : H.Ω 1 × Fin N → ℂ} {α : H.Ω 1 → ℂ} {φ' : H'.Ω 1 × Fin N → ℂ} {α' : H'.Ω 1 → ℂ}
    (h : IsDecBg C H a ν (rho4 d L N BG κ) s D φ α)
    (h' : IsDecBg C' H' a ν (rho4 d L N BG κ) s' D' φ' α') :
    (∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      α' ⟨x, hx'⟩ = α ⟨x, hx⟩) ∧
    (∀ (y : CTorus d L N₁ m₁ K) (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1), y ∈ Y → ∀ i : Fin N,
      φ' (⟨y, hy'⟩, i) = φ (⟨y, hy⟩, i)) := by
  classical
  have hd0 : 0 < d := by have := HB.hd; omega
  have hBG := hS.fam.2.1
  obtain ⟨W⟩ := DataWit.exists hDd
  obtain ⟨W'⟩ := DataWit.exists hDd'
  have Hd := decHyp_of_data (N := N) HB hBG hδ0 hδε hε hδ hνε W
  have Hd' := decHyp_of_data (N := N) HB' hBG hδ0' hδε' hε' hδ' hνε' W'
  set Bc : ℝ := famConst d L BG κ with hBc
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hle : ∀ {δ₂ : ℝ}, 0 < δ₂ → δ₂ ≤ c7 d L N BG κ →
      lemma53Const d L * δ₂ ≤ deltaStar' d L N Bc Γ := by
    intro δ₂ h0 h1
    obtain ⟨-, h2, -⟩ := c7_facts (L := L) (N := N) hd0 hBG h0.le h1
    have hdc := deltaClose_le_deltaStar' (d := d) (L := L) (N := N) (BG := BG) (κ := κ)
    have hdcp := deltaClose_pos (d := d) (L := L) (N := N) (κ := κ) hd0 hBG
    linarith
  have hYΩ : ∀ x ∈ Y, (x ∈ H.Ω 1 ↔ x ∈ H'.Ω 1) := fun x hx => mem_Ω_one_cross (hYlay x hx)
  -- the approximate fields agree on `Y ∩ Ω₁`
  have hφ0Y : ∀ y ∈ Y, y ∈ H.Ω 1 →
      approxField H a ν D.Ψ D.h y = approxField H' a ν D'.Ψ D'.h y := fun y hy hyΩ =>
    (approxField_cross a ν hyΩ (hYlay y hy) (hact y hy hyΩ) (hdat y hy hyΩ)).symm
  have hres' : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x,
      (∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧ (y ∈ H.Ω 1 → y ∈ Y) :=
    fun x hx hxΩ y hy => ⟨hYlay y (hres x hx hxΩ y hy).2, fun _ => (hres x hx hxΩ y hy).2⟩
  have hφ0 : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x,
      approxField H a ν D.Ψ D.h y = approxField H' a ν D'.Ψ D'.h y := fun x hx hxΩ y hy =>
    hφ0Y y (hres x hx hxΩ y hy).2 (hres x hx hxΩ y hy).1
  -- the residuals agree on `T`
  have hf : ∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      ∀ i, residual H a ν D (approxField H a ν D.Ψ D.h) (⟨x, hx⟩, i) =
        residual H' a ν D' (approxField H' a ν D'.Ψ D'.h) (⟨x, hx'⟩, i) := by
    intro x hx hx' hxT i
    have hdx := hdat x (hTY hxT) hx x (mem_approxDep_self x)
    exact (residual_cross a ν hx hx'
      (fun y hy => ⟨(hres x hxT hx y hy).1, hYlay y (hres x hxT hx y hy).2⟩)
      (hφ0 x hxT hx) hdx.1 hdx.2 i).symm
  have hfix : DecFixed C H a ν s true 0 (approxField H a ν D.Ψ D.h)
      (pertSource H a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual H a ν D (approxField H a ν D.Ψ D.h))) α := by
    rw [pertSource_zeroΨ]; exact h.fixed
  have hfix' : DecFixed C' H' a ν s' true 0 (approxField H' a ν D'.Ψ D'.h)
      (pertSource H' a (0 : CTorus d L N₁ m₁ K → Fin N → ℂ)
        (residual H' a ν D' (approxField H' a ν D'.Ψ D'.h))) α' := by
    rw [pertSource_zeroΨ]; exact h'.fixed
  obtain ⟨hα, hcorr⟩ := decFixed_component_cross hS.fam S S' hκ hM hs hs' hTY hYΩ hdich hdich'
    hrow hrow' hin hin' hres' true Hd Hd' (hle hδ0 hδ) (hle hδ0 hδ) (hle hδ0' hδ') (hle hδ0' hδ')
    (fun _ _ _ _ => rfl) hφ0 (fun _ _ _ _ _ => rfl) hf hfix h.small hfix' h'.small
  refine ⟨hα, fun y hy hy' hyY i => ?_⟩
  have e := hcorr y hy hy' hyY i
  rw [pertSource_zeroΨ, pertSource_zeroΨ] at e
  rw [h.field, h'.field]
  simp only
  rw [e, hφ0Y y hyY hy]

/-- **CrossI4b, values.**  Let `F₁`, `F₁'` be maps with the defining property of the two pairs (the
hypothesis `hF₁` of the fluctuation core): on parameters with `|s_P| < e^κ` and data in the union
domain of Theorem I-4b, `F₁ (s, rawOf D)` is every decoupled background field of `(s, D)`.  Under
the hypotheses of `decBg_component_cross` on the geometry and the data, for data `D`, `D'` in the
union domains, the multipliers agree on `T` and the fields agree on `Y`.  The solutions exist by
`Dec2.i4b_exists_unique` for each pair. -/
theorem decBg_value_cross {c BG : ℝ} (hS : DecSpecs d L Kc Cx c BG)
    (S : CoverBase C H a ν Kc Cx) (S' : CoverBase C' H' a ν Kc Cx)
    (HB : BgHyp d L K ϱ a ν) (HB' : BgHyp d L K ϱ' a ν) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : DecParams C × RawData d L (N₁ * L ^ m₁) K N → (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ)}
    {F₁' : DecParams C' × RawData d L (N₁ * L ^ m₁) K N → (H'.Ω 1 × Fin N → ℂ) × (H'.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams C) (D : BgData H N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC H (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : H.Ω 1 × Fin N → ℂ)
        (α : H.Ω 1 → ℂ), IsDecBg C H a ν (rho4 d L N BG κ) s D φ α → F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : DecParams C') (D : BgData H' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC H' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : H'.Ω 1 × Fin N → ℂ)
        (α : H'.Ω 1 → ℂ), IsDecBg C' H' a ν (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {s : DecParams C} {s' : DecParams C'} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hs' : ∀ P, ‖s' P‖ < Real.exp κ)
    {D : BgData H N} {D' : BgData H' N}
    (hDd : InUnionDomainC H (bgC0 d L N) (c7 d L N BG κ) ν D)
    (hDd' : InUnionDomainC H' (bgC0 d L N) (c7 d L N BG κ) ν D')
    {Y T : Finset (CTorus d L N₁ m₁ K)} (hTY : T ⊆ Y)
    (hYlay : ∀ y ∈ Y, ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n))
    (hdich : ∀ q ∈ C.cubeIdx, C.sProd (extS C s) q ≠ 0 →
      SubI H (intBox q) T ∨ DisjI H (intBox q) T)
    (hdich' : ∀ q ∈ C'.cubeIdx, C'.sProd (extS C' s') q ≠ 0 →
      SubI H' (intBox q) T ∨ DisjI H' (intBox q) T)
    (hrow : ∀ q ∈ C.cubeIdx, C.sProd (extS C s) q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hrow' : ∀ q ∈ C'.cubeIdx, C'.sProd (extS C' s') q ≠ 0 → ∀ x ∈ Y, x ∈ intBox q → x ∈ T)
    (hin : ∀ q ∈ innerCentres C H T, C.sProd (extS C s) q ≠ 0 →
      q ∈ innerCentres C' H' T ∧ C'.sProd (extS C' s') q = C.sProd (extS C s) q ∧
      (∀ x ∈ intBox q, ∀ y : CTorus d L N₁ m₁ K,
        (y = x ∨ ∃ μ : Fin d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) →
          ∀ n, 1 ≤ n → n ≤ K → (y ∈ H.layer n ↔ y ∈ H'.layer n)) ∧
      (∀ x ∈ intBox q, C.chi q x = C'.chi q x))
    (hin' : ∀ q ∈ innerCentres C' H' T, C'.sProd (extS C' s') q ≠ 0 →
      q ∈ innerCentres C H T ∧ C.sProd (extS C s) q ≠ 0)
    (hres : ∀ x ∈ T, x ∈ H.Ω 1 → ∀ y ∈ resSites H x, y ∈ H.Ω 1 ∧ y ∈ Y)
    (hact : ∀ y ∈ Y, y ∈ H.Ω 1 → ∀ q : ℕ × CTorus d L N₁ m₁ K, 1 ≤ q.1 → q.1 ≤ K →
      bump q.1 q.2 y ≠ 0 → ∀ n, 1 ≤ n → n ≤ K → (q.2 ∈ H.layer n ↔ q.2 ∈ H'.layer n))
    (hdat : ∀ y ∈ Y, y ∈ H.Ω 1 → ∀ z ∈ approxDep H y, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z) :
    (∀ (x : CTorus d L N₁ m₁ K) (hx : x ∈ H.Ω 1) (hx' : x ∈ H'.Ω 1), x ∈ T →
      (F₁' (s', rawOf D')).2 ⟨x, hx'⟩ = (F₁ (s, rawOf D)).2 ⟨x, hx⟩) ∧
    (∀ (y : CTorus d L N₁ m₁ K) (hy : y ∈ H.Ω 1) (hy' : y ∈ H'.Ω 1), y ∈ Y → ∀ i : Fin N,
      (F₁' (s', rawOf D')).1 (⟨y, hy'⟩, i) = (F₁ (s, rawOf D)).1 (⟨y, hy⟩, i)) := by
  obtain ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hDC⟩ := id hDd
  obtain ⟨δ', ε', hδ0', hδε', hε', hδ', hνε', hDC'⟩ := id hDd'
  obtain ⟨φ, α, hsol, -⟩ := i4b_exists_unique hS S HB hκ hM (fun P => (hs P).le) hδ0 hδε hε hδ
    hνε hDC
  obtain ⟨φ', α', hsol', -⟩ := i4b_exists_unique hS S' HB' hκ hM (fun P => (hs' P).le) hδ0' hδε'
    hε' hδ' hνε' hDC'
  rw [hF₁ s D hs hDd φ α hsol, hF₁' s' D' hs' hDd' φ' α' hsol']
  exact decBg_component_cross hS S S' HB HB' hκ hM (fun P => (hs P).le) (fun P => (hs' P).le)
    hδ0 hδε hε hδ hνε hδ0' hδε' hε' hδ' hνε' hDC hDC' hTY hYlay hdich hdich' hrow hrow' hin hin'
    hres hact hdat hsol hsol'

end Pair

end Dec2

end Balaban.Localization
