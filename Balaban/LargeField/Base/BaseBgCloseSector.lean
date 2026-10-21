/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseBgCloseCube
public import Balaban.LargeField.Base.BaseBackgroundIdent2
public import Balaban.LargeField.Base.BaseCutoffSmall

/-!
# From the cube test to the margins of the sector background: transport along `1 * n = M₁ N₁`

The sector lives on the torus of side `1 * n`; the cube generating sets of the characteristic
function `χ₁` live on `M₁ N₁`. This file carries the single-scale background across an equality of
base sides (`bgFieldC_single_cast`, `liftSingle_single_cast`) so that `cube_margins` applies to the
sector.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField

set_option linter.unusedSectionVars false

variable {d L N : ℕ} [NeZero L]

/-- The site of the torus of side `N₀' L` corresponding to a site of side `N₀ L` along `N₀ = N₀'`. -/
def castSite {a b : ℕ} (e : a = b) (x : Torus d (a * L ^ 1)) : Torus d (b * L ^ 1) :=
  (congrArg (fun m => Torus d (m * L ^ 1)) e) ▸ x

theorem castSite_rfl {a : ℕ} (x : Torus d (a * L ^ 1)) : castSite rfl x = x := rfl

/-- **The background of `single` is transported along an equality of base sides.** -/
theorem bgFieldC_single_cast {a b : ℕ} [NeZero a] [NeZero b] (e : a = b) (ϱ : ℝ) (w : ℕ → ℝ)
    (ν c₀ : ℝ)
    (D : BgData (GeneratingSet.single (d := d) (L := L) (N₀ := a) (k := 1) ϱ) N)
    (x : Torus d (a * L ^ 1)) (hx : x ∈ (GeneratingSet.single (d := d) (L := L) (N₀ := a)
      (k := 1) ϱ).Ω 1) (hx' : castSite e x ∈ (GeneratingSet.single (d := d) (L := L) (N₀ := b)
      (k := 1) ϱ).Ω 1) (i : Fin N) :
    bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := b) (k := 1) ϱ) w ν c₀
        (cast (bgData_single_eq e ϱ) D) (⟨castSite e x, hx'⟩, i) =
      bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := a) (k := 1) ϱ) w ν c₀ D
        (⟨x, hx⟩, i) := by
  subst e
  rfl

/-- The block of the coarse torus of side `b L^0` corresponding to one of side `a L^0`. -/
def castCoarse {a b : ℕ} (e : a = b) (y : Torus d (b * L ^ (1 - 1))) : Torus d (a * L ^ (1 - 1)) :=
  (congrArg (fun m => Torus d (m * L ^ (1 - 1))) e.symm) ▸ y

/-- **The lifted datum of `single` is transported along an equality of base sides.** -/
theorem liftSingle_single_cast {a b : ℕ} [NeZero a] [NeZero b] (e : a = b) (ϱ : ℝ)
    (ψ : Torus d (a * L ^ (1 - 1)) → Fin N → ℂ) (h : Fin N → ℂ) :
    cast (bgData_single_eq e ϱ)
        (liftSingle (GeneratingSet.single (d := d) (L := L) (N₀ := a) (k := 1) ϱ) ψ h) =
      liftSingle (GeneratingSet.single (d := d) (L := L) (N₀ := b) (k := 1) ϱ)
        (fun y i => ψ (castCoarse e y) i) h := by
  subst e
  rfl

theorem castSite_add_single {a b : ℕ} (e : a = b) (x : Torus d (a * L ^ 1)) (μ : Fin d) :
    castSite e (x + Pi.single μ 1) = castSite e x + Pi.single μ 1 := by
  subst e
  rfl

theorem rn_re_le_vn (u : Fin N → ℂ) : rn (fun i => (u i).re) ≤ vn u := by
  unfold rn vn
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  show (u i).re ^ 2 ≤ ‖u i‖ ^ 2
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [sq_nonneg (u i).im]

open Classical in
/-- **The chart centre is the real part of the complex background** (on the passing support). -/
theorem baseSectorCenter_eq_re {n : ℕ} [NeZero n] (ϱ : ℝ) (a : ℕ → ℝ) (regimeB : Prop)
    (ν δ₀ : ℝ) (hδ : 0 < δ₀) (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ a (if regimeB then ν else 0)) (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0) (z : Torus d (1 * n * L ^ 1)) (i : Fin N) :
    baseSectorCenter ϱ a regimeB ν h θ (baseSector_side L n ▸ z) i =
      (bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ) a
        (if regimeB then ν else 0) (bgC0 d L N) (baseSectorDatum ϱ θ h)
        (⟨z, baseSector_mem_single ϱ z⟩, i)).re := by
  have hD := baseSectorDatum_domain_of_product_ne_zero ϱ a regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp
  have hC := (theorem72_real (G := GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
    H hD).1
  unfold baseSectorCenter
  simp only [hD, ↓reduceIte]
  have hz : (baseSector_side L n).symm ▸ ((baseSector_side L n) ▸ z : Torus d (L * n)) = z :=
    torus_cast_symm_cast (baseSector_side L n) z
  rw [hC]
  simp only [hz]

theorem blockMap_pow_one' {ℓ : ℕ} (m : ℕ) (x : Torus d ℓ) :
    blockMap (L ^ 1) m x = blockMap L m x := by rw [pow_one]

theorem castSite_cancel {a b : ℕ} (e : a = b) (z : Torus d (b * L ^ 1)) :
    castSite e (castSite e.symm z) = z := by
  subst e
  rfl

/-- The coarse block of the torus of side `a L^0` corresponding to one of side `b L^0`. -/
def castC {a b : ℕ} (e : a = b) (y : Torus d (a * L ^ (1 - 1))) : Torus d (b * L ^ (1 - 1)) :=
  (congrArg (fun m => Torus d (m * L ^ (1 - 1))) e) ▸ y

theorem castCoarse_castC {a b : ℕ} (e : a = b) (y : Torus d (a * L ^ (1 - 1))) :
    castCoarse (L := L) e (castC e y) = y := by
  subst e
  rfl

/-- **Sums over a block are transported along `a = b`.** -/
theorem sum_fibre_cast {a b : ℕ} [NeZero a] [NeZero b] (e : a = b)
    (y : Torus d (a * L ^ (1 - 1))) (f : Torus d (a * L ^ 1) → ℂ) :
    ∑ z ∈ Finset.univ.filter (fun z : Torus d (a * L ^ 1) =>
        blockMap L (a * L ^ (1 - 1)) z = y), f z =
      ∑ z' ∈ Finset.univ.filter (fun z' : Torus d (b * L ^ 1) =>
        blockMap L (b * L ^ (1 - 1)) z' = castC e y), f (castSite e.symm z') := by
  subst e
  rfl

open Classical in
/-- **Bond margin of the sector background from the cube tests** (first step): for the sector with
`n = M₁ N₁`, `M₁ = L^{m₁}`, `N₁ = c n'`, if the coarse field passes the cube test `χ₁` at tolerance
`δ₁` for every cube of `Torus d n'`, then every bond difference of the chart centre satisfies
`|e_{x+e_μ} - e_x| < (δ₁ + √N ε)/L`, `ε = K_w c_F (2d+2) K₁ δ' e^{-γ_w c M₁}`, `δ' = 4 d L δ₀`. -/
theorem sector_bond_margin {N : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {n M1 N₁ m₁ c n' : ℕ} [NeZero n] [NeZero M1] [NeZero N₁] [NeZero n']
        (hn : 1 * n = M1 * N₁) (_hM1 : M1 = L ^ m₁) (_hm : N₁ * L ^ (1 - 1) = c * n')
        {ϱ a₁ ν δ₀ δ₁ : ℝ} (_ha₁ : 0 < a₁) (aw : ℕ → ℝ) (_hw : aw = compWeight L a₁) (regimeB : Prop)
        (_hδ : 0 < δ₀) (h : EuclideanSpace ℝ (Fin N)) (_hh : ‖h‖ = 1)
        (_H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
        (_hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N) {BG κ : ℝ}
        (_hΛ7 : 4 * d * L * δ₀ ≤ c7 d L N BG κ)
        (_H0 : BgHyp d L 1 (minSep L M1) (compWeight L a₁) (if regimeB then ν else 0))
        (_hν0 : 0 ≤ (if regimeB then ν else 0))
        (_hνle : (if regimeB then ν else 0) * ((L : ℝ) ^ 1) ^ 2 ≤ 1)
        (_hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1))
        (_hKs : bgK1 d L N * bgC1 d L N ≤ min (deltaStar d L N) δw)
        (_hδc : 4 * d * L * δ₀ ≤ thm73C1 d L N)
        (_hε' : 4 * d * L * δ₀ ≤ bgC0 d L N)
        (_hK1' : (2 * d + 2) * (bgK1 d L N * (4 * d * L * δ₀)) ≤ deltaStar d L N)
        (_hKw' : (2 * d + 2) * (bgK1 d L N * (4 * d * L * δ₀)) ≤ δw)
        (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
        (_hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0)
        (_hχ : ∀ y0 : Torus d n', ChiKProp (compWeight L a₁) (if regimeB then ν else 0) δ₁
          (fun i => h i) c n' y0
          (show BlockCfg d (M1 * N₁) L 1 1 N from fun y i => baseSectorTheta θ (castCoarse hn y) i)),
        (∀ (x : Torus d (1 * n * L ^ 1)) (μ : Fin d),
        rn (fun i => baseSectorCenter ϱ aw regimeB ν h θ (baseSector_side L n ▸ (x + Pi.single μ 1) : Torus d (L * n)) i -
          baseSectorCenter ϱ aw regimeB ν h θ (baseSector_side L n ▸ x : Torus d (L * n)) i) <
        (δ₁ + Real.sqrt N * (Kw * (cF d L * ((2 * d + 2) * (bgK1 d L N * (4 * d * L * δ₀)))) *
          Real.exp (-(gammaW d * ((c * M1 : ℕ) : ℝ))))) / L) ∧
        (∀ y : Torus d (1 * n * L ^ (1 - 1)),
        rn (fun i => baseSectorTheta θ y i - spinAverage (baseSectorN L n) L 1 1
          (fun z i => baseSectorCenter ϱ aw regimeB ν h θ
            (baseSector_side L n ▸ z : Torus d (L * n)) i) y i) <
        δ₁ + Real.sqrt N * (Kw * (cF d L * ((2 * d + 2) * (bgK1 d L N * (4 * d * L * δ₀)))) *
          Real.exp (-(gammaW d * ((c * M1 : ℕ) : ℝ))))) := by
  obtain ⟨Kw, δw, hK, hδw, hcm⟩ := cube_margins (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro n M1 N₁ m₁ c n' _ _ _ _ hn hM1 hm ϱ a₁ ν δ₀ δ₁ ha₁ aw hw regimeB hδ h hh H hΛ1 BG κ hΛ7 H0 hν0
    hνle hsep hKs hδc hε' hK1' hKw' θ φ hp hχ
  subst hw
  have hd0 : 0 < d := by omega
  have hδ' : 0 < 4 * (d : ℝ) * L * δ₀ := by positivity
  set ψ : BlockCfg d (M1 * N₁) L 1 1 N := fun y i => baseSectorTheta θ (castCoarse hn y) i with hψ
  set G1 := GeneratingSet.single (d := d) (L := L) (N₀ := M1 * N₁) (k := 1) ϱ with hG1
  have hDR := baseSectorDatum_inDomainR_c7 ϱ (compWeight L a₁) regimeB ν δ₀ hδ h hh H BG κ hΛ7 θ φ hp
  have hDRc := inDomainR_cast hn hDR
  have hDC : InDomainC G1 (if regimeB then ν else 0) (4 * d * L * δ₀) (4 * d * L * δ₀)
      (cast (bgData_single_eq hn ϱ) (baseSectorDatum ϱ θ h)) :=
    inDomainC_of_inDomainR hδ' hDRc
  have hcast : cast (bgData_single_eq hn ϱ) (baseSectorDatum ϱ θ h) =
      liftSingle G1 ψ.toC (fun i => (h i : ℂ)) := by
    unfold baseSectorDatum
    rw [liftSingle_single_cast hn]
    rfl
  rw [hcast] at hDC
  have hνε' : (if regimeB then ν else 0) * ((L : ℝ) ^ 1) ^ 2 * (4 * d * L * δ₀) ^ 2 ≤
      (4 * d * L * δ₀) ^ 2 := by nlinarith [sq_nonneg (4 * (d : ℝ) * L * δ₀)]
  have H1 : BgHyp d L 1 ϱ (compWeight L a₁) (if regimeB then ν else 0) := H
  have hmem : ∀ z : Torus d (M1 * N₁ * L ^ 1), z ∈ G1.Ω 1 := fun z => by
    rw [hG1, single_Ω_one le_rfl]; exact Finset.mem_univ z
  have hmemD : ∀ z : Torus d (1 * n * L ^ 1), z ∈ (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1 := fun z => baseSector_mem_single ϱ z
  have e2 := fun (z : Torus d (1 * n * L ^ 1)) (i : Fin N) =>
    baseSectorCenter_eq_re (n := n) ϱ (compWeight L a₁) regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp z i
  have e1 : ∀ (z : Torus d (1 * n * L ^ 1)) (i : Fin N),
      bgFieldC G1 (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N)
        (liftSingle G1 ψ.toC (fun i => (h i : ℂ))) (⟨castSite hn z, hmem _⟩, i) =
      bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
        (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N) (baseSectorDatum ϱ θ h)
        (⟨z, hmemD z⟩, i) := fun z i => by
    rw [← hcast]
    exact bgFieldC_single_cast hn ϱ _ _ _ _ z (hmemD z) (hmem _) i
  refine ⟨fun x μ => ?_, fun y => ?_⟩
  ·   set x' := castSite hn x with hx'
      set y' := castSite hn (x + Pi.single μ 1) with hy'
      have hy'eq : y' = x' + Pi.single μ 1 := castSite_add_single hn x μ
      set y0 : Torus d n' := blockMap (L ^ 1 * (c * M1)) n' x' with hy0
      obtain ⟨hbondC, -⟩ := hcm hM1 hm (ϱ1 := ϱ) (a₁ := a₁) (ν := if regimeB then ν else 0)
        (δ' := 4 * d * L * δ₀) (ε' := 4 * d * L * δ₀) (δ₁ := δ₁) (fun i => h i) ha₁ H0 H1 hν0 hνle hsep hKs
        hδ' le_rfl hε' hδc hνε' hK1' hKw' ψ y0 hDC (hχ y0)
      have hmem : ∀ z : Torus d (M1 * N₁ * L ^ 1), z ∈ G1.Ω 1 := fun z => by
        rw [hG1, single_Ω_one le_rfl]; exact Finset.mem_univ z
      have key := hbondC x' y' μ rfl hy'eq (hmem x') (hmem y')
      have hmemD : ∀ z : Torus d (1 * n * L ^ 1), z ∈ (GeneratingSet.single (d := d) (L := L)
          (N₀ := 1 * n) (k := 1) ϱ).Ω 1 := fun z => baseSector_mem_single ϱ z
      have e1 : ∀ (z : Torus d (1 * n * L ^ 1)) (i : Fin N),
          bgFieldC G1 (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N)
            (liftSingle G1 ψ.toC (fun i => (h i : ℂ))) (⟨castSite hn z, hmem _⟩, i) =
          bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
            (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N) (baseSectorDatum ϱ θ h)
            (⟨z, hmemD z⟩, i) := fun z i => by
        rw [← hcast]
        exact bgFieldC_single_cast hn ϱ _ _ _ _ z (hmemD z) (hmem _) i
      have e2 := fun (z : Torus d (1 * n * L ^ 1)) (i : Fin N) =>
        baseSectorCenter_eq_re (n := n) ϱ (compWeight L a₁) regimeB ν δ₀ hδ h hh H hΛ1 θ φ hp z i
      have hvn : (fun i => bgFieldC G1 (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N)
            (liftSingle G1 ψ.toC (fun i => (h i : ℂ))) (⟨y', hmem y'⟩, i) -
          bgFieldC G1 (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N)
            (liftSingle G1 ψ.toC (fun i => (h i : ℂ))) (⟨x', hmem x'⟩, i)) =
          fun i => bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
            (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N) (baseSectorDatum ϱ θ h)
            (⟨x + Pi.single μ 1, hmemD _⟩, i) -
            bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
            (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N) (baseSectorDatum ϱ θ h)
            (⟨x, hmemD _⟩, i) := by
        funext i
        exact congrArg₂ (· - ·) (e1 (x + Pi.single μ 1) i) (e1 x i)
      rw [hvn] at key
      have hu : (fun i => baseSectorCenter ϱ (compWeight L a₁) regimeB ν h θ
            (baseSector_side L n ▸ (x + Pi.single μ 1) : Torus d (L * n)) i -
          baseSectorCenter ϱ (compWeight L a₁) regimeB ν h θ (baseSector_side L n ▸ x : Torus d (L * n)) i) =
          fun i => ((bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
            (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N) (baseSectorDatum ϱ θ h)
            (⟨x + Pi.single μ 1, hmemD _⟩, i) -
            bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
            (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N) (baseSectorDatum ϱ θ h)
            (⟨x, hmemD _⟩, i))).re := by
        funext i
        rw [e2, e2, Complex.sub_re]
      rw [hu]
      refine lt_of_le_of_lt (rn_re_le_vn _) ?_
      have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      rw [lt_div_iff₀ hL0, mul_comm]
      exact key
  · set y' := castC hn y with hy'
    have hm0 : M1 * N₁ * L ^ 1 = L * (M1 * N₁ * L ^ (1 - 1)) := by simp [pow_one]; ring
    obtain ⟨x', hx'⟩ : ∃ x', x' ∈ blockFibre (ℓ := M1 * N₁ * L ^ 1) L (M1 * N₁ * L ^ (1 - 1)) y' := by
      have := card_blockFibre (d := d) (ℓ := M1 * N₁ * L ^ 1) (N := L)
        (m := M1 * N₁ * L ^ (1 - 1)) hm0 y'
      exact Finset.card_pos.1 (by rw [this]; positivity)
    have hx'm : blockMap L (M1 * N₁ * L ^ (1 - 1)) x' = y' := mem_blockFibre.1 hx'
    set y0 : Torus d n' := blockMap (L ^ 1 * (c * M1)) n' x' with hy0
    obtain ⟨-, hblockC⟩ := hcm hM1 hm (ϱ1 := ϱ) (a₁ := a₁) (ν := if regimeB then ν else 0)
      (δ' := 4 * d * L * δ₀) (ε' := 4 * d * L * δ₀) (δ₁ := δ₁) (fun i => h i) ha₁ H0 H1 hν0 hνle hsep
      hKs hδ' le_rfl hε' hδc hνε' hK1' hKw' ψ y0 hDC (hχ y0)
    have key := hblockC x' rfl (hmem x')
    have hjb : jBlock d L (M1 * N₁) 1 1 x' = y' := by
      unfold jBlock; rw [blockMap_pow_one']; exact hx'm
    have hψy : ∀ i, ψ (jBlock d L (M1 * N₁) 1 1 x') i = baseSectorTheta θ y i := by
      intro i
      rw [hjb]
      simp only [hψ, hy', castCoarse_castC]
    have e1' : ∀ (z' : Torus d (M1 * N₁ * L ^ 1)) (i : Fin N),
        bgFieldC G1 (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N)
          (liftSingle G1 ψ.toC (fun i => (h i : ℂ))) (⟨z', hmem z'⟩, i) =
        bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
          (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N) (baseSectorDatum ϱ θ h)
          (⟨castSite hn.symm z', hmemD _⟩, i) := fun z' i => by
      have := e1 (castSite hn.symm z') i
      have hs : (⟨castSite hn (castSite hn.symm z'), hmem _⟩ : G1.Ω 1) = ⟨z', hmem z'⟩ :=
        Subtype.ext (castSite_cancel hn z')
      rw [hs] at this
      exact this
    have hbavg : ∀ i, blockAvg G1 (bgFieldC G1 (compWeight L a₁) (if regimeB then ν else 0)
        (bgC0 d L N) (liftSingle G1 ψ.toC (fun i => (h i : ℂ)))) x' i =
        ((L : ℝ) ^ d)⁻¹ * ∑ z' ∈ Finset.univ.filter (fun z' : Torus d (M1 * N₁ * L ^ 1) =>
          blockMap L (M1 * N₁ * L ^ (1 - 1)) z' = y'),
          bgFieldC (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
            (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N) (baseSectorDatum ϱ θ h)
            (⟨castSite hn.symm z', hmemD _⟩, i) := by
      intro i
      unfold blockAvg
      rw [hG1, layerIndex_single le_rfl, pow_one, blk_eq_fibre]
      have hset : blockFibre (ℓ := M1 * N₁ * L ^ 1) (L ^ 1) (M1 * N₁ * L ^ (1 - 1))
          (jBlock d L (M1 * N₁) 1 1 x') = Finset.univ.filter (fun z' : Torus d (M1 * N₁ * L ^ 1) =>
          blockMap L (M1 * N₁ * L ^ (1 - 1)) z' = y') := by
        ext z'
        rw [mem_blockFibre, hjb, blockMap_pow_one']
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hset]
      congr 1
      refine Finset.sum_congr rfl fun z' _ => ?_
      rw [svec_of_mem G1 _ ⟨z', hmem z'⟩]
      exact e1' z' i
    have hspin : ∀ i, spinAverage (baseSectorN L n) L 1 1 (fun z i => baseSectorCenter ϱ
        (compWeight L a₁) regimeB ν h θ (baseSector_side L n ▸ z : Torus d (L * n)) i) y i =
        (blockAvg G1 (bgFieldC G1 (compWeight L a₁) (if regimeB then ν else 0)
          (bgC0 d L N) (liftSingle G1 ψ.toC (fun i => (h i : ℂ)))) x' i).re := by
      intro i
      rw [hbavg i, Complex.re_ofReal_mul]
      unfold spinAverage
      congr 1
      have hsf := sum_fibre_cast hn y (fun z => bgFieldC
        (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
        (compWeight L a₁) (if regimeB then ν else 0) (bgC0 d L N) (baseSectorDatum ϱ θ h)
        (⟨z, hmemD z⟩, i))
      rw [← hy'] at hsf
      rw [← hsf, Complex.re_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      exact e2 z i
    have hrn : rn (fun i => baseSectorTheta θ y i - spinAverage (baseSectorN L n) L 1 1
        (fun z i => baseSectorCenter ϱ (compWeight L a₁) regimeB ν h θ
          (baseSector_side L n ▸ z : Torus d (L * n)) i) y i) ≤
        vn (fun i => (ψ (jBlock d L (M1 * N₁) 1 1 x') i : ℂ) -
          blockAvg G1 (bgFieldC G1 (compWeight L a₁) (if regimeB then ν else 0)
            (bgC0 d L N) (liftSingle G1 ψ.toC (fun i => (h i : ℂ)))) x' i) := by
      refine le_trans (le_of_eq ?_) (rn_re_le_vn _)
      congr 1
      funext i
      rw [hspin i, hψy i, Complex.sub_re, Complex.ofReal_re]
    exact lt_of_le_of_lt hrn key



end Balaban.LargeField.Base
