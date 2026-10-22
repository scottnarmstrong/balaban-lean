module

public import Balaban.LargeField.Base.BaseFirstAction
public import Balaban.SmallField.Def6v2

/-!
# The first-step action as the class's action at scale `1`

The small-field density of the class at scale `1` is `exp(expo2 …)` with
`expo2 = -(betaFine d L 1 (β 1)) · action (topGS …) (aIdeal L 1 (a 1)) (Rg.physMass 1) D
(bgField …) + ℰ - E|T| + ℱ`.  The first physical step produces `exp(-β A₁(e_θ; θ))` with
`A₁(φ; θ) = H(φ) + (a L^{d-2}/2) Σ_y |θ_y - (Qφ)_y|²`.

The two agree exactly, term by term, under the dictionary

* the generating set `topGS d L N₁ m₁ 1 ϱ` is the single-scale set (`topGS_one_eq_single`);
* the block weight is `a 1 = aIdeal L 1 (a 1) 1` (`aIdeal_one_one`);
* the mass of the class is `Rg.physMass 1 = ν_1 / L²`, the same in the action and in `bgField`
  (`Regime.sfBgMass_eq`), and it is the mass `ν` of the physical energy;
* the fine inverse temperature is `betaFine d L 1 (β 1) = β 1 / L^{d-2}`, so `β = betaFine …`
  exactly when `β 1 = β L^{d-2}` (`betaFine_one_mul`);
* the data `D(θ)` is `firstDatum`, the lift of the coarse field `θ` with constant field `h`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Matrix

variable {d N L n : ℕ} [NeZero L] [NeZero n]

open Classical

/-- **The datum `D(θ)` of the first step** on the single-scale generating set over the coarse side
`N₀`: the lift of the coarse real field `θ` and the constant field `h`. -/
noncomputable def firstDatum {N₀ : ℕ} [NeZero N₀] (ϱ : ℝ) (hc : N₀ * L ^ (1 - 1) = n)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (h : EuclideanSpace ℝ (Fin N)) :
    BgData (GeneratingSet.single (d := d) (L := L) (N₀ := N₀) (k := 1) ϱ) N :=
  liftSingle (GeneratingSet.single (d := d) (L := L) (N₀ := N₀) (k := 1) ϱ)
    (fun y i => ((θ (hc ▸ y) i : ℝ) : ℂ)) (fun i => (h i : ℂ))

/-- At the coarse side `1 * n` the datum is the first-step datum `baseSectorDatum`. -/
theorem firstDatum_one_mul (ϱ : ℝ) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (h : EuclideanSpace ℝ (Fin N)) :
    firstDatum (N₀ := 1 * n) ϱ (baseSector_coarse L n) θ h = baseSectorDatum ϱ θ h := rfl

omit [NeZero L] in
/-- The mass-carrying branch of the regime switch is the mass itself. -/
theorem bgHyp_ite_of {ϱ : ℝ} {a : ℕ → ℝ} {μ : ℝ} {regimeB : Prop} (hr : regimeB)
    (H : BgHyp d L 1 ϱ a μ) : BgHyp d L 1 ϱ a (if regimeB then μ else 0) := by
  simpa only [hr, ↓reduceIte] using H

/-- **The first-step action at the background field, on a coarse side `N₀ = 1 * n`**, in the
mass-carrying regime. -/
theorem baseFirst_action_bgField_of_eq {N₀ : ℕ} [NeZero N₀] (hN : N₀ = 1 * n)
    (hc : N₀ * L ^ (1 - 1) = n) (ϱ : ℝ) (aw : ℕ → ℝ) (a₀ : ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (hr : regimeB) (ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw ν) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (hU : InUnionDomainR (GeneratingSet.single (d := d) (L := L)
      (N₀ := N₀) (k := 1) ϱ) (bgC1 d L N) ν (firstDatum ϱ hc θ h)) :
    let G := GeneratingSet.single (d := d) (L := L) (N₀ := N₀) (k := 1) ϱ
    let D := firstDatum ϱ hc θ h
    let e : Torus d (L * n) → EuclideanSpace ℝ (Fin N) := baseSectorCenter ϱ aw regimeB ν h θ
    let ec : CfgT d N L n := fun x => ⟨e x,
      mem_sphere_zero_iff_norm.mpr
        (baseSectorCenter_unit ϱ aw regimeB ν h hh (bgHyp_ite_of hr H) θ x)⟩
    action G aw ν D (bgField G aw ν D) =
      energy d N (L * n) ν h ec +
        (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
          ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2 := by
  subst hN
  have hμ : (if regimeB then ν else 0) = ν := by simp only [hr, ↓reduceIte]
  have hU' : InUnionDomainR (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) (bgC1 d L N) (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h) := by
    rw [hμ]
    exact hU
  have := baseFirst_action_bgField ϱ aw a₀ ha regimeB ν h hh (bgHyp_ite_of hr H) θ hU'
  simp only [hμ] at this
  exact this

section Class

variable {N₁ m₁ : ℕ} [NeZero N₁] {ϱ : ℝ}

/-- The top generating set of the class at scale `1` is the single-scale generating set. -/
theorem topGS_one_eq_single :
    topGS d L N₁ m₁ 1 ϱ = GeneratingSet.single (d := d) (L := L) (N₀ := N₁ * L ^ m₁) (k := 1) ϱ :=
  rfl

omit [NeZero L] in
omit [NeZero L] in
/-- The ideal block weight at scale `1` is `a 1`. -/
theorem aIdeal_one_one (hL : 2 ≤ L) (a₁ : ℝ) : aIdeal L 1 a₁ 1 = a₁ := by
  have hL' : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : (1 : ℝ) - ((L : ℝ) ^ 1)⁻¹ ^ 2 ≠ 0 := by
    have : ((L : ℝ) ^ 1)⁻¹ ^ 2 < 1 := by
      rw [pow_one, inv_pow]
      exact inv_lt_one_of_one_lt₀ (by nlinarith)
    linarith
  unfold aIdeal
  exact mul_div_cancel_right₀ a₁ h1

/-- The fine inverse temperature at scale `1`: `β = betaFine d L 1 (β L^{d-2})`. -/
theorem betaFine_one_mul (β : ℝ) : betaFine d L 1 (β * (L : ℝ) ^ (d - 2)) = β := by
  have hL : (L : ℝ) ^ (d - 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne L))
  unfold betaFine
  rw [one_mul]
  exact mul_div_cancel_right₀ β hL

/-- The physical mass at scale `1`: `physMass L 1 (L² μ) = μ`. -/
theorem physMass_one_mul (μ : ℝ) : physMass L 1 ((L : ℝ) ^ 2 * μ) = μ := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  unfold physMass
  rw [pow_one, inv_pow]
  field_simp

/-- **The class's background action is the first-step action `A₁(e_θ; θ)`** (deliverable 1).
For `D(θ) = firstDatum` on the real data domain, with `aw = aIdeal L 1 (a 1)`, the physical mass
`μ = Rg.physMass 1` (also the solver mass `Rg.sfBgMass 1`) and `e_θ = baseSectorCenter`:
`action (topGS …) aw μ D(θ) (bgField …) = energy μ h e_θ + (a 1 · L^d / (2 L²)) Σ_y |θ_y - (Q e_θ)_y|²`.
The right side is `A₁(e_θ; θ)` with `a L^{d-2}/2 = a L^d / (2 L²)`. -/
theorem baseFirst_action_eq_class (hL : 2 ≤ L) (Rg : Regime L) (a : ℕ → ℝ)
    (hN : N₁ * L ^ m₁ = 1 * n) (hc : N₁ * L ^ m₁ * L ^ (1 - 1) = n)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ (aIdeal L 1 (a 1)) (Rg.physMass 1))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (hU : InUnionDomainR (topGS d L N₁ m₁ 1 ϱ) (bgC1 d L N) (Rg.physMass 1)
      (firstDatum ϱ hc θ h)) :
    let G := topGS d L N₁ m₁ 1 ϱ
    let D : BgData G N := firstDatum ϱ hc θ h
    let e : Torus d (L * n) → EuclideanSpace ℝ (Fin N) :=
      baseSectorCenter ϱ (aIdeal L 1 (a 1)) True (Rg.physMass 1) h θ
    let ec : CfgT d N L n := fun x => ⟨e x,
      mem_sphere_zero_iff_norm.mpr
        (baseSectorCenter_unit ϱ (aIdeal L 1 (a 1)) True (Rg.physMass 1) h hh (bgHyp_ite_of trivial H) θ x)⟩
    action G (aIdeal L 1 (a 1)) (Rg.physMass 1) D
        (bgField G (aIdeal L 1 (a 1)) (Rg.sfBgMass 1) D) =
      energy d N (L * n) (Rg.physMass 1) h ec +
        (a 1 * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
          ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2 :=
  baseFirst_action_bgField_of_eq (N₀ := N₁ * L ^ m₁) hN hc ϱ (aIdeal L 1 (a 1)) (a 1)
    (aIdeal_one_one hL (a 1)) True trivial (Rg.physMass 1) h hh H θ hU

/-- **The exponent of the class at scale `1` is `-β A₁(e_θ; θ) + ℰ - E|T| + Fcomp`** when the fine
inverse temperature `β` of the physical step and the class coupling are related by
`β 1 = β L^{d-2}`. -/
theorem expo2_one_eq_firstAction (hL : 2 ≤ L) (P : Consts) (Rg : Regime L) (β a : ℕ → ℝ)
    (Tm : Terms d L N₁ m₁ 1 N ϱ) (Ek : ℝ) (g : Fld d L N₁ m₁ 1 N)
    (hN : N₁ * L ^ m₁ = 1 * n) (hc : N₁ * L ^ m₁ * L ^ (1 - 1) = n)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ (aIdeal L 1 (a 1)) (Rg.physMass 1))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (hU : InUnionDomainR (topGS d L N₁ m₁ 1 ϱ) (bgC1 d L N) (Rg.physMass 1)
      (firstDatum ϱ hc θ h)) (βp : ℝ) (hβ : β 1 = βp * (L : ℝ) ^ (d - 2)) :
    let G := topGS d L N₁ m₁ 1 ϱ
    let D : BgData G N := firstDatum ϱ hc θ h
    let e : Torus d (L * n) → EuclideanSpace ℝ (Fin N) :=
      baseSectorCenter ϱ (aIdeal L 1 (a 1)) True (Rg.physMass 1) h θ
    let ec : CfgT d N L n := fun x => ⟨e x,
      mem_sphere_zero_iff_norm.mpr
        (baseSectorCenter_unit ϱ (aIdeal L 1 (a 1)) True (Rg.physMass 1) h hh (bgHyp_ite_of trivial H) θ x)⟩
    expo2 P Rg β a Tm Ek D g =
      -((βp * (energy d N (L * n) (Rg.physMass 1) h ec +
        (a 1 * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
          ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2 : ℝ) : ℝ) : ℂ) +
        Ecomp P.m₀ Tm (aIdeal L 1 (a 1)) (Rg.sfBgMass 1) D -
        (Ek : ℂ) * (((N₁ * L ^ m₁) ^ d : ℕ) : ℂ) +
        Fcomp P.m₀ Tm (aIdeal L 1 (a 1)) (Rg.sfBgMass 1) D g := by
  intro G D e ec
  have hA := baseFirst_action_eq_class hL Rg a hN hc h hh H θ hU
  have hb : betaFine d L 1 (β 1) = βp := by rw [hβ]; exact betaFine_one_mul βp
  dsimp only at hA
  unfold expo2
  rw [hb, hA]
  push_cast
  ring

end Class

end Balaban.LargeField
