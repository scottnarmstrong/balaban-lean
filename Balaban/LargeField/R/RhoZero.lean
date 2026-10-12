/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroFinal
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The reference density of a component (Definition III.8.1, P7 (1.5), (3.1)-(3.2))

For a ripe component `Z` with outcome "to `R`" and `Z₀ = box b₀ w` (Lemma III.3.2 (c)), the reference density is
`ρ_{k,0}(Z) = χ_{Z₀} exp(-β_k A*_k(Z; ψ_k, φ_k(𝔹_k(U_k); ψ̃_k)))`, a function of `ψ_k↾Z₀` (the variable `u` of
`SuppSpace`) for the fixed outside data `ψ_k↾Z₀ᶜ`, where

* `χ_{Z₀} = 1[|ψ_k(z) - ψ⁰_k(z)| < C₆ β_k^{-1/2} p₀(β_k) ∀ z ∈ Z₀]` with `C₆ = 3dD₀(K₆ + 1)` (`cSix`) and `ψ⁰_k` the
  unconditional solution `psiZero` of (2.34);
* the action is the effective action `effAction` of the lifted data (massless: the landed `ν = 0` action; the
  `ν`-term of P5 p. 490 vanishes) divided by the volume factor `L^{k(d-2)}` of the fine-unit normalization, so that
  the Hessian of `A*_k` is bounded below by the `k`-independent constant `gaussConst d D` (`psiZero_hess_of_geometry`).
  `β_k` and `p₀(β_k)` are real parameters.

`rhoZeroWith` is the density for an arbitrary centre `ψ⁰`; `rhoZero` is the source object (centre `psiZero`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section RhoZero

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

/-- The constant `C₆ = 3 d D₀ (K₆ + 1)` of Definition III.8.1. -/
def cSix (d D : ℕ) (K6 : ℝ) : ℝ := 3 * d * D * (K6 + 1)

/-- The cutoff radius `C₆ β^{-1/2} p₀(β)`. -/
noncomputable def zeroRadius (C6 β p0 : ℝ) : ℝ := C6 * β ^ (-(1 / 2 : ℝ)) * p0

/-- The normalized effective action `A*_k(ψ_k) = effAction / L^{k(d-2)}` (action in `k`-block units). -/
noncomputable def effActionNorm (ψ : BlockField d L N₀ k N) : ℝ :=
  effAction G a ψ / (L : ℝ) ^ (k * (d - 2))

variable {G a}

/-- The cutoff event of `χ_{Z₀}`: `|u(z) - ψ⁰(z)| < r` on every block `z` of `Z₀`. -/
def ZeroCutoff {Zf : Finset (Torus d (N₀ * L ^ (k - k)))} (ψ0 : BlockField d L N₀ k N) (r : ℝ)
    (u : SuppSpace Zf N) : Prop :=
  ∀ z : ↥Zf, rn (fun i => u (z, i) - ψ0 z i) < r

open Classical in
/-- **The cutoff `χ_{Z₀}`** (Definition III.8.1) about the centre `ψ⁰`. -/
noncomputable def chiZero {Zf : Finset (Torus d (N₀ * L ^ (k - k)))} (ψ0 : BlockField d L N₀ k N) (r : ℝ)
    (u : SuppSpace Zf N) : ℝ :=
  if ZeroCutoff ψ0 r u then 1 else 0

variable (G a)

/-- **The reference density** `ρ_{k,0}(Z)(ψ_k↾Z₀)` for the centre `ψ⁰` (`ψ_k↾Z₀ = u`, the rest of `ψ_k` fixed). -/
noncomputable def rhoZeroWith (Zf : Finset (Torus d (N₀ * L ^ (k - k)))) (ψ0 ψk : BlockField d L N₀ k N)
    (C6 β p0 : ℝ) (u : SuppSpace Zf N) : ℝ :=
  chiZero ψ0 (zeroRadius C6 β p0) u * Real.exp (-β * effActionNorm G a (mergeField Zf ψk u))

theorem rhoZeroWith_nonneg (Zf : Finset (Torus d (N₀ * L ^ (k - k))))
    (ψ0 ψk : BlockField d L N₀ k N) (C6 β p0 : ℝ) (u : SuppSpace Zf N) :
    0 ≤ rhoZeroWith G a Zf ψ0 ψk C6 β p0 u := by
  unfold rhoZeroWith chiZero
  split_ifs <;> positivity

theorem rhoZeroWith_eq_zero (Zf : Finset (Torus d (N₀ * L ^ (k - k))))
    (ψ0 ψk : BlockField d L N₀ k N) (C6 β p0 : ℝ) (u : SuppSpace Zf N)
    (h : ¬ ZeroCutoff ψ0 (zeroRadius C6 β p0) u) : rhoZeroWith G a Zf ψ0 ψk C6 β p0 u = 0 := by
  simp [rhoZeroWith, chiZero, h]

theorem rhoZeroWith_of_cutoff (Zf : Finset (Torus d (N₀ * L ^ (k - k))))
    (ψ0 ψk : BlockField d L N₀ k N) (C6 β p0 : ℝ) (u : SuppSpace Zf N)
    (h : ZeroCutoff ψ0 (zeroRadius C6 β p0) u) :
    rhoZeroWith G a Zf ψ0 ψk C6 β p0 u = Real.exp (-β * effActionNorm G a (mergeField Zf ψk u)) := by
  simp [rhoZeroWith, chiZero, h]

section Source

variable [NeZero N] {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)

/-- **Definition III.8.1: `ρ_{k,0}(Z)`** for `Z₀ = box b₀ w`: the cutoff about `ψ⁰_k = psiZero` with
`C₆ = 3dD₀(K₆+1)` (`D₀ = D`, `K₆ = psiZeroK`) times `exp(-β_k A*_k)`; a function of `u = ψ_k↾Z₀` for
`ψ_k ∈ Ψ̃(X ∖ Z₀; δ)` fixed outside `Z₀`. -/
noncomputable def rhoZero {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (β p0 : ℝ) (u : SuppSpace (boxFinset b0 w) N) : ℝ :=
  rhoZeroWith G a (boxFinset b0 w) (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk) ψk
    (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) β p0 u

end Source

end RhoZero

end Balaban.LargeField
