/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseChartActReads
public import Balaban.LargeField.Base.BaseCrossValue
public import Balaban.LargeField.Base.BaseChartTerms

/-!
# The Hamiltonian and the chart exponent of two generating sets agree near a deep site

The entries of the Hessian `H(α)` of the first step on two generating sets at sites with the same
layers agree (`fullMatrix_cross`, `baseHamiltonian_cross`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Base

open Balaban Balaban.Multiscale Balaban.Localization Matrix

section Ham

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-- The entry of the averaging form at two sites only depends on the layers of the two sites. -/
theorem avgMatrix_cross (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ') (a : ℕ → ℝ)
    {x y : Torus d (N₀ * L ^ k)}
    (hx : ∀ j, 1 ≤ j → j ≤ k → (x ∈ G.layer j ↔ x ∈ G'.layer j))
    (hy : ∀ j, 1 ≤ j → j ≤ k → (y ∈ G.layer j ↔ y ∈ G'.layer j)) :
    avgMatrix G a x y = avgMatrix G' a x y := by
  unfold avgMatrix
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  congr 1
  unfold layerProjMatrix
  simp only [hx j h1 h2, hy j h1 h2]

theorem fullMatrix_cross (G : GeneratingSet d L N₀ k ϱ) (G' : GeneratingSet d L N₀ k ϱ')
    (a : ℕ → ℝ) (ν : ℝ) {x y : Torus d (N₀ * L ^ k)}
    (hx : ∀ j, 1 ≤ j → j ≤ k → (x ∈ G.layer j ↔ x ∈ G'.layer j))
    (hy : ∀ j, 1 ≤ j → j ≤ k → (y ∈ G.layer j ↔ y ∈ G'.layer j)) :
    fullMatrix G a ν x y = fullMatrix G' a ν x y := by
  unfold fullMatrix
  simp only [Matrix.add_apply, avgMatrix_cross G G' a hx hy]

end Ham

section Ham1

variable {d L N₁ m₁ : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}

/-- **The Hessian of the first step agrees at two sites of two generating sets** that have the same
layers there and the same multiplier on the diagonal. -/
theorem baseHamiltonian_cross (G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (G' : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ') (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (α' : G'.Ω 1 → ℂ) {x y : G.Ω 1} {x' y' : G'.Ω 1}
    (hxx : (x : Torus d (N₁ * L ^ m₁ * L ^ 1)) = x') (hyy : (y : Torus d (N₁ * L ^ m₁ * L ^ 1)) = y')
    (hlx : ∀ j, 1 ≤ j → j ≤ 1 → ((x : Torus d (N₁ * L ^ m₁ * L ^ 1)) ∈ G.layer j ↔
      (x : Torus d (N₁ * L ^ m₁ * L ^ 1)) ∈ G'.layer j))
    (hly : ∀ j, 1 ≤ j → j ≤ 1 → ((y : Torus d (N₁ * L ^ m₁ * L ^ 1)) ∈ G.layer j ↔
      (y : Torus d (N₁ * L ^ m₁ * L ^ 1)) ∈ G'.layer j))
    (hα : x = y → α x = α' x') :
    baseHamiltonian G a ν α (fun _ => 1) x y = baseHamiltonian G' a ν α' (fun _ => 1) x' y' := by
  rw [baseHamiltonian_one, baseHamiltonian_one]
  have hxy : x = y ↔ x' = y' := by
    constructor
    · intro h; apply Subtype.ext; rw [← hxx, ← hyy, h]
    · intro h; apply Subtype.ext; rw [hxx, hyy, h]
  unfold dirichletOperator
  simp only [Green.restrictOp, Matrix.add_apply, Matrix.submatrix_apply, Matrix.map_apply,
    Matrix.diagonal_apply]
  rw [← hxx, ← hyy] at *
  rw [fullMatrix_cross G G' a ν hlx hly]
  by_cases h : x = y
  · have h' : x' = y' := hxy.1 h
    subst h
    simp only [↓reduceIte, h', hα rfl]
  · have h' : ¬ x' = y' := fun h2 => h (hxy.2 h2)
    simp only [h, h', ↓reduceIte]

end Ham1

section Reads

variable {d L N₁ m₁ N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}

local notation "𝕋" => Torus d (N₁ * L ^ m₁ * L ^ 1)

/-- The matrix-vector product with the whitening, across two generating sets: if the rows of the two
whitening matrices are supported within `ρ` of the row and agree under the identification of the sites
(`hWx`), and the fields agree on the sites within `ρ + L` of `x`, the whitened fields agree at the
sites within `L` of `x`. -/
theorem whiten_cross (Gl : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ)
    (Gp : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ') (hΩp : ∀ z, z ∈ Gp.Ω 1) {ρ : ℕ}
    (Wl : Matrix (Gl.Ω 1 × Fin N) (Gl.Ω 1 × Fin N) ℂ) (Wp : Matrix (Gp.Ω 1 × Fin N) (Gp.Ω 1 × Fin N) ℂ)
    (ψl : Gl.Ω 1 × Fin N → ℂ) (ψp : Gp.Ω 1 × Fin N → ℂ)
    {y : Gl.Ω 1} {y' : Gp.Ω 1} (hyy : (y : Torus d (N₁ * L ^ m₁ * L ^ 1)) = y') (i : Fin N)
    (hdeep : ∀ z : Gp.Ω 1, supDist (y : Torus d (N₁ * L ^ m₁ * L ^ 1)) z ≤ ρ →
      (z : Torus d (N₁ * L ^ m₁ * L ^ 1)) ∈ Gl.Ω 1)
    (hWl : ∀ r, Wl (y, i) r ≠ 0 → supDist (y : Torus d (N₁ * L ^ m₁ * L ^ 1)) r.1 ≤ ρ)
    (hWp : ∀ r, Wp (y', i) r ≠ 0 → supDist (y' : Torus d (N₁ * L ^ m₁ * L ^ 1)) r.1 ≤ ρ)
    (hWx : ∀ (r : Gl.Ω 1 × Fin N) (r' : Gp.Ω 1 × Fin N),
      (r.1 : Torus d (N₁ * L ^ m₁ * L ^ 1)) = r'.1 → r.2 = r'.2 → Wp (y', i) r' = Wl (y, i) r)
    (hψ : ∀ (r : Gl.Ω 1 × Fin N) (r' : Gp.Ω 1 × Fin N),
      (r.1 : Torus d (N₁ * L ^ m₁ * L ^ 1)) = r'.1 → r.2 = r'.2 → supDist (y : Torus d (N₁ * L ^ m₁ * L ^ 1)) r.1 ≤ ρ →
        ψp r' = ψl r) :
    (Wp *ᵥ ψp) (y', i) = (Wl *ᵥ ψl) (y, i) := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  symm
  set J : Gl.Ω 1 × Fin N → Gp.Ω 1 × Fin N := fun r => (⟨(r.1 : Torus d (N₁ * L ^ m₁ * L ^ 1)), hΩp r.1⟩, r.2)
    with hJ
  have heq : ∀ r : Gl.Ω 1 × Fin N, supDist (y : Torus d (N₁ * L ^ m₁ * L ^ 1)) r.1 ≤ ρ →
      Wl (y, i) r * ψl r = Wp (y', i) (J r) * ψp (J r) := fun r hr => by
    rw [hWx r (J r) rfl rfl, hψ r (J r) rfl rfl hr]
  refine Finset.sum_bij_ne_zero (fun r _ _ => J r) (fun _ _ _ => Finset.mem_univ _)
    (fun r₁ _ _ r₂ _ _ h => ?_) (fun r' _ hr' => ?_) (fun r _ hr => ?_)
  · have h1 : (r₁.1 : Torus d (N₁ * L ^ m₁ * L ^ 1)) = r₂.1 := by
      have := congrArg (fun q : Gp.Ω 1 × Fin N => ((q.1 : Gp.Ω 1) : Torus d (N₁ * L ^ m₁ * L ^ 1))) h
      simpa [hJ] using this
    exact Prod.ext (Subtype.ext h1) (by simpa [hJ] using congrArg Prod.snd h)
  · have hW0 : Wp (y', i) r' ≠ 0 := fun h0 => hr' (by rw [h0]; simp)
    have hd := hWp r' hW0
    have hdl : supDist (y : Torus d (N₁ * L ^ m₁ * L ^ 1)) r'.1 ≤ ρ := by rw [hyy]; exact hd
    have hmem := hdeep r'.1 hdl
    set a : Gl.Ω 1 × Fin N := (⟨r'.1.1, hmem⟩, r'.2) with ha
    have hJa : J a = r' := Prod.ext (Subtype.ext rfl) rfl
    have hne : Wl (y, i) a * ψl a ≠ 0 := by
      rw [heq a hdl, hJa]; exact hr'
    exact ⟨a, Finset.mem_univ _, hne, hJa⟩
  · have hW0 : Wl (y, i) r ≠ 0 := fun h0 => hr (by rw [h0]; simp)
    exact heq r (hWl r hW0)

open Classical in
/-- **The chart exponent reads the same seed on two generating sets** (`ReadsSeedCross`).  Let `Gp` have
`Ω₁` the whole torus and `Gl` contain the sites within `ρ + L` of `x`, with the same layers there; let
the whitening families be supported within `ρ` of the row, agree under the identification of the sites when
the backgrounds agree within `ρ` of the row (`hWx`), and let the source at `x` and the field within `ρ + L`
of `x` agree.  Then `V_x` of the two systems is a pair of functionals of the backgrounds that read the same
seed `{y : |x - y| ≤ ρ + L}`. -/
theorem chartFe_readsSeedCross {Gl : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ}
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ'} (hΩp : ∀ z, z ∈ Gp.Ω 1) (a : ℕ → ℝ) (ν β : ℝ)
    (gl ψl : Gl.Ω 1 × Fin N → ℂ) (gp ψp : Gp.Ω 1 × Fin N → ℂ)
    (Wl : ((Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) → Matrix (Gl.Ω 1 × Fin N) (Gl.Ω 1 × Fin N) ℂ)
    (Wp : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → Matrix (Gp.Ω 1 × Fin N) (Gp.Ω 1 × Fin N) ℂ)
    (x : Gl.Ω 1) (x' : Gp.Ω 1) (hxx : (x : 𝕋) = x') (ρ : ℕ)
    (hdeep : ∀ z : 𝕋, supDist (x : 𝕋) z ≤ ρ + L → z ∈ Gl.Ω 1)
    (hlay : ∀ z : 𝕋, supDist (x : 𝕋) z ≤ ρ + L → ∀ j, 1 ≤ j → j ≤ 1 →
      (z ∈ Gl.layer j ↔ z ∈ Gp.layer j))
    (hg : ∀ i, gp (x', i) = gl (x, i))
    (hψ : ∀ (r : Gl.Ω 1 × Fin N) (r' : Gp.Ω 1 × Fin N), (r.1 : 𝕋) = r'.1 → r.2 = r'.2 →
      supDist (x : 𝕋) r.1 ≤ ρ + L → ψp r' = ψl r)
    (hWl : ∀ u p r, Wl u p r ≠ 0 → supDist (p.1 : 𝕋) r.1 ≤ ρ)
    (hWp : ∀ u p r, Wp u p r ≠ 0 → supDist (p.1 : 𝕋) r.1 ≤ ρ)
    (hWx : ∀ (u : (Gl.Ω 1 × Fin N → ℂ) × (Gl.Ω 1 → ℂ)) (u' : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (p : Gl.Ω 1 × Fin N) (p' : Gp.Ω 1 × Fin N) (r : Gl.Ω 1 × Fin N) (r' : Gp.Ω 1 × Fin N),
      (p.1 : 𝕋) = p'.1 → p.2 = p'.2 → (r.1 : 𝕋) = r'.1 → r.2 = r'.2 →
      (∀ (y : Gl.Ω 1) (y' : Gp.Ω 1), (y : 𝕋) = y' → supDist (p.1 : 𝕋) y ≤ ρ →
        (∀ i, u.1 (y, i) = u'.1 (y', i)) ∧ u.2 y = u'.2 y') → Wp u' p' r' = Wl u p r) :
    ReadsSeedCross Gl Gp (seedBall (x : 𝕋) (ρ + L))
      (chartFe Gl a ν β gl ψl Wl x) (chartFe Gp a ν β gp ψp Wp x') := by
  classical
  intro u u' hφ hα
  have hxs : supDist (x : 𝕋) x ≤ ρ + L := by rw [supDist_self]; exact Nat.zero_le _
  have hx'j : x' = ⟨(x : 𝕋), hΩp x⟩ := (Subtype.ext hxx).symm
  set jm : Gl.Ω 1 → Gp.Ω 1 := fun y => ⟨(y : 𝕋), hΩp y⟩ with hjm
  have hx'jm : x' = jm x := hx'j
  set NB : Finset (Gl.Ω 1) := Finset.univ.filter fun y => supDist (x : 𝕋) y ≤ L with hNB
  have hmemNB : ∀ y, y ∈ NB ↔ supDist (x : 𝕋) y ≤ L := by intro y; simp [hNB]
  have hxNB : x ∈ NB := (hmemNB x).2 (by rw [supDist_self]; exact Nat.zero_le _)
  have hseed : ∀ y : Gl.Ω 1, supDist (x : 𝕋) y ≤ ρ + L →
      (∀ i, u.1 (y, i) = u'.1 (jm y, i)) ∧ u.2 y = u'.2 (jm y) := fun y hy =>
    ⟨fun i => hφ y (jm y) rfl (mem_seedBall.2 hy) i, hα y (jm y) rfl (mem_seedBall.2 hy)⟩
  have hHH : ∀ y ∈ NB, baseHamiltonian Gp a ν u'.2 (fun _ => 1) (jm x) (jm y) =
      baseHamiltonian Gl a ν u.2 (fun _ => 1) x y := by
    intro y hy
    have hyd := (hmemNB y).1 hy
    refine (baseHamiltonian_cross Gl Gp a ν u.2 u'.2 (x := x) (y := y) (x' := jm x) (y' := jm y)
      rfl rfl (hlay _ hxs) (hlay _ (by omega)) ?_).symm
    intro hxy
    rw [(hseed x hxs).2]
  rw [hx'jm]
  refine (chartSite_cross (β := β) (e := fun y i => u.1 (y, i)) (e' := fun y i => u'.1 (y, i))
    (H := baseHamiltonian Gl a ν u.2 (fun _ => 1)) (H' := baseHamiltonian Gp a ν u'.2 (fun _ => 1))
    (g := gl) (g' := gp) (w := Wl u *ᵥ ψl) (w' := Wp u' *ᵥ ψp) jm x NB hxNB
    (fun a _ b _ h => Subtype.ext (congrArg (fun q : Gp.Ω 1 => (q : 𝕋)) h))
    (fun y h => (hmemNB y).2 (baseHamiltonian_ne_zero_dist Gl a ν u.2 h))
    (fun y' h => ?_) hHH (fun i => by rw [← hx'jm]; exact hg i) (fun y hy => ?_) (fun y hy i => ?_)).symm
  · have hd := baseHamiltonian_ne_zero_dist Gp a ν u'.2 h
    have hd' : supDist (x : 𝕋) y' ≤ L := by
      have : (jm x : 𝕋) = x := rfl
      rw [← this]; exact hd
    refine Finset.mem_image.2 ⟨⟨(y' : 𝕋), hdeep _ (by omega)⟩, (hmemNB _).2 hd', Subtype.ext rfl⟩
  · funext i
    exact (hseed y (by have := (hmemNB y).1 hy; omega)).1 i |>.symm
  · have hyd := (hmemNB y).1 hy
    refine whiten_cross Gl Gp hΩp (Wl u) (Wp u') ψl ψp (y := y) (y' := jm y) (ρ := ρ) rfl i ?_ ?_ ?_
      ?_ ?_
    · intro z hz
      exact hdeep _ (le_trans (supDist_triangle (x : 𝕋) y z) (by omega))
    · exact fun r h => hWl u (y, i) r h
    · exact fun r h => hWp u' (jm y, i) r h
    · intro r r' h1 h2
      refine hWx u u' (y, i) (jm y, i) r r' rfl rfl h1 h2 ?_
      intro z z' hzz hz
      have hz2 : supDist (y : 𝕋) z ≤ ρ := hz
      have hz' : z' = jm z := Subtype.ext hzz.symm
      subst hz'
      exact hseed z (le_trans (supDist_triangle (x : 𝕋) y z) (by omega))
    · intro r r' h1 h2 hr
      have hr' : r' = (jm r.1, r.2) := Prod.ext (Subtype.ext h1.symm) h2.symm
      rw [hr']
      exact hψ r _ rfl rfl (le_trans (supDist_triangle (x : 𝕋) y r.1) (by omega))

end Reads

end Balaban.LargeField.Base
