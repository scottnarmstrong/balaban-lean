/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormExpLemma35
public import Balaban.Background.ScaledDomainC

/-!
# The complex renormalized background at the real mass

`RenormThetaDatum` item (ii): for complex `ξ` the renormalized datum `θ_ξ = ((1 + ε ξ₁) Ψ, h)` depends on
`ξ₁` only, so its background is the solution at the real mass `ν`, i.e. the case `ξ = (ξ₁, 0, 0)` of the
perturbed system.

* `IsRenSol.eq_bgC`: for `ξ₂ = ξ₃ = 0` and complex `ξ₁` the solution map is
  `F((Ψ, h), ξ) = (φ^c_θ − φ^r, α^c_θ − α^r)`, where `(φ^c_θ, α^c_θ)` is a small solution of the datum
  `((1 + ζ) Ψ, h)` at the mass `ν` (complex analogue of `IsRenSol.eq_bg`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {a : ℕ → ℝ} {ν εζ ε r B : ℝ}
  {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}

/-- **The solution map at complex `ξ₁` and the real mass** (complex analogue of `IsRenSol.eq_bg`). -/
theorem IsRenSol.eq_bgC (hF : IsRenSol G a ν ε ε r B F) (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {D Dc : BgData G N} (hD : XiCOne G a ν ε D) {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ < r)
    (h1 : ξ 1 = 0) (h2 : ξ 2 = 0)
    (hΨ : ∀ x i, Dc.Ψ x i = (1 + renZeta ε ξ) * D.Ψ x i) (hh : ∀ x i, Dc.h x i = D.h x i)
    {c₀ : ℝ} (hc₀ : 2 * c₀ ≤ c6 d L N) {φc : G.Ω 1 × Fin N → ℂ} {αc : G.Ω 1 → ℂ}
    (hφc : IsSmallSolution G a ν c₀ Dc φc αc) :
    F ((D.Ψ, D.h), ξ) =
      (φc - bgFieldC G a ν (bgC0 d L N) D, αc - bgMultC G a ν (bgC0 d L N) D) := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨-, hs, hb, -⟩ := hD.bg H hsm hε hc1
  set φ := bgFieldC G a ν (bgC0 d L N) D
  set α := bgMultC G a ν (bgC0 d L N) D
  have hP := isPerturbed_of_EL a (μ := ν) (μu := ν) (δΨ := fun x i => renZeta ε ξ * D.Ψ x i)
    (fun x i => by rw [hΨ]; ring) hh (φ₀ := svec G φ) (fun x i => by rw [svec_of_mem]) hs.1 hφc.1
  have hm : renMassU ν ξ = (ν : ℂ) := by unfold renMassU; rw [h1, h2]; simp
  have hPM : IsPerturbedM G a (renMassU ν ξ) α (barField G D.Ψ φ)
      (pertSource G a (fun x i => renZeta ε ξ * D.Ψ x i) (renF1 ν ξ D.h φ)) (φc - φ) (αc - α) := by
    have ef : renF1 (G := G) ν ξ D.h φ =
        fun p => (((ν - ν : ℝ) : ℂ)) * (D.h p.1 p.2 - φ p) := by
      funext p; simp [renF1, hm]
    rw [hm, ef, isPerturbedM_congr_base G a _ α (φ₀' := svec G φ)
      (fun x i => by simp [barField, svec_of_mem]), isPerturbedM_ofReal]
    exact hP
  have hsmall : Small G (αc - α) (c6 d L N) := by
    intro x
    have h1' := (hφc.2 x).le
    have h2' := hb.alpha x
    obtain ⟨-, -, -, hKc⟩ := bgC1_facts d L N hd0 hc1
    have hc0 : bgC0 d L N ≤ c6 d L N := bgC0_le_c6 d L N
    have hsp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
      have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k))); positivity
    simp only [Pi.sub_apply]
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖αc x - α x‖
        ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (‖αc x‖ + ‖α x‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) hsp
      _ ≤ c6 d L N := by rw [mul_add]; linarith
  obtain ⟨e1, e2⟩ := hF.unique D hD _ hξ _ _ hPM hsmall
  exact Prod.ext e1.symm e2.symm

end Balaban.Fluctuation
