/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatEngineDom
public import Balaban.Fluctuation.HatEngineLift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The fan with the fluctuation decoupled by the cover parameters

The fluctuation field `ψ'(s) = β^{-1/2} C^{1/2}(s) ψ̂` is built from the decoupled square root
`decCovSqrt` at the same parameters `s` as the background objects: with `(φ, α) = F₁(s, Θ)`,
`C^{1/2}(s) = decCovSqrt Gp (compWeight L a₁) a₁ ν α (extS s) (φ̄) (unitQ) (unitP)`,
`φ̄ = barField Gp Ψ φ`, and `ψ'(s) = liftC (c • C^{1/2}(s) ψ̂)`.

* `hatSqrtF`, `hatPsiF`: these objects;
* `fanH_analytic`: analyticity of `(Θ, ψ̂, σ) ↦ Φ(F₁, Sol(s, flEdat (ψ'(s))).1, (Θ, ψ'(s)))`
  on the product of `Ξ^c`, a set of hat variables and the polydisc, generalizing
  `fanF_analytic`.  The complex-`s` sup bound of `decCovSqrt` (being proved separately) enters
  only as the explicit hypothesis `hSup` of this internal lemma, which keeps `ψ'(s)` in the ball
  of fluctuations.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section Fan

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}

variable (Gp a₁ ν) in
/-- **The decoupled square root** `C^{1/2}(s)` at the background `F₁(s, Θ) = (φ, α)`:
`decCovSqrt` with the multiplier `α`, the parameters `s` and the constraint field
`φ̄ = barField Gp Ψ φ`. -/
noncomputable def hatSqrtF
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (s : DecParams Gp) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) :
    Matrix (unitPts Gp × Fin N) (unitPts Gp × Fin N) ℂ :=
  decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, Θ)).2 (extS Gp s)
    (barField Gp Θ.1 (F₁ (s, Θ)).1) (unitQ Gp) (unitP Gp)

variable (Gp a₁ ν) in
/-- **The fluctuation field** `ψ'(s) = liftC (cc • C^{1/2}(s) ψ̂)` (`cc = β^{-1/2}`). -/
noncomputable def hatPsiF (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (s : DecParams Gp) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gp × Fin N → ℂ) :
    CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ :=
  liftC hG' (cc • (hatSqrtF Gp a₁ ν F₁ s Θ *ᵥ ψh))

section Analytic

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- **Analyticity of the fluctuation field in the data**: if `(s, (φ̄, α))` lies in `DecDom` at the
point `q` and `s, Ψ, φ, α, ψ̂` are analytic in `q`, then `ψ'(s) = liftC (cc • C^{1/2}(s) ψ̂)` is
analytic at `q`.  (Entries of `C^{1/2}` are analytic on `DecDom`, I-4c (iii).) -/
theorem analyticAt_hatPsi_of_decDom (hG' : IsLevel Gp (k + 1)) (hC : XSetting Gp (compWeight L a₁) a₁ ν)
    (hκ : 0 ≤ κ) (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ} (hδ : 0 ≤ δc)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {q : Q}
    {sF : Q → DecParams Gp} {ΨF : Q → CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
    {φF : Q → Gp.Ω 1 × Fin N → ℂ} {αF : Q → Gp.Ω 1 → ℂ} {ψh : Q → unitPts Gp × Fin N → ℂ}
    (hs : ∀ P, AnalyticAt ℂ (fun q => sF q P) q)
    (hΨ : ∀ y j, AnalyticAt ℂ (fun q => ΨF q y j) q)
    (hφ : ∀ r, AnalyticAt ℂ (fun q => φF q r) q) (hα : ∀ y, AnalyticAt ℂ (fun q => αF q y) q)
    (hψ : ∀ r, AnalyticAt ℂ (fun q => ψh q r) q)
    (hmem : (sF q, (barField Gp (ΨF q) (φF q), αF q)) ∈ DecDom Gp N κ δc) :
    AnalyticAt ℂ (fun q => liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (αF q)
      (extS Gp (sF q)) (barField Gp (ΨF q) (φF q)) (unitQ Gp) (unitP Gp) *ᵥ ψh q))) q := by
  classical
  have hbar := analyticAt_barField (Gp := Gp) φF ΨF hφ hΨ
  have he : AnalyticAt ℂ (fun q => (sF q, (barField Gp (ΨF q) (φF q), αF q))) q :=
    AnalyticAt.prod (analyticAt_pi_iff.2 hs) (hbar.prod (analyticAt_pi_iff.2 hα))
  have hU := (isUnitLatticeB_unit (G := Gp)).toIsUnitLattice
  have hent : ∀ p r, AnalyticAt ℂ (fun q => decCovSqrt Gp (compWeight L a₁) a₁ ν (αF q)
      (extS Gp (sF q)) (barField Gp (ΨF q) (φF q)) (unitQ Gp) (unitP Gp) p r) q := by
    intro p r
    have hg : AnalyticAt ℂ (fun e : DecData Gp N =>
        decCovSqrt Gp (compWeight L a₁) a₁ ν e.2.2 (extS Gp e.1) e.2.1 (unitQ Gp) (unitP Gp) p r)
        (sF q, (barField Gp (ΨF q) (φF q), αF q)) :=
      analyticOnNhd_decCovSqrt_entry (N := N) hC hκ hM hδ hsm hU p r _ hmem
    have hg' := hg
    exact AnalyticAt.comp (f := fun q => (sF q, (barField Gp (ΨF q) (φF q), αF q))) hg' he
  have hv : AnalyticAt ℂ (fun q => cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (αF q)
      (extS Gp (sF q)) (barField Gp (ΨF q) (φF q)) (unitQ Gp) (unitP Gp) *ᵥ ψh q)) q := by
    rw [analyticAt_pi_iff]
    intro r
    simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
    exact analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun t _ => (hent r t).mul (hψ t))
  exact analyticAt_liftC hG' hv

end Analytic

end Fan

end Balaban.Localization
