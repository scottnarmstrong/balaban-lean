/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidGaussEqConst

/-!
# The product over the fixed roots is `const^♮ e^{-𝒢^♮}`: choice of the composed weight (W942)

`notes/phase1/LF4R-PLAN.md` §8.5.  `prod_roots_eq_constNat_exp_of_inj`: the fixed roots `r` are in injective
correspondence `f` with the blocks of a set `Zb`; with `aN z := (precision of the root of z) / β_k` the product
over the roots of the composed Gaussian densities is `constNat · e^{-Re gaussNat}`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.ActionConv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.LargeField Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

open Classical in
theorem prod_roots_eq_constNat_exp_of_inj {ρ : Type*} [Fintype ρ] (Fx : ρ → Prop) (Pt : ρ → ℝ)
    (vt : ρ → EuclideanSpace ℝ (Fin N)) (G : GeneratingSet d L N₀ k ϱ) (ϖ : ℕ → ℝ)
    (Ψ : Torus d (N₀ * L ^ k) → Fin N → ℂ) {βk : ℝ} (hβ : 0 < βk)
    (ψk : Torus d (N₀ * L ^ (k - k)) → Fin N → ℂ) (Zb : Finset (Torus d (N₀ * L ^ (k - k))))
    (f : {r : ρ // Fx r} → Torus d (N₀ * L ^ (k - k))) (hf : Function.Injective f)
    (hZb : ∀ x, x ∈ Zb ↔ ∃ r, f r = x) (hPpos : ∀ r, Fx r → 0 < Pt r)
    (hreal : ∀ z ∈ Zb, ∀ i, (ψk z i - compMeanT G ϖ Ψ z i).im = 0)
    (hμ : ∀ r : {r : ρ // Fx r}, vt r.1 =
      (WithLp.toLp 2 fun i => (ψk (f r) i - compMeanT G ϖ Ψ (f r) i).re :
        EuclideanSpace ℝ (Fin N))) :
    ∃ aN : Torus d (N₀ * L ^ (k - k)) → ℝ, (∀ r : {r : ρ // Fx r}, Pt r.1 = βk * aN (f r)) ∧
      ∏ r : ρ, (if Fx r then ENNReal.ofReal (gaussDens (Pt r) (vt r)) else 1) =
        ENNReal.ofReal (constNat N βk aN Zb * Real.exp (-(gaussNat G ϖ Ψ βk aN ψk Zb).re)) := by
  let aN : Torus d (N₀ * L ^ (k - k)) → ℝ := fun x =>
    if h : ∃ r : {r : ρ // Fx r}, f r = x then Pt (Classical.choose h).1 / βk else 1
  have haN : ∀ r : {r : ρ // Fx r}, aN (f r) = Pt r.1 / βk := by
    intro r
    have h : ∃ r' : {r : ρ // Fx r}, f r' = f r := ⟨r, rfl⟩
    simp only [aN, h, dite_true]
    rw [hf (Classical.choose_spec h)]
  have hP : ∀ r : {r : ρ // Fx r}, Pt r.1 = βk * aN (f r) := by
    intro r; rw [haN r]; field_simp
  refine ⟨aN, hP, ?_⟩
  have hbij : Function.Bijective (fun r : {r : ρ // Fx r} => (⟨f r, (hZb _).mpr ⟨r, rfl⟩⟩ : ↥Zb)) := by
    refine ⟨fun r r' h => hf (congrArg Subtype.val h), fun x => ?_⟩
    obtain ⟨r, hr⟩ := (hZb x.1).mp x.2
    exact ⟨r, Subtype.ext hr⟩
  exact prod_roots_eq_constNat_exp Fx Pt vt G ϖ Ψ aN ψk Zb hreal
    (fun z hz => by
      obtain ⟨r, rfl⟩ := (hZb z).mp hz
      rw [← hP r]; exact hPpos r.1 r.2)
    (Equiv.ofBijective _ hbij) (fun r => hP r) (fun r => hμ r)

end Balaban.LargeField.ActionConv
