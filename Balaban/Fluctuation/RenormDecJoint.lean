/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormPertClass
public import Balaban.Fluctuation.RenormEndpointSharp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One cut family with all the clauses

The landed theorems `renDec_sharp`, `renDec_pertClass` and `renDec_one_unique_sharp` each return
their own family of cut solutions.  Here the family of `renDec_sharp` is taken once, and for that
one family the following hold simultaneously: analyticity on `expDom × polydisc`; the fixed-point
characterization and the sharp bounds of `renDec_sharp`; the class statement of
`renDec_pertClass`; the endpoint equality at the all-ones cut with the solution `F` of
`IsRenSol`.  The class statement and the endpoint come from the family-free cores
`renPertClass_of_sharp` and `renDec_one_unique_of_fixed'`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis Finset

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **`renDec_joint`.**  One family `Fcut` of cut solutions with: (i) analyticity on
`expDom × polydisc`; (ii) the three characterizing clauses, the sharp bounds and the vanishing at
`ξ = 0` of `renDec_sharp`; (iii) the class statement of `renDec_pertClass`; (iv) the endpoint
`Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ)`. -/
theorem renDec_joint
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {r₀ rF B cK : ℝ} (hr₀0 : 0 < r₀)
    (hr₀ : r₀ ≤ 1 / 16) (X₁ : Set (CTorus d L N₁ m₁ K))
    {F : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF : IsRenSol (N := N) Gp (compWeight L a₁) ν eps eps rF B F) (hrF : r₀ ≤ rF)
    (hD₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    (hδ₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hM2 : cK2' d L N (famConst d L BG κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀) ≤
        c6 d L N)
    (hB0 : 0 ≤ B) (hcK : 1 ≤ cK)
    (hCB : cK2' d L N (famConst d L BG κ) *
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps) ≤
        cK * cK2 d L N * B) :
    ∃ Fcut : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (RenLabel Gp X₁ → ℂ) →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
          (RenLabel Gp X₁ → ℂ) => Fcut p.1 p.2)
        (expDom Gp (XiCOneReal Gp (compWeight L a₁) ν eps) r₀ ×ˢ
          polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ)) ∧
      (∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < r₀ → ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
        ∀ (s' : DecParams Gp) (E : Edat Gp N),
          s' = extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) →
          E = renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D)
            (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D) ξ →
          (Fcut (rawOf D, ξ) s).1 = dphi Gp (decG Gp (compWeight L a₁) ν s') E.2.1 E.1
              (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (Fcut (rawOf D, ξ) s).2 ∧
          DecFixed Gp (compWeight L a₁) ν s' false E.2.1 E.1
              (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (Fcut (rawOf D, ξ) s).2 ∧
          Small Gp (Fcut (rawOf D, ξ) s).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) ∧
          Small Gp (Fcut (rawOf D, ξ) s).2 (cK2' d L N (famConst d L BG κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * ‖ξ‖)) ∧
          SupBounds Gp (Fcut (rawOf D, ξ) s).1 (cK2' d L N (famConst d L BG κ) *
            ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * ‖ξ‖)) ∧
          (ξ = 0 → (Fcut (rawOf D, ξ) s).2 = 0 ∧ (Fcut (rawOf D, ξ) s).1 = 0)) ∧
      (∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < r₀ → ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
          SupBounds Gp (Fcut (rawOf D, ξ) s).1 (cK * (cK2 d L N * (B * ‖ξ‖))) ∧
          ((Fcut (rawOf D, ξ) s).1,
            decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ)
              (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm)) D + (Fcut (rawOf D, ξ) s).2) ∈
            pertClass Gp (cK * (cK2 d L N * (B * ‖ξ‖)))
              (bgK1 d L N * (xiC1 d * eps) + cK * cK2 d L N * B * r₀ + 2) (renMassU ν ξ)) ∧
      (∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
        ‖ξ‖ < r₀ → Fcut (rawOf D, ξ) 1 = F ((D.Ψ, D.h), ξ)) := by
  classical
  obtain ⟨Fcut, han, hpt⟩ := renDec_sharp hC hr₀0 hr₀ X₁ hD₀ hδ₀ hδ₁
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  refine ⟨Fcut, han, hpt, ?_, ?_⟩
  · intro D hD ξ hξ s hs
    have hs'' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hsx : ∀ P, ‖extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) P‖ ≤ Real.exp κ :=
      fun P => (norm_extParams_lt hE1 (fun i => hs'' _) P).le
    obtain ⟨-, -, -, h4, h5, -⟩ := hpt D hD ξ hξ s hs _ _ rfl rfl
    have := renPertClass_of_sharp hC hr₀0 hr₀ hD₀ hB0 hcK hCB hD hξ hsx h4 h5
    exact ⟨this.1, this.2⟩
  · intro D hD ξ hξ
    have hs1 : ∀ P, ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ ≤ Real.exp κ := fun P => by
      simpa using Real.one_le_exp hC.hκ.le
    have hmem : (1 : RenLabel Gp X₁ → ℂ) ∈ polydisc (0 : RenLabel Gp X₁ → ℂ)
        (fun _ => Real.exp κ) := fun i => by
      simpa using Real.one_lt_exp_iff.2 hC.hκ
    have hext : extParams Gp X₁ ((1 : RenLabel Gp X₁ → ℂ) ∘ (renLabelEquiv Gp X₁).symm) =
        fun _ => 1 := by
      have h1 : (1 : RenLabel Gp X₁ → ℂ) ∘ (renLabelEquiv Gp X₁).symm = 1 := rfl
      rw [h1, extParams_one]
    obtain ⟨hU⟩ : Nonempty (InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D) :=
      ⟨renXiCOneReal_inUnionC7 hC hD⟩
    obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hU
    obtain ⟨φ, α, hI, hu, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
      (s := fun _ => 1) hs1 hδ0 hδε hε hδc hνε hDC
    obtain ⟨e1, e2⟩ := decBg_eq hI hu
    obtain ⟨h1, h2, h3, h4, -⟩ := hpt D hD ξ hξ 1 hmem (fun _ => 1) _ hext.symm rfl
    rw [e1, e2] at h1 h2
    have hb : 0 ≤ (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps := by
      have := renMassStar_nonneg hC
      have := hC.eps_pos
      positivity
    have hK2 : cK2' d L N (famConst d L BG κ) *
        ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * ‖ξ‖) ≤
        cK2' d L N (famConst d L BG κ) *
        ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hξ.le hb) ?_
      have hd0 : 0 < d := by have := hC.HBp.hd; omega
      have := famConst_ge_one (d := d) (L := L) hC.hS.fam.2.1 κ hd0
      exact cK2'_nonneg (d := d) (L := L) (N := N) (B := famConst d L BG κ) (by linarith)
    have key := renDec_one_unique_of_fixed' hC hF hr₀ hrF hD₀ hδ₀ hδ₁ hD hξ hI h2
      (δα := (Fcut (rawOf D, ξ) 1).2) h3 (h4.mono (hK2.trans hM2))
    exact Prod.ext (h1.trans key.1) key.2

end Balaban.Localization
