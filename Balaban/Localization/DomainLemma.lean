/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Fan
public import Balaban.Localization.DecoupledCompose
public import Balaban.Background.Def5
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma DL (the domain lemma), background part (LOCALIZATION.md §4.3)

For `Θ ∈ Ξ^c_K(𝔹_{k+1}; 1, ε')` and every decoupling vector `s` with `|s_P| < e^{κ₁}` the argument
of `𝓔` in `𝒯(s; Θ)` lies in `Ξ^c_j(𝔹_j(X); C₀, ε₂)` (`point_facts`), so `𝒯` is defined; it is
jointly analytic in `(Θ, s)` (`fan_analytic`) and bounded by the bound of `𝓔` (`fan_bound`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix

section DL

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}

/-- If `P` is not a parameter cube then `s_P = 1`. -/
theorem extParams_hs1 (s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ)
    (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx Gp) (hPn : P ∉ parCubes Gp X₁f) :
    extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s ⟨P, hP⟩ = 1 := by
  classical
  apply extParams_nonpar
  intro hdisj
  apply hPn
  unfold parCubes
  rw [Finset.mem_filter]
  refine ⟨hP, fun hsub => ?_⟩
  have hmem : P.2 ∈ cubeP P := mem_cubeP.2 (SameCell.refl _ _)
  exact Set.disjoint_left.1 hdisj (self_mem_Pset P) (Finset.mem_coe.2 (hsub hmem))

theorem analyticAt_compRaw {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁} {Q : Type*} [NormedAddCommGroup Q]
    [NormedSpace ℂ Q] {q0 : Q} (a : ℕ → ℝ)
    (F : Q → (G'.Ω 1 × Fin N → ℂ) × (G'.Ω 1 → ℂ)) (hF : AnalyticAt ℂ F q0)
    (U : Q → RawData d L (N₁ * L ^ m₁) K N) (hU : AnalyticAt ℂ U q0) :
    AnalyticAt ℂ (fun q => ((fun x i => composeField G G' a (F q).1 (U q).1 x i,
      fun x i => by classical exact if x ∈ G.Ω 1 then (U q).2 x i else 0) :
        RawData d L (N₁ * L ^ m₁) K N)) q0 := by
  classical
  refine AnalyticAt.prod (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
    (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
  · refine analyticAt_composeField (G := G) (G' := G') (Q := Q) a (fun q => (F q).1)
      (fun q => (U q).1) (fun r => ?_) (fun y jj => ?_) x i
    · exact analyticAt_pi_iff.1 (analyticAt_fst.comp hF) r
    · exact (analyticAt_rawΨ y jj (U q0)).comp_of_eq hU rfl
  · by_cases hx : x ∈ G.Ω 1
    · simp only [hx, ↓reduceIte]
      exact (analyticAt_rawh x i (U q0)).comp_of_eq hU rfl
    · simp only [hx, ↓reduceIte]
      exact analyticAt_const

variable (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
include hB

/-- **Lemma DL, analyticity (AE1).** -/
theorem fan_analytic
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃))) :
    AnalyticOnNhd ℂ (fun p : RawData d L (N₁ * L ^ m₁) K N ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
      E (D2raw Gk Gj (compWeight L a₁) Fk (D1raw Gp Gk (compWeight L a₁) F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2, p.1))))
      (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ)) := by
  classical
  rintro ⟨u, s⟩ ⟨⟨D, hD, rfl⟩, hs⟩
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hB.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  obtain ⟨φ, α, hI, hFeq, hst, hD1, hD2, hX2⟩ := point_facts hB hF₁ hFk hsx hs1 hD
  -- the maps
  set g0 : RawData d L (N₁ * L ^ m₁) K N × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) →
      DecParams Gp × RawData d L (N₁ * L ^ m₁) K N :=
    fun p => (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2, p.1) with hg0
  have ha0 : AnalyticAt ℂ g0 (rawOf D, s) :=
    ((analyticAt_extParams s).comp_of_eq analyticAt_snd rfl).prod analyticAt_fst
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D := by
    have hd0 : 0 < d := by have := hB.HBp.hd; omega
    have hc1 := one_le_xiC1 d
    have hε := hB.num.eps_pos
    have hδ0 : 0 < xiC1 d * eps := by positivity
    exact inUnionDomainC_of_inDomainC hB.HBp hδ0
      (hB.num.c7le.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hB.num.c7le
      (xiCData_inDomainC hB.HBp hB.num.small1 hD)
  have ha1 : AnalyticAt ℂ (fun p => F₁ (g0 p)) (rawOf D, s) :=
    (hF₁an (g0 (rawOf D, s)) ⟨hsx, D, hU, rfl⟩).comp_of_eq ha0 rfl
  have ha2 : AnalyticAt ℂ (fun p => D1raw Gp Gk (compWeight L a₁) F₁ (g0 p)) (rawOf D, s) :=
    analyticAt_compRaw (G := Gk) (G' := Gp) (compWeight L a₁) (fun p => F₁ (g0 p)) ha1
      (fun p => (g0 p).2) (analyticAt_snd.comp_of_eq ha0 rfl)
  have hUk := xiCData_unionC hst
  have ha3 : AnalyticAt ℂ (fun p => Fk (D1raw Gp Gk (compWeight L a₁) F₁ (g0 p)))
      (rawOf D, s) := by
    refine (hFkan _ ?_).comp_of_eq ha2 rfl
    refine ⟨_, hUk, ?_⟩
    have : D1raw Gp Gk (compWeight L a₁) F₁ (g0 (rawOf D, s)) = _ := hD1
    rw [this]; rfl
  have ha4 : AnalyticAt ℂ (fun p => D2raw Gk Gj (compWeight L a₁) Fk
      (D1raw Gp Gk (compWeight L a₁) F₁ (g0 p))) (rawOf D, s) :=
    analyticAt_compRaw (G := Gj) (G' := Gk) (compWeight L a₁)
      (fun p => Fk (D1raw Gp Gk (compWeight L a₁) F₁ (g0 p))) ha3
      (fun p => D1raw Gp Gk (compWeight L a₁) F₁ (g0 p)) ha2
  refine (hE _ ?_).comp_of_eq ha4 rfl
  show D2raw Gk Gj (compWeight L a₁) Fk (D1raw Gp Gk (compWeight L a₁) F₁ (g0 (rawOf D, s))) ∈ _
  have e : D1raw Gp Gk (compWeight L a₁) F₁ (g0 (rawOf D, s)) = _ := hD1
  rw [e, hD2]
  exact ⟨_, hX2, rfl⟩

/-- **Lemma DL, the bound.** -/
theorem fan_bound
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) K N → ℂ} {B : ℝ}
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃), ‖E r‖ ≤ B)
    {u : RawData d L (N₁ * L ^ m₁) K N} (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps)
    {s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ}
    (hs : s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ)
      (fun _ => Real.exp κ)) :
    ‖E (D2raw Gk Gj (compWeight L a₁) Fk (D1raw Gp Gk (compWeight L a₁) F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u)))‖ ≤ B := by
  classical
  obtain ⟨D, hD, rfl⟩ := hu
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hB.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  obtain ⟨φ, α, hI, hFeq, hst, hD1, hD2, hX2⟩ :=
    point_facts hB hF₁ hFk hsx (extParams_hs1 (X₁f := X₁f) (Gp := Gp) s) hD
  rw [hD1, hD2]
  exact hEb _ ⟨_, hX2, rfl⟩

end DL

end Balaban.Localization
