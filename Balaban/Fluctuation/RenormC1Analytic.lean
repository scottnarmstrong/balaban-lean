/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormDomainParams
public import Balaban.Fluctuation.RenormExpG
public import Balaban.Localization.DecoupledBackground
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The cut functional of the `C₁` density and its joint analyticity

`locC1` itself is NOT proved here.  This file is the zero class of the localization of `locC1`:
it defines the cut functional and proves its value at the uncut parameters and its joint
analyticity.  The statements do not depend on the choice of the generating set beyond the
hypotheses stated.

**The cut functional** `renC1Cut`.  For a datum `D`, a vector `ξ` and a vector `s` of cut
parameters indexed by the labels of the renormalization cover, `A₁((D, ξ), s)` is the density
`renC1On` at the data `(D.Ψ, D.h)` and at the decoupled background `decBgField` whose cut
parameters are the extension `extParams` of `s` (composed with the identification
`renLabelEquiv` of the labels with the free parameters).

**Value at `s = 1`** (`renC1Cut_one`): the decoupled background at `s ≡ 1` is the true
background `bgFieldC` (`i4b_one`), so `A₁((D, ξ), 1)` is `renC1On` at the true background.

**Joint analyticity** (`renC1Cut_analytic`).  There is a function `F` of the raw datum, `ξ` and `s`
that is analytic *at every point of* `expDom × polydisc` as a function on the ambient normed
space `RawData × ℂ³ × ℂ^labels` (the sense of `AnalyticOnNhd` that `HasLocPrinciple` and
`renLoc_localization_expansion_fin` use; the set itself is not required to be open), and equals
`renC1Cut` there.  `F` is built from the analytic family of `i4b_analytic` (a function of the raw
datum on all of `DecParams × RawData`), so it is a function of the raw datum `(D.Ψ, D.h)`; the
relation with the datum is `F (rawOf D, ξ) s = renC1Cut D ξ s`.  All hypotheses of
`i4b_analytic` (`DecSpecs`, `DGSetting`, `BgHyp`, `κ > 0`, the `hM` margin) and the union-domain
membership of the datum come from `FlCore` (`renXiCOneReal_inUnionC7`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis Finset

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}

section Def

variable (Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν εζ ρ : ℝ)
  (X₁ : Set (CTorus d L N₁ m₁ K)) (B : Finset (Torus d (N₁ * L ^ m₁ * L ^ K)))

/-- **The cut functional** `A₁((D, ξ), s)`: the density `C₁(B)` at the data `(D.Ψ, D.h)` and the
decoupled background whose cut parameters are the extension of `s` (a vector indexed by the labels
of the cover) to all cubes by `1`. -/
noncomputable def renC1Cut (D : BgData Gp N) (ξ : Fin 3 → ℂ) (s : RenLabel Gp X₁ → ℂ) : ℂ :=
  renC1On Gp a ν εζ B D.Ψ D.h
    (decBgField Gp a ν ρ (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm)) D) ξ

end Def

section Facts

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- For `s` in the open polydisc and a datum of the union domain, the decoupled background exists
and `decBgField` is its field. -/
theorem exists_decBg
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {D : BgData Gp N}
    (hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D) {s : DecParams Gp}
    (hs : ∀ P, ‖s P‖ < Real.exp κ) :
    ∃ (φ : Gp.Ω 1 × Fin N → ℂ) (α : Gp.Ω 1 → ℂ),
      IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α ∧
      decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D = φ := by
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hU
  obtain ⟨φ, α, hI, hu, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hs P).le) hδ0 hδε hε hδc hνε hDC
  exact ⟨φ, α, hI, (decBg_eq hI hu).1⟩

variable (a₁ ν eps) in
/-- **Value at `s = 1`.**  The cut functional at the all-ones vector is `C₁(B)` at the true
background `bgFieldC`. -/
theorem renC1Cut_one
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {D : BgData Gp N}
    (hD : XiCOneReal Gp (compWeight L a₁) ν eps D) (X₁ : Set (CTorus d L N₁ m₁ K))
    (B : Finset (Torus d (N₁ * L ^ m₁ * L ^ K))) (ξ : Fin 3 → ℂ) :
    renC1Cut Gp (compWeight L a₁) ν eps (rho4 d L N BG κ) X₁ B D ξ 1 =
      renC1On Gp (compWeight L a₁) ν eps B D.Ψ D.h
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D) ξ := by
  have hU := renXiCOneReal_inUnionC7 hC hD
  have hs : ∀ P, ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ := fun P => by
    simpa using Real.one_lt_exp_iff.2 hC.hκ
  obtain ⟨φ, α, hI, hF⟩ := exists_decBg hC hU hs
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hU
  obtain ⟨-, hb, -⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 hδε hε hδc hνε hDC hI
  unfold renC1Cut
  have h1 : (1 : RenLabel Gp X₁ → ℂ) ∘ (renLabelEquiv Gp X₁).symm = 1 := rfl
  rw [h1, extParams_one, hF, hb]

/-- Reindexing a vector of labels by `renLabelEquiv.symm` is analytic. -/
theorem analyticAt_reindex (X₁ : Set (CTorus d L N₁ m₁ K))
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q : Q}
    (t : Q → RenLabel Gp X₁ → ℂ) (ht : ∀ i, AnalyticAt ℂ (fun q => t q i) q) :
    AnalyticAt ℂ (fun q => t q ∘ (renLabelEquiv Gp X₁).symm) q :=
  analyticAt_pi_iff.2 fun _ => ht _

/-- **Joint analyticity of the cut functional** (`HasLocPrinciple`'s sense: ambient analyticity at
every point of the set `expDom × polydisc`, which is not required to be open).  There is a function
`F` of the raw datum, `ξ` and the cut vector `s`, analytic at each point of
`expDom G (XiCOneReal …) r₀ ×ˢ {s | ‖s_i‖ < e^κ}`, with `F (rawOf D, ξ) s = renC1Cut D ξ s`
for the data of `XiCOneReal`, `‖ξ‖ < r₀`, `‖s_i‖ < e^κ`.  The hypotheses of `i4b_analytic` come
from `FlCore`. -/
theorem renC1Cut_analytic
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (r₀ : ℝ)
    (X₁ : Set (CTorus d L N₁ m₁ K)) (B : Finset (Torus d (N₁ * L ^ m₁ * L ^ K))) :
    ∃ F : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (RenLabel Gp X₁ → ℂ) → ℂ,
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
          (RenLabel Gp X₁ → ℂ) => F p.1 p.2)
        (expDom Gp (XiCOneReal Gp (compWeight L a₁) ν eps) r₀ ×ˢ
          polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ)) ∧
      ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
        ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
          F (rawOf D, ξ) s =
            renC1Cut Gp (compWeight L a₁) ν eps (rho4 d L N BG κ) X₁ B D ξ s := by
  classical
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic (N := N) hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  refine ⟨fun u s => renC1On Gp (compWeight L a₁) ν eps B u.1.1 u.1.2
    (F₁ (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm), u.1)).1 u.2, ?_, ?_⟩
  · rintro ⟨u, s⟩ ⟨⟨D, hD, hu1, hu2⟩, hs⟩
    have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hU := renXiCOneReal_inUnionC7 hC hD
    have hsx : ∀ P, ‖extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) P‖ < Real.exp κ :=
      norm_extParams_lt hE1 (fun i => hs' _)
    set g : ((RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) × (RenLabel Gp X₁ → ℂ)) →
        DecParams Gp × RawData d L (N₁ * L ^ m₁) K N :=
      fun p => (extParams Gp X₁ (p.2 ∘ (renLabelEquiv Gp X₁).symm), p.1.1) with hg
    have hs2 : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.2 ∘ (renLabelEquiv Gp X₁).symm) (u, s) :=
      analyticAt_reindex (Gp := Gp) X₁
        (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) × (RenLabel Gp X₁ → ℂ) => p.2) fun i =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : RenLabel Gp X₁ => ℂ) i).analyticAt _
          |>.comp_of_eq analyticAt_snd rfl
    have hg0 : AnalyticAt ℂ g (u, s) :=
      ((analyticAt_extParams _).comp_of_eq hs2 rfl).prod (analyticAt_fst.comp analyticAt_fst)
    have hF1 : AnalyticAt ℂ (fun p => F₁ (g p)) (u, s) :=
      (hF₁an (g (u, s)) ⟨hsx, D, hU, by rw [hg]; exact hu1⟩).comp_of_eq hg0 rfl
    have hF1' : ∀ (y : Gp.Ω 1) i, AnalyticAt ℂ (fun p => (F₁ (g p)).1 (y, i)) (u, s) :=
      fun y i => (analyticAt_pi_iff.1 (analyticAt_fst.comp hF1) (y, i))
    have aP : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.1) (u, s) := analyticAt_fst.comp analyticAt_fst
    have aΨ : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.1.1) (u, s) := analyticAt_fst.comp aP
    have ah : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.1.2) (u, s) := analyticAt_snd.comp aP
    have aξ : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.2) (u, s) := analyticAt_snd.comp analyticAt_fst
    have hΨ : ∀ x i, AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.1.1 x i) (u, s) := fun x i =>
      analyticAt_pi_iff.1 (analyticAt_pi_iff.1 aΨ x) i
    have hh : ∀ x i, AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.1.2 x i) (u, s) := fun x i =>
      analyticAt_pi_iff.1 (analyticAt_pi_iff.1 ah x) i
    have hξ : ∀ j, AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp X₁ → ℂ) => p.1.2 j) (u, s) := fun j => analyticAt_pi_iff.1 aξ j
    exact an_renC1On (a := compWeight L a₁) ν eps B _ _ _ _ hΨ hh hF1' hξ
  · intro D hD ξ s hs
    have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hU := renXiCOneReal_inUnionC7 hC hD
    have hsx : ∀ P, ‖extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) P‖ < Real.exp κ :=
      norm_extParams_lt hE1 (fun i => hs' _)
    obtain ⟨φ, α, hI, hF⟩ := exists_decBg hC hU hsx
    have := hF₁ _ D hsx hU φ α hI
    unfold renC1Cut
    show renC1On Gp (compWeight L a₁) ν eps B D.Ψ D.h
      (F₁ (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm), (D.Ψ, D.h))).1 ξ = _
    rw [this, hF]

end Facts

section Instance

/-- **Non-vacuity at the landed pair of levels** (`d = L = 3`, `N₁ = 9`, `K = 2`, `X₁` the whole
torus, `a₁ = 1`, `ν = 0`).  `FlCore` holds, a datum of `XiCOneReal` exists, and for every block
`B` and radius `r₀` the conclusions of `renC1Cut_analytic` and `renC1Cut_one` hold.  The label
type is empty at this level, so the polydisc is a single point and the cut functional does not
depend on `s`; a setting with a nonempty label type needs a proper `X₁`, for instance the root
block of `levelLocalCover` in a torus with enough cells. -/
theorem renC1Cut_levelPair (N : ℕ) (hN : 0 < N) :
    ∃ (m₁ : ℕ) (ϱ BG κ eps : ℝ) (D : BgData (LevelPair.Gp m₁ ϱ) N),
      XiCOneReal (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 eps D ∧
      IsEmpty (RenLabel (LevelPair.Gp m₁ ϱ)
        (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))) ∧
      ∀ (r₀ : ℝ) (B : Finset (Torus 3 (9 * 3 ^ m₁ * 3 ^ 2))),
        (∃ F : RawData 3 3 (9 * 3 ^ m₁) 2 N × (Fin 3 → ℂ) →
            (RenLabel (LevelPair.Gp m₁ ϱ)
              (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) → ℂ) → ℂ,
          AnalyticOnNhd ℂ (fun p : (RawData 3 3 (9 * 3 ^ m₁) 2 N × (Fin 3 → ℂ)) ×
              (RenLabel (LevelPair.Gp m₁ ϱ)
                (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) → ℂ) =>
              F p.1 p.2)
            (expDom (LevelPair.Gp m₁ ϱ) (XiCOneReal (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 eps)
                r₀ ×ˢ polydisc (0 : RenLabel (LevelPair.Gp m₁ ϱ)
                  (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) → ℂ)
                  (fun _ => Real.exp κ)) ∧
          ∀ D : BgData (LevelPair.Gp m₁ ϱ) N,
            XiCOneReal (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 eps D → ∀ ξ : Fin 3 → ℂ,
            ∀ s ∈ polydisc (0 : RenLabel (LevelPair.Gp m₁ ϱ)
                  (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) → ℂ)
                  (fun _ => Real.exp κ),
              F (rawOf D, ξ) s = renC1Cut (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 eps
                (rho4 3 3 N BG κ) (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) :
                  Set (CTorus 3 3 9 m₁ 2)) B D ξ s) ∧
        ∀ ξ : Fin 3 → ℂ,
          renC1Cut (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 eps (rho4 3 3 N BG κ)
              (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) B D ξ 1 =
            renC1On (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 eps B D.Ψ D.h
              (bgFieldC (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 (bgC0 3 3 N) D) ξ := by
  obtain ⟨m₁, ϱ, c, BG, κ, eps, c₂, BG₂, δ₁, κdec, κ₀, hC, -, -, hH, -, -, hS, hX1, -⟩ :=
    LevelPair.interaction_levelPair_witness N
  have hε : 0 < eps := hC.eps_pos
  obtain ⟨D, hD⟩ := Balaban.Inhabited.exists_xiCOneReal hH (LevelPair.Gp m₁ ϱ) hN
    (by simp) hε
  have hemp : IsEmpty (RenLabel (LevelPair.Gp m₁ ϱ)
      (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))) := by
    refine ⟨fun q => ?_⟩
    exact Set.disjoint_left.1 q.2.2 (self_mem_Pset q.1) (Finset.mem_coe.2 (Finset.mem_univ _))
  exact ⟨m₁, ϱ, BG, κ, eps, D, hD, hemp, fun r₀ B =>
    ⟨renC1Cut_analytic hC r₀ _ B, fun ξ => renC1Cut_one 1 0 eps hC hD _ B ξ⟩⟩

end Instance

end Balaban.Localization
