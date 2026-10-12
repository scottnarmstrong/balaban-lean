/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5FluctFacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The composite function of Lemma DL with the fluctuation, as an analytic function of `(Θ, ψ', s)`

`fan_analytic_fl`: (AE1), the joint analyticity of
`F(s; Θ, ψ') = 𝓔(X; ψ(𝔹_j(X), 𝔹_k(X); ψ(𝔹_k(X), 𝔹_{k+1}; Θ, s) + δψ(𝔹_k(X), 𝔹_k; ψ', s)))`
on `Ξ^c_K(𝔹_{k+1}; 1, ε') × FlBallLC × {|s_P| < e^κ}` (`ψ'` layer-constant with `|ψ'| < δ₁`);
`fan_bound_fl`: its bound.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix

section Fan

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

variable (Gp Hm δ₁) in
/-- **The set of fluctuations** `{ψ' : |ψ'| < δ₁ on the data sites of H⁻}`. -/
def FlBall : Set (CTorus d L N₁ m₁ K → Fin N → ℂ) :=
  {ψ' | ∀ x ∈ dataSites Hm, vn (ψ' x) < δ₁}

variable (Hm δ₁) in
/-- **The ball of block fluctuations** (P3 (4.17)): the fluctuations `ψ'` of the source are fields
of the lattice of `𝔹_k`; their lifts to the fine lattice are the fields constant on the blocks of
every layer of `H⁻ = 𝔹_k` (`IsLayerConstant`).  `FlBallLC` is the set of these with `|ψ'| < δ₁` on
the data sites of `H⁻`. -/
def FlBallLC : Set (CTorus d L N₁ m₁ K → Fin N → ℂ) :=
  {ψ' | ψ' ∈ FlBall Hm δ₁ ∧ IsLayerConstant Hm ψ'}

theorem isLayerConstant_line {z w : CTorus d L N₁ m₁ K → Fin N → ℂ} (hz : IsLayerConstant Hm z)
    (hw : IsLayerConstant Hm w) (τ : ℂ) : IsLayerConstant Hm (z + τ • w) := by
  intro m h1 h2 x hx x' hx'
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [hz m h1 h2 x hx x' hx', hw m h1 h2 x hx x' hx']

theorem isLayerConstant_smul {z : CTorus d L N₁ m₁ K → Fin N → ℂ} (hz : IsLayerConstant Hm z)
    (c : ℂ) : IsLayerConstant Hm (c • z) := by
  intro m h1 h2 x hx x' hx'
  simp only [Pi.smul_apply]
  rw [hz m h1 h2 x hx x' hx']

theorem analyticAt_barField {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q : Q}
    (φ : Q → Gp.Ω 1 × Fin N → ℂ) (Ψ : Q → CTorus d L N₁ m₁ K → Fin N → ℂ)
    (hφ : ∀ r, AnalyticAt ℂ (fun q => φ q r) q)
    (hΨ : ∀ y j, AnalyticAt ℂ (fun q => Ψ q y j) q) :
    AnalyticAt ℂ (fun q => barField Gp (Ψ q) (φ q)) q := by
  classical
  refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
  by_cases hx : x ∈ Gp.Ω 1
  · simp only [barField, hx, ↓reduceDIte]
    exact hφ _
  · simp only [barField, hx, ↓reduceDIte]
    exact hΨ x i

theorem analyticAt_flAlpha {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q : Q}
    (α : Q → Gp.Ω 1 → ℂ) (hα : ∀ y, AnalyticAt ℂ (fun q => α q y) q) :
    AnalyticAt ℂ (fun q => flAlpha Gp Hm (α q)) q := by
  classical
  refine analyticAt_pi_iff.2 fun y => ?_
  by_cases hy : (y : CTorus d L N₁ m₁ K) ∈ Gp.Ω 1
  · simp only [flAlpha, hy, ↓reduceDIte]
    exact hα _
  · simp only [flAlpha, hy, ↓reduceDIte]
    exact analyticAt_const

theorem analyticAt_D2raw {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q] {q0 : Q}
    (a : ℕ → ℝ) (Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (U : Q → RawData d L (N₁ * L ^ m₁) K N) (hU : AnalyticAt ℂ U q0)
    (hFU : AnalyticAt ℂ (fun q => Fk (U q)) q0) :
    AnalyticAt ℂ (fun q => D2raw Gk Gj a Fk (U q)) q0 :=
  analyticAt_compRaw (G := Gj) (G' := Gk) a (fun q => Fk (U q)) hFU U hU

variable (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
  (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
include hB hF

/-- **Lemma DL, analyticity (AE1), with the fluctuation.** -/
theorem fan_analytic_fl
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
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {E : RawData d L (N₁ * L ^ m₁) K N → ℂ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl))) :
    AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
        (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
      E (D2raw Gk Gj (compWeight L a₁) Fk (D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2) p.1)))
      ((XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBallLC Hm δ₁) ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ)) := by
  classical
  rintro ⟨⟨u, ψ'⟩, s⟩ ⟨⟨⟨D, hD, rfl⟩, hψ, hψc⟩, hs⟩
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hB.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  obtain ⟨φ, α, δφ, hI, hFeq, hstrict, hδφ, hX3, hrawD, hD2, hX2⟩ :=
    point_facts_fl hB hF hF₁ hFk hSol hsx hs1 hD hψ hψc
  set pt : (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) := ((rawOf D, ψ'), s) with hpt
  set g0 : (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) →
      DecParams Gp × RawData d L (N₁ * L ^ m₁) K N :=
    fun p => (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2, p.1.1) with hg0
  have hext : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
      (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
      extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2) pt :=
    (analyticAt_extParams s).comp_of_eq analyticAt_snd rfl
  have ha0 : AnalyticAt ℂ g0 pt := hext.prod (analyticAt_fst.comp analyticAt_fst)
  have hU : InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D := by
    have hd0 : 0 < d := by have := hB.HBp.hd; omega
    have hc1 := one_le_xiC1 d
    have hε := hB.num.eps_pos
    have hδ0 : 0 < xiC1 d * eps := by positivity
    exact inUnionDomainC_of_inDomainC hB.HBp hδ0
      (hB.num.c7le.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))) hB.num.c7le
      (xiCData_inDomainC hB.HBp hB.num.small1 hD)
  have ha1 : AnalyticAt ℂ (fun p => F₁ (g0 p)) pt :=
    (hF₁an (g0 pt) ⟨hsx, D, hU, rfl⟩).comp_of_eq ha0 rfl
  have hφ1 : ∀ r, AnalyticAt ℂ (fun p => (F₁ (g0 p)).1 r) pt := fun r =>
    analyticAt_pi_iff.1 (analyticAt_fst.comp ha1) r
  have hα1 : ∀ y, AnalyticAt ℂ (fun p => (F₁ (g0 p)).2 y) pt := fun y =>
    analyticAt_pi_iff.1 (analyticAt_snd.comp ha1) y
  have hΨ1 : ∀ y jj, AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
      (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
      p.1.1.1 y jj) pt := fun y jj =>
    (analyticAt_rawΨ y jj (rawOf D)).comp_of_eq (analyticAt_fst.comp analyticAt_fst) rfl
  have hψ1 : ∀ y jj, AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
      (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
      p.1.2 y jj) pt := by
    intro y jj
    have h0 : AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
        (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
        p.1.2) pt := analyticAt_snd.comp analyticAt_fst
    exact analyticAt_pi_iff.1 (analyticAt_pi_iff.1 h0 y) jj
  -- the data of the fluctuation problem
  set ed : (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) → Edat Hm N :=
    fun p => flEdat Gp Hm (F₁ (g0 p)) p.1.1.1 p.1.2 with hed
  have haed : AnalyticAt ℂ ed pt := by
    refine AnalyticAt.prod (analyticAt_barField (fun p => (F₁ (g0 p)).1) (fun p => p.1.1.1) hφ1
      hΨ1) (AnalyticAt.prod (analyticAt_flAlpha (fun p => (F₁ (g0 p)).2) hα1)
      (AnalyticAt.prod (analyticAt_snd.comp analyticAt_fst) analyticAt_const))
  have hSolpt : AnalyticAt ℂ (fun p => Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2,
      ed p)) pt := by
    refine (hSolan (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, ed pt)
      ⟨hsx, ?_⟩).comp_of_eq (hext.prod haed) rfl
    have : ed pt = flEdat Gp Hm (φ, α) D.Ψ ψ' := by
      show flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D)) D.Ψ ψ' = _
      rw [hFeq]
    rw [this]; exact hstrict
  have hSolr : ∀ r, AnalyticAt ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N ×
      (CTorus d L N₁ m₁ K → Fin N → ℂ)) × (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2, ed p)).1 r) pt := fun r =>
    analyticAt_pi_iff.1 (analyticAt_fst.comp hSolpt) r
  have ha2 : AnalyticAt ℂ (fun p => D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2) p.1) pt := by
    classical
    refine AnalyticAt.prod (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
      (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
    · have hA := analyticAt_composeField (G := Gk) (G' := Gp) (q := pt) (compWeight L a₁)
        (fun p => (F₁ (g0 p)).1) (fun p => p.1.1.1) hφ1 hΨ1 x i
      have hA' := analyticAt_composeField (G := Gk) (G' := Hm) (q := pt) (compWeight L a₁)
        (fun p : (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) ×
          (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) =>
          (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2, ed p)).1)
        (fun p => p.1.2) hSolr hψ1 x i
      exact hA.add hA'
    · by_cases hx : x ∈ Gk.Ω 1
      · simp only [hx, ↓reduceIte]
        exact (analyticAt_rawh x i (rawOf D)).comp_of_eq (analyticAt_fst.comp analyticAt_fst) rfl
      · simp only [hx, ↓reduceIte]
        exact analyticAt_const
  have hUk := xiCData_unionC hX3
  have hmem : D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) (rawOf D, ψ') ∈
      {p : RawData d L (N₁ * L ^ m₁) K N | ∃ D : BgData Gk N,
        InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)} := by
    rw [hrawD]
    exact ⟨_, hUk, rfl⟩
  have ha3 : AnalyticAt ℂ (fun p => Fk (D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2) p.1)) pt :=
    (hFkan _ hmem).comp_of_eq ha2 rfl
  have ha4 : AnalyticAt ℂ (fun p => D2raw Gk Gj (compWeight L a₁) Fk
      (D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) p.2) p.1)) pt :=
    analyticAt_D2raw (Gj := Gj) (compWeight L a₁) Fk _ ha2 ha3
  refine (hE _ ?_).comp_of_eq ha4 rfl
  show D2raw Gk Gj (compWeight L a₁) Fk (D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol
    (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) (rawOf D, ψ')) ∈ _
  rw [hrawD, hD2]
  exact ⟨_, hX2, rfl⟩

/-- **Lemma DL, the bound, with the fluctuation.** -/
theorem fan_bound_fl
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {E : RawData d L (N₁ * L ^ m₁) K N → ℂ} {B : ℝ}
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j (scaledC0 d)
      (scaledC0 d ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ‖E r‖ ≤ B)
    {u : RawData d L (N₁ * L ^ m₁) K N} (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps)
    {ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ} (hψ : ψ' ∈ FlBallLC Hm δ₁)
    {s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ}
    (hs : s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ)
      (fun _ => Real.exp κ)) :
    ‖E (D2raw Gk Gj (compWeight L a₁) Fk (D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) (u, ψ')))‖ ≤ B := by
  classical
  obtain ⟨D, hD, rfl⟩ := hu
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hB.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  obtain ⟨φ, α, δφ, hI, hFeq, hstrict, hδφ, hX3, hrawD, hD2, hX2⟩ :=
    point_facts_fl hB hF hF₁ hFk hSol hsx (extParams_hs1 (X₁f := X₁f) (Gp := Gp) s) hD hψ.1 hψ.2
  rw [hrawD, hD2]
  exact hEb _ ⟨_, hX2, rfl⟩

end Fan

end Balaban.Localization
