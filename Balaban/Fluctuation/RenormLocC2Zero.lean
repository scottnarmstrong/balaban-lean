/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormC2Local
public import Balaban.Fluctuation.RenormDecJoint
public import Balaban.Fluctuation.RenormLocC1Zero

/-!
# The localization expansions of `C₂` and `δφ` at the zero class

The principles `locC2` (at a block root) and `locDφ` (at a site root) of the record
`RenormExpInput`, with `K_loc = 1`, from `renLoc_localization_expansion_fin` applied to the cut
family of `renDec_joint`.  The skeleton shared with `renLocC1_zero_at` is the lemma
`renLocCut_principle`; the two fields supply the cut functional, its locality, and its bounds.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis Finset

open LocalCover

section Skeleton

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- **The skeleton of the localization principle for a cut functional.**  Let `Fc` be a cut
functional analytic on `expDom × polydisc`, local for the agreement `RenC1Ag`, bounded by `Eb₀`
on the whole domain, bounded by any class-wide bound `M` at fixed `ξ`, and with value at `s = 1`
the constituent `f D (u D ξ) ξ`.  Then `HasLocPrinciple` holds with `K_loc = 1`, the cover `renYs`
and the size `renDY`, at a root with the cover facts of `renLoc_fin_domains`. -/
theorem renLocCut_principle {Dom : BgData Gp N → Prop} {m₀ j : ℕ}
    {X 𝒦X : Set (CTorus d L N₁ m₁ K)} (hcov : CovSetup Gp m₀ j X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hmem : ∀ i, renCube Gp (X1 Gp m₀ j 𝒦X) i ∈ cubeIdx Gp)
    (hinj : Function.Injective (renCube Gp (X1 Gp m₀ j 𝒦X)))
    (hdisj : ∀ i, Disjoint (Pset m₁ (renCube Gp (X1 Gp m₀ j 𝒦X) i)) (X1 Gp m₀ j 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0) {κ κd κ₀ κa : ℝ} (hκ₀ : 0 ≤ κ₀) (hκd : 3 * κ₀ + 3 ≤ κd)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κd ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hout : κa ≤ 2 * κd) {r₀ Eb₀ : ℝ} (hEb₀ : 0 ≤ Eb₀)
    {Fc : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) →
      (RenLabel Gp (X1 Gp m₀ j 𝒦X) → ℂ) → ℂ}
    (hana : AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
        (RenLabel Gp (X1 Gp m₀ j 𝒦X) → ℂ) => Fc p.1 p.2)
      (expDom Gp Dom r₀ ×ˢ polydisc (0 : RenLabel Gp (X1 Gp m₀ j 𝒦X) → ℂ)
        (fun _ => Real.exp κ)))
    (hlocD : LocalityAEOn (Real.exp κ) {u : BgData Gp N × (Fin 3 → ℂ) | Dom u.1 ∧ ‖u.2‖ < r₀}
      (fun i => Pset m₁ (renCube Gp (X1 Gp m₀ j 𝒦X) i))
      (compY (renCube Gp (X1 Gp m₀ j 𝒦X)) (X1 Gp m₀ j 𝒦X))
      (RenC1Ag (renCube Gp (X1 Gp m₀ j 𝒦X)) (X1 Gp m₀ j 𝒦X))
      (fun u s => Fc (rawOf u.1, u.2) s))
    (hbd₀ : ∀ D : BgData Gp N, Dom D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r₀ →
      ∀ s ∈ polydisc (0 : RenLabel Gp (X1 Gp m₀ j 𝒦X) → ℂ) (fun _ => Real.exp κ),
        ‖Fc (rawOf D, ξ) s‖ ≤ Eb₀)
    {U : Type*} {Kcl : BgData Gp N → (Fin 3 → ℂ) → Set U}
    {f : BgData Gp N → U → (Fin 3 → ℂ) → ℂ} {u : BgData Gp N → (Fin 3 → ℂ) → U}
    (hone : ∀ D : BgData Gp N, Dom D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r₀ →
      Fc (rawOf D, ξ) 1 = f D (u D ξ) ξ)
    (hbdM : ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r₀ → ∀ M : ℝ,
      (∀ D : BgData Gp N, Dom D → ∀ v ∈ Kcl D ξ, ‖f D v ξ‖ ≤ M) →
      ∀ D : BgData Gp N, Dom D →
        ∀ s ∈ polydisc (0 : RenLabel Gp (X1 Gp m₀ j 𝒦X) → ℂ) (fun _ => Real.exp κ),
          ‖Fc (rawOf D, ξ) s‖ ≤ M) :
    HasLocPrinciple (N := N) Gp Dom r₀
      (renYs (renCube Gp (X1 Gp m₀ j 𝒦X)) Gp m₀ (X1 Gp m₀ j 𝒦X)) (renDY Gp m₀) κa 1 Kcl f u := by
  classical
  have h1mem : (1 : RenLabel Gp (X1 Gp m₀ j 𝒦X) → ℂ) ∈ polydisc (0 : RenLabel Gp (X1 Gp m₀ j 𝒦X) → ℂ)
      (fun _ => Real.exp κ) := fun i => by
    simpa using (show (1 : ℝ) < Real.exp κ by
      have : 0 < κ := by
        have := hκ₁; have h0 : (0 : ℝ) ≤ 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κd := by
          have : 0 ≤ κd := by linarith
          positivity
        linarith [h1]
      exact Real.one_lt_exp_iff.2 this)
  let Ag : Finset (RenLabel Gp (X1 Gp m₀ j 𝒦X)) → (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) →
      (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) → Prop :=
    fun C q q' => ∀ D D' : BgData Gp N, rawOf D = q.1 → rawOf D' = q'.1 →
      RenC1Ag (renCube Gp (X1 Gp m₀ j 𝒦X)) (X1 Gp m₀ j 𝒦X) C (D, q.2) (D', q'.2)
  let AgY : Set (CTorus d L N₁ m₁ K) →
      (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) →
      (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) → Prop :=
    fun Y q q' => RawAgree (finOf Y) q.1 q'.1 ∧ q.2 = q'.2
  have hrefl : ∀ (C : Finset (RenLabel Gp (X1 Gp m₀ j 𝒦X))) q, Ag C q q := by
    intro C q D D' hD hD'
    have : D = D' := BgData.eq_of_raw (hD.trans hD'.symm)
    subst this
    exact renC1Ag_refl _ _ _ _
  have hlink : ∀ (C : Finset (RenLabel Gp (X1 Gp m₀ j 𝒦X))) q q',
      AgY (Ysites Gp m₀ (renCube Gp (X1 Gp m₀ j 𝒦X)) (X1 Gp m₀ j 𝒦X) C) q q' → Ag C q q' := by
    intro C q q' ⟨hraw, hξ⟩ D D' hD hD'
    refine renC1Ag_of_rawAgree hcov hmem C ?_ hξ
    simpa [hD, hD'] using hraw
  have hloc : ∀ S : Set (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)),
      S ⊆ expDom Gp Dom r₀ →
      LocalityAEOn (Real.exp κ) S (fun i => Pset m₁ (renCube Gp (X1 Gp m₀ j 𝒦X) i)) (compY (renCube Gp (X1 Gp m₀ j 𝒦X)) (X1 Gp m₀ j 𝒦X))
        Ag (fun q s => Fc q s) := by
    intro S hS C q q' hq hq' s s' hs hs' hss hAg
    obtain ⟨D, hD, hqD, hξ⟩ := hS hq
    obtain ⟨D', hD', hqD', hξ'⟩ := hS hq'
    have hqe : q = (rawOf D, q.2) := Prod.ext hqD rfl
    have hqe' : q' = (rawOf D', q'.2) := Prod.ext hqD' rfl
    have key := hlocD C (D, q.2) (D', q'.2) ⟨hD, hξ⟩ ⟨hD', hξ'⟩ s s' hs hs' hss
      (hAg D D' hqD.symm hqD'.symm)
    rw [hqe, hqe']
    exact key
  have expand : ∀ (S : Set (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ))) (Eb : ℝ),
      S ⊆ expDom Gp Dom r₀ → 0 ≤ Eb →
      (∀ q ∈ S, ∀ s ∈ polydisc (0 : RenLabel Gp (X1 Gp m₀ j 𝒦X) → ℂ) (fun _ => Real.exp κ),
        ‖Fc q s‖ ≤ Eb) →
      (∀ q ∈ S, Fc q 1 = ∑ Y ∈ renYs (renCube Gp (X1 Gp m₀ j 𝒦X)) Gp m₀ (X1 Gp m₀ j 𝒦X),
        evTerm (renCube Gp (X1 Gp m₀ j 𝒦X)) Gp m₀ (X1 Gp m₀ j 𝒦X) Fc (↑Y : Set (CTorus d L N₁ m₁ K)) q) ∧
      (∀ Y : Finset (CTorus d L N₁ m₁ K), ∀ q ∈ S, ∀ q' ∈ S, AgY ↑Y q q' →
        evTerm (renCube Gp (X1 Gp m₀ j 𝒦X)) Gp m₀ (X1 Gp m₀ j 𝒦X) Fc (↑Y : Set (CTorus d L N₁ m₁ K)) q =
          evTerm (renCube Gp (X1 Gp m₀ j 𝒦X)) Gp m₀ (X1 Gp m₀ j 𝒦X) Fc (↑Y : Set (CTorus d L N₁ m₁ K)) q') ∧
      (∀ Y : Finset (CTorus d L N₁ m₁ K), ∀ q ∈ S,
        ‖evTerm (renCube Gp (X1 Gp m₀ j 𝒦X)) Gp m₀ (X1 Gp m₀ j 𝒦X) Fc (↑Y : Set (CTorus d L N₁ m₁ K)) q‖ ≤
          Eb * Real.exp (-κa * renDY Gp m₀ Y)) ∧
      (∀ Y : Finset (CTorus d L N₁ m₁ K),
        AnalyticOnNhd ℂ (evTerm (renCube Gp (X1 Gp m₀ j 𝒦X)) Gp m₀ (X1 Gp m₀ j 𝒦X) Fc
          (↑Y : Set (CTorus d L N₁ m₁ K))) S) := by
    intro S Eb hS hEb hbd
    refine renLoc_localization_expansion_fin (c := renCube Gp (X1 Gp m₀ j 𝒦X)) (X := X)
      (𝒦X := 𝒦X) hcov hd hL hmem hinj hdisj hopt hΔ hκ₀ hκd hκ₁ h1 hlog hEb
      (S := S) (F := Fc) (Ag := Ag) (AgY := AgY) (fun C u _ => hrefl C u) hlink
      (hana.mono (Set.prod_mono hS le_rfl)) (fun q hq s hs => ?_) (hloc S hS) hout
    have := hbd q hq s hs
    rw [hΔ]
    simpa using this
  obtain ⟨e1, e2, -, e4⟩ := expand (expDom Gp Dom r₀) Eb₀ subset_rfl hEb₀
    (by
      rintro q ⟨D, hD, hqD, hξ⟩ s hs
      have hqe : q = (rawOf D, q.2) := Prod.ext hqD rfl
      rw [hqe]
      exact hbd₀ D hD q.2 hξ s hs)
  refine ⟨fun Y q => evTerm (renCube Gp (X1 Gp m₀ j 𝒦X)) Gp m₀ (X1 Gp m₀ j 𝒦X) Fc (↑Y : Set (CTorus d L N₁ m₁ K)) q,
    ?_, fun Y _ => e4 Y, ?_, ?_⟩
  · intro D hD ξ hξ
    have hmemS : ((rawOf D, ξ) : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ∈
        expDom Gp Dom r₀ := ⟨D, hD, rfl, hξ⟩
    rw [← hone D hD ξ hξ]
    exact e1 _ hmemS
  · intro Y _ q hq q' hq' hξ hraw
    refine e2 Y q hq q' hq' ⟨?_, hξ⟩
    rwa [finOf_coe]
  · intro ξ hξ M hM Y _ D hD
    have hmemS : ((rawOf D, ξ) : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ∈
        expDom Gp Dom r₀ := ⟨D, hD, rfl, hξ⟩
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hbdM ξ hξ M hM D hD 1 h1mem)
    let Sξ : Set (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) :=
      {q | ∃ D', Dom D' ∧ q.1 = (D'.Ψ, D'.h) ∧ q.2 = ξ}
    have hSξ : Sξ ⊆ expDom Gp Dom r₀ := by
      rintro q ⟨D', hD', h1', h2'⟩
      exact ⟨D', hD', h1', by rw [h2']; exact hξ⟩
    obtain ⟨-, -, e3, -⟩ := expand Sξ M hSξ hM0 (by
      rintro q ⟨D', hD', hqD, hqξ⟩ s hs
      have hqe : q = (rawOf D', q.2) := Prod.ext hqD rfl
      rw [hqe, hqξ]
      exact hbdM ξ hξ M hM D' hD' s hs)
    have := e3 Y ((D.Ψ, D.h), ξ) ⟨D, hD, rfl, rfl⟩
    simpa [neg_mul] using this

end Skeleton


section Multiplier

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The multiplier of the decoupled background as an ambient analytic function.**  There is a
function `Mc` of the raw datum, `ξ` and the cut vector, analytic at every point of
`expDom × polydisc`, equal to `decBgMult` at the extended cut on the data of `XiCOneReal`, and
equal to the true multiplier `bgMultC` at the all-ones cut. -/
theorem renBgMult_analytic
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (r₀ : ℝ)
    (X₁ : Set (CTorus d L N₁ m₁ K)) :
    ∃ Mc : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (RenLabel Gp X₁ → ℂ) →
        (Gp.Ω 1 → ℂ),
      AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) ×
          (RenLabel Gp X₁ → ℂ) => Mc p.1 p.2)
        (expDom Gp (XiCOneReal Gp (compWeight L a₁) ν eps) r₀ ×ˢ
          polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ)) ∧
      (∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
        ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
          Mc (rawOf D, ξ) s = decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ)
            (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm)) D) ∧
      (∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
        Mc (rawOf D, ξ) 1 = bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) := by
  classical
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic (N := N) hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have heq : ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
      ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
      (F₁ (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm), (D.Ψ, D.h))).2 =
        decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ)
          (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm)) D := by
    intro D hD ξ s hs
    have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hU := renXiCOneReal_inUnionC7 hC hD
    have hsx : ∀ P, ‖extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) P‖ < Real.exp κ :=
      norm_extParams_lt hE1 (fun i => hs' _)
    obtain ⟨φ, α, hI, -, hM⟩ := exists_decBg' hC hU hsx
    have := hF₁ _ D hsx hU φ α hI
    rw [this, hM]
  refine ⟨fun u s => (F₁ (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm), u.1)).2, ?_,
    fun D hD ξ s hs => heq D hD ξ s hs, ?_⟩
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
        (fun p : (RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ)) × (RenLabel Gp X₁ → ℂ) => p.2)
        fun i =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : RenLabel Gp X₁ => ℂ) i).analyticAt _
          |>.comp_of_eq analyticAt_snd rfl
    have hg0 : AnalyticAt ℂ g (u, s) :=
      ((analyticAt_extParams _).comp_of_eq hs2 rfl).prod (analyticAt_fst.comp analyticAt_fst)
    have hF1 : AnalyticAt ℂ (fun p => F₁ (g p)) (u, s) :=
      (hF₁an (g (u, s)) ⟨hsx, D, hU, by rw [hg]; exact hu1⟩).comp_of_eq hg0 rfl
    exact analyticAt_snd.comp hF1
  · intro D hD ξ
    have h1mem : (1 : RenLabel Gp X₁ → ℂ) ∈ polydisc (0 : RenLabel Gp X₁ → ℂ)
        (fun _ => Real.exp κ) := fun i => by simpa using hE1
    have hext : extParams Gp X₁ ((1 : RenLabel Gp X₁ → ℂ) ∘ (renLabelEquiv Gp X₁).symm) =
        fun _ => 1 := by
      have h1 : (1 : RenLabel Gp X₁ → ℂ) ∘ (renLabelEquiv Gp X₁).symm = 1 := rfl
      rw [h1, extParams_one]
    show (F₁ (extParams Gp X₁ ((1 : RenLabel Gp X₁ → ℂ) ∘ (renLabelEquiv Gp X₁).symm),
      (D.Ψ, D.h))).2 = _
    rw [heq D hD ξ 1 h1mem]
    have hs1 : ∀ P, ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ := fun P => by
      simpa using hE1
    obtain ⟨φ, α, hI, -, hM⟩ := exists_decBg' hC (renXiCOneReal_inUnionC7 hC hD) hs1
    obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := renXiCOneReal_inUnionC7 hC hD
    obtain ⟨-, -, hb⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 hδε hε hδc hνε hDC hI
    rw [hext, hM, hb]

end Multiplier


section Fields

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **`locDφ` at a site root** (zero class, `K_loc = 1`).  For the site `p`, the principle
`HasLocPrinciple` for the evaluation `v ↦ v p` of the perturbation field, with the class
`{v | SupBounds Gp v (c_K K₂ (B ‖ξ‖))}`, the cover `renYs` of the root neighbourhood of `p`, the
size `renDY` and the true field `(F ((Ψ, h), ξ)).1`, where `F` is the solution of `IsRenSol`. -/
theorem renLocDphi_zero_at
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    (hG' : IsLevel Gp (k + 1)) {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁)
    (hd : 3 ≤ d) (hL : 3 ≤ L) {κd κ₀ κb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκd : 3 * κ₀ + 3 ≤ κd)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κd ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hout : κb ≤ 2 * κd) {r₀ rF B cK : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ ≤ 1 / 16)
    {F : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
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
        cK * cK2 d L N * B)
    (p : Gp.Ω 1 × Fin N) :
    HasLocPrinciple (N := N) Gp (XiCOneReal Gp (compWeight L a₁) ν eps) r₀
      (renYs (renCube Gp (X1 Gp m₀ k (fam m₀ (p.1 : CTorus d L N₁ m₁ (k + 1))))) Gp m₀
        (X1 Gp m₀ k (fam m₀ (p.1 : CTorus d L N₁ m₁ (k + 1)))))
      (renDY Gp m₀) κb 1
      (fun _ ξ => {v | SupBounds Gp v (cK * (cK2 d L N * (B * ‖ξ‖)))})
      (fun _ v _ => v p) (fun D ξ => (F ((D.Ψ, D.h), ξ)).1) := by
  classical
  obtain ⟨-, hV⟩ := renLoc_fin_domains (N := N) Hm hC.Sp hG' hm₀ hN
  obtain ⟨hcov, -, hopt, hΔ, -, hinj, hmem, hdisj, -, -⟩ :=
    hV ((p.1 : CTorus d L N₁ m₁ (k + 1)), p.2)
  obtain ⟨Fcut, han, hF3, hcls, hend⟩ := renDec_joint hC hr₀0 hr₀1
    (X₁ := X1 Gp m₀ k (fam m₀ (p.1 : CTorus d L N₁ m₁ (k + 1)))) hF hrF hD₀ hδ₀ hδ₁ hM2 hB0
    hcK hCB
  have hcK0 : 0 ≤ cK := by linarith
  have hK2 := cK2_pos d L N
  refine renLocCut_principle (Fc := fun u s => (Fcut u s).1 p) (Eb₀ := cK * (cK2 d L N * (B * r₀)))
    hcov hd hL hmem hinj hdisj hopt hΔ hκ₀ hκd hκ₁ h1 hlog hout (by positivity) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    exact analyticAt_pi_iff.1 (analyticAt_fst.comp (han q hq)) p
  · exact renDphi_local_cut hC hconn hG' hm₀ hN p hr₀1 hD₀ hδ₀ hδ₁
      (S := {u | XiCOneReal Gp (compWeight L a₁) ν eps u.1 ∧ ‖u.2‖ < r₀})
      (fun u hu => hu.1) (fun u hu => hu.2)
      (fun D hD ξ hξ s hs s' E hs' hE => by
        obtain ⟨a, b, c, -⟩ := hF3 D hD ξ hξ s hs s' E hs' hE
        exact ⟨a, b, c⟩)
  · intro D hD ξ hξ s hs
    have h := ((hcls D hD ξ hξ s hs).1.val (p.1 : Torus d (N₁ * L ^ m₁ * L ^ (k + 1))) p.2)
    rw [svec_of_mem] at h
    refine h.trans ?_
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hξ.le hB0) hK2.le
    exact mul_le_mul_of_nonneg_left this hcK0
  · intro D hD ξ hξ
    show (Fcut (rawOf D, ξ) 1).1 p = (F ((D.Ψ, D.h), ξ)).1 p
    rw [hend D hD ξ hξ]
  · intro ξ hξ M hM D hD s hs
    refine hM D hD _ ?_
    exact (hcls D hD ξ hξ s hs).1

/-- **`locC2` at a block root** (zero class, `K_loc = 1`).  For the block root `z`, the principle
`HasLocPrinciple` for the density `C₂(B_{k+1}(z))` of the perturbation `(δφ, α + δα)` with the class
`pertClass`, the cover `renYs` of the root neighbourhood, the size `renDY`, and the true
perturbation `((F …).1, bgMultC … D + (F …).2)`, where `F` is the solution of `IsRenSol`.  The
cut functional carries the multiplier `Mc` of `renBgMult_analytic`; at `s = 1` it is `bgMultC`. -/
theorem renLocC2_zero_at
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    (hG' : IsLevel Gp (k + 1)) {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁)
    (hd : 3 ≤ d) (hL : 3 ≤ L) {κd κ₀ κa : ℝ} (hκ₀ : 0 ≤ κ₀) (hκd : 3 * κ₀ + 3 ≤ κd)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κd ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hout : κa ≤ 2 * κd) {r₀ rF B cK : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ ≤ 1 / 16)
    {F : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
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
        cK * cK2 d L N * B)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    HasLocPrinciple (N := N) Gp (XiCOneReal Gp (compWeight L a₁) ν eps) r₀
      (renYs (renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))) Gp m₀
        (X1 Gp m₀ k (fam m₀ (blockSite k z))))
      (renDY Gp m₀) κa 1
      (fun _ ξ => pertClass Gp (cK * (cK2 d L N * (B * ‖ξ‖)))
        (bgK1 d L N * (xiC1 d * eps) + cK * cK2 d L N * B * r₀ + 2) (renMassU ν ξ))
      (fun _ v ξ => renC2On Gp (compWeight L a₁) (blockSites d L N₁ m₁ (k + 1) k z) ξ
        (renMassU ν ξ) v.2 v.1)
      (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1,
        bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D + (F ((D.Ψ, D.h), ξ)).2)) := by
  classical
  obtain ⟨hV, -⟩ := renLoc_fin_domains (N := N) Hm hC.Sp hG' hm₀ hN
  obtain ⟨hcov, -, hopt, hΔ, -, -, -, hinj, hmem, hdisj, -, -⟩ := hV z
  obtain ⟨Fcut, han, hF3, hcls, hend⟩ := renDec_joint hC hr₀0 hr₀1
    (X₁ := X1 Gp m₀ k (fam m₀ (blockSite k z))) hF hrF hD₀ hδ₀ hδ₁ hM2 hB0 hcK hCB
  obtain ⟨Mc, hMan, hMc, hMone⟩ := renBgMult_analytic hC r₀
    (X1 Gp m₀ k (fam m₀ (blockSite k z)))
  set Bs := blockSites d L N₁ m₁ (k + 1) k z with hBs
  have hcK0 : 0 ≤ cK := by linarith
  have hK2 := cK2_pos d L N
  have hK1 := bgK1_pos d L N
  have hX := one_le_xiC1 d
  have hε := hC.eps_pos
  have hV0 : 0 ≤ cK * (cK2 d L N * (B * r₀)) := by positivity
  have hA0 : 0 ≤ bgK1 d L N * (xiC1 d * eps) + cK * cK2 d L N * B * r₀ + 2 := by positivity
  have hW : 0 ≤ blockWeight Gp Bs := Finset.sum_nonneg fun x _ => by
    have := spacing_pos Gp (x := (x : Torus d (N₁ * L ^ m₁ * L ^ (k + 1)))); positivity
  refine renLocCut_principle
    (Fc := fun u s => renC2On Gp (compWeight L a₁) Bs u.2 (renMassU ν u.2)
      (Mc u s + (Fcut u s).2) (Fcut u s).1)
    (Eb₀ := 17 / 32 * (N * ((3 + (bgK1 d L N * (xiC1 d * eps) + cK * cK2 d L N * B * r₀ + 2)) *
      (cK * (cK2 d L N * (B * r₀))) ^ 2)) * blockWeight Gp Bs)
    hcov hd hL hmem hinj hdisj hopt hΔ hκ₀ hκd hκ₁ h1 hlog hout (by positivity) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    obtain ⟨⟨D, hD, hq1, hq2⟩, hs⟩ := hq
    have han1 := han q ⟨⟨D, hD, hq1, hq2⟩, hs⟩
    have hM1 := hMan q ⟨⟨D, hD, hq1, hq2⟩, hs⟩
    have hne : 1 + q.1.2 2 ≠ 0 := one_add_ne_zero_of_norm (by linarith) 2
    have hξ : ∀ j, AnalyticAt ℂ (fun q' : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)) ×
        (RenLabel Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) → ℂ) => q'.1.2 j) q := fun j => by
      fun_prop
    have hm : AnalyticAt ℂ (fun q' : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)) ×
        (RenLabel Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) → ℂ) => renMassU ν q'.1.2) q := by
      unfold renMassU
      exact (analyticAt_const.mul (analyticAt_const.add (hξ 1))).div
        (analyticAt_const.add (hξ 2)) hne
    exact an_renC2On (G := Gp) (compWeight L a₁) Bs (fun (q' : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)) × (RenLabel Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) → ℂ)) => q'.1.2)
      (fun (q' : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)) × (RenLabel Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) → ℂ)) => renMassU ν q'.1.2) (fun (q' : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)) × (RenLabel Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) → ℂ)) => Mc q'.1 q'.2 + (Fcut q'.1 q'.2).2)
      (fun (q' : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)) × (RenLabel Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) → ℂ)) => (Fcut q'.1 q'.2).1) hξ hm
      (fun y => (analyticAt_pi_iff.1 hM1 y).add
        (analyticAt_pi_iff.1 (analyticAt_snd.comp han1) y))
      (fun y i => analyticAt_pi_iff.1 (analyticAt_fst.comp han1) (y, i))
  · intro C u u' hu hu' s s' hs hs' hss hag
    have hsp : s ∈ polydisc (0 : RenLabel Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) → ℂ)
        (fun _ => Real.exp κ) := fun i => by simpa using hs.2 i
    have hsp' : s' ∈ polydisc (0 : RenLabel Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) → ℂ)
        (fun _ => Real.exp κ) := fun i => by simpa using hs'.2 i
    have key := renC2_local_cut hC hconn hG' hm₀ hN z hr₀1 hD₀ hδ₀ hδ₁
      (S := {u | XiCOneReal Gp (compWeight L a₁) ν eps u.1 ∧ ‖u.2‖ < r₀})
      (fun u hu => hu.1) (fun u hu => hu.2)
      (fun D hD ξ hξ s hs s' E hs' hE => by
        obtain ⟨a, b, c, -⟩ := hF3 D hD ξ hξ s hs s' E hs' hE
        exact ⟨a, b, c⟩) C u u' hu hu' s s' hs hs' hss hag
    dsimp only
    rw [hMc u.1 hu.1 u.2 s hsp, hMc u'.1 hu'.1 u'.2 s' hsp']
    exact key
  · intro D hD ξ hξ s hs
    dsimp only
    rw [hMc D hD ξ s hs]
    have hv := (hcls D hD ξ hξ s hs).2
    have hV' : 0 ≤ cK * (cK2 d L N * (B * ‖ξ‖)) := by positivity
    refine (norm_renC2On_le_of_mem (G := Gp) (a := compWeight L a₁) hC.HBp.weights hV' hA0 hv
      (hξ.le.trans hr₀1) Bs).trans ?_
    have hle : cK * (cK2 d L N * (B * ‖ξ‖)) ≤ cK * (cK2 d L N * (B * r₀)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hξ.le hB0) hK2.le) hcK0
    have hsq := pow_le_pow_left₀ hV' hle 2
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    gcongr
  · intro D hD ξ hξ
    dsimp only
    rw [hMone D hD ξ, hend D hD ξ hξ]
  · intro ξ hξ M hM D hD s hs
    dsimp only
    rw [hMc D hD ξ s hs]
    have hv := (hcls D hD ξ hξ s hs).2
    exact hM D hD ((Fcut (rawOf D, ξ) s).1,
      decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ)
        (extParams Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))
          (s ∘ (renLabelEquiv Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))).symm)) D +
        (Fcut (rawOf D, ξ) s).2) hv

end Fields

end Balaban.Localization
