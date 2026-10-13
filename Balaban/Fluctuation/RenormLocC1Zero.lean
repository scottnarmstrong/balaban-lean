/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormC1Local
public import Balaban.Fluctuation.RenormC1Analytic
public import Balaban.Fluctuation.RenormLocFibre
public import Balaban.Fluctuation.RenormExpG
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The localization expansion of the `C₁` functional at the zero class

The first localization principle `locC1` of the record `RenormExpInput`, at a block root `z` of the
full level `k + 1`: the density `C₁(B_{k+1}(z))` at the true background is the sum over the
finsets `Y` of the renormalization cover of local, jointly analytic terms, and the terms satisfy the
transfer clause of `HasLocPrinciple` with `K_loc = 1`.

Only the zero class is treated.  The proof applies `renLoc_localization_expansion_fin` to the
cut functional of `renC1Cut_analytic`; its hypotheses come from `renLoc_fin_domains` (cover and
root facts), `renC1Cut_analytic` (analyticity), `norm_renC1On_dec_le_of_class` (the bound, through
the class-wide bound `M` of the transfer clause), `renC1_local_cut` (locality), `renC1Ag_refl` and
`renC1Ag_of_rawAgree` (the agreement relations) and `renC1Cut_one` (the value at `s = 1`).

The principles `locC2`, `locDφ` and an inhabitant of `RenormExpInput` are NOT proved here.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis Finset

section Main

open LocalCover

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **`locC1` at a block root, abstract setting** (zero class, `K_loc = 1`).  Under `FlCore`,
`HatConn`, `IsLevel Gp (k + 1)`, `1 ≤ m₀`, `L ^ m₀ ∣ N₁` and the rate hypotheses of
`renLoc_localization_expansion_fin` (the polydisc rate is the `κ` of `FlCore`, the decay rate
`κd`, the output rate `κa ≤ 2 κd`): the principle `HasLocPrinciple` for the density `C₁` of the
block of the root `z`, with the domain `XiCOneReal`, the class
`bgClass Gp ν ((2 + 2 K₄ ξ₁) ε)`, the cover `renYs` of the root neighbourhood and the size
`renDY`.  The bound `M` of the transfer clause is arbitrary. -/
theorem renLocC1_zero_at
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    (hG' : IsLevel Gp (k + 1)) {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁)
    (hd : 3 ≤ d) (hL : 3 ≤ L) {κd κ₀ κa : ℝ} (hκ₀ : 0 ≤ κ₀) (hκd : 3 * κ₀ + 3 ≤ κd)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κd ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hout : κa ≤ 2 * κd) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ ≤ 1 / 16)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    HasLocPrinciple (N := N) Gp (XiCOneReal Gp (compWeight L a₁) ν eps) r₀
      (renYs (renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))) Gp m₀
        (X1 Gp m₀ k (fam m₀ (blockSite k z))))
      (renDY Gp m₀) κa 1
      (fun D _ => bgClass Gp ν ((2 + 2 * K4 d L N BG κ * xiC1 d) * eps) D)
      (fun D φ ξ => renC1On Gp (compWeight L a₁) ν eps (blockSites d L N₁ m₁ (k + 1) k z)
        D.Ψ D.h φ ξ)
      (fun D _ => bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D) := by
  classical
  obtain ⟨hV, -⟩ := renLoc_fin_domains (N := N) Hm hC.Sp hG' hm₀ hN
  obtain ⟨hcov, hX₁, hopt, hΔ, -, -, -, hinj, hmem, hdisj, -, -⟩ := hV z
  set X₁ := X1 Gp m₀ k (fam m₀ (blockSite k z)) with hX₁def
  set B := blockSites d L N₁ m₁ (k + 1) k z with hB
  set Dom := XiCOneReal Gp (compWeight L a₁) ν eps with hDom
  obtain ⟨F, hFan, hFeq⟩ := renC1Cut_analytic hC r₀ X₁ B
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have h1mem : (1 : RenLabel Gp X₁ → ℂ) ∈ polydisc (0 : RenLabel Gp X₁ → ℂ)
      (fun _ => Real.exp κ) := fun i => by simpa using hE1
  -- the agreement relations on raw data
  let Ag : Finset (RenLabel Gp X₁) → (RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)) →
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)) → Prop :=
    fun C q q' => ∀ D D' : BgData Gp N, rawOf D = q.1 → rawOf D' = q'.1 →
      RenC1Ag (renCube Gp X₁) X₁ C (D, q.2) (D', q'.2)
  let AgY : Set (CTorus d L N₁ m₁ (k + 1)) →
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)) →
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)) → Prop :=
    fun Y q q' => RawAgree (finOf Y) q.1 q'.1 ∧ q.2 = q'.2
  have hrefl : ∀ (C : Finset (RenLabel Gp X₁)) q, Ag C q q := by
    intro C q D D' hD hD'
    have : D = D' := BgData.eq_of_raw (hD.trans hD'.symm)
    subst this
    exact renC1Ag_refl _ _ _ _
  have hlink : ∀ (C : Finset (RenLabel Gp X₁)) q q',
      AgY (Ysites Gp m₀ (renCube Gp X₁) X₁ C) q q' → Ag C q q' := by
    intro C q q' ⟨hraw, hξ⟩ D D' hD hD'
    refine renC1Ag_of_rawAgree hcov hmem C ?_ hξ
    simpa [hD, hD'] using hraw
  -- locality of the ambient cut functional on `expDom`
  have hloc : ∀ S : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)),
      S ⊆ expDom Gp Dom r₀ →
      LocalityAEOn (Real.exp κ) S (fun i => Pset m₁ (renCube Gp X₁ i)) (compY (renCube Gp X₁) X₁)
        Ag F := by
    intro S hS C q q' hq hq' s s' hs hs' hss hAg
    obtain ⟨D, hD, hqD, -⟩ := hS hq
    obtain ⟨D', hD', hqD', -⟩ := hS hq'
    have hsp : s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ) :=
      fun i => by simpa using hs.2 i
    have hsp' : s' ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ) :=
      fun i => by simpa using hs'.2 i
    have hqe : q = (rawOf D, q.2) := Prod.ext hqD rfl
    have hqe' : q' = (rawOf D', q'.2) := Prod.ext hqD' rfl
    have key := renC1_local_cut hC hconn hG' hm₀ hN z eps
      (S := {u : BgData Gp N × (Fin 3 → ℂ) | Dom u.1}) (fun u hu => hu) C (D, q.2) (D', q'.2)
      hD hD' s s' hs hs' hss (hAg D D' hqD.symm hqD'.symm)
    rw [hqe, hqe', hFeq D hD q.2 s hsp, hFeq D' hD' q'.2 s' hsp']
    exact key
  -- the finite expansion on a set `S ⊆ expDom` with a uniform bound `Eb`
  have expand : ∀ (S : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ))) (Eb : ℝ),
      S ⊆ expDom Gp Dom r₀ → 0 ≤ Eb →
      (∀ u ∈ S, ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
        ‖F u s‖ ≤ Eb) →
      (∀ u ∈ S, F u 1 = ∑ Y ∈ renYs (renCube Gp X₁) Gp m₀ X₁,
        evTerm (renCube Gp X₁) Gp m₀ X₁ F (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) u) ∧
      (∀ Y : Finset (CTorus d L N₁ m₁ (k + 1)), ∀ u ∈ S, ∀ u' ∈ S, AgY ↑Y u u' →
        evTerm (renCube Gp X₁) Gp m₀ X₁ F (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) u =
          evTerm (renCube Gp X₁) Gp m₀ X₁ F (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) u') ∧
      (∀ Y : Finset (CTorus d L N₁ m₁ (k + 1)), ∀ u ∈ S,
        ‖evTerm (renCube Gp X₁) Gp m₀ X₁ F (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) u‖ ≤
          Eb * Real.exp (-κa * renDY Gp m₀ Y)) ∧
      (∀ Y : Finset (CTorus d L N₁ m₁ (k + 1)),
        AnalyticOnNhd ℂ (evTerm (renCube Gp X₁) Gp m₀ X₁ F
          (↑Y : Set (CTorus d L N₁ m₁ (k + 1)))) S) := by
    intro S Eb hS hEb hbd
    refine renLoc_localization_expansion_fin (c := renCube Gp X₁) (X := cube m₀ k (blockSite k z))
      (𝒦X := fam m₀ (blockSite k z)) hcov hd hL hmem hinj hdisj hopt hΔ hκ₀ hκd hκ₁ h1 hlog hEb
      (S := S) (F := F) (Ag := Ag) (AgY := AgY) (fun C u _ => hrefl C u) hlink
      (hFan.mono (Set.prod_mono hS le_rfl)) (fun u hu s hs => ?_) (hloc S hS) hout
    have := hbd u hu s hs
    rw [hΔ]
    simpa using this
  have hd0 : 0 < d := by omega
  have hK4 := (K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0).le
  have hε := hC.eps_pos
  have hC1pos : 0 < xiC1 d := by unfold xiC1; positivity
  have hcK : eps ≤ (2 + 2 * K4 d L N BG κ * xiC1 d) * eps := by
    have : 0 ≤ K4 d L N BG κ * xiC1 d := by positivity
    nlinarith
  have hbw : 0 ≤ blockWeight Gp B :=
    Finset.sum_nonneg fun x _ => by positivity
  -- the uniform bound on the whole domain
  set Eb₀ : ℝ := (d + 6) * ((2 + 2 * K4 d L N BG κ * xiC1 d) * eps) ^ 2 * r₀ *
    blockWeight Gp B with hEb₀
  have hEb₀0 : 0 ≤ Eb₀ := by positivity
  have hbd₀ : ∀ q ∈ expDom Gp Dom r₀, ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ)
      (fun _ => Real.exp κ), ‖F q s‖ ≤ Eb₀ := by
    rintro q ⟨D, hD, hqD, hξ⟩ s hs
    have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hsx : ∀ P, ‖extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) P‖ < Real.exp κ :=
      norm_extParams_lt hE1 (fun i => hs' _)
    have hqe : q = (rawOf D, q.2) := Prod.ext hqD rfl
    rw [hqe, hFeq D hD q.2 s hs]
    have := norm_renC1On_dec_le hC hD (fun P => (hsx P).le) (εζ := eps) hε.le hcK
      (ξ := q.2) (hξ.le.trans hr₀1) B
    refine this.trans ?_
    rw [hEb₀]
    have h0 : 0 ≤ ((d : ℝ) + 6) * ((2 + 2 * K4 d L N BG κ * xiC1 d) * eps) ^ 2 := by positivity
    calc _ = ((d : ℝ) + 6) * ((2 + 2 * K4 d L N BG κ * xiC1 d) * eps) ^ 2 * (‖q.2‖ *
          blockWeight Gp B) := by ring
      _ ≤ ((d : ℝ) + 6) * ((2 + 2 * K4 d L N BG κ * xiC1 d) * eps) ^ 2 * (r₀ *
          blockWeight Gp B) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hξ.le hbw) h0
      _ = _ := by ring
  obtain ⟨e1, e2, -, e4⟩ := expand (expDom Gp Dom r₀) Eb₀ subset_rfl hEb₀0 hbd₀
  refine ⟨fun Y q => evTerm (renCube Gp X₁) Gp m₀ X₁ F (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) q,
    ?_, fun Y _ => e4 Y, ?_, ?_⟩
  · -- the sum over the cover
    intro D hD ξ hξ
    have hmemS : ((rawOf D, ξ) : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)) ∈
        expDom Gp Dom r₀ := ⟨D, hD, rfl, hξ⟩
    have := (e1 _ hmemS).symm
    rw [hFeq D hD ξ 1 h1mem, renC1Cut_one a₁ ν eps hC hD X₁ B ξ] at this
    exact this.symm
  · -- locality
    intro Y _ q hq q' hq' hξ hraw
    refine e2 Y q hq q' hq' ⟨?_, hξ⟩
    rwa [finOf_coe]
  · -- the transfer clause
    intro ξ hξ M hM Y _ D hD
    have hmemS : ((rawOf D, ξ) : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)) ∈
        expDom Gp Dom r₀ := ⟨D, hD, rfl, hξ⟩
    have hM0 : 0 ≤ M := by
      have h1' : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ ≤ Real.exp κ := fun P => by
        simpa using hE1.le
      exact (norm_nonneg _).trans (hM D hD _ (renBgClass_dec hC hD h1'))
    let Sξ : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ)) :=
      {q | ∃ D', Dom D' ∧ q.1 = (D'.Ψ, D'.h) ∧ q.2 = ξ}
    have hSξ : Sξ ⊆ expDom Gp Dom r₀ := by
      rintro q ⟨D', hD', h1', h2'⟩
      exact ⟨D', hD', h1', by rw [h2']; exact hξ⟩
    have hbdM : ∀ q ∈ Sξ, ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
        ‖F q s‖ ≤ M := by
      rintro q ⟨D', hD', hqD, hqξ⟩ s hs
      have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
      have hsx : ∀ P, ‖extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) P‖ < Real.exp κ :=
        norm_extParams_lt hE1 (fun i => hs' _)
      have hqe : q = (rawOf D', q.2) := Prod.ext hqD rfl
      rw [hqe, hFeq D' hD' q.2 s hs, hqξ]
      exact norm_renC1On_dec_le_of_class hC hD' (fun P => (hsx P).le) (hM := fun φ hφ =>
        hM D' hD' φ hφ)
    obtain ⟨-, -, e3, -⟩ := expand Sξ M hSξ hM0 hbdM
    have := e3 Y ((D.Ψ, D.h), ξ) ⟨D, hD, rfl, rfl⟩
    simpa [neg_mul] using this

/-- **`locC1` for every block root, abstract setting** (the field `RenormExpInput.locC1` at the
zero class, with `K_loc = 1`, `c_K = 2 + 2 K₄ ξ₁`, blocks `blockSites … k z`, covers `renYs` of the
root neighbourhoods and size `renDY`).  The hypotheses are those of `renLocC1_zero_at`. -/
theorem renLocC1_zero
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    (hG' : IsLevel Gp (k + 1)) {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁)
    (hd : 3 ≤ d) (hL : 3 ≤ L) {κd κ₀ κa : ℝ} (hκ₀ : 0 ≤ κ₀) (hκd : 3 * κ₀ + 3 ≤ κd)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κd ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hout : κa ≤ 2 * κd) {r₀ : ℝ} (hr₀0 : 0 < r₀) (hr₀1 : r₀ ≤ 1 / 16) :
    ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      HasLocPrinciple (N := N) Gp (XiCOneReal Gp (compWeight L a₁) ν eps) r₀
        (renYs (renCube Gp (X1 Gp m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z)))) Gp m₀
          (X1 Gp m₀ k (LocalCover.fam m₀ (LocalCover.blockSite k z))))
        (renDY Gp m₀) κa 1
        (fun D _ => bgClass Gp ν ((2 + 2 * K4 d L N BG κ * xiC1 d) * eps) D)
        (fun D φ ξ => renC1On Gp (compWeight L a₁) ν eps (blockSites d L N₁ m₁ (k + 1) k z)
          D.Ψ D.h φ ξ)
        (fun D _ => bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D) :=
  fun z => renLocC1_zero_at hC hconn hG' hm₀ hN hd hL hκ₀ hκd hκ₁ h1 hlog hout hr₀0 hr₀1 z

end Main

end Balaban.Localization
