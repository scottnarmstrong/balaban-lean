/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RTransport
public import Balaban.LargeField.R.RhoZeroRestricted
public import Balaban.LargeField.R.RopConcreteMeas
import Mathlib
import Balaban.LargeField.R.PsiZeroAnalytic

/-!
# The reference density of the removed kernel on the outputs of a localized history

`notes/phase1/LF4R-PLAN.md` §6.4.  The restricted reference density `rhoZeroRestricted` is a function
of `u = ψ_k↾Z₀` for a fixed outside field `ψ_k` in the tube `Ψ̃(X ∖ Z₀; δ)`.  The removed kernel
(`removedKernel`) takes a density `r : OutZero → OutRest → ℝ`.  The density used is the term

`r w y = if TubeOn G (X ∖ Z₀) δ ψ_y then rhoZeroRestricted … ψ_y … (u w) else 0`,

where `ψ_y` is the extension (zero off `V`) of the output equal to `0` on `Z₀` and `y` on
`V ∖ Z₀`, and `u w` is the variable of `Z₀` (`SuppSpace`) carrying the output `w`.  It enters the
theorems below through the equation `hr`; no definition is introduced.

* `measurable_rhoZeroRestrictedTot`: `(u, ψ_k) ↦ [tube] ρ^Z_{k,0}(Z)` is jointly Borel
  (`rhoZeroRestricted_eq_mul` and the landed measurability of the landed density);
* `measurable_removedDensity`, `removedDensity_nonneg`: joint measurability of `(w, y) ↦ r w y` and
  `0 ≤ r`;
* `remDen_eq_integral_rhoZeroRestricted`: `remDen r o = ∫ ρ^Z_{k,0}(Z) du` (the change of
  variables `measurePreserving_suppToOutPart`); `remDen_pos`, `remDen_eq_exp`: Lemma III.8.2 on
  the outputs (`denominatorRestricted_eq`); `remDen_eq_zero_of_not_tube`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ActionConv

section Total

variable (N : ℕ) {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] [NeZero N] {ϱ : ℝ}
  (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k)
  (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)

local notation "Kz" => psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H

include hd hk hw1 hwD hm hXreg hΩ hdata H in
open Classical in
/-- **The restricted reference density is jointly Borel in `(ψ_k↾Z₀, ψ_k)`** (Definition III.8.1,
P7 (1.5)), `0` off the tube: it is the landed density times the exponential of the (Borel on the
tube) difference of the action on `Ω₁` and the restricted action (`rhoZeroRestricted_eq_mul`). -/
theorem measurable_rhoZeroRestrictedTot {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) (Zr : Region G) (ν : ℝ)
    (h : Fin N → ℝ) {β0 p0 : ℝ} (hβ0 : 0 < β0) (hp0 : 1 ≤ cSix d D Kz * p0)
    (hrad : Kz * δ + 5 * zeroRadius (cSix d D Kz) (betaK d L k β0) p0 ≤ etaDen d L N D) :
    Measurable (fun p : SuppSpace (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) N ×
        BlockField d L N₀ k N => if hT : TubeOn G (X \ box b0 w) δ p.2 then
        rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hT Zr ν h β0 p0 p.1
      else 0) := by
  classical
  have hβk : 0 < betaK d L k β0 := by
    unfold betaK
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hT0 := measurable_rhoZeroTot N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hβk hp0 hrad
  by_cases hex : ∃ ψk : BlockField d L N₀ k N, TubeOn G (X \ box b0 w) δ ψk
  swap
  · have : (fun p : SuppSpace (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) N ×
        BlockField d L N₀ k N => if hT : TubeOn G (X \ box b0 w) δ p.2 then
        rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hT Zr ν h β0 p0 p.1
      else 0) = fun _ => 0 := by
      funext p
      have hT : ¬ TubeOn G (X \ box b0 w) δ p.2 := fun hT => hex ⟨p.2, hT⟩
      simp [hT]
    rw [this]; exact measurable_const
  obtain ⟨ψ1, hψ1⟩ := hex
  obtain ⟨hηpos, hη0, hη1, -⟩ :=
    tube_of_cutoff G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψ1 hβk hp0 hrad
  set Zb := boxFinset (L := L) (N₀ := N₀) (k := k) b0 w with hZb
  have hmergeM : Measurable fun p : SuppSpace Zb N × BlockField d L N₀ k N => mergeField Zb p.2 p.1 :=
    (continuous_mergeField (N := N) Zb).measurable
  have hEff := measurable_effTube G a H hηpos hη0 hη1
  have hAct : Measurable (fun ψ : BlockField d L N₀ k N =>
      if TubeOn G Set.univ (etaDen d L N D) ψ then actionZ G a Zr ν h ψ else 0) := by
    have hm' := ContinuousOn.measurable_piecewise
      (s := {ψ : BlockField d L N₀ k N | TubeOn G Set.univ (etaDen d L N D) ψ})
      (f := actionZ G a Zr ν h) (g := fun _ => (0 : ℝ))
      (continuousOn_actionZ H hηpos hη0 hη1 Zr ν h) continuous_const.continuousOn
      (measurableSet_tubeOn N G _ _)
    convert hm' using 1
    funext ψ
    simp [Set.piecewise]
  have heq : (fun p : SuppSpace Zb N × BlockField d L N₀ k N => if hT : TubeOn G (X \ box b0 w) δ p.2 then
        rhoZeroRestricted G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hT Zr ν h β0 p0 p.1
      else 0) =
      fun p => rhoZeroTot N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc (betaK d L k β0) p0 p *
        Real.exp (β0 * (effTube G a (etaDen d L N D) (mergeField Zb p.2 p.1) -
          (if TubeOn G Set.univ (etaDen d L N D) (mergeField Zb p.2 p.1) then
            actionZ G a Zr ν h (mergeField Zb p.2 p.1) else 0))) := by
    funext p
    by_cases hT : TubeOn G (X \ box b0 w) δ p.2
    · have h1 : rhoZeroTot N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc (betaK d L k β0) p0 p =
          rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hT (betaK d L k β0) p0 p.1 := by
        simp [rhoZeroTot, hT]
      rw [h1]
      simp only [hT, ↓reduceDIte]
      rw [rhoZeroRestricted_eq_mul]
      by_cases hc : ZeroCutoff (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hT)
          (zeroRadius (cSix d D Kz) (betaK d L k β0) p0) p.1
      · obtain ⟨-, -, -, hcut⟩ :=
          tube_of_cutoff G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hT hβk hp0 hrad
        have ht : TubeOn G Set.univ (etaDen d L N D) (mergeField Zb p.2 p.1) := hcut p.1 hc
        have e1 := effTube_eq (N := N) G a ht
        simp only [e1, ht, ↓reduceIte]
        rfl
      · have : rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hT (betaK d L k β0) p0 p.1 = 0 :=
          rhoZeroWith_eq_zero G a _ _ _ _ (betaK d L k β0) p0 _ hc
        rw [this]; simp
    · simp [rhoZeroTot, hT]
  rw [heq]
  exact hT0.mul (Real.measurable_exp.comp (measurable_const.mul
    ((hEff.comp hmergeM).sub (hAct.comp hmergeM))))

end Total

section Out

open Classical

set_option quotPrecheck false

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k N₀ : ℕ} [NeZero N₀] [NeZero N] (a : LocalHistory S n M K)
  (hN : N₀ * S.L ^ (k - k) = M * n K * S.L ^ (K - k)) {ϱ : ℝ}
  (G : GeneratingSet S.d S.L N₀ k ϱ) (aw : ℕ → ℝ) {D : ℕ} (hd : 2 ≤ S.d) (hk : 1 ≤ k)
  (b0 : Torus S.d (N₀ * S.L ^ (k - k))) (w : Fin S.d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * S.L ^ (k - k))
  {X : Set (Torus S.d (N₀ * S.L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock S.d S.L N₀ k k x ∈ X) (H : BgHyp S.d S.L k ϱ aw 0)
  {δ : ℝ} (hδ : 0 < δ) (hδc : δ ≤ psiZeroC11 N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)
  (Zr : Region G) (ν : ℝ) (h : Fin N → ℝ) (β0 p0 : ℝ) (Z0 : Set (BlockAt S n M K k))
  (hZ0 : ∀ y : BlockAt S n M K k, (y ∈ Vblk R a k ∧ y ∈ Z0) ↔
    torusCast hN.symm y ∈ boxFinset (L := S.L) (N₀ := N₀) (k := k) b0 w)

set_option hygiene false in
/-- The extension (zero off `V`) of the output equal to `0` on `Z₀` and to `y` on `V ∖ Z₀`, as a
block field of the level-`k` torus. -/
local notation "ψo[" y "]" =>
  (fun (z : Torus S.d (N₀ * S.L ^ (k - k))) (i : Fin N) =>
    outField N (remZeroMerge a k Z0 (0, y)) (torusCast hN z) i)

set_option hygiene false in
/-- The variable `u ∈ SuppSpace (box b₀ w)` of `Z₀` carrying the output `wv : OutZero`. -/
local notation "uo[" wv "]" =>
  (WithLp.toLp 2 (fun p : ↥(boxFinset (L := S.L) (N₀ := N₀) (k := k) b0 w) × Fin N =>
    wv ⟨torusCast hN p.1.1, (hZ0 _).2 (by rw [torusCast_symm_cast]; exact p.1.2)⟩ p.2) :
    SuppSpace (boxFinset (L := S.L) (N₀ := N₀) (k := k) b0 w) N)

variable (r : OutZero N R a k Z0 → OutRest N R a k Z0 → ℝ)
  (hr : ∀ (wv : OutZero N R a k Z0) (y : OutRest N R a k Z0), r wv y =
    if hψ : TubeOn G (X \ box b0 w) δ ψo[y] then
      rhoZeroRestricted G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψ Zr ν h β0 p0 uo[wv]
    else 0)

include hd hk hw1 hwD hm hXreg hΩ hdata H hZ0 hr

theorem removedDensity_nonneg (wv : OutZero N R a k Z0) (y : OutRest N R a k Z0) : 0 ≤ r wv y := by
  rw [hr]
  split_ifs
  · exact rhoZeroRestrictedWith_nonneg _ _ _ _ _ _ _ _ _ _
  · exact le_rfl

theorem measurable_removedDensity (hβ0 : 0 < β0) (hp0 : 1 ≤ cSix S.d D
      (psiZeroK N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) * p0)
    (hrad : psiZeroK N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ +
      5 * zeroRadius (cSix S.d D (psiZeroK N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H))
        (betaK S.d S.L k β0) p0 ≤ etaDen S.d S.L N D) :
    Measurable fun q : OutZero N R a k Z0 × OutRest N R a k Z0 => r q.1 q.2 := by
  have hT := measurable_rhoZeroRestrictedTot N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc
    Zr ν h hβ0 hp0 hrad
  have hu : Measurable fun wv : OutZero N R a k Z0 => uo[wv] := by
    refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr fun p => ?_)
    exact (EuclideanSpace.proj p.2).continuous.measurable.comp (measurable_pi_apply _)
  have hψ : Measurable fun y : OutRest N R a k Z0 => ψo[y] := by
    refine measurable_pi_iff.mpr fun z => measurable_pi_iff.mpr fun i => ?_
    have hmg : Measurable fun y : OutRest N R a k Z0 => remZeroMerge a k Z0 (0, y) :=
      (measurable_remZeroMerge a k Z0).comp (measurable_const.prodMk measurable_id)
    by_cases hz : torusCast hN z ∈ Vblk R a k
    · simp only [outField, hz, ↓reduceDIte]
      exact (EuclideanSpace.proj i).continuous.measurable.comp
        ((measurable_pi_apply _).comp hmg)
    · simp only [outField, hz, ↓reduceDIte]
      exact measurable_const
  have := hT.comp ((hu.comp measurable_fst).prodMk (hψ.comp measurable_snd))
  convert this using 1
  funext q
  rw [hr]
  rfl

/-- **The denominator on the outputs** (P7 (3.5)): if the outside field `ψ_y` read off `o` is in the
tube, `∫ dψ_k↾Z₀ r = ∫ du ρ^Z_{k,0}(Z)` (change of variables
`measurePreserving_suppToOutPart`). -/
theorem remDen_eq_integral_rhoZeroRestricted (hβ0 : 0 < β0)
    (hp0 : 1 ≤ cSix S.d D (psiZeroK N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) * p0)
    (hrad : psiZeroK N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ +
      5 * zeroRadius (cSix S.d D (psiZeroK N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H))
        (betaK S.d S.L k β0) p0 ≤ etaDen S.d S.L N D)
    (o : OutT N R a k)
    (hψ : TubeOn G (X \ box b0 w) δ ψo[(remZeroSplit a k Z0 o).2]) :
    remDen a k Z0 r o =
      ∫ u, rhoZeroRestricted G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψ Zr ν h β0 p0 u := by
  set F := rhoZeroRestricted G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψ Zr ν h β0 p0
    with hF
  have hT := measurable_rhoZeroRestrictedTot N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc
    Zr ν h hβ0 hp0 hrad
  have hFm : Measurable F := by
    have := hT.comp (measurable_id.prodMk (measurable_const (a := ψo[(remZeroSplit a k Z0 o).2])))
    convert this using 1
    funext u
    simp [hψ, hF]
  have hu : Measurable fun wv : OutZero N R a k Z0 => uo[wv] := by
    refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr fun p => ?_)
    exact (EuclideanSpace.proj p.2).continuous.measurable.comp (measurable_pi_apply _)
  have hf := measurePreserving_suppToOutPart (S := S) (n := n) (M := M) (K := K) (N := N) (k := k)
    hN (boxFinset (L := S.L) (N₀ := N₀) (k := k) b0 w) (Vblk R a k) (· ∈ Z0) hZ0
  have h1 : remDen a k Z0 r o = ∫ wv, F uo[wv] ∂(outPartMeasure N (Vblk R a k) (· ∈ Z0)) := by
    unfold remDen
    refine integral_congr_ae (Filter.Eventually.of_forall fun wv => ?_)
    simp only [hr, hψ, ↓reduceDIte, hF]
  rw [h1, ← hf.map_eq, integral_map (f := fun wv => F uo[wv]) hf.measurable.aemeasurable
    (hFm.comp hu).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hid : uo[(fun (y : {y : BlockAt S n M K k // y ∈ Vblk R a k ∧ y ∈ Z0}) =>
      (WithLp.toLp 2 (fun i => u (⟨torusCast hN.symm y.1, (hZ0 y.1).1 y.2⟩, i)) :
        EuclideanSpace ℝ (Fin N)))] = u := by
    ext ⟨⟨z, hz⟩, i⟩
    dsimp only
    congr!
    exact torusCast_symm_cast hN z
  show F _ = F u
  rw [hid]

/-- **Positivity of the denominator on the outputs** (Lemma III.8.2, first part). -/
theorem remDen_pos (ha : ∀ j, 0 ≤ aw j) (hν : 0 ≤ ν) (hβ0 : 0 < β0)
    (hp0 : 1 ≤ cSix S.d D (psiZeroK N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) * p0)
    (hrad : psiZeroK N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ +
      5 * zeroRadius (cSix S.d D (psiZeroK N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H))
        (betaK S.d S.L k β0) p0 ≤ etaDen S.d S.L N D)
    (o : OutT N R a k) (hψ : TubeOn G (X \ box b0 w) δ ψo[(remZeroSplit a k Z0 o).2]) :
    0 < remDen a k Z0 r o := by
  rw [remDen_eq_integral_rhoZeroRestricted a hN G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc
    Zr ν h β0 p0 Z0 hZ0 r hr hβ0 hp0 hrad o hψ]
  exact (integrable_rhoZeroRestricted G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψ Zr h ha hν
    hβ0 hp0 hrad).2

/-- **The denominator identity on the outputs** (Lemma III.8.2, the identity): `remDen r o` is
`exp(-β₀ A_Z(ψ⁰_k) - (N/2) log β_k |Z₀| + Ẽ₀^Z)` for the outside field `ψ_y` read off `o`. -/
theorem remDen_eq_exp (ha : ∀ j, 0 ≤ aw j) (hν : 0 ≤ ν) (hβ0 : 0 < β0)
    (hp0 : 1 ≤ cSix S.d D (psiZeroK N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) * p0)
    (hrad : psiZeroK N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ +
      5 * zeroRadius (cSix S.d D (psiZeroK N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H))
        (betaK S.d S.L k β0) p0 ≤ etaDen S.d S.L N D)
    (o : OutT N R a k) (hψ : TubeOn G (X \ box b0 w) δ ψo[(remZeroSplit a k Z0 o).2]) :
    remDen a k Z0 r o =
      Real.exp (-(β0 * actionZ G aw Zr ν h (psiZero N G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψ))
        - (N : ℝ) / 2 * Real.log (betaK S.d S.L k β0) *
          ((boxFinset (L := S.L) (N₀ := N₀) (k := k) b0 w).card : ℝ) +
        tildeE0Restricted G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψ Zr ν h β0 p0) := by
  rw [remDen_eq_integral_rhoZeroRestricted a hN G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc
    Zr ν h β0 p0 Z0 hZ0 r hr hβ0 hp0 hrad o hψ]
  exact (denominatorRestricted_eq G aw hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψ Zr h ha hν
    hβ0 hp0 hrad).1

/-- Off the tube the density vanishes, hence so does the denominator. -/
theorem remDen_eq_zero_of_not_tube (o : OutT N R a k)
    (hψ : ¬ TubeOn G (X \ box b0 w) δ ψo[(remZeroSplit a k Z0 o).2]) : remDen a k Z0 r o = 0 := by
  unfold remDen
  simp [hr, hψ]

end Out

end Balaban.LargeField
