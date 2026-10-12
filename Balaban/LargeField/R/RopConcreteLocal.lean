/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.Denominator

/-!
# Locality of the reference density (Lemma III.1.5, Definition III.5.1, used in Lemma III.8.4)

The effective action `effAction` of a block field reads the field only on the blocks `jBlock x`, `x ∈ dataSites G`
(`effAction_congr`), and the tube `TubeOn G X δ` only on the blocks of `X` (`tubeOn_congr`).  Since the data sites of
the generating set of `U_k` lie over `X ⊇ U^∼_k` (`hdata`), the unique solution `ψ⁰_k` of (2.34) and the reference
density `ρ_{k,0}(Z)` of Definition III.8.1 read the fixed outside field only on `X ∖ Z₀`:

* `psiZero_congr`: `ψ⁰_k(ψ_k)` and `ψ⁰_k(ψ'_k)` agree on `X` when `ψ_k = ψ'_k` on `X ∖ Z₀`;
* `rhoZero_congr`: `ρ_{k,0}(Z)` (`rhoZero`) is the same function of `u = ψ_k↾Z₀` for `ψ_k` and `ψ'_k` agreeing on `X ∖ Z₀`.

The conventions of the landed objects (`effAction`, `psiZero`, `rhoZero`) are used unchanged: the massless reference
convention of P7.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open Balaban Balaban.Multiscale Balaban.Background

namespace Balaban.LargeField

section Loc
variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)

theorem dataR_congr {ψ ψ' : BlockField d L N₀ k N}
    (h : ∀ x ∈ dataSites G, ψ (jBlock d L N₀ k k x) = ψ' (jBlock d L N₀ k k x)) :
    dataR G ψ = dataR G ψ' := by
  classical
  have hΨ : (dataR G ψ).Ψ = (dataR G ψ').Ψ := by
    funext x i
    by_cases hx : x ∈ dataSites G
    · rw [dataR_Ψ G ψ hx, dataR_Ψ G ψ' hx]; simp [liftR, h x hx]
    · rw [(dataR G ψ).Ψ_zero x hx, (dataR G ψ').Ψ_zero x hx]
  have hh : (dataR G ψ).h = (dataR G ψ').h := rfl
  cases hA : dataR G ψ
  cases hB : dataR G ψ'
  rw [hA, hB] at hΨ hh
  simp only at hΨ hh
  subst hΨ hh
  rfl

theorem effAction_congr {ψ ψ' : BlockField d L N₀ k N}
    (h : ∀ x ∈ dataSites G, ψ (jBlock d L N₀ k k x) = ψ' (jBlock d L N₀ k k x)) :
    effAction G a ψ = effAction G a ψ' := by
  unfold effAction
  rw [dataR_congr G h]

theorem tubeOn_congr {X : Set (Torus d (N₀ * L ^ (k - k)))} {δ : ℝ} {ψ ψ' : BlockField d L N₀ k N}
    (h : ∀ z ∈ X, ψ z = ψ' z) : TubeOn G X δ ψ ↔ TubeOn G X δ ψ' := by
  have hl : ∀ x, jBlock d L N₀ k k x ∈ X → liftR ψ x = liftR ψ' x := fun x hx => by
    funext i; simp [liftR, h _ hx]
  unfold TubeOn
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x x' hp hx hx' => ?_, fun x hx hX => ?_⟩
    · rw [← hl x hx, ← hl x' hx']; exact h1 x x' hp hx hx'
    · rw [← h _ hX]; exact h2 x hx hX
  · rintro ⟨h1, h2⟩
    refine ⟨fun x x' hp hx hx' => ?_, fun x hx hX => ?_⟩
    · rw [hl x hx, hl x' hx']; exact h1 x x' hp hx hx'
    · rw [h _ hX]; exact h2 x hx hX

variable [NeZero N] {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)

include hd hk hw1 hwD hm hXreg hΩ hdata H in
theorem psiZero_congr {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk ψk' : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (hψk' : TubeOn G (X \ box b0 w) δ ψk')
    (h : ∀ z ∈ X \ box b0 w, ψk z = ψk' z) :
    ∀ z ∈ X, psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk' z =
      psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk z := by
  classical
  obtain ⟨⟨hT, hoff, hmin⟩, -⟩ := psiZero_spec N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk
  set ψ0 := psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk with hψ0
  set κ := psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H * δ with hκ
  have hwin : ∀ ψ ψ' : BlockField d L N₀ k N, (∀ z ∈ X, ψ z = ψ' z) →
      effAction G a ψ = effAction G a ψ' := fun ψ ψ' hh =>
    effAction_congr G a fun x hx => hh _ (hdata x hx)
  set ψt : BlockField d L N₀ k N := fun z => if z ∈ X then ψ0 z else ψk' z with hψt
  have hsol : PsiZeroSol G a b0 w X κ ψk' ψt := by
    refine ⟨(tubeOn_congr G (fun z hz => by simp [hψt, hz])).2 hT, fun z hz => ?_, fun ψ' hT' hoff' => ?_⟩
    · by_cases hzX : z ∈ X
      · simp only [hψt, hzX, ite_true]
        rw [hoff z hz]; exact h z ⟨hzX, hz⟩
      · simp [hψt, hzX]
    · set ψ'' : BlockField d L N₀ k N := fun z => if z ∈ X then ψ' z else ψk z with hψ''
      have hT'' : TubeOn G X κ ψ'' := (tubeOn_congr G (fun z hz => by simp [hψ'', hz])).2 hT'
      have hoff'' : ∀ z, z ∉ box b0 w → ψ'' z = ψk z := fun z hz => by
        by_cases hzX : z ∈ X
        · simp only [hψ'', hzX, ite_true]
          rw [hoff' z hz]; exact (h z ⟨hzX, hz⟩).symm
        · simp [hψ'', hzX]
      have := hmin ψ'' hT'' hoff''
      rw [hwin ψt ψ0 (fun z hz => by simp [hψt, hz]), hwin ψ' ψ'' (fun z hz => by simp [hψ'', hz])]
      exact this
  intro z hz
  have := (psiZero_spec N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk').2 ψt hsol
  rw [← this]; simp [hψt, hz]

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **Locality of the reference density** (Definition III.8.1, Lemma III.1.5): `ρ_{k,0}(Z)` as a function of
`u = ψ_k↾Z₀` depends on the outside field `ψ_k` only through `ψ_k↾(X ∖ Z₀)`. -/
theorem rhoZero_congr {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk ψk' : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) (hψk' : TubeOn G (X \ box b0 w) δ ψk')
    (h : ∀ z ∈ X \ box b0 w, ψk z = ψk' z) (β p0 : ℝ) :
    rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk' β p0 =
      rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 := by
  funext u
  have hbX : ∀ z ∈ box b0 w, z ∈ X := fun z hz => hXreg (Or.inl hz)
  have hps := psiZero_congr G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hψk' h
  have hcut : ZeroCutoff (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk')
      (zeroRadius (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) β p0) u ↔
      ZeroCutoff (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)
      (zeroRadius (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) β p0) u := by
    unfold ZeroCutoff
    refine forall_congr' fun z => ?_
    have hz : (z : Torus d (N₀ * L ^ (k - k))) ∈ X := hbX _ (mem_boxFinset.1 z.2)
    rw [hps _ hz]
  have hact : effActionNorm G a (mergeField (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) ψk' u) =
      effActionNorm G a (mergeField (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) ψk u) := by
    unfold effActionNorm
    congr 1
    refine effAction_congr G a fun x hx => ?_
    have hxX := hdata x hx
    by_cases hz : jBlock d L N₀ k k x ∈ box b0 w
    · have hz' := mem_boxFinset.2 hz
      funext i
      rw [mergeField_of_mem hz' i, mergeField_of_mem hz' i]
    · have hz' : jBlock d L N₀ k k x ∉ boxFinset (L := L) (N₀ := N₀) (k := k) b0 w :=
        fun hh => hz (mem_boxFinset.1 hh)
      rw [mergeField_of_not_mem hz', mergeField_of_not_mem hz']
      exact (h _ ⟨hxX, hz⟩).symm
  unfold rhoZero rhoZeroWith chiZeroCut
  rw [hact]
  by_cases hc : ZeroCutoff (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)
      (zeroRadius (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) β p0) u
  · simp [hc, hcut.2 hc]
  · simp [hc, mt hcut.1 hc]

end Loc


end Balaban.LargeField
