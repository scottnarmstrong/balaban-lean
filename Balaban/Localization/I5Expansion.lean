/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Param
public import Balaban.Localization.PolymerCount
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The resummation step of Theorem I-5 (LOCALIZATION.md §4.4)

Given a function `F u s` of data `u : Ω → E` and decoupling parameters `s : ι → ℂ` satisfying (AE1)
(joint analyticity on `S × {|s i| < e^{κ₁}}` and the bound `Eb e^{-(κ-1)Δ}`) and (AE2) (locality),
`localization_expansion` proves

* `F u 1 = ∑_Y evTerm Y u`, the sum over the domains `Y = Y[𝒞]` of the connected families;
* `evTerm Y u` depends on `u|_Y` only;
* `|evTerm Y u| ≤ Eb e^{-κ₀ Δ - 2κ d̃^cov(Y)}`, from (GM3), (GM4);
* `evTerm Y` is analytic on `S`.

Here `Δ = treeLenCovOne m₀ j X`, `d̃^cov = treeLenCov`, `Y[𝒞] = Ysites`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Analysis Finset

section Expansion

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι] (c : ι → ℕ × CTorus d L N₁ m₁ K)

open Classical in
/-- The connected families `𝒞` with `Y[𝒞] = Y`. -/
noncomputable def connFams (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)
    (X₁ : Set (CTorus d L N₁ m₁ K)) (Y : Set (CTorus d L N₁ m₁ K)) : Finset (Finset ι) :=
  (Finset.univ.filter fun C : Finset ι =>
      IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c X₁) C).filter
    fun C => Ysites G m₀ c X₁ C = Y

variable {U : Type*}

/-- **The terms `𝓔(X, Y)`** of Theorem I-5: `∑_{𝒞 : Y[𝒞] = Y} F_𝒞`. -/
noncomputable def evTerm (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)
    (X₁ : Set (CTorus d L N₁ m₁ K)) (F : U → (ι → ℂ) → ℂ)
    (Y : Set (CTorus d L N₁ m₁ K)) (u : U) : ℂ :=
  ∑ C ∈ connFams c G m₀ X₁ Y, coef (F u) C

omit [DecidableEq ι] in
theorem mem_connFams {X₁ Y : Set (CTorus d L N₁ m₁ K)} {C : Finset ι} :
    C ∈ connFams c G m₀ X₁ Y ↔
      IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c X₁) C ∧ Ysites G m₀ c X₁ C = Y := by
  classical
  simp [connFams]

open Classical in
/-- The domains `Y[𝒞]` of the connected families. -/
noncomputable def domains (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)
    (X₁ : Set (CTorus d L N₁ m₁ K)) : Finset (Set (CTorus d L N₁ m₁ K)) :=
  (Finset.univ.filter fun C : Finset ι =>
      IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c X₁) C).image (Ysites G m₀ c X₁)

variable {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

omit [DecidableEq ι] in
/-- The Peierls sum (GM3) over the families of an arbitrary index type. -/
theorem gm3_fam (hS : CovSetup G m₀ j X 𝒦X) (hc : ∀ i, c i ∈ cubeIdx G)
    (hcinj : Function.Injective c)
    (hdisj : ∀ i, Disjoint (Pset m₁ (c i)) (X1 G m₀ j 𝒦X))
    (Y : Set (CTorus d L N₁ m₁ K)) (κ₂ : ℝ) (h1 : 1 ≤ κ₂ / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ κ₂ / 2) :
    ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) Y, Real.exp (-κ₂ * C.card) ≤ 1 := by
  classical
  let emb : ι ↪ ↥(cubeIdx G) := ⟨fun i => ⟨c i, hc i⟩, fun i i' h => hcinj (congrArg Subtype.val h)⟩
  have hmapinj : Function.Injective (fun C : Finset ι => C.map emb) := Finset.map_injective emb
  have := gm3 (G := G) (m₀ := m₀) hS.polySetup Y
    ((connFams c G m₀ (X1 G m₀ j 𝒦X) Y).image fun C => C.map emb) ?_ κ₂ h1 hlog
  · rw [Finset.sum_image (fun C _ C' _ h => hmapinj h)] at this
    simpa [Finset.card_map] using this
  · intro C' hC'
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hC'
    obtain ⟨-, hY⟩ := (mem_connFams c).1 hC
    refine ⟨?_, fun i hi => ?_⟩
    · rw [← hY]
      unfold Ysites
      congr 1
      ext x
      simp only [Set.mem_iUnion, Finset.mem_map, exists_prop]
      constructor
      · rintro ⟨i, ⟨i0, hi0, rfl⟩, hx⟩
        exact ⟨i0, hi0, hx⟩
      · rintro ⟨i0, hi0, hx⟩
        exact ⟨emb i0, ⟨i0, hi0, rfl⟩, hx⟩
    · obtain ⟨i0, -, rfl⟩ := Finset.mem_map.1 hi
      exact hdisj i0

variable [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- **The resummation step of Theorem I-5** (LOCALIZATION.md §4.4, after (AE1), (AE2)). -/
theorem localization_expansion (hS : CovSetup G m₀ j X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hc : ∀ i, c i ∈ cubeIdx G) (hcinj : Function.Injective c)
    (hdisj : ∀ i, Disjoint (Pset m₁ (c i)) (X1 G m₀ j 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κ κ₀ κ₁ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁)
    (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {S : Set U} {F : U → (ι → ℂ) → ℂ}
    {Ag : Finset ι → U → U → Prop} {AgY : Set (CTorus d L N₁ m₁ K) → U → U → Prop}
    (hrefl : ∀ C u, u ∈ S → Ag C u u)
    (hlink : ∀ C u u', AgY (Ysites G m₀ c (X1 G m₀ j 𝒦X) C) u u' → Ag C u u')
    (hana : AnalyticOnNhd ℂ (fun p : U × (ι → ℂ) => F p.1 p.2)
      (S ×ˢ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁)))
    (hbd : ∀ u ∈ S, ∀ s ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁),
      ‖F u s‖ ≤ Eb * Real.exp (-(κ - 1) * treeLenCovOne m₀ j X))
    (hloc : LocalityAEOn (Real.exp κ₁) S (fun i => Pset m₁ (c i)) (compY c (X1 G m₀ j 𝒦X)) Ag F) :
    (∀ u ∈ S, F u 1 = ∑ Y ∈ domains c G m₀ (X1 G m₀ j 𝒦X), evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u) ∧
    (∀ Y, ∀ u ∈ S, ∀ u' ∈ S, AgY Y u u' →
      evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u = evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u') ∧
    (∀ Y, ∀ u ∈ S, ‖evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u‖ ≤
      Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κ * treeLenCov G m₀ Y)) ∧
    (∀ Y, AnalyticOnNhd ℂ (evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y) S) := by
  classical
  have hκ1 : 1 ≤ κ₁ := by
    have h0 : (0 : ℝ) ≤ 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) := by positivity
    have : (1 : ℝ) ≤ 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) := by
      have hd1 : (3 : ℝ) ≤ d := by exact_mod_cast hd
      have : (1 : ℝ) ≤ (((2 * L + 1) ^ d : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_pow _ _ (by omega)
      nlinarith
    nlinarith
  have hanau : ∀ u ∈ S, AnalyticOnNhd ℂ (F u) (polydisc (0 : ι → ℂ) (fun _ => Real.exp κ₁)) := by
    intro u hu s hs
    exact (hana (u, s) ⟨hu, hs⟩).comp (g := fun p : U × (ι → ℂ) => F p.1 p.2)
      (f := fun s' : ι → ℂ => (u, s')) ((analyticAt_const (𝕜 := ℂ)).prod (analyticAt_id (𝕜 := ℂ)))
  obtain ⟨hsum, -, hcong, hbound⟩ := abstract_expansion_on (S := S) (P := fun i => Pset m₁ (c i))
    (Yc := compY c (X1 G m₀ j 𝒦X)) (Ag := Ag) (F := F) hκ1 hanau hbd hloc hrefl
  refine ⟨fun u hu => ?_, fun Y u hu u' hu' huu => ?_, fun Y u hu => ?_, fun Y => ?_⟩
  · rw [hsum u hu]
    unfold domains evTerm
    rw [← Finset.sum_fiberwise_of_maps_to (g := Ysites G m₀ c (X1 G m₀ j 𝒦X))
      (t := (Finset.univ.filter fun C : Finset ι =>
        IsConnectedFamily (fun i => Pset m₁ (c i)) (compY c (X1 G m₀ j 𝒦X)) C).image
          (Ysites G m₀ c (X1 G m₀ j 𝒦X)))
      (fun C hC => Finset.mem_image_of_mem _ hC)]
    rfl
  · unfold evTerm
    refine Finset.sum_congr rfl fun C hC => hcong C u u' hu hu' (hlink C u u' ?_)
    obtain ⟨-, hY⟩ := (mem_connFams c).1 hC
    rw [hY]; exact huu
  · set Δ := treeLenCovOne m₀ j X with hΔ
    set T := treeLenCov G m₀ Y with hT
    have hterm : ∀ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) Y,
        ‖coef (F u) C‖ ≤ Eb * Real.exp (-κ₀ * Δ - 2 * κ * T) *
          Real.exp (-(κ₁ / 2 - 1) * C.card) := by
      intro C hC
      obtain ⟨hconn, hY⟩ := (mem_connFams c).1 hC
      have h4 := gm4 hS hd hL hc C hconn hopt κ κ₀ κ₁ hκ₀ hκ hκ₁
      rw [hY] at h4
      refine (hbound u hu C).trans ?_
      rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hEb
      nlinarith [h4]
    calc ‖evTerm c G m₀ (X1 G m₀ j 𝒦X) F Y u‖
        ≤ ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) Y, ‖coef (F u) C‖ := norm_sum_le _ _
      _ ≤ ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) Y, Eb * Real.exp (-κ₀ * Δ - 2 * κ * T) *
          Real.exp (-(κ₁ / 2 - 1) * C.card) := Finset.sum_le_sum hterm
      _ = Eb * Real.exp (-κ₀ * Δ - 2 * κ * T) *
          ∑ C ∈ connFams c G m₀ (X1 G m₀ j 𝒦X) Y, Real.exp (-(κ₁ / 2 - 1) * C.card) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ Eb * Real.exp (-κ₀ * Δ - 2 * κ * T) * 1 :=
          mul_le_mul_of_nonneg_left (gm3_fam c hS hc hcinj hdisj Y _ h1 hlog)
            (by positivity)
      _ = _ := mul_one _
  · intro a ha
    unfold evTerm
    exact Finset.analyticAt_fun_sum _ fun C _ =>
      analyticOnNhd_coef_of_analyticOnNhd (Φ := fun p : U × (ι → ℂ) =>
        F p.1 p.2) (Real.one_lt_exp_iff.mpr (by linarith)) hana C a ha

end Expansion

end Balaban.Localization
