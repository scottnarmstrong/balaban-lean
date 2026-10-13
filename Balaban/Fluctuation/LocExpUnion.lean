/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormExpInputOn
public import Balaban.Fluctuation.RenormLocFibre
public import Balaban.Fluctuation.Prop33Level
public import Balaban.SmallField.Def6Terms

/-!
# Localized expansions on a common finite family of domains

Generic lemmas about `IsLocExp` and `HasLocPrinciple`: extension by zero to a larger finite family
of domains, the sum of two expansions on the union of their families, and a change of the size
functional (in particular `renDY = sizeJ` at a generating set of a given level).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization

section Union

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {Dom : BgData G N → Prop} {r κ B B₁ B₂ : ℝ}
  {Ys Ys' Ys₁ Ys₂ : Finset (Finset (Torus d (N₀ * L ^ k)))}
  {dY dY' : Finset (Torus d (N₀ * L ^ k)) → ℝ} {f f₁ f₂ : BgData G N → (Fin 3 → ℂ) → E}
  {term term₁ term₂ :
    Finset (Torus d (N₀ * L ^ k)) → RawData d L N₀ k N × (Fin 3 → ℂ) → E}

open Classical in
/-- **Zero extension.** An expansion over `Ys` is an expansion over every larger family `Ys'`, with
the terms set to zero off `Ys`. -/
theorem IsLocExp.extend (h : IsLocExp G Dom r Ys dY κ B f term) (hs : Ys ⊆ Ys') (hB : 0 ≤ B) :
    IsLocExp G Dom r Ys' dY κ B f (fun Y q => if Y ∈ Ys then term Y q else 0) where
  sum_eq D hD ξ hξ := by
    rw [h.sum_eq D hD ξ hξ, ← Finset.sum_subset hs]
    · exact Finset.sum_congr rfl fun Y hY => by simp [hY]
    · intro Y _ hY
      simp [hY]
  analytic Y hY := by
    by_cases hm : Y ∈ Ys
    · simpa [hm] using h.analytic Y hm
    · simpa [hm] using analyticOnNhd_const
  local_ Y hY q hq q' hq' h2 hag := by
    by_cases hm : Y ∈ Ys
    · simpa [hm] using h.local_ Y hm q hq q' hq' h2 hag
    · simp [hm]
  bound Y hY q hq := by
    by_cases hm : Y ∈ Ys
    · simpa [hm] using h.bound Y hm q hq
    · simpa [hm] using mul_nonneg hB (Real.exp_pos _).le

/-- **Zero extension, term already zero off `Ys`.** -/
theorem IsLocExp.extend_of_zero (h : IsLocExp G Dom r Ys dY κ B f term) (hs : Ys ⊆ Ys')
    (hB : 0 ≤ B) (hz : ∀ Y, Y ∉ Ys → ∀ q, term Y q = 0) :
    IsLocExp G Dom r Ys' dY κ B f term := by
  classical
  have := h.extend hs hB
  have e : (fun Y q => if Y ∈ Ys then term Y q else 0) = term := by
    funext Y q
    by_cases hm : Y ∈ Ys
    · simp [hm]
    · simp [hm, hz Y hm q]
  rwa [e] at this

open Classical in
/-- **The sum on the union of two families.** -/
theorem IsLocExp.add_union (h₁ : IsLocExp G Dom r Ys₁ dY κ B₁ f₁ term₁)
    (h₂ : IsLocExp G Dom r Ys₂ dY κ B₂ f₂ term₂) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) :
    IsLocExp G Dom r (Ys₁ ∪ Ys₂) dY κ (B₁ + B₂) (fun D ξ => f₁ D ξ + f₂ D ξ)
      (fun Y q => (if Y ∈ Ys₁ then term₁ Y q else 0) +
        (if Y ∈ Ys₂ then term₂ Y q else 0)) :=
  (h₁.extend Finset.subset_union_left hB₁).add (h₂.extend Finset.subset_union_right hB₂)

/-- **Change of the size functional**: a pointwise smaller size gives the same expansion with a
weaker bound (nonnegative rate and constant). -/
theorem IsLocExp.congr_dY (h : IsLocExp G Dom r Ys dY κ B f term) (hκ : 0 ≤ κ) (hB : 0 ≤ B)
    (hd : ∀ Y ∈ Ys, dY' Y ≤ dY Y) : IsLocExp G Dom r Ys dY' κ B f term :=
  { h with
    bound := fun Y hY q hq => (h.bound Y hY q hq).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by nlinarith [hd Y hY])) hB) }

end Union

section Eq

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {Dom : BgData G N → Prop} {r κ B : ℝ}
  {Ys : Finset (Finset (Torus d (N₀ * L ^ k)))}
  {dY dY' : Finset (Torus d (N₀ * L ^ k)) → ℝ} {f : BgData G N → (Fin 3 → ℂ) → E}
  {term : Finset (Torus d (N₀ * L ^ k)) → RawData d L N₀ k N × (Fin 3 → ℂ) → E}

/-- A change of the size functional that agrees on `Ys`. -/
theorem IsLocExp.congr_dY_eq (h : IsLocExp G Dom r Ys dY κ B f term)
    (hd : ∀ Y ∈ Ys, dY Y = dY' Y) : IsLocExp G Dom r Ys dY' κ B f term :=
  { h with
    bound := fun Y hY q hq => by rw [← hd Y hY]; exact h.bound Y hY q hq }

end Eq

section Principle

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Type*}
  {Dom : BgData G N → Prop} {r κ Kloc : ℝ}
  {Ys Ys' : Finset (Finset (Torus d (N₀ * L ^ k)))}
  {dY : Finset (Torus d (N₀ * L ^ k)) → ℝ}
  {Kcl : BgData G N → (Fin 3 → ℂ) → Set U} {f : BgData G N → U → (Fin 3 → ℂ) → E}
  {u : BgData G N → (Fin 3 → ℂ) → U}

/-- **Zero extension of a localization principle.**  The class is assumed nonempty at every datum
of the domain and every `ξ` of the polydisc (so that the bound `M` is nonnegative), and
`0 ≤ Kloc`. -/
theorem HasLocPrinciple.extend (h : HasLocPrinciple G Dom r Ys dY κ Kloc Kcl f u)
    (hs : Ys ⊆ Ys') (hK : 0 ≤ Kloc)
    (hne : ∀ D : BgData G N, Dom D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r → (Kcl D ξ).Nonempty) :
    HasLocPrinciple G Dom r Ys' dY κ Kloc Kcl f u := by
  classical
  obtain ⟨term, hsum, han, hloc, hbd⟩ := h
  refine ⟨fun Y q => if Y ∈ Ys then term Y q else 0, ?_, ?_, ?_, ?_⟩
  · intro D hD ξ hξ
    rw [hsum D hD ξ hξ, ← Finset.sum_subset hs]
    · exact Finset.sum_congr rfl fun Y hY => by simp [hY]
    · intro Y _ hY
      simp [hY]
  · intro Y hY
    by_cases hm : Y ∈ Ys
    · simpa [hm] using han Y hm
    · simpa [hm] using analyticOnNhd_const
  · intro Y hY q hq q' hq' h2 hag
    by_cases hm : Y ∈ Ys
    · simpa [hm] using hloc Y hm q hq q' hq' h2 hag
    · simp [hm]
  · intro ξ hξ M hM Y hY D hD
    by_cases hm : Y ∈ Ys
    · simpa [hm] using hbd ξ hξ M hM Y hm D hD
    · obtain ⟨v, hv⟩ := hne D hD ξ hξ
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM D hD v hv)
      simpa [hm] using mul_nonneg (mul_nonneg hK hM0) (Real.exp_pos _).le

end Principle

section RenDY

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {lev : ℕ}

/-- **`renDY = sizeJ` at a generating set of level `lev`**, on every finset of sites. -/
theorem renDY_eq_sizeJ (hG : IsLevel G lev) (m₀ : ℕ) (Y : Finset (CTorus d L N₁ m₁ K)) :
    renDY G m₀ Y = Balaban.SmallField.Def6.sizeJ m₀ lev (↑Y : Set (CTorus d L N₁ m₁ K)) :=
  treeLenCov_eq_treeLenCovOne hG m₀ _

end RenDY

end Balaban.Fluctuation
