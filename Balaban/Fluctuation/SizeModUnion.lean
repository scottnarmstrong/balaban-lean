/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SizeModCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (G3): unions (FLUCTUATION.md Lemma 1.2)

* `linked_box_direct`: two points of a box contained in a region are joined, inside the box, at
  cost `d s c` (`s` the side, `c` a bound for the bond weights).
* `exists_union_admissible`: admissible pairs for `X₁, X₂` sharing a site of `Ω` give an
  admissible pair for `X₁ ∪ X₂` of cost at most the sum plus `2 d L`.
* `G3_dcov`, `G3_dOmega`: the two forms of (G3), with `c_G = 2 d L`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization

section Direct

variable {d n : ℕ}

/-- Two points of a box inside the region `R` are joined inside `R` at cost `d s c`. -/
theorem linked_box_direct {R : Set (Torus d n)} {ω : Torus d n → Torus d n → ℝ}
    (hω : ∀ x y, 0 ≤ ω x y) (b : Torus d n) (s : ℕ) {c : ℝ} (hbox : box b s ⊆ R)
    (hc : ∀ x ∈ R, ∀ y ∈ R, ω x y ≤ c) {x y : Torus d n} (hx : x ∈ box b s)
    (hy : y ∈ box b s) : Linked R ω (d * s * c) x y := by
  have hbR : b ∈ R := hbox (by
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨0, fun μ => by simpa using (lt_of_le_of_lt (Nat.zero_le _) (hw μ)), by simp [natT_zero]⟩)
  have hc0 : 0 ≤ c := (hω b b).trans (hc b hbR b hbR)
  obtain ⟨wx, hwx, rfl⟩ := hx
  obtain ⟨wy, hwy, rfl⟩ := hy
  set m : Fin d → ℕ := fun μ => min (wx μ) (wy μ) with hm
  have key : ∀ w : Fin d → ℕ, (∀ μ, w μ < s) → (∀ μ, m μ ≤ w μ) →
      Linked R ω ((∑ μ, (w - m) μ : ℕ) * c) (b + natT m) (b + natT w) := by
    intro w hw hmw
    have h := linked_box hω (b + natT m) (w - m) (c := c) (fun w' hw' => by
      refine hbox ⟨m + w', fun μ => ?_, by rw [natT_add, add_assoc]⟩
      have := hw' μ
      have := hw μ
      have := hmw μ
      simp only [Pi.add_apply, Pi.sub_apply] at *
      omega) hc
    have e : b + natT m + natT (w - m) = b + natT w := by
      rw [add_assoc, ← natT_add]
      congr 2
      funext μ
      have := hmw μ
      simp only [Pi.add_apply, Pi.sub_apply]
      omega
    rwa [e] at h
  have h1 := key wx hwx (fun μ => min_le_left _ _)
  have h2 := key wy hwy (fun μ => min_le_right _ _)
  have h3 := Linked.trans hω h1.symm h2
  refine Covers.mono_c h3 ?_
  have hsum : (∑ μ, (wx - m) μ) + (∑ μ, (wy - m) μ) ≤ d * s := by
    rw [← Finset.sum_add_distrib]
    calc _ ≤ ∑ _μ : Fin d, s := Finset.sum_le_sum fun μ _ => by
          have := hwx μ
          have := hwy μ
          simp only [Pi.sub_apply, hm]
          omega
      _ = d * s := by simp
  have hsumR : (((∑ μ, (wx - m) μ : ℕ) : ℝ)) + ((∑ μ, (wy - m) μ : ℕ) : ℝ) ≤ d * s := by
    exact_mod_cast hsum
  nlinarith

end Direct

section Union

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

/-- The constant `c_G = 2 d L` of (G3). -/
def cG (d L : ℕ) : ℝ := 2 * d * L

omit [NeZero N₁] in
/-- **Union of admissible pairs.** -/
theorem exists_union_admissible {Ω X₁ X₂ 𝒦₁ 𝒦₂ : Set (CTorus d L N₁ m₁ K)}
    {W₁ W₂ : Finset (CTorus d L N₁ m₁ K)}
    {E₁ E₂ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)}
    (h₁ : ModAdmissible m₀ j Ω X₁ 𝒦₁ W₁ E₁) (h₂ : ModAdmissible m₀ j Ω X₂ 𝒦₂ W₂ E₂)
    {t : CTorus d L N₁ m₁ K} (ht1 : t ∈ X₁) (ht2 : t ∈ X₂) (htΩ : t ∈ Ω) :
    ∃ 𝒦 W E, ModAdmissible m₀ j Ω (X₁ ∪ X₂) 𝒦 W E ∧
      bondCost (scaleW L m₀ m₁ j) E ≤
        bondCost (scaleW L m₀ m₁ j) E₁ + bondCost (scaleW L m₀ m₁ j) E₂ + cG d L := by
  set a := cellSide L m₀ m₁ j with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ j
  have hLa : 0 < L * a := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) ha0
  obtain ⟨hK₁, hcov₁, hc₁, hW₁, hm₁⟩ := h₁
  obtain ⟨hK₂, hcov₂, hc₂, hW₂, hm₂⟩ := h₂
  obtain ⟨q₁, hq₁, htq₁⟩ := Set.mem_iUnion₂.1 (hcov₁ ⟨ht1, htΩ⟩)
  obtain ⟨q₂, hq₂, htq₂⟩ := Set.mem_iUnion₂.1 (hcov₂ ⟨ht2, htΩ⟩)
  obtain ⟨x₁, hx₁W, hx₁q⟩ := hm₁ q₁ hq₁
  obtain ⟨x₂, hx₂W, hx₂q⟩ := hm₂ q₂ hq₂
  set R : Set (CTorus d L N₁ m₁ K) := X₁ ∪ X₂ with hR
  set ω := scaleW L m₀ m₁ j (α := CTorus d L N₁ m₁ K) with hω
  set c : ℝ := ((L : ℝ) ^ (m₀ + m₁ + j))⁻¹ with hcdef
  have hω0 : ∀ x y, 0 ≤ ω x y := fun x y => by simp only [hω, scaleW]; positivity
  have hωc : ∀ x ∈ R, ∀ y ∈ R, ω x y ≤ c := fun x _ y _ => le_refl _
  have haR : (a : ℝ) = (L : ℝ) ^ (m₀ + m₁ + j) := by
    rw [ha]; unfold cellSide; push_cast; congr 1; ring
  have hcost : (d : ℝ) * ((L * a : ℕ) : ℝ) * c = d * L := by
    have hLpos : (0 : ℝ) < (L : ℝ) ^ (m₀ + m₁ + j) := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    push_cast
    rw [haR, hcdef]
    field_simp
  have hbox₁ : box q₁ (L * a) ⊆ R := (hK₁ q₁ hq₁).2.trans Set.subset_union_left
  have hbox₂ : box q₂ (L * a) ⊆ R := (hK₂ q₂ hq₂).2.trans Set.subset_union_right
  have L1 : Linked R ω (d * ((L * a : ℕ) : ℝ) * c) x₁ t :=
    linked_box_direct hω0 q₁ (L * a) hbox₁ hωc hx₁q htq₁
  have L2 : Linked R ω (d * ((L * a : ℕ) : ℝ) * c) t x₂ :=
    linked_box_direct hω0 q₂ (L * a) hbox₂ hωc htq₂ hx₂q
  rw [hcost] at L1 L2
  have C1 : Covers R ω (bondCost ω E₁) W₁ :=
    ⟨W₁, E₁, hc₁, hW₁.trans Set.subset_union_left, subset_rfl, le_rfl⟩
  have C2 : Covers R ω (bondCost ω E₂) W₂ :=
    ⟨W₂, E₂, hc₂, hW₂.trans Set.subset_union_right, subset_rfl, le_rfl⟩
  have J1 := Covers.join hω0 C1 L1 ⟨x₁, hx₁W, by simp⟩
  have J2 := Covers.join hω0 J1 L2 ⟨t, by simp, by simp⟩
  have J3 := Covers.join hω0 J2 C2 ⟨x₂, by simp, hx₂W⟩
  obtain ⟨W, E, hc, hWR, hA, hcost'⟩ := J3
  have hA₁ : W₁ ⊆ W := fun x hx => hA (by simp [hx])
  have hA₂ : W₂ ⊆ W := fun x hx => hA (by simp [hx])
  refine ⟨𝒦₁ ∪ 𝒦₂, W, E, ⟨?_, ?_, hc, hWR, ?_⟩, by unfold cG; linarith⟩
  · rintro b (hb | hb)
    · exact ⟨(hK₁ b hb).1, (hK₁ b hb).2.trans Set.subset_union_left⟩
    · exact ⟨(hK₂ b hb).1, (hK₂ b hb).2.trans Set.subset_union_right⟩
  · rintro z ⟨hz | hz, hzΩ⟩
    · obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 (hcov₁ ⟨hz, hzΩ⟩)
      exact Set.mem_iUnion₂.2 ⟨b, Or.inl hb, hzb⟩
    · obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.1 (hcov₂ ⟨hz, hzΩ⟩)
      exact Set.mem_iUnion₂.2 ⟨b, Or.inr hb, hzb⟩
  · rintro b (hb | hb)
    · obtain ⟨x, hx, hxb⟩ := hm₁ b hb
      exact ⟨x, hA₁ hx, hxb⟩
    · obtain ⟨x, hx, hxb⟩ := hm₂ b hb
      exact ⟨x, hA₂ hx, hxb⟩

omit [NeZero N₁] [NeZero L] in
/-- Two nearest-neighbour-connected sets with a common site have connected union. -/
theorem siteConnected_union {X₁ X₂ : Set (CTorus d L N₁ m₁ K)} (h₁ : SiteConnected X₁)
    (h₂ : SiteConnected X₂) {t : CTorus d L N₁ m₁ K} (ht1 : t ∈ X₁) (ht2 : t ∈ X₂) :
    SiteConnected (X₁ ∪ X₂) := by
  have hsymm : ∀ a b : CTorus d L N₁ m₁ K,
      (a ∈ X₁ ∪ X₂ ∧ b ∈ X₁ ∪ X₂ ∧ Nbr a b) → (b ∈ X₁ ∪ X₂ ∧ a ∈ X₁ ∪ X₂ ∧ Nbr b a) :=
    fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩
  have reach : ∀ x ∈ X₁ ∪ X₂, Relation.ReflTransGen
      (fun u v => u ∈ X₁ ∪ X₂ ∧ v ∈ X₁ ∪ X₂ ∧ Nbr u v) x t := by
    rintro x (hx | hx)
    · exact Relation.ReflTransGen.mono (fun u v h => ⟨Or.inl h.1, Or.inl h.2.1, h.2.2⟩) x t
        (h₁ x hx t ht1)
    · exact Relation.ReflTransGen.mono (fun u v h => ⟨Or.inr h.1, Or.inr h.2.1, h.2.2⟩) x t
        (h₂ x hx t ht2)
  intro x hx y hy
  exact (reach x hx).trans (rtg_symm hsymm (reach y hy))

omit [NeZero N₁] [NeZero L] in
/-- `𝒟_j(mod Ω^c)` is stable under unions of overlapping sets. -/
theorem DjMod_union {Ω X₁ X₂ : Set (CTorus d L N₁ m₁ K)} (h₁ : DjMod m₀ j Ω X₁)
    (h₂ : DjMod m₀ j Ω X₂) {t : CTorus d L N₁ m₁ K} (ht1 : t ∈ X₁) (ht2 : t ∈ X₂) :
    DjMod m₀ j Ω (X₁ ∪ X₂) := by
  refine ⟨⟨⟨t, Or.inl ht1⟩, ?_, siteConnected_union h₁.1.2.2 h₂.1.2.2 ht1 ht2⟩, ?_⟩
  · rintro z (hz | hz)
    · obtain ⟨b, hb1, hb2, hb3⟩ := h₁.1.2.1 z hz
      exact ⟨b, hb1, hb2, hb3.trans Set.subset_union_left⟩
    · obtain ⟨b, hb1, hb2, hb3⟩ := h₂.1.2.1 z hz
      exact ⟨b, hb1, hb2, hb3.trans Set.subset_union_right⟩
  · intro z hz
    rcases h₁.2 z hz with h | h
    · exact Or.inl (h.trans Set.subset_union_left)
    · rcases h₂.2 z hz with h' | h'
      · exact Or.inl (h'.trans Set.subset_union_right)
      · exact Or.inr (Set.disjoint_union_right.2 ⟨h, h'⟩)

/-- **(G3), first form.**  If `X₁ ∩ X₂` contains a `π_j`-cube of `Ω`, then
`X₁ ∪ X₂ ∈ 𝒟_j(mod Ω^c)` and
`d^cov_j(X₁ ∪ X₂ mod Ω^c) ≤ d^cov_j(X₁ mod Ω^c) + d^cov_j(X₂ mod Ω^c) + c_G`. -/
theorem G3_dcov {Ω X₁ X₂ : Set (CTorus d L N₁ m₁ K)} (h₁ : DjMod m₀ j Ω X₁)
    (h₂ : DjMod m₀ j Ω X₂)
    (hcube : ∃ t, Aligned (cellSide L m₀ m₁ j) t ∧ box t (cellSide L m₀ m₁ j) ⊆ X₁ ∩ X₂ ∩ Ω) :
    DjMod m₀ j Ω (X₁ ∪ X₂) ∧
      dcovMod m₀ j Ω (X₁ ∪ X₂) ≤ dcovMod m₀ j Ω X₁ + dcovMod m₀ j Ω X₂ + cG d L := by
  obtain ⟨t, -, ht⟩ := hcube
  have ht' : t ∈ X₁ ∩ X₂ ∩ Ω := ht (mem_box_self t (cellSide_pos m₀ m₁ j))
  refine ⟨DjMod_union h₁ h₂ ht'.1.1 ht'.1.2, ?_⟩
  obtain ⟨𝒦₁, W₁, E₁, hA₁, he₁⟩ := exists_admissible_eq_dcovMod (exists_admissible_of_IsDj (Ω := Ω) h₁.1)
  obtain ⟨𝒦₂, W₂, E₂, hA₂, he₂⟩ := exists_admissible_eq_dcovMod (exists_admissible_of_IsDj (Ω := Ω) h₂.1)
  obtain ⟨𝒦, W, E, hA, hc⟩ := exists_union_admissible hA₁ hA₂ ht'.1.1 ht'.1.2 ht'.2
  rw [← he₁, ← he₂]
  exact (dcovMod_le_of_admissible hA).trans hc

omit [NeZero N₁] [NeZero L] in
/-- `Ŷ` commutes with unions. -/
theorem Yhat_union (Ω S₁ S₂ : Set (CTorus d L N₁ m₁ K)) :
    Yhat Ω (S₁ ∪ S₂) = Yhat Ω S₁ ∪ Yhat Ω S₂ := by
  ext y
  simp only [Yhat, Set.mem_union]
  constructor
  · rintro (h | ⟨z, hz, ⟨s, hs | hs, hn⟩, hy⟩)
    · rcases h with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr ⟨z, hz, ⟨s, hs, hn⟩, hy⟩)
    · exact Or.inr (Or.inr ⟨z, hz, ⟨s, hs, hn⟩, hy⟩)
  · rintro ((h | ⟨z, hz, ⟨s, hs, hn⟩, hy⟩) | (h | ⟨z, hz, ⟨s, hs, hn⟩, hy⟩))
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨z, hz, ⟨s, Or.inl hs, hn⟩, hy⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨z, hz, ⟨s, Or.inr hs, hn⟩, hy⟩

omit [NeZero N₁] [NeZero L] in
theorem subset_Yhat (Ω S : Set (CTorus d L N₁ m₁ K)) : S ⊆ Yhat Ω S := fun _ h => Or.inl h

/-- **(G3), second form.**  For `S₁ ∩ S₂ ≠ ∅` (sets of `π_j`-cubes of `Ω`):
`d_Ω(S₁ ∪ S₂) ≤ d_Ω(S₁) + d_Ω(S₂) + c_G` in `[0, ∞]`. -/
theorem G3_dOmega {Ω S₁ S₂ : Set (CTorus d L N₁ m₁ K)} (hS₁ : S₁ ⊆ Ω)
    (hne : (S₁ ∩ S₂).Nonempty) :
    dOmega m₀ j Ω (S₁ ∪ S₂) ≤
      dOmega m₀ j Ω S₁ + dOmega m₀ j Ω S₂ + ENNReal.ofReal (cG d L) := by
  classical
  by_cases h1 : dOmega m₀ j Ω S₁ = ⊤
  · rw [h1]; simp
  by_cases h2 : dOmega m₀ j Ω S₂ = ⊤
  · rw [h2]; simp
  unfold dOmega at h1 h2 ⊢
  have hc1 : SiteConnected (Yhat Ω S₁) := by
    by_contra hh; simp [hh] at h1
  have hc2 : SiteConnected (Yhat Ω S₂) := by
    by_contra hh; simp [hh] at h2
  simp only [hc1, ↓reduceIte] at h1 ⊢
  simp only [hc2, ↓reduceIte] at h2 ⊢
  obtain ⟨t, ht1, ht2⟩ := hne
  have hY : SiteConnected (Yhat Ω (S₁ ∪ S₂)) := by
    rw [Yhat_union]
    exact siteConnected_union hc1 hc2 (subset_Yhat Ω S₁ ht1) (subset_Yhat Ω S₂ ht2)
  rw [Yhat_union] at hY ⊢
  simp only [hY, ↓reduceIte]
  have ex : ∀ S : Set (CTorus d L N₁ m₁ K), dcovModE m₀ j Ω (Yhat Ω S) ≠ ⊤ →
      ∃ 𝒦 W E, ModAdmissible m₀ j Ω (Yhat Ω S) 𝒦 W E := by
    intro S hS
    by_contra hh
    exact hS (le_antisymm le_top (le_iInf fun 𝒦 => le_iInf fun W => le_iInf fun E =>
      le_iInf fun h => absurd ⟨𝒦, W, E, h⟩ hh))
  obtain ⟨𝒦₁, W₁, E₁, hA₁, he₁⟩ := exists_admissible_eq_dcovModE (ex S₁ h1)
  obtain ⟨𝒦₂, W₂, E₂, hA₂, he₂⟩ := exists_admissible_eq_dcovModE (ex S₂ h2)
  obtain ⟨𝒦, W, E, hA, hc⟩ := exists_union_admissible hA₁ hA₂ (subset_Yhat Ω S₁ ht1)
    (subset_Yhat Ω S₂ ht2) (hS₁ ht1)
  rw [← he₁, ← he₂]
  refine (dcovModE_le_of_admissible hA).trans ?_
  have n1 := bondCost_scaleW_nonneg (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) (j := j) E₁
  have n2 := bondCost_scaleW_nonneg (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) (m₀ := m₀) (j := j) E₂
  have hg : 0 ≤ cG d L := by unfold cG; positivity
  rw [← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_add (add_nonneg n1 n2) hg]
  exact ENNReal.ofReal_le_ofReal hc

end Union

end Balaban.Fluctuation
