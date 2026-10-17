/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLocalBound
public import Balaban.Fluctuation.ClassOldTermSiteSums
public import Balaban.Fluctuation.SizeModG1
public import Balaban.Localization.BlockCount
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The polymer count of the class (blocker 5, the hypothesis `hcount`)

For `j ≤ k`, `L ^ m₀ ∣ N₁` and `κ ≥ a_ent + 2`, every site `w` of the torus satisfies
`∑_{y ∈ Λ_j} ∑_{X ∈ 𝒟_j, X ∋ y, X ∋ w} E₀ e^{-κ d_j(X)} ≤ A E₀` with the explicit constant
`A = L^{(m₀+m₁) d} c₁(d, L) K₀(d, L)`, not depending on `j`, `k`, `w` or the volume.

* `card_aligned_in_box`: an aligned box of side `n a` contains at most `n ^ d` points aligned at `a`.
* `card_aligned_polyDom_le`: a polymer `X ∈ 𝒟_j` contains at most
  `L^{(m₀+m₁) d} c₁ (1 + d_j(X))` points aligned at `L ^ j` (cells of (G1)).
* `sum_aligned_polyDom_le`: the sum over the aligned centres and the polymers through them.
* `hcount_class`: the hypothesis `hcount` of `norm_coef_cutoff_class_le_count`.
-/

@[expose] public section

open Finset Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6

namespace Balaban.Green

section Count

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

open Classical in
/-- An aligned box of side `n a` contains at most `n ^ d` points aligned at `a`. -/
theorem card_aligned_in_box {a n : ℕ} (ha : a ∣ (N₁ * L ^ m₁) * L ^ K) (ha0 : 0 < a)
    {b' : CTorus d L N₁ m₁ K} (hb' : Aligned a b') :
    (Finset.univ.filter fun b : CTorus d L N₁ m₁ K => Aligned a b ∧ b ∈ box b' (n * a)).card ≤
      n ^ d := by
  have hsub : (Finset.univ.filter fun b : CTorus d L N₁ m₁ K => Aligned a b ∧ b ∈ box b' (n * a)) ⊆
      (Fintype.piFinset fun _ : Fin d => Finset.range n).image
        (fun t : Fin d → ℕ => b' + natT (fun μ => a * t μ)) := by
    intro b hb
    obtain ⟨hal, w, hw, rfl⟩ := (Finset.mem_filter.1 hb).2
    rw [Finset.mem_image]
    refine ⟨fun μ => w μ / a, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro μ
      rw [Finset.mem_range, Nat.div_lt_iff_lt_mul ha0]
      have := hw μ
      linarith [mul_comm n a]
    · have hmod : ∀ μ, w μ % a = 0 := fun μ => by
        have := hal μ
        rwa [mod_of_aligned_add ha hb' μ] at this
      have hw' : (fun μ => a * (w μ / a)) = w := by
        funext μ
        have := Nat.div_add_mod (w μ) a
        rw [hmod μ] at this
        omega
      rw [hw']
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Fintype.piFinset fun _ : Fin d => Finset.range n).card := Finset.card_image_le
    _ = n ^ d := by simp

open Classical in
/-- **Aligned points of a polymer.**  A polymer `X ∈ 𝒟_j` (`j ≤ K`, `L ^ m₀ ∣ N₁`) contains at most
`L^{(m₀+m₁) d} c₁ (1 + d_j(X))` points aligned at `L ^ j`. -/
theorem card_aligned_polyDom_le {m₀ j : ℕ} (hjK : j ≤ K) (hN : L ^ m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ K)} (hX : IsPolyDom m₀ j X) :
    ((Finset.univ.filter fun y : CTorus d L N₁ m₁ K => Aligned (L ^ j) y ∧ y ∈ X).card : ℝ) ≤
      ((L : ℝ) ^ ((m₀ + m₁) * d) * c1 d L) * (1 + sizeJ m₀ j X) := by
  have hDj : IsDj m₀ j X := isDj_of_isPolyDom hX
  have hA0 : 0 < L ^ j := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hAdvd : L ^ j ∣ (N₁ * L ^ m₁) * L ^ K :=
    Dvd.dvd.mul_left (pow_dvd_pow L hjK) _
  have hcs : cellSide L m₀ m₁ j = L ^ (m₀ + m₁) * L ^ j := by
    unfold cellSide; rw [← pow_add]; congr 1; ring
  have hcsdvd : L ^ j ∣ cellSide L m₀ m₁ j := by rw [hcs]; exact dvd_mul_left _ _
  set S := Finset.univ.filter fun y : CTorus d L N₁ m₁ K => Aligned (L ^ j) y ∧ y ∈ X with hS
  set cb : CTorus d L N₁ m₁ K → CTorus d L N₁ m₁ K := cbase (cellSide L m₀ m₁ j) with hcb
  have hfib : ∀ c ∈ S.image cb, (S.filter fun y => cb y = c).card ≤ (L ^ (m₀ + m₁)) ^ d := by
    intro c hc
    obtain ⟨y₀, -, rfl⟩ := Finset.mem_image.1 hc
    have hca : Aligned (L ^ j) (cb y₀) :=
      Localization.aligned_of_dvd (a := cellSide L m₀ m₁ j) hcsdvd (aligned_cbase y₀)
    refine le_trans (Finset.card_le_card ?_)
      (card_aligned_in_box (n := L ^ (m₀ + m₁)) hAdvd hA0 hca)
    intro y hy
    obtain ⟨hyS, hyc⟩ := Finset.mem_filter.1 hy
    obtain ⟨hal, -⟩ := (Finset.mem_filter.1 hyS).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hal, ?_⟩
    have := mem_box_cbase (cellSide_pos (L := L) m₀ m₁ j) y
    rw [← hcb, hyc, hcs] at this
    exact this
  have h1 := Finset.card_le_mul_card_image S ((L ^ (m₀ + m₁)) ^ d) hfib
  have himg : S.image cb ⊆ Finset.univ.filter fun b : CTorus d L N₁ m₁ K =>
      Aligned (cellSide L m₀ m₁ j) b ∧ box b (cellSide L m₀ m₁ j) ⊆ X := by
    intro c hc
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨-, hyX⟩ := (Finset.mem_filter.1 hy).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, aligned_cbase y, ?_⟩
    exact cell_subset_of_mem hjK hN hDj hyX
  have h2 : (S.image cb).card ≤ cellCount (cellSide L m₀ m₁ j) X := by
    unfold cellCount; exact Finset.card_le_card himg
  have hG1 := G1_cellCount (m₀ := m₀) (j := j) hN hjK (Ω := Set.univ) (X := X)
    ⟨hDj, fun z hz => absurd (Set.mem_univ z) hz⟩
  rw [Set.inter_univ, dcovMod_of_subset (Set.subset_univ X)] at hG1
  have h3 : (S.card : ℝ) ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d * (cellCount (cellSide L m₀ m₁ j) X : ℝ) := by
    have := (h1.trans (Nat.mul_le_mul_left _ h2))
    exact_mod_cast this
  unfold sizeJ
  calc (S.card : ℝ) ≤ _ := h3
    _ ≤ ((L : ℝ) ^ (m₀ + m₁)) ^ d * (c1 d L * (1 + treeLenCovOne m₀ j X)) :=
        mul_le_mul_of_nonneg_left hG1 (by positivity)
    _ = _ := by rw [← pow_mul]; ring

open Classical in
/-- **The polymer count of the class** (`hcount` of `norm_coef_cutoff_class_le_count`).  For
`j ≤ K`, `L ^ m₀ ∣ N₁`, `E₀ ≥ 0` and `κ ≥ a_ent + 2`, every site `w` satisfies
`∑_{y ∈ Λ_j} ∑_{X ∈ 𝒟_j, X ∋ y} [w ∈ X] E₀ e^{-κ d_j(X)} ≤ L^{(m₀+m₁) d} c₁ K₀ E₀`.  The constant
does not depend on `j`, `K`, `w` or the volume. -/
theorem hcount_class {m₀ j : ℕ} (hjK : j ≤ K) (hN : L ^ m₀ ∣ N₁) {E₀ κ : ℝ} (hE₀ : 0 ≤ E₀)
    (hκ : aEnt d L + 2 ≤ κ) (w : CTorus d L N₁ m₁ K) :
    ∑ y ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter (Aligned (L ^ j)),
      ∑ᶠ X ∈ polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ j y,
        (if w ∈ X then E₀ * Real.exp (-κ * sizeJ m₀ j X) else 0) ≤
      ((L : ℝ) ^ ((m₀ + m₁) * d) * c1 d L * K0 d L (κ - 1)) * E₀ := by
  set B : ℝ := (L : ℝ) ^ ((m₀ + m₁) * d) * c1 d L with hB
  have hB0 : 0 ≤ B := by rw [hB]; unfold c1; positivity
  set g : Set (CTorus d L N₁ m₁ K) → ℝ := fun X =>
    if w ∈ X then E₀ * Real.exp (-κ * sizeJ m₀ j X) else 0 with hg
  have hg0 : ∀ X, 0 ≤ g X := fun X => by
    simp only [hg]; split_ifs
    · exact mul_nonneg hE₀ (Real.exp_pos _).le
    · exact le_rfl
  have hfs : ∀ y : CTorus d L N₁ m₁ K,
      ∑ᶠ X ∈ polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ j y, g X =
      ∑ X ∈ Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) => IsPolyDom m₀ j X),
        if y ∈ X then g X else 0 := fun y => by
    have : polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ j y =
        ↑(Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) => IsPolyDom m₀ j X ∧ y ∈ X)) := by
      ext X; simp [polysAt]
    rw [this, finsum_mem_coe_finset, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun X _ => ?_
    by_cases h1 : IsPolyDom m₀ j X <;> by_cases h2 : y ∈ X <;> simp [h1, h2]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun y _ => hfs y) ?_
  rw [Finset.sum_comm]
  have hterm : ∀ X ∈ (Finset.univ : Finset (Set (CTorus d L N₁ m₁ K))).filter
      (fun X => IsPolyDom m₀ j X),
      ∑ y ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ K)).filter (Aligned (L ^ j)),
        (if y ∈ X then g X else 0) ≤
      if w ∈ X then B * E₀ * Real.exp (-(κ - 1) * sizeJ m₀ j X) else 0 := by
    intro X hX
    have hXp := (Finset.mem_filter.1 hX).2
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    by_cases hw : w ∈ X
    · simp only [hw, ite_true]
      have hc := card_aligned_polyDom_le hjK hN hXp
      have hcard : ((Finset.univ.filter (Aligned (L ^ j))).filter (fun y => y ∈ X)).card =
          (Finset.univ.filter fun y : CTorus d L N₁ m₁ K => Aligned (L ^ j) y ∧ y ∈ X).card := by
        rw [Finset.filter_filter]
      rw [hcard]
      have hs0 : 0 ≤ sizeJ m₀ j X := treeLenCovOne_nonneg _ _ _
      have h1 : 1 + sizeJ m₀ j X ≤ Real.exp (sizeJ m₀ j X) := by
        linarith [Real.add_one_le_exp (sizeJ m₀ j X)]
      have hgX : g X = E₀ * Real.exp (-κ * sizeJ m₀ j X) := by simp [hg, hw]
      rw [hgX]
      have hexp : Real.exp (-κ * sizeJ m₀ j X) * Real.exp (sizeJ m₀ j X) =
          Real.exp (-(κ - 1) * sizeJ m₀ j X) := by
        rw [← Real.exp_add]; congr 1; ring
      calc _ ≤ (B * (1 + sizeJ m₀ j X)) * (E₀ * Real.exp (-κ * sizeJ m₀ j X)) :=
            mul_le_mul_of_nonneg_right hc (mul_nonneg hE₀ (Real.exp_pos _).le)
        _ ≤ (B * Real.exp (sizeJ m₀ j X)) * (E₀ * Real.exp (-κ * sizeJ m₀ j X)) := by
            gcongr
        _ = B * E₀ * (Real.exp (-κ * sizeJ m₀ j X) * Real.exp (sizeJ m₀ j X)) := by ring
        _ = _ := by rw [hexp]
    · have hgX : g X = 0 := by simp [hg, hw]
      simp [hgX, hw]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter]
  have hent : ∑ X ∈ (Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) => IsPolyDom m₀ j X)).filter
      (fun X => w ∈ X), Real.exp (-(κ - 1) * sizeJ m₀ j X) ≤ K0 d L (κ - 1) := by
    have := sum_polyDom_through_le (m₁ := m₁) (m₀ := m₀) hjK hN (κ₀ := κ - 1)
      (by linarith) w
    refine le_trans (le_of_eq ?_) this
    rw [Finset.filter_filter]
    rfl
  calc _ = B * E₀ * ∑ X ∈ (Finset.univ.filter (fun X : Set (CTorus d L N₁ m₁ K) =>
        IsPolyDom m₀ j X)).filter (fun X => w ∈ X), Real.exp (-(κ - 1) * sizeJ m₀ j X) := by
        rw [Finset.mul_sum]
    _ ≤ B * E₀ * K0 d L (κ - 1) := mul_le_mul_of_nonneg_left hent (mul_nonneg hB0 hE₀)
    _ = _ := by ring

end Count

section Class

open Set MeasureTheory Metric Balaban.Analysis Balaban.SmallField.Def6v2

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}

open Classical in
/-- **The volume-uniform bound with the polymer count discharged.**  `norm_coef_cutoff_class_le_count`
with `hcount` proved: for `L ^ P.m₀ ∣ N₁` and `P.κ ≥ a_ent + 2` the constant is
`A = L^{(m₀+m₁) d} c₁ K₀(d, L, P.κ - 1)` for every level `j`, and the bound reads
`‖coef J_{F_K} C‖ ≤ γ(box) e^{-(κ-1)|C|} (K A) |W| E₀`. -/
theorem norm_coef_cutoff_class_le_card (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ → ℝ)} {ρ β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β)
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    {d' : ℕ} {R : ℝ} {N₁ m₁ kc N : ℕ} [NeZero N₁] {ϱ : ℝ}
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) < R)
    {P : Consts} {Dom : FieldDom d' L N₁ m₁ kc N ϱ} {Tm : Terms d' L N₁ m₁ kc N ϱ}
    (hT : SFTermClauses P Dom Tm) {K : ℕ} (hK : K ≤ kc)
    {φ₀ : L1Torus d N₀ → ℂ}
    {Λ : ℕ → (L1Torus d N₀ → ℂ) → Fld d' L N₁ m₁ kc N × Fld d' L N₁ m₁ kc N}
    (hΛ : ∀ j, 1 ≤ j → j ≤ K → AnalyticOnNhd ℂ (Λ j) (polydisc φ₀ (fun _ => R)))
    (hsub : ∀ w ∈ polydisc φ₀ (fun _ => R), ∀ j, 1 ≤ j → j ≤ K →
      ∀ X, IsPolyDom P.m₀ j X → Dom.dom j (Tm.gs j X) (Λ j w).1 (Λ j w).2)
    (S : ℕ → CTorus d' L N₁ m₁ kc → Set (CTorus d' L N₁ m₁ kc) → Set (L1Torus d N₀))
    (hΛloc : ∀ j y X (w w' : L1Torus d N₀ → ℂ), (∀ x ∈ S j y X, w x = w' x) →
      ∀ z ∈ X, (Λ j w).1 z = (Λ j w').1 z ∧ (Λ j w).2 z = (Λ j w').2 z)
    (hE₀ : 0 ≤ P.E₀) (hN : L ^ P.m₀ ∣ N₁) (hκP : aEnt d' L + 2 ≤ P.κ)
    (C : Finset (MacIdx d N₀ M)) (hC : C.Nonempty) (W : Finset (CTorus d' L N₁ m₁ kc))
    (hW : ∀ j, 1 ≤ j → j ≤ K → ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
      (∃ x ∈ S j y X, x ∈ macRegion d N₀ M C) → ∃ w ∈ W, w ∈ X) :
    ‖coef (fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (fun w : L1Torus d N₀ → ℂ => ∑ j ∈ Finset.Icc 1 K,
            Edens P.m₀ Tm j (Λ j w).1 (Λ j w).2)
          (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C‖ ≤
      (γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal * Real.exp (-(κ - 1) * C.card) *
        (((K : ℝ) * ((L : ℝ) ^ ((P.m₀ + m₁) * d') * c1 d' L * K0 d' L (P.κ - 1))) *
          (W.card : ℝ) * P.E₀) := by
  have := norm_coef_cutoff_class_le_count hd hk hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hβ hγ hBR
    hT hK hΛ hsub S hΛloc hE₀
    (fun _ => (L : ℝ) ^ ((P.m₀ + m₁) * d') * c1 d' L * K0 d' L (P.κ - 1)) C hC W hW
    (fun j _ hjK w => hcount_class (hjK.trans hK) hN hE₀ hκP w)
  simpa using this

end Class

end Balaban.Green
