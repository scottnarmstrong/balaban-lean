/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTorusClose
public import Balaban.Green.FinalTaggedLocal
public import Balaban.Green.FinalTaggedRow
public import Balaban.Green.FinalLogDetLocal

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Closeness of the tagged parametrix entries on two tori (W802, blocker 7, estimate (I2))

`Polymer/TwoTorusFinal` proves *equality* of the entries of the tagged parametrix pieces on two
tori when the two operators agree exactly on `Y(C)²`.  The final operators of two tori agree only
up to a small error (`Green/FinalTorusClose`).  This file proves the approximate versions: if the
entries of `U` and `U'` differ by at most `ε` on `Y(C)²` (along the identification `f` of the
residues), then, for `s` supported on `C` and `s'` supported on `e C` with `s' (e i) = s i`,
`‖s p‖ ≤ e^κ`:

* `rowmul_close`: the perturbed defect and the box resolvent factors;
* `boxG_entry_close_twoTorus`: `‖boxG U (B_z) t x y - boxG U' (B_{e z}) t (f x) (f y)‖`
  is at most `|B|² ε / (g + t)²`;
* `taggedG_close_twoTorus`, `taggedK_close_twoTorus`: entries of the tagged `G_*` and `K`;
* `taggedGfin_close_twoTorus`: entries of `G_fin(s, t)`, at most `P ε / (g + t)`;
* `taggedCfinU_close_twoTorus`: entries of the Stieltjes family `taggedCfinU`, at most `P ε / √g`.

All constants depend on `d`, `L`, `M`, `κ`, the number of cells of `C` only; the error `ε` of
the operators enters linearly (for the final operator on two tori it is
`finalOp_entry_close`, which depends on `k`).
-/

@[expose] public section

open Finset Matrix MeasureTheory Set Balaban.Localization

namespace Balaban.Green

section Generic

variable {X X' : Type*} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']

/-- **Approximate `rowmul_transport`.**  Product of a matrix with `diag c * boxG`, along an
injective correspondence `f`, up to the errors of `A`, `A'` and of the box resolvents. -/
theorem rowmul_close (f : X → X') {Y B : Finset X} (hB : B ⊆ Y) (hinj : Set.InjOn f (Y : Set X))
    {U : Matrix X X ℂ} {U' : Matrix X' X' ℂ} (t : ℝ) {c : X → ℂ} {c' : X' → ℂ}
    (hc : ∀ u, c u ≠ 0 → u ∈ B) (hc' : ∀ u, c' u ≠ 0 → u ∈ B.image f)
    (hcY : ∀ u ∈ Y, c u = c' (f u)) (hc1 : ∀ u, ‖c u‖ ≤ 1)
    {A : Matrix X X ℂ} {A' : Matrix X' X' ℂ} {εA aA bG δG : ℝ}
    (hεA : 0 ≤ εA) (haA : 0 ≤ aA) (hbG : 0 ≤ bG) (hδG : 0 ≤ δG)
    (hA : ∀ x ∈ Y, ∀ y ∈ Y, ‖A x y - A' (f x) (f y)‖ ≤ εA)
    (hA' : ∀ x ∈ Y, ∀ y ∈ Y, ‖A' (f x) (f y)‖ ≤ aA)
    (hG : ∀ u ∈ B, ∀ y, ‖boxG U B t u y‖ ≤ bG)
    (hGc : ∀ u ∈ B, ∀ y ∈ B,
      ‖boxG U B t u y - boxG U' (B.image f) t (f u) (f y)‖ ≤ δG)
    {x y : X} (hx : x ∈ Y) (hy : y ∈ Y) :
    ‖(A * (Matrix.diagonal c * boxG U B t)) x y -
        (A' * (Matrix.diagonal c' * boxG U' (B.image f) t)) (f x) (f y)‖ ≤
      (B.card : ℝ) * (εA * bG + aA * δG) := by
  classical
  have hBinj : Set.InjOn f (B : Set X) := hinj.mono (by exact_mod_cast hB)
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.diagonal_mul]
  have hL : ∑ u, A x u * (c u * boxG U B t u y) = ∑ u ∈ B, A x u * (c u * boxG U B t u y) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun u _ hu => ?_)
    have : c u = 0 := by
      by_contra hne
      exact hu (hc u hne)
    simp [this]
  have hR : ∑ u', A' (f x) u' * (c' u' * boxG U' (B.image f) t u' (f y)) =
      ∑ u' ∈ B.image f, A' (f x) u' * (c' u' * boxG U' (B.image f) t u' (f y)) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun u _ hu => ?_)
    have : c' u = 0 := by
      by_contra hne
      exact hu (hc' u hne)
    simp [this]
  rw [hL, hR, Finset.sum_image hBinj, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ u ∈ B, ‖A x u * (c u * boxG U B t u y) -
        A' (f x) (f u) * (c' (f u) * boxG U' (B.image f) t (f u) (f y))‖
      ≤ ∑ _u ∈ B, (εA * bG + aA * δG) := by
        refine Finset.sum_le_sum fun u hu => ?_
        have huY : u ∈ Y := hB hu
        by_cases hyB : y ∈ B
        · rw [← hcY u huY]
          have hid : A x u * (c u * boxG U B t u y) -
              A' (f x) (f u) * (c u * boxG U' (B.image f) t (f u) (f y)) =
              (A x u - A' (f x) (f u)) * (c u * boxG U B t u y) +
              A' (f x) (f u) * (c u * (boxG U B t u y - boxG U' (B.image f) t (f u) (f y))) := by
            ring
          rw [hid]
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, norm_mul]
            calc ‖A x u - A' (f x) (f u)‖ * (‖c u‖ * ‖boxG U B t u y‖) ≤ εA * (1 * bG) :=
                  mul_le_mul (hA x hx u huY) (mul_le_mul (hc1 u) (hG u hu y) (norm_nonneg _)
                    zero_le_one) (by positivity) hεA
              _ = εA * bG := by ring
          · rw [norm_mul, norm_mul]
            calc ‖A' (f x) (f u)‖ * (‖c u‖ * ‖boxG U B t u y -
                  boxG U' (B.image f) t (f u) (f y)‖) ≤ aA * (1 * δG) :=
                  mul_le_mul (hA' x hx u huY) (mul_le_mul (hc1 u) (hGc u hu y hyB)
                    (norm_nonneg _) zero_le_one) (by positivity) haA
              _ = aA * δG := by ring
        · have h0 : boxG U B t u y = 0 := boxG_apply_of_not_mem hyB
          have h0' : boxG U' (B.image f) t (f u) (f y) = 0 := by
            refine boxG_apply_of_not_mem ?_
            intro hmem
            obtain ⟨b, hb, hbf⟩ := Finset.mem_image.1 hmem
            exact hyB (by rw [← hinj (hB hb) hy hbf]; exact hb)
          rw [h0, h0']
          simp only [mul_zero, sub_zero, norm_zero]
          positivity
    _ = (B.card : ℝ) * (εA * bG + aA * δG) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Generic

section Abstract

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

omit [DecidableEq Y] in
theorem entry_mul_le (A B : Matrix Y Y ℂ) {a b : ℝ} (ha : 0 ≤ a)
    (hA : ∀ p q, ‖A p q‖ ≤ a) (hB : ∀ p q, ‖B p q‖ ≤ b) (p q : Y) :
    ‖(A * B) p q‖ ≤ (Fintype.card Y : ℝ) * (a * b) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ u, ‖A p u * B u q‖ ≤ ∑ _u : Y, a * b :=
        Finset.sum_le_sum fun u _ => by
          rw [norm_mul]; exact mul_le_mul (hA p u) (hB u q) (norm_nonneg _) ha
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Perturbation of `G H⁻¹`** in entrywise norms: `G₁ A₁ - G₂ A₂` with `A₁ H₁ = 1`,
`H₂ A₂ = 1`. -/
theorem mul_inv_close (G₁ G₂ A₁ A₂ H₁ H₂ : Matrix Y Y ℂ) {δG δK g₁ a₁ : ℝ}
    (hδG : 0 ≤ δG) (hδK : 0 ≤ δK) (hg₁ : 0 ≤ g₁) (ha₁ : 0 ≤ a₁)
    (h1 : A₁ * H₁ = 1) (h2 : H₂ * A₂ = 1)
    (hG : ∀ p q, ‖G₁ p q - G₂ p q‖ ≤ δG) (hH : ∀ p q, ‖H₁ p q - H₂ p q‖ ≤ δK)
    (hG₂ : ∀ p q, ‖G₂ p q‖ ≤ g₁) (hA₁ : ∀ p q, ‖A₁ p q‖ ≤ a₁) (hA₂ : ∀ p q, ‖A₂ p q‖ ≤ a₁)
    (p q : Y) :
    ‖(G₁ * A₁ - G₂ * A₂) p q‖ ≤
      (Fintype.card Y : ℝ) * (δG * a₁) +
        (Fintype.card Y : ℝ) ^ 3 * (g₁ * (a₁ * (a₁ * δK))) := by
  set n : ℝ := (Fintype.card Y : ℝ) with hn
  have hn0 : 0 ≤ n := by positivity
  have hkey : G₁ * A₁ - G₂ * A₂ = (G₁ - G₂) * A₁ + G₂ * (A₁ * (H₂ - H₁) * A₂) := by
    have e1 : A₁ * (H₂ - H₁) * A₂ = A₁ - A₂ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, mul_assoc, h2, h1, Matrix.mul_one, Matrix.one_mul]
    rw [e1, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hkey, Matrix.add_apply]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have := entry_mul_le (G₁ - G₂) A₁ hδG (fun p q => by simpa using hG p q) hA₁ p q
    exact this
  · have hH' : ∀ p q, ‖(H₂ - H₁) p q‖ ≤ δK := fun p q => by
      rw [Matrix.sub_apply, norm_sub_rev]; exact hH p q
    have e2 := entry_mul_le A₁ (H₂ - H₁) ha₁ hA₁ hH'
    have e3 := entry_mul_le (A₁ * (H₂ - H₁)) A₂ (by positivity) (fun p q => e2 p q) hA₂
    have e4 := entry_mul_le G₂ (A₁ * (H₂ - H₁) * A₂) hg₁ hG₂
      (fun p q => e3 p q) p q
    refine e4.trans (le_of_eq ?_)
    ring

section TwoTorus

open Balaban.Localization

variable {d M J N N' : ℕ} [NeZero N] [NeZero N']

/-- **Approximate `taggedMat_entry_twoTorus`.**  If the families `a`, `a'` correspond up to `δ` on
`Y(C)²` for the cells of `C`, the tagged matrices at parameters `s`, `s'` (supported on `C`, `e C`,
equal along `e`, of modulus at most `e^κ`) differ by at most `|C| e^{κ |C|} δ` at `x, y ∈ Y(C)`. -/
theorem taggedMat_close_twoTorus (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    {a : MacIdx d N M → Matrix (L1Torus d N) (L1Torus d N) ℂ}
    {a' : MacIdx d N' M → Matrix (L1Torus d N') (L1Torus d N') ℂ} {δ κ : ℝ} (hκ : 0 ≤ κ)
    (hδ : 0 ≤ δ)
    (ha : ∀ z ∈ C, ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖a z x y - a' (e z) (f x) (f y)‖ ≤ δ)
    {s : MacIdx d N M → ℂ} (hs : s ∈ Balaban.Localization.supportedOn C)
    {s' : MacIdx d N' M → ℂ} (hs' : s' ∈ Balaban.Localization.supportedOn (C.image e))
    (hss : ∀ i ∈ C, s' (e i) = s i) (hsκ : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {x y : L1Torus d N} (hx : x ∈ macRegion d N M C)
    (hy : y ∈ macRegion d N M C) :
    ‖taggedMat Finset.univ (macTags d N M) a s x y -
      taggedMat Finset.univ (macTags d N' M) a' s' (f x) (f y)‖ ≤
      (C.card : ℝ) * Real.exp (κ * C.card) * δ := by
  classical
  obtain ⟨e', he'⟩ := exists_cellMap (d := d) (N := N') (N' := N) (J := J) hM hN
  set g : L1Torus d N' → L1Torus d N := fun y μ => (((y μ).val : ℕ) : ZMod N) with hgdef
  have hg : ∀ y μ, g y μ = (((y μ).val : ℕ) : ZMod N) := fun _ _ => rfl
  have hmidY : ∀ u, u ∈ macRegion d N M C → ∀ i, 2 * M < (u i).val ∧ (u i).val < (J + 3) * M :=
    fun u hu => mid_of_mem_macRegion hM hN hC hu
  have hxm := hmidY x hx
  have hym := hmidY y hy
  rw [taggedMat_apply_of_supportedOn _ _ _ hs, taggedMat_apply_of_supportedOn _ _ _ hs']
  have hgoodC : ∀ z ∈ C, ∀ i, (z i : ℕ) ≤ J + 4 := fun z hz i => by
    have := (hC z hz i).2; omega
  have hinjE : Set.InjOn e (C : Set (MacIdx d N M)) := by
    intro z1 hz1 z2 hz2 h
    funext i
    apply Fin.ext
    have h1 := he z1 i (hgoodC z1 hz1 i)
    have h2 := he z2 i (hgoodC z2 hz2 i)
    have : ((e z1 i : Fin (macK N' M)) : ℕ) = ((e z2 i : Fin (macK N' M)) : ℕ) := by rw [h]
    omega
  have hVimg : ∀ z ∈ C, macTags d N' M (e z) (f x) (f y) = (macTags d N M z x y).image e := by
    intro z hz
    ext w'
    constructor
    · intro hw'
      obtain ⟨w, hw, rfl⟩ := tags_backward hM hN hN' hf hg hxm hym he he' (hC z hz) hw'
      exact Finset.mem_image_of_mem e hw
    · intro hw'
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hw'
      exact (tags_forward hM hN hN' hf hxm hym he (hC z hz) hw).2
  have hsubset_iff : ∀ z ∈ C, (macTags d N M z x y ⊆ C) ↔
      (macTags d N' M (e z) (f x) (f y) ⊆ C.image e) := by
    intro z hz
    rw [hVimg z hz]
    constructor
    · intro h
      exact Finset.image_subset_image h
    · intro h w hw
      have h1 := h (Finset.mem_image_of_mem e hw)
      obtain ⟨c, hc, hce⟩ := Finset.mem_image.1 h1
      have hwg := (tags_forward hM hN hN' hf hxm hym he (hC z hz) hw).1
      have : w = c := by
        funext i
        apply Fin.ext
        have h1 := he w i (hwg i)
        have h2 := he c i (hgoodC c hc i)
        have : ((e w i : Fin (macK N' M)) : ℕ) = ((e c i : Fin (macK N' M)) : ℕ) := by rw [hce]
        omega
      rw [this]; exact hc
  have hL : (Finset.univ.filter fun z => macTags d N M z x y ⊆ C) =
      C.filter (fun z => macTags d N M z x y ⊆ C) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h (mem_macTags_self hM z x y), h⟩, fun h => h.2⟩
  have hR : (Finset.univ.filter fun z' => macTags d N' M z' (f x) (f y) ⊆ C.image e) =
      (C.filter (fun z => macTags d N M z x y ⊆ C)).image e := by
    ext z'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      have hz' : z' ∈ C.image e := h (mem_macTags_self hM z' _ _)
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
      exact ⟨z, ⟨hz, (hsubset_iff z hz).2 h⟩, rfl⟩
    · rintro ⟨z, ⟨hz, h⟩, rfl⟩
      exact (hsubset_iff z hz).1 h
  rw [hL, hR, Finset.sum_image (hinjE.mono (by intro z hz; exact (Finset.mem_filter.1 hz).1))]
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc _ ≤ ∑ _z ∈ C.filter (fun z => macTags d N M z x y ⊆ C),
        Real.exp (κ * C.card) * δ := by
        refine Finset.sum_le_sum fun z hz => ?_
        obtain ⟨hzC, hVC⟩ := Finset.mem_filter.1 hz
        rw [hVimg z hzC]
        have hprod : tagMon (macTags d N M z x y) s =
            tagMon ((macTags d N M z x y).image e) s' := by
          unfold tagMon
          rw [Finset.prod_image (hinjE.mono (by intro w hw; exact hVC hw))]
          refine Finset.prod_congr rfl fun w hw => ?_
          rw [hss w (hVC hw)]
        rw [hprod, ← mul_sub, norm_mul]
        have hT : ‖tagMon ((macTags d N M z x y).image e) s'‖ ≤ Real.exp (κ * C.card) := by
          rw [← hprod]
          unfold tagMon
          rw [norm_prod]
          calc ∏ w ∈ macTags d N M z x y, ‖s w‖ ≤ ∏ _w ∈ macTags d N M z x y, Real.exp κ :=
                by gcongr with w hw; exact hsκ w
            _ = Real.exp (κ * (macTags d N M z x y).card) := by
                rw [Finset.prod_const, ← Real.exp_nat_mul]; ring_nf
            _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
                (by exact_mod_cast Finset.card_le_card hVC) hκ)
        exact mul_le_mul hT (ha z hzC x hx y hy) (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have : ((C.filter (fun z => macTags d N M z x y ⊆ C)).card : ℝ) ≤ C.card := by
          exact_mod_cast Finset.card_filter_le _ _
        have h0 : 0 ≤ Real.exp (κ * C.card) * δ := by positivity
        calc _ ≤ (C.card : ℝ) * (Real.exp (κ * C.card) * δ) := mul_le_mul_of_nonneg_right this h0
          _ = _ := by ring

end TwoTorus

/-- **Approximate `ysupp_mul_inv_transport`.**  For matrices `G`, `K` supported on `Y × Y` and
`G'`, `K'` supported on `Y' × Y'`, `f` a bijection `Y → Y'`: if `G`, `K` correspond up to `δG`, `δK`
and the inverses `(1 - K)⁻¹`, `(1 - K')⁻¹` have entries at most `a₁`, `G'` entries at most `g₁`, then
`G (1 - K)⁻¹` and `G' (1 - K')⁻¹` correspond up to
`|Y| δG a₁ + |Y|³ g₁ a₁² δK`. -/
theorem ysupp_close {X X' : Type*} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']
    (f : X → X') {Y : Finset X} {Y' : Finset X'}
    (hf : Set.BijOn f (Y : Set X) (Y' : Set X')) {G K : Matrix X X ℂ} {G' K' : Matrix X' X' ℂ}
    (hG : ∀ x y, G x y ≠ 0 → x ∈ Y ∧ y ∈ Y) (hK : ∀ x y, K x y ≠ 0 → x ∈ Y ∧ y ∈ Y)
    (hG' : ∀ x y, G' x y ≠ 0 → x ∈ Y' ∧ y ∈ Y') (hK' : ∀ x y, K' x y ≠ 0 → x ∈ Y' ∧ y ∈ Y')
    {δG δK g₁ a₁ : ℝ} (hδG : 0 ≤ δG) (hδK : 0 ≤ δK) (hg₁ : 0 ≤ g₁) (ha₁ : 0 ≤ a₁)
    (hGG : ∀ x ∈ Y, ∀ y ∈ Y, ‖G x y - G' (f x) (f y)‖ ≤ δG)
    (hKK : ∀ x ∈ Y, ∀ y ∈ Y, ‖K x y - K' (f x) (f y)‖ ≤ δK)
    (hg : ∀ x y, ‖G' x y‖ ≤ g₁) (ha : ∀ x y, ‖(1 - K)⁻¹ x y‖ ≤ a₁)
    (ha' : ∀ x y, ‖(1 - K')⁻¹ x y‖ ≤ a₁) (hu : IsUnit (1 - K)) (hu' : IsUnit (1 - K'))
    {x y : X} (hx : x ∈ Y) (hy : y ∈ Y) :
    ‖(G * (1 - K)⁻¹) x y - (G' * (1 - K')⁻¹) (f x) (f y)‖ ≤
      (Y.card : ℝ) * (δG * a₁) + (Y.card : ℝ) ^ 3 * (g₁ * (a₁ * (a₁ * δK))) := by
  classical
  have hfx : f x ∈ Y' := hf.mapsTo hx
  have hfy : f y ∈ Y' := hf.mapsTo hy
  rw [(ysupp_mul_inv G K Y hG hK).2 x hx y hy, (ysupp_mul_inv G' K' Y' hG' hK').2 _ hfx _ hfy]
  have hbij : Function.Bijective (fun q : Y => (⟨f q, hf.mapsTo q.2⟩ : Y')) := by
    constructor
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (hf.injOn a.2 b.2 this)
    · intro b
      obtain ⟨a, ha, hab⟩ := hf.surjOn b.2
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  set ε : Y ≃ Y' := Equiv.ofBijective _ hbij with hε
  set Hb : Matrix Y Y ℂ := (1 - K).submatrix (fun q : Y => (q : X)) (fun q : Y => (q : X)) with hHb
  set Hb' : Matrix Y' Y' ℂ := (1 - K').submatrix (fun q : Y' => (q : X')) (fun q : Y' => (q : X'))
    with hHb'
  have hdet : IsUnit Hb.det := by
    rw [hHb, ← det_eq_det_submatrix_of_rows (1 - K) Y (fun x hx y => by
      have : K x y = 0 := by
        by_contra hc; exact hx (hK x y hc).1
      simp [Matrix.sub_apply, this])]
    exact (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hdet' : IsUnit Hb'.det := by
    rw [hHb', ← det_eq_det_submatrix_of_rows (1 - K') Y' (fun x hx y => by
      have : K' x y = 0 := by
        by_contra hc; exact hx (hK' x y hc).1
      simp [Matrix.sub_apply, this])]
    exact (Matrix.isUnit_iff_isUnit_det _).1 hu'
  set G1 : Matrix Y Y ℂ := G.submatrix (fun q : Y => (q : X)) (fun q : Y => (q : X)) with hG1
  set Gb' : Matrix Y' Y' ℂ := G'.submatrix (fun q : Y' => (q : X')) (fun q : Y' => (q : X'))
    with hGb'
  set G2 : Matrix Y Y ℂ := Gb'.submatrix ε ε with hG2
  set H2 : Matrix Y Y ℂ := Hb'.submatrix ε ε with hH2
  have hR : (Gb' * Hb'⁻¹) ⟨f x, hfx⟩ ⟨f y, hfy⟩ = (G2 * H2⁻¹) ⟨x, hx⟩ ⟨y, hy⟩ := by
    rw [hG2, hH2, Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv]
    rfl
  rw [hR]
  have hdet2 : IsUnit H2.det := by rw [hH2, Matrix.det_submatrix_equiv_self]; exact hdet'
  have hc1 : Hb⁻¹ * Hb = 1 := Matrix.nonsing_inv_mul _ hdet
  have hc2 : H2 * H2⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet2
  have hinv1 : Hb⁻¹ = ((1 - K)⁻¹).submatrix (fun q : Y => (q : X)) (fun q : Y => (q : X)) :=
    (inv_ysupp_submatrix K Y hK).symm
  have hinv2 : H2⁻¹ = (((1 - K')⁻¹).submatrix (fun q : Y' => (q : X'))
      (fun q : Y' => (q : X'))).submatrix ε ε := by
    rw [hH2, Matrix.inv_submatrix_equiv, hHb', inv_ysupp_submatrix K' Y' hK']
  have key := mul_inv_close G1 G2 (Hb⁻¹) (H2⁻¹) Hb H2 (δG := δG) (δK := δK) (g₁ := g₁) (a₁ := a₁)
    hδG hδK hg₁ ha₁ hc1 hc2 (fun p q => hGG p p.2 q q.2)
    (fun p q => by
      have hpq : (p = q) ↔ (f p = f q) :=
        ⟨fun h => by rw [h], fun h => Subtype.ext (hf.injOn p.2 q.2 h)⟩
      have h3 : ((p : X) = q) ↔ (f p = f q) := ⟨fun h => by rw [h], fun h => hf.injOn p.2 q.2 h⟩
      have : Hb p q - H2 p q = -(K p q - K' (f p) (f q)) := by
        simp only [hHb, hH2, hHb', Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply,
          hε, Equiv.ofBijective_apply]
        simp only [h3]
        ring
      rw [this, norm_neg]
      exact hKK p p.2 q q.2)
    (fun p q => hg _ _)
    (fun p q => by rw [hinv1]; exact ha _ _)
    (fun p q => by rw [hinv2]; exact ha' _ _) ⟨x, hx⟩ ⟨y, hy⟩
  rw [Fintype.card_coe] at key
  simpa using key

end Abstract

section FinalBoxes

variable {d L k M J N N' : ℕ} [NeZero N] [NeZero N'] [NeZero L]

theorem final_entry_le_decayC (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (x y : L1Torus d N) :
    ‖finalOp d L N k v a x y‖ ≤ finalDecayC d L := by
  refine (finalMass_entry_decay hd hk hv0 ha1 ha2 x y).trans ?_
  have hC := (finalDecayC_pos (L := L) hd).le
  have : Real.exp (-blockDecayRate d * dist x y) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [blockDecayRate_pos hd, dist_nonneg (x := x) (y := y)])
  nlinarith

theorem final_boxG_entry_le (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {t : ℝ} (ht : 0 ≤ t)
    (B : Finset (L1Torus d N)) (u w : L1Torus d N) :
    ‖boxG (finalOp d L N k v a) B t u w‖ ≤ 2 * (finalGap d L + t)⁻¹ := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have h := boxG_entry_bound_of_coercive (finalOp d L N k v a) (finalDecayC_pos hd).le
    (blockDecayRate_pos hd) hg (finalMass_isCoercive hd hv0 hv1 ha1 hmass)
    (finalMass_entry_decay hd hk hv0 ha1 ha2) ht B u w
  refine h.trans ?_
  have hr : 0 < ctRate (finalDecayC d L) (blockDecayRate d) (finalGap d L)
      (ballConst d (blockDecayRate d / 4)) :=
    ctRate_pos (finalDecayC_pos hd).le (blockDecayRate_pos hd) hg
      (ballConst_decay_nonneg (by have := blockDecayRate_pos hd; positivity))
  have : Real.exp (-ctRate (finalDecayC d L) (blockDecayRate d) (finalGap d L)
      (ballConst d (blockDecayRate d / 4)) * dist u w) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [dist_nonneg (x := u) (y := w)])
  have h2 : 0 ≤ 2 / (finalGap d L + t) := by positivity
  calc 2 / (finalGap d L + t) * _ ≤ 2 / (finalGap d L + t) * 1 :=
        mul_le_mul_of_nonneg_left this h2
    _ = _ := by rw [mul_one, div_eq_mul_inv]

/-- **Closeness of the box resolvent family of the final operators on two tori.**  Let the final
operators of the tori `N`, `N'` have entries differing by at most `ε` on `Y(C)²` (along the
identification `f` of the residues).  For a cell `z ∈ C` and `x, y ∈ Y(C)` the entries of
`χ_z G_z` differ by at most `|B|² ε (g + t)⁻²`, and those of the defect `R_z` by at most
`|B| ε (g + t)⁻¹ (2 + (A / g + 1) |B|²)`, where `|B| ≤ (8M+1)^d` and `A = finalDecayC d L`. -/
theorem final_boxFamily_close (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {ε : ℝ}
    (hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε)
    {t : ℝ} (ht : 0 ≤ t) {z : MacIdx d N M} (hzC : z ∈ C) {x y : L1Torus d N}
    (hx : x ∈ macRegion d N M C) (hy : y ∈ macRegion d N M C) :
    ‖(Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N k v a) (macBoxF d N M z) t) x y -
        (Matrix.diagonal (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) *
          boxG (finalOp d L N' k v a) (macBoxF d N' M (e z)) t) (f x) (f y)‖ ≤
      (((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2 ∧
    ‖boxR (finalOp d L N k v a) (macBoxF d N M z) (fun u => ((macChi d N M z u : ℝ) : ℂ)) t x y -
        boxR (finalOp d L N' k v a) (macBoxF d N' M (e z))
          (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) t (f x) (f y)‖ ≤
      (((8 * M + 1) ^ d : ℕ) : ℝ) * ε * (finalGap d L + t)⁻¹ *
        (2 + (finalDecayC d L / finalGap d L + 1) * (((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2) := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hgt : 0 < finalGap d L + t := by linarith
  have hT0 : 0 < (finalGap d L + t)⁻¹ := inv_pos.2 hgt
  have hA0 := finalDecayC_pos (L := L) hd
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hU x hx y hy)
  set Yset : Finset (L1Torus d N) := Finset.univ.filter (fun u => u ∈ macRegion d N M C) with hYset
  have hYmem : ∀ u, u ∈ Yset ↔ u ∈ macRegion d N M C := fun u => by simp [hYset]
  obtain ⟨hBY, hinjY, hc, hc', hcY⟩ := boxFamily_twoTorus hM hN hN' hf he hC hYmem hzC
  have hBimg := macBoxF_image hM hN hN' hf (fun y μ => rfl) he (hC z hzC)
    (g := fun y μ => (((y μ).val : ℕ) : ZMod N))
  set B := macBoxF d N M z with hBdef
  have hBcard : (B.card : ℝ) ≤ (((8 * M + 1) ^ d : ℕ) : ℝ) := by
    exact_mod_cast card_macBoxF_le hM z
  set nB : ℝ := (((8 * M + 1) ^ d : ℕ) : ℝ) with hnBdef
  have hnB : 0 ≤ nB := by positivity
  have hBinj : Set.InjOn f (B : Set (L1Torus d N)) := hinjY.mono (by exact_mod_cast hBY)
  have hGc : ∀ u ∈ B, ∀ w ∈ B, ‖boxG (finalOp d L N k v a) B t u w -
      boxG (finalOp d L N' k v a) (B.image f) t (f u) (f w)‖ ≤
      nB ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2 := by
    intro u hu w hw
    have h := final_boxG_close (L := L) (k := k) (m := N) (m' := N') hd hv0 hv1 ha1 hmass ht B f
      hBinj (ε := ε) (fun p hp q hq => hU p ((hYmem p).1 (hBY hp)) q ((hYmem q).1 (hBY hq)))
      hu hw
    refine h.trans ?_
    have : (B.card : ℝ) ^ 2 ≤ nB ^ 2 := by gcongr
    have h2 : 0 ≤ ε * (finalGap d L + t)⁻¹ ^ 2 := by positivity
    calc (B.card : ℝ) ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2
        = (B.card : ℝ) ^ 2 * (ε * (finalGap d L + t)⁻¹ ^ 2) := by ring
      _ ≤ nB ^ 2 * (ε * (finalGap d L + t)⁻¹ ^ 2) := mul_le_mul_of_nonneg_right this h2
      _ = _ := by ring
  have hbG := final_boxG_entry_le (L := L) (k := k) hd hk hv0 hv1 ha1 ha2 hmass ht B
  have hc1 : ∀ u, ‖((macChi d N M z u : ℝ) : ℂ)‖ ≤ 1 := fun u => by
    rw [Complex.norm_real, Real.norm_of_nonneg (macChi_nonneg z u)]; exact macChi_le_one z u
  rw [hBimg]
  refine ⟨?_, ?_⟩
  · -- the box resolvent factor
    simp only [Matrix.diagonal_mul]
    by_cases hxB : x ∈ B
    · rw [← hcY x ((hYmem x).2 hx)]
      by_cases hyB : y ∈ B
      · rw [← mul_sub, norm_mul]
        calc _ ≤ 1 * (nB ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2) :=
              mul_le_mul (hc1 x) (hGc x hxB y hyB) (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      · have h0 : boxG (finalOp d L N k v a) B t x y = 0 := boxG_apply_of_not_mem hyB
        have h0' : boxG (finalOp d L N' k v a) (B.image f) t (f x) (f y) = 0 := by
          refine boxG_apply_of_not_mem ?_
          intro hmem
          obtain ⟨b, hb, hbf⟩ := Finset.mem_image.1 hmem
          exact hyB (by rw [← hinjY (hBY hb) ((hYmem y).2 hy) hbf]; exact hb)
        rw [h0, h0']; simp only [mul_zero, sub_zero, norm_zero]; positivity
    · have hcx : ((macChi d N M z x : ℝ) : ℂ) = 0 := by
        by_contra hne; exact hxB (hc x hne)
      rw [← hcY x ((hYmem x).2 hx), hcx]; simp only [zero_mul, sub_zero, norm_zero]; positivity
  · -- the defect
    have hshift : ∀ p ∈ Yset, ∀ q ∈ Yset,
        ‖shiftMat (finalOp d L N k v a) t p q - shiftMat (finalOp d L N' k v a) t (f p) (f q)‖ ≤ ε := by
      intro p hp q hq
      have hpq : (p = q) ↔ (f p = f q) := ⟨fun h => by rw [h], fun h => hinjY hp hq h⟩
      have : shiftMat (finalOp d L N k v a) t p q - shiftMat (finalOp d L N' k v a) t (f p) (f q) =
          finalOp d L N k v a p q - finalOp d L N' k v a (f p) (f q) := by
        simp only [shiftMat, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, hpq]
        ring
      rw [this]
      exact hU p ((hYmem p).1 hp) q ((hYmem q).1 hq)
    have hshift' : ∀ p ∈ Yset, ∀ q ∈ Yset,
        ‖shiftMat (finalOp d L N' k v a) t (f p) (f q)‖ ≤ finalDecayC d L + t := by
      intro p hp q hq
      simp only [shiftMat, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
      refine (norm_add_le _ _).trans (add_le_add (final_entry_le_decayC hd hk hv0 ha1 ha2 _ _) ?_)
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ht]
      split_ifs <;> simp [ht]
    have hrow := rowmul_close f hBY hinjY (U := finalOp d L N k v a) (U' := finalOp d L N' k v a)
      t hc hc' hcY hc1 (A := shiftMat (finalOp d L N k v a) t)
      (A' := shiftMat (finalOp d L N' k v a) t) (εA := ε) (aA := finalDecayC d L + t)
      (bG := 2 * (finalGap d L + t)⁻¹) (δG := nB ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2)
      hε0 (by positivity) (by positivity) (by positivity) hshift hshift'
      (fun u _ w => hbG u w) hGc ((hYmem x).2 hx) ((hYmem y).2 hy)
    unfold boxR
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_assoc, Matrix.mul_assoc]
    have hdiag : (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ))) x y =
        (Matrix.diagonal (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ))) (f x) (f y) := by
      simp only [Matrix.diagonal_apply]
      by_cases hxy : x = y
      · subst hxy; simp [hcY x ((hYmem x).2 hx)]
      · have h' : ¬ f x = f y := fun h => hxy (hinjY ((hYmem x).2 hx) ((hYmem y).2 hy) h)
        simp [hxy, h']
    rw [hdiag, sub_sub_sub_cancel_left, norm_sub_rev]
    refine hrow.trans ?_
    have hP : (finalDecayC d L + t) * (finalGap d L + t)⁻¹ ≤ finalDecayC d L / finalGap d L + 1 := by
      have h1 : finalDecayC d L * (finalGap d L + t)⁻¹ ≤ finalDecayC d L / finalGap d L := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ hg (by linarith)) hA0.le
      have h2 : t * (finalGap d L + t)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hgt]; linarith
      nlinarith
    have hBc : (B.card : ℝ) ≤ nB := hBcard
    have hmain : (B.card : ℝ) * (ε * (2 * (finalGap d L + t)⁻¹) +
        (finalDecayC d L + t) * (nB ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2)) ≤
        nB * ε * (finalGap d L + t)⁻¹ *
          (2 + (finalDecayC d L / finalGap d L + 1) * nB ^ 2) := by
      have e1 : ε * (2 * (finalGap d L + t)⁻¹) +
          (finalDecayC d L + t) * (nB ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2) =
          ε * (finalGap d L + t)⁻¹ *
            (2 + ((finalDecayC d L + t) * (finalGap d L + t)⁻¹) * nB ^ 2) := by ring
      rw [e1]
      have h3 : 0 ≤ ε * (finalGap d L + t)⁻¹ := by positivity
      calc (B.card : ℝ) * (ε * (finalGap d L + t)⁻¹ *
            (2 + ((finalDecayC d L + t) * (finalGap d L + t)⁻¹) * nB ^ 2))
          ≤ nB * (ε * (finalGap d L + t)⁻¹ *
            (2 + (finalDecayC d L / finalGap d L + 1) * nB ^ 2)) := by
            apply mul_le_mul hBc _ (by positivity) hnB
            apply mul_le_mul_of_nonneg_left _ h3
            gcongr
        _ = _ := by ring
    exact hmain

/-- **Closeness of the tagged `G_*` and the tagged defect `K` of the final operators on two tori**
at `x, y ∈ Y(C)`, parameters `s`, `s'` supported on `C`, `e C`, equal along `e`, `‖s p‖ ≤ e^κ`. -/
theorem final_taggedGK_close (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {ε κ : ℝ} (hκ : 0 ≤ κ)
    (hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε)
    {t : ℝ} (ht : 0 ≤ t)
    {s : MacIdx d N M → ℂ} (hs : s ∈ supportedOn C)
    {s' : MacIdx d N' M → ℂ} (hs' : s' ∈ supportedOn (C.image e))
    (hss : ∀ i ∈ C, s' (e i) = s i) (hsκ : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {x y : L1Torus d N} (hx : x ∈ macRegion d N M C) (hy : y ∈ macRegion d N M C) :
    ‖taggedG Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
          (macTags d N M) (finalOp d L N k v a) t s x y -
        taggedG Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
          (macTags d N' M) (finalOp d L N' k v a) t s' (f x) (f y)‖ ≤
      (C.card : ℝ) * Real.exp (κ * C.card) *
        ((((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2) ∧
    ‖taggedK Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
          (macTags d N M) (finalOp d L N k v a) t s x y -
        taggedK Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
          (macTags d N' M) (finalOp d L N' k v a) t s' (f x) (f y)‖ ≤
      (C.card : ℝ) * Real.exp (κ * C.card) *
        ((((8 * M + 1) ^ d : ℕ) : ℝ) * ε * (finalGap d L + t)⁻¹ *
          (2 + (finalDecayC d L / finalGap d L + 1) * (((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2)) := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hU x hx y hy)
  refine ⟨?_, ?_⟩
  · unfold taggedG
    exact taggedMat_close_twoTorus hM hN hN' hf he hC hκ (by positivity)
      (fun z hzC u hu w hw => (final_boxFamily_close hM hN hN' hf he hC hd hk hv0 hv1 ha1 ha2
        hmass hU ht hzC hu hw).1) hs hs' hss hsκ hx hy
  · unfold taggedK
    have hpos : 0 ≤ (((8 * M + 1) ^ d : ℕ) : ℝ) * ε * (finalGap d L + t)⁻¹ *
        (2 + (finalDecayC d L / finalGap d L + 1) * (((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2) := by
      have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
      have hg := finalGap_pos (d := d) hL
      have hA0 := finalDecayC_pos (L := L) hd
      have hgt : 0 < finalGap d L + t := by linarith
      positivity
    exact taggedMat_close_twoTorus hM hN hN' hf he hC hκ hpos
      (fun z hzC u hu w hw => (final_boxFamily_close hM hN hN' hf he hC hd hk hv0 hv1 ha1 ha2
        hmass hU ht hzC hu hw).2) hs hs' hss hsκ hx hy

/-- Entries of the inverse of `1 - K` for the tagged defect of the final operator: the row sums
are at most `4/3` for `s` in the polydisc (the weight `1` case of `taggedGfin_row_bound`). -/
theorem final_inv_one_sub_taggedK (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {s : MacIdx d N M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) :
    IsUnit (1 - taggedK Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
      (macTags d N M) (finalOp d L N k v a) t s) ∧
    ∀ x y, ‖(1 - taggedK Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
      (macTags d N M) (finalOp d L N k v a) t s)⁻¹ x y‖ ≤ 4 / 3 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hε := pdEps_pos (d := d) (L := L) hd
  have hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M := by linarith
  have hq : pdB d L * Real.exp (pdH d * κ) / M ≤ 1 / 4 := by
    rw [div_le_iff₀ hM']; linarith
  have hinv := weightedRow_inv_le (fun _ _ : L1Torus d N => (1 : ℝ)) (fun _ _ => le_rfl)
    (fun _ => rfl) (fun _ _ _ => by norm_num)
    (taggedK Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
      (macTags d N M) (finalOp d L N k v a) t s) (q := 1 / 4) (by norm_num)
    (fun x => by
      have h := taggedK_row_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ le_rfl (by positivity) hκM
        hs x
      simp only [zero_mul, Real.exp_zero, one_mul] at h
      simpa using h.trans hq)
  refine ⟨hinv.1, fun x y => ?_⟩
  have h43 : 1 / (1 - (1 / 4 : ℝ)) = 4 / 3 := by norm_num
  have := hinv.2 x
  rw [h43] at this
  refine le_trans ?_ this
  simpa using Finset.single_le_sum (f := fun y => ‖(1 - taggedK Finset.univ (macBoxF d N M)
    (fun z u => ((macChi d N M z u : ℝ) : ℂ)) (macTags d N M) (finalOp d L N k v a) t s)⁻¹ x y‖)
    (fun y _ => norm_nonneg _) (Finset.mem_univ y)

theorem final_taggedG_entry_le (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {s : MacIdx d N M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (x y : L1Torus d N) :
    ‖taggedG Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
      (macTags d N M) (finalOp d L N k v a) t s x y‖ ≤
      2 * Real.exp (pdH d * κ) * (finalGap d L + t)⁻¹ := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hε := pdEps_pos (d := d) (L := L) hd
  have hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M := by
    have : (0 : ℝ) ≤ κ * 7 ^ d := by positivity
    nlinarith
  have h := taggedG_weighted_entry_bound hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ le_rfl (by positivity)
    hκM hs x y
  simp only [zero_mul, Real.exp_zero, one_mul] at h
  refine h.trans ?_
  have : Real.exp (-(pdEps d L / 2) * dist x y) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [dist_nonneg (x := x) (y := y)])
  have h2 : 0 ≤ 2 * Real.exp (pdH d * κ) / (finalGap d L + t) := by positivity
  calc 2 * Real.exp (pdH d * κ) / (finalGap d L + t) * _ ≤
      2 * Real.exp (pdH d * κ) / (finalGap d L + t) * 1 := mul_le_mul_of_nonneg_left this h2
    _ = _ := by rw [mul_one, div_eq_mul_inv]

/-- **Closeness of the tagged parametrix `G_fin` of the final operators on two tori.**  The
constant `P` depends on `d`, `L`, `M`, `κ` and a bound `nC` for the number of cells of `C` only
(not on `k`, the window `v, a`, the sides `N`, `N'`, or `t`); `ε` bounds the difference of the
operators on `Y(C)²`.  Parameters `s`, `s'` are supported on `C`, `e C`, equal along `e`, with
`‖s p‖ ≤ e^κ`; the sites `x, y` lie in `Y(C)`; `t ≥ 0`. -/
theorem final_taggedGfin_close (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (nC : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ {k J N N' : ℕ} [NeZero N] [NeZero N'], 1 ≤ k →
      2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' → ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {ε : ℝ}, (∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
        ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε) →
      ∀ {t : ℝ}, 0 ≤ t →
      ∀ {s : MacIdx d N M → ℂ}, s ∈ supportedOn C →
      ∀ {s' : MacIdx d N' M → ℂ}, s' ∈ supportedOn (C.image e) →
      (∀ i ∈ C, s' (e i) = s i) → (∀ p, ‖s p‖ ≤ Real.exp κ) →
      ∀ {x y : L1Torus d N}, x ∈ macRegion d N M C → y ∈ macRegion d N M C →
      ‖taggedGfin Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
            (macTags d N M) (finalOp d L N k v a) t s x y -
          taggedGfin Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
            (macTags d N' M) (finalOp d L N' k v a) t s' (f x) (f y)‖ ≤
        P * ε * (finalGap d L + t)⁻¹ := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hA0 := finalDecayC_pos (L := L) hd
  set nB : ℝ := (((8 * M + 1) ^ d : ℕ) : ℝ) with hnBdef
  have hnB : 0 ≤ nB := by positivity
  set cc : ℝ := (nC : ℝ) * Real.exp (κ * nC) with hcc
  set nY : ℝ := (nC : ℝ) * nB with hnY
  set P0 : ℝ := finalDecayC d L / finalGap d L + 1 with hP0
  have hP00 : 0 ≤ P0 := by positivity
  set Hk : ℝ := Real.exp (pdH d * κ) with hHk
  set a1 : ℝ := nY * (4 / 3) * cc * nB ^ 2 * (finalGap d L)⁻¹ +
    nY ^ 3 * (2 * Hk * (4 / 3 * (4 / 3)) * (cc * (nB * (2 + P0 * nB ^ 2)))) * (finalGap d L)⁻¹
    with ha1def
  refine ⟨a1, by positivity, ?_⟩
  intro k J N N' _ _ hk hN hN' f hf e he C hCc hC v a hv0 hv1 ha1' ha2 hmass ε hU t ht s hs s' hs'
    hss hsκ x y hx hy
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hU x hx y hy)
  have hgt : 0 < finalGap d L + t := by linarith
  set gT : ℝ := (finalGap d L + t)⁻¹ with hgT
  have hgT0 : 0 < gT := inv_pos.2 hgt
  have hgTg : gT ≤ (finalGap d L)⁻¹ := inv_anti₀ hg (by linarith)
  -- the tag parameter on the second torus
  have hsκ' : ∀ p, ‖s' p‖ ≤ Real.exp κ := by
    intro p
    by_cases hp : p ∈ C.image e
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      rw [hss i hi]; exact hsκ i
    · rw [hs' p hp, norm_zero]; exact (Real.exp_pos _).le
  obtain ⟨hGc, hKc⟩ := final_taggedGK_close hM hN hN' hf he hC hd hk hv0 hv1 ha1' ha2 hmass hκ hU
    ht hs hs' hss hsκ hx hy
  -- the sets
  set Yset : Finset (L1Torus d N) := Finset.univ.filter (fun u => u ∈ macRegion d N M C) with hYset
  have hYmem : ∀ u, u ∈ Yset ↔ u ∈ macRegion d N M C := fun u => by simp [hYset]
  set Y'set : Finset (L1Torus d N') :=
    Finset.univ.filter (fun u => u ∈ macRegion d N' M (C.image e)) with hY'set
  have hY'mem : ∀ u, u ∈ Y'set ↔ u ∈ macRegion d N' M (C.image e) := fun u => by simp [hY'set]
  obtain ⟨g, hg'⟩ : ∃ g : L1Torus d N' → L1Torus d N, ∀ y μ, g y μ = (((y μ).val : ℕ) : ZMod N) :=
    ⟨fun y μ => (((y μ).val : ℕ) : ZMod N), fun _ _ => rfl⟩
  have hbij : Set.BijOn f (Yset : Set (L1Torus d N)) (Y'set : Set (L1Torus d N')) := by
    have := macRegion_bijOn hM hN hN' hf hg' he hC
    simpa [hYset, hY'set] using this
  have hYcard : (Yset.card : ℝ) ≤ nY := by
    have h1 : Yset = C.biUnion (macBoxF d N M) := by
      ext u; rw [hYmem, mem_biUnion_macBoxF]
    rw [h1]
    calc ((C.biUnion (macBoxF d N M)).card : ℝ) ≤ (C.card : ℝ) * nB := by
          have := card_biUnion_macBoxF_le hM C
          rw [hnBdef]; exact_mod_cast this
      _ ≤ nY := by
          rw [hnY]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hCc) hnB
  have hY0 : (0 : ℝ) ≤ Yset.card := by positivity
  obtain ⟨hu, hinv⟩ := final_inv_one_sub_taggedK (L := L) (k := k) (N := N) hd hk hv0 hv1 ha1' ha2
    hmass ht hM hκ hMB hMκ hsκ
  obtain ⟨hu', hinv'⟩ := final_inv_one_sub_taggedK (L := L) (k := k) (N := N') hd hk hv0 hv1 ha1'
    ha2 hmass ht hM hκ hMB hMκ hsκ'
  have hgG := final_taggedG_entry_le (L := L) (k := k) (N := N') hd hk hv0 hv1 ha1' ha2 hmass ht hM
    hκ hMκ hsκ'
  have hcc0 : 0 ≤ cc := by positivity
  have hCc' : (C.card : ℝ) * Real.exp (κ * C.card) ≤ cc := by
    rw [hcc]
    apply mul_le_mul (by exact_mod_cast hCc) _ (Real.exp_pos _).le (by positivity)
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by exact_mod_cast hCc) hκ)
  set δG : ℝ := cc * (nB ^ 2 * ε * gT ^ 2) with hδG
  set δK : ℝ := cc * (nB * ε * gT * (2 + P0 * nB ^ 2)) with hδK
  have hδG0 : 0 ≤ δG := by positivity
  have hδK0 : 0 ≤ δK := by positivity
  have hGG : ∀ p ∈ Yset, ∀ q ∈ Yset, ‖taggedG Finset.univ (macBoxF d N M)
      (fun z u => ((macChi d N M z u : ℝ) : ℂ)) (macTags d N M) (finalOp d L N k v a) t s p q -
      taggedG Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
        (macTags d N' M) (finalOp d L N' k v a) t s' (f p) (f q)‖ ≤ δG := by
    intro p hp q hq
    refine (final_taggedGK_close hM hN hN' hf he hC hd hk hv0 hv1 ha1' ha2 hmass hκ hU ht hs hs' hss
      hsκ ((hYmem p).1 hp) ((hYmem q).1 hq)).1.trans ?_
    exact mul_le_mul_of_nonneg_right hCc' (by positivity)
  have hKK : ∀ p ∈ Yset, ∀ q ∈ Yset, ‖taggedK Finset.univ (macBoxF d N M)
      (fun z u => ((macChi d N M z u : ℝ) : ℂ)) (macTags d N M) (finalOp d L N k v a) t s p q -
      taggedK Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
        (macTags d N' M) (finalOp d L N' k v a) t s' (f p) (f q)‖ ≤ δK := by
    intro p hp q hq
    refine (final_taggedGK_close hM hN hN' hf he hC hd hk hv0 hv1 ha1' ha2 hmass hκ hU ht hs hs' hss
      hsκ ((hYmem p).1 hp) ((hYmem q).1 hq)).2.trans ?_
    exact mul_le_mul_of_nonneg_right hCc' (by positivity)
  have hmain := ysupp_close (G := taggedG Finset.univ (macBoxF d N M)
      (fun z u => ((macChi d N M z u : ℝ) : ℂ)) (macTags d N M) (finalOp d L N k v a) t s)
    (K := taggedK Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
      (macTags d N M) (finalOp d L N k v a) t s)
    (G' := taggedG Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
      (macTags d N' M) (finalOp d L N' k v a) t s')
    (K' := taggedK Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
      (macTags d N' M) (finalOp d L N' k v a) t s') f hbij
    (fun a b h => ⟨(hYmem a).2 (taggedMat_ne_zero_mem hM hd _ hs h).1,
      (hYmem b).2 (taggedMat_ne_zero_mem hM hd _ hs h).2⟩)
    (fun a b h => ⟨(hYmem a).2 (taggedMat_ne_zero_mem hM hd _ hs h).1,
      (hYmem b).2 (taggedMat_ne_zero_mem hM hd _ hs h).2⟩)
    (fun a b h => ⟨(hY'mem a).2 (taggedMat_ne_zero_mem hM hd _ hs' h).1,
      (hY'mem b).2 (taggedMat_ne_zero_mem hM hd _ hs' h).2⟩)
    (fun a b h => ⟨(hY'mem a).2 (taggedMat_ne_zero_mem hM hd _ hs' h).1,
      (hY'mem b).2 (taggedMat_ne_zero_mem hM hd _ hs' h).2⟩)
    (δG := δG) (δK := δK) (g₁ := 2 * Hk * gT) (a₁ := 4 / 3) hδG0 hδK0 (by positivity)
    (by norm_num) hGG hKK hgG hinv hinv' hu hu' ((hYmem x).2 hx) ((hYmem y).2 hy)
  unfold taggedGfin
  refine hmain.trans ?_
  -- arithmetic
  have hpos : 0 ≤ δG * (4 / 3) := by positivity
  calc (Yset.card : ℝ) * (δG * (4 / 3)) + (Yset.card : ℝ) ^ 3 *
        (2 * Hk * gT * (4 / 3 * (4 / 3 * δK)))
      ≤ nY * (δG * (4 / 3)) + nY ^ 3 * (2 * Hk * gT * (4 / 3 * (4 / 3 * δK))) := by
        gcongr
    _ = ε * gT * (nY * (4 / 3) * cc * nB ^ 2 * gT +
          nY ^ 3 * (2 * Hk * (4 / 3 * (4 / 3)) * (cc * (nB * (2 + P0 * nB ^ 2)))) * gT) := by
        rw [hδG, hδK]; ring
    _ ≤ ε * gT * (nY * (4 / 3) * cc * nB ^ 2 * (finalGap d L)⁻¹ +
          nY ^ 3 * (2 * Hk * (4 / 3 * (4 / 3)) * (cc * (nB * (2 + P0 * nB ^ 2)))) *
            (finalGap d L)⁻¹) := by
        gcongr
    _ = a1 * ε * gT := by rw [ha1def]; ring

/-- **Closeness of the Stieltjes family `taggedCfinU` of the final operators on two tori.**  The
Stieltjes integral of `final_taggedGfin_close`: the entries differ by at most `P ε / √g`, with the
same constant `P` (which does not depend on `k`). -/
theorem final_taggedCfinU_close (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (nC : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ {k J N N' : ℕ} [NeZero N] [NeZero N'], 1 ≤ k →
      2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' → ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {ε : ℝ}, (∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
        ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε) →
      ∀ {s : MacIdx d N M → ℂ}, s ∈ supportedOn C →
      ∀ {s' : MacIdx d N' M → ℂ}, s' ∈ supportedOn (C.image e) →
      (∀ i ∈ C, s' (e i) = s i) → (∀ p, ‖s p‖ ≤ Real.exp κ) →
      ∀ {x y : L1Torus d N}, x ∈ macRegion d N M C → y ∈ macRegion d N M C →
      ‖taggedCfinU d N M (finalOp d L N k v a) s x y -
          taggedCfinU d N' M (finalOp d L N' k v a) s' (f x) (f y)‖ ≤
        P * ε / Real.sqrt (finalGap d L) := by
  classical
  obtain ⟨P, hP0, hP⟩ := final_taggedGfin_close (L := L) hd hM hκ hMB hMκ nC
  refine ⟨P, hP0, ?_⟩
  intro k J N N' _ _ hk hN hN' f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass ε hU s hs s' hs' hss
    hsκ x y hx hy
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hU x hx y hy)
  have hsκ' : ∀ p, ‖s' p‖ ≤ Real.exp κ := by
    intro p
    by_cases hp : p ∈ C.image e
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      rw [hss i hi]; exact hsκ i
    · rw [hs' p hp, norm_zero]; exact (Real.exp_pos _).le
  have hint1 := taggedCfin_integrable (L := L) (N₀ := N) (k := k) (M := M) hd hk hv0 hv1 ha1 ha2
    hmass hM hκ hMB hMκ hsκ x y
  have hint2 := taggedCfin_integrable (L := L) (N₀ := N') (k := k) (M := M) hd hk hv0 hv1 ha1 ha2
    hmass hM hκ hMB hMκ hsκ' (f x) (f y)
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  rw [taggedCfinU_apply, taggedCfinU_apply, ← mul_sub, ← integral_sub hint1 hint2]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hint : Integrable (fun r : ℝ => (P * ε) * (r ^ (-(1 / 2 : ℝ)) * (finalGap d L + r)⁻¹)) μ :=
    (Localization.integrableOn_rpow_inv_add hg).const_mul (P * ε)
  have hbound := norm_integral_le_of_norm_le
    (f := fun r : ℝ => ((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        taggedGfin Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
          (macTags d N M) (finalOp d L N k v a) r s x y -
      ((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        taggedGfin Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
          (macTags d N' M) (finalOp d L N' k v a) r s' (f x) (f y))
    hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => by
      have hr0 : 0 < r := mem_Ioi.mp hr
      have h3 : 0 < r ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hr0 _
      have hres := hP hk hN hN' hf he hCc hC hv0 hv1 ha1 ha2 hmass hU hr0.le hs hs' hss hsκ hx hy
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le]
      calc r ^ (-(1 / 2 : ℝ)) * ‖_‖ ≤ r ^ (-(1 / 2 : ℝ)) * (P * ε * (finalGap d L + r)⁻¹) :=
            mul_le_mul_of_nonneg_left hres h3.le
        _ = _ := by ring))
  rw [integral_const_mul, Localization.integral_rpow_inv_add hg] at hbound
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : 0 < Real.sqrt (finalGap d L) := Real.sqrt_pos.2 hg
  calc 1 / Real.pi * ‖_‖ ≤ 1 / Real.pi * (P * ε * (Real.pi / Real.sqrt (finalGap d L))) := by
        gcongr
    _ = _ := by field_simp

/-- A site of the window, lifted by the identity on residues. -/
theorem castL1_val_eq (x : L1Torus d N) :
    castL1 N (fun μ => (((x μ).val : ℕ) : ℤ)) = x := by
  funext μ
  simp [castL1, castTorus]

omit [NeZero N'] in
theorem castL1_val_f {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) (x : L1Torus d N) :
    castL1 N' (fun μ => (((x μ).val : ℕ) : ℤ)) = f x := by
  funext μ
  simp [castL1, castTorus, hf]

/-- **The entries of the final operators of two tori on the window `Y(C)`** differ by at most
`C₀ exp(-c₀ (min N N' / 2 - (J + 3) M))` (`C₀`, `c₀` depend on `d`, `L`, `k` only). -/
theorem final_region_entry_close (hd : 0 < d) :
    ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧ ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 →
      ∀ {M J N N' : ℕ} [NeZero N] [NeZero N'], 0 < M → 2 * (J + 6) * M ≤ N →
      2 * (J + 6) * M ≤ N' → ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {C : Finset (MacIdx d N M)}, (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤
        C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ))) := by
  obtain ⟨C, c, hC, hc, hmain⟩ := finalOp_entry_close (d := d) (L := L) (k := k) hd
  refine ⟨C * Real.exp (3 / 2 * c), c, by positivity, hc, ?_⟩
  intro v a hv0 hv1 ha1 ha2 M J N N' _ _ hM hN hN' f hf C' hC' x hx y hy
  set S := min N N' with hS
  have hSN : S ≤ N := min_le_left _ _
  have hSN' : S ≤ N' := min_le_right _ _
  have hS2 : 2 * (J + 6) * M ≤ S := le_min hN hN'
  set W := (J + 3) * M with hW
  have hW3 : (J + 6) * M = W + 3 * M := by rw [hW]; ring
  have hS3 : 2 * (W + 3 * M) ≤ S := by rw [← hW3, ← mul_assoc]; exact hS2
  have hxm := mid_of_mem_macRegion hM hN hC' hx
  have hym := mid_of_mem_macRegion hM hN hC' hy
  have hxbox : (fun μ => (((x μ).val : ℕ) : ℤ)) ∈ sqBox d W := by
    rw [mem_sqBox]; intro μ
    have := (hxm μ).2
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast this.le
  have hybox : (fun μ => (((y μ).val : ℕ) : ℤ)) ∈ sqBox d W := by
    rw [mem_sqBox]; intro μ
    have := (hym μ).2
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast this.le
  have h := hmain hv0 hv1 ha1 ha2 (m := N) (m' := N') (Rm := (S - 2) / 2) (Rc := W)
    (by omega) (by omega) (by omega) hxbox hybox
  rw [castL1_val_eq, castL1_val_eq, castL1_val_f hf, castL1_val_f hf] at h
  refine h.trans ?_
  have hRm : (S : ℝ) / 2 - 3 / 2 ≤ (((S - 2) / 2 : ℕ) : ℝ) := by
    have : S ≤ 2 * ((S - 2) / 2) + 3 := by omega
    have h' : (S : ℝ) ≤ 2 * (((S - 2) / 2 : ℕ) : ℝ) + 3 := by exact_mod_cast this
    linarith
  have : Real.exp (-c * ((((S - 2) / 2 : ℕ) : ℝ) - (W : ℝ))) ≤
      Real.exp (3 / 2 * c) * Real.exp (-c * ((S : ℝ) / 2 - (W : ℝ))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith
  calc C * Real.exp (-c * ((((S - 2) / 2 : ℕ) : ℝ) - (W : ℝ)))
      ≤ C * (Real.exp (3 / 2 * c) * Real.exp (-c * ((S : ℝ) / 2 - (W : ℝ)))) :=
        mul_le_mul_of_nonneg_left this hC.le
    _ = _ := by ring

/-- **Box resolvents of the final operators on two tori (explicit error).**  For a cell `z ∈ C` and
`x, y ∈ Y(C)`, the entries of `χ_z G_z` differ by at most
`(8M+1)^{2d} C₀ exp(-c₀ (min N N' / 2 - (J+3) M)) (g + t)⁻²`; `C₀`, `c₀` depend on `d`, `L`, `k`. -/
theorem final_boxG_close_twoTorus (hd : 0 < d) {k : ℕ} (hk : 1 ≤ k) {M : ℕ} (hM : 0 < M) :
    ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧
      ∀ {J N N' : ℕ} [NeZero N] [NeZero N'], 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)},
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {t : ℝ}, 0 ≤ t → ∀ {z : MacIdx d N M}, z ∈ C →
      ∀ {x y : L1Torus d N}, x ∈ macRegion d N M C → y ∈ macRegion d N M C →
      ‖(Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N k v a) (macBoxF d N M z) t) x y -
        (Matrix.diagonal (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) *
          boxG (finalOp d L N' k v a) (macBoxF d N' M (e z)) t) (f x) (f y)‖ ≤
      (((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2 *
        (C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ)))) *
        (finalGap d L + t)⁻¹ ^ 2 := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hmain⟩ := final_region_entry_close (d := d) (L := L) (k := k) hd
  refine ⟨C₀, c₀, hC₀, hc₀, ?_⟩
  intro J N N' _ _ hN hN' f hf e he C hC v a hv0 hv1 ha1 ha2 hmass t ht z hzC x y hx hy
  refine (final_boxFamily_close hM hN hN' hf he hC hd hk hv0 hv1 ha1 ha2 hmass
    (fun p hp q hq => hmain hv0 hv1 ha1 ha2 hM hN hN' hf hC p hp q hq) ht hzC hx hy).1.trans ?_
  apply le_of_eq
  ring

/-- **The tagged parametrix `G_fin` of the final operators on two tori, explicit error.**  For
`s` supported on `C`, `s'` on `e C` (equal along `e`), `‖s p‖ ≤ e^κ`, `x, y ∈ Y(C)`, `t ≥ 0`: the
entries differ by at most `P C₀ exp(-c₀ (min N N' / 2 - (J+3) M)) (g + t)⁻¹`.  `P` depends on
`d, L, M, κ, nC` only; `C₀, c₀` also on `k` (through `finalOp_entry_close`). -/
theorem final_taggedGfin_close_twoTorus (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (nC : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ {k : ℕ}, 1 ≤ k → ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧
      ∀ {J N N' : ℕ} [NeZero N] [NeZero N'], 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {s : MacIdx d N M → ℂ}, s ∈ supportedOn C →
      ∀ {s' : MacIdx d N' M → ℂ}, s' ∈ supportedOn (C.image e) →
      (∀ i ∈ C, s' (e i) = s i) → (∀ p, ‖s p‖ ≤ Real.exp κ) →
      ∀ {x y : L1Torus d N}, x ∈ macRegion d N M C → y ∈ macRegion d N M C →
      ∀ {t : ℝ}, 0 ≤ t →
      ‖taggedGfin Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
            (macTags d N M) (finalOp d L N k v a) t s x y -
          taggedGfin Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
            (macTags d N' M) (finalOp d L N' k v a) t s' (f x) (f y)‖ ≤
        P * (C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ)))) *
          (finalGap d L + t)⁻¹ := by
  obtain ⟨P, hP0, hP⟩ := final_taggedGfin_close (L := L) hd hM hκ hMB hMκ nC
  refine ⟨P, hP0, ?_⟩
  intro k hk
  obtain ⟨C₀, c₀, hC₀, hc₀, hmain⟩ := final_region_entry_close (d := d) (L := L) (k := k) hd
  refine ⟨C₀, c₀, hC₀, hc₀, ?_⟩
  intro J N N' _ _ hN hN' f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass s hs s' hs' hss hsκ x y hx hy
    t ht
  exact hP hk hN hN' hf he hCc hC hv0 hv1 ha1 ha2 hmass
    (fun p hp q hq => hmain hv0 hv1 ha1 ha2 hM hN hN' hf hC p hp q hq) ht hs hs' hss hsκ hx hy

/-- **The Stieltjes family `taggedCfinU` of the final operators on two tori, explicit error**: the
entries differ by at most `P C₀ exp(-c₀ (min N N' / 2 - (J+3) M)) / √g`, same constants as
`final_taggedGfin_close_twoTorus`. -/
theorem final_taggedCfinU_close_twoTorus (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (nC : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ {k : ℕ}, 1 ≤ k → ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧
      ∀ {J N N' : ℕ} [NeZero N] [NeZero N'], 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {s : MacIdx d N M → ℂ}, s ∈ supportedOn C →
      ∀ {s' : MacIdx d N' M → ℂ}, s' ∈ supportedOn (C.image e) →
      (∀ i ∈ C, s' (e i) = s i) → (∀ p, ‖s p‖ ≤ Real.exp κ) →
      ∀ {x y : L1Torus d N}, x ∈ macRegion d N M C → y ∈ macRegion d N M C →
      ‖taggedCfinU d N M (finalOp d L N k v a) s x y -
          taggedCfinU d N' M (finalOp d L N' k v a) s' (f x) (f y)‖ ≤
        P * (C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ)))) /
          Real.sqrt (finalGap d L) := by
  obtain ⟨P, hP0, hP⟩ := final_taggedCfinU_close (L := L) hd hM hκ hMB hMκ nC
  refine ⟨P, hP0, ?_⟩
  intro k hk
  obtain ⟨C₀, c₀, hC₀, hc₀, hmain⟩ := final_region_entry_close (d := d) (L := L) (k := k) hd
  refine ⟨C₀, c₀, hC₀, hc₀, ?_⟩
  intro J N N' _ _ hN hN' f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass s hs s' hs' hss hsκ x y hx hy
  exact hP hk hN hN' hf he hCc hC hv0 hv1 ha1 ha2 hmass
    (fun p hp q hq => hmain hv0 hv1 ha1 ha2 hM hN hN' hf hC p hp q hq) hs hs' hss hsκ hx hy

end FinalBoxes

end Balaban.Green
