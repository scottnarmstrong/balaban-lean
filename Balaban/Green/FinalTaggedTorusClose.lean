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
public import Balaban.Green.FinalInteractionCutoff
public import Balaban.Green.FinalDetRatio

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

* `rowmul_close`, `taggedMat_close_twoTorus`: approximate `rowmul_transport` and
  `taggedMat_entry_twoTorus`;
* `final_boxFamily_close` (and `final_boxG_close_twoTorus` with the explicit error): the entries
  of `χ_z G_z` differ by at most `|B|² ε / (g + t)²`, those of the defect `R_z` by
  `|B| ε (g + t)⁻¹ (2 + (A / g + 1) |B|²)`;
* `final_taggedGK_close`, `final_taggedKE_close`: the entries of `G_*`, `K`, and of the perturbed
  defect `K_E`;
* `ysupp_close`, `mul_inv_close`: perturbation of `G (1 - K)⁻¹` on a block;
* `final_taggedGfin_close`, `final_taggedGfin_close_twoTorus`: entries of `G_fin(s, t)`, at most
  `P ε / (g + t)`;
* `final_taggedCfinU_close`, `final_taggedCfinU_close_twoTorus`: entries of the Stieltjes family
  `taggedCfinU`, at most `P ε / √g`;
* `final_region_entry_close`: `ε = C₀ exp(-c₀ (min N N' / 2 - (J+3) M))` for the final operators
  (from `finalOp_entry_close`).

The constant `P` depends on `d`, `L`, `M`, `κ` and a bound on the number of cells of `C` only,
not on `k`, the window `(v, a)`, the sides `N`, `N'` or `t`; `C₀`, `c₀` depend on `k` (through
`finalOp_entry_close`).

**Coefficients.**
* `coef_sub_open`, `norm_coef_sub_relabel_le`: the Cauchy estimate
  `‖coef f C - coef f' (e C)‖ ≤ B / (R - 1)^{|C|}` for two analytic functions that differ by at
  most `B` on corresponding cut parameters supported on `C`, `e C`.
* `integral_cutoff_close`, `final_coef_cutoffInteraction_close_twoTorus`: the localized
  coefficients of the cutoff interaction `∫_{box ρ} F (C_fin(s) ψ) dγ(ψ)` on the two tori differ by
  at most `Lip |Y(C)| δ ρ γ(box ρ) / (e^κ - 1)^{|C|}`, `δ` the entry error of
  `final_taggedCfinU_close_twoTorus`; `F`, `F'` correspond up to a Lipschitz bound `hFclose`
  (the exact correspondence `hF` of `TwoTorusFinal` is the case `η = 0`).
* `trace_series_close`, `logdet_close_abstract`, `logdet_close_blocks`,
  `final_coef_logdet_close_twoTorus`: for `(rE, η)`-small perturbations `E`, `E'` close up to `εE`
  on `Y(C)²`, the localized coefficients of the logarithms of `det (1 - K_E(s, t))` on the two
  tori differ by at most `P (ε + εE) / (e^κ - 1)^{|C|}` (trace series of the block
  `K_E` restricted to `Y(C)`).
-/

@[expose] public section

open Finset Matrix MeasureTheory Set Balaban.Localization Balaban.Analysis

namespace Balaban.Green

section Generic

variable {X X' : Type*} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']

/-- The sum form of `rowmul_close`: the entry of `A (diag c ⬝ G_B)` along an injective
correspondence differs from that of `A' (diag c' ⬝ G'_{f B})` by at most the sum over the box of
any pointwise bound `β` of the differences of the summands. -/
theorem rowmul_close_core (f : X → X') {B : Finset X} (hBinj : Set.InjOn f (B : Set X))
    {U : Matrix X X ℂ} {U' : Matrix X' X' ℂ} (t : ℝ) {c : X → ℂ} {c' : X' → ℂ}
    (hc : ∀ u, c u ≠ 0 → u ∈ B) (hc' : ∀ u, c' u ≠ 0 → u ∈ B.image f)
    {A : Matrix X X ℂ} {A' : Matrix X' X' ℂ} {β : X → ℝ} {x y : X}
    (hpt : ∀ u ∈ B, ‖A x u * (c u * boxG U B t u y) -
        A' (f x) (f u) * (c' (f u) * boxG U' (B.image f) t (f u) (f y))‖ ≤ β u) :
    ‖(A * (Matrix.diagonal c * boxG U B t)) x y -
        (A' * (Matrix.diagonal c' * boxG U' (B.image f) t)) (f x) (f y)‖ ≤ ∑ u ∈ B, β u := by
  classical
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
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum hpt)

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
  refine (rowmul_close_core f hBinj t hc hc' (β := fun _ => εA * bG + aA * δG) ?_).trans ?_
  · intro u hu
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
  · rw [Finset.sum_const, nsmul_eq_mul]

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

/-- Core of the two-torus closeness of tagged matrices: the difference at `x, y ∈ Y(C)` is at
most the sum over the cells `z ∈ C` with `macTags z x y ⊆ C` of `‖tagMon‖` times the entry
difference. -/
theorem taggedMat_close_twoTorus_core (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    {a : MacIdx d N M → Matrix (L1Torus d N) (L1Torus d N) ℂ}
    {a' : MacIdx d N' M → Matrix (L1Torus d N') (L1Torus d N') ℂ}     {s : MacIdx d N M → ℂ} (hs : s ∈ Balaban.Localization.supportedOn C)
    {s' : MacIdx d N' M → ℂ} (hs' : s' ∈ Balaban.Localization.supportedOn (C.image e))
    (hss : ∀ i ∈ C, s' (e i) = s i)
    {x y : L1Torus d N} (hx : x ∈ macRegion d N M C)
    (hy : y ∈ macRegion d N M C) :
    ‖taggedMat Finset.univ (macTags d N M) a s x y -
      taggedMat Finset.univ (macTags d N' M) a' s' (f x) (f y)‖ ≤
      ∑ z ∈ C.filter (fun z => macTags d N M z x y ⊆ C),
        ‖tagMon (macTags d N M z x y) s‖ * ‖a z x y - a' (e z) (f x) (f y)‖ := by
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
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz => ?_)
  obtain ⟨hzC, hVC⟩ := Finset.mem_filter.1 hz
  rw [hVimg z hzC]
  have hprod : tagMon (macTags d N M z x y) s =
      tagMon ((macTags d N M z x y).image e) s' := by
    unfold tagMon
    rw [Finset.prod_image (hinjE.mono (by intro w hw; exact hVC hw))]
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [hss w (hVC hw)]
  rw [hprod, ← mul_sub, norm_mul]

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
  refine (taggedMat_close_twoTorus_core hM hN hN' hf he hC hs hs' hss hx hy).trans ?_
  calc _ ≤ ∑ _z ∈ C.filter (fun z => macTags d N M z x y ⊆ C), Real.exp (κ * C.card) * δ := by
        refine Finset.sum_le_sum fun z hz => ?_
        obtain ⟨hzC, hVC⟩ := Finset.mem_filter.1 hz
        have hT : ‖tagMon (macTags d N M z x y) s‖ ≤ Real.exp (κ * C.card) := by
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

theorem sum_finset_subtype_le {α : Type*} [Fintype α] (Y : Finset α) (h : α → ℝ)
    (h0 : ∀ a, 0 ≤ h a) : ∑ j : ↥Y, h j ≤ ∑ a, h a := by
  classical
  rw [Finset.sum_coe_sort Y h]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => h0 a)

omit [DecidableEq Y] in
/-- Row sums of a product of matrices (the weight `1` case of `weightedRow_mul_le`). -/
theorem rowsum_mul_le [DecidableEq Y] (A B : Matrix Y Y ℂ) {a b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ x, ∑ y, ‖A x y‖ ≤ a) (hB : ∀ x, ∑ y, ‖B x y‖ ≤ b) (x : Y) :
    ∑ y, ‖(A * B) x y‖ ≤ a * b := by
  have := weightedRow_mul_le (fun _ _ : Y => (1 : ℝ)) (fun _ _ => zero_le_one)
    (fun _ _ _ => by norm_num) A B hb (a := a) (b := b) (by simpa using hA) (by simpa using hB) x
  simpa using this

/-- **The trace series of two close matrices.**  If `K₁`, `K₂` have row sums at most `q < 1` and
entries differing by at most `δ`, then
`‖∑ tr(K₁^{n+1})/(n+1) - ∑ tr(K₂^{n+1})/(n+1)‖ ≤ |Y|² δ / (1 - q)`. -/
theorem trace_series_close (K₁ K₂ : Matrix Y Y ℂ) {q δ : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hδ : 0 ≤ δ) (h1 : ∀ x, ∑ y, ‖K₁ x y‖ ≤ q) (h2 : ∀ x, ∑ y, ‖K₂ x y‖ ≤ q)
    (hd : ∀ x y, ‖K₁ x y - K₂ x y‖ ≤ δ) :
    ‖(∑' n : ℕ, (K₁ ^ (n + 1)).trace / ((n : ℂ) + 1)) -
        ∑' n : ℕ, (K₂ ^ (n + 1)).trace / ((n : ℂ) + 1)‖ ≤
      (Fintype.card Y : ℝ) ^ 2 * δ / (1 - q) := by
  set c : ℝ := (Fintype.card Y : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  have hDrow : ∀ x, ∑ y, ‖(K₁ - K₂) x y‖ ≤ c * δ := by
    intro x
    calc ∑ y, ‖(K₁ - K₂) x y‖ ≤ ∑ _y : Y, δ := Finset.sum_le_sum fun y _ => hd x y
      _ = c * δ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hP2 : ∀ m : ℕ, ∀ x, ∑ y, ‖(K₂ ^ m) x y‖ ≤ q ^ m := fun m x => matrix_rowsum_pow_le K₂ h2 m x
  -- bound on the rows of `K₁^m - K₂^m`
  have hE : ∀ m : ℕ, ∀ x, ∑ y, ‖(K₁ ^ (m + 1) - K₂ ^ (m + 1)) x y‖ ≤ (m + 1) * q ^ m * (c * δ) := by
    intro m
    induction m with
    | zero =>
      intro x
      simpa using hDrow x
    | succ m ih =>
      intro x
      have hsplit : K₁ ^ (m + 1 + 1) - K₂ ^ (m + 1 + 1) =
          K₁ * (K₁ ^ (m + 1) - K₂ ^ (m + 1)) + (K₁ - K₂) * K₂ ^ (m + 1) := by
        rw [pow_succ' K₁ (m + 1), pow_succ' K₂ (m + 1), Matrix.mul_sub, Matrix.sub_mul]
        abel
      rw [hsplit]
      have hb1 : 0 ≤ (m + 1 : ℝ) * q ^ m * (c * δ) := by positivity
      have a1 := rowsum_mul_le K₁ (K₁ ^ (m + 1) - K₂ ^ (m + 1)) hb1 h1 ih x
      have a2 := rowsum_mul_le (K₁ - K₂) (K₂ ^ (m + 1)) (pow_nonneg hq0 _) hDrow (hP2 (m + 1)) x
      calc ∑ y, ‖(K₁ * (K₁ ^ (m + 1) - K₂ ^ (m + 1)) + (K₁ - K₂) * K₂ ^ (m + 1)) x y‖
          ≤ ∑ y, (‖(K₁ * (K₁ ^ (m + 1) - K₂ ^ (m + 1))) x y‖ + ‖((K₁ - K₂) * K₂ ^ (m + 1)) x y‖) :=
            Finset.sum_le_sum fun y _ => by simpa using norm_add_le _ _
        _ = _ := Finset.sum_add_distrib
        _ ≤ q * ((m + 1) * q ^ m * (c * δ)) + c * δ * q ^ (m + 1) := add_le_add a1 a2
        _ = ((m + 1 : ℕ) + 1 : ℝ) * q ^ (m + 1) * (c * δ) := by push_cast; ring
  have hterm : ∀ n : ℕ, ‖(K₁ ^ (n + 1)).trace / ((n : ℂ) + 1) -
      (K₂ ^ (n + 1)).trace / ((n : ℂ) + 1)‖ ≤ c ^ 2 * δ * q ^ n := by
    intro n
    have hn : (n + 1 : ℝ) = ‖((n : ℂ) + 1)‖ := by
      have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]; push_cast; ring
    rw [← sub_div, norm_div, ← hn]
    have htr : ‖(K₁ ^ (n + 1)).trace - (K₂ ^ (n + 1)).trace‖ ≤ c * ((n + 1) * q ^ n * (c * δ)) := by
      rw [← Matrix.trace_sub]
      unfold Matrix.trace
      refine (norm_sum_le _ _).trans ?_
      calc ∑ p, ‖(K₁ ^ (n + 1) - K₂ ^ (n + 1)).diag p‖
          ≤ ∑ _p : Y, ((n + 1 : ℝ) * q ^ n * (c * δ)) := by
            refine Finset.sum_le_sum fun p _ => ?_
            refine le_trans ?_ (hE n p)
            exact Finset.single_le_sum (f := fun y => ‖(K₁ ^ (n + 1) - K₂ ^ (n + 1)) p y‖)
              (fun _ _ => norm_nonneg _) (Finset.mem_univ p)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hpos : (0 : ℝ) < n + 1 := by positivity
    rw [div_le_iff₀ hpos]
    calc ‖(K₁ ^ (n + 1)).trace - (K₂ ^ (n + 1)).trace‖ ≤ c * ((n + 1) * q ^ n * (c * δ)) := htr
      _ = c ^ 2 * δ * q ^ n * (n + 1) := by ring
  have hs1 := (det_one_sub_eq_exp_tsum_trace K₁ hq1 h1).1
  have hs2 := (det_one_sub_eq_exp_tsum_trace K₂ hq1 h2).1
  rw [← hs1.tsum_sub hs2]
  have hgeo : HasSum (fun n : ℕ => c ^ 2 * δ * q ^ n) (c ^ 2 * δ * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left _
  refine (tsum_of_norm_bounded hgeo fun n => ?_).trans (le_of_eq ?_)
  · exact hterm n
  · rw [div_eq_mul_inv]

/-- **Two logarithms of close determinants are close** (trace series, no smallness of the
logarithms needed beyond the row sums of `K₁`, `K₂`). -/
theorem logdet_close_abstract {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsPreconnected S)
    {x₀ : X} (hx₀ : x₀ ∈ S) {K₁ K₂ : X → Matrix Y Y ℂ} (hc₁ : Continuous K₁)
    (hc₂ : Continuous K₂) (h₁ : K₁ x₀ = 0) (h₂ : K₂ x₀ = 0) {q δ : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hδ : 0 ≤ δ) (hr₁ : ∀ x ∈ S, ∀ i, ∑ j, ‖K₁ x i j‖ ≤ q)
    (hr₂ : ∀ x ∈ S, ∀ i, ∑ j, ‖K₂ x i j‖ ≤ q)
    (hd : ∀ x ∈ S, ∀ i j, ‖K₁ x i j - K₂ x i j‖ ≤ δ) {ell₁ ell₂ : X → ℂ}
    (hl₁ : ContinuousOn ell₁ S) (hl₂ : ContinuousOn ell₂ S) (e₁ : ell₁ x₀ = 0) (e₂ : ell₂ x₀ = 0)
    (hdet₁ : ∀ x ∈ S, (1 - K₁ x).det = Complex.exp (ell₁ x))
    (hdet₂ : ∀ x ∈ S, (1 - K₂ x).det = Complex.exp (ell₂ x)) :
    ∀ x ∈ S, ‖ell₁ x - ell₂ x‖ ≤ (Fintype.card Y : ℝ) ^ 2 * δ / (1 - q) := by
  intro x hx
  rw [eq_neg_tsum_trace_of_exp_eq hS hx₀ K₁ hc₁ h₁ hq0 hq1 hr₁ hl₁ e₁ hdet₁ x hx,
    eq_neg_tsum_trace_of_exp_eq hS hx₀ K₂ hc₂ h₂ hq0 hq1 hr₂ hl₂ e₂ hdet₂ x hx]
  have := trace_series_close (K₁ x) (K₂ x) hq0 hq1 hδ (hr₁ x hx) (hr₂ x hx) (hd x hx)
  rw [show ∀ A B : ℂ, -A - -B = -(A - B) from fun A B => by ring, norm_neg]
  exact this

/-- **Logarithms of the determinants of two block-supported matrix families that correspond
up to `δ`.**  The matrices `KA z`, `KB z` (`z ∈ S`, `S` preconnected, `z₀ ∈ S`, both `0` at `z₀`)
have rows vanishing outside `Y`, `Y'`, row sums at most `1/2`, and correspond up to `δ` on
`Y × Y` along a bijection `f : Y → Y'`.  If `ell₁`, `ell₂` are continuous logarithms of
`det (1 - KA z)`, `det (1 - KB z)` vanishing at `z₀`, then `‖ell₁ z - ell₂ z‖ ≤ 2 |Y|² δ`. -/
theorem logdet_close_blocks {X X' : Type*} [Fintype X] [DecidableEq X] [Fintype X']
    [DecidableEq X'] {Z : Type*} [TopologicalSpace Z] {S : Set Z} (hS : IsPreconnected S)
    {z₀ : Z} (hz₀ : z₀ ∈ S) (f : X → X') {Y : Finset X} {Y' : Finset X'}
    (hf : Set.BijOn f (Y : Set X) (Y' : Set X')) {KA : Z → Matrix X X ℂ}
    {KB : Z → Matrix X' X' ℂ} (hcA : Continuous KA) (hcB : Continuous KB) (h0A : KA z₀ = 0)
    (h0B : KB z₀ = 0) (hrA : ∀ z ∈ S, ∀ x, x ∉ Y → ∀ y, KA z x y = 0)
    (hrB : ∀ z ∈ S, ∀ x, x ∉ Y' → ∀ y, KB z x y = 0)
    (hsA : ∀ z ∈ S, ∀ x, ∑ y, ‖KA z x y‖ ≤ 1 / 2)
    (hsB : ∀ z ∈ S, ∀ x, ∑ y, ‖KB z x y‖ ≤ 1 / 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdd : ∀ z ∈ S, ∀ x ∈ Y, ∀ y ∈ Y, ‖KA z x y - KB z (f x) (f y)‖ ≤ δ)
    {ell₁ ell₂ : Z → ℂ} (hl₁ : ContinuousOn ell₁ S) (hl₂ : ContinuousOn ell₂ S)
    (e₁ : ell₁ z₀ = 0) (e₂ : ell₂ z₀ = 0)
    (hdet₁ : ∀ z ∈ S, (1 - KA z).det = Complex.exp (ell₁ z))
    (hdet₂ : ∀ z ∈ S, (1 - KB z).det = Complex.exp (ell₂ z)) :
    ∀ z ∈ S, ‖ell₁ z - ell₂ z‖ ≤ 2 * ((Y.card : ℝ) ^ 2 * δ) := by
  classical
  have hbij : Function.Bijective (fun q : Y => (⟨f q, hf.mapsTo q.2⟩ : Y')) := by
    constructor
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (hf.injOn a.2 b.2 this)
    · intro b
      obtain ⟨a, ha, hab⟩ := hf.surjOn b.2
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  set εq : Y ≃ Y' := Equiv.ofBijective _ hbij with hεq
  set K₁ : Z → Matrix Y Y ℂ := fun z =>
    (KA z).submatrix (fun q : Y => (q : X)) (fun q : Y => (q : X)) with hK₁
  set K₂ : Z → Matrix Y Y ℂ := fun z =>
    ((KB z).submatrix (fun q : Y' => (q : X')) (fun q : Y' => (q : X'))).submatrix εq εq
    with hK₂
  have hc₁ : Continuous K₁ := hcA.matrix_submatrix _ _
  have hc₂ : Continuous K₂ := (hcB.matrix_submatrix _ _).matrix_submatrix _ _
  have h₁ : K₁ z₀ = 0 := by rw [hK₁]; simp only [h0A]; ext p q; rfl
  have h₂ : K₂ z₀ = 0 := by rw [hK₂]; simp only [h0B]; ext p q; rfl
  have hr₁ : ∀ z ∈ S, ∀ i, ∑ j, ‖K₁ z i j‖ ≤ 1 / 2 := fun z hz i =>
    le_trans (sum_finset_subtype_le Y (fun y => ‖KA z i y‖) fun y => norm_nonneg _) (hsA z hz i)
  have hr₂ : ∀ z ∈ S, ∀ i, ∑ j, ‖K₂ z i j‖ ≤ 1 / 2 := by
    intro z hz i
    refine le_trans ?_ (hsB z hz (εq i))
    refine le_trans (le_of_eq ?_) (sum_finset_subtype_le Y' (fun y => ‖KB z (εq i) y‖)
      fun y => norm_nonneg _)
    exact Equiv.sum_comp εq (fun j' => ‖KB z (εq i) j'‖)
  have hd12 : ∀ z ∈ S, ∀ i j, ‖K₁ z i j - K₂ z i j‖ ≤ δ := fun z hz i j => hdd z hz i i.2 j j.2
  have hdetA : ∀ z ∈ S, (1 - K₁ z).det = Complex.exp (ell₁ z) := by
    intro z hz
    have e1 : (1 - K₁ z) = (1 - KA z).submatrix (fun q : Y => (q : X)) (fun q : Y => (q : X)) := by
      ext p q
      simp only [hK₁, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.one_apply]
      by_cases h : (p : X) = q
      · have h' : p = q := Subtype.ext h
        simp only [h', ↓reduceIte]
      · have h' : ¬ p = q := fun hh => h (by rw [hh])
        simp only [h, h', ↓reduceIte]
    rw [e1, ← det_eq_det_submatrix_of_rows _ Y (fun x hx y => by
      rw [Matrix.sub_apply, hrA z hz x hx y, sub_zero])]
    exact hdet₁ z hz
  have hdetB : ∀ z ∈ S, (1 - K₂ z).det = Complex.exp (ell₂ z) := by
    intro z hz
    have hinj : ∀ p q : Y, ((εq p : Y') : X') = (εq q : Y') ↔ p = q :=
      fun p q => by rw [← Subtype.ext_iff]; exact εq.injective.eq_iff
    have e1 : (1 - K₂ z) = ((1 - KB z).submatrix (fun q : Y' => (q : X'))
        (fun q : Y' => (q : X'))).submatrix εq εq := by
      ext p q
      simp only [hK₂, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.one_apply]
      by_cases h : p = q
      · have h' : ((εq p : Y') : X') = (εq q : Y') := by rw [h]
        simp only [h, ↓reduceIte]
      · have h' : ¬ ((εq p : Y') : X') = (εq q : Y') := fun hh => h ((hinj p q).1 hh)
        simp only [h, h', ↓reduceIte]
    rw [e1, Matrix.det_submatrix_equiv_self, ← det_eq_det_submatrix_of_rows _ Y' (fun x hx y => by
      rw [Matrix.sub_apply, hrB z hz x hx y, sub_zero])]
    exact hdet₂ z hz
  intro z hz
  have := logdet_close_abstract hS hz₀ hc₁ hc₂ h₁ h₂ (q := 1 / 2) (δ := δ) (by norm_num)
    (by norm_num) hδ hr₁ hr₂ hd12 hl₁ hl₂ e₁ e₂ hdetA hdetB z hz
  rw [Fintype.card_coe] at this
  have h2 : (Y.card : ℝ) ^ 2 * δ / (1 - 1 / 2) = 2 * ((Y.card : ℝ) ^ 2 * δ) := by
    field_simp; ring
  rw [h2] at this
  exact this

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

/-- **Core of the closeness of the tagged parametrix `G_fin` on two tori.**  If the entries of the
tagged `G_*` and of the tagged defect `K` differ by at most `δG`, `δK` on `Y(C)²`, then those of
`G_fin = G_* (1 - K)⁻¹` differ at `x, y ∈ Y(C)` by at most
`|C| (8M+1)^d (4/3) δG + (|C| (8M+1)^d)^3 · 2 e^{H κ} (g + t)⁻¹ (4/3)² δK`, `|C| ≤ nC`.
Shared by the absolute and the distance-weighted versions. -/
theorem final_taggedGfin_close_core (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {nC : ℕ} (hk : 1 ≤ k) (hN : 2 * (J + 6) * M ≤ N) (hN' : 2 * (J + 6) * M ≤ N')
    {f : L1Torus d N → L1Torus d N'} (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hCc : C.card ≤ nC)
    (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1' : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {t : ℝ} (ht : 0 ≤ t)
    {s : MacIdx d N M → ℂ} (hs : s ∈ supportedOn C)
    {s' : MacIdx d N' M → ℂ} (hs' : s' ∈ supportedOn (C.image e))
    (hss : ∀ i ∈ C, s' (e i) = s i) (hsκ : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {x y : L1Torus d N} (hx : x ∈ macRegion d N M C) (hy : y ∈ macRegion d N M C)
    {δG δK : ℝ} (hδG0 : 0 ≤ δG) (hδK0 : 0 ≤ δK)
    (hGG : ∀ p ∈ macRegion d N M C, ∀ q ∈ macRegion d N M C,
      ‖taggedG Finset.univ (macBoxF d N M)
        (fun z u => ((macChi d N M z u : ℝ) : ℂ)) (macTags d N M) (finalOp d L N k v a) t s p q -
      taggedG Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
        (macTags d N' M) (finalOp d L N' k v a) t s' (f p) (f q)‖ ≤ δG)
    (hKK : ∀ p ∈ macRegion d N M C, ∀ q ∈ macRegion d N M C,
      ‖taggedK Finset.univ (macBoxF d N M)
        (fun z u => ((macChi d N M z u : ℝ) : ℂ)) (macTags d N M) (finalOp d L N k v a) t s p q -
      taggedK Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
        (macTags d N' M) (finalOp d L N' k v a) t s' (f p) (f q)‖ ≤ δK) :
    ‖taggedGfin Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
            (macTags d N M) (finalOp d L N k v a) t s x y -
          taggedGfin Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
            (macTags d N' M) (finalOp d L N' k v a) t s' (f x) (f y)‖ ≤
      ((nC : ℝ) * (((8 * M + 1) ^ d : ℕ) : ℝ)) * (δG * (4 / 3)) +
        ((nC : ℝ) * (((8 * M + 1) ^ d : ℕ) : ℝ)) ^ 3 *
          (2 * Real.exp (pdH d * κ) * (finalGap d L + t)⁻¹ * (4 / 3 * (4 / 3 * δK))) := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  set nB : ℝ := (((8 * M + 1) ^ d : ℕ) : ℝ) with hnBdef
  have hnB : 0 ≤ nB := by positivity
  set nY : ℝ := (nC : ℝ) * nB with hnY
  set Hk : ℝ := Real.exp (pdH d * κ) with hHk
  have hgt : 0 < finalGap d L + t := by linarith
  set gT : ℝ := (finalGap d L + t)⁻¹ with hgT
  have hgT0 : 0 < gT := inv_pos.2 hgt
  -- the tag parameter on the second torus
  have hsκ' : ∀ p, ‖s' p‖ ≤ Real.exp κ := by
    intro p
    by_cases hp : p ∈ C.image e
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      rw [hss i hi]; exact hsκ i
    · rw [hs' p hp, norm_zero]; exact (Real.exp_pos _).le
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
  have hGG' : ∀ p ∈ Yset, ∀ q ∈ Yset, ‖taggedG Finset.univ (macBoxF d N M)
      (fun z u => ((macChi d N M z u : ℝ) : ℂ)) (macTags d N M) (finalOp d L N k v a) t s p q -
      taggedG Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
        (macTags d N' M) (finalOp d L N' k v a) t s' (f p) (f q)‖ ≤ δG :=
    fun p hp q hq => hGG p ((hYmem p).1 hp) q ((hYmem q).1 hq)
  have hKK' : ∀ p ∈ Yset, ∀ q ∈ Yset, ‖taggedK Finset.univ (macBoxF d N M)
      (fun z u => ((macChi d N M z u : ℝ) : ℂ)) (macTags d N M) (finalOp d L N k v a) t s p q -
      taggedK Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
        (macTags d N' M) (finalOp d L N' k v a) t s' (f p) (f q)‖ ≤ δK :=
    fun p hp q hq => hKK p ((hYmem p).1 hp) q ((hYmem q).1 hq)
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
    (by norm_num) hGG' hKK' hgG hinv hinv' hu hu' ((hYmem x).2 hx) ((hYmem y).2 hy)
  unfold taggedGfin
  refine hmain.trans ?_
  have hpos : 0 ≤ δG * (4 / 3) := by positivity
  calc (Yset.card : ℝ) * (δG * (4 / 3)) + (Yset.card : ℝ) ^ 3 *
        (2 * Hk * gT * (4 / 3 * (4 / 3 * δK)))
      ≤ nY * (δG * (4 / 3)) + nY ^ 3 * (2 * Hk * gT * (4 / 3 * (4 / 3 * δK))) := by
        gcongr


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
  have hCc' : (C.card : ℝ) * Real.exp (κ * C.card) ≤ cc := by
    rw [hcc]
    apply mul_le_mul (by exact_mod_cast hCc) _ (Real.exp_pos _).le (by positivity)
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by exact_mod_cast hCc) hκ)
  set δG : ℝ := cc * (nB ^ 2 * ε * gT ^ 2) with hδG
  set δK : ℝ := cc * (nB * ε * gT * (2 + P0 * nB ^ 2)) with hδK
  have hδG0 : 0 ≤ δG := by positivity
  have hδK0 : 0 ≤ δK := by positivity
  have hcc0 : 0 ≤ cc := by positivity
  refine (final_taggedGfin_close_core hd hM hκ hMB hMκ hk hN hN' hf he hCc hC hv0 hv1 ha1' ha2 hmass ht hs hs' hss hsκ hx hy
    hδG0 hδK0 (fun p hp q hq => ?_) (fun p hp q hq => ?_)).trans ?_
  · refine (final_taggedGK_close hM hN hN' hf he hC hd hk hv0 hv1 ha1' ha2 hmass hκ hU ht hs hs' hss
      hsκ hp hq).1.trans ?_
    exact mul_le_mul_of_nonneg_right hCc' (by positivity)
  · refine (final_taggedGK_close hM hN hN' hf he hC hd hk hv0 hv1 ha1' ha2 hmass hκ hU ht hs hs' hss
      hsκ hp hq).2.trans ?_
    exact mul_le_mul_of_nonneg_right hCc' (by positivity)
  show nY * (δG * (4 / 3)) + nY ^ 3 * (2 * Hk * gT * (4 / 3 * (4 / 3 * δK))) ≤ a1 * ε * gT
  calc nY * (δG * (4 / 3)) + nY ^ 3 * (2 * Hk * gT * (4 / 3 * (4 / 3 * δK)))
    _ = ε * gT * (nY * (4 / 3) * cc * nB ^ 2 * gT +
          nY ^ 3 * (2 * Hk * (4 / 3 * (4 / 3)) * (cc * (nB * (2 + P0 * nB ^ 2)))) * gT) := by
        rw [hδG, hδK]; ring
    _ ≤ ε * gT * (nY * (4 / 3) * cc * nB ^ 2 * (finalGap d L)⁻¹ +
          nY ^ 3 * (2 * Hk * (4 / 3 * (4 / 3)) * (cc * (nB * (2 + P0 * nB ^ 2)))) *
            (finalGap d L)⁻¹) := by
        gcongr
    _ = a1 * ε * gT := by rw [ha1def]; ring

/-- **Core of the closeness of the Stieltjes family `taggedCfinU` on two tori.**  If the entries
of `G_fin(s, r)` and `G_fin(s', r)` of the two tori differ by at most `Q (g + r)⁻¹` for every
`r > 0`, then those of `taggedCfinU` differ by at most `Q / √g`.  Shared by the absolute and the
distance-weighted versions. -/
theorem taggedCfinU_close_of_Gfin (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (hk : 1 ≤ k) {f : L1Torus d N → L1Torus d N'}
    {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {s : MacIdx d N M → ℂ} {s' : MacIdx d N' M → ℂ}
    (hsκ : ∀ p, ‖s p‖ ≤ Real.exp κ) (hsκ' : ∀ p, ‖s' p‖ ≤ Real.exp κ)
    {x y : L1Torus d N} {Q : ℝ}
    (hres : ∀ r : ℝ, 0 < r →
      ‖taggedGfin Finset.univ (macBoxF d N M) (fun z u => ((macChi d N M z u : ℝ) : ℂ))
          (macTags d N M) (finalOp d L N k v a) r s x y -
        taggedGfin Finset.univ (macBoxF d N' M) (fun z u => ((macChi d N' M z u : ℝ) : ℂ))
          (macTags d N' M) (finalOp d L N' k v a) r s' (f x) (f y)‖ ≤
        Q * (finalGap d L + r)⁻¹) :
    ‖taggedCfinU d N M (finalOp d L N k v a) s x y -
        taggedCfinU d N' M (finalOp d L N' k v a) s' (f x) (f y)‖ ≤
      Q / Real.sqrt (finalGap d L) := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hint1 := taggedCfin_integrable (L := L) (N₀ := N) (k := k) (M := M) hd hk hv0 hv1 ha1 ha2
    hmass hM hκ hMB hMκ hsκ x y
  have hint2 := taggedCfin_integrable (L := L) (N₀ := N') (k := k) (M := M) hd hk hv0 hv1 ha1 ha2
    hmass hM hκ hMB hMκ hsκ' (f x) (f y)
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  rw [taggedCfinU_apply, taggedCfinU_apply, ← mul_sub, ← integral_sub hint1 hint2]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hint : Integrable (fun r : ℝ => Q * (r ^ (-(1 / 2 : ℝ)) * (finalGap d L + r)⁻¹)) μ :=
    (Localization.integrableOn_rpow_inv_add hg).const_mul Q
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
      have hres := hres r hr0
      rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg h3.le]
      calc r ^ (-(1 / 2 : ℝ)) * ‖_‖ ≤ r ^ (-(1 / 2 : ℝ)) * (Q * (finalGap d L + r)⁻¹) :=
            mul_le_mul_of_nonneg_left hres h3.le
        _ = _ := by ring))
  rw [integral_const_mul, Localization.integral_rpow_inv_add hg] at hbound
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : 0 < Real.sqrt (finalGap d L) := Real.sqrt_pos.2 hg
  calc 1 / Real.pi * ‖_‖ ≤ 1 / Real.pi * (Q * (Real.pi / Real.sqrt (finalGap d L))) := by
        gcongr
    _ = _ := by field_simp


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
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hU x hx y hy)
  have hsκ' : ∀ p, ‖s' p‖ ≤ Real.exp κ := by
    intro p
    by_cases hp : p ∈ C.image e
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      rw [hss i hi]; exact hsκ i
    · rw [hs' p hp, norm_zero]; exact (Real.exp_pos _).le
  exact taggedCfinU_close_of_Gfin hd hM hκ hMB hMκ hk hv0 hv1 ha1 ha2 hmass hsκ hsκ'
    (fun r hr => hP hk hN hN' hf he hCc hC hv0 hv1 ha1 ha2 hmass hU hr.le hs hs' hss
      hsκ hx hy)

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

/-- **The entries of the final operators of two tori on the window `Y(C)`, from the closeness of
the entries on a cube**: if the entries of `finalOp` at the sites of a cube of the two tori differ
by at most `C exp(-c (Rm - Rc))` (`hmain`), then on the window they differ by at most
`C exp(3c/2) exp(-c (min N N' / 2 - (J + 3) M))`. -/
theorem final_region_entry_close_of_entries {C c : ℝ} (hC : 0 < C) (hc : 0 < c) {v a : ℝ}
    (hmain : ∀ {m m' : ℕ} [NeZero m] [NeZero m'] {Rm Rc : ℕ}, 2 * Rm + 1 < m → 2 * Rm + 1 < m' →
      Rc + 1 ≤ Rm → ∀ {y y' : Fin d → ℤ}, y ∈ sqBox d Rc → y' ∈ sqBox d Rc →
      ‖finalOp d L m k v a (castL1 m y) (castL1 m y') -
          finalOp d L m' k v a (castL1 m' y) (castL1 m' y')‖ ≤
        C * Real.exp (-c * ((Rm : ℝ) - Rc))) :
    ∀ {M J N N' : ℕ} [NeZero N] [NeZero N'], 0 < M → 2 * (J + 6) * M ≤ N →
      2 * (J + 6) * M ≤ N' → ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {C' : Finset (MacIdx d N M)}, (∀ z ∈ C', ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ x ∈ macRegion d N M C', ∀ y ∈ macRegion d N M C',
      ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤
        (C * Real.exp (3 / 2 * c)) *
          Real.exp (-c * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ))) := by
  intro M J N N' _ _ hM hN hN' f hf C' hC' x hx y hy
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
  have h := hmain (m := N) (m' := N') (Rm := (S - 2) / 2) (Rc := W)
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
  exact final_region_entry_close_of_entries (L := L) (k := k) hC hc (hmain hv0 hv1 ha1 ha2) hM hN hN'
    hf hC' x hx y hy

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

/-- The `E`-part of the perturbed defect: closeness of `E χ_z G_z` for the final operators on two
tori, `E`, `E'` close up to `εE` on `Y(C)²` and `‖E'‖ ≤ η` entrywise. -/
theorem final_boxE_close (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {ε εE η : ℝ} (hη : 0 ≤ η)
    (hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε)
    {E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {E' : Matrix (L1Torus d N') (L1Torus d N') ℂ}
    (hEc : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, ‖E x y - E' (f x) (f y)‖ ≤ εE)
    (hEb : ∀ x y, ‖E' x y‖ ≤ η)
    {t : ℝ} (ht : 0 ≤ t) {z : MacIdx d N M} (hzC : z ∈ C) {x y : L1Torus d N}
    (hx : x ∈ macRegion d N M C) (hy : y ∈ macRegion d N M C) :
    ‖(E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N k v a) (macBoxF d N M z) t)) x y -
        (E' * (Matrix.diagonal (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) *
          boxG (finalOp d L N' k v a) (macBoxF d N' M (e z)) t)) (f x) (f y)‖ ≤
      (((8 * M + 1) ^ d : ℕ) : ℝ) * (εE * (2 * (finalGap d L + t)⁻¹) +
        η * ((((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2)) := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hgt : 0 < finalGap d L + t := by linarith
  have hT0 : 0 < (finalGap d L + t)⁻¹ := inv_pos.2 hgt
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hU x hx y hy)
  have hεE0 : 0 ≤ εE := (norm_nonneg _).trans (hEc x hx y hy)
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
  have hrow := rowmul_close f hBY hinjY (U := finalOp d L N k v a) (U' := finalOp d L N' k v a)
    t hc hc' hcY hc1 (A := E) (A' := E') (εA := εE) (aA := η)
    (bG := 2 * (finalGap d L + t)⁻¹) (δG := nB ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2)
    hεE0 hη (by positivity) (by positivity)
    (fun p hp q hq => hEc p ((hYmem p).1 hp) q ((hYmem q).1 hq)) (fun p _ q _ => hEb _ _)
    (fun u _ w => hbG u w) hGc ((hYmem x).2 hx) ((hYmem y).2 hy)
  refine hrow.trans ?_
  exact mul_le_mul_of_nonneg_right hBcard (by positivity) |>.trans (le_of_eq rfl)

/-- **Closeness of the tagged perturbed defect `K_E` of the final operators on two tori.** -/
theorem final_taggedKE_close (hM : 0 < M) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    (hd : 0 < d) (hk : 1 ≤ k) {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {ε εE η κ : ℝ} (hκ : 0 ≤ κ) (hη : 0 ≤ η)
    (hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε)
    {E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {E' : Matrix (L1Torus d N') (L1Torus d N') ℂ}
    (hEc : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, ‖E x y - E' (f x) (f y)‖ ≤ εE)
    (hEb : ∀ x y, ‖E' x y‖ ≤ η)
    {t : ℝ} (ht : 0 ≤ t)
    {s : MacIdx d N M → ℂ} (hs : s ∈ supportedOn C)
    {s' : MacIdx d N' M → ℂ} (hs' : s' ∈ supportedOn (C.image e))
    (hss : ∀ i ∈ C, s' (e i) = s i) (hsκ : ∀ p, ‖s p‖ ≤ Real.exp κ)
    {x y : L1Torus d N} (hx : x ∈ macRegion d N M C) (hy : y ∈ macRegion d N M C) :
    ‖taggedMat Finset.univ (macTags d N M)
        (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
            (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
          E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N k v a) (macBoxF d N M z) t)) s x y -
      taggedMat Finset.univ (macTags d N' M)
        (fun z => boxR (finalOp d L N' k v a) (macBoxF d N' M z)
            (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
          E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N' k v a) (macBoxF d N' M z) t)) s' (f x) (f y)‖ ≤
      (C.card : ℝ) * Real.exp (κ * C.card) *
        ((((8 * M + 1) ^ d : ℕ) : ℝ) * ε * (finalGap d L + t)⁻¹ *
            (2 + (finalDecayC d L / finalGap d L + 1) * (((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2) +
          (((8 * M + 1) ^ d : ℕ) : ℝ) * (εE * (2 * (finalGap d L + t)⁻¹) +
            η * ((((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2))) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hA0 := finalDecayC_pos (L := L) hd
  have hgt : 0 < finalGap d L + t := by linarith
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hU x hx y hy)
  have hεE0 : 0 ≤ εE := (norm_nonneg _).trans (hEc x hx y hy)
  have hpos : 0 ≤ (((8 * M + 1) ^ d : ℕ) : ℝ) * ε * (finalGap d L + t)⁻¹ *
            (2 + (finalDecayC d L / finalGap d L + 1) * (((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2) +
          (((8 * M + 1) ^ d : ℕ) : ℝ) * (εE * (2 * (finalGap d L + t)⁻¹) +
            η * ((((8 * M + 1) ^ d : ℕ) : ℝ) ^ 2 * ε * (finalGap d L + t)⁻¹ ^ 2)) := by
    positivity
  refine taggedMat_close_twoTorus hM hN hN' hf he hC hκ hpos
    (fun z hzC u hu w hw => ?_) hs hs' hss hsκ hx hy
  have h1 := (final_boxFamily_close hM hN hN' hf he hC hd hk hv0 hv1 ha1 ha2 hmass hU ht hzC hu hw).2
  have h2 := final_boxE_close hM hN hN' hf he hC hd hk hv0 hv1 ha1 ha2 hmass hη hU hEc hEb ht hzC hu hw
  have : (boxR (finalOp d L N k v a) (macBoxF d N M z) (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
        E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N k v a) (macBoxF d N M z) t)) u w -
      (boxR (finalOp d L N' k v a) (macBoxF d N' M (e z))
          (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) t -
        E' * (Matrix.diagonal (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) *
          boxG (finalOp d L N' k v a) (macBoxF d N' M (e z)) t)) (f u) (f w) =
      (boxR (finalOp d L N k v a) (macBoxF d N M z) (fun u => ((macChi d N M z u : ℝ) : ℂ)) t u w -
        boxR (finalOp d L N' k v a) (macBoxF d N' M (e z))
          (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) t (f u) (f w)) -
      ((E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N k v a) (macBoxF d N M z) t)) u w -
        (E' * (Matrix.diagonal (fun u => ((macChi d N' M (e z) u : ℝ) : ℂ)) *
          boxG (finalOp d L N' k v a) (macBoxF d N' M (e z)) t)) (f u) (f w)) := by
    simp only [Matrix.sub_apply]; ring
  rw [this]
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

end FinalBoxes

section Coef

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- Linearity of the coefficient on functions analytic on a polydisc of radius `R > 1`. -/
theorem coef_sub_open {R : ℝ} (hR : 1 < R) {f g : (ι → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R)))
    (hg : AnalyticOnNhd ℂ g (polydisc (0 : ι → ℂ) (fun _ => R))) (C : Finset ι) :
    coef (fun s => f s - g s) C = coef f C - coef g C := by
  have hfg : AnalyticOnNhd ℂ (fun s => f s - g s) (polydisc (0 : ι → ℂ) (fun _ => R)) :=
    hf.sub hg
  refine Balaban.Polymer.TwoTorusStep.eq_of_sum_powerset_eq_of_subset
    (g := coef (fun s => f s - g s)) (h := fun B => coef f B - coef g B) (C := C) ?_ C
    Finset.Subset.rfl
  intro A _
  rw [← sum_coef_unit hR hfg A, Finset.sum_sub_distrib, ← sum_coef_unit hR hf A,
    ← sum_coef_unit hR hg A]

/-- **Cauchy estimate for the difference of two coefficients under a relabelling.**  Let
`f`, `f'` be analytic on the polydisc of radius `R > 1`, `e` injective on `C`.  If
`‖f s - f' s'‖ ≤ B` whenever `s` is supported on `C` with `|s_i| < R` and `s'` is supported on
`e C` with `s' (e i) = s i`, then `‖coef f C - coef f' (e C)‖ ≤ B / (R - 1)^{|C|}`. -/
theorem norm_coef_sub_relabel_le {R : ℝ} (hR : 1 < R) (e : ι → ι') {C : Finset ι}
    (he : Set.InjOn e (C : Set ι)) {f : (ι → ℂ) → ℂ} {f' : (ι' → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R)))
    (hf' : AnalyticOnNhd ℂ f' (polydisc (0 : ι' → ℂ) (fun _ => R))) {B : ℝ}
    (hB : ∀ s ∈ supN C R, ∀ s' ∈ supportedOn (C.image e), (∀ i ∈ C, s' (e i) = s i) →
      ‖f s - f' s'‖ ≤ B) :
    ‖coef f C - coef f' (C.image e)‖ ≤ B / (R - 1) ^ C.card := by
  classical
  have hR0 : 0 < R := by linarith
  set pb : (ι' → ℂ) → (ι → ℂ) := fun w i => if i ∈ C then w (e i) else 0 with hpb
  set g : (ι' → ℂ) → ℂ := fun w => f (pb w) with hg
  have hpbA : ∀ w, AnalyticAt ℂ pb w := by
    intro w
    rw [analyticAt_pi_iff]
    intro i
    by_cases hi : i ∈ C
    · have : (fun w : ι' → ℂ => pb w i) = fun w => w (e i) := by
        funext w; simp [hpb, hi]
      rw [this]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι' => ℂ) (e i)).analyticAt w
    · have : (fun w : ι' → ℂ => pb w i) = fun _ => 0 := by
        funext w; simp [hpb, hi]
      rw [this]
      exact analyticAt_const
  have hpbP : ∀ w ∈ polydisc (0 : ι' → ℂ) (fun _ => R),
      pb w ∈ polydisc (0 : ι → ℂ) (fun _ => R) := by
    intro w hw i
    by_cases hi : i ∈ C
    · simpa [hpb, hi] using hw (e i)
    · simpa [hpb, hi] using hR0
  have hgA : AnalyticOnNhd ℂ g (polydisc (0 : ι' → ℂ) (fun _ => R)) := fun w hw =>
    (hf (pb w) (hpbP w hw)).comp (hpbA w)
  have h1 : coef g (C.image e) = coef f C := by
    refine Balaban.Polymer.TwoTorusStep.coef_relabel_injOn hR e he hf ?_
    intro s hs s' hs' hss
    have : pb s' = s := by
      funext i
      by_cases hi : i ∈ C
      · simp [hpb, hi, hss i hi]
      · simp [hpb, hi, hs.1 i hi]
    simp only [hg, this]
  have hdiff : AnalyticOnNhd ℂ (fun s' => g s' - f' s')
      (polydisc (0 : ι' → ℂ) (fun _ => R)) := hgA.sub hf'
  have h2 : coef f C - coef f' (C.image e) = coef (fun s' => g s' - f' s') (C.image e) := by
    rw [coef_sub_open hR hgA hf', h1]
  rw [h2]
  have hproj := analyticOnNhd_comp_proj hdiff (C.image e) hR0
  have h3 : coef (fun s' => g s' - f' s') (C.image e) =
      coef (fun s' : ι' → ℂ => (fun s'' => g s'' - f' s'') (fun i => if i ∈ C.image e then s' i
        else 0)) (C.image e) :=
    coef_congr fun w hw => by
      have hw' : (fun i => if i ∈ C.image e then w i else 0) = w := by
        funext i
        by_cases hi : i ∈ C.image e
        · simp only [hi, ↓reduceIte]
        · simp only [hi, ↓reduceIte, hw i hi]
      rw [hw']
  rw [h3]
  have hcard : (C.image e).card = C.card := Finset.card_image_of_injOn he
  rw [← hcard]
  refine norm_coef_le hR hproj (B := B) (fun s' hs' => ?_) (C.image e)
  set u : ι' → ℂ := fun i => if i ∈ C.image e then s' i else 0 with hu
  have hus : u ∈ supportedOn (C.image e) := fun i hi => by
    show (if i ∈ C.image e then s' i else 0) = 0
    simp only [hi, ↓reduceIte]
  have hsN : pb u ∈ supN C R := by
    refine ⟨fun i hi => by simp [hpb, hi], fun i => ?_⟩
    by_cases hi : i ∈ C
    · have hmem : e i ∈ C.image e := Finset.mem_image_of_mem e hi
      have : pb u i = s' (e i) := by
        show (if i ∈ C then u (e i) else 0) = s' (e i)
        simp only [hi, ↓reduceIte]
        show (if e i ∈ C.image e then s' (e i) else 0) = s' (e i)
        simp only [hmem, ↓reduceIte]
      rw [this]
      simpa using hs' (e i)
    · simpa [hpb, hi] using hR0
  have := hB (pb u) hsN u hus (fun i hi => by simp [hpb, hi])
  simpa [hg] using this

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] in
/-- The transport of cut parameters along a map injective on `C`. -/
theorem exists_relabel_map (e : ι → ι') {C : Finset ι} (he : Set.InjOn e (C : Set ι)) :
    ∃ τ : (ι → ℂ) → (ι' → ℂ), Continuous τ ∧ τ 0 = 0 ∧ (∀ u, ∀ i ∈ C, τ u (e i) = u i) ∧
      (∀ u, τ u ∈ supportedOn (C.image e)) ∧
      (∀ u : ι → ℂ, ∀ R : ℝ, 0 ≤ R → (∀ i, ‖u i‖ ≤ R) → ∀ j, ‖τ u j‖ ≤ R) := by
  classical
  set τ : (ι → ℂ) → (ι' → ℂ) := fun u j => ∑ i ∈ C.filter (fun i => e i = j), u i with hτ
  have hτe : ∀ u, ∀ i ∈ C, τ u (e i) = u i := by
    intro u i hi
    have : C.filter (fun i' => e i' = e i) = {i} := by
      ext i'
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hi', h⟩
        exact he hi' hi h
      · rintro rfl
        exact ⟨hi, rfl⟩
    simp [hτ, this]
  have hτsupp : ∀ u, τ u ∈ supportedOn (C.image e) := by
    intro u j hj
    have : C.filter (fun i => e i = j) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hi h
      exact hj (Finset.mem_image.2 ⟨i, hi, h⟩)
    simp [hτ, this]
  refine ⟨τ, continuous_pi fun j => continuous_finsetSum _ fun i _ => continuous_apply i, ?_,
    hτe, hτsupp, ?_⟩
  · funext j; simp [hτ]
  · intro u R hR hu j
    by_cases hj : j ∈ C.image e
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
      rw [hτe u i hi]; exact hu i
    · rw [hτsupp u j hj, norm_zero]; exact hR

end Coef

section Interaction

variable {d M J N N' L : ℕ} [NeZero N] [NeZero N'] [NeZero L]

/-- **Approximate `integral_cutoff_twoTorus`.**  The cutoff integrals on the two tori differ by at
most `Lip · |Y(C)| δ ρ · γ(box ρ)` when the entries of the Stieltjes families correspond up to `δ`
on `Y(C)²` (and both have row sums at most `Bc`), the functionals `F`, `F'` correspond up to the
Lipschitz bound `hFclose` on fields vanishing off `Y(C)`, `Y(e C)` and bounded by `Bc ρ`, and the
reference measures correspond exactly (`hγ`, as in `integral_cutoff_twoTorus`). -/
theorem integral_cutoff_close (hM : 0 < M) (hd : 0 < d) (hN : 2 * (J + 6) * M ≤ N)
    (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    {U : Matrix (L1Torus d N) (L1Torus d N) ℂ} {U' : Matrix (L1Torus d N') (L1Torus d N') ℂ}
    {s : MacIdx d N M → ℂ} (hs : s ∈ supportedOn C)
    {s' : MacIdx d N' M → ℂ} (hs' : s' ∈ supportedOn (C.image e))
    {δ Bc ρ BF Lip nY : ℝ} (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (hnY : (Nat.card ↥(macRegion d N M C) : ℝ) ≤ nY)
    (hCC : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖taggedCfinU d N M U s x y - taggedCfinU d N' M U' s' (f x) (f y)‖ ≤ δ)
    (hrow : ∀ x, ∑ y, ‖taggedCfinU d N M U s x y‖ ≤ Bc)
    (hrow' : ∀ x', ∑ y, ‖taggedCfinU d N' M U' s' x' y‖ ≤ Bc)
    {γ : Measure (L1Torus d N → ℝ)} {γ' : Measure (L1Torus d N' → ℝ)}
    (hγfin : γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    {F : (L1Torus d N → ℂ) → ℂ} {F' : (L1Torus d N' → ℂ) → ℂ}
    (hFm : Measurable F) (hFm' : Measurable F')
    (hFB : ∀ w : L1Torus d N → ℂ, (∀ x, ‖w x‖ ≤ Bc * ρ) → ‖F w‖ ≤ BF)
    (hFB' : ∀ w : L1Torus d N' → ℂ, (∀ x, ‖w x‖ ≤ Bc * ρ) → ‖F' w‖ ≤ BF)
    (hFclose : ∀ (w : L1Torus d N → ℂ) (w' : L1Torus d N' → ℂ),
      (∀ x, x ∉ macRegion d N M C → w x = 0) →
      (∀ x', x' ∉ macRegion d N' M (C.image e) → w' x' = 0) →
      (∀ x, ‖w x‖ ≤ Bc * ρ) → (∀ x', ‖w' x'‖ ≤ Bc * ρ) → ∀ η : ℝ, 0 ≤ η →
      (∀ x ∈ macRegion d N M C, ‖w' (f x) - w x‖ ≤ η) → ‖F' w' - F w‖ ≤ Lip * η)
    (hγ : Measure.map (fun (ψ : L1Torus d N → ℝ) (q : ↥(macRegion d N M C)) => ψ q)
        (γ.restrict {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}) =
      Measure.map (fun (ψ' : L1Torus d N' → ℝ) (q : ↥(macRegion d N M C)) => ψ' (f q))
        (γ'.restrict {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ})) :
    ‖(∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
      F (fun x => ∑ y, taggedCfinU d N M U s x y * ((ψ y : ℝ) : ℂ)) ∂γ) -
    ∫ ψ' in {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ},
      F' (fun x => ∑ y, taggedCfinU d N' M U' s' x y * ((ψ' y : ℝ) : ℂ)) ∂γ'‖ ≤
      Lip * (nY * δ * ρ) * (γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : L1Torus d N' → L1Torus d N, ∀ y μ, g y μ = (((y μ).val : ℕ) : ZMod N) :=
    ⟨fun y μ => (((y μ).val : ℕ) : ZMod N), fun _ _ => rfl⟩
  have hbij := macRegion_bijOn hM hN hN' hf hg he hC
  set Yreg : Set (L1Torus d N) := macRegion d N M C with hYreg
  set Y'reg : Set (L1Torus d N') := macRegion d N' M (C.image e) with hY'reg
  set Cs := taggedCfinU d N M U s with hCs
  set Cs' := taggedCfinU d N' M U' s' with hCs'
  have hCs0 : ∀ x y, ¬ (x ∈ Yreg ∧ y ∈ Yreg) → Cs x y = 0 := fun x y h =>
    taggedCfinU_eq_zero_of_not_mem hM hd U hs h
  have hCs0' : ∀ x y, ¬ (x ∈ Y'reg ∧ y ∈ Y'reg) → Cs' x y = 0 := fun x y h =>
    taggedCfinU_eq_zero_of_not_mem hM hd U' hs' h
  set Gs : (↥Yreg → ℝ) → ℂ := fun φ => F (fun x => ∑ q : ↥Yreg, Cs x q * ((φ q : ℝ) : ℂ)) with hGs
  set Gs' : (↥Yreg → ℝ) → ℂ :=
    fun φ => F' (fun x' => ∑ q : ↥Yreg, Cs' x' (f q) * ((φ q : ℝ) : ℂ)) with hGs'
  have hsum : ∀ (ψ : L1Torus d N → ℝ) (x : L1Torus d N),
      ∑ y, Cs x y * ((ψ y : ℝ) : ℂ) = ∑ q : ↥Yreg, Cs x q * ((ψ q : ℝ) : ℂ) := by
    intro ψ x
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun y => y ∈ Yreg))
      (fun y _ hy => by
        have : y ∉ Yreg := by simpa using hy
        rw [hCs0 x y (fun h => this h.2), zero_mul])]
    exact Finset.sum_subtype _ (fun y => by simp) (fun y => Cs x y * ((ψ y : ℝ) : ℂ))
  have hsum' : ∀ (ψ' : L1Torus d N' → ℝ) (x' : L1Torus d N'),
      ∑ y, Cs' x' y * ((ψ' y : ℝ) : ℂ) = ∑ q : ↥Yreg, Cs' x' (f q) * ((ψ' (f q) : ℝ) : ℂ) := by
    intro ψ' x'
    have himg : Finset.univ.filter (fun y => y ∈ Y'reg) =
        (Finset.univ.filter fun y => y ∈ Yreg).image f := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hy
        obtain ⟨a, ha, hay⟩ := hbij.surjOn hy
        exact ⟨a, ha, hay⟩
      · rintro ⟨a, ha, rfl⟩
        exact hbij.mapsTo ha
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun y => y ∈ Y'reg))
      (fun y _ hy => by
        have : y ∉ Y'reg := by simpa using hy
        rw [hCs0' x' y (fun h => this h.2), zero_mul]), himg,
      Finset.sum_image (fun a ha b hb hab => hbij.injOn (by simpa using ha) (by simpa using hb) hab)]
    exact Finset.sum_subtype _ (fun y => by simp) (fun y => Cs' x' (f y) * ((ψ' (f y) : ℝ) : ℂ))
  have hr : Measurable (fun (ψ : L1Torus d N → ℝ) (q : ↥Yreg) => ψ q) :=
    Measurable.of_eval fun q => measurable_pi_apply _
  have hr' : Measurable (fun (ψ' : L1Torus d N' → ℝ) (q : ↥Yreg) => ψ' (f q)) :=
    Measurable.of_eval fun q => measurable_pi_apply _
  have hGsm : Measurable Gs := by
    refine hFm.comp (Measurable.of_eval fun x => ?_)
    exact Finset.measurable_sum _ fun q _ =>
      measurable_const.mul (Complex.measurable_ofReal.comp (measurable_pi_apply q))
  have hGsm' : Measurable Gs' := by
    refine hFm'.comp (Measurable.of_eval fun x => ?_)
    exact Finset.measurable_sum _ fun q _ =>
      measurable_const.mul (Complex.measurable_ofReal.comp (measurable_pi_apply q))
  have e1 : (∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
      F (fun x => ∑ y, Cs x y * ((ψ y : ℝ) : ℂ)) ∂γ) =
      ∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}, Gs (fun q => ψ q) ∂γ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ψ => ?_)
    simp only [hGs, hsum]
  have e2 : (∫ ψ' in {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ},
      F' (fun x => ∑ y, Cs' x y * ((ψ' y : ℝ) : ℂ)) ∂γ') =
      ∫ ψ' in {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ}, Gs' (fun q => ψ' (f q)) ∂γ' := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ψ' => ?_)
    simp only [hGs', hsum']
  set box : Set (L1Torus d N → ℝ) := {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ} with hbox
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (↥Yreg → ℝ), μ = Measure.map
      (fun (ψ : L1Torus d N → ℝ) (q : ↥Yreg) => ψ q) (γ.restrict box) := ⟨_, rfl⟩
  have hboxm : MeasurableSet box := by
    have : box = Set.pi Set.univ (fun _ : L1Torus d N => Icc (-ρ) ρ) := by
      ext ψ; simp only [hbox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_Icc, abs_le]
    rw [this]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hfin : IsFiniteMeasure (γ.restrict box) := ⟨by rw [Measure.restrict_apply_univ]; exact hγfin⟩
  have hμfin : IsFiniteMeasure μ := by
    rw [hμ]; infer_instance
  have i1 : (∫ ψ in box, Gs (fun q => ψ q) ∂γ) = ∫ φ, Gs φ ∂μ := by
    rw [hμ]
    exact (integral_map hr.aemeasurable hGsm.aestronglyMeasurable).symm
  have i2 : (∫ ψ' in {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ}, Gs' (fun q => ψ' (f q)) ∂γ') =
      ∫ φ, Gs' φ ∂μ := by
    rw [hμ, hγ]
    exact (integral_map hr'.aemeasurable hGsm'.aestronglyMeasurable).symm
  -- a.e. the field lies in the box
  have hae : ∀ᵐ φ ∂μ, ∀ q, |φ q| ≤ ρ := by
    have hmeas : MeasurableSet {φ : ↥Yreg → ℝ | ∀ q, |φ q| ≤ ρ} := by
      have : {φ : ↥Yreg → ℝ | ∀ q, |φ q| ≤ ρ} =
          Set.pi Set.univ (fun _ : ↥Yreg => Icc (-ρ) ρ) := by
        ext φ; simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
          Set.mem_Icc, abs_le]
      rw [this]
      exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
    rw [hμ, ae_map_iff hr.aemeasurable hmeas]
    exact (ae_restrict_iff' hboxm).2 (Filter.Eventually.of_forall fun ψ hψ q => hψ q)
  -- the fields
  set wf : (↥Yreg → ℝ) → L1Torus d N → ℂ := fun φ x => ∑ q : ↥Yreg, Cs x q * ((φ q : ℝ) : ℂ)
    with hwf
  set wf' : (↥Yreg → ℝ) → L1Torus d N' → ℂ := fun φ x' =>
    ∑ q : ↥Yreg, Cs' x' (f q) * ((φ q : ℝ) : ℂ) with hwf'
  have hYsub : ∀ (x : L1Torus d N) (h : L1Torus d N → ℝ), (∀ y, 0 ≤ h y) →
      ∑ q : ↥Yreg, h q ≤ ∑ y, h y := by
    intro x h h0
    rw [← Finset.sum_subtype (Finset.univ.filter fun y => y ∈ Yreg) (fun y => by simp) h]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun y _ _ => h0 y)
  have hbd : ∀ φ : ↥Yreg → ℝ, (∀ q, |φ q| ≤ ρ) → ∀ x, ‖wf φ x‖ ≤ Bc * ρ := by
    intro φ hφ x
    calc ‖wf φ x‖ ≤ ∑ q : ↥Yreg, ‖Cs x q * ((φ q : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ q : ↥Yreg, ‖Cs x q‖ * ρ := by
          refine Finset.sum_le_sum fun q _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hφ q) (norm_nonneg _)
      _ = (∑ q : ↥Yreg, ‖Cs x q‖) * ρ := by rw [Finset.sum_mul]
      _ ≤ (∑ y, ‖Cs x y‖) * ρ :=
          mul_le_mul_of_nonneg_right (hYsub x (fun y => ‖Cs x y‖) fun y => norm_nonneg _) hρ
      _ ≤ Bc * ρ := mul_le_mul_of_nonneg_right (hrow x) hρ
  have hbd' : ∀ φ : ↥Yreg → ℝ, (∀ q, |φ q| ≤ ρ) → ∀ x', ‖wf' φ x'‖ ≤ Bc * ρ := by
    intro φ hφ x'
    calc ‖wf' φ x'‖ ≤ ∑ q : ↥Yreg, ‖Cs' x' (f q) * ((φ q : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ q : ↥Yreg, ‖Cs' x' (f q)‖ * ρ := by
          refine Finset.sum_le_sum fun q _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hφ q) (norm_nonneg _)
      _ = (∑ q : ↥Yreg, ‖Cs' x' (f q)‖) * ρ := by rw [Finset.sum_mul]
      _ ≤ (∑ y, ‖Cs' x' y‖) * ρ := by
          refine mul_le_mul_of_nonneg_right ?_ hρ
          have himg : ∑ q : ↥Yreg, ‖Cs' x' (f q)‖ =
              ∑ y ∈ (Finset.univ.filter fun y => y ∈ Yreg).image f, ‖Cs' x' y‖ := by
            rw [Finset.sum_image (fun a ha b hb hab =>
              hbij.injOn (by simpa using ha) (by simpa using hb) hab)]
            exact (Finset.sum_subtype (Finset.univ.filter fun y => y ∈ Yreg)
              (p := fun y => y ∈ Yreg) (fun y => by simp) (fun y => ‖Cs' x' (f y)‖)).symm
          rw [himg]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun y _ _ => norm_nonneg _)
      _ ≤ Bc * ρ := mul_le_mul_of_nonneg_right (hrow' x') hρ
  have hint1 : Integrable Gs μ := by
    refine Integrable.of_bound hGsm.aestronglyMeasurable BF ?_
    filter_upwards [hae] with φ hφ using hFB _ (hbd φ hφ)
  have hint2 : Integrable Gs' μ := by
    refine Integrable.of_bound hGsm'.aestronglyMeasurable BF ?_
    filter_upwards [hae] with φ hφ using hFB' _ (hbd' φ hφ)
  have hcard : (Fintype.card ↥Yreg : ℝ) ≤ nY := by
    rw [← Nat.card_eq_fintype_card]; exact hnY
  have hpt : ∀ᵐ φ ∂μ, ‖Gs φ - Gs' φ‖ ≤ Lip * (nY * δ * ρ) := by
    filter_upwards [hae] with φ hφ
    rw [norm_sub_rev]
    have hw0 : ∀ x, x ∉ Yreg → wf φ x = 0 := fun x hx => by
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [hCs0 x q (fun h => hx h.1), zero_mul]
    have hw0' : ∀ x', x' ∉ Y'reg → wf' φ x' = 0 := fun x' hx' => by
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [hCs0' x' (f q) (fun h => hx' h.1), zero_mul]
    have hη : ∀ x ∈ Yreg, ‖wf' φ (f x) - wf φ x‖ ≤ nY * δ * ρ := by
      intro x hx
      have : wf' φ (f x) - wf φ x = ∑ q : ↥Yreg,
          (Cs' (f x) (f q) - Cs x q) * ((φ q : ℝ) : ℂ) := by
        simp only [hwf, hwf', ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun q _ => by ring
      rw [this]
      calc ‖∑ q : ↥Yreg, (Cs' (f x) (f q) - Cs x q) * ((φ q : ℝ) : ℂ)‖
          ≤ ∑ q : ↥Yreg, ‖(Cs' (f x) (f q) - Cs x q) * ((φ q : ℝ) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ _q : ↥Yreg, δ * ρ := by
            refine Finset.sum_le_sum fun q _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev]
            exact mul_le_mul (hCC x hx q q.2) (hφ q) (abs_nonneg _) hδ
        _ = (Fintype.card ↥Yreg : ℝ) * (δ * ρ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ nY * (δ * ρ) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = nY * δ * ρ := by ring
    have := hFclose (wf φ) (wf' φ) hw0 hw0' (hbd φ hφ) (hbd' φ hφ) (nY * δ * ρ)
      (by
        have : (0 : ℝ) ≤ Fintype.card ↥Yreg := by positivity
        have h0 : 0 ≤ nY := this.trans hcard
        positivity) hη
    exact this
  have hdiff : ‖(∫ ψ in box, F (fun x => ∑ y, Cs x y * ((ψ y : ℝ) : ℂ)) ∂γ) -
      ∫ ψ' in {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ},
        F' (fun x => ∑ y, Cs' x y * ((ψ' y : ℝ) : ℂ)) ∂γ'‖ ≤
      Lip * (nY * δ * ρ) * μ.real Set.univ := by
    rw [e1, e2, i1, i2, ← integral_sub hint1 hint2]
    exact norm_integral_le_of_norm_le_const hpt
  refine hdiff.trans ?_
  have hmu : μ.real Set.univ = (γ box).toReal := by
    rw [hμ, Measure.real, Measure.map_apply hr MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ]
  rw [hmu]

/-- **The core of the closeness of the coefficients of the cutoff interaction on two tori.**
If the entries of the Stieltjes families of the final operators differ by at most `δ` on `Y(C)²`
(`hmain`), the coefficients of the cutoff interaction differ by at most
`Lip |Y(C)| δ ρ γ(box ρ) / (e^κ - 1)^{|C|}`; both the absolute and the weighted closeness of the
Stieltjes families enter through this statement. -/
theorem final_coef_cutoffInteraction_close_core (hd : 0 < d) (hM : 0 < M) {κ : ℝ}
    (hκ : 1 ≤ κ) (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M)
    (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) (nC : ℕ)
    {k : ℕ} (hk : 1 ≤ k) {δ : ℕ → ℕ → ℕ → ℝ} (hδ0 : ∀ J N N', 0 ≤ δ J N N')
    (hmain : ∀ {J N N' : ℕ} [NeZero N] [NeZero N'], 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' →
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
        δ J N N') :
    ∀ {J N N' : ℕ} [NeZero N] [NeZero N'], 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {γ : Measure (L1Torus d N → ℝ)} {γ' : Measure (L1Torus d N' → ℝ)} {ρ RF B' Lip : ℝ},
      0 ≤ ρ →
      γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
      γ' {ψ : L1Torus d N' → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * ρ < RF →
      ∀ {F : (L1Torus d N → ℂ) → ℂ} {F' : (L1Torus d N' → ℂ) → ℂ},
      AnalyticOnNhd ℂ F (polydisc (0 : L1Torus d N → ℂ) (fun _ => RF)) →
      (∀ w ∈ polydisc (0 : L1Torus d N → ℂ) (fun _ => RF), ‖F w‖ ≤ B') →
      AnalyticOnNhd ℂ F' (polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF)) →
      (∀ w ∈ polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF), ‖F' w‖ ≤ B') →
      Measurable F → Measurable F' →
      (∀ (w : L1Torus d N → ℂ) (w' : L1Torus d N' → ℂ),
        (∀ x, x ∉ macRegion d N M C → w x = 0) →
        (∀ x', x' ∉ macRegion d N' M (C.image e) → w' x' = 0) →
        (∀ x, ‖w x‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρ) →
        (∀ x', ‖w' x'‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρ) → ∀ η : ℝ, 0 ≤ η →
        (∀ x ∈ macRegion d N M C, ‖w' (f x) - w x‖ ≤ η) → ‖F' w' - F w‖ ≤ Lip * η) →
      Measure.map (fun (ψ : L1Torus d N → ℝ) (q : ↥(macRegion d N M C)) => ψ q)
          (γ.restrict {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}) =
        Measure.map (fun (ψ' : L1Torus d N' → ℝ) (q : ↥(macRegion d N M C)) => ψ' (f q))
          (γ'.restrict {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ}) →
      ‖coef (fun s : MacIdx d N M → ℂ => ∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
          F (fun x => ∑ y, taggedCfin d L N k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C -
        coef (fun s' : MacIdx d N' M → ℂ => ∫ ψ' in {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ},
          F' (fun x => ∑ y, taggedCfin d L N' k M v a s' x y * ((ψ' y : ℝ) : ℂ)) ∂γ')
          (C.image e)‖ ≤
        Lip * (((nC * (8 * M + 1) ^ d : ℕ) : ℝ) *
          (δ J N N') * ρ) *
          (γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal / (Real.exp κ - 1) ^ C.card := by
  classical
  have hκ0 : 0 ≤ κ := by linarith
  intro J N N' _ _ hN hN' f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass γ γ' ρ RF B' Lip hρ hγfin
    hγfin' hBR F F' hFan hFB hFan' hFB' hFm hFm' hFclose hγ
  have hδ0 := hδ0 J N N'
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 (by linarith)
  set Bc : ℝ := 4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
    Real.sqrt (finalGap d L) with hBc
  have hBc0 : 0 ≤ Bc := by
    have : 0 ≤ ballConst d (pdEps d L / 2) :=
      ballConst_decay_nonneg (by have := pdEps_pos (d := d) (L := L) hd; positivity)
    positivity
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
  obtain ⟨hJan, -⟩ := cutoffInteraction_final (N₀ := N) (k := k) (L := L) (v := v) (a := a) hd hk
    hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hγfin hBR hFan hFB
  obtain ⟨hJan', -⟩ := cutoffInteraction_final (N₀ := N') (k := k) (L := L) (v := v) (a := a) hd hk
    hv0 hv1 ha1 ha2 hmass hM hκ hMB hMκ hρ hγfin' hBR hFan' hFB'
  have hnY : (Nat.card ↥(macRegion d N M C) : ℝ) ≤ ((nC * (8 * M + 1) ^ d : ℕ) : ℝ) := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h1 : (Finset.univ.filter fun u => u ∈ macRegion d N M C) = C.biUnion (macBoxF d N M) := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mem_biUnion_macBoxF]
    rw [h1]
    have := card_biUnion_macBoxF_le hM C
    have h2 : C.card * (8 * M + 1) ^ d ≤ nC * (8 * M + 1) ^ d :=
      Nat.mul_le_mul_right _ hCc
    exact_mod_cast this.trans h2
  have hFBw : ∀ w : L1Torus d N → ℂ, (∀ x, ‖w x‖ ≤ Bc * ρ) → ‖F w‖ ≤ B' := fun w hw =>
    hFB w (fun x => by
      simpa using lt_of_le_of_lt (hw x) hBR)
  have hFBw' : ∀ w : L1Torus d N' → ℂ, (∀ x, ‖w x‖ ≤ Bc * ρ) → ‖F' w‖ ≤ B' := fun w hw =>
    hFB' w (fun x => by
      simpa using lt_of_le_of_lt (hw x) hBR)
  refine norm_coef_sub_relabel_le hR e hinjE hJan hJan' (fun s hs s' hs' hss => ?_)
  have hsκ : ∀ p, ‖s p‖ ≤ Real.exp κ := fun p => (hs.2 p).le
  have hCC : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖taggedCfinU d N M (finalOp d L N k v a) s x y -
        taggedCfinU d N' M (finalOp d L N' k v a) s' (f x) (f y)‖ ≤
      δ J N N' := fun x hx y hy =>
    hmain hN hN' hf he hCc hC hv0 hv1 ha1 ha2 hmass hs.1 hs' hss hsκ hx hy
  have hsκ' : ∀ p, ‖s' p‖ ≤ Real.exp κ := by
    intro p
    by_cases hp : p ∈ C.image e
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
      rw [hss i hi]; exact hsκ i
    · rw [hs' p hp, norm_zero]; exact (Real.exp_pos _).le
  have hrow : ∀ x, ∑ y, ‖taggedCfinU d N M (finalOp d L N k v a) s x y‖ ≤ Bc := by
    intro x
    simp only [taggedCfinU_finalOp]
    simpa using taggedCfin_row_bound (N₀ := N) (k := k) (L := L) (v := v) (a := a) (M := M) hd hk
      hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ hsκ (r := 0) le_rfl
      (by have := pdEps_pos (d := d) (L := L) hd; positivity) x
  have hrow' : ∀ x', ∑ y, ‖taggedCfinU d N' M (finalOp d L N' k v a) s' x' y‖ ≤ Bc := by
    intro x'
    simp only [taggedCfinU_finalOp]
    simpa using taggedCfin_row_bound (N₀ := N') (k := k) (L := L) (v := v) (a := a) (M := M) hd hk
      hv0 hv1 ha1 ha2 hmass hM hκ0 hMB hMκ hsκ' (r := 0) le_rfl
      (by have := pdEps_pos (d := d) (L := L) hd; positivity) x'
  have := integral_cutoff_close hM hd hN hN' hf he hC (U := finalOp d L N k v a)
    (U' := finalOp d L N' k v a) hs.1 hs' hρ hδ0 hnY hCC hrow hrow' hγfin hFm hFm'
    hFBw hFBw' hFclose hγ
  simpa only [taggedCfinU_finalOp] using this


/-- **The coefficients of the cutoff interaction of the final operators on two tori, from the
closeness of the entries of the Stieltjes families** (`hmain` is the conclusion of
`final_taggedCfinU_close_twoTorus` at the scale `k`, for given `P`, `C₀`, `c₀`). -/
theorem final_coef_cutoffInteraction_close_twoTorus_of_cfin (hd : 0 < d) (hM : 0 < M) {κ : ℝ}
    (hκ : 1 ≤ κ) (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M)
    (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) (nC : ℕ)
    {k : ℕ} (hk : 1 ≤ k) {P C₀ c₀ : ℝ} (hP0 : 0 ≤ P) (hC₀ : 0 < C₀)
    (hmain : ∀ {J N N' : ℕ} [NeZero N] [NeZero N'], 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' →
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
          Real.sqrt (finalGap d L)) :
    ∀ {J N N' : ℕ} [NeZero N] [NeZero N'], 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {γ : Measure (L1Torus d N → ℝ)} {γ' : Measure (L1Torus d N' → ℝ)} {ρ RF B' Lip : ℝ},
      0 ≤ ρ →
      γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
      γ' {ψ : L1Torus d N' → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * ρ < RF →
      ∀ {F : (L1Torus d N → ℂ) → ℂ} {F' : (L1Torus d N' → ℂ) → ℂ},
      AnalyticOnNhd ℂ F (polydisc (0 : L1Torus d N → ℂ) (fun _ => RF)) →
      (∀ w ∈ polydisc (0 : L1Torus d N → ℂ) (fun _ => RF), ‖F w‖ ≤ B') →
      AnalyticOnNhd ℂ F' (polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF)) →
      (∀ w ∈ polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF), ‖F' w‖ ≤ B') →
      Measurable F → Measurable F' →
      (∀ (w : L1Torus d N → ℂ) (w' : L1Torus d N' → ℂ),
        (∀ x, x ∉ macRegion d N M C → w x = 0) →
        (∀ x', x' ∉ macRegion d N' M (C.image e) → w' x' = 0) →
        (∀ x, ‖w x‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρ) →
        (∀ x', ‖w' x'‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρ) → ∀ η : ℝ, 0 ≤ η →
        (∀ x ∈ macRegion d N M C, ‖w' (f x) - w x‖ ≤ η) → ‖F' w' - F w‖ ≤ Lip * η) →
      Measure.map (fun (ψ : L1Torus d N → ℝ) (q : ↥(macRegion d N M C)) => ψ q)
          (γ.restrict {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}) =
        Measure.map (fun (ψ' : L1Torus d N' → ℝ) (q : ↥(macRegion d N M C)) => ψ' (f q))
          (γ'.restrict {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ}) →
      ‖coef (fun s : MacIdx d N M → ℂ => ∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
          F (fun x => ∑ y, taggedCfin d L N k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C -
        coef (fun s' : MacIdx d N' M → ℂ => ∫ ψ' in {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ},
          F' (fun x => ∑ y, taggedCfin d L N' k M v a s' x y * ((ψ' y : ℝ) : ℂ)) ∂γ')
          (C.image e)‖ ≤
        Lip * (((nC * (8 * M + 1) ^ d : ℕ) : ℝ) *
          (P * (C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ)))) /
            Real.sqrt (finalGap d L)) * ρ) *
          (γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal / (Real.exp κ - 1) ^ C.card := by
  exact final_coef_cutoffInteraction_close_core hd hM hκ hMB hMκ nC hk
    (δ := fun J N N' => P * (C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 -
      (((J + 3) * M : ℕ) : ℝ)))) / Real.sqrt (finalGap d L)) (fun _ _ _ => by positivity) hmain

/-- **The coefficients of the cutoff interaction of the final operators on two tori.**  The
localized coefficients `coef J C` and `coef J' (e C)` of
`J(s) = ∫_{box ρ} F (C_fin(s) ψ) dγ(ψ)` on the two tori differ by at most
`Lip · |Y(C)| δ ρ γ(box ρ) / (e^κ - 1)^{|C|}`, where `δ = P C₀ exp(-c₀ (min N N'/2 - (J+3) M)) / √g`
bounds the entries of the Stieltjes families (`final_taggedCfinU_close_twoTorus`).  The functionals
`F`, `F'` are analytic and bounded on a polydisc of radius `R_F > B_C ρ` (`B_C` the row bound of
`taggedCfin`), measurable, and correspond up to the Lipschitz bound `hFclose` (the exact
correspondence `hF` of `coef_cutoffInteraction_final_eq_twoTorus` is the case `η = 0`); the reference
measures correspond exactly (`hγ`). -/
theorem final_coef_cutoffInteraction_close_twoTorus (hd : 0 < d) (hM : 0 < M) {κ : ℝ}
    (hκ : 1 ≤ κ) (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M)
    (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M) (nC : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ {k : ℕ}, 1 ≤ k → ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧
      ∀ {J N N' : ℕ} [NeZero N] [NeZero N'], 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {γ : Measure (L1Torus d N → ℝ)} {γ' : Measure (L1Torus d N' → ℝ)} {ρ RF B' Lip : ℝ},
      0 ≤ ρ →
      γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
      γ' {ψ : L1Torus d N' → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤ →
      (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
        Real.sqrt (finalGap d L)) * ρ < RF →
      ∀ {F : (L1Torus d N → ℂ) → ℂ} {F' : (L1Torus d N' → ℂ) → ℂ},
      AnalyticOnNhd ℂ F (polydisc (0 : L1Torus d N → ℂ) (fun _ => RF)) →
      (∀ w ∈ polydisc (0 : L1Torus d N → ℂ) (fun _ => RF), ‖F w‖ ≤ B') →
      AnalyticOnNhd ℂ F' (polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF)) →
      (∀ w ∈ polydisc (0 : L1Torus d N' → ℂ) (fun _ => RF), ‖F' w‖ ≤ B') →
      Measurable F → Measurable F' →
      (∀ (w : L1Torus d N → ℂ) (w' : L1Torus d N' → ℂ),
        (∀ x, x ∉ macRegion d N M C → w x = 0) →
        (∀ x', x' ∉ macRegion d N' M (C.image e) → w' x' = 0) →
        (∀ x, ‖w x‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρ) →
        (∀ x', ‖w' x'‖ ≤ (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
          Real.sqrt (finalGap d L)) * ρ) → ∀ η : ℝ, 0 ≤ η →
        (∀ x ∈ macRegion d N M C, ‖w' (f x) - w x‖ ≤ η) → ‖F' w' - F w‖ ≤ Lip * η) →
      Measure.map (fun (ψ : L1Torus d N → ℝ) (q : ↥(macRegion d N M C)) => ψ q)
          (γ.restrict {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}) =
        Measure.map (fun (ψ' : L1Torus d N' → ℝ) (q : ↥(macRegion d N M C)) => ψ' (f q))
          (γ'.restrict {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ}) →
      ‖coef (fun s : MacIdx d N M → ℂ => ∫ ψ in {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ},
          F (fun x => ∑ y, taggedCfin d L N k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ) C -
        coef (fun s' : MacIdx d N' M → ℂ => ∫ ψ' in {ψ' : L1Torus d N' → ℝ | ∀ y, |ψ' y| ≤ ρ},
          F' (fun x => ∑ y, taggedCfin d L N' k M v a s' x y * ((ψ' y : ℝ) : ℂ)) ∂γ')
          (C.image e)‖ ≤
        Lip * (((nC * (8 * M + 1) ^ d : ℕ) : ℝ) *
          (P * (C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ)))) /
            Real.sqrt (finalGap d L)) * ρ) *
          (γ {ψ : L1Torus d N → ℝ | ∀ y, |ψ y| ≤ ρ}).toReal / (Real.exp κ - 1) ^ C.card := by
  have hκ0 : 0 ≤ κ := by linarith
  obtain ⟨P, hP0, hP⟩ := final_taggedCfinU_close_twoTorus (L := L) hd hM hκ0 hMB hMκ nC
  refine ⟨P, hP0, ?_⟩
  intro k hk
  obtain ⟨C₀, c₀, hC₀, hc₀, hmain⟩ := hP hk
  exact ⟨C₀, c₀, hC₀, hc₀, final_coef_cutoffInteraction_close_twoTorus_of_cfin hd hM hκ hMB hMκ nC
    hk hP0 hC₀ hmain⟩

end Interaction


section LogDet

variable {d M J N N' L : ℕ} [NeZero N] [NeZero N'] [NeZero L]

/-- A `(r, η)`-small matrix with `0 ≤ r` and `0 ≤ η` has entries of modulus at most `η`. -/
theorem WSmall.norm_le_of_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace ι]
    {r η : ℝ} {E : Matrix ι ι ℂ} (h : WSmall r η E) (hr : 0 ≤ r) (hη : 0 ≤ η) (x y : ι) :
    ‖E x y‖ ≤ η := by
  refine (h.entry x y).trans ?_
  have : Real.exp (-r * dist x y) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [dist_nonneg (x := x) (y := y)])
  nlinarith

/-- **The core of the closeness of the localized logarithm coefficients on two tori.**  If the
tagged perturbed defects of the two tori differ by at most `δ0` on `Y(C)²` for all parameters
`s`, `s'` (supported on `C`, `e C`, equal along `e`, of modulus at most `e^κ`), then the
coefficients of the logarithms of their determinants over `C` and `e C` differ by at most
`2 (nC (8M+1)^d)² δ0 / (e^κ - 1)^{|C|}`.  The absolute and the weighted closeness of the tagged
defects both enter through this statement. -/
theorem final_coef_logdet_close_core (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 < κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {rE η : ℝ} (hrE : pdEps d L / 4 ≤ rE)
    (hη : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η *
      ballConst d (3 * pdEps d L / 4))) ≤ 1) (nC : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hN : 2 * (J + 6) * M ≤ N) (hN' : 2 * (J + 6) * M ≤ N') {f : L1Torus d N → L1Torus d N'}
    (hf : ∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N'))
    {e : MacIdx d N M → MacIdx d N' M}
    (he : ∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i)
    {C : Finset (MacIdx d N M)} (hCc : C.card ≤ nC)
    (hC : ∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J)
    {v a : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
    (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v) {t : ℝ} (ht : 0 ≤ t)
    {E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {E' : Matrix (L1Torus d N') (L1Torus d N') ℂ}
    (hE : WSmall rE η E) (hE' : WSmall rE η E')
    {ρ ρ' : ℝ} (hρ : Real.exp κ < ρ) (hρ' : Real.exp κ < ρ')
    {ell : (MacIdx d N M → ℂ) → ℂ} {ell' : (MacIdx d N' M → ℂ) → ℂ}
    (hell : AnalyticOnNhd ℂ ell (Metric.ball 0 ρ)) (hell' : AnalyticOnNhd ℂ ell' (Metric.ball 0 ρ'))
    (h0 : ell 0 = 0) (h0' : ell' 0 = 0)
    (hdet : ∀ s ∈ Metric.ball (0 : MacIdx d N M → ℂ) ρ,
        (1 - taggedMat Finset.univ (macTags d N M)
          (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
              (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N k v a) (macBoxF d N M z) t)) s).det =
          Complex.exp (ell s))
    (hdet' : ∀ s ∈ Metric.ball (0 : MacIdx d N' M → ℂ) ρ',
        (1 - taggedMat Finset.univ (macTags d N' M)
          (fun z => boxR (finalOp d L N' k v a) (macBoxF d N' M z)
              (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
            E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N' k v a) (macBoxF d N' M z) t)) s).det =
          Complex.exp (ell' s))
    {δ0 : ℝ} (hδ00 : 0 ≤ δ0)
    (hdd : ∀ {s : MacIdx d N M → ℂ}, s ∈ supportedOn C →
      ∀ {s' : MacIdx d N' M → ℂ}, s' ∈ supportedOn (C.image e) →
      (∀ i ∈ C, s' (e i) = s i) → (∀ p, ‖s p‖ ≤ Real.exp κ) →
      ∀ {x y : L1Torus d N}, x ∈ macRegion d N M C → y ∈ macRegion d N M C →
      ‖taggedMat Finset.univ (macTags d N M)
          (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
              (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N k v a) (macBoxF d N M z) t)) s x y -
        taggedMat Finset.univ (macTags d N' M)
          (fun z => boxR (finalOp d L N' k v a) (macBoxF d N' M z)
              (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
            E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N' k v a) (macBoxF d N' M z) t)) s' (f x) (f y)‖ ≤ δ0) :
    ‖coef ell C - coef ell' (C.image e)‖ ≤
      2 * ((((nC : ℝ) * (((8 * M + 1) ^ d : ℕ) : ℝ)) ^ 2) * δ0) / (Real.exp κ - 1) ^ C.card := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hA0 := finalDecayC_pos (L := L) hd
  have hκ0 : 0 ≤ κ := hκ.le
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hR0 : 0 < Real.exp κ := by linarith
  set nB : ℝ := (((8 * M + 1) ^ d : ℕ) : ℝ) with hnBdef
  have hnB : 0 ≤ nB := by positivity
  set nY : ℝ := (nC : ℝ) * nB with hnY
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
  obtain ⟨τ, hτc, hτ0, hτe, hτs, hτn⟩ := exists_relabel_map e hinjE
  -- the sets and the bijection
  obtain ⟨g, hg'⟩ : ∃ g : L1Torus d N' → L1Torus d N, ∀ y μ, g y μ = (((y μ).val : ℕ) : ZMod N) :=
    ⟨fun y μ => (((y μ).val : ℕ) : ZMod N), fun _ _ => rfl⟩
  set Yset : Finset (L1Torus d N) := Finset.univ.filter (fun u => u ∈ macRegion d N M C) with hYset
  have hYmem : ∀ u, u ∈ Yset ↔ u ∈ macRegion d N M C := fun u => by simp [hYset]
  set Y'set : Finset (L1Torus d N') :=
    Finset.univ.filter (fun u => u ∈ macRegion d N' M (C.image e)) with hY'set
  have hY'mem : ∀ u, u ∈ Y'set ↔ u ∈ macRegion d N' M (C.image e) := fun u => by simp [hY'set]
  have hbij : Set.BijOn f (Yset : Set (L1Torus d N)) (Y'set : Set (L1Torus d N')) := by
    have := macRegion_bijOn hM hN hN' hf hg' he hC
    simpa [hYset, hY'set] using this
  have hbij' : Function.Bijective (fun q : Yset => (⟨f q, hbij.mapsTo q.2⟩ : Y'set)) := by
    constructor
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (hbij.injOn a.2 b.2 this)
    · intro b
      obtain ⟨a, ha, hab⟩ := hbij.surjOn b.2
      exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  set εq : Yset ≃ Y'set := Equiv.ofBijective _ hbij' with hεq
  have hYcard : (Fintype.card Yset : ℝ) ≤ nY := by
    rw [Fintype.card_coe]
    have h1 : Yset = C.biUnion (macBoxF d N M) := by
      ext u; rw [hYmem, mem_biUnion_macBoxF]
    rw [h1]
    calc ((C.biUnion (macBoxF d N M)).card : ℝ) ≤ (C.card : ℝ) * nB := by
          have := card_biUnion_macBoxF_le hM C
          rw [hnBdef]; exact_mod_cast this
      _ ≤ nY := by
          rw [hnY]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hCc) hnB
  set aF : MacIdx d N M → Matrix (L1Torus d N) (L1Torus d N) ℂ := fun z =>
    boxR (finalOp d L N k v a) (macBoxF d N M z) (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
      E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
        boxG (finalOp d L N k v a) (macBoxF d N M z) t) with haF
  set aF' : MacIdx d N' M → Matrix (L1Torus d N') (L1Torus d N') ℂ := fun z =>
    boxR (finalOp d L N' k v a) (macBoxF d N' M z) (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
      E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
        boxG (finalOp d L N' k v a) (macBoxF d N' M z) t) with haF'
  have hrowfull : ∀ s : MacIdx d N M → ℂ, (∀ p, ‖s p‖ ≤ Real.exp κ) → ∀ x,
      ∑ y, ‖taggedMat Finset.univ (macTags d N M) aF s x y‖ ≤ 1 / 2 := fun s hs x =>
    taggedKE_rowsum_le_half hd hk hv0 hv1 ha1 ha2 hmass hE hrE ht hM hκ0 hMB hMκ hη hs x
  have hrowfull' : ∀ s : MacIdx d N' M → ℂ, (∀ p, ‖s p‖ ≤ Real.exp κ) → ∀ x,
      ∑ y, ‖taggedMat Finset.univ (macTags d N' M) aF' s x y‖ ≤ 1 / 2 := fun s hs x =>
    taggedKE_rowsum_le_half hd hk hv0 hv1 ha1 ha2 hmass hE' hrE ht hM hκ0 hMB hMκ hη hs x
  set S : Set (MacIdx d N M → ℂ) := Metric.closedBall 0 (Real.exp κ) ∩ supportedOn C with hS
  have hSconv : IsPreconnected S :=
    ((convex_closedBall _ _).inter (convex_supportedOn C)).isPreconnected
  have h0S : (0 : MacIdx d N M → ℂ) ∈ S := ⟨Metric.mem_closedBall_self hR0.le, fun i _ => rfl⟩
  have hsκ : ∀ s ∈ S, ∀ p, ‖s p‖ ≤ Real.exp κ := fun s hs p =>
    (norm_le_pi_norm s p).trans (mem_closedBall_zero_iff.1 hs.1)
  have hτκ : ∀ s ∈ S, ∀ p, ‖τ s p‖ ≤ Real.exp κ := fun s hs p =>
    hτn s _ hR0.le (hsκ s hs) p
  have hdd' : ∀ s ∈ S, ∀ x ∈ Yset, ∀ y ∈ Yset,
      ‖taggedMat Finset.univ (macTags d N M) aF s x y -
        taggedMat Finset.univ (macTags d N' M) aF' (τ s) (f x) (f y)‖ ≤ δ0 :=
    fun s hs x hx y hy => hdd hs.2 (hτs s) (fun i hi => hτe s i hi) (hsκ s hs)
      ((hYmem x).1 hx) ((hYmem y).1 hy)
  have hSball : ∀ s ∈ S, s ∈ Metric.ball (0 : MacIdx d N M → ℂ) ρ := fun s hs => by
    rw [mem_ball_zero_iff]; exact lt_of_le_of_lt (mem_closedBall_zero_iff.1 hs.1) hρ
  have hSball' : ∀ s ∈ S, τ s ∈ Metric.ball (0 : MacIdx d N' M → ℂ) ρ' := fun s hs => by
    rw [mem_ball_zero_iff]
    exact lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hR0.le).2 (hτκ s hs)) hρ'
  have key := logdet_close_blocks hSconv h0S f hbij
    (KA := fun s => taggedMat Finset.univ (macTags d N M) aF s)
    (KB := fun s => taggedMat Finset.univ (macTags d N' M) aF' (τ s))
    (tm_continuous aF) ((tm_continuous aF').comp hτc) (tm_zero hM hd aF)
    (by simp only [hτ0]; exact tm_zero hM hd aF')
    (fun s hs x hx y => tm_row_eq_zero hM hd aF hs.2 (fun h => hx ((hYmem x).2 h)) y)
    (fun s hs x hx y => tm_row_eq_zero hM hd aF' (hτs s) (fun h => hx ((hY'mem x).2 h)) y)
    (fun s hs x => hrowfull s (hsκ s hs) x) (fun s hs x => hrowfull' (τ s) (hτκ s hs) x) hδ00 hdd'
    (ell₁ := ell) (ell₂ := fun s => ell' (τ s))
    (hell.continuousOn.mono fun s hs => hSball s hs)
    (hell'.continuousOn.comp hτc.continuousOn fun s hs => hSball' s hs) h0
    (by simp only [hτ0]; exact h0')
    (fun s hs => hdet s (hSball s hs)) (fun s hs => hdet' _ (hSball' s hs))
  have hA := norm_coef_sub_relabel_le hR e hinjE (f := ell) (f' := ell')
    (by rw [polydisc_eq_ball hR0]; exact hell.mono (Metric.ball_subset_ball hρ.le))
    (by rw [polydisc_eq_ball hR0]; exact hell'.mono (Metric.ball_subset_ball hρ'.le))
    (B := 2 * (nY ^ 2 * δ0)) (fun s hs s' hs' hss => ?_)
  · exact hA
  · have hsS : s ∈ S := ⟨mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg hR0.le).2
      fun p => (hs.2 p).le), hs.1⟩
    have hs'eq : s' = τ s := by
      funext j
      by_cases hj : j ∈ C.image e
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
        rw [hss i hi, hτe s i hi]
      · rw [hs' j hj, hτs s j hj]
    rw [hs'eq]
    refine (key s hsS).trans ?_
    have hcard2 : (Yset.card : ℝ) ^ 2 ≤ nY ^ 2 := by
      have : (0 : ℝ) ≤ Yset.card := by positivity
      have h' : (Yset.card : ℝ) ≤ nY := by rw [← Fintype.card_coe]; exact hYcard
      exact pow_le_pow_left₀ this h' 2
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard2 hδ00) (by norm_num)


/-- **The localized coefficients of the logarithm of the perturbed defect on two tori, from the
closeness of the entries of the final operators on the window** (`hmain`: the conclusion of
`final_region_entry_close` at the scale `k`, including the mass window; the constant `P` does not
depend on `k`, `C₀`, `c₀`). -/
theorem final_coef_logdet_close_twoTorus_of_entries (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 < κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {rE η : ℝ} (hrE : pdEps d L / 4 ≤ rE) (hη0 : 0 ≤ η)
    (hη : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η *
      ballConst d (3 * pdEps d L / 4))) ≤ 1) (nC : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ {k : ℕ}, 1 ≤ k → ∀ {C₀ c₀ : ℝ}, 0 < C₀ → 0 < c₀ →
      (∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
        ∀ {M J N N' : ℕ} [NeZero N] [NeZero N'], 0 < M → 2 * (J + 6) * M ≤ N →
        2 * (J + 6) * M ≤ N' → ∀ {f : L1Torus d N → L1Torus d N'},
        (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
        ∀ {C : Finset (MacIdx d N M)}, (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
        ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
        ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤
          C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ)))) →
      ∀ {J N N' : ℕ} [NeZero N] [NeZero N'], 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {t : ℝ}, 0 ≤ t →
      ∀ {E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {E' : Matrix (L1Torus d N') (L1Torus d N') ℂ},
      WSmall rE η E → WSmall rE η E' → ∀ {εE : ℝ}, 0 ≤ εE →
      (∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, ‖E x y - E' (f x) (f y)‖ ≤ εE) →
      ∀ {ρ ρ' : ℝ}, Real.exp κ < ρ → Real.exp κ < ρ' →
      ∀ {ell : (MacIdx d N M → ℂ) → ℂ} {ell' : (MacIdx d N' M → ℂ) → ℂ},
      AnalyticOnNhd ℂ ell (Metric.ball 0 ρ) → AnalyticOnNhd ℂ ell' (Metric.ball 0 ρ') →
      ell 0 = 0 → ell' 0 = 0 →
      (∀ s ∈ Metric.ball (0 : MacIdx d N M → ℂ) ρ,
        (1 - taggedMat Finset.univ (macTags d N M)
          (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
              (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N k v a) (macBoxF d N M z) t)) s).det =
          Complex.exp (ell s)) →
      (∀ s ∈ Metric.ball (0 : MacIdx d N' M → ℂ) ρ',
        (1 - taggedMat Finset.univ (macTags d N' M)
          (fun z => boxR (finalOp d L N' k v a) (macBoxF d N' M z)
              (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
            E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N' k v a) (macBoxF d N' M z) t)) s).det =
          Complex.exp (ell' s)) →
      ‖coef ell C - coef ell' (C.image e)‖ ≤
        P * (C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ))) + εE) /
          (Real.exp κ - 1) ^ C.card := by
  classical
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg := finalGap_pos (d := d) hL
  have hA0 := finalDecayC_pos (L := L) hd
  have hκ0 : 0 ≤ κ := hκ.le
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hR0 : 0 < Real.exp κ := by linarith
  set nB : ℝ := (((8 * M + 1) ^ d : ℕ) : ℝ) with hnBdef
  have hnB : 0 ≤ nB := by positivity
  set cc : ℝ := (nC : ℝ) * Real.exp (κ * nC) with hcc
  set nY : ℝ := (nC : ℝ) * nB with hnY
  set P0 : ℝ := finalDecayC d L / finalGap d L + 1 with hP0
  set c1 : ℝ := nB * (2 + P0 * nB ^ 2) / finalGap d L + η * nB ^ 3 / finalGap d L ^ 2 with hc1
  set c2 : ℝ := 2 * nB / finalGap d L with hc2
  have hP00 : 0 ≤ P0 := by positivity
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  refine ⟨2 * nY ^ 2 * cc * (c1 + c2), by positivity, ?_⟩
  intro k hk C₀ c₀ hC₀ hc₀ hmain J N N' _ _ hN hN' f hf e he C hCc hC v a hv0 hv1 ha1 ha2 hmass t ht E E'
    hE hE' εE hεE0 hEc ρ ρ' hρ hρ' ell ell' hell hell' h0 h0' hdet hdet'
  set ε₀ : ℝ := C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ))) with hε₀
  have hε00 : 0 ≤ ε₀ := by positivity
  have hU : ∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C,
      ‖finalOp d L N k v a x y - finalOp d L N' k v a (f x) (f y)‖ ≤ ε₀ :=
    fun x hx y hy => hmain hv0 hv1 ha1 ha2 hmass hM hN hN' hf hC x hx y hy
  have hEb : ∀ x y, ‖E' x y‖ ≤ η := fun x y => WSmall.norm_le_of_nonneg hE'
    (le_trans (by have := pdEps_pos (d := d) (L := L) hd; positivity) hrE) hη0 x y
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
  set δ0 : ℝ := cc * (c1 * ε₀ + c2 * εE) with hδ0
  have hδ00 : 0 ≤ δ0 := by positivity
  have hnum : ∀ gT : ℝ, 0 ≤ gT → gT ≤ (finalGap d L)⁻¹ →
      nB * ε₀ * gT * (2 + P0 * nB ^ 2) +
        nB * (εE * (2 * gT) + η * (nB ^ 2 * ε₀ * gT ^ 2)) ≤ c1 * ε₀ + c2 * εE := by
    intro gT hgT0 hgT
    have e1 : nB * ε₀ * gT * (2 + P0 * nB ^ 2) +
        nB * (εE * (2 * gT) + η * (nB ^ 2 * ε₀ * gT ^ 2)) =
        (nB * (2 + P0 * nB ^ 2) * ε₀) * gT + (η * nB ^ 3 * ε₀) * gT ^ 2 + (2 * nB * εE) * gT := by
      ring
    have e2 : c1 * ε₀ + c2 * εE = (nB * (2 + P0 * nB ^ 2) * ε₀) * (finalGap d L)⁻¹ +
        (η * nB ^ 3 * ε₀) * ((finalGap d L)⁻¹) ^ 2 + (2 * nB * εE) * (finalGap d L)⁻¹ := by
      simp only [hc1, hc2, div_eq_mul_inv, inv_pow]; ring
    rw [e1, e2]
    gcongr
  have hdd0 : ∀ {s : MacIdx d N M → ℂ}, s ∈ supportedOn C →
      ∀ {s' : MacIdx d N' M → ℂ}, s' ∈ supportedOn (C.image e) →
      (∀ i ∈ C, s' (e i) = s i) → (∀ p, ‖s p‖ ≤ Real.exp κ) →
      ∀ {x y : L1Torus d N}, x ∈ macRegion d N M C → y ∈ macRegion d N M C →
      ‖taggedMat Finset.univ (macTags d N M)
          (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
              (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N k v a) (macBoxF d N M z) t)) s x y -
        taggedMat Finset.univ (macTags d N' M)
          (fun z => boxR (finalOp d L N' k v a) (macBoxF d N' M z)
              (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
            E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N' k v a) (macBoxF d N' M z) t)) s' (f x) (f y)‖ ≤ δ0 := by
    intro s hs s' hs' hss hsκ x y hx hy
    have hgt : 0 < finalGap d L + t := by linarith
    have h := final_taggedKE_close hM hN hN' hf he hC hd hk hv0 hv1 ha1 ha2 hmass hκ0 hη0 hU hEc
      hEb ht hs hs' hss hsκ hx hy
    refine h.trans ?_
    have hCc' : (C.card : ℝ) * Real.exp (κ * C.card) ≤ cc := by
      rw [hcc]
      apply mul_le_mul (by exact_mod_cast hCc) _ (Real.exp_pos _).le (by positivity)
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by exact_mod_cast hCc) hκ0)
    have hgT : (finalGap d L + t)⁻¹ ≤ (finalGap d L)⁻¹ := inv_anti₀ hg (by linarith)
    have hb := hnum _ (inv_pos.2 hgt).le hgT
    have hbig : 0 ≤ nB * ε₀ * (finalGap d L + t)⁻¹ * (2 + P0 * nB ^ 2) +
        nB * (εE * (2 * (finalGap d L + t)⁻¹) + η * (nB ^ 2 * ε₀ * (finalGap d L + t)⁻¹ ^ 2)) := by
      have := inv_pos.2 hgt
      positivity
    calc _ ≤ cc * ((nB * ε₀ * (finalGap d L + t)⁻¹ * (2 + P0 * nB ^ 2) +
            nB * (εE * (2 * (finalGap d L + t)⁻¹) + η * (nB ^ 2 * ε₀ * (finalGap d L + t)⁻¹ ^ 2)))) :=
          mul_le_mul_of_nonneg_right hCc' hbig
      _ ≤ cc * (c1 * ε₀ + c2 * εE) := mul_le_mul_of_nonneg_left hb (by positivity)
  refine (final_coef_logdet_close_core hd hM hκ hMB hMκ hrE hη nC hk hN hN' hf he hCc hC hv0 hv1
    ha1 ha2 hmass ht hE hE' hρ hρ' hell hell' h0 h0' hdet hdet' hδ00 hdd0).trans ?_
  have hpow : 0 < (Real.exp κ - 1) ^ C.card := pow_pos (by linarith) _
  rw [div_eq_mul_inv, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hpow.le)
  have : c1 * ε₀ + c2 * εE ≤ (c1 + c2) * (ε₀ + εE) := by
    have h1 : 0 ≤ c1 * εE := mul_nonneg hc10 hεE0
    have h2 : 0 ≤ c2 * ε₀ := mul_nonneg hc20 hε00
    calc c1 * ε₀ + c2 * εE ≤ (c1 * ε₀ + c2 * εE) + (c1 * εE + c2 * ε₀) :=
          le_add_of_nonneg_right (add_nonneg h1 h2)
      _ = (c1 + c2) * (ε₀ + εE) := by ring
  calc 2 * (nY ^ 2 * δ0) = 2 * nY ^ 2 * cc * (c1 * ε₀ + c2 * εE) := by rw [hδ0]; ring
    _ ≤ 2 * nY ^ 2 * cc * ((c1 + c2) * (ε₀ + εE)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring


/-- **The localized coefficients of the logarithm of the perturbed defect on two tori.**
Let `E`, `E'` be `(rE, η)`-small perturbations of the final operators of the tori `N`, `N'` that
are close up to `εE` on `Y(C)²`, and `ell`, `ell'` analytic logarithms (vanishing at `0`) of
`det (1 - K_E(s, t))` on a polydisc of radius `> e^κ`.  Then
`‖coef ell C - coef ell' (e C)‖ ≤ P (ε + εE) / (e^κ - 1)^{|C|}`, where
`ε = C₀ exp(-c₀ (min N N' / 2 - (J+3) M))` is the error of the final operators
(`final_region_entry_close`) and `P` depends on `d, L, M, κ, η` and a bound `nC` of `|C|` only. -/
theorem final_coef_logdet_close_twoTorus (hd : 0 < d) (hM : 0 < M) {κ : ℝ} (hκ : 0 < κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {rE η : ℝ} (hrE : pdEps d L / 4 ≤ rE) (hη0 : 0 ≤ η)
    (hη : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η *
      ballConst d (3 * pdEps d L / 4))) ≤ 1) (nC : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ {k : ℕ}, 1 ≤ k → ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧
      ∀ {J N N' : ℕ} [NeZero N] [NeZero N'], 2 * (J + 6) * M ≤ N → 2 * (J + 6) * M ≤ N' →
      ∀ {f : L1Torus d N → L1Torus d N'},
      (∀ x μ, f x μ = (((x μ).val : ℕ) : ZMod N')) →
      ∀ {e : MacIdx d N M → MacIdx d N' M},
      (∀ z i, (z i : ℕ) ≤ J + 4 → ((e z i : Fin (macK N' M)) : ℕ) = z i) →
      ∀ {C : Finset (MacIdx d N M)}, C.card ≤ nC →
      (∀ z ∈ C, ∀ i, 4 ≤ (z i : ℕ) ∧ (z i : ℕ) ≤ J) →
      ∀ {v a : ℝ}, 0 ≤ v → v ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v →
      ∀ {t : ℝ}, 0 ≤ t →
      ∀ {E : Matrix (L1Torus d N) (L1Torus d N) ℂ} {E' : Matrix (L1Torus d N') (L1Torus d N') ℂ},
      WSmall rE η E → WSmall rE η E' → ∀ {εE : ℝ}, 0 ≤ εE →
      (∀ x ∈ macRegion d N M C, ∀ y ∈ macRegion d N M C, ‖E x y - E' (f x) (f y)‖ ≤ εE) →
      ∀ {ρ ρ' : ℝ}, Real.exp κ < ρ → Real.exp κ < ρ' →
      ∀ {ell : (MacIdx d N M → ℂ) → ℂ} {ell' : (MacIdx d N' M → ℂ) → ℂ},
      AnalyticOnNhd ℂ ell (Metric.ball 0 ρ) → AnalyticOnNhd ℂ ell' (Metric.ball 0 ρ') →
      ell 0 = 0 → ell' 0 = 0 →
      (∀ s ∈ Metric.ball (0 : MacIdx d N M → ℂ) ρ,
        (1 - taggedMat Finset.univ (macTags d N M)
          (fun z => boxR (finalOp d L N k v a) (macBoxF d N M z)
              (fun u => ((macChi d N M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N k v a) (macBoxF d N M z) t)) s).det =
          Complex.exp (ell s)) →
      (∀ s ∈ Metric.ball (0 : MacIdx d N' M → ℂ) ρ',
        (1 - taggedMat Finset.univ (macTags d N' M)
          (fun z => boxR (finalOp d L N' k v a) (macBoxF d N' M z)
              (fun u => ((macChi d N' M z u : ℝ) : ℂ)) t -
            E' * (Matrix.diagonal (fun u => ((macChi d N' M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N' k v a) (macBoxF d N' M z) t)) s).det =
          Complex.exp (ell' s)) →
      ‖coef ell C - coef ell' (C.image e)‖ ≤
        P * (C₀ * Real.exp (-c₀ * (((min N N' : ℕ) : ℝ) / 2 - (((J + 3) * M : ℕ) : ℝ))) + εE) /
          (Real.exp κ - 1) ^ C.card := by
  obtain ⟨P, hP0, hcore⟩ := final_coef_logdet_close_twoTorus_of_entries (L := L) hd hM hκ hMB hMκ
    hrE hη0 hη nC
  refine ⟨P, hP0, ?_⟩
  intro k hk
  obtain ⟨C₀, c₀, hC₀, hc₀, hmain⟩ := final_region_entry_close (d := d) (L := L) (k := k) hd
  exact ⟨C₀, c₀, hC₀, hc₀, hcore hk hC₀ hc₀ (fun hv0 hv1 ha1 ha2 _ => hmain hv0 hv1 ha1 ha2)⟩

end LogDet

end Balaban.Green
