/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6FsharpRootedCount
public import Balaban.LargeField.Def7FineSize
public import Balaban.Fluctuation.SizeModG1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The active top cells of the old boundary term of P6 (VMOD-34 §4, package 2)

Geometry and counting only.  That a non-zero coefficient of the P6 interpolation has all its
components rooted at active top cells (active-only coefficient support,
`OPEN-P6-ACTIVE-COEF-ROOT`) is NOT proved here; it is open and is the subject of a question to the
author.

## The two tori

Fix a scale `k`, the frame `F : FineSizeFrame S n M (k+1) m₀ m₁` of the fine size (`Def7FineSize`)
and the cover torus `CTorus d L (c * n (k+1)) m₁ (k+1)` of the P6 pair.  The fine torus of the
frame is `CTorus d L F.N₁ m₁ (k+1)`, of side `(F.N₁ L^{m₁}) L^{k+1} = M n_{k+1} L^{k+1}`.  They are
the same torus up to a cast exactly when `(F.N₁ L^{m₁}) L^{k+1} = (c n_{k+1}) L^{m₁} L^{k+1}`
(`hside`, an explicit premise: the identification is never a definitional equality).  Since
`F.N₁ = L^{m₀} n_{k+1}` this holds iff `c = L^{m₀}` (`hside_iff`); the numerical premise
`L^{m₀} ∣ c` of the landed cover lemmas is then automatic.

* `d7ToCover`: the cast (`castT`) of the fine torus of the frame onto the cover torus.  It maps
  boxes to boxes, aligned sites to aligned sites, and the top cell of a site to the top cell of its
  image (`d7ToCover_topCell`).

## The seed of the term

For a set `X` of cubes of `𝕋_k` (a boundary domain of the D7 class), a region `Om ⊆ 𝕋_k` (the
region of the size) and the new region `ΩK ⊆ 𝕋_{k+1}`, the *active seed* `d7ActiveSeed` is the set
of bases `u` of top cells (cells of side `L^{k+1+m₀+m₁}`) of the cover torus that meet the cast of
`X_f ∩ Om_f ∩ ΩK_f`, where `X_f`, `Om_f`, `ΩK_f` are the fine sets (`d7Pull`).  The top cells are
indexed by their bases, so that distinct elements are distinct cells.  When `Ω_{k+1} ⊆ Ω_k` the
intersection with `Om_f` is redundant and the seed is the set of top cells meeting
`X_f ∩ Ω_{k+1,f}`; the inclusion is not used.

The region identification `hΩ : ΩK = st.Omega` (VMOD-33 `OPEN-P6-REGION-CAST`) identifies the new
region of the D7 history (`Def7.OmegaCube H (k+1)`, which is `(H.step k).Omega` by definition,
`omegaCube_succ_eq`) with the region `Ω_{k+1}` of the region step of the P6 pair.  It is the raw
(pre-`R`) region, not `omegaPost`.

* `d7ActiveSeed_active`: every cell of the seed satisfies the activity hypothesis of
  `p6_root_patch_count`.
* `d7ActiveSeed_card_le`: `|seed| ≤ c₁ (1 + Δ_X)`, `c₁ = [3 (2 L - 1)]^d` and `Δ_X` the fine
  modular size; since distinct top cells are disjoint and each contains a cell of side
  `L^{k+m₀+m₁}` inside `X_f ∩ Om_f`, no factor `L^d` is lost, and a fortiori
  `|seed| ≤ L^d c₁ (1 + Δ_X)` (VMOD-33 (2.2)).
* `d7ActiveSeed_rooted_sum_le`: the fixed-support count for the actual domain.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer Balaban.LargeField.Def7

set_option linter.unusedSectionVars false

/-! ### Casts of tori of equal side -/

section Cast

variable {d : ℕ} {ℓ ℓ' : ℕ}

theorem castT_natT (h : ℓ = ℓ') (w : Fin d → ℕ) :
    castT h (natT w : Torus d ℓ) = natT w := by subst h; rfl

/-- The cast maps the box of side `s` at `b` onto the box of side `s` at the cast of `b`. -/
theorem castT_image_box (h : ℓ = ℓ') (b : Torus d ℓ) (s : ℕ) :
    castT h '' Localization.box b s = Localization.box (castT h b) s := by
  subst h; ext x; simp [castT]

theorem castT_cbase (h : ℓ = ℓ') (a : ℕ) (x : Torus d ℓ) :
    castT h (cbase a x) = cbase a (castT h x) := by subst h; rfl

theorem castT_aligned (h : ℓ = ℓ') (a : ℕ) {b : Torus d ℓ} (hb : Aligned a b) :
    Aligned a (castT h b) := fun μ => by rw [castT_val]; exact hb μ

theorem blockMap_castT (h : ℓ = ℓ') (N m : ℕ) (x : Torus d ℓ) :
    blockMap N m (castT h x) = blockMap N m x := by subst h; rfl

theorem cbase_cbase_of_dvd [NeZero ℓ] {a A : ℕ} (hA : a ∣ A) (ha : 0 < a) (x : Torus d ℓ) :
    cbase A (cbase a x) = cbase A x := by
  obtain ⟨q, rfl⟩ := hA
  funext μ
  have hlt : a * ((x μ).val / a) < ℓ :=
    lt_of_le_of_lt (Nat.mul_div_le _ _) (ZMod.val_lt _)
  have hv : ((cbase a x) μ).val = a * ((x μ).val / a) := by
    simp only [cbase]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  show (((a * q * ((cbase a x μ).val / (a * q)) : ℕ)) : ZMod ℓ) = _
  rw [hv, Nat.mul_div_mul_left _ _ ha, Nat.div_div_eq_div_mul]
  rfl

theorem cbase_self_of_aligned [NeZero ℓ] {a : ℕ} (ha : a ∣ ℓ) {b : Torus d ℓ} (hb : Aligned a b)
    (ha0 : 0 < a) : cbase a b = b :=
  cbase_eq_of_mem_box ha hb (mem_box_self b ha0)

end Cast

/-! ### The two tori -/

section Tori

variable {S : Setting} {n : ℕ → ℕ} {M m₀ m₁ k : ℕ}

/-- **The cast of the fine torus of the frame onto the cover torus** of the P6 pair
(`CTorus d L (c * n (k+1)) m₁ (k+1)`), under the explicit premise `hside` that the two side
lengths agree. -/
def d7ToCover (F : FineSizeFrame S n M (k + 1) m₀ m₁) (c : ℕ)
    (hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))
    (x : Localization.CTorus S.d S.L F.N₁ m₁ (k + 1)) : Localization.CTorus S.d S.L (c * n (k + 1)) m₁ (k + 1) :=
  castT hside x

variable [NeZero S.L] [∀ j, NeZero (n j)]

/-- The side identity is equivalent to `c = L ^ m₀`. -/
theorem hside_iff (F : FineSizeFrame S n M (k + 1) m₀ m₁) (c : ℕ) :
    (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1) ↔
      c = S.L ^ m₀ := by
  have hL : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hn : 0 < n (k + 1) := Nat.pos_of_ne_zero (NeZero.ne _)
  rw [F.N₁_eq]
  constructor
  · intro h
    have h1 := Nat.eq_of_mul_eq_mul_right (pow_pos hL _) h
    have h2 := Nat.eq_of_mul_eq_mul_right (pow_pos hL _) h1
    exact (Nat.eq_of_mul_eq_mul_right hn h2).symm
  · rintro rfl; rfl

/-- **The side identity holds for the standard frame when `c = L ^ m₀`** (satisfiability of the
premise `hside`: the frame `fineFrame` of any torus with `M = L ^ (m₀ + m₁)`). -/
theorem fineFrame_hside (hM : M = S.L ^ (m₀ + m₁)) :
    ((fineFrame S n (k + 1) (m₀ := m₀) (m₁ := m₁) hM).N₁ * S.L ^ m₁) * S.L ^ (k + 1) =
      (S.L ^ m₀ * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1) := rfl

theorem d7ToCover_injective (F : FineSizeFrame S n M (k + 1) m₀ m₁) (c : ℕ)
    (hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1)) :
    Function.Injective (d7ToCover F c hside) := castT_injective hside

/-- An aligned cell of side `a` maps onto the aligned cell of side `a` at the image of its base. -/
theorem d7ToCover_image_box (F : FineSizeFrame S n M (k + 1) m₀ m₁) (c : ℕ)
    (hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))
    (b : Localization.CTorus S.d S.L F.N₁ m₁ (k + 1)) (a : ℕ) :
    d7ToCover F c hside '' Localization.box b a = Localization.box (d7ToCover F c hside b) a :=
  castT_image_box hside b a

/-- The cast preserves alignment. -/
theorem d7ToCover_aligned (F : FineSizeFrame S n M (k + 1) m₀ m₁) (c : ℕ)
    (hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))
    {b : Localization.CTorus S.d S.L F.N₁ m₁ (k + 1)} (a : ℕ) (hb : Aligned a b) :
    Aligned a (d7ToCover F c hside b) := castT_aligned hside a hb

/-- **The top cell of a site is carried to the top cell of its image.** -/
theorem d7ToCover_topCell (F : FineSizeFrame S n M (k + 1) m₀ m₁) (c : ℕ)
    (hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))
    (u : Localization.CTorus S.d S.L F.N₁ m₁ (k + 1)) :
    d7ToCover F c hside '' topCell m₀ (k + 1, u) =
      topCell m₀ (k + 1, d7ToCover F c hside u) := by
  unfold topCell
  rw [d7ToCover_image_box]
  unfold d7ToCover
  rw [castT_cbase]

end Tori

end Balaban.LargeField
