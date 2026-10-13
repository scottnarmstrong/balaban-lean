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

open Classical in
/-- **The active seed `A_X` of the old boundary term.**  The bases `u` of the top cells (side
`L^{k+1+m₀+m₁}`) of the cover torus that meet the cast of `X_f ∩ Om_f ∩ ΩK_f`: the fine set of the
domain `X ⊆ 𝕋_k`, of the region `Om ⊆ 𝕋_k` of its size and of the new region `ΩK ⊆ 𝕋_{k+1}`.
A cell is *meeting*, not contained in, the region (the contained cells of side `L^{k+1+m₀+m₁}`
are the bases of top cells inside `ΩK_f`; every meeting cell is also active, see
`d7ActiveSeed_active`). -/
noncomputable def d7ActiveSeed (F : FineSizeFrame S n M (k + 1) m₀ m₁) (c : ℕ) [NeZero c]
    (hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))
    (Om : Set (Torus S.d (n k))) (ΩK : Set (Torus S.d (n (k + 1))))
    (X : Finset (Torus S.d (n k))) :
    Finset (Localization.CTorus S.d S.L (c * n (k + 1)) m₁ (k + 1)) :=
  Finset.univ.filter fun u => Aligned (cellSide S.L m₀ m₁ (k + 1)) u ∧
    (topCell m₀ (k + 1, u) ∩ d7ToCover F c hside ''
      (d7Pull F k (X : Set (Torus S.d (n k))) ∩ d7Pull F k Om ∩ d7Pull F (k + 1) ΩK)).Nonempty

theorem mem_d7ActiveSeed {F : FineSizeFrame S n M (k + 1) m₀ m₁} {c : ℕ} [NeZero c]
    {hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1)}
    {Om : Set (Torus S.d (n k))} {ΩK : Set (Torus S.d (n (k + 1)))}
    {X : Finset (Torus S.d (n k))} {u : Localization.CTorus S.d S.L (c * n (k + 1)) m₁ (k + 1)} :
    u ∈ d7ActiveSeed F c hside Om ΩK X ↔ Aligned (cellSide S.L m₀ m₁ (k + 1)) u ∧
      ∃ s, s ∈ d7Pull F k (X : Set (Torus S.d (n k))) ∩ d7Pull F k Om ∩ d7Pull F (k + 1) ΩK ∧
        d7ToCover F c hside s ∈ topCell m₀ (k + 1, u) := by
  classical
  unfold d7ActiveSeed
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨y, hy1, s, hs, rfl⟩
    exact ⟨s, hs, hy1⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨_, h, s, hs, rfl⟩

/-- The new region of the D7 history is the region of the region step, by definition. -/
theorem omegaCube_succ_eq {R : ℕ → ℝ} {k0 K : ℕ} (H : RegionHistory S n R k0 K) (j : ℕ) :
    Def7.OmegaCube H (j + 1) = (H.step j).Omega := rfl

/-- **T2 (active region cast).**  Under the identification `hΩ` of the region `ΩK` (e.g.
`Def7.OmegaCube H (k+1)`) with the region `st.Omega` of the region step of the P6 pair
(VMOD-33 `OPEN-P6-REGION-CAST`), and the side identity `hside` of the two tori, every cell of the
active seed satisfies the activity hypothesis of `p6_root_patch_count`. -/
theorem d7ActiveSeed_active {M1 c n0 : ℕ} [NeZero c] [NeZero M1] {Rprev Rk : ℝ}
    (F : FineSizeFrame S n M (k + 1) m₀ m₁)
    (hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))
    (hM1 : M1 = S.L ^ m₁) (st : RegionStep S.d S.L n0 (n (k + 1)) Rprev Rk)
    {Om : Set (Torus S.d (n k))} {ΩK : Set (Torus S.d (n (k + 1)))}
    {X : Finset (Torus S.d (n k))} (hΩ : ΩK = st.Omega)
    {u : Localization.CTorus S.d S.L (c * n (k + 1)) m₁ (k + 1)}
    (hu : u ∈ d7ActiveSeed F c hside Om ΩK X) :
    LargeField.torusCast (by rw [p6_side hM1] : (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1) =
        M1 * (c * n (k + 1)) * S.L ^ (k + 1)) u ∈ fineK1 M1 c (n (k + 1)) S.L k st.Omega := by
  have hc : c = S.L ^ m₀ := (hside_iff F c).1 hside
  have hcM : c * M1 = M := by rw [hc, hM1, F.hM, pow_add]
  obtain ⟨-, s, hs, hyT⟩ := mem_d7ActiveSeed.1 hu
  have hmem : cubeMap n S.L M (k + 1) (k + 1) (castT F.side s) ∈ ΩK := hs.2
  rw [mem_fineK1, blockMap_torusCast]
  have hN : S.L ^ m₀ ∣ c * n (k + 1) := hc ▸ Dvd.intro _ rfl
  have ha0 : 0 < cellSide S.L m₀ m₁ (k + 1) := cellSide_pos m₀ m₁ _
  have hadvd := cellSide_dvd (L := S.L) (K := k + 1) (m₁ := m₁) hN le_rfl
  have hs' : cellSide S.L m₀ m₁ (k + 1) ∣ S.L ^ (k + 1) * (c * M1) := by
    rw [hcM, F.hM]
    unfold cellSide
    rw [show k + 1 + m₀ + m₁ = (k + 1) + (m₀ + m₁) by ring, pow_add]
  have e1 := blockMap_eq_of_mem_box (m := n (k + 1)) ha0 hadvd hs' hyT
  rw [← e1, hcM]
  unfold d7ToCover
  rw [blockMap_castT]
  have h2 : blockMap (S.L ^ (k + 1) * M) (n (k + 1)) (castT F.side s) ∈ ΩK := hmem
  rw [blockMap_castT] at h2
  rw [← hΩ]
  exact h2

/-! ### The count -/

/-- **T3 (the count).**  `|A_X| ≤ c₁ (1 + Δ_X)`, `c₁ = [3 (2 L - 1)]^d` (`Fluctuation.c1`) and
`Δ_X = d7SizeAt F k Om X` the fine modular size of the valid boundary domain `X` at the region
`Om`.  Distinct top cells are disjoint, and each one meeting `X_f ∩ Om_f` contains a cell of side
`L^{k+m₀+m₁}` inside it (the fine sets are unions of such cells), so `|A_X| ≤ n_π(X_f ∩ Om_f)` and
the landed `Fluctuation.G1_cellCount` applies. -/
theorem d7ActiveSeed_card_le {c : ℕ} [NeZero c] (F : FineSizeFrame S n M (k + 1) m₀ m₁)
    (hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))
    {Om : Set (Torus S.d (n k))} (ΩK : Set (Torus S.d (n (k + 1))))
    {X : Finset (Torus S.d (n k))} (hv : FineValidAt F k Om X) :
    ((d7ActiveSeed F c hside Om ΩK X).card : ℝ) ≤
      Fluctuation.c1 S.d S.L * (1 + d7SizeAt F k Om X) := by
  classical
  have hc : c = S.L ^ m₀ := (hside_iff F c).1 hside
  have hN := F.divN₁
  have hN' : S.L ^ m₀ ∣ c * n (k + 1) := hc ▸ Dvd.intro _ rfl
  set a := cellSide S.L m₀ m₁ k with ha
  set A1 := cellSide S.L m₀ m₁ (k + 1) with hA1
  have ha0 : 0 < a := cellSide_pos m₀ m₁ k
  have hA10 : 0 < A1 := cellSide_pos m₀ m₁ _
  have haA : a ∣ A1 := ⟨S.L, by rw [ha, hA1]; unfold cellSide; rw [show k + 1 + m₀ + m₁ = (k + m₀ + m₁) + 1 by ring, pow_succ]⟩
  have haM : a = S.L ^ k * M := by rw [ha, F.hM, ← pow_add]; unfold cellSide; congr 1; ring
  have hadvd : a ∣ (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) := cellSide_dvd hN (Nat.le_succ k)
  have hA1dvd : A1 ∣ ((c * n (k + 1)) * S.L ^ m₁) * S.L ^ (k + 1) :=
    cellSide_dvd (L := S.L) (K := k + 1) (m₁ := m₁) hN' le_rfl
  -- fine sets are unions of cells of side `a`
  have hinv : ∀ (Y : Set (Torus S.d (n k))) (s w : Localization.CTorus S.d S.L F.N₁ m₁ (k + 1)),
      s ∈ d7Pull F k Y → w ∈ Localization.box (cbase a s) a → w ∈ d7Pull F k Y := by
    intro Y s w hs hw
    have h1 := blockMap_eq_of_mem_box (m := n k) ha0 hadvd (show a ∣ S.L ^ k * M from haM ▸ dvd_refl (S.L ^ k * M)) hw
    rw [mem_d7Pull] at hs ⊢
    unfold cubeMap at hs ⊢
    rw [blockMap_castT] at hs ⊢
    rw [h1]; exact hs
  have hex : ∀ u ∈ d7ActiveSeed F c hside Om ΩK X, ∃ s, s ∈ d7Pull F k (X : Set (Torus S.d (n k))) ∩
      d7Pull F k Om ∩ d7Pull F (k + 1) ΩK ∧ d7ToCover F c hside s ∈ topCell m₀ (k + 1, u) :=
    fun u hu => (mem_d7ActiveSeed.1 hu).2
  choose! g hg using hex
  have hrec : ∀ u ∈ d7ActiveSeed F c hside Om ΩK X,
      cbase A1 (d7ToCover F c hside (g u)) = u := by
    intro u hu
    have hal := (mem_d7ActiveSeed.1 hu).1
    have hT := (hg u hu).2
    unfold topCell at hT
    simp only at hT
    rw [cbase_self_of_aligned hA1dvd hal hA10] at hT
    exact cbase_eq_of_mem_box hA1dvd hal hT
  have key : (d7ActiveSeed F c hside Om ΩK X).card ≤
      cellCount a (d7Pull F k (X : Set (Torus S.d (n k))) ∩ d7Pull F k Om) := by
    unfold cellCount
    refine Finset.card_le_card_of_injOn (fun u => cbase a (g u)) ?_ ?_
    · intro u hu
      have hgu := (hg u hu).1
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      refine ⟨aligned_cbase _, fun w hw => ⟨hinv _ _ _ hgu.1.1 hw, hinv _ _ _ hgu.1.2 hw⟩⟩
    · intro u hu v hv huv
      have hu' : u ∈ d7ActiveSeed F c hside Om ΩK X := hu
      have hv' : v ∈ d7ActiveSeed F c hside Om ΩK X := hv
      have h1 : ∀ w ∈ d7ActiveSeed F c hside Om ΩK X,
          w = cbase A1 (d7ToCover F c hside (cbase a (g w))) := by
        intro w hw
        unfold d7ToCover
        rw [castT_cbase, cbase_cbase_of_dvd haA ha0]
        exact (hrec w hw).symm
      rw [h1 u hu', h1 v hv']
      simp only at huv
      rw [huv]
  have hcount := Fluctuation.G1_cellCount (j := k) (m₀ := m₀) hN (Nat.le_succ k) hv.1
  have hsz : Fluctuation.dcovMod m₀ k (d7Pull F k Om) (d7Pull F k (X : Set (Torus S.d (n k)))) =
      d7SizeAt F k Om X := rfl
  rw [hsz] at hcount
  exact (Nat.cast_le.2 key).trans hcount

/-- **T3, in the constant of VMOD-33 (2.2).**  `|A_X| ≤ L^d [3 (2 L - 1)]^d (1 + Δ_X)`. -/
theorem d7ActiveSeed_card_le_cA {c : ℕ} [NeZero c] (F : FineSizeFrame S n M (k + 1) m₀ m₁)
    (hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))
    {Om : Set (Torus S.d (n k))} (ΩK : Set (Torus S.d (n (k + 1))))
    {X : Finset (Torus S.d (n k))} (hv : FineValidAt F k Om X) :
    ((d7ActiveSeed F c hside Om ΩK X).card : ℝ) ≤
      ((S.L : ℝ) ^ S.d * Fluctuation.c1 S.d S.L) * (1 + d7SizeAt F k Om X) := by
  refine (d7ActiveSeed_card_le F hside ΩK hv).trans ?_
  have hL : (1 : ℝ) ≤ (S.L : ℝ) ^ S.d :=
    one_le_pow₀ (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L))
  have h0 : 0 ≤ Fluctuation.c1 S.d S.L * (1 + d7SizeAt F k Om X) := by
    unfold Fluctuation.c1 d7SizeAt
    have := ENNReal.toReal_nonneg (a := d7SizeAtE F k Om X)
    positivity
  nlinarith

/-! ### The rooted sum for the term -/

section Rooted

variable {M1 c n0 : ℕ} [NeZero c] [NeZero M1] [NeZero n0] {Rprev Rk : ℝ}

/-- **T4 (fixed-support count for the actual domain).**  The sum over the families of patches of
`F♯` rooted at the active seed `A_X` of the old boundary term of `e^{-κ₂ |C|}` is at most
`e^{h c₁} e^{h c₁ Δ_X}`, `h = -log (1 - z)`, `z = D² e^{-κ₂} < 1`, `Δ_X` the fine modular size.
Premises: the typing data of the P6 pair, the side identity `hside` of the two tori, the
identification `hΩ` of the D7 region with the region step, a valid domain `X`, and the landed
numerical premises.  Counting only: nothing is said about the coefficients. -/
theorem d7ActiveSeed_rooted_sum_le (F : FineSizeFrame S n M (k + 1) m₀ m₁)
    (hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))
    (hM1 : M1 = S.L ^ m₁) (hn : n0 = S.L * n (k + 1))
    (hρ : 3 * S.L ≤ ⌊Rprev⌋₊) (h5 : 5 ≤ c) (hm₁ : 2 ≤ m₁) (hd : S.d < 5 * S.L ^ 3 * M1)
    (st : RegionStep S.d S.L n0 (n (k + 1)) Rprev Rk)
    {Om : Set (Torus S.d (n k))} {ΩK : Set (Torus S.d (n (k + 1)))}
    {X : Finset (Torus S.d (n k))} (hΩ : ΩK = st.Omega) (hv : FineValidAt F k Om X)
    {κ₂ : ℝ} (hz : ((fsharpD S.d S.L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) < 1) :
    ∑ C ∈ rootedSets (G := mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ h5 st.Z hM1))
        (⋃ u ∈ d7ActiveSeed F c hside Om ΩK X,
          (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ h5 st.Z hM1 m₀ u : Set _)),
        Real.exp (-κ₂ * C.card)
      ≤ Real.exp (-Real.log (1 - ((fsharpD S.d S.L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) *
            Fluctuation.c1 S.d S.L) *
        Real.exp (-Real.log (1 - ((fsharpD S.d S.L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) *
            Fluctuation.c1 S.d S.L * d7SizeAt F k Om X) := by
  have hc : c = S.L ^ m₀ := (hside_iff F c).1 hside
  have hmc : S.L ^ m₀ ∣ c := hc ▸ dvd_rfl
  exact fsharp_rooted_sum_le_of_rootCount st hM1 hmc hn (Nat.pos_of_ne_zero (NeZero.ne S.L)) hρ
    h5 hm₁ hd _ (fun u hu => d7ActiveSeed_active F hside hM1 st hΩ hu) hz
    (d7ActiveSeed_card_le F hside ΩK hv)

/-- **T4, in the constant `c_A = L^d [3 (2 L - 1)]^d` of VMOD-33 (2.2).** -/
theorem d7ActiveSeed_rooted_sum_le_cA (F : FineSizeFrame S n M (k + 1) m₀ m₁)
    (hside : (F.N₁ * S.L ^ m₁) * S.L ^ (k + 1) = (c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1))
    (hM1 : M1 = S.L ^ m₁) (hn : n0 = S.L * n (k + 1))
    (hρ : 3 * S.L ≤ ⌊Rprev⌋₊) (h5 : 5 ≤ c) (hm₁ : 2 ≤ m₁) (hd : S.d < 5 * S.L ^ 3 * M1)
    (st : RegionStep S.d S.L n0 (n (k + 1)) Rprev Rk)
    {Om : Set (Torus S.d (n k))} {ΩK : Set (Torus S.d (n (k + 1)))}
    {X : Finset (Torus S.d (n k))} (hΩ : ΩK = st.Omega) (hv : FineValidAt F k Om X)
    {κ₂ : ℝ} (hz : ((fsharpD S.d S.L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) < 1) :
    ∑ C ∈ rootedSets (G := mooreGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ h5 st.Z hM1))
        (⋃ u ∈ d7ActiveSeed F c hside Om ΩK X,
          (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ h5 st.Z hM1 m₀ u : Set _)),
        Real.exp (-κ₂ * C.card)
      ≤ Real.exp (-Real.log (1 - ((fsharpD S.d S.L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) *
            ((S.L : ℝ) ^ S.d * Fluctuation.c1 S.d S.L)) *
        Real.exp (-Real.log (1 - ((fsharpD S.d S.L m₀ : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) *
            ((S.L : ℝ) ^ S.d * Fluctuation.c1 S.d S.L) * d7SizeAt F k Om X) := by
  have hc : c = S.L ^ m₀ := (hside_iff F c).1 hside
  have hmc : S.L ^ m₀ ∣ c := hc ▸ dvd_rfl
  exact fsharp_rooted_sum_le_of_rootCount st hM1 hmc hn (Nat.pos_of_ne_zero (NeZero.ne S.L)) hρ
    h5 hm₁ hd _ (fun u hu => d7ActiveSeed_active F hside hM1 st hΩ hu) hz
    (d7ActiveSeed_card_le_cA F hside ΩK hv)

end Rooted

end Tori

end Balaban.LargeField
