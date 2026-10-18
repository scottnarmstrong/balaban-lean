/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSumSize
public import Balaban.Inhabited.StepTowerNewLabels

/-!
# The per-centre sum of the label bounds of the new level (`StepTowerNewLevelSum`)

The premise `hsum` of `localClass_newLevel_of_expansion_cast`: for a polymer `Y` of index `m₀` and
a centre `y`, the sum over the cube sets `T′` of index one whose `π′`-hull of index `m₀` is `Y`
of the label bounds `b(blockIndex y, T′)` is at most `E₀ e^{-κ sizeJ Y}`.

* `card_fibre_le`: the number of cube sets of index one with hull `Y` is at most
  `exp (γ (1 + d_{m₀}(Y)) log 2)`, `γ = (L^{m₀-1})^d c₁`: such a set consists of cubes of index one
  inside `Y`, which are at most `(L^{m₀-1})^d` times as many as the cubes of index `m₀` of `Y`
  (`cellCount_le_pow_mul_cellCount`), and these at most `c₁ (1 + d_{m₀}(Y))`.
* `sizeJ_piHull_le_dExt` (`StepTowerNewLevelSumSize.lean`): `d_{m₀}(Y) ≤ α (1 + dExt T′)` for every
  `T′` of the fibre, `α = 1 + L^{2d} c₁ · 4 d L`.
* `newLabels_hsum_of_bound`: if `b(z, T′) ≤ B e^{-ρ dExt T′}`, the rate `ρ` satisfies
  `κ + γ log 2 ≤ ρ / α` and `E₀ ≥ B e^{γ log 2 + ρ}`, then `hsum` holds with `E₀` and `κ`.
* `newLabels_hsum_of_chain_bound`: the same for the two-term bound of the class chain
  (`e0CoeffFamily_class_exists_tower_struct_step`), `b ≤ A₁ e^{-ρ₁ dExt} + A₂ e^{-ρ₂ dExt}`, with
  `ρ = min (ρ₁, ρ₂)`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

section Sum

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

open Classical in
/-- **The number of cube sets of index one with a given hull.**  For a polymer `Y` of index
`m₀ ≥ 1`, at most `exp (γ (1 + d_{m₀}(Y)) log 2)` sets `T′` of cubes of index one have
`π′`-hull `Y`, with `γ = (L^{m₀-1})^d c₁`. -/
theorem card_fibre_le (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀)
    {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) :
    (((Finset.univ.filter fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ) => sitesOf (piHull m₀ (sitesOf T)) = Y).card : ℕ) : ℝ) ≤
      Real.exp ((((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L *
        (1 + sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) * Real.log 2) := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hN1 : L ^ 1 ∣ N₁ := (pow_dvd_pow L hM).trans hN
  have hDj : IsDj m₀ K Y := isDj_of_isPolyDom hY
  set Q : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ) :=
    Finset.univ.filter fun β => box β.1 (cellSide L 1 m₁ K) ⊆ Y with hQ
  have hsub : (Finset.univ.filter fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (K := K) 1 K Set.univ) => sitesOf (piHull m₀ (sitesOf T)) = Y) ⊆
      Q.powerset := by
    intro T hT
    have hT' := (Finset.mem_filter.1 hT).2
    rw [Finset.mem_powerset]
    intro β hβ
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x hx => ?_⟩
    rw [← hT']
    exact subset_sitesOf_piHull hN _ (mem_sitesOf.2 ⟨β, hβ, hx⟩)
  have hcard : (Finset.univ.filter fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (K := K) 1 K Set.univ) => sitesOf (piHull m₀ (sitesOf T)) = Y).card ≤
      2 ^ Q.card := by
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_powerset]
  have hQc : Q.card ≤ cellCount (cellSide L 1 m₁ K) Y := by
    unfold cellCount
    refine Finset.card_le_card_of_injOn (fun b => b.1) (fun b hb => ?_)
      (fun a _ b _ h => Subtype.ext h)
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, b.2.1, (Finset.mem_filter.1 hb).2⟩
  have haM : cellSide L m₀ m₁ K = L ^ (m₀ - 1) * cellSide L 1 m₁ K := by
    unfold cellSide; rw [← pow_add]; congr 1; omega
  have hYc : ∀ y ∈ Y, box (cbase (L ^ (m₀ - 1) * cellSide L 1 m₁ K) y)
      (L ^ (m₀ - 1) * cellSide L 1 m₁ K) ⊆ Y := by
    rw [← haM]
    exact isDj_cells_subset hN le_rfl hDj
  have hcc := cellCount_le_pow_mul_cellCount (cellSide_dvd hN1 le_rfl) (cellSide_pos 1 m₁ K)
    (pow_pos hL0 (m₀ - 1)) hYc
  rw [← haM] at hcc
  have hccR : (cellCount (cellSide L 1 m₁ K) Y : ℝ) ≤
      (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * (cellCount (cellSide L m₀ m₁ K) Y : ℝ) := by
    exact_mod_cast hcc
  have hcM := cellCount_le_one_add_treeLenCovOne hN le_rfl hDj
  have hQR : (Q.card : ℝ) ≤ (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L *
      (1 + sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) := by
    have h1 : (Q.card : ℝ) ≤ cellCount (cellSide L 1 m₁ K) Y := by exact_mod_cast hQc
    have h2 := mul_le_mul_of_nonneg_left hcM (Nat.cast_nonneg (α := ℝ) ((L ^ (m₀ - 1)) ^ d))
    have : sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y = treeLenCovOne m₀ K Y := rfl
    rw [this]
    linarith
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc (_ : ℝ) ≤ ((2 ^ Q.card : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = Real.exp (Q.card * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]; push_cast; rfl
    _ ≤ _ := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hQR hlog)

open Classical in
/-- **`hsum` of the new-level theorem for the labels of the class chain, from a one-term bound.**
Let `b(z, T′) ≤ B e^{-ρ dExt T′}` (`0 ≤ B`, `0 ≤ ρ`) and let `EbE T′ y Y` be `b(blockIndex y, T′)`
if the `π′`-hull of index `m₀ ≥ 1` of `sitesOf T′` is `Y` and `0` otherwise.  If the rate satisfies
`κ + γ log 2 ≤ ρ / α` and `B e^{γ log 2 + ρ} ≤ E₀`, with `γ = (L^{m₀-1})^d c₁` and
`α = 1 + L^{2d} c₁ · 4 d L`, then for every polymer `Y` of index `m₀` and every centre
`∑_{T′} EbE T′ y Y ≤ E₀ e^{-κ d_{m₀}(Y)}`. -/
theorem newLabels_hsum_of_bound (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀)
    (b : RootIdx d L N₁ m₁ K → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := K) 1 K Set.univ) → ℝ)
    (EbE : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ) →
      CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) → ℝ)
    (hEbE : ∀ T y Y, EbE T y Y =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then b (blockIndex y) T else 0)
    {B ρ κ E₀ : ℝ} (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hb : ∀ z T, b z T ≤ B * Real.exp (-ρ * dExt T))
    (hrate : κ + (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L * Real.log 2 ≤
      ρ / (1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L)))
    (hE₀ : B * Real.exp ((((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L * Real.log 2 + ρ) ≤ E₀) :
    ∀ y (Y : Set (CTorus d L N₁ m₁ K)),
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y → y ∈ Y →
      ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ))), EbE T y Y ≤
        E₀ * Real.exp (-κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) := by
  intro y Y hY _
  have hc1 := one_le_c1 d L
  set α : ℝ := 1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L) with hα
  set γ : ℝ := (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L with hγ
  have hα1 : 1 ≤ α := by
    have : (0 : ℝ) ≤ ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L) := by positivity
    linarith
  have hαpos : 0 < α := by linarith
  set s := sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y with hs
  have hs0 : 0 ≤ s := treeLenCovOne_nonneg m₀ K Y
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hU : ∀ T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ),
      EbE T y Y ≤ if sitesOf (piHull m₀ (sitesOf T)) = Y then
        B * Real.exp (-ρ * (s / α - 1)) else 0 := by
    intro T
    rw [hEbE]
    split_ifs with h
    · have hY' : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K
          (sitesOf (piHull m₀ (sitesOf T))) := by rw [h]; exact hY
      have h1 := sizeJ_piHull_le_dExt hN hM T hY'
      rw [h] at h1
      have h2 : s / α - 1 ≤ dExt T := by
        rw [sub_le_iff_le_add, div_le_iff₀ hαpos]
        nlinarith
      refine (hb _ T).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB
      nlinarith
    · exact le_rfl
  have hcard := card_fibre_le (m₁ := m₁) hN hM hY
  have hUnn : 0 ≤ B * Real.exp (-ρ * (s / α - 1)) := by positivity
  calc ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ))), EbE T y Y
      ≤ ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ))), (if sitesOf (piHull m₀ (sitesOf T)) = Y then
          B * Real.exp (-ρ * (s / α - 1)) else 0) := Finset.sum_le_sum fun T _ => hU T
    _ = _ := by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (γ * (1 + s) * Real.log 2) * (B * Real.exp (-ρ * (s / α - 1))) :=
        mul_le_mul_of_nonneg_right hcard hUnn
    _ = B * Real.exp ((γ * Real.log 2 + ρ) + (γ * Real.log 2 - ρ / α) * s) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
    _ ≤ B * Real.exp ((γ * Real.log 2 + ρ) + -κ * s) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB
        nlinarith
    _ = (B * Real.exp (γ * Real.log 2 + ρ)) * Real.exp (-κ * s) := by
        rw [Real.exp_add]; ring
    _ ≤ E₀ * Real.exp (-κ * s) :=
        mul_le_mul_of_nonneg_right hE₀ (Real.exp_pos _).le

open Classical in
/-- **`hsum` for the two-term bound of the class chain.**  The coefficients of
`e0CoeffFamily_class_exists_tower_struct_step` satisfy
`‖e θ T′‖ ≤ A₁ e^{-ρ₁ dExt T′} + A₂ e^{-ρ₂ dExt T′}`; for `b` bounded by this expression and
`0 ≤ ρ ≤ min (ρ₁, ρ₂)` the premise `hsum` of `localClass_newLevel_of_expansion_cast` holds with
`𝒯E = Finset.univ`, the labels' bounds `EbE` and
`κ + γ log 2 ≤ ρ / α`, `(A₁ + A₂) e^{γ log 2 + ρ} ≤ E₀` (constants of
`newLabels_hsum_of_bound`). -/
theorem newLabels_hsum_of_chain_bound (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀)
    (b : RootIdx d L N₁ m₁ K → Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := K) 1 K Set.univ) → ℝ)
    (EbE : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ) →
      CTorus d L N₁ m₁ K → Set (CTorus d L N₁ m₁ K) → ℝ)
    (hEbE : ∀ T y Y, EbE T y Y =
      if sitesOf (piHull m₀ (sitesOf T)) = Y then b (blockIndex y) T else 0)
    {A₁ A₂ ρ₁ ρ₂ ρ κ E₀ : ℝ} (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hρ : 0 ≤ ρ)
    (hρ₁ : ρ ≤ ρ₁) (hρ₂ : ρ ≤ ρ₂)
    (hb : ∀ z T, b z T ≤ A₁ * Real.exp (-ρ₁ * dExt T) + A₂ * Real.exp (-ρ₂ * dExt T))
    (hrate : κ + (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L * Real.log 2 ≤
      ρ / (1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L)))
    (hE₀ : (A₁ + A₂) * Real.exp ((((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L * Real.log 2 + ρ) ≤ E₀) :
    ∀ y (Y : Set (CTorus d L N₁ m₁ K)),
      IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y → y ∈ Y →
      ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ))), EbE T y Y ≤
        E₀ * Real.exp (-κ * sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) := by
  refine newLabels_hsum_of_bound hN hM b EbE hEbE (B := A₁ + A₂) (add_nonneg hA₁ hA₂) hρ
    (fun z T => ?_) hrate hE₀
  have hd := dExt_nonneg T
  have e1 : Real.exp (-ρ₁ * dExt T) ≤ Real.exp (-ρ * dExt T) :=
    Real.exp_le_exp.2 (by nlinarith)
  have e2 : Real.exp (-ρ₂ * dExt T) ≤ Real.exp (-ρ * dExt T) :=
    Real.exp_le_exp.2 (by nlinarith)
  refine (hb z T).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left e1 hA₁, mul_le_mul_of_nonneg_left e2 hA₂]

end Sum

end Balaban.Inhabited
