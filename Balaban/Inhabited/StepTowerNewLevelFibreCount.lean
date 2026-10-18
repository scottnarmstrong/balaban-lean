/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelSum
public import Balaban.Polymer.GasCoreSize

/-!
# The entropy-weighted count of the cube sets with a given hull (`StepTowerNewLevelFibreCount`)

For a polymer `Y` of index `m₀ ≥ 1` the weighted sum
`∑_{T′ : hull T′ = Y} e^{-ρ d_Ext T′}` over cube sets `T′` of index one is at most
`γ (1 + d_{m₀}(Y)) (K₀ + 1) · e^{-(ρ - r)(d_{m₀}(Y)/α - 1)}`, `r = a_ent + 1`,
`γ = (L^{m₀-1})^d c₁`, `α = 1 + L^{2d} c₁ · 4 d L`, as soon as `ρ ≥ r`.  Every set of the fibre
contains one of the at most `γ (1 + d_{m₀}(Y))` cubes of index one inside `Y`
(`card_fibre_cubes_le`); the connected-set entropy `sum_exp_core_le` pays `e^{-r d_Ext}` for the
sets through a given cube, and `d_Ext T′ ≥ d_{m₀}(Y)/α - 1` pays the rest.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

section Count

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

open Classical in
/-- **The cubes of index one inside a polymer.**  For a polymer `Y` of index `m₀ ≥ 1`, at most
`γ (1 + d_{m₀}(Y))` cubes of index one lie inside `Y`, `γ = (L^{m₀-1})^d c₁`. -/
theorem card_cubesIn_le (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀)
    {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) :
    (((Finset.univ.filter fun β : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ => box β.1 (cellSide L 1 m₁ K) ⊆ Y)).card : ℝ) ≤
      (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L *
        (1 + sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hN1 : L ^ 1 ∣ N₁ := (pow_dvd_pow L hM).trans hN
  have hDj : IsDj m₀ K Y := isDj_of_isPolyDom hY
  have hQc : ((Finset.univ.filter fun β : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ => box β.1 (cellSide L 1 m₁ K) ⊆ Y)).card ≤
      cellCount (cellSide L 1 m₁ K) Y := by
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
  have h1 : (((Finset.univ.filter fun β : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ => box β.1 (cellSide L 1 m₁ K) ⊆ Y)).card : ℝ) ≤
      cellCount (cellSide L 1 m₁ K) Y := by exact_mod_cast hQc
  have h2 := mul_le_mul_of_nonneg_left hcM (Nat.cast_nonneg (α := ℝ) ((L ^ (m₀ - 1)) ^ d))
  have : sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y = treeLenCovOne m₀ K Y := rfl
  rw [this]
  linarith

open Classical in
/-- Every cube set of index one with hull `Y ∋ y` contains a cube of index one inside `Y`. -/
theorem exists_mem_cubesIn_of_hull (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)} {y}
    (hy : y ∈ Y)
    {T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ)}
    (hT : sitesOf (piHull m₀ (sitesOf T)) = Y) :
    ∃ β ∈ T, β ∈ (Finset.univ.filter fun β : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ => box β.1 (cellSide L 1 m₁ K) ⊆ Y) := by
  rw [← hT, sitesOf_piHull hN] at hy
  obtain ⟨b, ⟨_, s, _, hs⟩, _⟩ := Set.mem_iUnion₂.1 hy
  obtain ⟨β, hβ, _⟩ := mem_sitesOf.1 hs
  refine ⟨β, hβ, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun x hx => ?_⟩⟩
  rw [← hT]
  exact subset_sitesOf_piHull hN _ (mem_sitesOf.2 ⟨β, hβ, hx⟩)

open Classical in
/-- **The entropy-weighted count of the cube sets with a given hull map.**  Let `h` assign to each
set `T′` of cubes of index one a site set `h T′` that contains the cubes of `T′`, is nonempty only
for nonempty `T′`, and has size `d_{m₀}(h T′) ≤ α (1 + d_Ext T′)` whenever it is a polymer of
index `m₀`.  For a polymer `Y` of index `m₀ ≥ 1`, a point `y ∈ Y` and `a_ent + 1 ≤ ρ`,
`∑_{T′} [h T′ = Y] e^{-ρ d_Ext T′} ≤ γ (1 + d_{m₀}(Y)) (K₀ + 1) e^{-(ρ - r)(d_{m₀}(Y)/α - 1)}`
with `r = a_ent + 1`, `γ = (L^{m₀-1})^d c₁`. -/
theorem weighted_fibre_le_of_hull (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀)
    (h : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ) → Set (CTorus d L N₁ m₁ K)) {α : ℝ} (hα1 : 1 ≤ α)
    (hcont : ∀ T, ∀ β ∈ T, box β.1 (cellSide L 1 m₁ K) ⊆ h T)
    (hne : ∀ T y, y ∈ h T → T.Nonempty)
    (hsize : ∀ T, IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (h T) →
      sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (h T) ≤ α * (1 + dExt T))
    {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) {y : CTorus d L N₁ m₁ K}
    (hy : y ∈ Y) {ρ : ℝ} (hρ : aEnt d L + 1 ≤ ρ) :
    ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ))),
      (if h T = Y then Real.exp (-ρ * dExt T) else 0) ≤
      (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L *
        (1 + sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) * (K0 d L (aEnt d L + 1) + 1) *
      Real.exp (-(ρ - (aEnt d L + 1)) *
        (sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y / α - 1)) := by
  have hc1 := one_le_c1 d L
  have hαpos : 0 < α := by linarith
  set r : ℝ := aEnt d L + 1 with hr
  set s := sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y with hs
  set W : ℝ := Real.exp (-(ρ - r) * (s / α - 1)) with hW
  have hW0 : 0 ≤ W := (Real.exp_pos _).le
  have hpt : ∀ T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ),
      (if h T = Y then Real.exp (-ρ * dExt T) else 0) ≤
        ∑ β ∈ (Finset.univ.filter fun β : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ => box β.1 (cellSide L 1 m₁ K) ⊆ Y),
          (if β ∈ T then W * Real.exp (-r * dExt T) else 0) := by
    intro T
    split_ifs with hTY
    · obtain ⟨β, hβT⟩ := hne T y (by rw [hTY]; exact hy)
      have hβ : β ∈ (Finset.univ.filter fun β : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ => box β.1 (cellSide L 1 m₁ K) ⊆ Y) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hTY ▸ hcont T β hβT⟩
      have hY' : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K (h T) := by
        rw [hTY]; exact hY
      have h1 := hsize T hY'
      rw [hTY] at h1
      have h2 : s / α - 1 ≤ dExt T := by
        rw [sub_le_iff_le_add, div_le_iff₀ hαpos]
        nlinarith
      have h3 : Real.exp (-ρ * dExt T) ≤ W * Real.exp (-r * dExt T) := by
        rw [hW, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        nlinarith
      have h4 : W * Real.exp (-r * dExt T) ≤
          ∑ β ∈ (Finset.univ.filter fun β : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ => box β.1 (cellSide L 1 m₁ K) ⊆ Y),
            (if β ∈ T then W * Real.exp (-r * dExt T) else 0) := by
        refine le_trans ?_ (Finset.single_le_sum (f := fun β =>
          (if β ∈ T then W * Real.exp (-r * dExt T) else 0)) (fun _ _ => by
            split_ifs
            · positivity
            · exact le_rfl) hβ)
        simp [hβT]
      exact h3.trans h4
    · exact Finset.sum_nonneg fun β _ => by split_ifs <;> positivity
  have hent : ∀ β : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ,
      ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ))), (if β ∈ T then W * Real.exp (-r * dExt T) else 0) ≤
        W * (K0 d L r + 1) := by
    intro β
    have h := sum_exp_core_le (m₀ := 1) (j := K) (Ω := Set.univ) (m₁ := m₁) (K := K)
      (Yt := Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ))
      ((pow_dvd_pow L hM).trans hN) le_rfl (fun T => T) (m := 1) (κ := r)
      (fun T => by
        have : (Finset.univ.filter fun y : Finset (CubeB (d := d) (L := L) (N₁ := N₁)
          (m₁ := m₁) (K := K) 1 K Set.univ) => y = T) = {T} := by ext; simp
        rw [this]; simp) (le_refl r) β
    calc _ = W * ∑ T ∈ Finset.univ.filter (fun T : Finset (CubeB (d := d) (L := L) (N₁ := N₁)
          (m₁ := m₁) (K := K) 1 K Set.univ) => β ∈ T), Real.exp (-r * dExt T) := by
          rw [Finset.mul_sum, Finset.sum_filter]
      _ ≤ W * (K0 d L r + 1) := mul_le_mul_of_nonneg_left (by simpa using h) hW0
  have hcard := card_cubesIn_le (m₁ := m₁) hN hM hY
  calc _ ≤ ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ))), ∑ β ∈ (Finset.univ.filter fun β : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ => box β.1 (cellSide L 1 m₁ K) ⊆ Y),
          (if β ∈ T then W * Real.exp (-r * dExt T) else 0) :=
        Finset.sum_le_sum fun T _ => hpt T
    _ = ∑ β ∈ (Finset.univ.filter fun β : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ => box β.1 (cellSide L 1 m₁ K) ⊆ Y),
        ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (K := K) 1 K Set.univ))), (if β ∈ T then W * Real.exp (-r * dExt T) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ _β ∈ (Finset.univ.filter fun β : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ => box β.1 (cellSide L 1 m₁ K) ⊆ Y),
        W * (K0 d L r + 1) := Finset.sum_le_sum fun β _ => hent β
    _ = ((Finset.univ.filter fun β : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) 1 K Set.univ => box β.1 (cellSide L 1 m₁ K) ⊆ Y)).card *
        (W * (K0 d L r + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L * (1 + s)) * (W * (K0 d L r + 1)) :=
        mul_le_mul_of_nonneg_right hcard (by
          have := K0_pos d L r
          positivity)
    _ = _ := by ring


open Classical in
/-- **The entropy-weighted count of the cube sets with hull `Y`.**  For a polymer `Y` of index
`m₀ ≥ 1`, a point `y ∈ Y` and `a_ent + 1 ≤ ρ`,
`∑_{T′} [hull T′ = Y] e^{-ρ d_Ext T′} ≤ γ (1 + d_{m₀}(Y)) (K₀ + 1) e^{-(ρ - r)(d_{m₀}(Y)/α - 1)}`
with `r = a_ent + 1`, `γ = (L^{m₀-1})^d c₁`, `α = 1 + L^{2d} c₁ · 4 d L`. -/
theorem weighted_fibre_le (hN : L ^ m₀ ∣ N₁) (hM : 1 ≤ m₀)
    {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) {y : CTorus d L N₁ m₁ K}
    (hy : y ∈ Y) {ρ : ℝ} (hρ : aEnt d L + 1 ≤ ρ) :
    ∑ T ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := K) 1 K Set.univ))),
      (if sitesOf (piHull m₀ (sitesOf T)) = Y then Real.exp (-ρ * dExt T) else 0) ≤
      (((L ^ (m₀ - 1)) ^ d : ℕ) : ℝ) * c1 d L *
        (1 + sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y) * (K0 d L (aEnt d L + 1) + 1) *
      Real.exp (-(ρ - (aEnt d L + 1)) *
        (sizeJ (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) m₀ K Y /
          (1 + ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L)) - 1)) := by
  have hc1 := one_le_c1 d L
  have hq : (0 : ℝ) ≤ ((L ^ d * L ^ d : ℕ) : ℝ) * c1 d L * (4 * d * L) := by positivity
  refine weighted_fibre_le_of_hull hN hM (fun T => sitesOf (piHull m₀ (sitesOf T)))
    (by linarith) (fun T β hβ => ?_) (fun T y hy => ?_) (fun T hT => ?_) hY hy hρ
  · exact (fun x hx => subset_sitesOf_piHull hN _ (mem_sitesOf.2 ⟨β, hβ, hx⟩))
  · obtain ⟨β, hβ, _⟩ := exists_mem_cubesIn_of_hull hN hy rfl
    exact ⟨β, hβ⟩
  · exact sizeJ_piHull_le_dExt hN hM T hT

end Count

end Balaban.Inhabited
