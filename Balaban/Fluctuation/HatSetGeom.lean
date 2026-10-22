/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityIrrelSuppSet
public import Balaban.Localization.TreeLengthDiam

/-!
# The geometry of the set `X̂` of ruling R13 (`HatSetGeom`)

`X̂ = hatSet m₀ j X` is `X` thickened by `⌊L/2⌋` cells of `𝒟_j` (`GsSpecHat`).

* `exists_cube_of_mem_hatBox`: every site of a box `Localization.box (b, (2⌊L/2⌋ + 1) c)` with an aligned base
  lies in a `π'_j`-cube inside the box;
* `cell_subset_hatSet`: `X̂` is a union of cells of `𝒟_j`;
* `exists_near_of_mem_hatSet`: every site of `X̂` is within the sup distance `⌊L/2⌋ c` of a site of
  `X`, for `X` a union of cells;
* `mem_hatSet_of_supDist_le`: a site within one cell of `X` lies in `X̂`;
* `union_cubeAt_subset_hatSet`: the cover `X ∪ □(y)` of a label `(j, y, X)` lies in `X̂`;
* `settings_family_castLocalB_hat`: the per-label settings with each term composed on the cast
  local set `𝔹_{j_τ}(X̂_τ)` of its polymer (ruling R13), the cover `XL τ ⊆ X̂_τ` unchanged.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ}

/-- **A site of a box of side `(2⌊L/2⌋ + 1) c` lies in a `π'_j`-cube (side `L c`) inside the box**,
for an aligned base and `c ∣` the side of the torus. -/
theorem exists_cube_of_mem_hatBox {c : ℕ} (hc : c ∣ (N₁ * L ^ m₁) * L ^ k)
    {b z : CTorus d L N₁ m₁ k} (hb : Aligned c b) (hz : z ∈ Localization.box b ((2 * (L / 2) + 1) * c)) :
    ∃ b', Aligned c b' ∧ z ∈ Localization.box b' (L * c) ∧ Localization.box b' (L * c) ⊆ Localization.box b ((2 * (L / 2) + 1) * c) := by
  obtain ⟨w, hw, rfl⟩ := hz
  have hL2 : 2 * (L / 2) + 1 ≤ L + 1 := by omega
  set t : Fin d → ℕ := fun μ => if w μ < L * c then 0 else c with ht
  have htw : ∀ μ, t μ ≤ w μ := fun μ => by
    simp only [ht]
    split_ifs with h
    · exact Nat.zero_le _
    · have : c ≤ L * c := Nat.le_mul_of_pos_left c (Nat.pos_of_ne_zero (NeZero.ne L))
      generalize L * c = B at *
      omega
  have htc : ∀ μ, t μ % c = 0 := fun μ => by
    simp only [ht]; split_ifs <;> simp
  have hwt : ∀ μ, w μ - t μ < L * c := fun μ => by
    have h1 := hw μ
    simp only [ht]
    split_ifs with h
    · simpa using h
    · have h4 : w μ < L * c + c :=
        lt_of_lt_of_le h1 ((Nat.mul_le_mul_right _ hL2).trans (le_of_eq (by ring)))
      have h5 : c ≤ w μ :=
        le_trans (Nat.le_mul_of_pos_left c (Nat.pos_of_ne_zero (NeZero.ne L))) (not_lt.1 h)
      generalize L * c = B at h4 ⊢
      omega
  have htw' : ∀ μ, t μ = c → L * c ≤ w μ := fun μ h => by
    by_contra hlt
    push Not at hlt
    have : t μ = 0 := by simp [ht, hlt]
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · exfalso
        have := hw μ
        rw [h0, mul_zero] at this
        exact Nat.not_lt_zero _ this
      · exact h0
    omega
  refine ⟨b + natT t, aligned_add_natT hc hb htc, ⟨w - t, hwt, ?_⟩, ?_⟩
  · rw [add_assoc, ← natT_add]
    congr 2
    funext μ
    simp only [Pi.add_apply, Pi.sub_apply]
    exact (Nat.add_sub_cancel' (htw μ)).symm
  · rintro z ⟨r, hr, rfl⟩
    refine ⟨t + r, fun μ => ?_, by rw [natT_add, add_assoc]⟩
    simp only [Pi.add_apply]
    by_cases h : w μ < L * c
    · have : t μ = 0 := by simp [ht, h]
      rw [this, zero_add]
      exact lt_of_lt_of_le (hr μ) (Nat.mul_le_mul_right _ (by omega))
    · have htμ : t μ = c := by simp [ht, h]
      have h1 := hw μ
      have h2 : L * c < (2 * (L / 2) + 1) * c := lt_of_le_of_lt (not_lt.1 h) h1
      have h3 : L < 2 * (L / 2) + 1 := lt_of_mul_lt_mul_right h2 (Nat.zero_le c)
      have h4 : 2 * (L / 2) + 1 = L + 1 := by omega
      rw [htμ, h4]
      have := hr μ
      have e : (L + 1) * c = c + L * c := by ring
      omega

/-- **`X̂` is a union of cells of `𝒟_j`.** -/
theorem cell_subset_hatSet (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k) (X : Set (CTorus d L N₁ m₁ k)) :
    ∀ z ∈ hatSet m₀ j X, Localization.box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) ⊆
      hatSet m₀ j X := by
  rintro z ⟨y, hy, hz⟩
  have hdvd := cellSide_dvd (K := k) (m₁ := m₁) (L := L) (N₁ := N₁) hN hjk
  obtain ⟨b', hb', hzb', hsub⟩ := exists_cube_of_mem_hatBox hdvd
    (aligned_cubeAt_base (m₀ := m₀) hN hjk y) hz
  exact (cell_subset_cube hdvd (cellSide_pos m₀ m₁ j) hb' hzb').trans
    (hsub.trans fun w hw => ⟨y, hy, hw⟩)

/-- **Every site of `X̂` is within `⌊L/2⌋` cells of `X`** (sup distance `≤ ⌊L/2⌋ c`), for `X` a
union of cells of `𝒟_j`. -/
theorem exists_near_of_mem_hatSet {X : Set (CTorus d L N₁ m₁ k)}
    (hcell : ∀ z ∈ X, Localization.box (cbase (cellSide L m₀ m₁ j) z) (cellSide L m₀ m₁ j) ⊆ X) :
    ∀ z ∈ hatSet m₀ j X, ∃ w ∈ X, supDist z w ≤ L / 2 * cellSide L m₀ m₁ j := by
  rintro z ⟨y, hy, ⟨v, hv, rfl⟩⟩
  set c := cellSide L m₀ m₁ j with hcdef
  have hc0 : 0 < c := cellSide_pos m₀ m₁ j
  set h := L / 2 with hh
  -- the nearest site of the cell of `y`
  set u : Fin d → ℕ := fun μ => min (max (v μ) (h * c)) (h * c + c - 1) with hu
  have hu1 : ∀ μ, h * c ≤ u μ := fun μ => by
    simp only [hu]; refine le_min (le_max_right _ _) (by omega)
  have hu2 : ∀ μ, u μ - h * c < c := fun μ => by
    have : u μ ≤ h * c + c - 1 := min_le_right _ _
    omega
  have hcell_y : cbase c y + natT (fun μ => u μ - h * c) ∈ X :=
    hcell y hy ⟨fun μ => u μ - h * c, hu2, rfl⟩
  refine ⟨cbase c y + natT (fun μ => u μ - h * c), hcell_y, ?_⟩
  have e : (cbase c y - natT fun _ => h * c) + natT u = cbase c y + natT (fun μ => u μ - h * c) := by
    have : u = (fun _ => h * c) + fun μ => u μ - h * c := by
      funext μ; simp only [Pi.add_apply]; exact (Nat.add_sub_cancel' (hu1 μ)).symm
    rw [this, natT_add]
    simp only [Pi.add_apply, Nat.add_sub_cancel_left]
    abel
  rw [← e, supDist_le_iff]
  intro μ
  rw [cycNorm_le_iff]
  refine ⟨(v μ : ℤ) - u μ, ?_, by simp⟩
  have h1 := hv μ
  have h2 : u μ = min (max (v μ) (h * c)) (h * c + c - 1) := rfl
  rw [abs_le]
  have e2 : (2 * h + 1) * c = 2 * (h * c) + c := by ring
  constructor
  · -- `v ≥ u - h c`
    rcases le_total (v μ) (h * c) with hvh | hvh
    · have : u μ = h * c := by
        rw [h2, max_eq_right hvh]; exact min_eq_left (by omega)
      rw [this]
      push_cast
      have : (0 : ℤ) ≤ v μ := by positivity
      nlinarith
    · have : u μ ≤ v μ := by rw [h2, max_eq_left hvh]; exact min_le_left _ _
      have : ((u μ : ℕ) : ℤ) ≤ v μ := by exact_mod_cast this
      have : (0 : ℤ) ≤ (h * c : ℕ) := by positivity
      push_cast at *
      linarith
  · -- `v ≤ u + h c`
    have hle : v μ ≤ u μ + h * c := by
      rcases le_total (v μ) (h * c + c - 1) with hv2 | hv2
      · have : u μ = max (v μ) (h * c) := by rw [h2]; exact min_eq_left (max_le hv2 (by omega))
        rw [this]
        have := le_max_left (v μ) (h * c)
        omega
      · have : u μ = h * c + c - 1 := by
          rw [h2]; exact min_eq_right (le_max_of_le_left hv2)
        rw [this]
        rw [e2] at h1
        omega
    have : ((v μ : ℕ) : ℤ) ≤ ((u μ + h * c : ℕ) : ℤ) := by exact_mod_cast hle
    push_cast at this ⊢
    linarith

/-- **A site within one cell of `X` lies in `X̂`** (`L ≥ 2`, so that `X̂` reaches one cell beyond
`X`): if `supDist z x₀ ≤ c`, `x₀ ∈ X`, `c = cellSide`, then `z ∈ X̂`. -/
theorem mem_hatSet_of_supDist_le (hL : 2 ≤ L) {X : Set (CTorus d L N₁ m₁ k)}
    {x₀ z : CTorus d L N₁ m₁ k} (hx₀ : x₀ ∈ X) (hz : supDist z x₀ ≤ cellSide L m₀ m₁ j) :
    z ∈ hatSet m₀ j X := by
  set c := cellSide L m₀ m₁ j with hcdef
  set h := L / 2 with hh
  have hh1 : 1 ≤ h := by omega
  refine ⟨x₀, hx₀, ?_⟩
  -- the offset of `z` from the base of the box
  have hd := supDist_le_iff.1 hz
  choose t ht htz using fun μ => (cycNorm_le_iff (z μ - x₀ μ) c).1 (hd μ)
  set r : Fin d → ℕ := fun μ => (x₀ μ).val % c with hr
  have hc0 : 0 < c := cellSide_pos m₀ m₁ j
  have hrc : ∀ μ, r μ < c := fun μ => Nat.mod_lt _ hc0
  -- `w = r + h c + t ∈ [0, (2h+1) c)`
  have hw0 : ∀ μ, 0 ≤ (r μ : ℤ) + h * c + t μ := fun μ => by
    have h1 := (abs_le.1 (ht μ)).1
    have h2 : (c : ℤ) ≤ h * c := by exact_mod_cast Nat.le_mul_of_pos_left c (by omega)
    have h3 : (0 : ℤ) ≤ r μ := by positivity
    linarith
  refine ⟨fun μ => ((r μ : ℤ) + h * c + t μ).toNat, fun μ => ?_, ?_⟩
  · have h1 := (abs_le.1 (ht μ)).2
    have h2 := hrc μ
    have : ((r μ : ℤ) + h * c + t μ) < ((2 * h + 1) * c : ℕ) := by
      push_cast
      have : (r μ : ℤ) < c := by exact_mod_cast h2
      nlinarith
    rw [← Int.ofNat_lt, Int.toNat_of_nonneg (hw0 μ)]
    exact_mod_cast this
  · funext μ
    have hzμ : z μ = x₀ μ + (t μ : ZMod _) := by rw [htz μ]; ring
    rw [hzμ]
    have e1 : x₀ μ = (cbase c x₀) μ + ((r μ : ℕ) : ZMod _) := by
      have := congrFun (cbase_eq_sub c x₀) μ
      simp only [Pi.sub_apply, natT] at this
      rw [this]; simp [hr]
    simp only [Pi.add_apply, Pi.sub_apply, natT]
    rw [e1]
    have e2 : (((((r μ : ℤ) + h * c + t μ).toNat : ℕ)) : ZMod ((N₁ * L ^ m₁) * L ^ k)) =
        ((r μ : ℤ) + h * c + t μ : ℤ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hw0 μ)]
    rw [e2]
    push_cast
    ring

/-- **The cover `X ∪ □(y)` of a label `(j, y, X)` lies in `X̂`.** -/
theorem union_cubeAt_subset_hatSet {X : Set (CTorus d L N₁ m₁ k)} {y : CTorus d L N₁ m₁ k}
    (hy : y ∈ X) :
    X ∪ Localization.box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
      (L * cellSide L m₀ m₁ j) ⊆ hatSet m₀ j X :=
  Set.union_subset (subset_hatSet m₀ j X) (cubeAt_subset_hatSet m₀ j hy)

section Family

variable {N : ℕ} {ϱ ϱ₁ ϱ₂ ϱ₀ ϱ₃ ϱm : ℝ}

/-- **The per-label settings with each term composed on `𝔹_{j_τ}(X̂_τ)`** (ruling R13): for labels
with polymers `Xp τ ∈ 𝒟_{j_τ}` and covers `Xp τ ⊆ XL τ ⊆ X̂_τ`, the instance of
`settings_family_castLocalB_far` at `X_j τ = X̂_τ`, `D_h = ⌊L/2⌋ cellSide_k`,
`c_D = ⌊L/2⌋ L^{m₀}`: the settings of the step, `GsSpecStrong j_τ (XL τ) (Gj τ)` and
`Gj τ = castG hc (𝔹_{j_τ}(X̂_τ))`, under `(5 L + 13) c₁ + ⌊L/2⌋ L^{m₀} + r₀ L ≤ (L - 2) L^{m₀+1}`. -/
theorem settings_family_castLocalB_hat_Gk {ι : Type*} {N₁' m₁' : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG' : IsLevel Gp (k + 1))
    {Gk0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₀}
    {Gj0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₃}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    {X₀' X₁f' X₁f'' : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB0 : BgSetting N Gp Gk0 Gj0 a₁ ν c BG κ r₀ eps δ₃ X₀' X₁f' j₁)
    (hF0 : FlSetting N Gp Gk0 Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f'')
    (hG : IsLevel Hm k) (hL : 2 ≤ L) (hN : L ^ m₀ ∣ N₁) (hm : m₁' ≤ m₀ + m₁)
    (jL : ι → ℕ) (XL 𝒦X Xp : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k) (hXp : ∀ τ, IsPolyDom m₀ (jL τ) (Xp τ))
    (hXpL : ∀ τ, Xp τ ⊆ XL τ) (hXL : ∀ τ, XL τ ⊆ hatSet m₀ (jL τ) (Xp τ))
    (hcov : ∀ τ, CovSetup Gp m₀ (jL τ) (XL τ) (𝒦X τ))
    (hϱ₁ : bgR0 d L ≤ ϱ₁) (hϱ₂ : bgR0 d L ≤ ϱ₂) (hs₁ : ϱ₁ ≤ minSep L (L ^ m₁'))
    (hs₂ : ϱ₂ ≤ minSep L (L ^ m₁')) {c₁ : ℕ} (hm1 : L ^ m₁' ≤ L ^ m₁ * c₁)
    (hm' : (((5 * L + 13) * c₁ + L / 2 * L ^ m₀ : ℕ) : ℝ) + r₀ * L ≤
      (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1)) :
    ∃ (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
      (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂)
      (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))),
      (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (jL τ) (𝒦X τ)) ∧
      (∀ τ, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (jL τ)) ∧
      (∀ τ, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ)) ∧
      (∀ (τ : ι) (h : jL τ ≤ k + 1), GsSpecStrong (jL τ) h (XL τ) (Gj τ)) ∧
      (∀ τ, Gj τ = castG hc (localB (jL τ) (Nat.le_succ_of_le (hjk τ))
        {x' : CTorus d L N₁' m₁' (k + 1) |
          (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ hatSet m₀ (jL τ) (Xp τ)} hs₂)) ∧
      ∀ τ, Gk τ = castG hc (localB k (Nat.le_succ k)
        (castNbhd (N₁' := N₁') (m₁' := m₁')
          {x' | (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ XL τ ∪ hatSet m₀ (jL τ) (Xp τ)}) hs₁) := by
  have hcs : ∀ τ, cellSide L m₀ m₁ (jL τ) ≤ cellSide L m₀ m₁ k := fun τ => by
    unfold cellSide
    exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by have := hjk τ; omega)
  refine settings_family_castLocalB_far_Gk hc hG' hB0 hF0 hG hL hN hm jL XL 𝒦X
    (fun τ => hatSet m₀ (jL τ) (Xp τ)) XL hj1 hjk
    (fun τ => cell_subset_hatSet hN (Nat.le_succ_of_le (hjk τ)) (Xp τ)) hXL
    (Dh := L / 2 * cellSide L m₀ m₁ k) (cD := L / 2 * L ^ m₀) (fun τ z hz => ?_) ?_ hcov hϱ₁ hϱ₂
    hs₁ hs₂ hm1 hm'
  · obtain ⟨w, hw, hd⟩ := exists_near_of_mem_hatSet
      (cell_subset_of_isPolyDom hN (Nat.le_succ_of_le (hjk τ)) (hXp τ)) z hz
    exact ⟨w, hXpL τ hw, hd.trans (Nat.mul_le_mul_left _ (hcs τ))⟩
  · refine le_of_eq ?_
    unfold cellSide
    rw [show k + m₀ + m₁ = (m₁ + k) + m₀ by ring, pow_add]
    ring

/-- **The per-label settings with each term composed on `𝔹_{j_τ}(X̂_τ)`** (ruling R13): for labels
with polymers `Xp τ ∈ 𝒟_{j_τ}` and covers `Xp τ ⊆ XL τ ⊆ X̂_τ`, the instance of
`settings_family_castLocalB_far` at `X_j τ = X̂_τ`, `D_h = ⌊L/2⌋ cellSide_k`,
`c_D = ⌊L/2⌋ L^{m₀}`: the settings of the step, `GsSpecStrong j_τ (XL τ) (Gj τ)` and
`Gj τ = castG hc (𝔹_{j_τ}(X̂_τ))`, under `(5 L + 13) c₁ + ⌊L/2⌋ L^{m₀} + r₀ L ≤ (L - 2) L^{m₀+1}`. -/
theorem settings_family_castLocalB_hat {ι : Type*} {N₁' m₁' : ℕ} [NeZero N₁']
    (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG' : IsLevel Gp (k + 1))
    {Gk0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₀}
    {Gj0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₃}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}
    {X₀' X₁f' X₁f'' : Finset (CTorus d L N₁ m₁ (k + 1))} {j₁ : ℕ}
    (hB0 : BgSetting N Gp Gk0 Gj0 a₁ ν c BG κ r₀ eps δ₃ X₀' X₁f' j₁)
    (hF0 : FlSetting N Gp Gk0 Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f'')
    (hG : IsLevel Hm k) (hL : 2 ≤ L) (hN : L ^ m₀ ∣ N₁) (hm : m₁' ≤ m₀ + m₁)
    (jL : ι → ℕ) (XL 𝒦X Xp : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k) (hXp : ∀ τ, IsPolyDom m₀ (jL τ) (Xp τ))
    (hXpL : ∀ τ, Xp τ ⊆ XL τ) (hXL : ∀ τ, XL τ ⊆ hatSet m₀ (jL τ) (Xp τ))
    (hcov : ∀ τ, CovSetup Gp m₀ (jL τ) (XL τ) (𝒦X τ))
    (hϱ₁ : bgR0 d L ≤ ϱ₁) (hϱ₂ : bgR0 d L ≤ ϱ₂) (hs₁ : ϱ₁ ≤ minSep L (L ^ m₁'))
    (hs₂ : ϱ₂ ≤ minSep L (L ^ m₁')) {c₁ : ℕ} (hm1 : L ^ m₁' ≤ L ^ m₁ * c₁)
    (hm' : (((5 * L + 13) * c₁ + L / 2 * L ^ m₀ : ℕ) : ℝ) + r₀ * L ≤
      (((L - 2 : ℕ)) : ℝ) * (L : ℝ) ^ (m₀ + 1)) :
    ∃ (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
      (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂)
      (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))),
      (∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ (jL τ) (𝒦X τ)) ∧
      (∀ τ, BgSetting N Gp (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ) (X₁f τ) (jL τ)) ∧
      (∀ τ, FlSetting N Gp (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ)) ∧
      (∀ (τ : ι) (h : jL τ ≤ k + 1), GsSpecStrong (jL τ) h (XL τ) (Gj τ)) ∧
      ∀ τ, Gj τ = castG hc (localB (jL τ) (Nat.le_succ_of_le (hjk τ))
        {x' : CTorus d L N₁' m₁' (k + 1) |
          (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ hatSet m₀ (jL τ) (Xp τ)} hs₂) := by
  obtain ⟨Gk, Gj, X₀, X₁f, h1, h2, h3, h4, h5, -⟩ := settings_family_castLocalB_hat_Gk hc hG' hB0 hF0
    hG hL hN hm jL XL 𝒦X Xp hj1 hjk hXp hXpL hXL hcov hϱ₁ hϱ₂ hs₁ hs₂ hm1 hm'
  exact ⟨Gk, Gj, X₀, X₁f, h1, h2, h3, h4, h5⟩

end Family

end Balaban.Fluctuation
