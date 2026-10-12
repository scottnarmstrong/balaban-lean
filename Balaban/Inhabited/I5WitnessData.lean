/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.BgSettingData
public import Balaban.Localization.TreeLengthPaper
public import Balaban.Localization.TreeLengthDiam
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The geometry of `i5_background` with non-empty data sites

Setting: `d = L = 3`, `K = 2`, the torus of side `240 · 3^{m₁} · 9`, `j = 1`, `m₀ = 0`, the
landed sets `GpD` (new, whole lattice), `GkD` (old, one `1`-block) of `BgSettingData`.

* `XD m₁` is the union of the cubes of side `3 · cellSide 1 = ℓ` at the points of the chosen
  family `KX m₁` (the `ℓ`-aligned points within `ℓ¹` distance `328 ℓ` of the origin).
* `covSetup_data`: `CovSetup (GpD m₁ ρ) 0 1 (XD m₁) (KX m₁)`; hence `X1 (GpD m₁ ρ) 0 1 (KX m₁)` is the
  landed `X1f`.
* `layerUnion_GpD`, `hatConn_GpD`: `LayerUnion` and `HatConn` for the full-level set.
* `siteConnected_XD`: `XD m₁` is nearest-neighbour connected (path to the origin that moves one
  coordinate at a time towards `0`).
-/

@[expose] public section

namespace Balaban.Inhabited
namespace I5WitnessData

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.I5Inhabited Balaban.Inhabited.BgSettingData

/-! ### The region `X` and the cover data -/

section Cover

variable (m₁ : ℕ)

/-- The domain `X`: the union of the cubes of side `ℓ = 3 · cellSide 1` at the points of `KX`. -/
def XD : Set (T m₁) := ⋃ b ∈ KX m₁, box b (3 * cellSide 3 0 m₁ 1)

variable {m₁}

theorem three_cellSide_one (m₁ : ℕ) : 3 * cellSide 3 0 m₁ 1 = cellSide 3 0 m₁ 2 := by
  rw [cellSide_one, cellSide_two]; ring

theorem aligned_one_of_KX {b : T m₁} (hb : b ∈ KX m₁) : Aligned (cellSide 3 0 m₁ 1) b := by
  intro μ
  have h := hb.1 μ
  have hd : cellSide 3 0 m₁ 1 ∣ cellSide 3 0 m₁ 2 := ⟨3, by rw [cellSide_one, cellSide_two]; ring⟩
  rw [← Nat.mod_mod_of_dvd _ hd, h]; simp

theorem mem_XD {x : T m₁} : x ∈ XD m₁ ↔ ∃ b ∈ KX m₁, x ∈ box b (3 * cellSide 3 0 m₁ 1) := by
  simp [XD]

theorem layerUnion_GpD {ρ : ℝ} (m₀ : ℕ) : LayerUnion (GpD m₁ ρ) m₀ := by
  intro n hn1 hnK z hz
  have hn : n = 2 ∨ n = 1 := by omega
  rcases hn with rfl | rfl
  · refine ⟨cbase (cellSide 3 m₀ m₁ 2) z, aligned_cbase z,
      box_mono _ (Nat.le_mul_of_pos_left _ (by norm_num)) (mem_box_cbase (cellSide_pos m₀ m₁ 2) z), ?_⟩
    rw [GpD_layer_two]; intro x _; simp
  · exfalso
    simp [GeneratingSet.layer, GpD_Ω] at hz

/-- **`CovSetup` with the landed chosen family.**  The nest cube of `q ∈ KX` is `q` itself, a cube of
side `3ℓ ≤ 3 cellSide 2`. -/
theorem covSetup_data (m₁ : ℕ) (ρ : ℝ) : CovSetup (GpD m₁ ρ) 0 1 (XD m₁) (KX m₁) where
  hU := layerUnion_GpD 0
  hN := by simp
  hjK := by norm_num
  chosen := ⟨fun b hb => ⟨aligned_one_of_KX hb, fun z hz => mem_XD.2 ⟨b, hb, hz⟩⟩,
    fun z hz => by obtain ⟨b, hb, hzb⟩ := mem_XD.1 hz; exact ⟨b, hb, hzb⟩⟩
  nest := fun b hb => ⟨b, hb.1, box_mono _ (by
      rw [three_cellSide_one]; omega), by
    rw [GpD_layer_two]; intro x _; simp⟩

theorem hatConn_GpD {ρ : ℝ} : HatConn (GpD m₁ ρ) := by
  intro q _
  have : hatI (GpD m₁ ρ) q = hatBox q := by
    unfold hatI
    refine Finset.filter_true_of_mem fun x _ => ?_
    simp [GpD_Ω]
  rw [this]
  unfold hatBox
  refine boxSet_connected q.2 ?_
  unfold hatRad
  have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (q.1 + m₁) := one_le_pow₀ (by norm_num)
  have : (0 : ℝ) ≤ 3 * (3 : ℝ) ^ 2 * (3 : ℝ) ^ q.1 := by positivity
  push_cast
  linarith

end Cover

/-! ### Connectedness of `X` -/

section Connected

variable {m₁ : ℕ}

/-- The coordinate of `cbase` through an integer lift. -/
theorem cbase_apply_int {d n a : ℕ} [NeZero n] (hdvd : a ∣ n) (x : Torus d n) (μ : Fin d) (Z : ℤ)
    (hZ : (Z : ZMod n) = x μ) : cbase a x μ = ((a * (Z / a) : ℤ) : ZMod n) := by
  have h := congrFun (cbase_eq_sub a x) μ
  simp only [Pi.sub_apply, natT_apply] at h
  rw [h]
  have hv : (((x μ).val : ℕ) : ℤ) = Z % n := by rw [← hZ, ZMod.val_intCast]
  have hmod : ((((x μ).val % a : ℕ)) : ℤ) = Z % a := by
    rw [Int.natCast_mod, hv]
    exact Int.emod_emod_of_dvd Z (Int.natCast_dvd_natCast.2 hdvd)
  have e1 : ((((x μ).val % a : ℕ)) : ZMod n) = ((Z % a : ℤ) : ZMod n) := by
    rw [← hmod, Int.cast_natCast]
  rw [e1, ← hZ]
  have := Int.emod_add_mul_ediv Z a
  have e2 : ((a * (Z / a) : ℤ) : ZMod n) = (Z : ZMod n) - ((Z % a : ℤ) : ZMod n) := by
    rw [eq_sub_iff_add_eq, ← Int.cast_add]
    congr 1; linarith
  rw [e2]

/-- The integer predicate: the rounded-down coordinates have total size at most `328 ℓ`. -/
def Q (m₁ : ℕ) (Z : Fin 3 → ℤ) : Prop :=
  ∑ μ, ((cellSide 3 0 m₁ 2 : ℤ) * (Z μ / (cellSide 3 0 m₁ 2 : ℤ))).natAbs ≤ 328 * cellSide 3 0 m₁ 2

theorem side_eq_240 (m₁ : ℕ) : 240 * 3 ^ m₁ * 3 ^ 2 = 240 * cellSide 3 0 m₁ 2 := by
  rw [cellSide_two]; ring

theorem cellSide_dvd (m₁ : ℕ) : cellSide 3 0 m₁ 2 ∣ 240 * 3 ^ m₁ * 3 ^ 2 :=
  ⟨240, by rw [side_eq_240]; ring⟩

theorem Q_mem {Z : Fin 3 → ℤ} (hQ : Q m₁ Z) : (intTorus Z : T m₁) ∈ XD m₁ := by
  set b : T m₁ := cbase (cellSide 3 0 m₁ 2) (intTorus Z) with hb
  refine mem_XD.2 ⟨b, ⟨aligned_cbase _, ?_⟩, ?_⟩
  · have hd : Green.torusDist 3 (240 * 3 ^ m₁ * 3 ^ 2) b 0 ≤
        ((∑ μ, ((cellSide 3 0 m₁ 2 : ℤ) * (Z μ / (cellSide 3 0 m₁ 2 : ℤ))).natAbs : ℕ) : ℝ) := by
      unfold Green.torusDist
      push_cast
      refine Finset.sum_le_sum fun μ _ => ?_
      have := Green.natAbs_cycRep_le_of_cast (b μ - (0 : T m₁) μ)
        ((cellSide 3 0 m₁ 2 : ℤ) * (Z μ / (cellSide 3 0 m₁ 2 : ℤ))) (by
          simp only [Pi.zero_apply, sub_zero]
          exact (cbase_apply_int (cellSide_dvd m₁) _ μ (Z μ) rfl).symm)
      exact_mod_cast this
    have : ((∑ μ, ((cellSide 3 0 m₁ 2 : ℤ) * (Z μ / (cellSide 3 0 m₁ 2 : ℤ))).natAbs : ℕ) : ℝ) ≤
        328 * (cellSide 3 0 m₁ 2 : ℝ) := by exact_mod_cast hQ
    linarith
  · rw [three_cellSide_one]
    exact mem_box_cbase (cellSide_pos 0 m₁ 2) _

/-- Per coordinate: the rounded-down lift of the minimal representative is no larger than the
minimal representative of the rounded-down point. -/
theorem natAbs_round_le {ℓ n : ℕ} (hn : n = 240 * ℓ) (hℓ : 0 < ℓ) [NeZero n] (a : ZMod n) :
    (((ℓ : ℤ) * (Green.cycRep a / (ℓ : ℤ))).natAbs) ≤
      (Green.cycRep (((ℓ : ℤ) * (Green.cycRep a / (ℓ : ℤ)) : ℤ) : ZMod n)).natAbs := by
  subst hn
  have hℓz : (0 : ℤ) < ℓ := by exact_mod_cast hℓ
  have half : ∀ b : ZMod (240 * ℓ), (Green.cycRep b).natAbs ≤ 120 * ℓ := by
    intro b
    have := ZMod.val_lt b
    unfold Green.cycRep; split_ifs with h <;> omega
  set Z := Green.cycRep a with hZ
  set g : ℤ := (ℓ : ℤ) * (Z / (ℓ : ℤ)) with hg
  set e := Green.cycRep (g : ZMod (240 * ℓ)) with he
  have hZb : -(120 * ℓ : ℤ) ≤ Z ∧ Z ≤ 120 * ℓ := by
    have := half a; omega
  have hq1 : Z / (ℓ : ℤ) ≤ 120 := by
    have := Int.ediv_le_ediv hℓz hZb.2
    rwa [Int.mul_ediv_cancel _ hℓz.ne'] at this
  have hq2 : -120 ≤ Z / (ℓ : ℤ) := by
    have := Int.ediv_le_ediv hℓz hZb.1
    rwa [show -(120 * (ℓ : ℤ)) = (-120) * ℓ by ring, Int.mul_ediv_cancel _ hℓz.ne'] at this
  have hgb : -(120 * ℓ : ℤ) ≤ g ∧ g ≤ 120 * ℓ := by
    constructor <;> nlinarith
  have heb : -(120 * ℓ : ℤ) ≤ e ∧ e ≤ 120 * ℓ := by
    have := half (g : ZMod (240 * ℓ)); omega
  have hcast : ((e : ℤ) : ZMod (240 * ℓ)) = (g : ZMod (240 * ℓ)) := Green.cast_cycRep _
  have hdvd : ((240 * ℓ : ℕ) : ℤ) ∣ g - e := (ZMod.intCast_eq_intCast_iff_dvd_sub e g _).1 hcast
  obtain ⟨k, hk⟩ := hdvd
  push_cast at hk
  have hk1 : k ≤ 1 := by
    by_contra h; push Not at h; nlinarith [hgb.1, heb.2]
  have hk2 : -1 ≤ k := by
    by_contra h; push Not at h; nlinarith [hgb.2, heb.1]
  have : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl | rfl <;> omega

theorem exists_Q {x : T m₁} (hx : x ∈ XD m₁) : ∃ Z : Fin 3 → ℤ, (intTorus Z : T m₁) = x ∧ Q m₁ Z := by
  obtain ⟨b, hbK, hxb⟩ := mem_XD.1 hx
  rw [three_cellSide_one] at hxb
  have hcb : cbase (cellSide 3 0 m₁ 2) x = b :=
    cbase_eq_of_mem_box (cellSide_dvd m₁) hbK.1 hxb
  refine ⟨fun μ => Green.cycRep (x μ), ?_, ?_⟩
  · funext μ; simp [intTorus_apply, Green.cast_cycRep]
  · have hdist := hbK.2
    unfold Q
    have h1 : ∀ μ, ((cellSide 3 0 m₁ 2 : ℤ) * (Green.cycRep (x μ) / (cellSide 3 0 m₁ 2 : ℤ))).natAbs ≤
        (Green.cycRep (b μ - (0 : T m₁) μ)).natAbs := by
      intro μ
      have hbμ : b μ = (((cellSide 3 0 m₁ 2 : ℤ) * (Green.cycRep (x μ) / (cellSide 3 0 m₁ 2 : ℤ)) : ℤ) :
          ZMod (240 * 3 ^ m₁ * 3 ^ 2)) := by
        rw [← hcb]
        exact cbase_apply_int (cellSide_dvd m₁) x μ _ (Green.cast_cycRep _)
      simp only [Pi.zero_apply, sub_zero]
      rw [hbμ]
      exact natAbs_round_le (side_eq_240 m₁) (cellSide_pos 0 m₁ 2) (x μ)
    have h2 : ((∑ μ, ((cellSide 3 0 m₁ 2 : ℤ) * (Green.cycRep (x μ) / (cellSide 3 0 m₁ 2 : ℤ))).natAbs : ℕ) : ℝ) ≤
        Green.torusDist 3 (240 * 3 ^ m₁ * 3 ^ 2) b 0 := by
      unfold Green.torusDist
      push_cast
      exact Finset.sum_le_sum fun μ _ => by exact_mod_cast h1 μ
    have : ((∑ μ, ((cellSide 3 0 m₁ 2 : ℤ) * (Green.cycRep (x μ) / (cellSide 3 0 m₁ 2 : ℤ))).natAbs : ℕ) : ℝ) ≤
        328 * (cellSide 3 0 m₁ 2 : ℝ) := h2.trans hdist
    exact_mod_cast this

theorem round_step (ℓ : ℤ) (hℓ : 0 < ℓ) (Z δ : ℤ) (h : (0 < Z ∧ δ = -1) ∨ (Z < 0 ∧ δ = 1)) :
    (ℓ * ((Z + δ) / ℓ)).natAbs ≤ (ℓ * (Z / ℓ)).natAbs := by
  rcases h with ⟨hZ, rfl⟩ | ⟨hZ, rfl⟩
  · have h0 : 0 ≤ (Z + -1) / ℓ := Int.ediv_nonneg (by omega) hℓ.le
    have h1 : (Z + -1) / ℓ ≤ Z / ℓ := Int.ediv_le_ediv hℓ (by omega)
    have h2 : ℓ * ((Z + -1) / ℓ) ≤ ℓ * (Z / ℓ) := Int.mul_le_mul_of_nonneg_left h1 hℓ.le
    have h3 : 0 ≤ ℓ * ((Z + -1) / ℓ) := Int.mul_nonneg hℓ.le h0
    omega
  · have h0 : (Z + 1) / ℓ ≤ 0 := by
      have := Int.ediv_le_ediv hℓ (show Z + 1 ≤ 0 by omega)
      simpa using this
    have h1 : Z / ℓ ≤ (Z + 1) / ℓ := Int.ediv_le_ediv hℓ (by omega)
    have h2 : ℓ * (Z / ℓ) ≤ ℓ * ((Z + 1) / ℓ) := Int.mul_le_mul_of_nonneg_left h1 hℓ.le
    have h3 : ℓ * ((Z + 1) / ℓ) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos hℓ.le h0
    omega

theorem path_to_zero : ∀ n : ℕ, ∀ Z : Fin 3 → ℤ, Q m₁ Z → ∑ μ, (Z μ).natAbs = n →
    Relation.ReflTransGen (fun u v : T m₁ => u ∈ XD m₁ ∧ v ∈ XD m₁ ∧ Nbr u v)
      (intTorus Z) 0 := by
  intro n
  induction n with
  | zero =>
    intro Z _ hs
    have : Z = 0 := by
      funext μ
      have := (Finset.sum_eq_zero_iff.1 hs) μ (Finset.mem_univ μ)
      simpa using this
    subst this
    have : (intTorus (0 : Fin 3 → ℤ) : T m₁) = 0 := by funext μ; simp [intTorus_apply]
    rw [this]
  | succ n ih =>
    intro Z hQ hs
    obtain ⟨μ, -, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (by omega : ∑ μ, (Z μ).natAbs ≠ 0)
    have hne : Z μ ≠ 0 := by intro h; apply hμ; simp [h]
    have hℓ : (0 : ℤ) < (cellSide 3 0 m₁ 2 : ℤ) := by exact_mod_cast cellSide_pos 0 m₁ 2
    obtain ⟨δ, hδ, hδ'⟩ : ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧
        ((0 < Z μ ∧ δ = -1) ∨ (Z μ < 0 ∧ δ = 1)) := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨1, Or.inl rfl, Or.inr ⟨hlt, rfl⟩⟩
      · exact ⟨-1, Or.inr rfl, Or.inl ⟨hgt, rfl⟩⟩
    set Z' : Fin 3 → ℤ := Z + Pi.single μ δ with hZ'
    have hZ'μ : Z' μ = Z μ + δ := by simp [hZ']
    have hZ'ν : ∀ ν, ν ≠ μ → Z' ν = Z ν := fun ν hν => by simp [hZ', hν]
    have hQ' : Q m₁ Z' := by
      unfold Q at hQ ⊢
      refine le_trans (Finset.sum_le_sum fun ν _ => ?_) hQ
      by_cases hν : ν = μ
      · subst hν; rw [hZ'μ]; exact round_step _ hℓ _ _ hδ'
      · rw [hZ'ν ν hν]
    have hsum : ∑ ν, (Z' ν).natAbs = n := by
      have e1 := Finset.sum_erase_add Finset.univ (fun ν => (Z ν).natAbs) (Finset.mem_univ μ)
      have e2 := Finset.sum_erase_add Finset.univ (fun ν => (Z' ν).natAbs) (Finset.mem_univ μ)
      have e3 : ∑ ν ∈ Finset.univ.erase μ, (Z' ν).natAbs = ∑ ν ∈ Finset.univ.erase μ, (Z ν).natAbs :=
        Finset.sum_congr rfl fun ν hν => by rw [hZ'ν ν (Finset.ne_of_mem_erase hν)]
      rw [hZ'μ] at e2
      omega
    refine Relation.ReflTransGen.head ?_ (ih Z' hQ' hsum)
    refine ⟨Q_mem hQ, Q_mem hQ', ?_⟩
    rcases hδ with rfl | rfl
    · refine ⟨μ, Or.inl ?_⟩
      rw [hZ', ← intTorus_add_aux]
      congr 1
      simp [intTorus_single_aux]
    · refine ⟨μ, Or.inr ?_⟩
      rw [hZ', ← intTorus_add_aux]
      have : (intTorus (Pi.single μ (-1 : ℤ)) : T m₁) = -Pi.single μ 1 := by
        funext ν
        by_cases hν : ν = μ <;> simp [intTorus_apply, hν]
      rw [add_assoc, this, neg_add_cancel, add_zero]

/-- **`X` is nearest-neighbour connected.** -/
theorem siteConnected_XD (m₁ : ℕ) : SiteConnected (XD m₁) := by
  intro x hx y hy
  obtain ⟨Z, rfl, hZ⟩ := exists_Q hx
  obtain ⟨Y, rfl, hY⟩ := exists_Q hy
  have h1 := path_to_zero _ Z hZ rfl
  have h2 := path_to_zero _ Y hY rfl
  have : Std.Symm (fun u v : T m₁ => u ∈ XD m₁ ∧ v ∈ XD m₁ ∧ Nbr u v) :=
    ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  exact h1.trans (Std.Symm.symm _ _ h2)

end Connected

end I5WitnessData
end Balaban.Inhabited
