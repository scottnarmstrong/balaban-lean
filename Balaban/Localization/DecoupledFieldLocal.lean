/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledSolveAnalytic
public import Balaban.Localization.DecoupledGeometry
public import Balaban.Localization.BoxConn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem I-4a (e): locality of the decoupled perturbed system

* Item 0: `HatConn` (the thickened interaction cubes are nearest-neighbour connected inside `Ω₁`)
  holds for the centres of layer `≥ 2`, where `□̂_z ⊂ Ω₁` (`hatConn_of_layer_one`); it remains a
  hypothesis for the centres of layer `1`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Item0

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The thickened interaction cube of a centre of layer `≥ 2` lies in `Ω₁`. -/
theorem hatBox_subset_Omega (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) (hq2 : 2 ≤ q.1) {y : CTorus d L N₁ m₁ K} (hy : y ∈ hatBox q) :
    y ∈ G.Ω 1 := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast S.hM
  have hd1 : (0 : ℝ) ≤ d := by positivity
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ q.1 :=
    one_le_pow₀ (by linarith)
  have hlam : (L : ℝ) ^ (q.1 + m₁) = (L : ℝ) ^ q.1 * (L : ℝ) ^ m₁ := pow_add _ _ _
  have hl0 : (0 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by positivity
  have key : hatRad L m₁ q.1 + (L : ℝ) ^ (q.1 + m₁) / 2 ≤ 4 * (L : ℝ) ^ (q.1 + m₁) := by
    unfold hatRad
    have := mul_le_mul_of_nonneg_right hM' (by linarith : (0 : ℝ) ≤ (L : ℝ) ^ q.1)
    rw [hlam] at *
    nlinarith
  have hbox : InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y := by
    unfold hatBox at hy
    exact mem_boxSet.1 hy
  have hdist := torusDist_le_of_inBox hbox
  have h4 : Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) y q.2 ≤ 4 * d * (L : ℝ) ^ (q.1 + m₁) := by
    refine hdist.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left key hd1]
  have hq2Ω : q.2 ∈ G.Ω q.1 := (G.mem_layer.1 hl).1
  have := mem_pred_cube m₁ G S.cover_sep hq2 hmK hq2Ω (by
    rw [Green.torusDist_comm_gen]; exact h4)
  exact G.Ω_antitone le_rfl (by omega) (by omega) this

/-- **Item 0.**  The thickened interaction cubes of the centres of layer `≥ 2` are
nearest-neighbour connected inside `Ω₁` (they lie in `Ω₁` and are boxes); only the centres of
layer `1` need the regularity hypothesis. -/
theorem hatConn_of_layer_one (S : DGSetting G a ν)
    (h1 : ∀ q ∈ cubeIdx G, q.1 = 1 → ConnIn (hatI G q)) : HatConn G := by
  classical
  intro q hq
  by_cases hq1 : q.1 = 1
  · exact h1 q hq hq1
  · obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
    have hq2 : 2 ≤ q.1 := by omega
    have hI : hatI G q = hatBox q := by
      unfold hatI
      exact Finset.filter_true_of_mem fun y hy => hatBox_subset_Omega S hq hq2 hy
    rw [hI]
    have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
    have hLj : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := one_le_pow₀ (by linarith)
    have hR : 1 ≤ hatRad L m₁ q.1 := by
      unfold hatRad
      have : (0 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 := by positivity
      linarith
    exact boxSet_connected q.2 hR

end Item0

section Inner

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The sites of the interaction cubes of the centres of `Z_Y`. -/
noncomputable def SY (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (X₁ : Finset (CTorus d L N₁ m₁ K))
    (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)) (Y : Finset (CTorus d L N₁ m₁ K)) :
    Finset (CTorus d L N₁ m₁ K) :=
  (ZY G X₁ 𝒞 Y).biUnion intBox

theorem hact_aux {X₁ : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (u : ℕ × CTorus d L N₁ m₁ K → ℂ) (hu : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → u P = 0)
    (z : ℕ × CTorus d L N₁ m₁ K) (hz : sProd G u z ≠ 0) :
    ∀ P ∈ Qset G z, P ∈ parCubes G X₁ → P ∈ 𝒞 := by
  intro P hP hPP
  by_contra hPC
  exact (sProd_ne_zero_iff u z |>.1 hz) P hP (hu P hPP hPC)

/-- The thickened cube of a centre that only sees parameter cubes of `𝒞` lies in `V(𝒞) ∩ Ω₁`. -/
theorem hhat_aux (S : DGSetting G a ν) {X₁ : Finset (CTorus d L N₁ m₁ K)}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} (z : ℕ × CTorus d L N₁ m₁ K)
    (hP : ∀ P ∈ Qset G z, P ∈ parCubes G X₁ → P ∈ 𝒞) :
    hatI G z ⊆ (Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1 := by
  classical
  intro x hx
  unfold hatI at hx
  rw [Finset.mem_filter] at hx
  obtain ⟨hxh, hxΩ⟩ := hx
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hxΩ
  set n := G.layerIndex x with hn
  have hown := own_mem_cubeIdx S.aligned hn1 hnK hxl
  have hQ : (n, ownBase (n + m₁) x) ∈ Qset G z := by
    rw [mem_Qset]
    exact ⟨hown, x, ownBase_sameCell x, (mem_boxSet.1 hxh)⟩
  rw [Finset.mem_filter]
  refine ⟨?_, hxΩ⟩
  unfold Vset
  rw [Finset.mem_union]
  by_cases hPP : (n, ownBase (n + m₁) x) ∈ parCubes G X₁
  · right
    rw [Finset.mem_biUnion]
    exact ⟨_, hP _ hQ hPP, mem_cubeP.2 (ownBase_sameCell x)⟩
  · left
    have : cubeP (n, ownBase (n + m₁) x) ⊆ X₁ := by
      by_contra hc
      exact hPP (Finset.mem_filter.2 ⟨hown, hc⟩)
    exact this (mem_cubeP.2 (ownBase_sameCell x))

/-- The dichotomy: an active interaction cube lies inside `Y` or avoids it. -/
theorem hdich_aux (S : DGSetting G a ν) (hconn : HatConn G) {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y)
    (z : ℕ × CTorus d L N₁ m₁ K) (hz : z ∈ cubeIdx G)
    (hP : ∀ P ∈ Qset G z, P ∈ parCubes G X₁ → P ∈ 𝒞) :
    SubI G (hatBox z) Y ∨ DisjI G (hatBox z) Y := by
  classical
  rcases connIn_dichotomy (hconn z hz) (hhat_aux S z hP) hY with h | h
  · left
    intro x hx
    exact h (by
      unfold hatI
      rw [Finset.mem_filter]
      exact ⟨hx, x.2⟩)
  · right
    intro x hx hxY
    exact Finset.disjoint_left.1 h (by
      unfold hatI
      rw [Finset.mem_filter]
      exact ⟨hx, x.2⟩) hxY


theorem SY_subset {X₁ Y : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {x : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y) : (x : CTorus d L N₁ m₁ K) ∈ Y := by
  classical
  unfold SY at hx
  obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.1 hx
  exact (Finset.mem_filter.1 hz).2.2 x (box_subset_hatBox z hxz)

/-- **(DG5'), the version with data agreeing on `S_Y` only.**  Let `Y` be a union of
nearest-neighbour components of `V(𝒞) ∩ Ω₁` and `S_Y = ⋃_{z ∈ Z_Y} □_z`.  If `A = A'` and `f = f'`
on `S_Y` (and the parameters are as in `dg5'`) then `G_s(A) f = G_{s'}(A') f'` on all of `Y ∩ Ω₁`. -/
theorem dg5'_inner (S : DGSetting G a ν) (hconn : HatConn G)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y)
    {α α' : G.Ω 1 → ℂ} (hα : AdmPot G α) (hα' : AdmPot G α')
    {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal G a ν α s)) (hU' : IsUnit (1 - Kcal G a ν α' s'))
    (hs1 : ∀ P ∈ cubeIdx G, P ∉ parCubes G X₁ → s P = 1 ∧ s' P = 1)
    (hs0 : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → s P = 0 ∧ s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI G (cubeP P) Y → s P = s' P)
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → α x = α' x)
    {f f' : G.Ω 1 → ℂ}
    (hf : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → f x = f' x) :
    ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y →
      (Gs G a ν α s *ᵥ f) x = (Gs G a ν α' s' *ᵥ f') x := by
  classical
  have hact : ∀ z, (sProd G s z ≠ 0 ∨ sProd G s' z ≠ 0) →
      ∀ P ∈ Qset G z, P ∈ parCubes G X₁ → P ∈ 𝒞 := by
    intro z hz
    rcases hz with h | h
    · exact hact_aux s (fun P hP hPC => (hs0 P hP hPC).1) z h
    · exact hact_aux s' (fun P hP hPC => (hs0 P hP hPC).2) z h
  -- an active interaction cube inside `Y` has `z ∈ Z_Y`
  have hbase : ∀ z ∈ cubeIdx G, ∃ b : G.Ω 1, (b : CTorus d L N₁ m₁ K) = z.2 ∧
      z.2 ∈ intBox z := by
    intro z hz
    obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hz
    have hbaseΩ : z.2 ∈ G.Ω 1 := G.layer_subset hm1 hmK hl
    refine ⟨⟨z.2, hbaseΩ⟩, rfl, ?_⟩
    rw [mem_intBox]
    intro μ
    refine ⟨0, ?_⟩
    have hB : (1 : ℝ) ≤ (L : ℝ) ^ (z.1 + m₁) :=
      one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
    simp only [Int.cast_zero, zero_mul, add_zero]
    rw [abs_lt]
    constructor <;> nlinarith
  have hhatY : ∀ z ∈ cubeIdx G, (sProd G s z ≠ 0 ∨ sProd G s' z ≠ 0) →
      SubI G (intBox z) Y → SubI G (hatBox z) Y := by
    intro z hz hactive hbox
    obtain ⟨b, hb, hbbox⟩ := hbase z hz
    have hbY : (b : CTorus d L N₁ m₁ K) ∈ Y := hbox b (hb ▸ hbbox)
    rcases hdich_aux S hconn hY z hz (hact z hactive) with h | h
    · exact h
    · exact absurd hbY (h b (hb ▸ box_subset_hatBox z hbbox))
  have hzY : ∀ z ∈ cubeIdx G, (sProd G s z ≠ 0 ∨ sProd G s' z ≠ 0) →
      SubI G (intBox z) Y → z ∈ ZY G X₁ 𝒞 Y := fun z hz hactive hbox =>
    Finset.mem_filter.2 ⟨hz, hact z hactive, hhatY z hz hactive hbox⟩
  have hdichT : ∀ z ∈ cubeIdx G, (sProd G s z ≠ 0 ∨ sProd G s' z ≠ 0) →
      SubI G (intBox z) (SY G X₁ 𝒞 Y) ∨ DisjI G (intBox z) (SY G X₁ 𝒞 Y) := by
    intro z hz hactive
    rcases hdich_aux S hconn hY z hz (hact z hactive) with h | h
    · left
      intro x hx
      have hzZ : z ∈ ZY G X₁ 𝒞 Y := Finset.mem_filter.2 ⟨hz, hact z hactive, h⟩
      exact Finset.mem_biUnion.2 ⟨z, hzZ, hx⟩
    · right
      intro x hx hxT
      exact h x (box_subset_hatBox z hx) (SY_subset hxT)
  have hagreeT : ∀ z ∈ cubeIdx G, SubI G (intBox z) (SY G X₁ 𝒞 Y) → sProd G s z = sProd G s' z := by
    intro z hz hbox
    by_cases hactive : sProd G s z ≠ 0 ∨ sProd G s' z ≠ 0
    · have hP := hact z hactive
      have hboxY : SubI G (intBox z) Y := fun x hx => SY_subset (hbox x hx)
      have hhatYz := hhatY z hz hactive hboxY
      unfold sProd
      refine Finset.prod_congr rfl fun P hPQ => ?_
      by_cases hPP : P ∈ parCubes G X₁
      · by_cases hPC : P ∈ 𝒞
        · obtain ⟨hPi, y, hy, hyhat⟩ := (mem_Qset).1 hPQ
          have hyP : y ∈ cubeP P := mem_cubeP.2 hy
          have hyΩ : y ∈ G.Ω 1 := cubeP_subset_Ω S hPi hyP
          have hyY : y ∈ Y := hhatYz ⟨y, hyΩ⟩ (mem_boxSet.2 hyhat)
          have hsubV : cubeP P ⊆ (Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1 := by
            intro x hx
            rw [Finset.mem_filter]
            refine ⟨?_, cubeP_subset_Ω S hPi hx⟩
            unfold Vset
            rw [Finset.mem_union]
            right
            exact Finset.mem_biUnion.2 ⟨P, hPC, hx⟩
          have hsubY : SubI G (cubeP P) Y := by
            rcases connIn_dichotomy (cubeP_connIn S hPi) hsubV hY with h | h
            · intro x hx; exact h hx
            · exfalso; exact Finset.disjoint_left.1 h hyP hyY
          exact hag P hPC hsubY
        · rw [(hs0 P hPP hPC).1, (hs0 P hPP hPC).2]
      · rw [(hs1 P ((mem_Qset).1 hPQ).1 hPP).1, (hs1 P ((mem_Qset).1 hPQ).1 hPP).2]
    · push Not at hactive
      rw [hactive.1, hactive.2]
  intro x hxY
  by_cases hxT : (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y
  · exact Gs_local S hα hα' hU hU' hdichT hagreeT hA hf x hxT
  · -- outside `S_Y` both sides vanish
    have hz0 : ∀ {u : ℕ × CTorus d L N₁ m₁ K → ℂ} {β : G.Ω 1 → ℂ} {g : G.Ω 1 → ℂ},
        (∀ P ∈ parCubes G X₁, P ∉ 𝒞 → u P = 0) →
        (Gs G a ν β u *ᵥ g) x = 0 := by
      intro u β g hu
      by_contra hne
      have hc := dg5_support u g x hne
      unfold Core at hc
      obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hc
      have hzZ' := Finset.mem_filter.1 hzZ
      have hactive : sProd G u z ≠ 0 := hzZ'.2
      have hP := hact_aux u hu z hactive
      have hxbox : (x : CTorus d L N₁ m₁ K) ∈ intBox z := coreBox_subset_box hxz
      rcases hdich_aux S hconn hY z hzZ'.1 hP with h | h
      · exact hxT (Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hzZ'.1, hP, h⟩, hxbox⟩)
      · exact h x (box_subset_hatBox z hxbox) hxY
    rw [hz0 (fun P hP hPC => (hs0 P hP hPC).1), hz0 (fun P hP hPC => (hs0 P hP hPC).2)]

end Inner

end Balaban.Localization
