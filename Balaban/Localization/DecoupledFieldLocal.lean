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

section Rows

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **Support of a row of `H_D(α)`**: the entry `H x y` vanishes unless `y` is `x`, a neighbour of
`x` or in the block of `x`. -/
theorem dirichlet_entry_eq_zero (α : G.Ω 1 → ℂ) {x y : G.Ω 1}
    (hxy : (y : CTorus d L N₁ m₁ K) ≠ x)
    (hnb : ∀ μ : Fin d, (y : CTorus d L N₁ m₁ K) ≠ (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∧
      (y : CTorus d L N₁ m₁ K) ≠ (x : CTorus d L N₁ m₁ K) - Pi.single μ 1)
    (hblk : (y : CTorus d L N₁ m₁ K) ∉ G.blk (G.layerIndex (x : CTorus d L N₁ m₁ K)) x) :
    dirichletOperator G a ν α x y = 0 := by
  classical
  have h := dirichlet_apply G a ν α (Pi.single y 1) x
  have e : (dirichletOperator G a ν α *ᵥ (Pi.single y (1 : ℂ) : G.Ω 1 → ℂ)) x =
      dirichletOperator G a ν α x y := by
    rw [Matrix.mulVec_single_one]; rfl
  rw [e] at h
  have hz : ∀ w : CTorus d L N₁ m₁ K, w ≠ (y : CTorus d L N₁ m₁ K) →
      zeroExt (G.Ω 1) (Pi.single y (1 : ℂ) : G.Ω 1 → ℂ) w = 0 := by
    intro w hw
    unfold zeroExt
    split_ifs with hwΩ
    · have : (⟨w, hwΩ⟩ : G.Ω 1) ≠ y := fun h' => hw (congrArg Subtype.val h')
      exact Pi.single_eq_of_ne this _
    · rfl
  have hx0 : (Pi.single y (1 : ℂ) : G.Ω 1 → ℂ) x = 0 :=
    Pi.single_eq_of_ne (fun h' => hxy (by rw [h'])) _
  rw [h]
  unfold negLap blockTerm
  have h1 : zeroExt (G.Ω 1) (Pi.single y (1 : ℂ) : G.Ω 1 → ℂ) (x : CTorus d L N₁ m₁ K) = 0 :=
    hz _ (fun h' => hxy h'.symm)
  have h2 : ∀ μ : Fin d, zeroExt (G.Ω 1) (Pi.single y (1 : ℂ) : G.Ω 1 → ℂ)
      ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) = 0 := fun μ => hz _ (fun h' => (hnb μ).1 h'.symm)
  have h3 : ∀ μ : Fin d, zeroExt (G.Ω 1) (Pi.single y (1 : ℂ) : G.Ω 1 → ℂ)
      ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) = 0 := fun μ => hz _ (fun h' => (hnb μ).2 h'.symm)
  have h4 : ∑ y' ∈ G.blk (G.layerIndex (x : CTorus d L N₁ m₁ K)) x,
      zeroExt (G.Ω 1) (Pi.single y (1 : ℂ) : G.Ω 1 → ℂ) y' = 0 := by
    refine Finset.sum_eq_zero fun y' hy' => hz _ ?_
    rintro rfl
    exact hblk hy'
  simp [h1, h2, h3, h4, hx0]


theorem inBox_hat_of_add_int {z : ℕ × CTorus d L N₁ m₁ K}
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ intBox z) (w : Fin d → ℤ) {B : ℝ}
    (hw : ∀ μ, |(w μ : ℝ)| ≤ B) (hB : B ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ z.1) :
    x + (intTorus w : CTorus d L N₁ m₁ K) ∈ hatBox z := by
  unfold hatBox
  rw [mem_boxSet]
  refine ((mem_intBox.1 hx).add_int w hw).mono ?_
  unfold hatRad
  linarith

/-- **The row of `H_D(α)` at a site of `□_z` lies in `□̂_z`.**  If `x ∈ □_z ∩ Ω₁` and
`H_D(α) x y ≠ 0` then `y ∈ □̂_z`. -/
theorem row_mem_hatBox (S : DGSetting G a ν) {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ cubeIdx G)
    (α : G.Ω 1 → ℂ) {x : G.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∈ intBox z) {y : G.Ω 1}
    (h : dirichletOperator G a ν α x y ≠ 0) : (y : CTorus d L N₁ m₁ K) ∈ hatBox z := by
  classical
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast S.hL
  have hLr : (1 : ℝ) ≤ L := by linarith
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ z.1 := one_le_pow₀ hLr
  have hbig : (1 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ z.1 := by nlinarith
  by_contra hyH
  apply h
  apply dirichlet_entry_eq_zero (G := G) α
  · intro hyx
    exact hyH (hyx ▸ box_subset_hatBox z hx)
  · intro μ
    constructor
    · intro hyx
      have hw : ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) =
          (x : CTorus d L N₁ m₁ K) + (intTorus (Pi.single μ (1 : ℤ)) : CTorus d L N₁ m₁ K) := by
        congr 1
        funext ν'
        by_cases h' : ν' = μ <;> simp [intTorus_apply, h']
      refine hyH (hyx ▸ ?_)
      rw [hw]
      refine inBox_hat_of_add_int hx _ (B := 1) (fun ν' => ?_) (by linarith)
      by_cases h' : ν' = μ <;> simp [h']
    · intro hyx
      have hw : ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) =
          (x : CTorus d L N₁ m₁ K) + (intTorus (Pi.single μ (-1 : ℤ)) : CTorus d L N₁ m₁ K) := by
        funext ν'
        by_cases h' : ν' = μ <;> simp [intTorus_apply, h', sub_eq_add_neg]
      refine hyH (hyx ▸ ?_)
      rw [hw]
      refine inBox_hat_of_add_int hx _ (B := 1) (fun ν' => ?_) (by linarith)
      by_cases h' : ν' = μ <;> simp [h']
  · intro hy
    have hy' := G.mem_blk.1 hy
    obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec x.2
    have hnle := layer_le_of_mem_box S.cover_sep (by have := S.hL; omega) hz hn1 hnK hxl hx
    have hcell : SameCell (L ^ G.layerIndex (x : CTorus d L N₁ m₁ K))
        (y : CTorus d L N₁ m₁ K) x := sameCell_of_jBlock_eq hnK hy'
    have hlpos : 0 < L ^ G.layerIndex (x : CTorus d L N₁ m₁ K) :=
      pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
    obtain ⟨w, hw, hwb⟩ := exists_int_of_sameCell hlpos hcell
    refine hyH ?_
    rw [hw]
    refine inBox_hat_of_add_int hx w (B := (L : ℝ) ^ (z.1 + 1)) (fun ν' => ?_) ?_
    · have h1 := hwb ν'
      have h3 : (((L ^ G.layerIndex (x : CTorus d L N₁ m₁ K) : ℕ)) : ℝ) =
          (L : ℝ) ^ G.layerIndex (x : CTorus d L N₁ m₁ K) := by push_cast; rfl
      rw [h3] at h1
      exact h1.le.trans (pow_le_pow_right₀ hLr hnle)
    · have : (L : ℝ) ^ (z.1 + 1) = L * (L : ℝ) ^ z.1 := by ring
      rw [this]
      nlinarith

end Rows

section Congr

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **`𝒩` at a site only sees the data on the support of the row of `H₀`.** -/
theorem Nexp_congr (ιU : Bool) {φ φ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {Fs Fs' dφ dφ' : G.Ω 1 × Fin N → ℂ} {H H' : Matrix (G.Ω 1) (G.Ω 1) ℂ} {x : G.Ω 1}
    (hHx : ∀ y, H x y = H' x y) (hφx : ∀ i, φ x i = φ' x i) (hFx : ∀ i, Fs (x, i) = Fs' (x, i))
    (hdx : ∀ i, dφ (x, i) = dφ' (x, i))
    (hy : ∀ y : G.Ω 1, H x y ≠ 0 → (∀ i, φ y i = φ' y i) ∧ (∀ i, dφ (y, i) = dφ' (y, i))) :
    Nexp ιU φ Fs dφ H x = Nexp ιU φ' Fs' dφ' H' x := by
  have hH' : ∀ y, H' x y = H x y := fun y => (hHx y).symm
  unfold Nexp
  simp only [hH']
  have t1 : ∑ i, (φ x i + dφ (x, i)) * Fs (x, i) = ∑ i, (φ' x i + dφ' (x, i)) * Fs' (x, i) :=
    Finset.sum_congr rfl fun i _ => by rw [hφx i, hdx i, hFx i]
  have t2 : ∑ y, ∑ i, H x y * (φ x i - φ y i) * dφ (y, i) =
      ∑ y, ∑ i, H x y * (φ' x i - φ' y i) * dφ' (y, i) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h0 : H x y = 0
    · simp [h0]
    · obtain ⟨h1, h2⟩ := hy y h0
      exact Finset.sum_congr rfl fun i _ => by rw [hφx i, h1 i, h2 i]
  have t3 : ∑ y, H x y * ∑ i, dφ (y, i) * dφ (y, i) = ∑ y, H x y * ∑ i, dφ' (y, i) * dφ' (y, i) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h0 : H x y = 0
    · simp [h0]
    · obtain ⟨-, h2⟩ := hy y h0
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [h2 i]
  have t4 : ∑ i, dφ (x, i) * ∑ y, H x y * dφ (y, i) = ∑ i, dφ' (x, i) * ∑ y, H x y * dφ' (y, i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdx i]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h0 : H x y = 0
    · simp [h0]
    · obtain ⟨-, h2⟩ := hy y h0
      rw [h2 i]
  have t5 : ∑ y, H x y * (∑ i, φ y i * φ y i - 1) = ∑ y, H x y * (∑ i, φ' y i * φ' y i - 1) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h0 : H x y = 0
    · simp [h0]
    · obtain ⟨h1, -⟩ := hy y h0
      congr 2
      exact Finset.sum_congr rfl fun i _ => by rw [h1 i]
  rw [t1, t2, t3, t4, t5]

end Congr

section Step

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **Agreement of two data sets on `Y`**: `α₀, φ₀, f₁` agree at the sites of `Y ∩ Ω₁`, and `δΨ`
at those sites and at the collar sites adjacent to them (the source `F_s` of the linear problem
reads `δΨ` on the neighbours of a site). -/
structure DataAgree (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (N : ℕ)
    (Y : Finset (CTorus d L N₁ m₁ K))
    (α₀ α₀' : G.Ω 1 → ℂ) (φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (f₁ f₁' : G.Ω 1 × Fin N → ℂ) : Prop where
  alpha : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → α₀ x = α₀' x
  phi : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → φ₀ x = φ₀' x
  psi : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → δΨ x = δΨ' x
  psi_collar : ∀ y ∈ collar G, (∃ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y ∧ Adj (x : CTorus d L N₁ m₁ K) y) →
    δΨ y = δΨ' y
  src : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → ∀ i, f₁ (x, i) = f₁' (x, i)

theorem pertSource_congr {Y : Finset (CTorus d L N₁ m₁ K)} {α₀ α₀' : G.Ω 1 → ℂ}
    {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ} {f₁ f₁' : G.Ω 1 × Fin N → ℂ}
    (hD : DataAgree G N Y α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁') {z : G.Ω 1}
    (hz : (z : CTorus d L N₁ m₁ K) ∈ Y) (i : Fin N) :
    pertSource G a δΨ f₁ (z, i) = pertSource G a δΨ' f₁' (z, i) := by
  unfold pertSource qStar boundaryTerm
  simp only [Pi.add_apply]
  rw [hD.psi z hz, hD.src z hz i]
  congr 2
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  · by_cases h : (z : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∈ collar G
    · simp only [h, ↓reduceIte]
      rw [hD.psi_collar _ h ⟨z, hz, μ, Or.inl rfl⟩]
    · simp only [h, ↓reduceIte]
  · by_cases h : (z : CTorus d L N₁ m₁ K) - Pi.single μ 1 ∈ collar G
    · simp only [h, ↓reduceIte]
      rw [hD.psi_collar _ h ⟨z, hz, μ, Or.inr (by simp)⟩]
    · simp only [h, ↓reduceIte]


/-- **One step of the comparison (the heart of Step 5 of I-4a).**  If the rescaled potentials
`ξ, η` agree on `S_Y`, then `𝒩_s(ξ)` and `𝒩_{s'}(η)` (for data agreeing on `Y`) agree on `S_Y`. -/
theorem local_step {cstar BG : ℝ} (hF : FamSpec d L cstar BG) (S : DGSetting G a ν) (hconn : HatConn G)
    {κ : ℝ} (hκ : 0 ≤ κ) (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams G} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : G.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : G.Ω 1 × Fin N → ℂ} {δ₀ ρ : ℝ} (hα0 : Small G α₀ δ₀) (hα0' : Small G α₀' δ₀)
    (hρ : δ₀ + ρ ≤ gamma1 d / 8)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx G, P ∉ parCubes G X₁ → extS G s P = 1 ∧ extS G s' P = 1)
    (hs0 : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → extS G s P = 0 ∧ extS G s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI G (cubeP P) Y → extS G s P = extS G s' P)
    (hD : DataAgree G N Y α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {ξ η : G.Ω 1 → ℂ} (hξ : ∀ x, ‖ξ x‖ ≤ ρ) (hη : ∀ x, ‖η x‖ ≤ ρ)
    (hξη : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → ξ x = η x) :
    ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y →
      Smap G (decG G a ν s) (dirichletOperator G a ν α₀) ιU α₀ φ₀ (pertSource G a δΨ f₁) ξ x =
      Smap G (decG G a ν s') (dirichletOperator G a ν α₀') ιU α₀' φ₀' (pertSource G a δΨ' f₁') η x := by
  classical
  intro x hxT
  have hxY : (x : CTorus d L N₁ m₁ K) ∈ Y := SY_subset hxT
  have hd0 : 0 < d := by have := S.hd; omega
  obtain ⟨-, hunit⟩ := hF.2.2 G S hκ hM hs N
  obtain ⟨-, hunit'⟩ := hF.2.2 G S hκ hM hs' N
  have hδα : Small G (toAlpha G ξ) ρ := small_toAlpha G ξ hξ
  have hδα' : Small G (toAlpha G η) ρ := small_toAlpha G η hη
  have hA : Small G (α₀ + toAlpha G ξ) (gamma1 d / 8) := fun y =>
    ((Small.add hα0 hδα) y).trans hρ
  have hA' : Small G (α₀' + toAlpha G η) (gamma1 d / 8) := fun y =>
    ((Small.add hα0' hδα') y).trans hρ
  have hAeq : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y →
      (α₀ + toAlpha G ξ) y = (α₀' + toAlpha G η) y := by
    intro y hy
    simp only [Pi.add_apply]
    rw [hD.alpha y (SY_subset hy), show toAlpha G ξ y = toAlpha G η y by
      unfold toAlpha; rw [hξη y hy]]
  have hdphi : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) (toAlpha G ξ) (y, i) =
      dphi G (decG G a ν s') α₀' φ₀' (pertSource G a δΨ' f₁') (toAlpha G η) (y, i) := by
    intro y hy i
    unfold dphi
    rw [liftOp_mulVec, liftOp_mulVec]
    refine dg5'_inner S hconn hY (admPot_of_small hd0 hA) (admPot_of_small hd0 hA')
      (hunit (admPot_of_small hd0 hA)) (hunit' (admPot_of_small hd0 hA')) hs1 hs0 hag hAeq
      (f := fun b => Fsrc φ₀ (pertSource G a δΨ f₁) (toAlpha G ξ) (b, i))
      (f' := fun b => Fsrc φ₀' (pertSource G a δΨ' f₁') (toAlpha G η) (b, i)) ?_ y hy
    intro b hb
    simp only [Fsrc]
    rw [pertSource_congr hD (SY_subset hb) i, hD.phi b (SY_subset hb)]
    congr 2
    unfold toAlpha; rw [hξη b hb]
  -- the geometry of `x`
  obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hxT
  have hzZ' := Finset.mem_filter.1 hzZ
  unfold Smap
  rw [Nmap_explicit, Nmap_explicit]
  congr 1
  refine Nexp_congr ιU ?_ (fun i => by rw [hD.phi x hxY]) (fun i => pertSource_congr hD hxY i)
    (fun i => hdphi x hxY i) (fun y hy => ?_)
  · intro y
    rw [dirichletOperator_eq_add a ν α₀, dirichletOperator_eq_add a ν α₀']
    simp only [Matrix.add_apply, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy; simp [hD.alpha x hxY]
    · simp [hxy]
  · have hyhat := row_mem_hatBox S hzZ'.1 α₀ hxz hy
    have hyY : (y : CTorus d L N₁ m₁ K) ∈ Y := hzZ'.2.2 y hyhat
    exact ⟨fun i => by rw [hD.phi y hyY], fun i => hdphi y hyY i⟩

end Step

section Pair

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The fixed point of `Smap` in the ball with its Picard iterates (rate `1/2`). -/
theorem smap_fixed_iterates {𝒢 : (G.Ω 1 → ℂ) → Matrix (G.Ω 1) (G.Ω 1) ℂ}
    {H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ} {ιU : Bool} {B Kc Rc γ : ℝ} {α₀ : G.Ω 1 → ℂ}
    {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} {Fs : G.Ω 1 × Fin N → ℂ} {δ₀ Fb Gb ρ : ℝ}
    (hG : GreenFamily G N 𝒢 B γ) (H : Setup G H₀ ιU Kc Rc α₀ φ₀ Fs δ₀ Fb Gb)
    (hC : CoreHyp N B Kc Rc γ δ₀ Fb Gb ρ) :
    ∃ ξ ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) ρ, Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ = ξ ∧
      (∀ ξ' ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) ρ, Smap G 𝒢 H₀ ιU α₀ φ₀ Fs ξ' = ξ' → ξ' = ξ) ∧
      ∀ n : ℕ, (Smap G 𝒢 H₀ ιU α₀ φ₀ Fs)^[n] 0 ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) ρ ∧
        ‖(Smap G 𝒢 H₀ ιU α₀ φ₀ Fs)^[n] 0 - ξ‖ ≤ (1 / 2 : ℝ) ^ n * ρ :=
  Balaban.Analysis.exists_unique_fixedPoint_closedBall (S := Smap G 𝒢 H₀ ιU α₀ φ₀ Fs) hC.ρ_nn
    (by norm_num) (by norm_num) (Smap_mem_ball hG H hC)
    (fun ξ hξ ξ' hξ' => Smap_lip_norm hG H hC ξ ξ' hξ hξ')

/-- The Picard iterates of two maps that agree on `T` at every step agree on `T`; so do their
fixed points. -/
theorem fixed_agree_of_step {ι : Type*} {S S' : (ι → ℂ) → (ι → ℂ)}
    {T : ι → Prop} {ρ : ℝ} {ξ ξ' : ι → ℂ} [Fintype ι]
    (hstep : ∀ u v : ι → ℂ, (∀ i, ‖u i‖ ≤ ρ) → (∀ i, ‖v i‖ ≤ ρ) → (∀ i, T i → u i = v i) →
      ∀ i, T i → S u i = S' v i)
    (hit : ∀ n : ℕ, S^[n] 0 ∈ Metric.closedBall (0 : ι → ℂ) ρ ∧ ‖S^[n] 0 - ξ‖ ≤ (1 / 2 : ℝ) ^ n * ρ)
    (hit' : ∀ n : ℕ, S'^[n] 0 ∈ Metric.closedBall (0 : ι → ℂ) ρ ∧
      ‖S'^[n] 0 - ξ'‖ ≤ (1 / 2 : ℝ) ^ n * ρ) (hρ : 0 ≤ ρ) :
    ∀ i, T i → ξ i = ξ' i := by
  have hagree : ∀ n : ℕ, ∀ i, T i → (S^[n] 0) i = (S'^[n] 0) i := by
    intro n
    induction n with
    | zero => intro i _; simp
    | succ n ih =>
      intro i hi
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine hstep _ _ (fun j => ?_) (fun j => ?_) ih i hi
      · have := (mem_closedBall_zero_iff.1 (hit n).1)
        exact (norm_le_pi_norm _ j).trans this
      · have := (mem_closedBall_zero_iff.1 (hit' n).1)
        exact (norm_le_pi_norm _ j).trans this
  intro i hi
  by_contra hne
  have hpos : 0 < ‖ξ i - ξ' i‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ‖ξ i - ξ' i‖ / (2 * (ρ + 1)))
    (by norm_num : (1 / 2 : ℝ) < 1)
  have h1 : ‖ξ i - (S^[n] 0) i‖ ≤ (1 / 2 : ℝ) ^ n * ρ := by
    have e : ξ i - (S^[n] 0) i = (ξ - S^[n] 0) i := rfl
    rw [e]
    exact (norm_le_pi_norm _ i).trans (by rw [norm_sub_rev]; exact (hit n).2)
  have h2 : ‖(S'^[n] 0) i - ξ' i‖ ≤ (1 / 2 : ℝ) ^ n * ρ :=
    (norm_le_pi_norm (S'^[n] 0 - ξ') i).trans (hit' n).2
  have h3 : ξ i - ξ' i = (ξ i - (S^[n] 0) i) + ((S'^[n] 0) i - ξ' i) := by
    rw [← hagree n i hi]; ring
  have : ‖ξ i - ξ' i‖ ≤ 2 * ((1 / 2 : ℝ) ^ n * ρ) := by
    rw [h3]; calc _ ≤ _ := norm_add_le _ _
      _ ≤ _ := by linarith
  have h4 : (1 / 2 : ℝ) ^ n * (2 * (ρ + 1)) < ‖ξ i - ξ' i‖ := by
    have := (lt_div_iff₀ (by positivity : 0 < 2 * (ρ + 1))).1 hn
    exact this
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]


/-- **Theorem I-4a (e): locality, comparison form.**  Let `𝒞 ⊂ 𝔓`-data, `Y` a union of
nearest-neighbour components of `V(𝒞) ∩ Ω₁`, `S_Y = ⋃_{z ∈ Z_Y} □_z` (so `Core_Y ⊆ S_Y ⊆ Y`), two
parameter vectors `s, s'` that vanish on `𝔓 ∖ 𝒞`, equal `1` off `𝔓` and agree on the cubes of `𝒞`
inside `Y`, and two data sets that agree on `Y`.  Then the solutions of the two decoupled systems
satisfy `δα(s) = δα(s')` on `S_Y` and `δφ(s) = δφ(s')` on `Y ∩ Ω₁`; in particular on `Core_Y`. -/
theorem i4a_local {cstar BG : ℝ} (hF : FamSpec d L cstar BG) (S : DGSetting G a ν)
    (hconn : HatConn G) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams G} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : G.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (H : DecHyp G a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) (H' : DecHyp G a ν ιU α₀' φ₀' δΨ' f₁' δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx G, P ∉ parCubes G X₁ → extS G s P = 1 ∧ extS G s' P = 1)
    (hs0 : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → extS G s P = 0 ∧ extS G s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI G (cubeP P) Y → extS G s P = extS G s' P)
    (hD : DataAgree G N Y α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {δα δα' : G.Ω 1 → ℂ}
    (hfix : DecFixed G a ν s ιU α₀ φ₀ (pertSource G a δΨ f₁) δα)
    (hsm : Small G δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed G a ν s' ιU α₀' φ₀' (pertSource G a δΨ' f₁') δα')
    (hsm' : Small G δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → δα x = δα' x) ∧
    (∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα (y, i) =
      dphi G (decG G a ν s') α₀' φ₀' (pertSource G a δΨ' f₁') δα' (y, i)) := by
  classical
  have hBG := hF.2.1
  have hd0 : 0 < d := by have := S.hd; omega
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ B := by have := famConst_ge_one (L := L) hBG κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ H.δ₀_nn H.δ₁_nn hδ₀ hδ₁
  obtain ⟨⟨hfam, -⟩, hunit⟩ := hF.2.2 G S hκ hM hs N
  obtain ⟨⟨hfam', -⟩, hunit'⟩ := hF.2.2 G S hκ hM hs' N
  obtain ⟨ξ, hξB, hξfix, hξuniq, hit⟩ := smap_fixed_iterates hfam H.setup hC
  obtain ⟨ξ', hξB', hξfix', hξuniq', hit'⟩ := smap_fixed_iterates hfam' H'.setup hC
  -- identify `toAlpha ξ` with `δα`
  have hid : ∀ {s₀ : DecParams G} {α₀₀ : G.Ω 1 → ℂ} {φ₀₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}
      {Fs₀ : G.Ω 1 × Fin N → ℂ} {ξ₀ δα₀ : G.Ω 1 → ℂ},
      Smap G (decG G a ν s₀) (dirichletOperator G a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀ ξ₀ = ξ₀ →
      ξ₀ ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) (c6' d L N B Γ) →
      (∀ ξ' ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) (c6' d L N B Γ),
        Smap G (decG G a ν s₀) (dirichletOperator G a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀ ξ' = ξ' → ξ' = ξ₀) →
      DecFixed G a ν s₀ ιU α₀₀ φ₀₀ Fs₀ δα₀ → Small G δα₀ (c6' d L N B Γ) →
      toAlpha G ξ₀ = δα₀ := by
    intro s₀ α₀₀ φ₀₀ Fs₀ ξ₀ δα₀ _ _ huniq hf hsm₀
    have hm : ofAlpha G δα₀ ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) (c6' d L N B Γ) := by
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg (c6'_pos (d := d) (L := L) (N := N) hB0 hΓ).le).2
        fun x => ?_
      rw [norm_ofAlpha]; exact hsm₀ x
    have hf' : Smap G (decG G a ν s₀) (dirichletOperator G a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀
        (ofAlpha G δα₀) = ofAlpha G δα₀ := by
      funext x
      unfold Smap
      rw [toAlpha_ofAlpha]
      have := congrFun hf x
      unfold DecFixed at hf
      rw [hf]
      rfl
    rw [← huniq _ hm hf', toAlpha_ofAlpha]
  have e1 : toAlpha G ξ = δα := hid hξfix hξB hξuniq hfix hsm
  have e2 : toAlpha G ξ' = δα' := hid hξfix' hξB' hξuniq' hfix' hsm'
  have hpoly : ∀ {α₀₀ : G.Ω 1 → ℂ}, Small G α₀₀ δ₀ → δ₀ + c6' d L N B Γ ≤ Γ := by
    intro _ _; linarith [hC.poly, hC.ρ_nn]
  -- the pair induction
  have hagreeξ : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → ξ x = ξ' x := by
    refine fixed_agree_of_step (T := fun x : G.Ω 1 => (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y)
      (fun u v hu hv huv i hi => ?_) (fun n => ⟨(hit n).1, (hit n).2⟩)
      (fun n => ⟨(hit' n).1, (hit' n).2⟩) hC.ρ_nn
    exact local_step hF S hconn hκ hM hs hs' H.alpha0 H'.alpha0 (hpoly H.alpha0)
      hY hs1 hs0 hag hD hu hv huv i hi
  have hδ : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → δα x = δα' x := by
    intro x hx
    rw [← e1, ← e2]
    unfold toAlpha
    rw [hagreeξ x hx]
  refine ⟨hδ, fun y hy i => ?_⟩
  have hA : Small G (α₀ + δα) Γ := fun z => ((Small.add H.alpha0 hsm) z).trans (hpoly H.alpha0)
  have hA' : Small G (α₀' + δα') Γ := fun z =>
    ((Small.add H'.alpha0 hsm') z).trans (hpoly H'.alpha0)
  unfold dphi
  rw [liftOp_mulVec, liftOp_mulVec]
  refine dg5'_inner S hconn hY (admPot_of_small hd0 hA) (admPot_of_small hd0 hA')
    (hunit (admPot_of_small hd0 hA)) (hunit' (admPot_of_small hd0 hA')) hs1 hs0 hag
    (fun z hz => ?_) (f := fun b => Fsrc φ₀ (pertSource G a δΨ f₁) δα (b, i))
    (f' := fun b => Fsrc φ₀' (pertSource G a δΨ' f₁') δα' (b, i)) (fun b hb => ?_) y hy
  · simp only [Pi.add_apply]
    rw [hD.alpha z (SY_subset hz), hδ z hz]
  · simp only [Fsrc]
    rw [pertSource_congr hD (SY_subset hb) i, hD.phi b (SY_subset hb), hδ b hb]

end Pair

end Balaban.Localization
