/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2FieldClose
public import Balaban.Localization.Decoupled2Geometry
public import Balaban.Localization.DecoupledFieldLocal

/-!
# Theorem I-4a (e): locality of the decoupled perturbed system, for a cover `C` and an operator `H`

The comparison form of the locality (`i4a_local`): the pair induction on the Picard iterates of the
two maps `𝒮_s`, `𝒮_{s'}`.  The data of the two systems agree on `Y` (`DataAgree`, which reads the
operator `H` only), the parameters as in `dg5'`; the geometry of the cover enters through
`CoverLocal` (the centres, the cubes `P` and the rows of `H_D` at the points of `□_z`, which lie in
`□̂_z`: `row_mem_hat`).
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

/-- The sites of the interaction cubes of the centres of `Z_Y`. -/
noncomputable def SY (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (X₁ : Finset (CTorus d L N₁ m₁ K))
    (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)) (Y : Finset (CTorus d L N₁ m₁ K)) :
    Finset (CTorus d L N₁ m₁ K) :=
  (ZY C H X₁ 𝒞 Y).biUnion intBox

theorem hact_aux {X₁ : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (u : ℕ × CTorus d L N₁ m₁ K → ℂ) (hu : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → u P = 0)
    (z : ℕ × CTorus d L N₁ m₁ K) (hz : C.sProd u z ≠ 0) :
    ∀ P ∈ C.Qset z, P ∈ C.parCubes X₁ → P ∈ 𝒞 := by
  intro P hP hPP
  by_contra hPC
  exact (sProd_ne_zero_iff u z |>.1 hz) P hP (hu P hPP hPC)

/-- The thickened cube of a centre that only sees parameter cubes of `𝒞` lies in `V(𝒞) ∩ Ω₁`. -/
theorem hhat_aux (S : CoverLocal C H a ν Kc Cx) {X₁ : Finset (CTorus d L N₁ m₁ K)}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} (z : ℕ × CTorus d L N₁ m₁ K)
    (hP : ∀ P ∈ C.Qset z, P ∈ C.parCubes X₁ → P ∈ 𝒞) :
    hatI H z ⊆ (Vset X₁ 𝒞).filter fun x => x ∈ H.Ω 1 := by
  classical
  intro x hx
  unfold hatI at hx
  rw [Finset.mem_filter] at hx
  obtain ⟨hxh, hxΩ⟩ := hx
  obtain ⟨P, hown, hxP⟩ := S.own_cover x hxΩ
  have hQ : P ∈ C.Qset z := C.mem_Qset.2 ⟨hown, x, mem_cubeP.1 hxP, mem_boxSet.1 hxh⟩
  rw [Finset.mem_filter]
  refine ⟨?_, hxΩ⟩
  unfold Vset
  rw [Finset.mem_union]
  by_cases hPP : P ∈ C.parCubes X₁
  · right
    rw [Finset.mem_biUnion]
    exact ⟨_, hP _ hQ hPP, hxP⟩
  · left
    have : cubeP P ⊆ X₁ := by
      by_contra hc
      exact hPP (Finset.mem_filter.2 ⟨hown, hc⟩)
    exact this hxP

/-- The dichotomy: an active interaction cube lies inside `Y` or avoids it. -/
theorem hdich_aux (S : CoverLocal C H a ν Kc Cx) (hconn : HatConn C H) {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ H.Ω 1) Y)
    (z : ℕ × CTorus d L N₁ m₁ K) (hz : z ∈ C.cubeIdx)
    (hP : ∀ P ∈ C.Qset z, P ∈ C.parCubes X₁ → P ∈ 𝒞) :
    SubI H (hatBox z) Y ∨ DisjI H (hatBox z) Y := by
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
    {x : H.Ω 1} (hx : (x : CTorus d L N₁ m₁ K) ∈ SY C H X₁ 𝒞 Y) : (x : CTorus d L N₁ m₁ K) ∈ Y := by
  classical
  unfold SY at hx
  obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.1 hx
  exact (Finset.mem_filter.1 hz).2.2 x (box_subset_hatBox z hxz)

/-- **(DG5'), the version with data agreeing on `S_Y` only.**  Let `Y` be a union of
nearest-neighbour components of `V(𝒞) ∩ Ω₁` and `S_Y = ⋃_{z ∈ Z_Y} □_z`.  If `A = A'` and `f = f'`
on `S_Y` (and the parameters are as in `dg5'`) then `G_s(A) f = G_{s'}(A') f'` on all of `Y ∩ Ω₁`. -/
theorem dg5'_inner (S : CoverLocal C H a ν Kc Cx) (hconn : HatConn C H)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ H.Ω 1) Y)
    {α α' : H.Ω 1 → ℂ} (hα : AdmPot H α) (hα' : AdmPot H α')
    {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hU : IsUnit (1 - Kcal C H a ν α s)) (hU' : IsUnit (1 - Kcal C H a ν α' s'))
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → s P = 1 ∧ s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → s P = 0 ∧ s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI H (cubeP P) Y → s P = s' P)
    (hA : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY C H X₁ 𝒞 Y → α x = α' x)
    {f f' : H.Ω 1 → ℂ}
    (hf : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY C H X₁ 𝒞 Y → f x = f' x) :
    ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y →
      (Gs C H a ν α s *ᵥ f) x = (Gs C H a ν α' s' *ᵥ f') x := by
  classical
  have hact : ∀ z, (C.sProd s z ≠ 0 ∨ C.sProd s' z ≠ 0) →
      ∀ P ∈ C.Qset z, P ∈ C.parCubes X₁ → P ∈ 𝒞 := by
    intro z hz
    rcases hz with h | h
    · exact hact_aux s (fun P hP hPC => (hs0 P hP hPC).1) z h
    · exact hact_aux s' (fun P hP hPC => (hs0 P hP hPC).2) z h
  -- an active interaction cube inside `Y` has `z ∈ Z_Y`
  have hbase : ∀ z ∈ C.cubeIdx, ∃ b : H.Ω 1, (b : CTorus d L N₁ m₁ K) = z.2 ∧
      z.2 ∈ intBox z := by
    intro z hz
    have hbaseΩ : z.2 ∈ H.Ω 1 := S.cubeP_sub z hz z.2 (mem_cubeP.2 (SameCell.refl _ _))
    refine ⟨⟨z.2, hbaseΩ⟩, rfl, ?_⟩
    rw [mem_intBox]
    intro μ
    refine ⟨0, ?_⟩
    have hB : (1 : ℝ) ≤ (L : ℝ) ^ (z.1 + m₁) :=
      one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
    simp only [Int.cast_zero, zero_mul, add_zero]
    rw [abs_lt]
    constructor <;> nlinarith
  have hhatY : ∀ z ∈ C.cubeIdx, (C.sProd s z ≠ 0 ∨ C.sProd s' z ≠ 0) →
      SubI H (intBox z) Y → SubI H (hatBox z) Y := by
    intro z hz hactive hbox
    obtain ⟨b, hb, hbbox⟩ := hbase z hz
    have hbY : (b : CTorus d L N₁ m₁ K) ∈ Y := hbox b (hb ▸ hbbox)
    rcases hdich_aux S hconn hY z hz (hact z hactive) with h | h
    · exact h
    · exact absurd hbY (h b (hb ▸ box_subset_hatBox z hbbox))
  have hzY : ∀ z ∈ C.cubeIdx, (C.sProd s z ≠ 0 ∨ C.sProd s' z ≠ 0) →
      SubI H (intBox z) Y → z ∈ ZY C H X₁ 𝒞 Y := fun z hz hactive hbox =>
    Finset.mem_filter.2 ⟨hz, hact z hactive, hhatY z hz hactive hbox⟩
  have hdichT : ∀ z ∈ C.cubeIdx, (C.sProd s z ≠ 0 ∨ C.sProd s' z ≠ 0) →
      SubI H (intBox z) (SY C H X₁ 𝒞 Y) ∨ DisjI H (intBox z) (SY C H X₁ 𝒞 Y) := by
    intro z hz hactive
    rcases hdich_aux S hconn hY z hz (hact z hactive) with h | h
    · left
      intro x hx
      have hzZ : z ∈ ZY C H X₁ 𝒞 Y := Finset.mem_filter.2 ⟨hz, hact z hactive, h⟩
      exact Finset.mem_biUnion.2 ⟨z, hzZ, hx⟩
    · right
      intro x hx hxT
      exact h x (box_subset_hatBox z hx) (SY_subset hxT)
  have hagreeT : ∀ z ∈ C.cubeIdx, SubI H (intBox z) (SY C H X₁ 𝒞 Y) → C.sProd s z = C.sProd s' z := by
    intro z hz hbox
    by_cases hactive : C.sProd s z ≠ 0 ∨ C.sProd s' z ≠ 0
    · have hP := hact z hactive
      have hboxY : SubI H (intBox z) Y := fun x hx => SY_subset (hbox x hx)
      have hhatYz := hhatY z hz hactive hboxY
      unfold DecCover.sProd
      refine Finset.prod_congr rfl fun P hPQ => ?_
      by_cases hPP : P ∈ C.parCubes X₁
      · by_cases hPC : P ∈ 𝒞
        · obtain ⟨hPi, y, hy, hyhat⟩ := C.mem_Qset.1 hPQ
          have hyP : y ∈ cubeP P := mem_cubeP.2 hy
          have hyΩ : y ∈ H.Ω 1 := cubeP_subset_Ω' S hPi hyP
          have hyY : y ∈ Y := hhatYz ⟨y, hyΩ⟩ (mem_boxSet.2 hyhat)
          have hsubV : cubeP P ⊆ (Vset X₁ 𝒞).filter fun x => x ∈ H.Ω 1 := by
            intro x hx
            rw [Finset.mem_filter]
            refine ⟨?_, cubeP_subset_Ω' S hPi hx⟩
            unfold Vset
            rw [Finset.mem_union]
            right
            exact Finset.mem_biUnion.2 ⟨P, hPC, hx⟩
          have hsubY : SubI H (cubeP P) Y := by
            rcases connIn_dichotomy (cubeP_connIn' S hPi) hsubV hY with h | h
            · intro x hx; exact h hx
            · exfalso; exact Finset.disjoint_left.1 h hyP hyY
          exact hag P hPC hsubY
        · rw [(hs0 P hPP hPC).1, (hs0 P hPP hPC).2]
      · rw [(hs1 P (C.mem_Qset.1 hPQ).1 hPP).1, (hs1 P (C.mem_Qset.1 hPQ).1 hPP).2]
    · push Not at hactive
      rw [hactive.1, hactive.2]
  intro x hxY
  by_cases hxT : (x : CTorus d L N₁ m₁ K) ∈ SY C H X₁ 𝒞 Y
  · exact Gs_local S.toCoverBase hα hα' hU hU' hdichT hagreeT hA hf x hxT
  · -- outside `S_Y` both sides vanish
    have hz0 : ∀ {u : ℕ × CTorus d L N₁ m₁ K → ℂ} {β : H.Ω 1 → ℂ} {g : H.Ω 1 → ℂ},
        (∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → u P = 0) →
        (Gs C H a ν β u *ᵥ g) x = 0 := by
      intro u β g hu
      by_contra hne
      have hc := dg5_support S u g x hne
      unfold Core at hc
      obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hc
      have hzZ' := Finset.mem_filter.1 hzZ
      have hactive : C.sProd u z ≠ 0 := hzZ'.2
      have hP := hact_aux u hu z hactive
      have hxbox : (x : CTorus d L N₁ m₁ K) ∈ intBox z := coreBox_subset_box hxz
      rcases hdich_aux S hconn hY z hzZ'.1 hP with h | h
      · exact hxT (Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hzZ'.1, hP, h⟩, hxbox⟩)
      · exact h x (box_subset_hatBox z hxbox) hxY
    rw [hz0 (fun P hP hPC => (hs0 P hP hPC).1), hz0 (fun P hP hPC => (hs0 P hP hPC).2)]




/-- **One step of the comparison (the heart of Step 5 of I-4a).**  If the rescaled potentials
`ξ, η` agree on `S_Y`, then `𝒩_s(ξ)` and `𝒩_{s'}(η)` (for data agreeing on `Y`) agree on `S_Y`. -/
theorem local_step {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG) (S : CoverLocal C H a ν Kc Cx) (hconn : HatConn C H)
    {κ : ℝ} (hκ : 0 ≤ κ) (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : H.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : H.Ω 1 × Fin N → ℂ} {δ₀ ρ : ℝ} (hα0 : Small H α₀ δ₀) (hα0' : Small H α₀' δ₀)
    (hρ : δ₀ + ρ ≤ gamma1 d / 8)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ H.Ω 1) Y)
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → extS C s P = 1 ∧ extS C s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → extS C s P = 0 ∧ extS C s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI H (cubeP P) Y → extS C s P = extS C s' P)
    (hD : DataAgree H N Y α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {ξ η : H.Ω 1 → ℂ} (hξ : ∀ x, ‖ξ x‖ ≤ ρ) (hη : ∀ x, ‖η x‖ ≤ ρ)
    (hξη : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY C H X₁ 𝒞 Y → ξ x = η x) :
    ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY C H X₁ 𝒞 Y →
      Smap H (decG C H a ν s) (dirichletOperator H a ν α₀) ιU α₀ φ₀ (pertSource H a δΨ f₁) ξ x =
      Smap H (decG C H a ν s') (dirichletOperator H a ν α₀') ιU α₀' φ₀' (pertSource H a δΨ' f₁') η x := by
  classical
  intro x hxT
  have hxY : (x : CTorus d L N₁ m₁ K) ∈ Y := SY_subset hxT
  have hd0 : 0 < d := by have := S.hd; omega
  obtain ⟨-, hunit⟩ := hF.2.2 C H S.toCoverBase hκ hM hs N
  obtain ⟨-, hunit'⟩ := hF.2.2 C H S.toCoverBase hκ hM hs' N
  have hδα : Small H (toAlpha H ξ) ρ := small_toAlpha H ξ hξ
  have hδα' : Small H (toAlpha H η) ρ := small_toAlpha H η hη
  have hA : Small H (α₀ + toAlpha H ξ) (gamma1 d / 8) := fun y =>
    ((Small.add hα0 hδα) y).trans hρ
  have hA' : Small H (α₀' + toAlpha H η) (gamma1 d / 8) := fun y =>
    ((Small.add hα0' hδα') y).trans hρ
  have hAeq : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ SY C H X₁ 𝒞 Y →
      (α₀ + toAlpha H ξ) y = (α₀' + toAlpha H η) y := by
    intro y hy
    simp only [Pi.add_apply]
    rw [hD.alpha y (SY_subset hy), show toAlpha H ξ y = toAlpha H η y by
      unfold toAlpha; rw [hξη y hy]]
  have hdphi : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) (toAlpha H ξ) (y, i) =
      dphi H (decG C H a ν s') α₀' φ₀' (pertSource H a δΨ' f₁') (toAlpha H η) (y, i) := by
    intro y hy i
    unfold dphi
    rw [liftOp_mulVec, liftOp_mulVec]
    refine dg5'_inner S hconn hY (admPot_of_small hd0 hA) (admPot_of_small hd0 hA')
      (hunit (admPot_of_small hd0 hA)) (hunit' (admPot_of_small hd0 hA')) hs1 hs0 hag hAeq
      (f := fun b => Fsrc φ₀ (pertSource H a δΨ f₁) (toAlpha H ξ) (b, i))
      (f' := fun b => Fsrc φ₀' (pertSource H a δΨ' f₁') (toAlpha H η) (b, i)) ?_ y hy
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
  · have hyhat := S.row_mem_hat _ hzZ'.1 α₀ hxz hy
    have hyY : (y : CTorus d L N₁ m₁ K) ∈ Y := hzZ'.2.2 y hyhat
    exact ⟨fun i => by rw [hD.phi y hyY], fun i => hdphi y hyY i⟩





/-- **Theorem I-4a (e): locality, comparison form.**  Let `𝒞 ⊂ 𝔓`-data, `Y` a union of
nearest-neighbour components of `V(𝒞) ∩ Ω₁`, `S_Y = ⋃_{z ∈ Z_Y} □_z` (so `Core_Y ⊆ S_Y ⊆ Y`), two
parameter vectors `s, s'` that vanish on `𝔓 ∖ 𝒞`, equal `1` off `𝔓` and agree on the cubes of `𝒞`
inside `Y`, and two data sets that agree on `Y`.  Then the solutions of the two decoupled systems
satisfy `δα(s) = δα(s')` on `S_Y` and `δφ(s) = δφ(s')` on `Y ∩ Ω₁`; in particular on `Core_Y`. -/
theorem i4a_local {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG) (S : CoverLocal C H a ν Kc Cx)
    (hconn : HatConn C H) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : H.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : H.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (Hh : DecHyp H a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) (H' : DecHyp H a ν ιU α₀' φ₀' δΨ' f₁' δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ H.Ω 1) Y)
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → extS C s P = 1 ∧ extS C s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → extS C s P = 0 ∧ extS C s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI H (cubeP P) Y → extS C s P = extS C s' P)
    (hD : DataAgree H N Y α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {δα δα' : H.Ω 1 → ℂ}
    (hfix : DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα)
    (hsm : Small H δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed C H a ν s' ιU α₀' φ₀' (pertSource H a δΨ' f₁') δα')
    (hsm' : Small H δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY C H X₁ 𝒞 Y → δα x = δα' x) ∧
    (∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα (y, i) =
      dphi H (decG C H a ν s') α₀' φ₀' (pertSource H a δΨ' f₁') δα' (y, i)) := by
  classical
  have hBG := hF.2.1
  have hd0 : 0 < d := by have := S.hd; omega
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ B := by have := famConst_ge_one (L := L) hBG κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ Hh.δ₀_nn Hh.δ₁_nn hδ₀ hδ₁
  obtain ⟨⟨hfam, -⟩, hunit⟩ := hF.2.2 C H S.toCoverBase hκ hM hs N
  obtain ⟨⟨hfam', -⟩, hunit'⟩ := hF.2.2 C H S.toCoverBase hκ hM hs' N
  obtain ⟨ξ, hξB, hξfix, hξuniq, hit⟩ := smap_fixed_iterates hfam Hh.setup hC
  obtain ⟨ξ', hξB', hξfix', hξuniq', hit'⟩ := smap_fixed_iterates hfam' H'.setup hC
  -- identify `toAlpha ξ` with `δα`
  have hid : ∀ {s₀ : DecParams C} {α₀₀ : H.Ω 1 → ℂ} {φ₀₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}
      {Fs₀ : H.Ω 1 × Fin N → ℂ} {ξ₀ δα₀ : H.Ω 1 → ℂ},
      Smap H (decG C H a ν s₀) (dirichletOperator H a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀ ξ₀ = ξ₀ →
      ξ₀ ∈ Metric.closedBall (0 : H.Ω 1 → ℂ) (c6' d L N B Γ) →
      (∀ ξ' ∈ Metric.closedBall (0 : H.Ω 1 → ℂ) (c6' d L N B Γ),
        Smap H (decG C H a ν s₀) (dirichletOperator H a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀ ξ' = ξ' → ξ' = ξ₀) →
      DecFixed C H a ν s₀ ιU α₀₀ φ₀₀ Fs₀ δα₀ → Small H δα₀ (c6' d L N B Γ) →
      toAlpha H ξ₀ = δα₀ := by
    intro s₀ α₀₀ φ₀₀ Fs₀ ξ₀ δα₀ _ _ huniq hf hsm₀
    have hm : ofAlpha H δα₀ ∈ Metric.closedBall (0 : H.Ω 1 → ℂ) (c6' d L N B Γ) := by
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg (c6'_pos (d := d) (L := L) (N := N) hB0 hΓ).le).2
        fun x => ?_
      rw [norm_ofAlpha]; exact hsm₀ x
    have hf' : Smap H (decG C H a ν s₀) (dirichletOperator H a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀
        (ofAlpha H δα₀) = ofAlpha H δα₀ := by
      funext x
      unfold Smap
      rw [toAlpha_ofAlpha]
      have := congrFun hf x
      unfold DecFixed at hf
      rw [hf]
      rfl
    rw [← huniq _ hm hf', toAlpha_ofAlpha]
  have e1 : toAlpha H ξ = δα := hid hξfix hξB hξuniq hfix hsm
  have e2 : toAlpha H ξ' = δα' := hid hξfix' hξB' hξuniq' hfix' hsm'
  have hpoly : ∀ {α₀₀ : H.Ω 1 → ℂ}, Small H α₀₀ δ₀ → δ₀ + c6' d L N B Γ ≤ Γ := by
    intro _ _; linarith [hC.poly, hC.ρ_nn]
  -- the pair induction
  have hagreeξ : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY C H X₁ 𝒞 Y → ξ x = ξ' x := by
    refine fixed_agree_of_step (T := fun x : H.Ω 1 => (x : CTorus d L N₁ m₁ K) ∈ SY C H X₁ 𝒞 Y)
      (fun u v hu hv huv i hi => ?_) (fun n => ⟨(hit n).1, (hit n).2⟩)
      (fun n => ⟨(hit' n).1, (hit' n).2⟩) hC.ρ_nn
    exact local_step hF S hconn hκ hM hs hs' Hh.alpha0 H'.alpha0 (hpoly Hh.alpha0)
      hY hs1 hs0 hag hD hu hv huv i hi
  have hδ : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY C H X₁ 𝒞 Y → δα x = δα' x := by
    intro x hx
    rw [← e1, ← e2]
    unfold toAlpha
    rw [hagreeξ x hx]
  refine ⟨hδ, fun y hy i => ?_⟩
  have hA : Small H (α₀ + δα) Γ := fun z => ((Small.add Hh.alpha0 hsm) z).trans (hpoly Hh.alpha0)
  have hA' : Small H (α₀' + δα') Γ := fun z =>
    ((Small.add H'.alpha0 hsm') z).trans (hpoly H'.alpha0)
  unfold dphi
  rw [liftOp_mulVec, liftOp_mulVec]
  refine dg5'_inner S hconn hY (admPot_of_small hd0 hA) (admPot_of_small hd0 hA')
    (hunit (admPot_of_small hd0 hA)) (hunit' (admPot_of_small hd0 hA')) hs1 hs0 hag
    (fun z hz => ?_) (f := fun b => Fsrc φ₀ (pertSource H a δΨ f₁) δα (b, i))
    (f' := fun b => Fsrc φ₀' (pertSource H a δΨ' f₁') δα' (b, i)) (fun b hb => ?_) y hy
  · simp only [Pi.add_apply]
    rw [hD.alpha z (SY_subset hz), hδ z hz]
  · simp only [Fsrc]
    rw [pertSource_congr hD (SY_subset hb) i, hD.phi b (SY_subset hb), hδ b hb]



end Balaban.Localization.Dec2
