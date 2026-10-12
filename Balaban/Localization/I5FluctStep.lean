/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2FpField

/-!
# Theorem I-4a (e), footprint form, with the potential agreeing on `S_Y^F` only

`local_step_fp` and `i4a_local_fp` of `Decoupled2FpField.lean` require the data `(α₀, φ₀, δΨ, f₁)`
of the two systems to agree on all of `Y`.  The potential `α₀` enters the comparison only at the
sites of `S_Y^F` (`SYF_subset_Y`; the rows of `H_D(α)` at the sites of an eligible centre with
footprint in `Y`), so the same proof holds when `α₀` agrees on `S_Y^F` only (`DataAgreeS`).  This
is the form needed for the fluctuation problem on `H⁻` whose background potential is the decoupled
multiplier of `H⁺`, which is known to agree on `S_Y` only (Theorem I-4b (iv)).
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

/-- **Agreement of two data sets on `Y`, the potential on a subset `S` only.** -/
structure DataAgreeS (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (N : ℕ)
    (Y S : Finset (CTorus d L N₁ m₁ K))
    (α₀ α₀' : H.Ω 1 → ℂ) (φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (f₁ f₁' : H.Ω 1 × Fin N → ℂ) : Prop where
  alpha : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ S → α₀ x = α₀' x
  phi : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → φ₀ x = φ₀' x
  psi : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → δΨ x = δΨ' x
  psi_collar : ∀ y ∈ collar H, (∃ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y ∧ Adj (x : CTorus d L N₁ m₁ K) y) →
    δΨ y = δΨ' y
  src : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → ∀ i, f₁ (x, i) = f₁' (x, i)

theorem pertSource_congrS {Y S : Finset (CTorus d L N₁ m₁ K)} {α₀ α₀' : H.Ω 1 → ℂ}
    {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ} {f₁ f₁' : H.Ω 1 × Fin N → ℂ}
    (hD : DataAgreeS H N Y S α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁') {z : H.Ω 1}
    (hz : (z : CTorus d L N₁ m₁ K) ∈ Y) (i : Fin N) :
    pertSource H a δΨ f₁ (z, i) = pertSource H a δΨ' f₁' (z, i) := by
  unfold pertSource qStar boundaryTerm
  simp only [Pi.add_apply]
  rw [hD.psi z hz, hD.src z hz i]
  congr 2
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  · by_cases h : (z : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∈ collar H
    · simp only [h, ↓reduceIte]
      rw [hD.psi_collar _ h ⟨z, hz, μ, Or.inl rfl⟩]
    · simp only [h, ↓reduceIte]
  · by_cases h : (z : CTorus d L N₁ m₁ K) - Pi.single μ 1 ∈ collar H
    · simp only [h, ↓reduceIte]
      rw [hD.psi_collar _ h ⟨z, hz, μ, Or.inr (by simp)⟩]
    · simp only [h, ↓reduceIte]

/-- **One step of the comparison (the heart of Step 5 of I-4a).**  If the rescaled potentials
`ξ, η` agree on `S_Y`, then `𝒩_s(ξ)` and `𝒩_{s'}(η)` (for data agreeing on `Y`) agree on `S_Y`. -/
theorem local_step_fpS {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG) (S : FootLocal C H a ν Kc Cx)
    {κ : ℝ} (hκ : 0 ≤ κ) (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : H.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : H.Ω 1 × Fin N → ℂ} {δ₀ ρ : ℝ} (hα0 : Small H α₀ δ₀) (hα0' : Small H α₀' δ₀)
    (hρ : δ₀ + ρ ≤ gamma1 d / 8)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → extS C s P = 1 ∧ extS C s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → extS C s P = 0 ∧ extS C s' P = 0)
    (hag : ∀ P ∈ 𝒞, P ∈ A → extS C s P = extS C s' P)
    (hD : DataAgreeS H N Y (SYF C H a ν X₁ 𝒞 Y) α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {ξ η : H.Ω 1 → ℂ} (hξ : ∀ x, ‖ξ x‖ ≤ ρ) (hη : ∀ x, ‖η x‖ ≤ ρ)
    (hξη : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → ξ x = η x) :
    ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y →
      Smap H (decG C H a ν s) (dirichletOperator H a ν α₀) ιU α₀ φ₀ (pertSource H a δΨ f₁) ξ x =
      Smap H (decG C H a ν s') (dirichletOperator H a ν α₀') ιU α₀' φ₀' (pertSource H a δΨ' f₁') η x := by
  classical
  intro x hxT
  have hxY : (x : CTorus d L N₁ m₁ K) ∈ Y := SYF_subset_Y hxT
  have hd0 : 0 < d := by have := S.hd; omega
  obtain ⟨-, hunit⟩ := hF.2.2 C H S.toCoverBase hκ hM hs N
  obtain ⟨-, hunit'⟩ := hF.2.2 C H S.toCoverBase hκ hM hs' N
  have hδα : Small H (toAlpha H ξ) ρ := small_toAlpha H ξ hξ
  have hδα' : Small H (toAlpha H η) ρ := small_toAlpha H η hη
  have hA : Small H (α₀ + toAlpha H ξ) (gamma1 d / 8) := fun y =>
    ((Small.add hα0 hδα) y).trans hρ
  have hA' : Small H (α₀' + toAlpha H η) (gamma1 d / 8) := fun y =>
    ((Small.add hα0' hδα') y).trans hρ
  have hAeq : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y →
      (α₀ + toAlpha H ξ) y = (α₀' + toAlpha H η) y := by
    intro y hy
    simp only [Pi.add_apply]
    rw [hD.alpha y hy, show toAlpha H ξ y = toAlpha H η y by
      unfold toAlpha; rw [hξη y hy]]
  have hdphi : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) (toAlpha H ξ) (y, i) =
      dphi H (decG C H a ν s') α₀' φ₀' (pertSource H a δΨ' f₁') (toAlpha H η) (y, i) := by
    intro y hy i
    unfold dphi
    rw [liftOp_mulVec, liftOp_mulVec]
    refine dg5'_inner_fp S hY (admPot_of_small hd0 hA) (admPot_of_small hd0 hA')
      (hunit (admPot_of_small hd0 hA)) (hunit' (admPot_of_small hd0 hA')) hs1 hs0 hag hAeq
      (f := fun b => Fsrc φ₀ (pertSource H a δΨ f₁) (toAlpha H ξ) (b, i))
      (f' := fun b => Fsrc φ₀' (pertSource H a δΨ' f₁') (toAlpha H η) (b, i)) ?_ y hy
    intro b hb
    simp only [Fsrc]
    rw [pertSource_congrS hD (SYF_subset_Y hb) i, hD.phi b (SYF_subset_Y hb)]
    congr 2
    unfold toAlpha; rw [hξη b hb]
  -- the geometry of `x`
  obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hxT
  have hzZ' := Finset.mem_filter.1 hzZ
  unfold Smap
  rw [Nmap_explicit, Nmap_explicit]
  congr 1
  refine Nexp_congr ιU ?_ (fun i => by rw [hD.phi x hxY]) (fun i => pertSource_congrS hD hxY i)
    (fun i => hdphi x hxY i) (fun y hy => ?_)
  · intro y
    rw [dirichletOperator_eq_add a ν α₀, dirichletOperator_eq_add a ν α₀']
    simp only [Matrix.add_apply, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy; simp [hD.alpha x hxT]
    · simp [hxy]
  · have hyY : (y : CTorus d L N₁ m₁ K) ∈ Y :=
      hzZ'.2.2.2 y (footprint_row (b := x) hxz α₀ hy)
    exact ⟨fun i => by rw [hD.phi y hyY], fun i => hdphi y hyY i⟩





/-- **Theorem I-4a (e): locality, comparison form.**  Let `𝒞 ⊂ 𝔓`-data, `Y` a union of
nearest-neighbour components of `V(𝒞) ∩ Ω₁`, `S_Y = ⋃_{z ∈ Z_Y} □_z` (so `Core_Y ⊆ S_Y ⊆ Y`), two
parameter vectors `s, s'` that vanish on `𝔓 ∖ 𝒞`, equal `1` off `𝔓` and agree on the cubes of `𝒞`
inside `Y`, and two data sets that agree on `Y`.  Then the solutions of the two decoupled systems
satisfy `δα(s) = δα(s')` on `S_Y` and `δφ(s) = δφ(s')` on `Y ∩ Ω₁`; in particular on `Core_Y`. -/
theorem i4a_local_fpS {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG) (S : FootLocal C H a ν Kc Cx)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : H.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : H.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (Hh : DecHyp H a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) (H' : DecHyp H a ν ιU α₀' φ₀' δΨ' f₁' δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → extS C s P = 1 ∧ extS C s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → extS C s P = 0 ∧ extS C s' P = 0)
    (hag : ∀ P ∈ 𝒞, P ∈ A → extS C s P = extS C s' P)
    (hD : DataAgreeS H N Y (SYF C H a ν X₁ 𝒞 Y) α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {δα δα' : H.Ω 1 → ℂ}
    (hfix : DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα)
    (hsm : Small H δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed C H a ν s' ιU α₀' φ₀' (pertSource H a δΨ' f₁') δα')
    (hsm' : Small H δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → δα x = δα' x) ∧
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
  have hagreeξ : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → ξ x = ξ' x := by
    refine fixed_agree_of_step (T := fun x : H.Ω 1 => (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y)
      (fun u v hu hv huv i hi => ?_) (fun n => ⟨(hit n).1, (hit n).2⟩)
      (fun n => ⟨(hit' n).1, (hit' n).2⟩) hC.ρ_nn
    exact local_step_fpS hF S hκ hM hs hs' Hh.alpha0 H'.alpha0 (hpoly Hh.alpha0)
      hY hs1 hs0 hag hD hu hv huv i hi
  have hδ : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → δα x = δα' x := by
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
  refine dg5'_inner_fp S hY (admPot_of_small hd0 hA) (admPot_of_small hd0 hA')
    (hunit (admPot_of_small hd0 hA)) (hunit' (admPot_of_small hd0 hA')) hs1 hs0 hag
    (fun z hz => ?_) (f := fun b => Fsrc φ₀ (pertSource H a δΨ f₁) δα (b, i))
    (f' := fun b => Fsrc φ₀' (pertSource H a δΨ' f₁') δα' (b, i)) (fun b hb => ?_) y hy
  · simp only [Pi.add_apply]
    rw [hD.alpha z hz, hδ z hz]
  · simp only [Fsrc]
    rw [pertSource_congrS hD (SYF_subset_Y hb) i, hD.phi b (SYF_subset_Y hb), hδ b hb]



end Balaban.Localization.Dec2
