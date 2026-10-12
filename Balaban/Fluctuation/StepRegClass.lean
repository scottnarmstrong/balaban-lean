/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepRegTerms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `ClassRegular`, `ClassRegularLoc`, `ClassRegularObs` from regularity along the ray

* `classRegularObs_of_contDiff` (internal): `ℰ_k` and the components of `ℳ_k` smooth along the ray
  give the three named inputs;
* **`classRegularObs_of_analytic`** (and `classRegularLoc_of_analytic`, `classRegular_of_analytic`):
  for any class whose terms are analytic on the `Ξ^c` domains (`StepTermsAnalytic`) given the
  composition-domain inclusion `RayInDomain`;
* **`classRegularObs_zeroClass`** (and the other two): the class with zero old terms but the actual
  background-dependent leading terms `svec φ_k` of `ℳ_k` and `Φ₁ = -β V^{(k)}`, for every source `g`,
  under `RayData` only.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory Set Matrix

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {pp : ℝ} (C : StepClass d L N₁ m₁ k N ϱ)

section FromContDiff

variable {g : Fld d L N₁ m₁ (k + 1) N} (R : S.RayData pp)
  (hE : ∀ q : ℝ × S.E, |q.1| * ‖q.2‖ < pp → ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
    EcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU (S.psiAt q.1 q.2))) q)
  (hM : ∀ q : ℝ × S.E, |q.1| * ‖q.2‖ < pp → ∀ (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N),
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E =>
      McompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU (S.psiAt q.1 q.2)) g y i) q)

include hE in
theorem contDiffAt_dE_ray {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => S.dE C (S.psiAt q.1 q.2)) q :=
  (hE q hq).sub contDiffAt_const

include hM in
theorem contDiffAt_dF_ray {q : ℝ × S.E} (hq : |q.1| * ‖q.2‖ < pp) :
    ContDiffAt ℝ ⊤ (fun q : ℝ × S.E => S.dF C g (S.psiAt q.1 q.2)) q := by
  unfold dF
  simp only [FcompAt_eq_pair]
  refine ContDiffAt.sub (ContDiffAt.sum fun x _ => ContDiffAt.sum fun i _ => ?_) contDiffAt_const
  exact contDiffAt_const.mul (hM q hq x i)

include hE hM in
theorem classRegular_of_contDiff (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp) : S.ClassRegular C g := by
  obtain ⟨U₁, hEf⟩ := S.isC1Family_trunc (f := fun q : ℝ × S.E => S.dE C (S.psiAt q.1 q.2))
    hp₁ hlt fun q hq => (contDiffAt_dE_ray C hE hq).of_le (by exact_mod_cast le_top)
  obtain ⟨U₂, hFf⟩ := S.isC1Family_trunc (f := fun q : ℝ × S.E => S.dF C g (S.psiAt q.1 q.2))
    hp₁ hlt fun q hq => (contDiffAt_dF_ray C hM hq).of_le (by exact_mod_cast le_top)
  have hopen : IsOpen (U₁ ∩ U₂) := hEf.isOpen.inter hFf.isOpen
  have hIcc : Set.Icc (0 : ℝ) 1 ⊆ U₁ ∩ U₂ :=
    fun s hs => ⟨hEf.Icc_subset hs, hFf.Icc_subset hs⟩
  exact ⟨⟨U₁ ∩ U₂, _, _, hEf.restrict hopen Set.inter_subset_left hIcc,
    hFf.restrict hopen Set.inter_subset_right hIcc⟩⟩

include R hE in
theorem contDiffAt_Phi1_segment (hlt : S.p₁ < pp) {x : S.E} (hx : ‖x‖ ≤ S.p₁) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 1 (S.Phi1 C) (s • S.shiftU x) := by
  have hq : |((1 : ℝ), S.unshiftU (s • S.shiftU x)).1| *
      ‖((1 : ℝ), S.unshiftU (s • S.shiftU x)).2‖ < pp := R.unshift_ray hlt hx hs
  have h1 : ContDiffAt ℝ 1 (fun y => S.Vk (S.psi0 + y)) (s • S.shiftU x) :=
    (R.contDiffAt_Vk_shift hlt hx hs).of_le (by exact_mod_cast le_top)
  have h2 : ContDiffAt ℝ 1 (fun y => S.dE C (S.psi0 + y)) (s • S.shiftU x) :=
    (R.contDiffAt_shift (G := S.dE C) (n := 1)
      ((contDiffAt_dE_ray C hE hq).of_le (by exact_mod_cast le_top)))
  exact (contDiffAt_const.mul h1).add h2

include R hE hM in
theorem classRegularLoc_of_contDiff (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp) :
    S.ClassRegularLoc C g := by
  refine ⟨classRegular_of_contDiff C hE hM hp₁ hlt, ?_⟩
  obtain ⟨O, hO, hcd, hT⟩ := exists_open_contDiffOn (f := S.Phi1 C)
    (T := {y | ∃ (x : S.E) (s : ℝ), ‖x‖ ≤ S.p₁ ∧ s ∈ Icc (0 : ℝ) 1 ∧ y = s • S.shiftU x})
    (by
      rintro y ⟨x, s, hx, hs, rfl⟩
      exact contDiffAt_Phi1_segment C R hE hlt hx hs)
  exact ⟨O, hO, hcd, fun x hx s hs => hT ⟨x, s, hx, hs, rfl⟩⟩

include R hE hM in
theorem classRegularObs_of_contDiff (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp) :
    S.ClassRegularObs C g := by
  refine ⟨classRegularLoc_of_contDiff C R hE hM hp₁ hlt, fun y i => ?_⟩
  obtain ⟨U, hU⟩ := S.isC1Family_trunc (pp := pp)
    (f := fun q : ℝ × S.E =>
      McompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) (S.dataU (S.psiAt q.1 q.2)) g y i)
    hp₁ hlt fun q hq => (hM q hq y i).of_le (by exact_mod_cast le_top)
  exact ⟨U, _, hU⟩

end FromContDiff

section Analytic

variable {g : Fld d L N₁ m₁ (k + 1) N} {A : ℕ → ℝ} {μ : ℝ} {ε : ℕ → ℝ}
  (R : S.RayData pp) (hT : StepTermsAnalytic C A μ ε) (hD : S.RayInDomain C g A μ ε pp)
  (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)

include R hT hD hp₁ hlt in
/-- **`ClassRegular` for a class with analytic terms**, given the composition-domain inclusion. -/
theorem classRegular_of_analytic : S.ClassRegular C g :=
  classRegular_of_contDiff C (fun _ hq => contDiffAt_EcompRay C R hT hD hq)
    (fun _ hq y i => contDiffAt_McompRay C R hT hD hq y i) hp₁ hlt

include R hT hD hp₁ hlt in
/-- **`ClassRegularLoc` for a class with analytic terms**, given the composition-domain inclusion. -/
theorem classRegularLoc_of_analytic : S.ClassRegularLoc C g :=
  classRegularLoc_of_contDiff C R (fun _ hq => contDiffAt_EcompRay C R hT hD hq)
    (fun _ hq y i => contDiffAt_McompRay C R hT hD hq y i) hp₁ hlt

include R hT hD hp₁ hlt in
/-- **`ClassRegularObs` for a class with analytic terms**, given the composition-domain inclusion. -/
theorem classRegularObs_of_analytic : S.ClassRegularObs C g :=
  classRegularObs_of_contDiff C R (fun _ hq => contDiffAt_EcompRay C R hT hD hq)
    (fun _ hq y i => contDiffAt_McompRay C R hT hD hq y i) hp₁ hlt

end Analytic

end StepSetting

section Zero

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {pp : ℝ}

theorem McompAt_zero_eq (m₀ : ℕ) (a : ℕ → ℝ) (ν : ℝ) {K j : ℕ} (hj : j ≤ K)
    (D : BgData (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) N)
    (g : Fld d L N₁ m₁ K N) (x : CTorus d L N₁ m₁ K) (i : Fin N) :
    McompAt m₀ (zeroTerms d L N₁ m₁ K N ϱ) a ν hj D g x i =
      svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        (bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν D)
        x i := by
  simp [McompAt, Mloc_zero]

/-- **`ClassRegularObs` for the class with zero old terms** (non-degenerate: `ℳ_k = svec φ_k`,
`Φ₁ = -β V^{(k)}`, `ℱ_k = ⟨g, φ_k⟩`), for every source `g`. -/
theorem classRegularObs_zeroClass (R : S.RayData pp) (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (g : Fld d L N₁ m₁ (k + 1) N) :
    S.ClassRegularObs (zeroClass d L N₁ m₁ k N ϱ) g := by
  refine StepSetting.classRegularObs_of_contDiff _ R (fun q _ => ?_) (fun q hq y i => ?_) hp₁ hlt
  · have : (fun q : ℝ × S.E => EcompAt (zeroClass d L N₁ m₁ k N ϱ).m₀
        (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν (Nat.le_succ k) (S.dataU (S.psiAt q.1 q.2))) =
        fun _ => 0 := funext fun q => EcompAt_zero _ _ _ _ _
    rw [this]; exact contDiffAt_const
  · have : (fun q : ℝ × S.E => McompAt (zeroClass d L N₁ m₁ k N ϱ).m₀
        (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν (Nat.le_succ k) (S.dataU (S.psiAt q.1 q.2)) g y i) =
        S.bgComp y i := funext fun q => McompAt_zero_eq _ _ _ _ _ _ _ _
    rw [this]; exact R.contDiffAt_bgComp y i hq

theorem classRegularLoc_zeroClass (R : S.RayData pp) (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (g : Fld d L N₁ m₁ (k + 1) N) : S.ClassRegularLoc (zeroClass d L N₁ m₁ k N ϱ) g :=
  (classRegularObs_zeroClass R hp₁ hlt g).toClassRegularLoc

theorem classRegular_zeroClass (R : S.RayData pp) (hp₁ : 0 < S.p₁) (hlt : S.p₁ < pp)
    (g : Fld d L N₁ m₁ (k + 1) N) : S.ClassRegular (zeroClass d L N₁ m₁ k N ϱ) g :=
  (classRegularObs_zeroClass R hp₁ hlt g).toClassRegular

end Zero

end Balaban.Fluctuation
