/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusStepGeometry
public import Balaban.Inhabited.StepTowerScale
import Mathlib.Tactic.Linarith

/-!
# The data of one step on two tori

Two raw background data on the step tori of sides `N₁ L^m₁ L^K` and `N₁' L^m₁ L^K` agree on a set
`R` of sites of the first torus when their two components agree under the identification
`boxMap` of the centred boxes (`RawBoxAgree`); the same relation for sources is `SrcBoxAgree`.
A datum on one torus is not extended by zero to the other one (this is not admissible in general):
the correspondence is a relation between two data, each admissible on its own torus.

* `RawBoxAgree`, `SrcBoxAgree`: monotone, reflexive on the box when the two tori coincide,
  symmetric through the inverse box map.
* The zero-class base data `unitBg` of the steps on `N₁` and `N₁'` agree on every set `R`
  (`rawBoxAgree_step_D'`); the constants of the two steps coincide (`step_consts_eq`).
* `pushSrc R g` is the source on the second torus equal to `g` composed with the inverse box map
  on the image of `R` and zero elsewhere; it has the same `ℓ¹` norm as `g` restricted to `R`.
* The sources pulled back from one function on `ℤ^d` through `ZMod.valMinAbs` on two tori agree
  on the box (`pullSrc_boxAgree`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.Polymer Balaban.Multiscale
  Balaban.Background Balaban.Localization.I5Inhabited

section Defs

variable {d L N₁ N₁' m₁ K N : ℕ}

/-- Two raw data `(Ψ, h)` on the step tori of `N₁` and `N₁'` agree on the set `R` of sites of the
first torus under the box map. -/
def RawBoxAgree (R : Set (Torus d ((N₁ * L ^ m₁) * L ^ K)))
    (u : RawData d L (N₁ * L ^ m₁) K N) (u' : RawData d L (N₁' * L ^ m₁) K N) : Prop :=
  ∀ x ∈ R, u.1 x = u'.1 (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K) x) ∧
    u.2 x = u'.2 (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K) x)

end Defs

/-- Two sources on tori of sides `n`, `n'` agree on the set `R` of sites of the first torus under
the box map. -/
def SrcBoxAgree {d n n' N : ℕ} (R : Set (Torus d n)) (g : Torus d n → Fin N → ℂ)
    (g' : Torus d n' → Fin N → ℂ) : Prop :=
  ∀ x ∈ R, ∀ i, g x i = g' (boxMap n n' x) i

/-- The source on the second torus equal to `g` composed with the inverse box map on the image of
`R`, and `0` elsewhere. -/
def pushSrc {d N : ℕ} (n n' : ℕ) (R : Finset (Torus d n)) (g : Torus d n → Fin N → ℂ) :
    Torus d n' → Fin N → ℂ :=
  fun y i => if y ∈ R.image (boxMap n n') then g (boxMap n' n y) i else 0

/-! ### Generic lemmas -/

section Generic

variable {d n n' r N : ℕ}

theorem boxMap_self (c : Torus d n) : boxMap n n c = c := by
  funext μ
  exact ZMod.coe_valMinAbs _

theorem SrcBoxAgree.mono {R R' : Set (Torus d n)} {g : Torus d n → Fin N → ℂ}
    {g' : Torus d n' → Fin N → ℂ} (h : SrcBoxAgree R g g') (hR : R' ⊆ R) :
    SrcBoxAgree R' g g' := fun x hx i => h x (hR hx) i

theorem srcBoxAgree_refl {R : Set (Torus d n)} (g : Torus d n → Fin N → ℂ) : SrcBoxAgree R g g :=
  fun x hx i => by rw [boxMap_self x]

theorem SrcBoxAgree.symm (hm' : 2 * r + 1 < n') {R : Set (Torus d n)}
    (hR : ∀ x ∈ R, InBox d r n x) {g : Torus d n → Fin N → ℂ} {g' : Torus d n' → Fin N → ℂ}
    (h : SrcBoxAgree R g g') : SrcBoxAgree (boxMap n n' '' R) g' g := by
  rintro _ ⟨x, hx, rfl⟩ i
  rw [boxMap_boxMap hm' (hR x hx)]
  exact (h x hx i).symm

theorem RawBoxAgree.mono {L N₁ N₁' m₁ K : ℕ} {R R' : Set (Torus d ((N₁ * L ^ m₁) * L ^ K))}
    {u : RawData d L (N₁ * L ^ m₁) K N} {u' : RawData d L (N₁' * L ^ m₁) K N}
    (h : RawBoxAgree R u u') (hR : R' ⊆ R) : RawBoxAgree R' u u' :=
  fun x hx => h x (hR hx)

theorem rawBoxAgree_refl {L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁]
    (R : Set (Torus d ((N₁ * L ^ m₁) * L ^ K)))
    (u : RawData d L (N₁ * L ^ m₁) K N) : RawBoxAgree (N₁' := N₁) R u u :=
  fun x hx => by rw [boxMap_self x]; exact ⟨rfl, rfl⟩

theorem RawBoxAgree.symm {L N₁ N₁' m₁ K : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁'] {r : ℕ}
    (hm' : 2 * r + 1 < (N₁' * L ^ m₁) * L ^ K)
    {R : Set (Torus d ((N₁ * L ^ m₁) * L ^ K))} (hR : ∀ x ∈ R, InBox d r _ x)
    {u : RawData d L (N₁ * L ^ m₁) K N} {u' : RawData d L (N₁' * L ^ m₁) K N}
    (h : RawBoxAgree R u u') :
    RawBoxAgree (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K) '' R) u' u := by
  rintro _ ⟨x, hx, rfl⟩
  rw [boxMap_boxMap hm' (hR x hx)]
  exact ⟨(h x hx).1.symm, (h x hx).2.symm⟩

/-- For the raw data of two background data the relation is agreement of `Ψ` and `h`. -/
theorem rawBoxAgree_rawOf_iff {L N₁ N₁' m₁ K : ℕ} [NeZero L] [NeZero N₁] [NeZero N₁'] {ϱ ϱ' : ℝ}
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {G' : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'}
    (R : Set (Torus d ((N₁ * L ^ m₁) * L ^ K))) (D : BgData G N) (D' : BgData G' N) :
    RawBoxAgree R (rawOf D) (rawOf D') ↔ ∀ x ∈ R,
      D.Ψ x = D'.Ψ (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K) x) ∧
      D.h x = D'.h (boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K) x) := Iff.rfl

/-! ### Sources -/

theorem pushSrc_boxMap (hm' : 2 * r + 1 < n') {R : Finset (Torus d n)}
    (hR : ∀ x ∈ R, InBox d r n x) (g : Torus d n → Fin N → ℂ) {x : Torus d n} (hx : x ∈ R)
    (i : Fin N) : pushSrc n n' R g (boxMap n n' x) i = g x i := by
  have h := Finset.mem_image_of_mem (boxMap n n') hx
  simp only [pushSrc, h, ↓reduceIte, boxMap_boxMap hm' (hR x hx)]

theorem pushSrc_of_notMem {R : Finset (Torus d n)} (g : Torus d n → Fin N → ℂ)
    {y : Torus d n'} (hy : y ∉ R.image (boxMap n n')) (i : Fin N) :
    pushSrc n n' R g y i = 0 := by
  simp only [pushSrc, hy, ↓reduceIte]

theorem srcBoxAgree_pushSrc (hm' : 2 * r + 1 < n') {R : Finset (Torus d n)}
    (hR : ∀ x ∈ R, InBox d r n x) (g : Torus d n → Fin N → ℂ) :
    SrcBoxAgree (↑R : Set (Torus d n)) g (pushSrc n n' R g) :=
  fun _ hx i => (pushSrc_boxMap hm' hR g hx i).symm

theorem pushSrc_norm_sum [NeZero n] [NeZero n'] (hm' : 2 * r + 1 < n') {R : Finset (Torus d n)}
    (hR : ∀ x ∈ R, InBox d r n x) (g : Torus d n → Fin N → ℂ) :
    ∑ y, ∑ i, ‖pushSrc n n' R g y i‖ = ∑ x ∈ R, ∑ i, ‖g x i‖ := by
  have h1 : ∑ y, ∑ i, ‖pushSrc n n' R g y i‖ =
      ∑ y ∈ R.image (boxMap n n'), ∑ i, ‖pushSrc n n' R g y i‖ := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun y _ hy => ?_)
    simp [pushSrc_of_notMem g hy]
  rw [h1, Finset.sum_image (fun a ha b hb h => boxMap_inj (hm' := hm') (hR a ha) (hR b hb) h)]
  exact Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun i _ => by
    rw [pushSrc_boxMap hm' hR g hx i]))

theorem pushSrc_norm_sum_le [NeZero n] [NeZero n'] (hm' : 2 * r + 1 < n') {R : Finset (Torus d n)}
    (hR : ∀ x ∈ R, InBox d r n x) (g : Torus d n → Fin N → ℂ) :
    ∑ y, ∑ i, ‖pushSrc n n' R g y i‖ ≤ ∑ x, ∑ i, ‖g x i‖ := by
  rw [pushSrc_norm_sum hm' hR g]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-! ### The root's pull-back through `valMinAbs` -/

/-- `boxMap` is, by definition, the pull-back of the centred representative. -/
theorem boxMap_eq_valMinAbs (c : Torus d n) :
    boxMap n n' c = fun μ => (((c μ).valMinAbs : ℤ) : ZMod n') := rfl

/-- The source on the torus of side `n` pulled back from `g` on `ℤ^d` through `ZMod.valMinAbs`,
in the form of the clause of Root-F. -/
theorem pullSrc_boxAgree (hm' : 2 * r + 1 < n') {R : Set (Torus d n)}
    (hR : ∀ x ∈ R, InBox d r n x) (g : (Fin d → ℤ) → Fin N → ℂ) :
    SrcBoxAgree R (fun z : Torus d n => g fun μ => ZMod.valMinAbs (n := n) (z μ))
      (fun z : Torus d n' => g fun μ => ZMod.valMinAbs (n := n') (z μ)) := by
  intro x hx i
  have : (fun μ => ZMod.valMinAbs (n := n') (boxMap n n' x μ)) =
      fun μ => ZMod.valMinAbs (n := n) (x μ) := funext (valMinAbs_boxMap hm' (hR x hx))
  simp only [this]

/-- The pulled-back source at the cast of an integer point of the box is `g` there. -/
theorem pull_intCast (hm : 2 * r + 1 < n) (g : (Fin d → ℤ) → Fin N → ℂ) {a : Fin d → ℤ}
    (ha : ∀ μ, |a μ| ≤ r) :
    (fun z : Torus d n => g fun μ => ZMod.valMinAbs (n := n) (z μ))
      (fun μ => (a μ : ZMod n)) = g a := by
  have : (fun μ => ZMod.valMinAbs (n := n) ((a μ : ℤ) : ZMod n)) = a :=
    funext fun μ => valMinAbs_intCast_of_abs_le hm (ha μ)
  simp only [this]

/-- A quarter-box bound `4 |a μ| < n` with `1 ≤ r`, `4 r < n` gives the margin `2 r + 1 < n`. -/
theorem two_r_one_lt_of_four {r n : ℕ} (hr : 1 ≤ r) (h : 4 * r < n) : 2 * r + 1 < n := by omega

end Generic

/-! ### The zero-class base data -/

section Step

variable {κmin : ℝ} (T : Inhabited.StepTower κmin) {k : ℕ} (hk : 1 ≤ k) {N₁ N₁' : ℕ} [NeZero N₁]
  [NeZero N₁'] (ν β p₁ : ℝ)

/-- The constants of the steps on `N₁` and `N₁'` coincide. -/
theorem step_consts_eq :
    (T.step k hk N₁ ν β p₁).β = (T.step k hk N₁' ν β p₁).β ∧
    (T.step k hk N₁ ν β p₁).ν = (T.step k hk N₁' ν β p₁).ν ∧
    (T.step k hk N₁ ν β p₁).a = (T.step k hk N₁' ν β p₁).a ∧
    (T.step k hk N₁ ν β p₁).a₁ = (T.step k hk N₁' ν β p₁).a₁ ∧
    (T.step k hk N₁ ν β p₁).p₁ = (T.step k hk N₁' ν β p₁).p₁ ∧
    (T.step k hk N₁ ν β p₁).δ = (T.step k hk N₁' ν β p₁).δ ∧
    (T.step k hk N₁ ν β p₁).betaU = (T.step k hk N₁' ν β p₁).betaU ∧
    (T.step k hk N₁ ν β p₁).h₀ = (T.step k hk N₁' ν β p₁).h₀ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The base data `unitBg` of the zero-class steps on `N₁` and `N₁'` agree on every set `R` of
sites: both are the constant unit vector field `Ψ`, and the constant `h₀`, at every site (the
generating sets are the whole-lattice level sets, so `dataSites` is everything).  No margin is
needed. -/
theorem rawBoxAgree_step_D' (R : Set (CTorus 3 3 N₁ T.m₁ (k + 1))) :
    RawBoxAgree R (rawOf (T.step k hk N₁ ν β p₁).D') (rawOf (T.step k hk N₁' ν β p₁).D') := by
  intro x _
  have hΩ : ∀ (M : ℕ) [NeZero M] (y : CTorus 3 3 M T.m₁ (k + 1)),
      y ∈ (Inhabited.LevelStep.lvTop M T.m₁ k (rhoSep T.m₁)).Ω 1 := fun M _ y => by
    rw [Inhabited.LevelStep.lvTop_Ω]; simp
  refine ⟨funext fun i => ?_, funext fun i => ?_⟩
  · show (Inhabited.unitBg (Inhabited.LevelStep.lvTop N₁ T.m₁ k (rhoSep T.m₁)) Fluctuation.hN2
      (Inhabited.unitVec Fluctuation.hN2)).Ψ x i = (Inhabited.unitBg (Inhabited.LevelStep.lvTop N₁' T.m₁ k (rhoSep T.m₁))
      Fluctuation.hN2 (Inhabited.unitVec Fluctuation.hN2)).Ψ _ i
    rw [Inhabited.unitBg_Ψ_of_mem _ Fluctuation.hN2 (Inhabited.unitVec Fluctuation.hN2) ((mem_dataSites _).2 (Or.inl (hΩ N₁ x))),
      Inhabited.unitBg_Ψ_of_mem _ Fluctuation.hN2 (Inhabited.unitVec Fluctuation.hN2) ((mem_dataSites _).2 (Or.inl (hΩ N₁' _)))]
  · show (Inhabited.unitBg (Inhabited.LevelStep.lvTop N₁ T.m₁ k (rhoSep T.m₁)) Fluctuation.hN2
      (Inhabited.unitVec Fluctuation.hN2)).h x i = (Inhabited.unitBg (Inhabited.LevelStep.lvTop N₁' T.m₁ k (rhoSep T.m₁))
      Fluctuation.hN2 (Inhabited.unitVec Fluctuation.hN2)).h _ i
    rw [Inhabited.unitBg_h_of_mem _ Fluctuation.hN2 (Inhabited.unitVec Fluctuation.hN2) (hΩ N₁ x),
      Inhabited.unitBg_h_of_mem _ Fluctuation.hN2 (Inhabited.unitVec Fluctuation.hN2) (hΩ N₁' _)]

end Step

end Balaban.Polymer.TwoTorusStep
