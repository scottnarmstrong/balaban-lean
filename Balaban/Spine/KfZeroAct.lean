/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.KfZero
public import Balaban.LargeField.Base.KF0PolymerLift

/-!
# Scale-`1` activities from local terms on the block tori

A family `P` of local terms on the block tori (`P m Y g` for a set `Y` of blocks of side `s` of the
torus of side `s m` and a source `g`) defines activities on every torus (`blockAct`): on a torus
of side `s m`, the activity of a polymer `X` (`IsPolymer d (s m) s X`) at scale `1` is the local
term of its set of blocks, and every other activity is `0`. The clauses of
`ObservableActivities` follow from the corresponding properties of the family:

* `blockAct_support`: always;
* `blockAct_local`: `P m Y g` depends on `g` at the sites of the blocks of `Y` only;
* `blockAct_analytic`, `blockAct_bound`: analyticity and the bound of the increments of `P`;
* `blockAct_agree`: the two-torus agreement of `P` on the polymers of the quarter box;
* `blockAct_sum`: the activities add up to `∑_Y P m Y g` when `P` vanishes off the connected sets.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Polymer Balaban.Green Balaban.KF0Lift

open scoped Classical

section Act

variable {d N : ℕ}

/-- **The activity of a polymer of the torus of side `s m`**: the local term of its set of blocks,
zero for a non-polymer. -/
noncomputable def blockActCore (s m : ℕ) [NeZero s] [NeZero m]
    (P : ∀ (m : ℕ) [NeZero m], Finset (Torus d m) → (Torus d (s * m) → Fin N → ℂ) → ℂ)
    (X : Finset (Torus d (s * m))) (g : Torus d (s * m) → Fin N → ℂ) : ℂ :=
  if IsPolymer d (s * m) s X then P m (X.image (blockOf d s m)) g else 0

/-- **The activities on every torus**: `blockActCore` on a torus of side `s m` at scale `1`, zero at
the other scales and on tori whose side is not a multiple of `s`. -/
noncomputable def blockAct (s : ℕ) [NeZero s]
    (P : ∀ (m : ℕ) [NeZero m], Finset (Torus d m) → (Torus d (s * m) → Fin N → ℂ) → ℂ) :
    (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ :=
  fun ℓ j X g =>
    if j = 1 then
      if hm : ∃ m : ℕ, 0 < m ∧ ℓ = s * m then
        @blockActCore d N s hm.choose _ ⟨hm.choose_spec.1.ne'⟩ P
          (hm.choose_spec.2 ▸ X) (hm.choose_spec.2 ▸ g)
      else 0
    else 0

variable {s : ℕ} [NeZero s]
  (P : ∀ (m : ℕ) [NeZero m], Finset (Torus d m) → (Torus d (s * m) → Fin N → ℂ) → ℂ)

theorem blockAct_of_ne {j : ℕ} (hj : j ≠ 1) (ℓ : ℕ) (X : Finset (Torus d ℓ))
    (g : Torus d ℓ → Fin N → ℂ) : blockAct s P ℓ j X g = 0 := by
  simp [blockAct, hj]

/-- On a torus of side `s m` the activity at scale `1` is `blockActCore`. -/
theorem blockAct_spec (m : ℕ) [NeZero m] (X : Finset (Torus d (s * m)))
    (g : Torus d (s * m) → Fin N → ℂ) :
    blockAct s P (s * m) 1 X g = blockActCore s m P X g := by
  have hm : ∃ m' : ℕ, 0 < m' ∧ s * m = s * m' := ⟨m, Nat.pos_of_ne_zero (NeZero.ne m), rfl⟩
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hmm : hm.choose = m := Nat.eq_of_mul_eq_mul_left hs hm.choose_spec.2.symm
  simp only [blockAct, ite_true, hm, dite_true]
  have key : ∀ (m₁ : ℕ) (inst : NeZero m₁) (h₁ : s * m = s * m₁), m₁ = m →
      @blockActCore d N s m₁ _ inst P (h₁ ▸ X) (h₁ ▸ g) = blockActCore s m P X g := by
    intro m₁ inst h₁ hmm'
    subst hmm'
    rfl
  exact key hm.choose ⟨hm.choose_spec.1.ne'⟩ hm.choose_spec.2 hmm

end Act

/-- A torus side divisible by `M L^{kf+1}` is `M L m` with `m ≥ 1`. -/
theorem exists_multiple {M L kf ℓ : ℕ} [NeZero ℓ] (hℓ : M * L ^ (kf + 1) ∣ ℓ) :
    ∃ m : ℕ, NeZero m ∧ ℓ = M * L * m := by
  obtain ⟨q, hq⟩ := hℓ
  refine ⟨L ^ kf * q, ⟨fun h0 => NeZero.ne ℓ ?_⟩, ?_⟩
  · rw [hq, pow_succ, show M * (L ^ kf * L) * q = M * L * (L ^ kf * q) by ring, h0, mul_zero]
  · rw [hq, pow_succ]
    ring

section Clauses

variable {d N : ℕ} {M L : ℕ} [NeZero (M * L)]
  (P : ∀ (m : ℕ) [NeZero m], Finset (Torus d m) → (Torus d (M * L * m) → Fin N → ℂ) → ℂ)

theorem blockAct_support {ℓ : ℕ} [NeZero ℓ] (m : ℕ) [NeZero m] (hℓ : ℓ = M * L * m) :
    ActSupportAt d N L M 1 ℓ (blockAct (M * L) P) := by
  intro j X hX g
  by_cases hj : j = 1
  · subst hj
    have hnp : ¬ IsPolymer d ℓ (M * L) X := fun hp =>
      hX ⟨Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩, by rwa [pow_one]⟩
    subst hℓ
    rw [blockAct_spec, blockAct_spec]
    simp only [blockActCore, hnp, ite_false]
  · rw [blockAct_of_ne P hj, blockAct_of_ne P hj]

theorem blockAct_local {ℓ : ℕ} [NeZero ℓ] (m : ℕ) [NeZero m] (hℓ : ℓ = M * L * m)
    (hP : ∀ (Y : Finset (Torus d m)) (g g' : Torus d (M * L * m) → Fin N → ℂ),
      (∀ x, blockOf d (M * L) m x ∈ Y → g x = g' x) → P m Y g = P m Y g') :
    ActLocalAt d N ℓ (blockAct (M * L) P) := by
  intro j X g g' hg
  by_cases hj : j = 1
  · subst hj
    subst hℓ
    rw [blockAct_spec, blockAct_spec]
    unfold blockActCore
    by_cases hX : IsPolymer d (M * L * m) (M * L) X
    · simp only [hX, ite_true]
      refine hP _ g g' fun x hx => hg x ?_
      have := siteSet_image_blockOf (d := d) (s := M * L) (m := m) hX.2.1
      rw [← this]
      exact (mem_siteSet d (M * L) m).2 hx
    · simp only [hX, ite_false]
  · rw [blockAct_of_ne P hj, blockAct_of_ne P hj]

theorem blockAct_analytic {ℓ : ℕ} [NeZero ℓ] (m : ℕ) [NeZero m] (hℓ : ℓ = M * L * m)
    (hAn : ∀ Y : Finset (Torus d m), AnalyticOnNhd ℂ (P m Y)
      {g : Torus d (M * L * m) → Fin N → ℂ | ∑ x, ∑ i, ‖g x i‖ < 1}) :
    ActAnalyticAt d N ℓ (blockAct (M * L) P) := by
  intro j X
  by_cases hj : j = 1
  · subst hj
    subst hℓ
    have : blockAct (M * L) P (M * L * m) 1 X = fun g => blockActCore (M * L) m P X g :=
      funext fun g => blockAct_spec P m X g
    rw [this]
    unfold blockActCore
    by_cases hX : IsPolymer d (M * L * m) (M * L) X
    · simp only [hX, ite_true]
      exact hAn _
    · simp only [hX, ite_false]
      exact analyticOnNhd_const
  · have : blockAct (M * L) P ℓ j X = fun _ => 0 :=
      funext fun g => blockAct_of_ne P hj ℓ X g
    rw [this]
    exact analyticOnNhd_const

theorem blockAct_bound {κ c₉' δ B : ℝ} {ℓ : ℕ} [NeZero ℓ] (m : ℕ) [NeZero m]
    (hℓ : ℓ = M * L * m) (hc : 0 ≤ c₉')
    (hBd : ∀ Y : Finset (Torus d m), IsAnimal (blockGraph d m) Y →
      ∀ g : Torus d (M * L * m) → Fin N → ℂ, ∑ x, ∑ i, ‖g x i‖ < 1 →
        ‖P m Y g - P m Y 0‖ ≤ B * Real.exp (-κ * (Y.card : ℝ)))
    (hB : B ≤ c₉' / 2 * (L : ℝ) ^ (-((1 : ℝ) * (((d : ℝ) - 2) / 2 + δ)))) :
    ActBoundAt d N L M κ c₉' δ 1 ℓ (blockAct (M * L) P) := by
  intro j hj X g hg
  have hj1 : j = 1 := le_antisymm (Finset.mem_Icc.1 hj).2 (Finset.mem_Icc.1 hj).1
  subst hj1
  subst hℓ
  rw [blockAct_spec, blockAct_spec]
  unfold blockActCore
  have hpos : 0 ≤ c₉' / 2 * (L : ℝ) ^ (-(((1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) *
      Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ 1) ^ d) := by
    have := Real.exp_pos (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ 1) ^ d)
    have h2 : 0 ≤ (L : ℝ) ^ (-(((1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  by_cases hX : IsPolymer d (M * L * m) (M * L) X
  · simp only [hX, ite_true]
    have hY := isAnimal_image_blockOf (d := d) (s := M * L) (m := m) hX
    have h1 := hBd _ hY g hg
    have hcard := card_div_eq (d := d) (s := M * L) (m := m) X hX.2.1
    have hexp : Real.exp (-κ * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ 1) ^ d) =
        Real.exp (-κ * ((X.image (blockOf d (M * L) m)).card : ℝ)) := by
      rw [← hcard]
      congr 1
      push_cast
      rw [pow_one]
      ring
    rw [hexp]
    refine h1.trans ?_
    simp only [Nat.cast_one] at hB ⊢
    exact mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le
  · simp only [hX, ite_false, sub_self, norm_zero]
    exact hpos

/-- **The two-torus agreement of the activities.** -/
theorem blockAct_agree {kf : ℕ} (hs : 6 ≤ M * L) (hd : 1 ≤ d)
    (hP : ∀ (m m2 : ℕ) [NeZero m] [NeZero m2] (A : Finset (Fin d → ℤ)),
      (∀ y ∈ A, ∀ μ, 4 * |y μ| < ((M * L * m : ℕ) : ℤ) ∧ 4 * |y μ| < ((M * L * m2 : ℕ) : ℤ)) →
      IsPolymer d (M * L * m) (M * L) (A.image (intToTorus d (M * L * m))) →
      ∀ g : (Fin d → ℤ) → Fin N → ℂ,
        P m2 ((A.image (intToTorus d (M * L * m2))).image (blockOf d (M * L) m2))
            (fun z => g fun μ => ZMod.valMinAbs (n := M * L * m2) (z μ)) =
          P m ((A.image (intToTorus d (M * L * m))).image (blockOf d (M * L) m))
            (fun z => g fun μ => ZMod.valMinAbs (n := M * L * m) (z μ))) :
    ActAgree d N L M kf (blockAct (M * L) P) := by
  intro ℓ ℓ' _ _ hℓ hℓ' j a A g ha hbox
  by_cases hj : j = 1
  · subst hj
    obtain ⟨m, hm, rfl⟩ := exists_multiple hℓ
    obtain ⟨m2, hm2, rfl⟩ := exists_multiple hℓ'
    have hXe : (A.image fun y μ => ((y μ : ℤ) : ZMod (M * L * m))) =
        A.image (intToTorus d (M * L * m)) := rfl
    have hXe2 : (A.image fun y μ => ((y μ : ℤ) : ZMod (M * L * m2))) =
        A.image (intToTorus d (M * L * m2)) := rfl
    rw [hXe, hXe2, blockAct_spec, blockAct_spec, blockAct_spec, blockAct_spec]
    have hbox' : ∀ y ∈ A, ∀ μ, 4 * |y μ| < ((M * L * m : ℕ) : ℤ) ∧
        4 * |y μ| < ((M * L * m2 : ℕ) : ℤ) := hbox
    unfold blockActCore
    by_cases hX : IsPolymer d (M * L * m) (M * L) (A.image (intToTorus d (M * L * m)))
    · obtain ⟨hX', -⟩ := polymer_lift hs hd A hbox' hX
      have h1 := hP m m2 A hbox' hX g
      have h2 := hP m m2 A hbox' hX (fun _ _ => 0)
      simp only [hX, hX', ite_true]
      rw [h1]
      exact congrArg (HSub.hSub _) h2.symm
    · have hX' : ¬ IsPolymer d (M * L * m2) (M * L) (A.image (intToTorus d (M * L * m2))) := by
        intro hX'
        exact hX (polymer_lift hs hd A (fun y hy μ => ⟨(hbox' y hy μ).2, (hbox' y hy μ).1⟩) hX').1
      simp only [hX, hX', ite_false]
  · rw [blockAct_of_ne P hj, blockAct_of_ne P hj, blockAct_of_ne P hj, blockAct_of_ne P hj]

/-- **The activities regroup the local terms.** -/
theorem blockAct_sum {ℓ : ℕ} [NeZero ℓ] (m : ℕ) [NeZero m] (hℓ : ℓ = M * L * m)
    (hz : ∀ (g' : Torus d (M * L * m) → Fin N → ℂ) (Y : Finset (Torus d m)),
      ¬ IsAnimal (blockGraph d m) Y → P m Y g' = 0)
    (g : Torus d ℓ → Fin N → ℂ) :
    ∑ X : Finset (Torus d ℓ), blockAct (M * L) P ℓ 1 X g =
      ∑ Y : Finset (Torus d m), P m Y (hℓ ▸ g) := by
  subst hℓ
  simp only [blockAct_spec]
  unfold blockActCore
  rw [← Finset.sum_filter]
  have hv : ∀ Y ∈ (Finset.univ : Finset (Finset (Torus d m))),
      Y ∉ (Finset.univ : Finset (Finset (Torus d m))).filter (IsAnimal (blockGraph d m)) →
      P m Y g = 0 := by
    intro Y _ hY
    exact hz g Y (by simpa using hY)
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hv]
  refine Finset.sum_nbij' (fun X => X.image (blockOf d (M * L) m))
    (fun Y => siteSet d (M * L) m Y) ?_ ?_ ?_ ?_ ?_
  · intro X hX
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢
    exact isAnimal_image_blockOf hX
  · intro Y hY
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY ⊢
    exact (isPolymer_siteSet_iff Y).mpr hY
  · intro X hX
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX
    exact siteSet_image_blockOf hX.2.1
  · intro Y _
    exact image_siteSet Y
  · intro X _
    rfl

end Clauses

end Balaban.RootFSpine
