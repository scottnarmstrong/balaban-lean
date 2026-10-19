/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.KfZero
public import Balaban.LargeField.Base.KF0PolymerLift
public import Balaban.LargeField.Base.KF0SmallUniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The all-good sector input from the product-cutoff gas (A7-1 (b)–(e))

`KF0GoodSectorInput` (`Spine/KfZero.lean`) asks for scale-`1` activities `a` and vacuum terms `E`
with `Z_∅(g) = exp(E + ⟨g, h⟩ + ∑_X a(X; g))` in the form of `ObservableActivities`. The landed
files `KF0AllGoodGas`, `KF0AllPlusGas`, `KF0F1Assembly` expand the *product-cutoff* part of the
chart integral at a real source. This file supplies the items (b)–(e) of
`notes/phase1/SPINE.md`, A7-1, for that part, and states item (a) as a named input.

* (b) the complex source: `KF0HaloAffine`, `KF0AllPlusComplex`, `KF0AllPlusGasC`: the activities are
  affine in the source, the local terms `kf0PY` of the gas are analytic on the unit `ℓ¹` ball
  (`kf0PY_analyticOnNhd`) and the cutoff integral at a complex source is
  `(1 - τ)^{|Λ|} e^{⟨g, h⟩} exp(∑_Y P(Y)(g))` (`kf0CutIntegral_eq`);
* (c) the measurable walk terms with clipping: `KF0AllPlusGas` (`measurable_f1SiteHalo`, `clip`) at a
  real source, `measurable_gasTermC` at a complex source;
* (d) the regrouping onto `IsPolymer d ℓ (M L)` and the exact two-torus agreement: `kf0GoodAct`
  (`kf0ActCore`: the local term at the blocks of a polymer, zero otherwise), `kf0GoodAct_sum`
  (the activities add up to the series of the gas), `kf0GoodAct_agree` (`KF0BoxLift`,
  `KF0BlockLift`, `KF0PolymerLift`: the walks, halos and polymers of two tori correspond inside the
  quarter box);
* (e) the amplitude: `kf0GoodAct_bound` with the constant `2 · 64 e H₀ e^{-2κ₀}` of the gas
  (`kf0_gas_facts`), `H₀ = 2(1 + 2d) s^d ε`, and `ε` small (`kf0_choose_eps`, `kf0_small_uniform`).

`KF0ThresholdInput` is item (a): the physical threshold is not local in the Gaussian variables
(LF-BASE-KF0 E.4), and the input says that `Z_∅` is the cutoff integral times the exponential of a
gas `r` of defects, at half the amplitude. `kf0GoodSectorInput_of_threshold` is the reduction
`KF0GoodSectorInput ⇐ (a) + (b)–(e)` under the typing `M ≥ 3 (κ + 2κ₀ + 4) 3^d (2d+1) L`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Polymer Balaban.Green MeasureTheory Balaban.LargeField.SphereChart
  Balaban.LargeField.KF0AllPlus Balaban.KF0Lift

open scoped Classical

section GoodAct

variable {d N n : ℕ} {h : EuclideanSpace ℝ (Fin N)}

/-- **The activity of a polymer of the torus of side `s m`**: the local term of the all-plus gas
at the set of its blocks, zero for a non-polymer. -/
noncomputable def kf0ActCore (s m : ℕ) [NeZero s] [NeZero m]
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ) (pc : Measure (perp h))
    (X : Finset (Torus d (s * m))) (g : Torus d (s * m) → Fin N → ℂ) : ℂ :=
  if IsPolymer d (s * m) s X then kf0PY e β ν p pc (X.image (blockOf d s m)) g else 0

/-- **The all-good activities on every torus** `ℓ = s m`, in the form of `ObservableActivities` at
scale `1`, and zero at the other scales and on tori whose side is not a multiple of `s`. -/
noncomputable def kf0GoodAct (s : ℕ) [NeZero s] (e : OrthonormalBasis (Fin n) ℝ (perp h))
    (β ν p : ℝ) (pc : Measure (perp h)) :
    (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ :=
  fun ℓ j X g =>
    if j = 1 then
      if hm : ∃ m : ℕ, 0 < m ∧ ℓ = s * m then
        @kf0ActCore d N n h s hm.choose _ ⟨hm.choose_spec.1.ne'⟩ e β ν p pc
          (hm.choose_spec.2 ▸ X) (hm.choose_spec.2 ▸ g)
      else 0
    else 0

theorem kf0GoodAct_of_ne {s : ℕ} [NeZero s] (e : OrthonormalBasis (Fin n) ℝ (perp h))
    (β ν p : ℝ) (pc : Measure (perp h)) {j : ℕ} (hj : j ≠ 1) (ℓ : ℕ) (X : Finset (Torus d ℓ))
    (g : Torus d ℓ → Fin N → ℂ) : kf0GoodAct s e β ν p pc ℓ j X g = 0 := by
  simp [kf0GoodAct, hj]

/-- On a torus of side `s m` the activity at scale `1` is `kf0ActCore`. -/
theorem kf0GoodAct_spec {s : ℕ} [NeZero s] (e : OrthonormalBasis (Fin n) ℝ (perp h))
    (β ν p : ℝ) (pc : Measure (perp h)) (m : ℕ) [NeZero m] (X : Finset (Torus d (s * m)))
    (g : Torus d (s * m) → Fin N → ℂ) :
    kf0GoodAct s e β ν p pc (s * m) 1 X g = kf0ActCore s m e β ν p pc X g := by
  have hm : ∃ m' : ℕ, 0 < m' ∧ s * m = s * m' := ⟨m, Nat.pos_of_ne_zero (NeZero.ne m), rfl⟩
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hmm : hm.choose = m := Nat.eq_of_mul_eq_mul_left hs hm.choose_spec.2.symm
  simp only [kf0GoodAct, ite_true, hm, dite_true]
  have key : ∀ (m₁ : ℕ) (inst : NeZero m₁) (h₁ : s * m = s * m₁), m₁ = m →
      @kf0ActCore d N n h s m₁ _ inst e β ν p pc (h₁ ▸ X) (h₁ ▸ g) =
        kf0ActCore s m e β ν p pc X g := by
    intro m₁ inst h₁ hmm'
    subst hmm'
    rfl
  exact key hm.choose ⟨hm.choose_spec.1.ne'⟩ hm.choose_spec.2 hmm

end GoodAct

section Clauses

variable {d N n : ℕ} {h : EuclideanSpace ℝ (Fin N)} {M L : ℕ} [NeZero (M * L)]
  (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ) (pc : Measure (perp h))

theorem kf0GoodAct_support {ℓ : ℕ} [NeZero ℓ] (m : ℕ) [NeZero m] (hℓ : ℓ = M * L * m) :
    ActSupportAt d N L M 1 ℓ (kf0GoodAct (M * L) e β ν p pc) := by
  intro j X hX g
  by_cases hj : j = 1
  · subst hj
    have hnp : ¬ IsPolymer d ℓ (M * L) X := fun hp =>
      hX ⟨Finset.mem_Icc.2 ⟨le_rfl, le_rfl⟩, by rwa [pow_one]⟩
    subst hℓ
    rw [kf0GoodAct_spec, kf0GoodAct_spec]
    simp only [kf0ActCore, hnp, ite_false]
  · rw [kf0GoodAct_of_ne e β ν p pc hj, kf0GoodAct_of_ne e β ν p pc hj]

theorem kf0GoodAct_local {ℓ : ℕ} [NeZero ℓ] (m : ℕ) [NeZero m] (hℓ : ℓ = M * L * m) :
    ActLocalAt d N ℓ (kf0GoodAct (M * L) e β ν p pc) := by
  intro j X g g' hg
  by_cases hj : j = 1
  · subst hj
    subst hℓ
    rw [kf0GoodAct_spec, kf0GoodAct_spec]
    unfold kf0ActCore
    by_cases hX : IsPolymer d (M * L * m) (M * L) X
    · simp only [hX, ite_true]
      refine kf0PY_congr e β ν p pc _ fun x hx => hg x ?_
      have := siteSet_image_blockOf (d := d) (s := M * L) (m := m) hX.2.1
      rw [← this]
      exact (mem_siteSet d (M * L) m).2 hx
    · simp only [hX, ite_false]
  · rw [kf0GoodAct_of_ne e β ν p pc hj, kf0GoodAct_of_ne e β ν p pc hj]

theorem kf0GoodAct_analytic {ℓ : ℕ} [NeZero ℓ] (m : ℕ) [NeZero m] (hℓ : ℓ = M * L * m)
    (hAn : ∀ Y : Finset (Torus d m), AnalyticOnNhd ℂ (kf0PY e β ν p pc Y)
      {g : Torus d (M * L * m) → Fin N → ℂ | ∑ x, ∑ i, ‖g x i‖ < 1}) :
    ActAnalyticAt d N ℓ (kf0GoodAct (M * L) e β ν p pc) := by
  intro j X
  by_cases hj : j = 1
  · subst hj
    subst hℓ
    have : kf0GoodAct (M * L) e β ν p pc (M * L * m) 1 X = fun g => kf0ActCore (M * L) m e β ν p pc X g :=
      funext fun g => kf0GoodAct_spec e β ν p pc m X g
    rw [this]
    unfold kf0ActCore
    by_cases hX : IsPolymer d (M * L * m) (M * L) X
    · simp only [hX, ite_true]
      exact hAn _
    · simp only [hX, ite_false]
      exact analyticOnNhd_const
  · have : kf0GoodAct (M * L) e β ν p pc ℓ j X = fun _ => 0 :=
      funext fun g => kf0GoodAct_of_ne e β ν p pc hj ℓ X g
    rw [this]
    exact analyticOnNhd_const

end Clauses

section Bound

variable {d N n : ℕ} {h : EuclideanSpace ℝ (Fin N)} {M L : ℕ} [NeZero (M * L)]
  (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ) (pc : Measure (perp h))

theorem kf0GoodAct_bound {κ c₉' δ B : ℝ} {ℓ : ℕ} [NeZero ℓ] (m : ℕ) [NeZero m]
    (hℓ : ℓ = M * L * m) (hc : 0 ≤ c₉')
    (hBd : ∀ Y : Finset (Torus d m), IsAnimal (blockGraph d m) Y →
      ∀ g : Torus d (M * L * m) → Fin N → ℂ, ∑ x, ∑ i, ‖g x i‖ < 1 →
        ‖kf0PY (s := M * L) (m' := m) e β ν p pc Y g - kf0PY (s := M * L) (m' := m) e β ν p pc Y 0‖ ≤ B * Real.exp (-κ * (Y.card : ℝ)))
    (hB : B ≤ c₉' / 2 * (L : ℝ) ^ (-((1 : ℝ) * (((d : ℝ) - 2) / 2 + δ)))) :
    ActBoundAt d N L M κ c₉' δ 1 ℓ (kf0GoodAct (M * L) e β ν p pc) := by
  intro j hj X g hg
  have hj1 : j = 1 := le_antisymm (Finset.mem_Icc.1 hj).2 (Finset.mem_Icc.1 hj).1
  subst hj1
  subst hℓ
  rw [kf0GoodAct_spec, kf0GoodAct_spec]
  unfold kf0ActCore
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

end Bound

section Agreement

variable {d N n : ℕ} {h : EuclideanSpace ℝ (Fin N)} {M L : ℕ} [NeZero (M * L)]
  (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ) (pc : Measure (perp h))

/-- A torus side divisible by `M L^{kf+1}` is `M L m` with `m ≥ 1`. -/
theorem exists_multiple {M L kf ℓ : ℕ} [NeZero ℓ] (hℓ : M * L ^ (kf + 1) ∣ ℓ) :
    ∃ m : ℕ, NeZero m ∧ ℓ = M * L * m := by
  obtain ⟨q, hq⟩ := hℓ
  refine ⟨L ^ kf * q, ⟨fun h0 => NeZero.ne ℓ ?_⟩, ?_⟩
  · rw [hq, pow_succ, show M * (L ^ kf * L) * q = M * L * (L ^ kf * q) by ring, h0, mul_zero]
  · rw [hq, pow_succ]
    ring

/-- **The two-torus agreement of the all-good activities (d).** -/
theorem kf0GoodAct_agree {kf : ℕ} (hs : 6 ≤ M * L) (hd : 1 ≤ d) [IsProbabilityMeasure pc] :
    ActAgree d N L M kf (kf0GoodAct (M * L) e β ν p pc) := by
  intro ℓ ℓ' _ _ hℓ hℓ' j a A g ha hbox
  by_cases hj : j = 1
  · subst hj
    obtain ⟨m, hm, rfl⟩ := exists_multiple hℓ
    obtain ⟨m2, hm2, rfl⟩ := exists_multiple hℓ'
    have hXe : (A.image fun y μ => ((y μ : ℤ) : ZMod (M * L * m))) =
        A.image (intToTorus d (M * L * m)) := rfl
    have hXe2 : (A.image fun y μ => ((y μ : ℤ) : ZMod (M * L * m2))) =
        A.image (intToTorus d (M * L * m2)) := rfl
    rw [hXe, hXe2, kf0GoodAct_spec, kf0GoodAct_spec, kf0GoodAct_spec, kf0GoodAct_spec]
    have hbox' : ∀ y ∈ A, ∀ μ, 4 * |y μ| < ((M * L * m : ℕ) : ℤ) ∧
        4 * |y μ| < ((M * L * m2 : ℕ) : ℤ) := hbox
    unfold kf0ActCore
    by_cases hX : IsPolymer d (M * L * m) (M * L) (A.image (intToTorus d (M * L * m)))
    · obtain ⟨hX', -⟩ := polymer_lift hs hd A hbox' hX
      have h1 := kf0PY_agree hs hd A hbox' hX e β ν p pc g
      have h2 : kf0PY (s := M * L) (m' := m2) e β ν p pc
          ((A.image (intToTorus d (M * L * m2))).image (blockOf d (M * L) m2)) 0 =
          kf0PY (s := M * L) (m' := m) e β ν p pc
            ((A.image (intToTorus d (M * L * m))).image (blockOf d (M * L) m)) 0 :=
        kf0PY_agree hs hd A hbox' hX e β ν p pc (fun _ _ => 0)
      simp only [hX, hX', ite_true]
      rw [h1, h2]
    · have hX' : ¬ IsPolymer d (M * L * m2) (M * L) (A.image (intToTorus d (M * L * m2))) := by
        intro hX'
        exact hX (polymer_lift hs hd A (fun y hy μ => ⟨(hbox' y hy μ).2, (hbox' y hy μ).1⟩) hX').1
      simp only [hX, hX', ite_false]
  · rw [kf0GoodAct_of_ne e β ν p pc hj, kf0GoodAct_of_ne e β ν p pc hj,
      kf0GoodAct_of_ne e β ν p pc hj, kf0GoodAct_of_ne e β ν p pc hj]

end Agreement

section Sum

variable {d N n : ℕ} {h : EuclideanSpace ℝ (Fin N)} {M L : ℕ} [NeZero (M * L)]
  (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ) (pc : Measure (perp h))

/-- **The activities regroup the gas**: on the torus of side `M L m` the sum of the scale-`1`
activities over all site sets is the sum of the local terms over all block sets. -/
theorem kf0GoodAct_sum {ℓ : ℕ} [NeZero ℓ] (m : ℕ) [NeZero m] (hℓ : ℓ = M * L * m)
    (hz : ∀ (g' : Torus d (M * L * m) → Fin N → ℂ) (X : NePoly (Torus d m)),
      ¬ IsAnimal (blockGraph d m) X.1 →
      ∀ Φ : ∀ b, Balaban.LargeField.KF0Gas.BlockSpace d (M * L) m (perp h) b,
        gasTermC e β ν p X g' Φ = 0)
    (g : Torus d ℓ → Fin N → ℂ) :
    ∑ X : Finset (Torus d ℓ), kf0GoodAct (M * L) e β ν p pc ℓ 1 X g =
      ∑ Y : Finset (Torus d m), kf0PY (s := M * L) (m' := m) e β ν p pc Y (hℓ ▸ g) := by
  subst hℓ
  simp only [kf0GoodAct_spec]
  unfold kf0ActCore
  rw [← Finset.sum_filter]
  have hv : ∀ Y ∈ (Finset.univ : Finset (Finset (Torus d m))),
      Y ∉ (Finset.univ : Finset (Finset (Torus d m))).filter (IsAnimal (blockGraph d m)) →
      kf0PY (s := M * L) (m' := m) e β ν p pc Y g = 0 := by
    intro Y _ hY
    exact kf0PY_eq_zero_of_not_isAnimal e β ν p pc g (hz g) Y (by simpa using hY)
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

end Sum

section Numerics

/-- The constant `κ₀` of the block gas: `log 4 + 1 ≤ κ₀` and `(2d)² · 2 · e^{-κ₀} ≤ 1/2`. -/
noncomputable def kf0K0 (d : ℕ) : ℝ := max (Real.log 4 + 1) (Real.log (16 * (d : ℝ) ^ 2))

theorem kf0K0_ge_log (d : ℕ) : Real.log 4 + 1 ≤ kf0K0 d := le_max_left _ _

theorem kf0K0_pos (d : ℕ) : 4 ≤ kf0K0 d + 3 := by
  have h1 := kf0K0_ge_log d
  have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith

theorem kf0K0_sq (d : ℕ) (hd : 1 ≤ d) :
    ((2 * d : ℕ) : ℝ) ^ 2 * 2 * Real.exp (-kf0K0 d) ≤ 1 / 2 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : Real.log (16 * (d : ℝ) ^ 2) ≤ kf0K0 d := le_max_right _ _
  have h2 : Real.exp (-kf0K0 d) ≤ 1 / (16 * (d : ℝ) ^ 2) := by
    rw [Real.exp_neg, one_div]
    refine inv_anti₀ (by positivity) ?_
    calc 16 * (d : ℝ) ^ 2 = Real.exp (Real.log (16 * (d : ℝ) ^ 2)) :=
          (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (kf0K0 d) := Real.exp_le_exp.2 h1
  push_cast
  calc (2 * (d : ℝ)) ^ 2 * 2 * Real.exp (-kf0K0 d) ≤ (2 * (d : ℝ)) ^ 2 * 2 * (1 / (16 * (d : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 / 2 := by field_simp; ring

/-- The exponent `γ = ½ log ((2d + g)/(2d))` of the walk expansion. -/
noncomputable def kf0Gamma (d : ℕ) (g : ℝ) : ℝ := (1 / 2) * Real.log ((2 * d + g) / (2 * d))

theorem kf0Gamma_spec {d : ℕ} (hd : 1 ≤ d) {g : ℝ} (hg : 0 < g) :
    0 ≤ kf0Gamma d g ∧ 2 * d / (2 * d + g) * Real.exp (kf0Gamma d g) < 1 ∧
      g / (2 * (2 * d + g)) ≤ kf0Gamma d g := by
  have hd0 : (0 : ℝ) < 2 * d := by have : (0 : ℝ) < d := by exact_mod_cast hd
                                   linarith
  have hx : 1 < (2 * (d : ℝ) + g) / (2 * d) := by
    rw [lt_div_iff₀ hd0]; linarith
  have hlog : 0 < Real.log ((2 * (d : ℝ) + g) / (2 * d)) := Real.log_pos hx
  refine ⟨by unfold kf0Gamma; positivity, ?_, ?_⟩
  · set q : ℝ := 2 * d / (2 * d + g) with hq
    have hq0 : 0 < q := by positivity
    have hq1 : q < 1 := by rw [hq, div_lt_one (by linarith)]; linarith
    have he : Real.exp (kf0Gamma d g) ^ 2 = 1 / q := by
      unfold kf0Gamma
      rw [← Real.exp_nat_mul]
      have : ((2 : ℕ) : ℝ) * (1 / 2 * Real.log ((2 * (d : ℝ) + g) / (2 * d))) =
          Real.log ((2 * (d : ℝ) + g) / (2 * d)) := by push_cast; ring
      rw [this, Real.exp_log (by positivity), hq]
      field_simp
    have hsq : (q * Real.exp (kf0Gamma d g)) ^ 2 = q := by
      rw [mul_pow, he]; field_simp
    by_contra hcon
    push Not at hcon
    have : 1 ≤ (q * Real.exp (kf0Gamma d g)) ^ 2 := by nlinarith
    linarith
  · unfold kf0Gamma
    have := Real.one_sub_inv_le_log_of_pos (x := (2 * (d : ℝ) + g) / (2 * d)) (by positivity)
    have e : 1 - ((2 * (d : ℝ) + g) / (2 * d))⁻¹ = g / (2 * d + g) := by
      field_simp; ring
    rw [e] at this
    have h3 : g / (2 * (2 * d + g)) = (1 / 2) * (g / (2 * d + g)) := by
      have : (2 * (d : ℝ) + g) ≠ 0 := by linarith
      field_simp
    linarith

end Numerics

section GammaKappa

/-- **The decay of the walk expansion beats the block size**: if `M ≥ 3 κ_h 3^d (2d+1) L` then
`κ_h 3^d / (M L) ≤ γ` for `g = 7/(8 L²)`. -/
theorem kf0_gamma_kappa {d : ℕ} (hd : 1 ≤ d) {L M : ℕ} (hL : 1 ≤ L) {κh : ℝ} (hκh : 0 < κh)
    (hM : κh * 3 ^ d * (2 * d + 1) * 3 * L ≤ M) :
    κh * 3 ^ d / ((M * L : ℕ) : ℝ) ≤ kf0Gamma d (7 / (8 * (L : ℝ) ^ 2)) := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set g₀ : ℝ := 7 / (8 * (L : ℝ) ^ 2) with hg₀
  have hg : 0 < g₀ := by positivity
  have hg1 : g₀ ≤ 1 := by
    rw [hg₀, div_le_one (by positivity)]; nlinarith
  have hgL : g₀ * (L : ℝ) ^ 2 = 7 / 8 := by rw [hg₀]; field_simp
  obtain ⟨-, -, h3⟩ := kf0Gamma_spec hd hg
  refine le_trans ?_ h3
  set u : ℝ := κh * 3 ^ d * (2 * d + 1) with hu
  have hu0 : 0 < u := by positivity
  have hMr : (3 * u * L : ℝ) ≤ M := by rw [hu]; linarith
  have hMpos : (0 : ℝ) < ((M * L : ℕ) : ℝ) := by
    have : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hMr
    push_cast
    positivity
  rw [div_le_div_iff₀ hMpos (by positivity)]
  push_cast
  have h1 : κh * 3 ^ d * (2 * (2 * d + g₀)) ≤ 2 * u := by
    rw [hu]
    have : 0 ≤ κh * 3 ^ d := by positivity
    nlinarith
  have h2 : (21 / 8 : ℝ) * u ≤ g₀ * ((M : ℝ) * L) := by
    have := mul_le_mul_of_nonneg_left hMr (mul_nonneg hg.le (by positivity : (0 : ℝ) ≤ L))
    nlinarith [hgL]
  nlinarith

end GammaKappa

section Bounds

open Balaban.LargeField.KF0Gas Balaban.LargeField.KF0F1 Balaban.LargeField.KF0Taylor

variable {d N n : ℕ} {h : EuclideanSpace ℝ (Fin N)}
  (e : OrthonormalBasis (Fin n) ℝ (perp h)) (β ν p : ℝ) (pc : Measure (perp h))

theorem stSize_eq_card {m : ℕ} [NeZero m] {Y : Finset (Torus d m)}
    (hY : IsAnimal (blockGraph d m) Y) : stSize Y = (Y.card : ℝ) := by
  unfold stSize
  have h1 : (steiner (blockGraph d m) Y) ≤ Y.card := steiner_le hY (Finset.Subset.refl Y)
  have h2 : Y.card ≤ steiner (blockGraph d m) Y := card_le_steiner (exists_animal_supset Y)
  exact_mod_cast le_antisymm h1 h2

/-- **The increments of the local terms are bounded by the sum bound of the gas.** -/
theorem kf0PY_increment_le {s m : ℕ} [NeZero s] [NeZero m] {Bnd κ' : ℝ}
    (hbnd : ∀ gc : Torus d (s * m) → Fin N → ℂ, ∑ x, ∑ i, ‖gc x i‖ < 1 →
      ∀ b : Torus d m, ∑ Y ∈ (Finset.univ : Finset (Finset (Torus d m))).filter (fun Y => b ∈ Y),
        ‖kf0PY (s := s) (m' := m) e β ν p pc Y gc‖ * Real.exp (κ' * stSize Y) ≤ Bnd)
    {Y : Finset (Torus d m)} (hY : IsAnimal (blockGraph d m) Y) (g : Torus d (s * m) → Fin N → ℂ)
    (hg : ∑ x, ∑ i, ‖g x i‖ < 1) :
    ‖kf0PY (s := s) (m' := m) e β ν p pc Y g - kf0PY (s := s) (m' := m) e β ν p pc Y 0‖ ≤
      2 * Bnd * Real.exp (-κ' * (Y.card : ℝ)) := by
  obtain ⟨b, hb⟩ := hY.1
  have hone : ∀ gc : Torus d (s * m) → Fin N → ℂ, ∑ x, ∑ i, ‖gc x i‖ < 1 →
      ‖kf0PY (s := s) (m' := m) e β ν p pc Y gc‖ ≤ Bnd * Real.exp (-κ' * (Y.card : ℝ)) := by
    intro gc hgc
    have h1 : ‖kf0PY (s := s) (m' := m) e β ν p pc Y gc‖ * Real.exp (κ' * stSize Y) ≤ Bnd :=
      (Finset.single_le_sum (f := fun Y' : Finset (Torus d m) =>
        ‖kf0PY (s := s) (m' := m) e β ν p pc Y' gc‖ * Real.exp (κ' * stSize Y'))
        (fun _ _ => by positivity)
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)).trans (hbnd gc hgc b)
    rw [stSize_eq_card hY] at h1
    have : Real.exp (-κ' * (Y.card : ℝ)) * Real.exp (κ' * (Y.card : ℝ)) = 1 := by
      rw [← Real.exp_add]; simp
    calc ‖kf0PY (s := s) (m' := m) e β ν p pc Y gc‖
        = ‖kf0PY (s := s) (m' := m) e β ν p pc Y gc‖ * Real.exp (κ' * (Y.card : ℝ)) *
            Real.exp (-κ' * (Y.card : ℝ)) := by
          rw [mul_assoc, mul_comm (Real.exp (κ' * _)), this, mul_one]
      _ ≤ Bnd * Real.exp (-κ' * (Y.card : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have h0 : ∑ x : Torus d (s * m), ∑ i : Fin N, ‖(0 : Torus d (s * m) → Fin N → ℂ) x i‖ < 1 := by
    simp
  calc _ ≤ ‖kf0PY (s := s) (m' := m) e β ν p pc Y g‖ +
        ‖kf0PY (s := s) (m' := m) e β ν p pc Y (0 : Torus d (s * m) → Fin N → ℂ)‖ := norm_sub_le _ _
    _ ≤ Bnd * Real.exp (-κ' * (Y.card : ℝ)) + Bnd * Real.exp (-κ' * (Y.card : ℝ)) :=
        add_le_add (hone g hg) (hone 0 h0)
    _ = _ := by ring

end Bounds

section WeightedSmall

open Balaban.LargeField.KF0Gas Balaban.LargeField.KF0F1 Balaban.LargeField.KF0Taylor

variable {d N n : ℕ} {h : EuclideanSpace ℝ (Fin N)}

/-- **The weighted bounds of the three kinds of pieces from the smallness of the majorants.** -/
theorem kf0_weighted_small {β ν g γ κ ε : ℝ} (hβ : 0 < β) (hg : 0 < g) (hgν : g ≤ ν)
    (hν1 : ν ≤ 1) (hγ : 0 ≤ γ) (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) {s m' : ℕ}
    [NeZero s] [NeZero m'] (hs : 0 < s) (hκ : 0 ≤ κ) (hγκ : κ * 3 ^ d / s ≤ γ)
    (hp : 0 < Real.log β) (hn : 1 ≤ n) (hρ1 : kf0Rho d g γ κ (Real.log β) β ≤ 1)
    (hρ : (n : ℝ) * kf0Rho d g γ κ (Real.log β) β ^ 2 ≤ 1 / 4)
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) (hh : ‖h‖ = 1)
    (S1 : (n : ℝ) ^ 2 * (kf0Rho d g γ κ (Real.log β) β ^ 2 +
      β * kf0Rho d g γ κ (Real.log β) β ^ 4) ≤ ε)
    (S2 : 2 * (n : ℝ) ^ 2 * (β * kf0Rho d g γ κ (Real.log β) β ^ 4) ≤ ε)
    (S3 : (n : ℝ) * kf0Rho d g γ κ (Real.log β) β ^ 2 +
      (n : ℝ) * kf0Rho d g γ κ (Real.log β) β ≤ ε) :
    (∀ x : Torus d (s * m'), ∑ H : Finset (Torus d (s * m')),
      Real.exp (κ * kf0BlockCount s m' H) *
        cutoffSup (Real.log β) (f1SiteHalo e β ν (fun _ _ => 0) x H) ≤ ε) ∧
    (∀ (x : Torus d (s * m')) (μ : Fin d), ∑ H : Finset (Torus d (s * m')),
      Real.exp (κ * kf0BlockCount s m' H) * cutoffSup (Real.log β) (f1BondHalo e β ν x μ H) ≤ ε) ∧
    (∀ (x : Torus d (s * m')) (i : Fin N), ∑ H : Finset (Torus d (s * m')),
      Real.exp (κ * kf0BlockCount s m' H) *
        cutoffSup (Real.log β) (f1SiteSrcHalo e β ν x i H) ≤ ε) := by
  refine ⟨fun x => ?_, fun x μ => ?_, fun x i => ?_⟩
  · refine (site_halo_decomposition (ℓ := s * m') hβ hg hgν hν1 hγ hq hs rfl hκ hγκ hp hn hρ1 hρ e
      (fun _ _ => 0) x).2.2.trans ?_
    have hz : ∀ j, f1Lin e (fun (_ : Torus d (s * m')) (_ : Fin N) => (0 : ℝ)) x j = 0 := fun j => by
      simp [f1Lin]
    simp only [hz, f1Nrm, zero_mul, Finset.sum_const_zero, abs_zero, add_zero, zero_add]
    exact S1
  · refine (bond_halo_decomposition (ℓ := s * m') hβ hg hgν hγ hq hs rfl hκ hγκ hp hρ e x μ).2.2.trans ?_
    calc 2 * (n : ℝ) ^ 2 * β * kf0Rho d g γ κ (Real.log β) β ^ 4 =
        2 * (n : ℝ) ^ 2 * (β * kf0Rho d g γ κ (Real.log β) β ^ 4) := by ring
      _ ≤ ε := S2
  · refine (f1SiteSrcHalo_weighted (n := n) (s := s) (m' := m') hg hgν hβ hq hs hκ hγκ hp hρ e x i).trans ?_
    have hρ0 : 0 ≤ kf0Rho d g γ κ (Real.log β) β := (kf0Rho_pos hg hq hp hβ).le
    have hhi : |h i| ≤ 1 := by
      have := PiLp.norm_apply_le h i
      rw [hh] at this
      simpa using this
    have hej : ∀ j, |((e j : perp h) : EuclideanSpace ℝ (Fin N)) i| ≤ 1 := fun j => by
      have := PiLp.norm_apply_le ((e j : perp h) : EuclideanSpace ℝ (Fin N)) i
      have h1 : ‖((e j : perp h) : EuclideanSpace ℝ (Fin N))‖ = 1 := by
        exact (Submodule.norm_coe (e j)).trans (e.norm_eq_one j)
      rw [h1] at this
      simpa using this
    have hsum : ∑ j, |((e j : perp h) : EuclideanSpace ℝ (Fin N)) i| ≤ n := by
      calc _ ≤ ∑ _j : Fin n, (1 : ℝ) := Finset.sum_le_sum fun j _ => hej j
        _ = n := by simp
    calc |h i| * ((n : ℝ) * kf0Rho d g γ κ (Real.log β) β ^ 2) +
        kf0Rho d g γ κ (Real.log β) β * ∑ j, |((e j : perp h) : EuclideanSpace ℝ (Fin N)) i|
        ≤ 1 * ((n : ℝ) * kf0Rho d g γ κ (Real.log β) β ^ 2) +
          kf0Rho d g γ κ (Real.log β) β * n := by
          gcongr
      _ = _ := by ring
      _ ≤ ε := S3

end WeightedSmall

section Main

open Balaban.LargeField Balaban.LargeField.KF0Gas Balaban.LargeField.KF0F1 Balaban.LargeField.KF0Taylor
  Balaban.LargeField.KF0AllPlus

/-- **Item (a) of A7-1, the threshold (LF-BASE-KF0 E.4), as a named input.**  The physical threshold
of the all-good sector is not local in the Gaussian variables `ψ`: the sector `Z_∅(g)` (every spin
within `thr` of `h`) differs from the product-cutoff part of the chart integral
(`kf0CutIntegral`, every `‖ψ_y‖ ≤ log β`) by the sites with a large Gaussian variable whose spin is
still good. This input says that the ratio is a gas of defects: there are activities `r` in the
form of Root-F, at half the amplitude `c₉/4`, and constants `E₀` with
`Z_∅(g) = exp(E₀ + ∑_X r(X; g)) · (product-cutoff integral)(g)` on every admissible torus
(`ℓ = M L m`) and every source of the unit `ℓ¹` ball. It is **not proved**; see
`notes/phase1/SPINE.md`, A7-1 (a). -/
def KF0ThresholdInput (d N : ℕ) (δ : ℝ) (T : ℝ → ℝ → Typing)
    (thr : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
  ∀ ν : ℝ, 7 / 8 < ν * ((T κ c₉).L : ℝ) ^ 2 → ν ≤ 1 →
  ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon (T κ c₉).L ν kf →
    ∃ (r : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (E₀ : ℕ → ℂ),
      ObservableActivities d N (T κ c₉).L (T κ c₉).M κ (c₉ / 4) δ 1 kf r ∧
      ∀ (m : ℕ) [NeZero m] [NeZero ((T κ c₉).M * (T κ c₉).L)],
        (T κ c₉).M * (T κ c₉).L ^ (kf + 1) ∣ (T κ c₉).M * (T κ c₉).L * m →
        ∀ g : Torus d ((T κ c₉).M * (T κ c₉).L * m) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
          kf0Sector ((T κ c₉).M * (T κ c₉).L) m (thr κ c₉ β ν) β ν h ∅ g =
            Complex.exp (E₀ ((T κ c₉).M * (T κ c₉).L * m) +
              ∑ X, r ((T κ c₉).M * (T κ c₉).L * m) 1 X g) *
              kf0CutIntegral (s := (T κ c₉).M * (T κ c₉).L) (m' := m)
                (oneSiteGaussian (perp h)) β ν (Real.log β) g

end Main


section GasFacts

open Balaban.LargeField Balaban.LargeField.KF0Gas Balaban.LargeField.KF0F1 Balaban.LargeField.KF0Taylor
  Balaban.LargeField.KF0AllPlus

/-- **The facts about the all-plus gas on one torus that the activities need** (items (b), (c),
(e)): analyticity of the local terms on the unit `ℓ¹` ball, the bound of their increments, the
identity of the cutoff integral at a complex source, and the vanishing of the activities of
non-connected block sets. The hypotheses are the regime constants of the walk expansion, the
weighted bounds of the three kinds of pieces, and the numerical conditions of the block gas. -/
theorem kf0_gas_facts {d N n s m : ℕ} [NeZero s] [NeZero m] {h : EuclideanSpace ℝ (Fin N)}
    (e : OrthonormalBasis (Fin n) ℝ (perp h)) {β ν g γ κh κ κ0 κ1 p ε : ℝ} (hβ : 0 < β)
    (hg : 0 < g) (hgν : g ≤ ν) (hν1 : ν ≤ 1) (hγ : 0 ≤ γ)
    (hq : 2 * d / (2 * d + g) * Real.exp γ < 1) (hκh : 0 ≤ κh) (hγκ : κh * 3 ^ d / s ≤ γ)
    (hp : 0 < p) (hn : 1 ≤ n) (hρ1 : kf0Rho d g γ κh p β ≤ 1)
    (hρ : (n : ℝ) * kf0Rho d g γ κh p β ^ 2 ≤ 1 / 4)
    (hsite : ∀ x : Torus d (s * m), ∑ H : Finset (Torus d (s * m)),
      Real.exp (κh * kf0BlockCount s m H) * cutoffSup p (f1SiteHalo e β ν (fun _ _ => 0) x H) ≤ ε)
    (hbond : ∀ (x : Torus d (s * m)) (μ : Fin d), ∑ H : Finset (Torus d (s * m)),
      Real.exp (κh * kf0BlockCount s m H) * cutoffSup p (f1BondHalo e β ν x μ H) ≤ ε)
    (hsrc : ∀ (x : Torus d (s * m)) (i : Fin N), ∑ H : Finset (Torus d (s * m)),
      Real.exp (κh * kf0BlockCount s m H) * cutoffSup p (f1SiteSrcHalo e β ν x i H) ≤ ε)
    (hε0 : 0 ≤ ε) (hεs : ε ≤ (1 + 2 * d) * s ^ d * ε)
    (hq0 : ((2 * d : ℕ) : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2)
    (hκ0 : Real.log 4 + 1 ≤ κ0) (hκ : 0 ≤ κ) (hκg : κ + κ0 + 1 ≤ κ1 - 3 / 2)
    (hH0 : 0 ≤ 2 * ((1 + 2 * d) * s ^ d * ε))
    (hH0log : 2 * ((1 + 2 * d) * s ^ d * ε) ≤ Real.log 2)
    (hH0K : 2 * ((1 + 2 * d) * s ^ d * ε) * (4 * Real.exp (-κ0)) ≤ 1 / 4)
    (hκ01 : 1 + κ0 + κ1 ≤ κh) (hκ01' : 0 ≤ κ0 + κ1)
    (γ₀ : Measure (perp h)) [IsProbabilityMeasure γ₀] (hpos : γ₀ (smallSet p) ≠ 0) :
    (∀ Y : Finset (Torus d m), AnalyticOnNhd ℂ
      (kf0PY (s := s) (m' := m) e β ν p (ProbabilityTheory.cond γ₀ (smallSet p)) Y)
      {g' : Torus d (s * m) → Fin N → ℂ | ∑ x, ∑ i, ‖g' x i‖ < 1}) ∧
    (∀ Y : Finset (Torus d m), IsAnimal (blockGraph d m) Y →
      ∀ g' : Torus d (s * m) → Fin N → ℂ, ∑ x, ∑ i, ‖g' x i‖ < 1 →
        ‖kf0PY (s := s) (m' := m) e β ν p (ProbabilityTheory.cond γ₀ (smallSet p)) Y g' -
            kf0PY (s := s) (m' := m) e β ν p (ProbabilityTheory.cond γ₀ (smallSet p)) Y 0‖ ≤
          2 * (64 * Real.exp 1 * (2 * ((1 + 2 * d) * s ^ d * ε)) * Real.exp (-(2 * κ0))) *
            Real.exp (-κ * (Y.card : ℝ))) ∧
    (∀ gc : Torus d (s * m) → Fin N → ℂ, ∑ x, ∑ i, ‖gc x i‖ < 1 →
      kf0CutIntegral (s := s) (m' := m) γ₀ β ν p gc =
        (((1 - γ₀.real (largeSet p)) ^ Fintype.card (Torus d (s * m)) : ℝ) : ℂ) *
          Complex.exp (∑ x, ∑ i, gc x i * (h i : ℂ)) *
          Complex.exp (∑ Y : Finset (Torus d m),
            kf0PY (s := s) (m' := m) e β ν p (ProbabilityTheory.cond γ₀ (smallSet p)) Y gc)) ∧
    (∀ (g' : Torus d (s * m) → Fin N → ℂ) (X : NePoly (Torus d m)),
      ¬ IsAnimal (blockGraph d m) X.1 → ∀ Φ : ∀ b, BlockSpace d s m (perp h) b,
        gasTermC e β ν p X g' Φ = 0) := by
  have hbd := gasTermC_bd (s := s) (m' := m) hβ hg hgν hν1 hγ hq hκh hγκ hp hn hρ1 hρ e hsite hbond
    hsrc hε0 hεs hκ01 hκ01'
  have hbsrc := bdd_blockSrc (s := s) (m' := m) hβ hg hgν hq hκh hγκ hp hρ e hsrc
  have hprob : IsProbabilityMeasure (ProbabilityTheory.cond γ₀ (smallSet p)) :=
    cond_smallSet_isProbabilityMeasure γ₀ p hpos
  have hcut := fun gc (hgc : ∑ x, ∑ i, ‖gc x i‖ < 1) =>
    kf0CutIntegral_eq (s := s) (m' := m) hβ hg hgν hν1 hγ hq hκh hγκ hp hn hρ1 hρ e hsite hbond hsrc
      hε0 hεs hq0 hκ0 hκ hκg hH0 hH0log hH0K hκ01 γ₀ hpos gc hgc
  refine ⟨fun Y => kf0PY_analyticOnNhd hq0 hκ0 hκ hκg hH0 hH0log hH0K e β ν p _ hbd hbsrc Y,
    fun Y hY g' hg' => ?_, fun gc hgc => (hcut gc hgc).1, fun g' X hX Φ => ?_⟩
  · exact kf0PY_increment_le e β ν p _ (fun gc hgc b => (hcut gc hgc).2 b) hY g' hg'
  · exact gasTermC_eq_zero_of_not_isAnimal hβ hg hgν hν1 hγ hq hκh hγκ hp hn hρ1 hρ e X hX g' Φ

end GasFacts


section ChooseEps

/-- **The choice of `ε`**: a single `ε > 0` makes the gas amplitude, the cluster-expansion
conditions of the block gas and the target amplitude hold. -/
theorem kf0_choose_eps {d s : ℕ} (hs : 1 ≤ s) {κ0 Btar : ℝ} (hB : 0 < Btar) :
    ∃ ε : ℝ, 0 < ε ∧ 2 * ((1 + 2 * (d : ℝ)) * (s : ℝ) ^ d * ε) ≤ Real.log 2 ∧
      2 * ((1 + 2 * (d : ℝ)) * (s : ℝ) ^ d * ε) * (4 * Real.exp (-κ0)) ≤ 1 / 4 ∧
      2 * (64 * Real.exp 1 * (2 * ((1 + 2 * (d : ℝ)) * (s : ℝ) ^ d * ε)) *
        Real.exp (-(2 * κ0))) ≤ Btar ∧ ε ≤ (1 + 2 * (d : ℝ)) * (s : ℝ) ^ d * ε := by
  have hsr : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  set C : ℝ := 2 * ((1 + 2 * (d : ℝ)) * (s : ℝ) ^ d) with hC
  have hCpos : 0 < C := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min (Real.log 2 / C) (min (1 / (16 * Real.exp (-κ0) * C))
    (Btar / (128 * Real.exp 1 * C * Real.exp (-(2 * κ0))))), by positivity, ?_, ?_, ?_, ?_⟩
  all_goals set ε : ℝ := min (Real.log 2 / C) (min (1 / (16 * Real.exp (-κ0) * C))
    (Btar / (128 * Real.exp 1 * C * Real.exp (-(2 * κ0))))) with hεdef
  · have : ε ≤ Real.log 2 / C := min_le_left _ _
    calc 2 * ((1 + 2 * (d : ℝ)) * (s : ℝ) ^ d * ε) = C * ε := by rw [hC]; ring
      _ ≤ C * (Real.log 2 / C) := mul_le_mul_of_nonneg_left this hCpos.le
      _ = Real.log 2 := by field_simp
  · have : ε ≤ 1 / (16 * Real.exp (-κ0) * C) := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : C * ε * (4 * Real.exp (-κ0)) ≤ C * (1 / (16 * Real.exp (-κ0) * C)) *
        (4 * Real.exp (-κ0)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hCpos.le) (by positivity)
    calc 2 * ((1 + 2 * (d : ℝ)) * (s : ℝ) ^ d * ε) * (4 * Real.exp (-κ0)) =
        C * ε * (4 * Real.exp (-κ0)) := by rw [hC]; ring
      _ ≤ _ := h2
      _ = 1 / 4 := by field_simp; ring
  · have : ε ≤ Btar / (128 * Real.exp 1 * C * Real.exp (-(2 * κ0))) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hpos : 0 < 128 * Real.exp 1 * C * Real.exp (-(2 * κ0)) := by positivity
    rw [le_div_iff₀ hpos] at this
    calc 2 * (64 * Real.exp 1 * (2 * ((1 + 2 * (d : ℝ)) * (s : ℝ) ^ d * ε)) *
        Real.exp (-(2 * κ0))) = (128 * Real.exp 1 * C * Real.exp (-(2 * κ0))) * ε := by
          rw [hC]; ring
      _ ≤ Btar := by linarith
  · have h1 : (1 : ℝ) ≤ (s : ℝ) ^ d := one_le_pow₀ hsr
    have h2 : (1 : ℝ) ≤ (1 + 2 * (d : ℝ)) * (s : ℝ) ^ d := by nlinarith
    have : 0 < ε := by positivity
    nlinarith

end ChooseEps


section Normalization

open Balaban.LargeField Balaban.LargeField.KF0Gas Balaban.LargeField.KF0AllPlus

/-- The normalizing factor of the cutoff measure is the exponential of a constant. -/
theorem cutoff_factor_eq_exp {W : Type*} [NormedAddCommGroup W] [MeasurableSpace W] [BorelSpace W]
    [SecondCountableTopology W] (γ₀ : Measure W) [IsProbabilityMeasure γ₀] (p : ℝ)
    (hpos : γ₀ (smallSet p) ≠ 0) (c : ℕ) :
    (((1 - γ₀.real (largeSet p)) ^ c : ℝ) : ℂ) =
      Complex.exp ((c : ℂ) * ((Real.log (1 - γ₀.real (largeSet p)) : ℝ) : ℂ)) := by
  have h1 : 1 - γ₀.real (largeSet p) = γ₀.real (smallSet p) := by
    have h := probReal_compl_eq_one_sub (μ := γ₀) (measurableSet_largeSet p)
    rw [smallSet_eq_compl]
    exact h.symm
  have h2 : 0 < 1 - γ₀.real (largeSet p) := by
    rw [h1]
    exact ENNReal.toReal_pos hpos (measure_ne_top _ _)
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.ofReal_inj,
    ← Real.log_pow, Real.exp_log (pow_pos h2 _)]

theorem card_torus (d ℓ : ℕ) [NeZero ℓ] : Fintype.card (Torus d ℓ) = ℓ ^ d := by
  simp [Torus, ZMod.card]

end Normalization

section MainTheorem

open Balaban.LargeField Balaban.LargeField.KF0Gas Balaban.LargeField.KF0F1 Balaban.LargeField.KF0Taylor
  Balaban.LargeField.KF0AllPlus

/-- **The fixed-constant form of `kf0GoodSectorInput_of_threshold`**: for the typing constants
`L`, `M` at one pair `κ, c₉`. -/
theorem kf0_good_fixed {d N : ℕ} {δ κ c₉ : ℝ} {L M : ℕ} (hd : 1 ≤ d) (hN : 2 ≤ N)
    (hκ : 0 < κ) (hc₉ : 0 < c₉) (hL1 : 1 ≤ L)
    (hM : (κ + 2 * kf0K0 d + 4) * 3 ^ d * (2 * d + 1) * 3 * (L : ℝ) ≤ (M : ℝ))
    {β₀' : ℝ} {thrv : ℝ → ℝ → ℝ}
    (hthr : ∀ β : ℝ, β₀' ≤ β → ∀ ν : ℝ, 7 / 8 < ν * (L : ℝ) ^ 2 → ν ≤ 1 →
      ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon L ν kf →
        ∃ (r : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (E₀ : ℕ → ℂ),
          ObservableActivities d N L M κ (c₉ / 4) δ 1 kf r ∧
          ∀ (m : ℕ) [NeZero m] [NeZero (M * L)], M * L ^ (kf + 1) ∣ M * L * m →
            ∀ g : Torus d (M * L * m) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              kf0Sector (M * L) m (thrv β ν) β ν h ∅ g =
                Complex.exp (E₀ (M * L * m) + ∑ X, r (M * L * m) 1 X g) *
                  kf0CutIntegral (s := M * L) (m' := m) (oneSiteGaussian (perp h)) β ν
                    (Real.log β) g) :
    ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β → ∀ ν : ℝ, 7 / 8 < ν * (L : ℝ) ^ 2 → ν ≤ 1 →
      ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 → ∀ kf : ℕ, IsHorizon L ν kf →
        ∃ (a : (ℓ : ℕ) → ℕ → Finset (Torus d ℓ) → (Torus d ℓ → Fin N → ℂ) → ℂ) (E : ℕ → ℂ),
          ObservableActivities d N L M κ (c₉ / 2) δ 1 kf a ∧
          ∀ (ℓ : ℕ) [NeZero ℓ], M * L ^ (kf + 1) ∣ ℓ →
            ∀ (m : ℕ) [NeZero m], ℓ = M * L * m →
              ∀ g : Torus d ℓ → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
                kf0Sector (M * L) m (thrv β ν) β ν h ∅ g =
                  Complex.exp (E ℓ + ∑ x, ∑ i, g x i * (h i : ℂ) + ∑ X, a ℓ 1 X g) := by
  have hLr : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨κ0, hκ0def⟩ : ∃ κ0 : ℝ, κ0 = kf0K0 d := ⟨_, rfl⟩
  have hκ0ge : Real.log 4 + 1 ≤ κ0 := hκ0def ▸ kf0K0_ge_log d
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [← hκ0def] at hM
  obtain ⟨κh, hκhdef⟩ : ∃ κh : ℝ, κh = κ + 2 * κ0 + 4 := ⟨_, rfl⟩
  rw [← hκhdef] at hM
  have hκhpos : 4 ≤ κh := by rw [hκhdef]; linarith
  have h3d : (3 : ℝ) ≤ 3 ^ d := by
    calc (3 : ℝ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ d := pow_le_pow_right₀ (by norm_num) hd
  have hMbig : (108 : ℝ) * L ≤ M := by
    have h2 : (3 : ℝ) ≤ 2 * d + 1 := by linarith
    calc (108 : ℝ) * L = 4 * 3 * 3 * 3 * L := by ring
      _ ≤ κh * 3 ^ d * (2 * d + 1) * 3 * L := by gcongr
      _ ≤ M := hM
  have hs6 : 6 ≤ M * L := by
    have : (6 : ℝ) ≤ (M : ℝ) * L := by nlinarith
    exact_mod_cast this
  have hNZ : NeZero (M * L) := ⟨by omega⟩
  obtain ⟨g₀, hg₀def⟩ : ∃ g₀ : ℝ, g₀ = 7 / (8 * (L : ℝ) ^ 2) := ⟨_, rfl⟩
  have hg₀ : 0 < g₀ := by rw [hg₀def]; positivity
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = kf0Gamma d g₀ := ⟨_, rfl⟩
  obtain ⟨hγ0', hq', -⟩ := kf0Gamma_spec hd hg₀
  rw [← hγdef] at hγ0' hq'
  have hγκ : κh * 3 ^ d / ((M * L : ℕ) : ℝ) ≤ γ := by
    rw [hγdef, hg₀def]
    exact kf0_gamma_kappa hd hL1 (by linarith) hM
  obtain ⟨Btar, hBtardef⟩ : ∃ Btar : ℝ, Btar =
      c₉ / 4 / 2 * (L : ℝ) ^ (-((1 : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := ⟨_, rfl⟩
  have hBtarpos : 0 < Btar := by
    have : 0 < (L : ℝ) ^ (-((1 : ℝ) * (((d : ℝ) - 2) / 2 + δ))) :=
      Real.rpow_pos_of_pos (by linarith) _
    rw [hBtardef]; positivity
  obtain ⟨ε, hε0, hH0log, hH0K, hamp, hεs⟩ := kf0_choose_eps (d := d) (s := M * L)
    (by omega) (κ0 := κ0) hBtarpos
  obtain ⟨β₁, hβ₁⟩ := kf0_small_uniform (d := d) (n := N - 1) (g := g₀) (γ := γ) (κ := κh)
    (ε := ε) hg₀ hq' hε0
  refine ⟨max β₀' β₁, fun β hβ ν hνL hν1 h hh kf hkf => ?_⟩
  obtain ⟨r, E₀, hr, hid⟩ := hthr β (le_of_max_le_left hβ) ν hνL hν1 h hh kf hkf
  obtain ⟨hβ0, hp, hρ1, hρ, S1, S2, S3⟩ := hβ₁ β (le_of_max_le_right hβ)
  obtain ⟨e⟩ := nonempty_tangent_basis (N := N) (h := h) hh
  have hn : 1 ≤ N - 1 := by omega
  have hgν : g₀ ≤ ν := by
    rw [hg₀def, div_le_iff₀ (by positivity)]
    nlinarith
  have hκhnn : 0 ≤ κh := by linarith
  have hpos : oneSiteGaussian (perp h) (smallSet (Real.log β)) ≠ 0 :=
    oneSiteGaussian_smallSet_ne_zero hp
  have hprob : IsProbabilityMeasure
      (ProbabilityTheory.cond (oneSiteGaussian (perp h)) (smallSet (Real.log β))) :=
    cond_smallSet_isProbabilityMeasure _ _ hpos
  -- numerical facts of the Mayer layer
  have hq0 : ((2 * d : ℕ) : ℝ) ^ 2 * 2 * Real.exp (-κ0) ≤ 1 / 2 := hκ0def ▸ kf0K0_sq d hd
  obtain ⟨κ1, hκ1def⟩ : ∃ κ1 : ℝ, κ1 = κ + κ0 + 5 / 2 := ⟨_, rfl⟩
  have hκg : κ + κ0 + 1 ≤ κ1 - 3 / 2 := by rw [hκ1def]; linarith
  have hκ01 : 1 + κ0 + κ1 ≤ κh := by rw [hκ1def, hκhdef]; linarith
  have hκ01' : 0 ≤ κ0 + κ1 := by rw [hκ1def]; linarith
  have hH0 : 0 ≤ 2 * ((1 + 2 * (d : ℝ)) * ((M * L : ℕ) : ℝ) ^ d * ε) := by positivity
  have hW := fun (m : ℕ) [NeZero m] =>
    kf0_weighted_small (s := M * L) (m' := m) hβ0 hg₀ hgν hν1 hγ0' hq' (by omega) hκhnn hγκ hp hn
      hρ1 hρ e hh S1 S2 S3
  have hF := fun (m : ℕ) [NeZero m] =>
    kf0_gas_facts (s := M * L) (m := m) e hβ0 hg₀ hgν hν1 hγ0' hq' hκhnn hγκ hp hn hρ1 hρ
      (hW m).1 (hW m).2.1 (hW m).2.2 hε0.le hεs hq0 hκ0ge hκ.le hκg hH0 hH0log hH0K hκ01 hκ01'
      (oneSiteGaussian (perp h)) hpos
  have hB : 2 * (64 * Real.exp 1 * (2 * ((1 + 2 * (d : ℝ)) * ((M * L : ℕ) : ℝ) ^ d * ε)) *
      Real.exp (-(2 * κ0))) ≤ c₉ / 4 / 2 * (L : ℝ) ^ (-((1 : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
    rw [← hBtardef]; exact hamp
  have hgas : ObservableActivities d N L M κ (c₉ / 4) δ 1 kf
      (kf0GoodAct (M * L) e β ν (Real.log β)
        (ProbabilityTheory.cond (oneSiteGaussian (perp h)) (smallSet (Real.log β)))) := by
    refine ⟨fun ℓ _ hℓ => ?_, kf0GoodAct_agree e β ν _ _ hs6 hd⟩
    obtain ⟨m, hm, hℓm⟩ := exists_multiple hℓ
    exact ⟨kf0GoodAct_support e β ν _ _ m hℓm, kf0GoodAct_analytic e β ν _ _ m hℓm (hF m).1,
      kf0GoodAct_local e β ν _ _ m hℓm,
      kf0GoodAct_bound e β ν _ _ m hℓm (by positivity) (hF m).2.1 hB⟩
  refine ⟨actAdd (kf0GoodAct (M * L) e β ν (Real.log β)
      (ProbabilityTheory.cond (oneSiteGaussian (perp h)) (smallSet (Real.log β)))) r,
    fun ℓ => E₀ ℓ + ((ℓ ^ d : ℕ) : ℂ) *
      ((Real.log (1 - (oneSiteGaussian (perp h)).real (largeSet (Real.log β))) : ℝ) : ℂ),
    ⟨fun ℓ _ hℓ => ?_, hgas.2.add hr.2⟩, fun ℓ _ hℓ m _ hℓm g hg => ?_⟩
  · obtain ⟨hsA, haA, hlA, hbA⟩ := hgas.1 ℓ hℓ
    obtain ⟨hsB, haB, hlB, hbB⟩ := hr.1 ℓ hℓ
    have hbAB := hbA.add hbB
    have : c₉ / 4 + c₉ / 4 = c₉ / 2 := by ring
    rw [this] at hbAB
    exact ⟨hsA.add hsB, haA.add haB, hlA.add hlB, hbAB⟩
  · subst hℓm
    rw [hid m hℓ g hg, (hF m).2.2.1 g hg]
    have hsum := kf0GoodAct_sum e β ν (Real.log β)
      (ProbabilityTheory.cond (oneSiteGaussian (perp h)) (smallSet (Real.log β))) m rfl
      (hF m).2.2.2 g
    have hsplit : ∑ X, actAdd (kf0GoodAct (M * L) e β ν (Real.log β)
        (ProbabilityTheory.cond (oneSiteGaussian (perp h)) (smallSet (Real.log β)))) r
        (M * L * m) 1 X g =
        ∑ Y : Finset (Torus d m), kf0PY (s := M * L) (m' := m) e β ν (Real.log β)
          (ProbabilityTheory.cond (oneSiteGaussian (perp h)) (smallSet (Real.log β))) Y g +
        ∑ X, r (M * L * m) 1 X g := by
      simp only [actAdd, Finset.sum_add_distrib]
      rw [hsum]
    rw [hsplit, card_torus, cutoff_factor_eq_exp _ _ hpos, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    simp only []
    ring

/-- **`KF0GoodSectorInput` from the threshold input (a) and the typing.**  Under `d ≥ 1`, `N ≥ 2`,
`M ≥ 3 (κ + 2κ₀ + 4) 3^d (2d+1) L` (the cubes of side `M L` are large against the decay `√ν_*` of
the walk expansion, `ν_* = 7/(8 L²)`, and the entropy of the block gas, `κ₀ = kf0K0 d`) and the
threshold input `KF0ThresholdInput` (item (a)), the all-good sector is the exponential of the gas of
the product-cutoff sector (items (b)–(e): the complex source `kf0PY_analyticOnNhd`, the measurable
walk terms with clipping of `KF0AllPlusGas`, the regrouping onto `IsPolymer d ℓ (M L)` with exact
two-torus agreement `kf0GoodAct_agree`, the amplitude `kf0GoodAct_bound`) times the activities of
the threshold input. -/
theorem kf0GoodSectorInput_of_threshold {d N : ℕ} {δ : ℝ} {T : ℝ → ℝ → Typing}
    {thr : ℝ → ℝ → ℝ → ℝ → ℝ} (hd : 1 ≤ d) (hN : 2 ≤ N)
    (hM : ∀ κ c₉ : ℝ, 0 < κ → 0 < c₉ →
      (κ + 2 * kf0K0 d + 4) * 3 ^ d * (2 * d + 1) * 3 * ((T κ c₉).L : ℝ) ≤ ((T κ c₉).M : ℝ))
    (hthr : KF0ThresholdInput d N δ T thr) : KF0GoodSectorInput d N δ T thr := by
  intro κ hκ c₉ hc₉
  obtain ⟨β₀', hβ₀'⟩ := hthr κ hκ c₉ hc₉
  by_cases hL0 : (T κ c₉).L = 0
  · exact ⟨0, fun β _ ν hν => by rw [hL0] at hν; norm_num at hν⟩
  · exact kf0_good_fixed hd hN hκ hc₉ (Nat.pos_of_ne_zero hL0) (hM κ c₉ hκ hc₉) hβ₀'

end MainTheorem

end Balaban.RootFSpine
