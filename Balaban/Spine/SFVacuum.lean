/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.SFStep
public import Balaban.Spine.SFVacuumRatio
public import Balaban.Fluctuation.VacuumStep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The vacuum map `ΦE` of the small-field step and `SFVacuumInput` (A4-1g)

**The map.** One step of the class gives (P4 (2.1), (2.41), (2.63), (4.21);
`StepSetting.vacuumEnergy_succ_eq_increment`)
`E_{k+1} = L^d E_k + g_k`, `g_k = Γ_k - e₀ / |T^{(k+1)}_1|`, where `e₀` is the vacuum value (the sum
over the torus at the zero datum) of the new localized terms `ℰ^{(k+1)}` (the determinant part
`½ log det C^{(k)}` and `ℰ₁^{(k+1)}`), absorbed by the renormalization condition (H.5), and
`Γ_k = L^d (E'''_k - E_k)` is the Gaussian increment, computed exactly
(`StepSetting.step_increment_eq`):
`Γ_k = ½ N (L^d - 1) log β_k - ½ N log (a₁ L^{d-2} / 2π) - L^d log Z₁(p₁)`.
The two parts of `g_k` have different characters. `L^d E_k` and `e₀ / |T^{(k+1)}_1|` are the
extensive parts: they are the same on every torus and are not carried by the class, which only
asks `|E_j| ≤ C_b (log β_j + 1)`; the vacuum normalization `s` of the step density
(`stepDensity`, `ρ' = e^{-s |T^{(k+1)}_1|} S T ρ`) absorbs them. The vacuum constant of the class at
scale `k + 1` is what remains, the Gaussian increment itself:
`ΦE = vacIncrement = Γ_k`, a function of `β_k`, the kernel coefficient `a₁` and the cutoff
`p₁ = p(β_k)`, and not of the record or of the flow `E_j`.

**Compatibility with the tie of `LFStepInput`.** The normalization `s` is a free output of
`LFStepInput`. The step's total vacuum constant is `E_{k+1}^{tot} = L^d E_k + Γ_k - e₀/|T^{(k+1)}_1|`
(`vacuumEnergy_succ_eq_increment`), so the class constant `ΦE = Γ_k` goes with the normalization
`s = L^d E_k - e₀ / |T^{(k+1)}_1|`: `ΦE + s = E_{k+1}^{tot}`
(`vacIncrement_add_normalization`). The tie (`StepData.VacuumTie` with `vacExt rec.Ev k ΦE`) fixes
the constants of the step data to the flow `E_0, …, E_k, ΦE`; these are of size `O(log β)`
(`sfVacuumInput_of_inherit_renorm`), which is what the bound on `b⁰_k` of R5, R5′ uses. The
map `ΦE` does not depend on `e₀`; the size of `e₀ / |T^{(k+1)}_1|` enters only `s`.

**The bound.** `|Γ_k| ≤ A (log β_k + 1)` for `β_k ≥ 1`, `p(β_k) ≥ 1`
(`abs_vacIncrement_le`: `Z₁(p) ∈ [Z₁(1), (2π)^{N/2}]`), and `β_k ≤ (5/4) β_{k+1}`
(`CoeffBounds.beta_succ_ge`: `β_{k+1} = β_k L^{d-2}/(1 + ξ₃)`, `|ξ₃| ≤ 1/4`). So
`|ΦE| ≤ C_b (log β_{k+1} + 1)` as soon as `C_b ≥ vacConst`, the explicit constant below
(`sfVacuumInput_of_inherit_renorm`).
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Fluctuation

namespace Balaban.RootFSpine

/-! ### The Gaussian increment of one step -/

/-- **The Gaussian increment `Γ_k = L^d (E'''_k - E_k)`** of the vacuum constant in one step
(P4 (2.1), (2.41), (2.63)), as a function of the coupling `β_k` (in the units of the paper), the
kernel coefficient `a₁` and the radius `p₁` of `χ_fl`:
`½ N (L^d - 1) log β_k - ½ N log (a₁ L^{d-2}/2π) - L^d log Z₁(p₁)`. -/
noncomputable def vacIncrement (d L N : ℕ) (a₁ βk p₁ : ℝ) : ℝ :=
  (N : ℝ) / 2 * ((L : ℝ) ^ d - 1) * Real.log βk -
    (N : ℝ) / 2 * Real.log (a₁ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / (2 * Real.pi)) -
    (L : ℝ) ^ d * Real.log (fluctNorm N p₁)

/-- **`vacIncrement` is the increment of the step**: for every step setting with `β_k` the paper
coupling `betaU`, `L^d (E'''_k - E_k) = Γ_k`. -/
theorem vacIncrement_eq_step {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ) (ha₁ : 0 < S.a₁)
    (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) :
    (L : ℝ) ^ d * (S.Eppp C - C.Ek) = vacIncrement d L N S.a₁ S.betaU S.p₁ :=
  S.step_increment_eq C ha₁ hβ hp₁

/-- **The total vacuum constant is the class constant plus the normalization**: if `E'` is the
constant of the next class, defined by absorbing the vacuum value `e₀` of the new localized terms,
then `E' = Γ_k + s` with `s = L^d E_k - e₀ / |T^{(k+1)}_1|`: the part of the step's vacuum energy
that the normalization `s` of the step density carries is `s`, and `Γ_k` is what the class keeps. -/
theorem vacIncrement_add_normalization {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ) (hnB : 0 < S.nBlocks)
    (ha₁ : 0 < S.a₁) (hβ : 0 < S.β) (hp₁ : 0 < S.p₁) {Ek' e₀ : ℝ}
    (hE' : Ek' * S.nBlocks = S.Eppp C * S.nU - e₀) :
    Ek' = vacIncrement d L N S.a₁ S.betaU S.p₁ + ((L : ℝ) ^ d * C.Ek - e₀ / S.nBlocks) := by
  have h := S.vacuumEnergy_succ_eq_increment C hnB ha₁ hβ hp₁ hE'
  unfold vacIncrement
  rw [h]
  ring

/-! ### The bound of the Gaussian increment -/

/-- **`log Z₁(p)` is bounded for `p ≥ 1`**: `Z₁(1) ≤ Z₁(p) ≤ (2π)^{N/2}`. -/
theorem abs_log_fluctNorm_le (N : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    |Real.log (fluctNorm N p)| ≤ |Real.log (fluctNorm N 1)| + (N : ℝ) / 2 * |Real.log (2 * Real.pi)| := by
  have h1 : 0 < fluctNorm N 1 := fluctNorm_pos N one_pos
  have hlo : fluctNorm N 1 ≤ fluctNorm N p := fluctNorm_mono N hp
  have hhi := fluctNorm_le N p
  have hpos : 0 < fluctNorm N p := h1.trans_le hlo
  have hN : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  have a1 : Real.log (fluctNorm N 1) ≤ Real.log (fluctNorm N p) := Real.log_le_log h1 hlo
  have a2 : Real.log (fluctNorm N p) ≤ (N : ℝ) / 2 * Real.log (2 * Real.pi) := by
    calc Real.log (fluctNorm N p) ≤ Real.log ((2 * Real.pi) ^ ((N : ℝ) / 2)) :=
          Real.log_le_log hpos hhi
      _ = _ := Real.log_rpow (by positivity) _
  have b1 := neg_abs_le (Real.log (fluctNorm N 1))
  have b2 := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (2 * Real.pi))) hN
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg (Real.log (fluctNorm N 1)),
    mul_nonneg hN (abs_nonneg (Real.log (2 * Real.pi)))]

/-- The leading coefficient `½ N (L^d - 1)` of `log β_k` in `Γ_k`. -/
noncomputable def vacLead (d L N : ℕ) : ℝ := (N : ℝ) / 2 * ((L : ℝ) ^ d - 1)

/-- The `β`-free part of the bound of `|Γ_k|`: `½ N |log (a₁ L^{d-2}/2π)| + L^d (|log Z₁(1)| +
½ N |log 2π|)`. -/
noncomputable def vacFree (d L N : ℕ) (a₁ : ℝ) : ℝ :=
  (N : ℝ) / 2 * |Real.log (a₁ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / (2 * Real.pi))| +
    (L : ℝ) ^ d * (|Real.log (fluctNorm N 1)| + (N : ℝ) / 2 * |Real.log (2 * Real.pi)|)

/-- **The constant of the vacuum bound**: `|Γ_k| ≤ vacConst · (log β_{k+1} + 1)` under the
hypotheses of `sfVacuumInput_of_inherit_renorm`; the provider's constant `C_b` is asked to be at
least this number. -/
noncomputable def vacConst (d L N : ℕ) (a₁ : ℝ) : ℝ :=
  vacLead d L N + vacLead d L N * Real.log (5 / 4) + vacFree d L N a₁

theorem vacLead_nonneg (d L N : ℕ) (hL : 1 ≤ L) : 0 ≤ vacLead d L N := by
  have : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hL)
  unfold vacLead
  have : (0 : ℝ) ≤ (L : ℝ) ^ d - 1 := by linarith
  positivity

theorem vacFree_nonneg (d L N : ℕ) (a₁ : ℝ) : 0 ≤ vacFree d L N a₁ := by
  unfold vacFree
  positivity

theorem vacConst_nonneg (d L N : ℕ) (a₁ : ℝ) (hL : 1 ≤ L) : 0 ≤ vacConst d L N a₁ := by
  have h1 := vacLead_nonneg d L N hL
  have h2 := vacFree_nonneg d L N a₁
  have h3 : 0 ≤ Real.log (5 / 4) := Real.log_nonneg (by norm_num)
  unfold vacConst
  positivity

/-- **The Gaussian increment is `O(log β_k)`**: for `β_k ≥ 1` and `p₁ ≥ 1`,
`|Γ_k| ≤ ½ N (L^d - 1) log β_k + vacFree`. -/
theorem abs_vacIncrement_le (d L N : ℕ) (hL : 1 ≤ L) (a₁ βk p₁ : ℝ) (hβ : 1 ≤ βk) (hp : 1 ≤ p₁) :
    |vacIncrement d L N a₁ βk p₁| ≤ vacLead d L N * Real.log βk + vacFree d L N a₁ := by
  have hLd : (0 : ℝ) ≤ (L : ℝ) ^ d := by positivity
  have hlead := vacLead_nonneg d L N hL
  have hlog : 0 ≤ Real.log βk := Real.log_nonneg hβ
  have h1 : |(N : ℝ) / 2 * ((L : ℝ) ^ d - 1) * Real.log βk| = vacLead d L N * Real.log βk := by
    unfold vacLead; rw [abs_of_nonneg (by unfold vacLead at hlead; exact mul_nonneg hlead hlog)]
  have h2 : |(N : ℝ) / 2 * Real.log (a₁ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / (2 * Real.pi))| =
      (N : ℝ) / 2 * |Real.log (a₁ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / (2 * Real.pi))| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) / 2)]
  have h3 : |(L : ℝ) ^ d * Real.log (fluctNorm N p₁)| =
      (L : ℝ) ^ d * |Real.log (fluctNorm N p₁)| := by rw [abs_mul, abs_of_nonneg hLd]
  have h4 := mul_le_mul_of_nonneg_left (abs_log_fluctNorm_le N hp) hLd
  have e : ∀ x y z : ℝ, |x - y - z| ≤ |x| + |y| + |z| := fun x y z =>
    (abs_sub _ _).trans (add_le_add_left (abs_sub _ _) _)
  unfold vacIncrement vacFree
  refine (e _ _ _).trans ?_
  rw [h1, h2, h3]
  nlinarith [h4]

/-! ### The map and the input -/

/-- **The vacuum map `ΦE` of the small-field step** (A4-1g; P4 (2.1), (2.41), (2.63)): the Gaussian
increment `Γ_k` of the step, at the coupling `β_k`, the kernel coefficient `a₁ = a` of the
constants (`OpConsts.aKer`, the one of `stepDensity`) and the radius `p₁ = p(β_k)` of the
fluctuation cutoff. It depends on the small-field data only through `β_k`, not on the flow `E_j`
(the extensive part `L^d E_k - e₀/|T^{(k+1)}_1|` is the normalization `s`,
`vacIncrement_add_normalization`), and it is the same formula off the class. -/
noncomputable def vacMap (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
    (C7 : ℝ → ℝ → Consts7) (cs₀ : ℝ → ℝ → OpConsts) (ϱ : ℝ → ℝ → ℝ) :
    ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
      SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) → (ℕ → ℝ) → ℝ :=
  fun κ c₉ _ _ k _ sf _ =>
    vacIncrement d (T κ c₉).L N (cs₀ κ c₉).aKer (sf.β k) ((P6 κ c₉).p (sf.β k))

/-- **A4-1g from the inherited data and the renormalization (P4 (5.28), (2.1), (2.41), (2.63)).**
For the vacuum map `vacMap` the new constant satisfies `|ΦE| ≤ C_b (log β_{k+1} + 1)`:
* `β_k = β L^{k(d-2)} γ_k` with `|log γ_k| ≤ 1/20` (the input class, (I.2)), so `β_k ≥ (19/20) β`;
* the image keeps `β_k` (`SFInheritInput`) and its `β_{k+1} = β_k L^{d-2}/(1 + ξ₃)` with
  `|ξ₃| ≤ 1/4` (`SFRenormInput`, `CoeffBounds.beta_succ_ge`), so `β_k ≤ (5/4) β_{k+1}`;
* the cutoff `p(β)` of the class constants is at least `1` for large `β` (`hp`), so
  `|log Z₁(p(β_k))|` is bounded (`abs_log_fluctNorm_le`);
* `hCb` is the range of the provider's constant `C_b = (cs₀ κ c₉).Cb` (it is at least `vacConst`,
  the constant `½ N (L^d - 1) (1 + log (5/4)) + ⋯` of `abs_vacIncrement_le`).
The hypotheses `hp`, `hCb` are ranges of the constants; the other two are the existing spine
sub-inputs A4-1a and A4-1c. -/
theorem sfVacuumInput_of_inherit_renorm (d N : ℕ) (T : ℝ → ℝ → Typing)
    (P6 : ℝ → ℝ → Def6.Consts) (C7 : ℝ → ℝ → Consts7) (cs₀ : ℝ → ℝ → OpConsts)
    (ϱ : ℝ → ℝ → ℝ)
    (hp : ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → 1 ≤ (P6 κ c₉).p x)
    (hCb : ∀ κ : ℝ, 0 < κ → ∀ c₉ : ℝ, 0 < c₉ →
      vacConst d (T κ c₉).L N (cs₀ κ c₉).aKer ≤ (cs₀ κ c₉).Cb)
    (Φ : ∀ (κ c₉ _ _ : ℝ) (k : ℕ) [NeZero (T κ c₉).L],
      SFData d (T κ c₉).L (C7 κ c₉).m₁ k N (ϱ κ c₉) →
        SFData d (T κ c₉).L (C7 κ c₉).m₁ (k + 1) N (ϱ κ c₉))
    (hI : SFInheritInput d N T P6 C7 cs₀ ϱ Φ) (hRn : SFRenormInput d N T P6 C7 cs₀ ϱ Φ) :
    SFVacuumInput d N T P6 C7 cs₀ ϱ Φ (vacMap d N T P6 C7 cs₀ ϱ) := by
  intro κ hκ c₉ hc₉
  obtain ⟨x₀, hx₀⟩ := hp κ hκ c₉ hc₉
  obtain ⟨β₁, h1⟩ := hI κ hκ c₉ hc₉
  obtain ⟨β₂, h2⟩ := hRn κ hκ c₉ hc₉
  refine ⟨max (max β₁ β₂) (2 * max x₀ 1), ?_⟩
  intro β hβ ν hν hνL _ k hk1 hkk sf hsf Ev _
  have hβ1 : β₁ ≤ β := (le_max_left _ _).trans ((le_max_left _ _).trans hβ)
  have hβ2 : β₂ ≤ β := (le_max_right _ _).trans ((le_max_left _ _).trans hβ)
  have hβx : 2 * max x₀ 1 ≤ β := (le_max_right _ _).trans hβ
  have hm1 : 1 ≤ max x₀ 1 := le_max_right _ _
  have hI' := h1 β hβ1 ν hν hνL k hk1 hkk sf hsf
  have hR' := h2 β hβ2 ν hν hνL k hk1 hkk sf hsf
  obtain ⟨-, -, -, -, -, -, hrun⟩ := hsf
  obtain ⟨γ, hγ0, hγ, hβk⟩ := hrun.beta_eq k le_rfl
  have hL1 : 1 ≤ (T κ c₉).L := by have := hrun.hL; omega
  have hL1r : (1 : ℝ) ≤ ((T κ c₉).L : ℝ) := by exact_mod_cast hL1
  -- the size of `β_k`
  have hγlow : 19 / 20 ≤ γ := by
    have h := (abs_le.1 hγ).1
    have h' : Real.exp (-(1 / 20)) ≤ γ := (Real.le_log_iff_exp_le hγ0).1 h
    have h'' := Real.add_one_le_exp (-(1 / 20) : ℝ)
    linarith
  have hpowge : (1 : ℝ) ≤ ((T κ c₉).L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ hL1r
  have hβpos : 0 < β := by linarith
  have hβkge : 19 / 20 * β ≤ sf.β k := by
    rw [hβk]
    have : β * 1 * (19 / 20) ≤ β * ((T κ c₉).L : ℝ) ^ (k * (d - 2)) * γ := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hpowge hβpos.le) hγlow (by norm_num)
        (by positivity)
    linarith
  have hβk2 : 19 / 10 ≤ sf.β k := by linarith
  have hβk1 : 1 ≤ sf.β k := by linarith
  have hpk : 1 ≤ (P6 κ c₉).p (sf.β k) := hx₀ _ (by linarith [le_max_left x₀ 1])
  -- the step of the flow
  have hkeep : (Φ κ c₉ β ν k sf).β k = sf.β k := (hI'.1 k le_rfl).1
  obtain ⟨hpos', hge'⟩ := hR'.1.beta_succ_ge hL1 (by rw [hkeep]; linarith)
  rw [hkeep] at hge'
  have hLd2 : (1 : ℝ) ≤ ((T κ c₉).L : ℝ) ^ (d - 2) := one_le_pow₀ hL1r
  have hβ'ge : 4 / 5 * sf.β k ≤ (Φ κ c₉ β ν k sf).β (k + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hLd2 (by linarith : (0 : ℝ) ≤ sf.β k)]
  have hβ'1 : 1 ≤ (Φ κ c₉ β ν k sf).β (k + 1) := by linarith
  have hlam : 0 ≤ Real.log ((Φ κ c₉ β ν k sf).β (k + 1)) := Real.log_nonneg hβ'1
  have hlogk : Real.log (sf.β k) ≤
      Real.log ((Φ κ c₉ β ν k sf).β (k + 1)) + Real.log (5 / 4) := by
    rw [← Real.log_mul hpos'.ne' (by norm_num)]
    exact Real.log_le_log (by linarith) (by linarith)
  -- the bound
  have hb := abs_vacIncrement_le d (T κ c₉).L N hL1 (cs₀ κ c₉).aKer (sf.β k)
    ((P6 κ c₉).p (sf.β k)) hβk1 hpk
  have hlead := vacLead_nonneg d (T κ c₉).L N hL1
  have hfree := vacFree_nonneg d (T κ c₉).L N (cs₀ κ c₉).aKer
  have hl54 : 0 ≤ Real.log (5 / 4) := Real.log_nonneg (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hlogk hlead
  have hC := hCb κ hκ c₉ hc₉
  have hstep : vacLead d (T κ c₉).L N * Real.log (sf.β k) + vacFree d (T κ c₉).L N
      (cs₀ κ c₉).aKer ≤ vacConst d (T κ c₉).L N (cs₀ κ c₉).aKer *
        (Real.log ((Φ κ c₉ β ν k sf).β (k + 1)) + 1) := by
    unfold vacConst
    nlinarith [mul_nonneg (mul_nonneg hlead hl54) hlam, mul_nonneg hfree hlam]
  calc |vacMap d N T P6 C7 cs₀ ϱ κ c₉ β ν k sf Ev|
      ≤ vacLead d (T κ c₉).L N * Real.log (sf.β k) + vacFree d (T κ c₉).L N
          (cs₀ κ c₉).aKer := hb
    _ ≤ _ := hstep
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (by linarith)

end Balaban.RootFSpine
