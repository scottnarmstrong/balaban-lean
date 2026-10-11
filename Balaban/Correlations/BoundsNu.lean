/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.ZeroLimit

/-!
# Step B: bounds for `ν > 0` (CORRELATIONS.md §3.2)

`|m(ν) - 1| ≤ c β^{-1+ρ₁}` and `|G_tr(ν, x)|, |G_lg(ν, x)| ≤ c (1+|x|)^{-(d-2)} e^{-c'√ν |x|}`
from the infinite-volume form of (F2), (F3) (Lemma 3.0) and the kernel decay.
-/

@[expose] public section

open Filter Topology Finset

namespace Balaban.Correlations

open Balaban Balaban.Flow

/-- The constant `K₁ = √2 c_* r/(1 - r)`, `r = L^{-ρ₀}`, in `|m_J - 1| ≤ K₁ β^{-1+ρ₁}`. -/
noncomputable def K1 (L : ℕ) (cS ρ₀ : ℝ) : ℝ :=
  Real.sqrt 2 * cS * ((L : ℝ) ^ (-ρ₀) / (1 - (L : ℝ) ^ (-ρ₀)))

theorem K1_nonneg {L : ℕ} (hL : 2 ≤ L) {cS ρ₀ : ℝ} (hcS : 0 ≤ cS) (hρ₀ : 0 < ρ₀) :
    0 ≤ K1 L cS ρ₀ := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hr1 : (L : ℝ) ^ (-ρ₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
  have hr0 : 0 ≤ (L : ℝ) ^ (-ρ₀) := (Real.rpow_pos_of_pos (by linarith) _).le
  unfold K1
  have : 0 ≤ (L : ℝ) ^ (-ρ₀) / (1 - (L : ℝ) ^ (-ρ₀)) := div_nonneg hr0 (by linarith)
  positivity

variable {d N L M : ℕ} [NeZero L] {hN : 2 ≤ N} {a cS cX cP ρ₀ ρ₁ γ₀ β : ℝ} {J : ℝ → ℕ}
  {ξ : ℝ → ℕ → Fin 3 → ℝ} {μ : ℕ → ℝ → (Fin d → ℤ) → ℝ}
  {rtr rlg : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ} {em : ℕ → ℝ → (Fin d → ℤ) → ℝ}
  {rtrLim rlgLim : ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
  {rtrZero rlgZero : (Fin d → ℤ) → (Fin d → ℤ) → ℝ}

theorem rpow_neg_two_le {β ρ₁ : ℝ} (hβ1 : 1 ≤ β) (hρ₁0 : 0 < ρ₁) :
    (β ^ 2)⁻¹ ≤ β ^ (-1 + ρ₁) := by
  have hβ : 0 < β := by linarith
  have : (β ^ 2)⁻¹ = β ^ (-(2 : ℝ)) := by rw [Real.rpow_neg hβ.le, Real.rpow_two]
  rw [this]
  exact Real.rpow_le_rpow_of_exponent_le hβ1 (by linarith)

theorem bounds_pos_nu (hL : 2 ≤ L) (hM : 1 ≤ M)
    (hβ1 : 1 ≤ β) (hρ₀ : 0 < ρ₀) (hcS : 0 ≤ cS) (hρ₁0 : 0 < ρ₁) (hρ₁ : ρ₁ < 1)
    (HS : ∀ ν ∈ Set.Icc (0 : ℝ) 1, SeqHyp L γ₀ (cX / β) (ξ ν))
    (hJb : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, (L : ℝ) ^ J ν * Real.sqrt ν ≤ (L : ℝ) ^ 2)
    (h2 : C1StarF2 d N L M hN cS ρ₀ ρ₁ J β ξ μ em)
    (h3 : C1StarF3 d N L M hN a cS cP ρ₀ J β ξ μ rtr rlg rtrLim rlgLim rtrZero rlgZero)
    {t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
    {t0 : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ} {C_G δ_G C_P : ℝ}
    (H : KernelHyp d L a t t0 C_G δ_G C_P) (HL : KernelHypLarge d L a t C_G δ_G)
    {C1 : ℝ} (hC1nn : 0 ≤ C1) (hC1 : MainSumBound d L C_G δ_G C1)
    {m : ℝ → ℝ} {Gtr Glg : ℝ → (Fin d → ℤ) → ℝ}
    (hm : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, LimAlong (M * L) (fun ℓ _ => blockM d N ℓ hN β ν) (m ν))
    (hGtr : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ z,
      LimAlong (M * L) (fun ℓ _ => blockGtr d N ℓ hN β ν (embedZ ℓ z)) (Gtr ν z))
    (hGlg : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ z,
      LimAlong (M * L) (fun ℓ _ => blockGlg d N ℓ hN β ν (embedZ ℓ z)) (Glg ν z))
    {c c' : ℝ} (hc1 : cS + K1 L cS ρ₀ ≤ c)
    (hc2 : (1 + K1 L cS ρ₀) ^ 2 * (2 * C_G * C1) + cS ≤ c) (hc'1 : c' ≤ cP)
    (hc'2 : c' ≤ δ_G / (2 * (L : ℝ) ^ 2)) :
    ∀ ν ∈ Set.Ioc (0 : ℝ) 1, |m ν - 1| ≤ c * β ^ (-1 + ρ₁) ∧ ∀ x,
      |Gtr ν x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2)) * Real.exp (-(c' * Real.sqrt ν * ‖x‖)) ∧
      |Glg ν x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2)) * Real.exp (-(c' * Real.sqrt ν * ‖x‖)) := by
  intro ν hν
  have hIcc : ν ∈ Set.Icc (0 : ℝ) 1 := ⟨hν.1.le, hν.2⟩
  have HSν := HS ν hIcc
  have hβ : 0 < β := by linarith
  have hK0 := K1_nonneg hL hcS hρ₀
  have hε0 : 0 ≤ β ^ (-1 + ρ₁) := Real.rpow_nonneg hβ.le _
  have hε1 : β ^ (-1 + ρ₁) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hβ1 (by linarith)
  have hmag : ∀ x, |magJ L d (ξ ν) (fun j => μ j ν) β (J ν) x - 1| ≤
      K1 L cS ρ₀ * β ^ (-1 + ρ₁) := fun x =>
    abs_magJ_sub_one_le HSν hρ₀ hcS hβ (J ν) (fun j hj => h2.1 j hj ν hIcc x)
  have hmagb : ∀ x, |magJ L d (ξ ν) (fun j => μ j ν) β (J ν) x| ≤ 1 + K1 L cS ρ₀ := by
    intro x
    have h := hmag x
    have h' : K1 L cS ρ₀ * β ^ (-1 + ρ₁) ≤ K1 L cS ρ₀ := by nlinarith
    have := abs_le.1 (h.trans h')
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hLe : (0 : ℝ) < (L : ℝ) ^ (2 * J ν * (d - 2)) := by
    have : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hLe1 : ((L : ℝ) ^ (2 * J ν * (d - 2)))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ L)))
  refine ⟨?_, fun x => ?_⟩
  · have hmJ0 := abs_m_sub_magJ_le hM hL (hm ν hν) h2 hν 0
    have hb1 : cS * (β ^ 2)⁻¹ * ((L : ℝ) ^ (2 * J ν * (d - 2)))⁻¹ ≤ cS * β ^ (-1 + ρ₁) := by
      calc cS * (β ^ 2)⁻¹ * ((L : ℝ) ^ (2 * J ν * (d - 2)))⁻¹ ≤ cS * (β ^ 2)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hLe1 (by positivity)
        _ ≤ cS * β ^ (-1 + ρ₁) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left (rpow_neg_two_le hβ1 hρ₁0) hcS
    calc |m ν - 1| = |(m ν - magJ L d (ξ ν) (fun j => μ j ν) β (J ν) 0) +
          (magJ L d (ξ ν) (fun j => μ j ν) β (J ν) 0 - 1)| := by ring_nf
      _ ≤ |m ν - magJ L d (ξ ν) (fun j => μ j ν) β (J ν) 0| +
          |magJ L d (ξ ν) (fun j => μ j ν) β (J ν) 0 - 1| := abs_add_le _ _
      _ ≤ cS * β ^ (-1 + ρ₁) + K1 L cS ρ₀ * β ^ (-1 + ρ₁) := add_le_add (hmJ0.trans hb1) (hmag 0)
      _ ≤ c * β ^ (-1 + ρ₁) := by nlinarith
  · have hcnn : 0 ≤ c := by
      have : 0 ≤ (1 + K1 L cS ρ₀) ^ 2 * (2 * C_G * C1) := by
        have := H.nonneg_G; positivity
      linarith
    set R : ℝ := (1 + ‖x‖) ^ (-((d : ℝ) - 2)) with hR
    set E : ℝ := Real.exp (-(c' * Real.sqrt ν * ‖x‖)) with hE
    have hR0 : 0 ≤ R := Real.rpow_nonneg (by positivity) _
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hx1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have hrem := abs_rtrLim_le hM hL h3 hν x 0
    simp only [sub_zero] at hrem
    have hrem' : ∀ w, |w| ≤ cS * (1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) *
        Real.exp (-(cP * Real.sqrt ν * ‖x‖)) → |w| ≤ cS * R * E := by
      intro w hw
      refine hw.trans ?_
      have e1 : (1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) ≤ R :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have e2 : Real.exp (-(cP * Real.sqrt ν * ‖x‖)) ≤ E := by
        refine Real.exp_le_exp.2 ?_
        have : c' * Real.sqrt ν * ‖x‖ ≤ cP * Real.sqrt ν * ‖x‖ := by
          have := Real.sqrt_nonneg ν
          have := norm_nonneg x
          gcongr
        linarith
      calc cS * (1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) * Real.exp (-(cP * Real.sqrt ν * ‖x‖))
          ≤ cS * R * E := by gcongr
        _ = _ := rfl
    refine ⟨?_, ?_⟩
    · have hid := gtr_eq hM hL (hGtr ν hν) h3 HL hν (fun j hj => mass_mem' HSν hν hj (hJb ν hν)) x 0
      simp only [sub_zero] at hid
      have hS := hC1 HSν hβ hν.1 (hJb ν hν) HL.g2 (fun j hj => mass_mem' HSν hν hj (hJb ν hν)) x 0
      simp only [sub_zero] at hS
      have hEG : Real.exp (-(δ_G / (2 * (L : ℝ) ^ 2) * Real.sqrt ν * ‖x‖)) ≤ E := by
        refine Real.exp_le_exp.2 ?_
        have : c' * Real.sqrt ν * ‖x‖ ≤ δ_G / (2 * (L : ℝ) ^ 2) * Real.sqrt ν * ‖x‖ := by
          have := Real.sqrt_nonneg ν
          have := norm_nonneg x
          gcongr
        linarith
      have h2b : 2 / β ≤ 2 := by
        rw [div_le_iff₀ hβ]; linarith
      have hCG := H.nonneg_G
      have hS' : |∑ j ∈ range (J ν), (β * gammaR (ξ ν) j)⁻¹ *
          t j (ν * deltaR (ξ ν) j) x 0| ≤ 2 * C_G * C1 * R * E := by
        have hh : 2 / β * C_G * C1 * R *
            Real.exp (-(δ_G / (2 * (L : ℝ) ^ 2) * Real.sqrt ν * ‖x‖)) ≤ 2 * C_G * C1 * R * E := by
          gcongr
        exact hS.trans hh
      rw [hid]
      set mx := magJ L d (ξ ν) (fun j => μ j ν) β (J ν) x
      set m0 := magJ L d (ξ ν) (fun j => μ j ν) β (J ν) 0
      set S := ∑ j ∈ range (J ν), (β * gammaR (ξ ν) j)⁻¹ * t j (ν * deltaR (ξ ν) j) x 0
      have hr := hrem' _ hrem.1
      calc |mx * m0 * S + rtrLim ν x 0| ≤ |mx * m0 * S| + |rtrLim ν x 0| := abs_add_le _ _
        _ ≤ (1 + K1 L cS ρ₀) * (1 + K1 L cS ρ₀) * (2 * C_G * C1 * R * E) + cS * R * E := by
            refine add_le_add ?_ hr
            rw [abs_mul, abs_mul]
            have := hmagb x
            have := hmagb 0
            gcongr
        _ = ((1 + K1 L cS ρ₀) ^ 2 * (2 * C_G * C1) + cS) * R * E := by ring
        _ ≤ c * R * E := by gcongr
    · rw [show Glg ν x = rlgLim ν x 0 by
        simpa using glg_eq hM hL (hGlg ν hν) h3 hν x 0]
      refine (hrem' _ hrem.2).trans ?_
      have : cS ≤ c := by
        have : 0 ≤ (1 + K1 L cS ρ₀) ^ 2 * (2 * C_G * C1) := by
          have := H.nonneg_G; positivity
        linarith
      calc cS * R * E ≤ c * R * E := by gcongr

end Balaban.Correlations
