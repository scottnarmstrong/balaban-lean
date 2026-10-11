/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.BoundsNu
public import Balaban.Correlations.GoldstoneUniform

/-!
# Steps C, D, E: the limits `ν ↓ 0`, the lattice Green's function, the Goldstone asymptotics
(CORRELATIONS.md §3.3-3.5)
-/

@[expose] public section

open Filter Topology Finset

namespace Balaban.Correlations

open Balaban Balaban.Flow

variable {d N L M : ℕ} [NeZero L] {hN : 2 ≤ N} {a cS cX cP ρ₀ ρ₁ γ₀ β : ℝ} {J : ℝ → ℕ}
  {ξ : ℝ → ℕ → Fin 3 → ℝ} {μ : ℕ → ℝ → (Fin d → ℤ) → ℝ}
  {rtr rlg : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ} {em : ℕ → ℝ → (Fin d → ℤ) → ℝ}
  {rtrLim rlgLim : ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
  {rtrZero rlgZero : (Fin d → ℤ) → (Fin d → ℤ) → ℝ}

omit [NeZero L] in
/-- The real `γ_∞` of the running coefficients `ξ`, with `|γ_∞ - 1| ≤ c₈ q/(2(1-q))` and the
Goldstone comparison of the main sum with `(β γ_∞)⁻¹ ∑_j t_j`. -/
theorem exists_gammaInfty {γ₀ δ_G C2 c₈ : ℝ} (hL : 2 ≤ L) {C_G : ℝ} (hC_G : 0 ≤ C_G)
    (hC2 : GoldBound (L : ℝ) d γ₀ δ_G C2) {ξ0 : ℕ → Fin 3 → ℝ} (H0 : SeqHyp L γ₀ c₈ ξ0) (β : ℝ)
    (hβ : 0 < β) :
    ∃ γ : ℝ, |γ - 1| ≤ c₈ * rate (L : ℝ) γ₀ / (2 * (1 - rate (L : ℝ) γ₀)) ∧
      ∀ (t : ℕ → ℝ) (r : ℝ), 0 ≤ r → KernelDecay d (L : ℝ) C_G δ_G r t →
        |∑' j, (β * gammaR ξ0 j)⁻¹ * t j - (β * γ)⁻¹ * ∑' j, t j| ≤
          Real.exp 2 * (c₈ * rate (L : ℝ) γ₀ / (2 * (1 - rate (L : ℝ) γ₀))) * β⁻¹ * C_G * C2 *
            (1 + r) ^ (-(((d - 2 : ℕ) : ℝ) + 2 * γ₀)) := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨γc, hT, hγ1, hbd⟩ := hC2 H0.hc (ξ := xiC ξ0) H0.hs H0.bound_xiC
  have himg : γc.im = 0 := by
    have h1 : Tendsto (fun j => (gammaSeq (xiC ξ0) j).im) atTop (𝓝 γc.im) :=
      (Complex.continuous_im.tendsto _).comp hT
    have h2' : ∀ j, (gammaSeq (xiC ξ0) j).im = 0 := fun j => by
      rw [gammaSeq_xiC]; exact Complex.ofReal_im _
    simp only [h2'] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hγc : γc = (γc.re : ℂ) := Complex.ext (by simp) (by simpa using himg)
  refine ⟨γc.re, ?_, fun t r hr ht => ?_⟩
  · refine le_trans ?_ hγ1
    have := Complex.abs_re_le_norm (γc - 1)
    simpa using this
  · have hb := (hbd (β : ℂ) C_G r t hC_G hr ht).2
    have hser : ∀ j, (betaSeq (L : ℝ) d (xiC ξ0) (β : ℂ) j)⁻¹ *
        (((L : ℝ) : ℂ) ^ (j * (d - 2)) * (t j : ℂ)) =
        (((β * gammaR ξ0 j)⁻¹ * t j : ℝ) : ℂ) := by
      intro j
      rw [betaSeq_eq, gammaSeq_xiC, ← gammaR_eq]
      have h1 : ((L : ℝ) : ℂ) ^ (j * (d - 2)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hL0.ne')
      have h2 : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
      have h3 : (gammaR ξ0 j : ℂ) ≠ 0 := by exact_mod_cast (H0.gammaR_pos j).ne'
      push_cast
      field_simp
      exact mul_div_cancel_left₀ _ h1
    simp only [hser] at hb
    rw [hγc] at hb
    have key : (((∑' j, (β * gammaR ξ0 j)⁻¹ * t j - (β * γc.re)⁻¹ * ∑' j, t j : ℝ)) : ℂ) =
        ∑' j, (((β * gammaR ξ0 j)⁻¹ * t j : ℝ) : ℂ) - ((β : ℂ) * (γc.re : ℂ))⁻¹ *
          ∑' j, (t j : ℂ) := by
      push_cast
      rfl
    rw [← key, Complex.norm_real, Real.norm_eq_abs] at hb
    refine hb.trans (le_of_eq ?_)
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]

theorem limits_zero (hd : 3 ≤ d) (hL : 2 ≤ L) (hM : 1 ≤ M)
    (hβ1 : 1 ≤ β) (hρ₀ : 0 < ρ₀) (hcS : 0 ≤ cS) (hρ₁0 : 0 < ρ₁) (hρ₁ : ρ₁ < 1) (ha : 0 < a)
    (hcP0 : 0 ≤ cP) (hcX : 0 ≤ cX)
    (HS : ∀ ν ∈ Set.Icc (0 : ℝ) 1, SeqHyp L γ₀ (cX / β) (ξ ν))
    (hc1 : ∀ k, Tendsto (fun ν => ξ ν k) (𝓝[>] 0) (𝓝 (ξ 0 k)))
    (hJt : Tendsto J (𝓝[>] 0) atTop)
    (hJb : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, (L : ℝ) ^ J ν * Real.sqrt ν ≤ (L : ℝ) ^ 2)
    (h2 : C1StarF2 d N L M hN cS ρ₀ ρ₁ J β ξ μ em)
    (h3 : C1StarF3 d N L M hN a cS cP ρ₀ J β ξ μ rtr rlg rtrLim rlgLim rtrZero rlgZero)
    {t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
    {t0 : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ} {C_G δ_G C_P : ℝ}
    (H : KernelHyp d L a t t0 C_G δ_G C_P) (HL : KernelHypLarge d L a t C_G δ_G)
    {C2 : ℝ} (hC2 : GoldBound (L : ℝ) d γ₀ δ_G C2) (hC2nn : 0 ≤ C2)
    {m : ℝ → ℝ} {Gtr Glg : ℝ → (Fin d → ℤ) → ℝ}
    (hm : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, LimAlong (M * L) (fun ℓ _ => blockM d N ℓ hN β ν) (m ν))
    (hGtr : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ z,
      LimAlong (M * L) (fun ℓ _ => blockGtr d N ℓ hN β ν (embedZ ℓ z)) (Gtr ν z))
    (hGlg : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ z,
      LimAlong (M * L) (fun ℓ _ => blockGlg d N ℓ hN β ν (embedZ ℓ z)) (Glg ν z))
    {c : ℝ} (hcS' : cS ≤ c)
    (hcA : (1 + K1 L cS ρ₀) ^ 2 * (Real.exp 2 * (cX * rate (L : ℝ) γ₀ /
      (2 * (1 - rate (L : ℝ) γ₀))) * C_G * C2) + cS ≤ c)
    (hcB : cX * rate (L : ℝ) γ₀ / (2 * (1 - rate (L : ℝ) γ₀)) ≤ c) :
    ∃ (m₀ γ : ℝ) (Gtr₀ Glg₀ G : (Fin d → ℤ) → ℝ),
      Tendsto m (𝓝[>] 0) (𝓝 m₀) ∧
      (∀ x, Tendsto (fun ν => Gtr ν x) (𝓝[>] 0) (𝓝 (Gtr₀ x))) ∧
      (∀ x, Tendsto (fun ν => Glg ν x) (𝓝[>] 0) (𝓝 (Glg₀ x))) ∧
      (∀ x, ∑ μ : Fin d, (2 * G x - G (x + Pi.single μ 1) - G (x - Pi.single μ 1))
          = if x = 0 then 1 else 0) ∧
      Tendsto G cofinite (𝓝 0) ∧
      0 < γ ∧ |γ - 1| ≤ c / β ∧
      ∀ x : Fin d → ℤ,
        |Gtr₀ x - m₀ ^ 2 / (β * γ) * G x| ≤
          c * (1 + ‖x‖) ^ (-((d : ℝ) - 2 + min ρ₀ (2 * γ₀))) ∧
        |Glg₀ x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2 + min ρ₀ (2 * γ₀))) := by
  have hβ : 0 < β := by linarith
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have H0 := HS 0 ⟨le_rfl, zero_le_one⟩
  have hI : ∀ᶠ ν in 𝓝[>] (0 : ℝ), ν ∈ Set.Ioc (0 : ℝ) 1 := Ioc_mem_nhdsGT one_pos
  have hIcc : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ν ∈ Set.Icc (0 : ℝ) 1 := fun ν hν => ⟨hν.1.le, hν.2⟩
  have hK0 := K1_nonneg hL hcS hρ₀
  -- magnetization
  obtain ⟨m₀, hmT, hmagT, hm₀⟩ := tendsto_mag hd hL HS hc1 hρ₀ hcS hβ h2.1 h2.2.1 hJt (m := m)
    (fun ν hν x => abs_m_sub_magJ_le hM hL (hm ν hν) h2 hν x)
  have hε1 : β ^ (-1 + ρ₁) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hβ1 (by linarith)
  have hε0 : 0 ≤ β ^ (-1 + ρ₁) := Real.rpow_nonneg hβ.le _
  have hm₀b : |m₀| ≤ 1 + K1 L cS ρ₀ := by
    have h1 : K1 L cS ρ₀ * β ^ (-1 + ρ₁) ≤ K1 L cS ρ₀ := by nlinarith
    have := abs_le.1 (hm₀.trans h1)
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  -- γ
  obtain ⟨γ, hγ1, hγG⟩ := exists_gammaInfty hL H.nonneg_G hC2 H0 β hβ
  set q : ℝ := rate (L : ℝ) γ₀ with hq
  have hq1 : q < 1 := H0.hq1
  have h1q : 0 < 1 - q := by linarith
  have hA3 : cX / β * q / (2 * (1 - q)) = cX * q / (2 * (1 - q)) / β := by
    field_simp
  have hsmall := H0.small
  have hA3le : cX / β * q / (2 * (1 - q)) ≤ 1 / 4 := by
    have : cX / β * q / (2 * (1 - q)) = (cX / β * q / (1 - q)) / 2 := by
      field_simp
    rw [this]; linarith
  have hγpos : 0 < γ := by
    have := abs_le.1 hγ1
    linarith [this.1]
  have hγc : |γ - 1| ≤ c / β := by
    refine hγ1.trans ?_
    rw [hA3]
    exact div_le_div_of_nonneg_right hcB hβ.le
  -- the limit functions
  set S0 : (Fin d → ℤ) → ℝ := fun z => ∑' j, (β * gammaR (ξ 0) j)⁻¹ * t0 j z 0 with hS0
  have hGt : Tendsto (LatticeGreen.latticeGreen d) cofinite (𝓝 0) :=
    LatticeGreen.latticeGreen_tendsto_zero hd
  refine ⟨m₀, γ, fun z => m₀ * m₀ * S0 z + rtrZero z 0, fun z => rlgZero z 0,
    LatticeGreen.latticeGreen d, hmT, ?_, ?_, LatticeGreen.latticeGreen_equation hd, hGt,
    hγpos, hγc, fun x => ?_⟩
  · intro x
    have hlim := (((hmagT x).mul (hmagT 0)).mul
      (tendsto_mainSum hL hd HS hc1 hβ hJt hJb H HL x 0)).add (h3.2.2 x 0).1
    refine hlim.congr' ?_
    filter_upwards [hI] with ν hν
    have hid := gtr_eq hM hL (hGtr ν hν) h3 HL hν (fun j hj => mass_mem' (HS ν (hIcc ν hν)) hν hj (hJb ν hν)) x 0
    simp only [sub_zero] at hid
    exact hid.symm
  · intro x
    refine (h3.2.2 x 0).2.congr' ?_
    filter_upwards [hI] with ν hν
    have := glg_eq hM hL (hGlg ν hν) h3 hν x 0
    simp only [sub_zero] at this
    exact this.symm
  · -- Goldstone bound
    have hk := H.g2 x 0
    rw [sub_zero] at hk
    have hGx : ∑' j, t0 j x 0 = LatticeGreen.latticeGreen d x := by
      have := (H.tsum_eq_latticeGreen ha hd (by omega) x 0).2
      simpa using this
    have hgold := hγG (fun j => t0 j x 0) ‖x‖ (norm_nonneg x) hk
    rw [hGx] at hgold
    have hcast : (((d - 2 : ℕ)) : ℝ) = (d : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    set ρC : ℝ := min ρ₀ (2 * γ₀) with hρC
    have hx1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    set R : ℝ := (1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρC)) with hR
    have hR0 : 0 ≤ R := Real.rpow_nonneg (by positivity) _
    have hRg : (1 + ‖x‖) ^ (-(((d - 2 : ℕ) : ℝ) + 2 * γ₀)) ≤ R := by
      refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
      rw [hcast]
      have : ρC ≤ 2 * γ₀ := min_le_right _ _
      linarith
    have hB : Real.exp 2 * (cX / β * q / (2 * (1 - q))) * β⁻¹ * C_G * C2 *
        (1 + ‖x‖) ^ (-(((d - 2 : ℕ) : ℝ) + 2 * γ₀)) ≤
        Real.exp 2 * (cX * q / (2 * (1 - q))) * C_G * C2 * R := by
      have hCG := H.nonneg_G
      have hA3nn : 0 ≤ cX * q / (2 * (1 - q)) := by
        have := H0.hq0; positivity
      have hA : cX / β * q / (2 * (1 - q)) ≤ cX * q / (2 * (1 - q)) := by
        rw [hA3]; exact div_le_self hA3nn hβ1
      have hβi : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ1
      have hnn : 0 ≤ cX / β * q / (2 * (1 - q)) := by
        rw [hA3]; exact div_nonneg hA3nn hβ.le
      calc Real.exp 2 * (cX / β * q / (2 * (1 - q))) * β⁻¹ * C_G * C2 *
            (1 + ‖x‖) ^ (-(((d - 2 : ℕ) : ℝ) + 2 * γ₀))
          ≤ Real.exp 2 * (cX * q / (2 * (1 - q))) * 1 * C_G * C2 * R := by
            gcongr
        _ = _ := by ring
    -- the remainder at ν = 0
    have hzero : ∀ {f : ℝ → ℝ} {z : ℝ}, Tendsto f (𝓝[>] 0) (𝓝 z) →
        (∀ ν ∈ Set.Ioc (0 : ℝ) 1, f ν ≤ cS * ((1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) +
          ν ^ (((d : ℝ) - 2) / 2)) * Real.exp (-(cP * Real.sqrt ν * ‖x‖))) → z ≤ cS * R := by
      intro f z hf hb
      have hp : (0 : ℝ) < ((d : ℝ) - 2) / 2 := by
        have : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have hT := ((tendsto_rpow_nhdsGT_zero hp).const_add ((1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)))).const_mul cS
      have hT' : Tendsto (fun ν : ℝ => cS * ((1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) +
          ν ^ (((d : ℝ) - 2) / 2))) (𝓝[>] 0) (𝓝 (cS * ((1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) + 0))) := hT
      have e1 : (1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) ≤ R :=
        Real.rpow_le_rpow_of_exponent_le hx1 (by
          have : ρC ≤ ρ₀ := min_le_left _ _
          linarith)
      refine le_of_tendsto_of_tendsto hf hT' ?_ |>.trans (by gcongr; linarith)
      filter_upwards [hI] with ν hν
      refine (hb ν hν).trans ?_
      have e2 : Real.exp (-(cP * Real.sqrt ν * ‖x‖)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ cP * Real.sqrt ν * ‖x‖ := by
          have := hcP0; positivity
        linarith
      have : 0 ≤ cS * ((1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) + ν ^ (((d : ℝ) - 2) / 2)) := by
        have : 0 ≤ ν ^ (((d : ℝ) - 2) / 2) := Real.rpow_nonneg hν.1.le _
        have : 0 ≤ (1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) := Real.rpow_nonneg (by positivity) _
        positivity
      calc _ ≤ cS * ((1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) + ν ^ (((d : ℝ) - 2) / 2)) * 1 := by gcongr
        _ = _ := mul_one _
    have hr0 : |rtrZero x 0| ≤ cS * R := by
      have hlim := (h3.2.2 x 0).1.abs
      exact hzero hlim (fun ν hν => by simpa using (abs_rtrLim_le hM hL h3 hν x 0).1)
    refine ⟨?_, ?_⟩
    · have hform : m₀ * m₀ * S0 x + rtrZero x 0 - m₀ ^ 2 / (β * γ) *
          LatticeGreen.latticeGreen d x =
          m₀ ^ 2 * (S0 x - (β * γ)⁻¹ * LatticeGreen.latticeGreen d x) + rtrZero x 0 := by
        ring
      show |m₀ * m₀ * S0 x + rtrZero x 0 - _| ≤ _
      rw [hform]
      have hS : |S0 x - (β * γ)⁻¹ * LatticeGreen.latticeGreen d x| ≤
          Real.exp 2 * (cX * q / (2 * (1 - q))) * C_G * C2 * R := by
        refine hgold.trans (le_trans ?_ hB)
        exact le_of_eq rfl
      calc |m₀ ^ 2 * (S0 x - (β * γ)⁻¹ * LatticeGreen.latticeGreen d x) + rtrZero x 0|
          ≤ |m₀ ^ 2 * (S0 x - (β * γ)⁻¹ * LatticeGreen.latticeGreen d x)| + |rtrZero x 0| :=
            abs_add_le _ _
        _ ≤ (1 + K1 L cS ρ₀) ^ 2 * (Real.exp 2 * (cX * q / (2 * (1 - q))) * C_G * C2 * R) +
            cS * R := by
            refine add_le_add ?_ hr0
            rw [abs_mul, abs_pow]
            gcongr
        _ = ((1 + K1 L cS ρ₀) ^ 2 * (Real.exp 2 * (cX * q / (2 * (1 - q))) * C_G * C2) + cS) * R := by
            ring
        _ ≤ c * R := by gcongr
    · have : |rlgZero x 0| ≤ cS * R := by
        have hlim := (h3.2.2 x 0).2.abs
        exact hzero hlim (fun ν hν => by simpa using (abs_rtrLim_le hM hL h3 hν x 0).2)
      exact this.trans (by gcongr)

end Balaban.Correlations
