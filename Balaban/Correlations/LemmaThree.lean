/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.MainTerm

/-!
# Lemma 3.0: from finite tori to the infinite-volume form (CORRELATIONS.md §3.1)

For `ν ∈ (0, 1]` the limits `Gtr, Glg` of `blockGtr, blockGlg` along the tori `(M L)^n ∣ ℓ` satisfy
the infinite-volume form of (F3):
`Gtr(x - y) = m_J(ν; x) m_J(ν; y) ∑_{j<J} (β γ_j)⁻¹ t_j^{ν δ_j}(x, y) + r_tr(ν; x, y)`,
`Glg(x - y) = r_lg(ν; x, y)`, with `r_tr, r_lg` the limits of the remainders on the tori, and the
bounds of (F2), (F3) pass to the limits.
-/

@[expose] public section

open Filter Topology Finset

namespace Balaban.Correlations

open Balaban Balaban.Flow

variable {d N L M : ℕ}

/-- Tori with `(M L)^{n₁} ∣ ℓ` are admissible at scale `J` and large compared with `w`. -/
theorem exists_good_tori (hM : 1 ≤ M) (hL : 2 ≤ L) (J : ℕ) (w : Fin d → ℤ) :
    ∃ n₁ : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ], (M * L) ^ n₁ ∣ ℓ →
      M * L ^ (J + 1) ∣ ℓ ∧ ∀ i, 2 * |w i| < (ℓ : ℤ) := by
  have hq : 2 ≤ M * L := by nlinarith
  set R : ℕ := Finset.univ.sup (fun i => (w i).natAbs) + 1 with hR
  refine ⟨max (J + 1) (4 * R), fun ℓ _ hd => ⟨admissible_of_dvd_pow (le_max_left _ _) hd, ?_⟩⟩
  have h4 : 4 * R ≤ ℓ := four_mul_le_of_dvd_pow hq (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    (le_max_right _ _) hd
  intro i
  have h1 : (w i).natAbs ≤ Finset.univ.sup (fun i => (w i).natAbs) :=
    Finset.le_sup (f := fun i => (w i).natAbs) (Finset.mem_univ i)
  rw [Int.abs_eq_natAbs]
  omega

variable [NeZero L] {hN : 2 ≤ N} {a cS cP ρ₀ β : ℝ} {J : ℝ → ℕ}
  {ξ : ℝ → ℕ → Fin 3 → ℝ} {μ : ℕ → ℝ → (Fin d → ℤ) → ℝ}
  {rtr rlg : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
  {rtrLim rlgLim : ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
  {rtrZero rlgZero : (Fin d → ℤ) → (Fin d → ℤ) → ℝ}

/-- Lemma 3.0, transverse part. -/
theorem gtr_eq (hM : 1 ≤ M) (hL : 2 ≤ L) {Gtr : (Fin d → ℤ) → ℝ} {ν : ℝ}
    (hGtr : ∀ z, LimAlong (M * L) (fun ℓ _ => blockGtr d N ℓ hN β ν (embedZ ℓ z)) (Gtr z))
    (h3 : C1StarF3 d N L M hN a cS cP ρ₀ J β ξ μ rtr rlg rtrLim rlgLim rtrZero rlgZero)
    {t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ} {C_G δ_G : ℝ}
    (H : KernelHypLarge d L a t C_G δ_G) (hν : ν ∈ Set.Ioc (0 : ℝ) 1)
    (hμ : ∀ j < J ν, 0 < ν * deltaR (ξ ν) j ∧
      ν * deltaR (ξ ν) j * (L : ℝ) ^ (2 * (j + 1)) ≤ 2 * (L : ℝ) ^ 4) (x y : Fin d → ℤ) :
    Gtr (x - y) =
      magJ L d (ξ ν) (fun j => μ j ν) β (J ν) x * magJ L d (ξ ν) (fun j => μ j ν) β (J ν) y *
        (∑ j ∈ range (J ν), (β * gammaR (ξ ν) j)⁻¹ * t j (ν * deltaR (ξ ν) j) x y)
        + rtrLim ν x y := by
  have hq : 2 ≤ M * L := by nlinarith
  have hlim := ((H.limAlong_mainTr hM hL (β := β) hμ x y).const_mul
    (magJ L d (ξ ν) (fun j => μ j ν) β (J ν) x * magJ L d (ξ ν) (fun j => μ j ν) β (J ν) y)).add
    (h3.2.1 ν hν x y).1
  obtain ⟨n₁, hn₁⟩ := exists_good_tori hM hL (J ν) (x - y)
  have hev : LimAlong (M * L) (fun ℓ _ => blockGtr d N ℓ hN β ν (embedZ ℓ (x - y)))
      (magJ L d (ξ ν) (fun j => μ j ν) β (J ν) x * magJ L d (ξ ν) (fun j => μ j ν) β (J ν) y *
        (∑ j ∈ range (J ν), (β * gammaR (ξ ν) j)⁻¹ * t j (ν * deltaR (ξ ν) j) x y)
        + rtrLim ν x y) := by
    refine LimAlong.congr ⟨n₁, fun ℓ _ hd => ?_⟩ hlim
    obtain ⟨hadm, hsz⟩ := hn₁ ℓ hd
    exact (h3.1 ν hν x y ℓ hadm hsz).1.symm
  exact LimAlong.unique hq (hGtr (x - y)) hev

/-- Lemma 3.0, longitudinal part. -/
theorem glg_eq (hM : 1 ≤ M) (hL : 2 ≤ L) {Glg : (Fin d → ℤ) → ℝ} {ν : ℝ}
    (hGlg : ∀ z, LimAlong (M * L) (fun ℓ _ => blockGlg d N ℓ hN β ν (embedZ ℓ z)) (Glg z))
    (h3 : C1StarF3 d N L M hN a cS cP ρ₀ J β ξ μ rtr rlg rtrLim rlgLim rtrZero rlgZero)
    (hν : ν ∈ Set.Ioc (0 : ℝ) 1) (x y : Fin d → ℤ) : Glg (x - y) = rlgLim ν x y := by
  have hq : 2 ≤ M * L := by nlinarith
  obtain ⟨n₁, hn₁⟩ := exists_good_tori hM hL (J ν) (x - y)
  have hev : LimAlong (M * L) (fun ℓ _ => blockGlg d N ℓ hN β ν (embedZ ℓ (x - y)))
      (rlgLim ν x y) := by
    refine LimAlong.congr ⟨n₁, fun ℓ _ hd => ?_⟩ (h3.2.1 ν hν x y).2
    obtain ⟨hadm, hsz⟩ := hn₁ ℓ hd
    exact (h3.1 ν hν x y ℓ hadm hsz).2.1.symm
  exact LimAlong.unique hq (hGlg (x - y)) hev

/-- The bound on the remainder passes to the limit. -/
theorem abs_rtrLim_le (hM : 1 ≤ M) (hL : 2 ≤ L)
    (h3 : C1StarF3 d N L M hN a cS cP ρ₀ J β ξ μ rtr rlg rtrLim rlgLim rtrZero rlgZero)
    {ν : ℝ} (hν : ν ∈ Set.Ioc (0 : ℝ) 1) (x y : Fin d → ℤ) :
    |rtrLim ν x y| ≤ cS * ((1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) + ν ^ (((d : ℝ) - 2) / 2)) *
      Real.exp (-(cP * Real.sqrt ν * ‖x - y‖)) ∧
    |rlgLim ν x y| ≤ cS * ((1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) + ν ^ (((d : ℝ) - 2) / 2)) *
      Real.exp (-(cP * Real.sqrt ν * ‖x - y‖)) := by
  have hq : 2 ≤ M * L := by nlinarith
  obtain ⟨n₁, hn₁⟩ := exists_good_tori hM hL (J ν) (x - y)
  constructor
  · have := LimAlong.abs_sub_le hq (c := 0)
      (B := cS * ((1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) + ν ^ (((d : ℝ) - 2) / 2)) *
        Real.exp (-(cP * Real.sqrt ν * ‖x - y‖))) (h3.2.1 ν hν x y).1
      ⟨n₁, fun ℓ _ hd => by
        obtain ⟨hadm, hsz⟩ := hn₁ ℓ hd
        simpa using (h3.1 ν hν x y ℓ hadm hsz).2.2.1⟩
    simpa using this
  · have := LimAlong.abs_sub_le hq (c := 0)
      (B := cS * ((1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) + ν ^ (((d : ℝ) - 2) / 2)) *
        Real.exp (-(cP * Real.sqrt ν * ‖x - y‖))) (h3.2.1 ν hν x y).2
      ⟨n₁, fun ℓ _ hd => by
        obtain ⟨hadm, hsz⟩ := hn₁ ℓ hd
        simpa using (h3.1 ν hν x y ℓ hadm hsz).2.2.2⟩
    simpa using this

/-- The bound on `e_m` passes to the limit: `|m - m_J(ν; x)| ≤ c_* β⁻² L^{-2J(d-2)}`. -/
theorem abs_m_sub_magJ_le (hM : 1 ≤ M) (hL : 2 ≤ L) {ρ₁ cStar : ℝ} {em : ℕ → ℝ → (Fin d → ℤ) → ℝ}
    {m : ℝ} {ν : ℝ}
    (hm : LimAlong (M * L) (fun ℓ _ => blockM d N ℓ hN β ν) m)
    (h2 : C1StarF2 d N L M hN cStar ρ₀ ρ₁ J β ξ μ em) (hν : ν ∈ Set.Ioc (0 : ℝ) 1)
    (x : Fin d → ℤ) :
    |m - magJ L d (ξ ν) (fun j => μ j ν) β (J ν) x| ≤
      cStar * (β ^ 2)⁻¹ * ((L : ℝ) ^ (2 * J ν * (d - 2)))⁻¹ := by
  have hq : 2 ≤ M * L := by nlinarith
  obtain ⟨ℓ₀, h⟩ := h2.2.2 ν hν x
  refine LimAlong.abs_sub_le hq hm ⟨ℓ₀ + J ν + 1, fun ℓ _ hd => ?_⟩
  have hadm : M * L ^ (J ν + 1) ∣ ℓ := admissible_of_dvd_pow (by omega) hd
  have hle : ℓ₀ ≤ ℓ := by
    have h1 : (M * L) ^ (ℓ₀ + J ν + 1) ≤ ℓ := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne ℓ)) hd
    have h2 : ℓ₀ + J ν + 1 < (M * L) ^ (ℓ₀ + J ν + 1) :=
      (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left hq _)
    omega
  obtain ⟨he, hb⟩ := h ℓ hle hadm
  rw [he]
  simpa using hb

theorem tendsto_rpow_nhdsGT_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun ν : ℝ => ν ^ p) (𝓝[>] 0) (𝓝 0) := by
  have := (Real.continuousAt_rpow_const (0 : ℝ) p (Or.inr hp.le)).tendsto
  rw [Real.zero_rpow hp.ne'] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- `ν^{p/2} e^{-c√ν r} ≤ C (1+r)^{-p} e^{-(c/2)√ν r}` for `ν ∈ (0,1]`, `r ≥ 0`. -/
theorem exists_rpow_exp_le {p c : ℝ} (hp : 0 < p) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ r : ℝ, 0 ≤ r →
      ν ^ (p / 2) * Real.exp (-(c * Real.sqrt ν * r)) ≤
        C * (1 + r) ^ (-p) * Real.exp (-(c / 2 * Real.sqrt ν * r)) := by
  set ε : ℝ := min 1 (c / (2 * p)) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεp : p * ε ≤ c / 2 := by
    have : ε ≤ c / (2 * p) := min_le_right _ _
    calc p * ε ≤ p * (c / (2 * p)) := by gcongr
      _ = c / 2 := by field_simp
  refine ⟨(ε⁻¹) ^ p, by positivity, fun ν hν r hr => ?_⟩
  set s : ℝ := Real.sqrt ν with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hν.1
  have hs1 : s ≤ 1 := Real.sqrt_le_one.2 hν.2
  have hνs : ν ^ (p / 2) = s ^ p := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_mul hν.1.le]; congr 1; ring
  set t : ℝ := s * r with ht
  have ht0 : 0 ≤ t := by positivity
  have h1 : 1 + t ≤ ε⁻¹ * Real.exp (ε * t) := by
    have := Real.add_one_le_exp (ε * t)
    have h2 : ε * (1 + t) ≤ Real.exp (ε * t) := by nlinarith [mul_nonneg hε0.le ht0]
    calc 1 + t = ε⁻¹ * (ε * (1 + t)) := by field_simp
      _ ≤ _ := by gcongr
  have h2 : (1 + t) ^ p ≤ (ε⁻¹) ^ p * Real.exp (p * ε * t) := by
    calc (1 + t) ^ p ≤ (ε⁻¹ * Real.exp (ε * t)) ^ p :=
          Real.rpow_le_rpow (by positivity) h1 hp.le
      _ = _ := by
          rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]; ring_nf
  have h3 : s ^ p * (1 + r) ^ p ≤ (1 + t) ^ p := by
    rw [← Real.mul_rpow hs0.le (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith) hp.le
  have hr1 : 0 < (1 + r) ^ p := Real.rpow_pos_of_pos (by linarith) _
  have h4 : s ^ p ≤ (1 + t) ^ p * (1 + r) ^ (-p) := by
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hr1]; exact h3
  have h5 : Real.exp (-(c * s * r)) * Real.exp (p * ε * t) ≤ Real.exp (-(c / 2 * s * r)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have : p * ε * t ≤ c / 2 * t := by gcongr
    rw [ht] at this; nlinarith
  rw [hνs]
  calc s ^ p * Real.exp (-(c * s * r)) ≤ ((1 + t) ^ p * (1 + r) ^ (-p)) * Real.exp (-(c * s * r)) :=
        by gcongr
    _ ≤ (((ε⁻¹) ^ p * Real.exp (p * ε * t)) * (1 + r) ^ (-p)) * Real.exp (-(c * s * r)) := by
        gcongr
    _ = (ε⁻¹) ^ p * (1 + r) ^ (-p) * (Real.exp (-(c * s * r)) * Real.exp (p * ε * t)) := by ring
    _ ≤ (ε⁻¹) ^ p * (1 + r) ^ (-p) * Real.exp (-(c / 2 * s * r)) := by gcongr

end Balaban.Correlations
