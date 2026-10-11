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
    |rtrLim ν x y| ≤ cS * (1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) *
      Real.exp (-(cP * Real.sqrt ν * ‖x - y‖)) ∧
    |rlgLim ν x y| ≤ cS * (1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) *
      Real.exp (-(cP * Real.sqrt ν * ‖x - y‖)) := by
  have hq : 2 ≤ M * L := by nlinarith
  obtain ⟨n₁, hn₁⟩ := exists_good_tori hM hL (J ν) (x - y)
  constructor
  · have := LimAlong.abs_sub_le hq (c := 0)
      (B := cS * (1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) *
        Real.exp (-(cP * Real.sqrt ν * ‖x - y‖))) (h3.2.1 ν hν x y).1
      ⟨n₁, fun ℓ _ hd => by
        obtain ⟨hadm, hsz⟩ := hn₁ ℓ hd
        simpa using (h3.1 ν hν x y ℓ hadm hsz).2.2.1⟩
    simpa using this
  · have := LimAlong.abs_sub_le hq (c := 0)
      (B := cS * (1 + ‖x - y‖) ^ (-((d : ℝ) - 2 + ρ₀)) *
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
  refine LimAlong.abs_sub_le hq hm ⟨J ν + 1, fun ℓ _ hd => ?_⟩
  have hadm : M * L ^ (J ν + 1) ∣ ℓ := admissible_of_dvd_pow le_rfl hd
  obtain ⟨he, hb⟩ := h2.2.2 ν hν x ℓ hadm
  rw [he]
  simpa using hb

end Balaban.Correlations
