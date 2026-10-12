/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledGs

/-!
# (DG1)--(DG3): the decoupled Green's operator is defined and bounded

* `dg2_sup`: for `M₁ ≥ c_* e^{N₀ κ₁}`, every `s` with `|s_P| ≤ e^{κ₁}`, every `A` with
  `|A|₂ ≤ γ₁` and every weight `w` of rate `γ_w`: `1 - 𝒦_s(A)` is invertible and
  `G_s(A) f` satisfies the four pointwise bounds (value, gradient, Laplacian) with the weight `w`
  and the constant `B_G e^{N₀ κ₁} |f|_{2,w}`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L : ℕ} [NeZero L]

theorem Kcal_weighted_of_dg1 {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {α : G.Ω 1 → ℂ}
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {w : CTorus d L N₁ m₁ K → ℝ}
    (hK : ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      ∀ x : G.Ω 1, w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
        ‖(Kcal G a ν α s *ᵥ f) x‖ ≤ C / 4) :
    ∀ (h : G.Ω 1 → ℂ) (C : ℝ), 0 ≤ C →
      WBd (fun x : G.Ω 1 => w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) h C →
      WBd (fun x : G.Ω 1 => w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2)
        (Kcal G a ν α s *ᵥ h) (C / 4) :=
  fun h C hC hh => hK h hC hh

/-- **(DG1)--(DG3), pointwise form.** -/
theorem dg2_sup (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ cstar BG : ℝ, 0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, DGSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {w : CTorus d L N₁ m₁ K → ℝ}, IsWeight G (gammaW d) w →
      ∀ (f : G.Ω 1 → ℂ) {C : ℝ}, 0 ≤ C →
      (∀ x : G.Ω 1, w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ C) →
      IsUnit (1 - Kcal G a ν α s) ∧
      SupBdW G w (zeroExt (G.Ω 1) (Gs G a ν α s *ᵥ f)) (BG * Real.exp (N0 d L * κ) * C) := by
  obtain ⟨cstar, hcs, hD1⟩ := dg1 (d := d) (L := L) hd hL
  obtain ⟨Bw, hBw, hS⟩ := cube_star (d := d) (L := L) hd hL
  have hFc := Fc_bounds d L
  have hF0 : 0 ≤ Fc d L := by linarith [hFc.1]
  refine ⟨cstar, 3 * 5 ^ d * (4 / 3) * Bw * Real.exp (2 * gammaW d * d) * Fc d L, hcs, by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα κ hκ hMκ s hs w hw f C hC hfC
  have hd0 : 0 < d := by omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hγ0 := gammaW_nonneg hd0
  have hρ := S.one_lt_rho
  have hspos : ∀ x : G.Ω 1, 0 < (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 := fun x => by
    have := spacing_pos G (x := (x : CTorus d L N₁ m₁ K)); positivity
  -- invertibility
  have hw1 : IsWeight G (gammaW d) (fun _ => (1 : ℝ)) := IsWeight.one G hγ0
  have hK1 : ∀ (h : G.Ω 1 → ℂ) (C : ℝ), 0 ≤ C →
      WBd (fun x : G.Ω 1 => (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) h C →
      WBd (fun x : G.Ω 1 => (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) (Kcal G a ν α s *ᵥ h) (C / 4) := by
    intro h C0 hC0 hh x
    have := hD1 G S hα hκ hMκ hs hw1 h hC0 (fun y => by simpa using hh y) x
    simpa using this
  have hU : IsUnit (1 - Kcal G a ν α s) := neumann_isUnit hspos hK1
  refine ⟨hU, ?_⟩
  -- the solution of `(1 - 𝒦) g = f`
  set g : G.Ω 1 → ℂ := (1 - Kcal G a ν α s)⁻¹ *ᵥ f with hgdef
  have hg : g - Kcal G a ν α s *ᵥ g = f := by
    have h1 : (1 - Kcal G a ν α s) *ᵥ g = f := by
      rw [hgdef, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU), Matrix.one_mulVec]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    exact h1
  have hωpos : ∀ x : G.Ω 1, 0 < w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 := fun x =>
    mul_pos (hw.pos x) (hspos x)
  have hKw := Kcal_weighted_of_dg1 (a := a) (ν := ν) (α := α) (s := s)
    (fun f' C' hC' hf' => hD1 G S hα hκ hMκ hs hw f' hC' hf')
  have hgW : WBd (fun x : G.Ω 1 => w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) g (4 * C / 3) :=
    neumann_bound hωpos hKw hg hC (fun x => hfC x)
  have hgC : ∀ z : G.Ω 1, w z * (G.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖g z‖ ≤ 4 * C / 3 :=
    fun z => hgW z
  have hGsf : Gs G a ν α s *ᵥ f = Gstar G a ν α s *ᵥ g := by
    rw [hgdef, Gs, ← Matrix.mulVec_mulVec]
  rw [hGsf]
  set v : CTorus d L N₁ m₁ K → ℂ := zeroExt (G.Ω 1) (Gstar G a ν α s *ᵥ g) with hvdef
  -- the pointwise analysis
  have hpt : ∀ x : G.Ω 1,
      (∃ A : Finset (ℕ × CTorus d L N₁ m₁ K),
        (A.card : ℝ) ≤ 3 * 5 ^ d ∧ (∀ q ∈ A, q ∈ cubeIdx G) ∧
        (∀ y : CTorus d L N₁ m₁ K, (y = (x : CTorus d L N₁ m₁ K) ∨ ∃ μ : Fin d,
          y = (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∨ y = (x : CTorus d L N₁ m₁ K) - Pi.single μ 1) →
          v y = ∑ q ∈ A, sProd G s q * (((chi G q y : ℝ) : ℂ) * cubeSolE G a ν α q g y)) ∧
        ∀ q ∈ A, ‖((chi G q x : ℝ) : ℂ) * cubeSolE G a ν α q g x‖ * w x ≤
            Bw * (4 * C / 3) * Real.exp (2 * gammaW d * d) ∧
          (∀ μ : Fin d, G.spacing (x : CTorus d L N₁ m₁ K) *
            ‖((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
              ((chi G q x : ℝ) : ℂ) * cubeSolE G a ν α q g x‖ * w x ≤
            (1 + Cchi d L) * (Bw * (4 * C / 3) * Real.exp (2 * gammaW d * d))) ∧
          (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖∑ μ : Fin d, (2 * (((chi G q x : ℝ) : ℂ) *
              cubeSolE G a ν α q g x) -
            ((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
            ((chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1))‖ * w x ≤
            (1 + Cchi d L + d * Cchi d L * (1 + L)) *
              (Bw * (4 * C / 3) * Real.exp (2 * gammaW d * d))) := by
    intro x
    obtain ⟨A, hA1, hAc, hrepr⟩ := Gstar_repr S α s g x
    refine ⟨A, by exact_mod_cast hAc, fun q hq => (hA1 q hq).1, fun y hy => hrepr y hy,
      fun q hq => ?_⟩
    obtain ⟨hqi, hIq⟩ := hA1 q hq
    obtain ⟨hsupp, hgq⟩ := cD_source q g (by positivity : (0 : ℝ) ≤ 4 * C / 3) hgC
    have hst := hS G S hα hqi hw (cD G q *ᵥ g) hsupp (by positivity : (0 : ℝ) ≤ 4 * C / 3) hgq hIq
    have hwx := hw.pos x
    have hux : ∀ y, y ∉ G.Ω 1 → cubeSolE G a ν α q g y = 0 := fun y hy => cubeSolE_of_not_mem q g hy
    have hV0 : 0 ≤ Bw * (4 * C / 3) * Real.exp (2 * gammaW d * d) / w x := by positivity
    have hper := perq_bounds S hqi hux hV0 hst
    have hVw : Bw * (4 * C / 3) * Real.exp (2 * gammaW d * d) / w x * w x =
        Bw * (4 * C / 3) * Real.exp (2 * gammaW d * d) := by field_simp
    refine ⟨?_, fun μ => ?_, ?_⟩
    · calc _ ≤ Bw * (4 * C / 3) * Real.exp (2 * gammaW d * d) / w x * w x :=
            mul_le_mul_of_nonneg_right hper.1 hwx.le
        _ = _ := hVw
    · calc _ ≤ (1 + Cchi d L) * (Bw * (4 * C / 3) * Real.exp (2 * gammaW d * d) / w x) * w x :=
            mul_le_mul_of_nonneg_right (hper.2.1 μ) hwx.le
        _ = _ := by rw [mul_assoc, hVw]
    · calc _ ≤ (1 + Cchi d L + d * Cchi d L * (1 + L)) *
            (Bw * (4 * C / 3) * Real.exp (2 * gammaW d * d) / w x) * w x :=
            mul_le_mul_of_nonneg_right hper.2.2 hwx.le
        _ = _ := by rw [mul_assoc, hVw]
  -- assembling the four bounds
  set Wc : ℝ := Bw * (4 * C / 3) * Real.exp (2 * gammaW d * d) with hWc
  have hWc0 : 0 ≤ Wc := by positivity
  have hE0 : 0 < Real.exp (N0 d L * κ) := Real.exp_pos _
  have htarget : 3 * 5 ^ d * (4 / 3) * Bw * Real.exp (2 * gammaW d * d) * Fc d L *
      Real.exp (N0 d L * κ) * C = (3 * 5 ^ d) * (Real.exp (N0 d L * κ) * (Fc d L * Wc)) := by
    rw [hWc]; ring
  have hmono : ∀ c : ℝ, c ≤ Fc d L →
      (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) * (c * Wc)) ≤
        3 * 5 ^ d * (4 / 3) * Bw * Real.exp (2 * gammaW d * d) * Fc d L *
          Real.exp (N0 d L * κ) * C := by
    intro c hc
    rw [htarget]
    gcongr
  have hcoef : ∀ q ∈ cubeIdx G, ‖sProd G s q‖ ≤ Real.exp (N0 d L * κ) := fun q hq =>
    norm_sProd_le S.aligned S.cover_sep S.hM (by omega : 1 ≤ L) hq hκ hs
  refine ⟨fun x hx => ?_, fun x hx μ => ?_, fun x hx μ hxe => ?_, fun x hx => ?_⟩
  · obtain ⟨A, hcard, hAq, hrepr, hq⟩ := hpt ⟨x, hx⟩
    rw [hrepr x (Or.inl rfl)]
    refine (sum_scaled_bound A hcard (hw.pos x).le hE0.le hWc0 (fun q => sProd G s q)
      (fun q => ((chi G q x : ℝ) : ℂ) * cubeSolE G a ν α q g x)
      (fun q hqA => hcoef q (hAq q hqA)) (fun q hqA => ?_)).trans (hmono 1 (Fc_bounds d L).1 |>.trans_eq' ?_)
    · have := (hq q hqA).1
      simpa [mul_comm] using this
    · ring
  · obtain ⟨A, hcard, hAq, hrepr, hq⟩ := hpt ⟨x, hx⟩
    have e : v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x = ∑ q ∈ A, sProd G s q *
        (((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
          cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
        ((chi G q x : ℝ) : ℂ) * cubeSolE G a ν α q g x) := by
      rw [hrepr _ (Or.inr ⟨μ, Or.inl rfl⟩), hrepr x (Or.inl rfl), ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [e, ← mul_assoc]
    refine (sum_scaled_bound A hcard (mul_nonneg (hw.pos x).le (spacing_pos G).le) hE0.le
      (mul_nonneg (by linarith [Cchi_nonneg d L]) hWc0) (fun q => sProd G s q)
      (fun q => ((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
          cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
        ((chi G q x : ℝ) : ℂ) * cubeSolE G a ν α q g x)
      (fun q hqA => hcoef q (hAq q hqA)) (fun q hqA => ?_)).trans (hmono (1 + Cchi d L) (Fc_bounds d L).2.1)
    have := (hq q hqA).2.1 μ
    nlinarith [this]
  · obtain ⟨A, hcard, hAq, hrepr, hq⟩ := hpt ⟨x, hx⟩
    have e : v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x = ∑ q ∈ A, sProd G s q *
        (((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
          cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
        ((chi G q x : ℝ) : ℂ) * cubeSolE G a ν α q g x) := by
      rw [hrepr _ (Or.inr ⟨μ, Or.inl rfl⟩), hrepr x (Or.inl rfl), ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun q _ => by ring
    have hadj : Adj (x : CTorus d L N₁ m₁ K) ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) :=
      ⟨μ, Or.inl rfl⟩
    have hsp := spacing_adj_le G hρ.le hx hxe hadj
    have hmain : w x * (G.spacing (x : CTorus d L N₁ m₁ K) *
        ‖v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x‖) ≤
        (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) * ((1 + Cchi d L) * Wc)) := by
      rw [e, ← mul_assoc]
      refine (sum_scaled_bound A hcard (mul_nonneg (hw.pos x).le (spacing_pos G).le) hE0.le
        (mul_nonneg (by linarith [Cchi_nonneg d L]) hWc0) (fun q => sProd G s q)
        (fun q => ((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
            cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
          ((chi G q x : ℝ) : ℂ) * cubeSolE G a ν α q g x)
        (fun q hqA => hcoef q (hAq q hqA)) (fun q hqA => ?_))
      have := (hq q hqA).2.1 μ
      nlinarith [this]
    have hnn := norm_nonneg (v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x)
    have hw0 := (hw.pos x).le
    calc w x * (G.spacing ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) *
          ‖v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x‖)
        ≤ w x * ((L * G.spacing (x : CTorus d L N₁ m₁ K)) *
          ‖v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x‖) := by gcongr
      _ = L * (w x * (G.spacing (x : CTorus d L N₁ m₁ K) *
          ‖v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x‖)) := by ring
      _ ≤ L * ((3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) * ((1 + Cchi d L) * Wc))) := by gcongr
      _ = (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) * ((L * (1 + Cchi d L)) * Wc)) := by ring
      _ ≤ _ := hmono _ (Fc_bounds d L).2.2.2
  · obtain ⟨A, hcard, hAq, hrepr, hq⟩ := hpt ⟨x, hx⟩
    have e : ∑ μ : Fin d, (2 * v x - v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
        v ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1)) = ∑ q ∈ A, sProd G s q *
        ∑ μ : Fin d, (2 * (((chi G q x : ℝ) : ℂ) * cubeSolE G a ν α q g x) -
          ((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
            cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
          ((chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ) *
            cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1)) := by
      calc _ = ∑ μ : Fin d, ∑ q ∈ A, sProd G s q *
            (2 * (((chi G q x : ℝ) : ℂ) * cubeSolE G a ν α q g x) -
            ((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
            ((chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1)) := by
            refine Finset.sum_congr rfl fun μ _ => ?_
            rw [hrepr x (Or.inl rfl), hrepr _ (Or.inr ⟨μ, Or.inl rfl⟩),
              hrepr _ (Or.inr ⟨μ, Or.inr rfl⟩), Finset.mul_sum, ← Finset.sum_sub_distrib,
              ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun q _ => by ring
        _ = ∑ q ∈ A, ∑ μ : Fin d, sProd G s q *
            (2 * (((chi G q x : ℝ) : ℂ) * cubeSolE G a ν α q g x) -
            ((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
            ((chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1)) :=
            Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun q _ => (Finset.mul_sum _ _ _).symm
    rw [e, ← mul_assoc]
    have hCc := Cchi_nonneg d L
    have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have hFl : 0 ≤ 1 + Cchi d L + d * Cchi d L * (1 + L) := by positivity
    refine (sum_scaled_bound A hcard (mul_nonneg (hw.pos x).le (by positivity)) hE0.le
      (mul_nonneg hFl hWc0) (fun q => sProd G s q)
      (fun q => ∑ μ : Fin d, (2 * (((chi G q x : ℝ) : ℂ) * cubeSolE G a ν α q g x) -
          ((chi G q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
            cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
          ((chi G q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ) *
            cubeSolE G a ν α q g ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1)))
      (fun q hqA => hcoef q (hAq q hqA)) (fun q hqA => ?_)).trans
      (hmono (1 + Cchi d L + d * Cchi d L * (1 + L)) (Fc_bounds d L).2.2.1)
    have := (hq q hqA).2.2
    nlinarith [this]

end Balaban.Localization
