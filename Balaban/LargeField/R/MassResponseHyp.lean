/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.MassResponse
public import Balaban.Inhabited.LocalizationSettings
public import Balaban.Inhabited.XiCDomains
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Discharging the hypotheses of the same-datum mass response (MASS-RESPONSE.md §1)

* `prop51Hyp_massSource` : `Prop51Hyp` for the mass source from `GreenSetting`, `BgBounds`,
  the bound `|φ⁰| ≤ 3/2` on `Ω₁`, and the size premises;
* `prop51Hyp_massSource_unit` : the same for a real unit field `φ⁰`;
* `massChange_sameData_response` : the response bound under the premises (1.3) only, with the
  constants `K_w, δ_w` depending only on `(d, L, N)`;
* `massChange_sameData_response_unit` : the real hard-spin form (`Bh = 2`).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization Finset Matrix

section T1

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- On `Ω₁`, the extension `barField` is the field itself. -/
theorem barField_apply_mem (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) (i : Fin N) :
    barField G D.Ψ φ x i = φ (x, i) := by
  simp [barField, x.2]

/-- **`Prop51Hyp` for the mass source** (note (1.3)): at mass `0`, `δΨ = 0`,
`f₁ = massSource`. -/
theorem prop51Hyp_massSource (a : ℕ → ℝ) (μ m Bh δ₀ δ₁ : ℝ) (D : BgData G N)
    {φ0 φm : G.Ω 1 × Fin N → ℂ} {α0 : G.Ω 1 → ℂ}
    (hG : GreenSetting G a 0) (h0 : IsEL G a 0 D φ0 α0) (hb : BgBounds G D φ0 α0 δ₀)
    (hφ : ∀ x : G.Ω 1, vn (fun i => φ0 (x, i)) ≤ 3 / 2)
    (hμ : 0 ≤ μ) (hμℓ : ∀ x : G.Ω 1, μ * G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 ≤ m)
    (hB : ∀ (x : G.Ω 1) (i : Fin N), ‖φm (x, i) - D.h x i‖ ≤ Bh)
    (hδ₀ : 0 ≤ δ₀) (hδ₁ : 0 ≤ δ₁) (hδ₀s : δ₀ ≤ deltaStar d L N) (hδ₁s : δ₁ ≤ deltaStar d L N)
    (hmB : m * Bh ≤ δ₁) :
    Prop51Hyp G a 0 α0 (barField G D.Ψ φ0) (0 : Torus d (N₀ * L ^ K) → Fin N → ℂ)
      (massSource μ D φm) δ₀ δ₁ := by
  have hg : ∀ x : G.Ω 1, gdef G (barField G D.Ψ φ0) x = 0 := by
    intro x
    have := h0.2 x
    simp only [gdef, barField, x.2, dite_true]
    rw [this]; ring
  have hz : zeroExt (G.Ω 1) (gdef G (barField G D.Ψ φ0)) = 0 := by
    funext y
    have : gdef G (barField G D.Ψ φ0) = 0 := funext hg
    simp [zeroExt, this]
  refine ⟨hG, hδ₀, hδ₁, hδ₀s, hδ₁s, ⟨fun x hx μ' => hb.grad ⟨x, hx⟩ μ',
    fun x hx => hb.lap ⟨x, hx⟩⟩, fun x hx => ?_, fun x => hb.alpha x, fun x i => ?_,
    fun x _ => by simpa [vn_zero] using hδ₁, fun x => ?_, fun x => ?_⟩
  · have e : barField G D.Ψ φ0 x = fun i => φ0 (⟨x, hx⟩, i) := by
      funext i; exact barField_apply_mem D φ0 ⟨x, hx⟩ i
    rw [e]; exact hφ ⟨x, hx⟩
  · exact (massSource_bound D φm hμ hμℓ hB x i).trans hmB
  · rw [hg x, norm_zero]; exact hδ₁
  · rw [hz]; simp [negLap]; exact hδ₁

/-- A real unit field `φ⁰` (`∑ ‖φ⁰(x,i)‖² = 1`) satisfies `|φ⁰| ≤ 3/2`. -/
theorem vn_le_of_unit {φ0 : G.Ω 1 × Fin N → ℂ} (hφ : ∀ x : G.Ω 1, ∑ i, ‖φ0 (x, i)‖ ^ 2 = 1)
    (x : G.Ω 1) : vn (fun i => φ0 (x, i)) ≤ 3 / 2 := by
  have h := vn_sq (fun i => φ0 (x, i))
  rw [hφ x] at h
  nlinarith [vn_nonneg (fun i => φ0 (x, i))]

/-- **`Prop51Hyp` for the mass source, real unit field `φ⁰`.** -/
theorem prop51Hyp_massSource_unit (a : ℕ → ℝ) (μ m Bh δ₀ δ₁ : ℝ) (D : BgData G N)
    {φ0 φm : G.Ω 1 × Fin N → ℂ} {α0 : G.Ω 1 → ℂ}
    (hG : GreenSetting G a 0) (h0 : IsEL G a 0 D φ0 α0) (hb : BgBounds G D φ0 α0 δ₀)
    (hφ : ∀ x : G.Ω 1, ∑ i, ‖φ0 (x, i)‖ ^ 2 = 1)
    (hμ : 0 ≤ μ) (hμℓ : ∀ x : G.Ω 1, μ * G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 ≤ m)
    (hB : ∀ (x : G.Ω 1) (i : Fin N), ‖φm (x, i) - D.h x i‖ ≤ Bh)
    (hδ₀ : 0 ≤ δ₀) (hδ₁ : 0 ≤ δ₁) (hδ₀s : δ₀ ≤ deltaStar d L N) (hδ₁s : δ₁ ≤ deltaStar d L N)
    (hmB : m * Bh ≤ δ₁) :
    Prop51Hyp G a 0 α0 (barField G D.Ψ φ0) (0 : Torus d (N₀ * L ^ K) → Fin N → ℂ)
      (massSource μ D φm) δ₀ δ₁ :=
  prop51Hyp_massSource a μ m Bh δ₀ δ₁ D hG h0 hb (vn_le_of_unit hφ) hμ hμℓ hB hδ₀ hδ₁ hδ₀s hδ₁s hmB

end T1

section T2

variable {d L N : ℕ} [NeZero L]

/-- **Same-datum mass response, premises (1.3) only** (MASS-RESPONSE.md §1).  There are
`K_w, δ_w > 0` depending only on `(d, L, N)` such that for every generating set, datum and pair
of Euler-Lagrange backgrounds at masses `0` and `μ` with the stated bounds, the multiplier
difference and the field difference are bounded with weight one by `K_w · (m · Bh)`, and the
consumer's `hresp` holds with `K_m = √N · K_w`.  `Dec2.OpSetting G a 0` is the geometric
separation condition of the generating set. -/
theorem massChange_sameData_response (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        (a : ℕ → ℝ) (μ m Bh δ₀ : ℝ) (D : BgData G N)
        {φ0 φm : G.Ω 1 × Fin N → ℂ} {α0 αm : G.Ω 1 → ℂ},
        IsEL G a 0 D φ0 α0 → IsEL G a μ D φm αm →
        BgBounds G D φ0 α0 δ₀ → BgBounds G D φm αm δ₀ →
        GreenSetting G a 0 → Dec2.OpSetting G a 0 →
        0 ≤ δ₀ → δ₀ ≤ min (deltaStar d L N) δw → 2 * δ₀ ≤ c6 d L N →
        0 ≤ m → 0 ≤ Bh → m * Bh ≤ min (deltaStar d L N) δw →
        0 ≤ μ → (∀ x : G.Ω 1, μ * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ m) →
        (∀ (x : G.Ω 1) (i : Fin N), ‖φm (x, i) - D.h x i‖ ≤ Bh) →
        (∀ x : G.Ω 1, vn (fun i => φ0 (x, i)) ≤ 3 / 2) →
        (SmallW G (fun _ => 1) (αm - α0) (Kw * (m * Bh)) ∧
          SupBoundsW G (fun _ => 1) (φm - φ0) (Kw * (m * Bh))) ∧
        ∀ x, vnorm (wExt D D φm φ0 x) ≤ (Real.sqrt N * Kw) * Bh * m := by
  obtain ⟨Kw, δw, hK, hδ, hW⟩ := weightedProp51S_exists N hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a μ m Bh δ₀ D φ0 φm α0 αm h0 hm b0 bm hG hO hδ₀ hδs h2 hm0 hBh0 hmB hμ hμℓ hB hφ
  have hd0 : 0 < d := by omega
  have hP := prop51Hyp_massSource a μ m Bh δ₀ (m * Bh) D hG h0 b0 hφ hμ hμℓ hB hδ₀
    (mul_nonneg hm0 hBh0) (hδs.trans (min_le_left _ _)) (hmB.trans (min_le_left _ _)) le_rfl
  have hα : Small G (αm - α0) (c6 d L N) := fun x => by
    have := massMultiplier_small b0 bm x
    linarith
  refine ⟨massChange_sameData_response_of_weighted hd0 hW a μ m Bh δ₀ (m * Bh) D h0 hm hP hO
    (hδs.trans (min_le_right _ _)) (hmB.trans (min_le_right _ _)) hm0 hBh0 hμ hμℓ hB hα,
    massChange_sameData_hresp_of_weighted hd0 hW a μ m Bh δ₀ (m * Bh) D h0 hm hP hO
    (hδs.trans (min_le_right _ _)) (hmB.trans (min_le_right _ _)) hm0 hBh0 hμ hμℓ hB hα hK.le⟩

/-- **Real hard-spin form** (`Bh = 2`): unit `φ⁰`, `φᵐ`, `h`. -/
theorem massChange_sameData_response_unit (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        (a : ℕ → ℝ) (μ m δ₀ : ℝ) (D : BgData G N)
        {φ0 φm : G.Ω 1 × Fin N → ℂ} {α0 αm : G.Ω 1 → ℂ},
        IsEL G a 0 D φ0 α0 → IsEL G a μ D φm αm →
        BgBounds G D φ0 α0 δ₀ → BgBounds G D φm αm δ₀ →
        GreenSetting G a 0 → Dec2.OpSetting G a 0 →
        0 ≤ δ₀ → δ₀ ≤ min (deltaStar d L N) δw → 2 * δ₀ ≤ c6 d L N →
        0 ≤ m → m * 2 ≤ min (deltaStar d L N) δw →
        0 ≤ μ → (∀ x : G.Ω 1, μ * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ m) →
        (∀ x : G.Ω 1, ∑ i, ‖φ0 (x, i)‖ ^ 2 = 1) → (∀ x : G.Ω 1, ∑ i, ‖φm (x, i)‖ ^ 2 = 1) →
        (∀ x : G.Ω 1, ∑ i, ‖D.h x i‖ ^ 2 = 1) →
        (SmallW G (fun _ => 1) (αm - α0) (Kw * (m * 2)) ∧
          SupBoundsW G (fun _ => 1) (φm - φ0) (Kw * (m * 2))) ∧
        ∀ x, vnorm (wExt D D φm φ0 x) ≤ (Real.sqrt N * Kw) * 2 * m := by
  obtain ⟨Kw, δw, hK, hδ, H⟩ := massChange_sameData_response N hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a μ m δ₀ D φ0 φm α0 αm h0 hm b0 bm hG hO hδ₀ hδs h2 hm0 hmB hμ hμℓ u0 um uh
  exact H a μ m 2 δ₀ D h0 hm b0 bm hG hO hδ₀ hδs h2 hm0 (by norm_num) hmB hμ hμℓ
    (norm_sub_le_two_of_unit D um uh) (vn_le_of_unit u0)

end T2

section T4

open Balaban.Inhabited Balaban.Localization.I5Inhabited Balaban.SmallField

/-- **Non-vacuity of the premises of `massChange_sameData_response`** (case `μ = 0`,
`φᵐ = φ⁰`, `αᵐ = α⁰`): at `d = L = 3`, `N = 2`, `ν = 0`, `a = compWeight 3 1`, on the
whole-lattice level-two generating set with `Dec2.OpSetting`, for every `δw > 0` there are a
datum `D`, the Theorem 5.2 background `(φ⁰, α⁰)` of `D`, `m = 0` and sizes `δ₀` such that every
premise of the response theorem holds. -/
theorem massChange_sameData_hyps_nonempty {δw : ℝ} (hδw : 0 < δw) :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (G : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 ϱ) (a : ℕ → ℝ)
      (μ m Bh δ₀ : ℝ) (D : BgData G 2) (φ0 φm : G.Ω 1 × Fin 2 → ℂ) (α0 αm : G.Ω 1 → ℂ),
      IsEL G a 0 D φ0 α0 ∧ IsEL G a μ D φm αm ∧
      BgBounds G D φ0 α0 δ₀ ∧ BgBounds G D φm αm δ₀ ∧
      GreenSetting G a 0 ∧ Dec2.OpSetting G a 0 ∧
      0 ≤ δ₀ ∧ δ₀ ≤ min (deltaStar 3 3 2) δw ∧ 2 * δ₀ ≤ c6 3 3 2 ∧
      0 ≤ m ∧ 0 ≤ Bh ∧ m * Bh ≤ min (deltaStar 3 3 2) δw ∧
      0 ≤ μ ∧ (∀ x : G.Ω 1, μ * G.spacing (x : CTorus 3 3 6 m₁ 2) ^ 2 ≤ m) ∧
      (∀ (x : G.Ω 1) (i : Fin 2), ‖φm (x, i) - D.h x i‖ ≤ Bh) ∧
      (∀ x : G.Ω 1, vn (fun i => φ0 (x, i)) ≤ 3 / 2) := by
  obtain ⟨m₁, h4, -⟩ := exists_m₁_cstar
  have hN : 0 < 2 := by norm_num
  have hd0 : 0 < 3 := by norm_num
  have S := dgSetting_rho h4
  have hH := bgHyp_rho m₁
  set G : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 (rhoSep m₁) := GP (m₁ := m₁) (ϱ := rhoSep m₁) with hG
  have hOp : Dec2.OpSetting G (compWeight 3 1) 0 := ⟨⟨S.hd, S.hL, S.mass, S.weights, S.sep⟩, S.massLe⟩
  have hK := bgK1_pos 3 3 2
  have hds := deltaStar_pos 3 3 2 hd0
  have hc6 := c6_pos 3 3 2 hd0
  set M : ℝ := min (min (deltaStar 3 3 2) δw) (min (c6 3 3 2 / 2) (1 / 2)) with hM
  have hM0 : 0 < M := lt_min (lt_min hds hδw) (lt_min (half_pos hc6) (by norm_num))
  set δ : ℝ := min (min (bgC0 3 3 2) (bgC1 3 3 2)) (M / (bgK1 3 3 2 + 1)) with hδ
  have hδ0 : 0 < δ :=
    lt_min (lt_min (bgC0_pos 3 3 2 hd0) (bgC1_pos' hd0)) (by positivity)
  have hδc0 : δ ≤ bgC0 3 3 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδc1 : δ ≤ bgC1 3 3 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδM : bgK1 3 3 2 * δ ≤ M := by
    have h1 : δ ≤ M / (bgK1 3 3 2 + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  set D : BgData G 2 := complexData G (fun _ => unitVec hN) (unitVec hN) 0 0
    (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl) with hD
  have hR := complexData_realizes (G := G) (Ψ₀ := fun _ => unitVec hN) (h₀ := unitVec hN)
    (Ψ'' := 0) (h'' := 0) (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ _ => rfl)
  have hDom : InDomainC G 0 δ δ D :=
    ⟨fun _ => unitVec hN, unitVec hN, 0, 0, exists_inPsiTildeC G hN 0 hδ0 hδ0, hR.1, hR.2⟩
  obtain ⟨φ, α, hsol, hbb, -⟩ := theorem52_exists (a := compWeight 3 1) (ν := 0) hH hδ0 le_rfl
    hδc0 hδc1 (by rw [zero_mul, zero_mul]; positivity) hDom
  have hMle : M ≤ min (deltaStar 3 3 2) δw := min_le_left _ _
  have hM2 : M ≤ c6 3 3 2 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hM3 : M ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hδ₀0 : 0 ≤ bgK1 3 3 2 * δ := by positivity
  -- the bound on `|φ⁰|`
  have hvn : ∀ x : G.Ω 1, vn (fun i => φ (x, i)) ≤ 3 / 2 := by
    intro x
    have hxd : (x : CTorus 3 3 6 m₁ 2) ∈ dataSites G := (mem_dataSites G).2 (Or.inl x.2)
    have h1 := hbb.val x
    have e : (fun i => φ (x, i)) = (fun i => φ (x, i) - D.Ψ x i) + D.Ψ x := by
      funext i; simp
    have hΨ : vn (D.Ψ x) = 1 := by
      have : D.Ψ x = fun i => ((unitVec hN i : ℝ) : ℂ) := by
        funext i; have := hR.1 x hxd i; simp only [Pi.zero_apply, add_zero] at this; exact this
      rw [this, vn_ofReal, rn_unitVec]
    rw [e]
    have := vn_add (fun i => φ (x, i) - D.Ψ x i) (D.Ψ x)
    linarith
  refine ⟨m₁, rhoSep m₁, G, compWeight 3 1, 0, 0, ∑ x : G.Ω 1, ∑ i : Fin 2, ‖φ (x, i) - D.h x i‖,
    bgK1 3 3 2 * δ, D, φ, φ, α, α, hsol.1, ?_, hbb, hbb, hH.green, hOp, hδ₀0, ?_, ?_, le_rfl,
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _, ?_, le_rfl, ?_, ?_,
    hvn⟩
  · exact hsol.1
  · exact hδM.trans hMle
  · have := hδM.trans hM2; linarith
  · simp only [zero_mul]; exact le_min hds.le hδw.le
  · intro x; simp only [zero_mul]; exact le_rfl
  · intro x i
    exact (Finset.single_le_sum (f := fun i => ‖φ (x, i) - D.h x i‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ i)).trans (Finset.single_le_sum
      (f := fun x => ∑ i : Fin 2, ‖φ (x, i) - D.h x i‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ x))

end T4

end Balaban.LargeField.ActionConv
