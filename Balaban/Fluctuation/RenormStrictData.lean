/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormBgClassDec
public import Balaban.Localization.DecoupledSolveAnalytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The data of the shifted perturbation problem for the renormalization cut family

Toward the second and third fields `locC2`, `locDφ` of `RenormExpInput`.  **`locC2` and `locDφ`
are NOT proved here**, and neither is the analyticity or the sharp `O(r)` bound of the shifted
solution.  This file proves the data-side inputs of Theorem I-4a, in mode P (`ιU = false`), for the
cut family; it uses no zero class and is independent of the choice of the generator.

For a raw datum `D = (Ψ, h)` of `XiCOneReal`, a complex cut `s` with `‖s_P‖ ≤ e^κ`, the decoupled
background `(φ_s, α_s)` and a parameter `ξ` with `‖ξ‖ < r₀ ≤ 1/16`, the data are

`renEdat = (φ̄_s, α_s + Δν, ε ξ₀ Ψ, Δν (h - φ_s))`,   `Δν = ν_u - ν`,

in the order `(φ₀, α₀, δΨ, f₁)` of `Edat`.  With `δ = xiC1 d · ε`, `K₄ = K4 d L N BG κ`,
`K₁ = bgK1 d L N`, `m_* = 3 + (K₄ + K₁) xiC1 d`, `b_* = 3/2 + (32/15) m_*`, the file proves

* `renMass_field_le_of_flCore`: `ν ℓ² ‖h - φ_s‖ ≤ m_* ε` on `Ω₁`, for every complex cut;
* `renEdat_decHyp_of_flCore`: `DecHyp` in mode P at `(D₀, b_* ε ‖ξ‖)`, `D₀ = 2 K₄ δ + 3 r₀`,
  under the explicit margin `D₀ ≤ 1`;
* `renEdat_strictDataM_of_flCore`: `StrictDataM … false D₀ (b_* ε r₀)` (no further margin);
* `renMargins_arith`, `renMargins_exists_r₀_of_flCore`: the margins are jointly satisfiable.

The margins `D₀, D₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)` that
`Dec.i4a_analytic` needs are not consequences of `FlCore` (its `B_le` is stated with `BG₂`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.FinalCutoff
  Balaban.Localization Finset Matrix

section Generic

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν ε : ℝ}

/-- **The data of the shifted perturbation problem** (mode P of Theorem I-4a) for the cut family:
the background field extended by the datum, the multiplier shifted by `Δν = ν_u - ν`, the
perturbation `δΨ = ε ξ₀ Ψ`, and `f₁ = Δν (h - φ)`. -/
noncomputable def renEdat (ν ε : ℝ) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ)
    (ξ : Fin 3 → ℂ) : Edat G N :=
  (barField G D.Ψ φ, α + fun _ => renMassU ν ξ - ν, fun x i => renZeta ε ξ * D.Ψ x i,
    renF1 ν ξ D.h φ)

theorem renEdat_alpha_le {α : G.Ω 1 → ℂ} {B r : ℝ} (hν0 : 0 ≤ ν)
    (hνℓ : ∀ x : G.Ω 1, ν * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ 1)
    (hα : Small G α B) {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ ≤ r) (hr : r ≤ 1 / 16) (x : G.Ω 1) :
    G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖(α + fun _ : G.Ω 1 => renMassU ν ξ - ν) x‖ ≤
      B + 32 / 15 * r := by
  have hsp : 0 ≤ G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 := by positivity
  have h := renMassU_sub_norm_le hν0 (hξ.trans hr)
  have h1 := hα x
  have h3 := hνℓ x
  have hξ0 := norm_nonneg ξ
  simp only [Pi.add_apply]
  have hΔ : G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖renMassU ν ξ - ν‖ ≤ 32 / 15 * r := by
    calc G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖renMassU ν ξ - ν‖
        ≤ G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * (32 / 15 * ν * ‖ξ‖) :=
          mul_le_mul_of_nonneg_left h hsp
      _ = 32 / 15 * ‖ξ‖ * (ν * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2) := by ring
      _ ≤ 32 / 15 * r * 1 :=
          mul_le_mul (by linarith) h3 (mul_nonneg hν0 hsp) (by linarith)
      _ = 32 / 15 * r := mul_one _
  calc G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α x + (renMassU ν ξ - ν)‖
      ≤ G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * (‖α x‖ + ‖renMassU ν ξ - ν‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hsp
    _ = G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α x‖ +
          G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖renMassU ν ξ - ν‖ := by ring
    _ ≤ B + 32 / 15 * r := add_le_add h1 hΔ

theorem renEdat_f1_le {D : BgData G N} {φ : G.Ω 1 × Fin N → ℂ} {M r : ℝ} (hν0 : 0 ≤ ν)
    (hνℓ : ∀ x : G.Ω 1, ν * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ 1)
    (hM : ∀ x : G.Ω 1, ν * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      vn (fun i => D.h x i - φ (x, i)) ≤ M)
    {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ ≤ r) (hr : r ≤ 1 / 16) (x : G.Ω 1) (i : Fin N) :
    G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖renF1 ν ξ D.h φ (x, i)‖ ≤ 32 / 15 * M * r := by
  have hsp : 0 ≤ G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 := by positivity
  have h := renMassU_sub_norm_le hν0 (hξ.trans hr)
  have hM0 : 0 ≤ M := le_trans (mul_nonneg (mul_nonneg hν0 hsp) (vn_nonneg _)) (hM x)
  have hξ0 := norm_nonneg ξ
  have hvi : ‖D.h x i - φ (x, i)‖ ≤ vn (fun i => D.h x i - φ (x, i)) :=
    norm_le_vn (fun i => D.h x i - φ (x, i)) i
  have h2 : G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖renMassU ν ξ - ν‖ ≤
      32 / 15 * ‖ξ‖ * (ν * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2) := by
    calc _ ≤ G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * (32 / 15 * ν * ‖ξ‖) :=
          mul_le_mul_of_nonneg_left h hsp
      _ = _ := by ring
  simp only [renF1, norm_mul]
  calc G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * (‖renMassU ν ξ - ν‖ * ‖D.h x i - φ (x, i)‖)
      = (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖renMassU ν ξ - ν‖) *
          ‖D.h x i - φ (x, i)‖ := by ring
    _ ≤ (32 / 15 * ‖ξ‖ * (ν * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2)) *
          vn (fun i => D.h x i - φ (x, i)) :=
        mul_le_mul h2 hvi (norm_nonneg _) (by have := hνℓ x; positivity)
    _ = 32 / 15 * ‖ξ‖ * (ν * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
          vn (fun i => D.h x i - φ (x, i))) := by ring
    _ ≤ 32 / 15 * r * M :=
        mul_le_mul (by linarith) (hM x) (mul_nonneg (mul_nonneg hν0 hsp) (vn_nonneg _))
          (by linarith)
    _ = 32 / 15 * M * r := by ring

theorem renEdat_dPsi_le {D : BgData G N} (hε : 0 ≤ ε)
    (hΨ : ∀ x ∈ dataSites G, vn (D.Ψ x) ≤ 3 / 2) {ξ : Fin 3 → ℂ} {r : ℝ} (hξ : ‖ξ‖ ≤ r)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ dataSites G) :
    vn (fun i => renZeta ε ξ * D.Ψ x i) ≤ 3 / 2 * ε * r := by
  rw [vn_smul_complex]
  have hz := norm_renZeta_le hε ξ
  have hξ0 := norm_nonneg ξ
  calc ‖renZeta ε ξ‖ * vn (D.Ψ x) ≤ (ε * ‖ξ‖) * (3 / 2) :=
        mul_le_mul hz (hΨ x hx) (vn_nonneg _) (mul_nonneg hε hξ0)
    _ ≤ 3 / 2 * ε * r := by nlinarith

theorem renEdat_phi_eq {D : BgData G N} (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ)
    (ξ : Fin 3 → ℂ) (x : G.Ω 1) :
    (renEdat ν ε D φ α ξ).1 (x : CTorus d L N₁ m₁ K) = fun i => φ (x, i) := by
  funext i
  simp [renEdat, barField, x.2]

/-- **`DecHyp` in mode P for the shifted data**, from the bounds `BgBounds` of the background with
constant `B ≥ 0`, the mass bound `M`, and the datum bound `‖Ψ‖ ≤ 3/2`, with
`B + (32/15) r ≤ D₀ ≤ 1`, `(32/15) M r ≤ D₁` and `(3/2) ε r ≤ D₁`. -/
theorem renEdat_decHyp_of_bgBounds (S : DGSetting G a ν) {D : BgData G N}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} {B M r D₀ D₁ : ℝ} (hb : BgBounds G D φ α B)
    (hB : 0 ≤ B) (hν0 : 0 ≤ ν)
    (hνℓ : ∀ x : G.Ω 1, ν * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ 1)
    (hM : ∀ x : G.Ω 1, ν * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      vn (fun i => D.h x i - φ (x, i)) ≤ M)
    (hΨ : ∀ x ∈ dataSites G, vn (D.Ψ x) ≤ 3 / 2)
    (hphi : ∀ x : G.Ω 1, vn (fun i => φ (x, i)) ≤ 3 / 2) (hε : 0 ≤ ε)
    {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ ≤ r) (hr : r ≤ 1 / 16) (hD₀ : B + 32 / 15 * r ≤ D₀)
    (hD₀1 : D₀ ≤ 1) (hD₁ : 32 / 15 * M * r ≤ D₁) (hD₁' : 3 / 2 * ε * r ≤ D₁) :
    DecHyp G a ν false (renEdat ν ε D φ α ξ).2.1 (renEdat ν ε D φ α ξ).1
      (renEdat ν ε D φ α ξ).2.2.1 (renEdat ν ε D φ α ξ).2.2.2 D₀ D₁ := by
  have hr0 : 0 ≤ r := (norm_nonneg ξ).trans hξ
  have hD₀0 : 0 ≤ D₀ := by linarith
  have hD₁0 : 0 ≤ D₁ := le_trans (by positivity) hD₁'
  refine ⟨S.toGreen, hD₀0, hD₁0, hD₀1, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, fun h => absurd h (by simp),
    fun h => absurd h (by simp)⟩
  · intro x hx μ
    obtain ⟨h1, h2⟩ := hb.grad ⟨x, hx⟩ μ
    have hle : B / G.spacing x ≤ D₀ / G.spacing x :=
      div_le_div_of_nonneg_right (by linarith) (spacing_pos G).le
    exact ⟨h1.trans hle, h2.trans hle⟩
  · intro x hx
    have hle : B / G.spacing x ^ 2 ≤ D₀ / G.spacing x ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (by have := spacing_pos G (x := x); positivity)
    exact (hb.lap ⟨x, hx⟩).trans hle
  · intro x hx
    have e : (renEdat ν ε D φ α ξ).1 x = fun i => φ (⟨x, hx⟩, i) := renEdat_phi_eq φ α ξ ⟨x, hx⟩
    rw [e]; exact hphi ⟨x, hx⟩
  · intro x
    exact (renEdat_alpha_le hν0 hνℓ hb.alpha hξ hr x).trans hD₀
  · intro x i
    exact (renEdat_f1_le hν0 hνℓ hM hξ hr x i).trans hD₁
  · intro x hx
    exact (renEdat_dPsi_le hε hΨ hξ hx).trans hD₁'

/-- **`StrictDataM … false` for the shifted data**, from the same bounds with strict margins
`B + (32/15) r < D₀`, `(32/15) M r < D₁`, `(3/2) ε r < D₁` and `‖φ‖ < 3/2`. -/
theorem renEdat_strictDataM_of_bgBounds {D : BgData G N}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} {B M r D₀ D₁ : ℝ} (hb : BgBounds G D φ α B)
    (hν0 : 0 ≤ ν)
    (hνℓ : ∀ x : G.Ω 1, ν * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ 1)
    (hM : ∀ x : G.Ω 1, ν * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      vn (fun i => D.h x i - φ (x, i)) ≤ M)
    (hΨ : ∀ x ∈ dataSites G, vn (D.Ψ x) ≤ 3 / 2)
    (hphi : ∀ x : G.Ω 1, vn (fun i => φ (x, i)) < 3 / 2) (hε : 0 ≤ ε)
    {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ ≤ r) (hr : r ≤ 1 / 16) (hD₀ : B + 32 / 15 * r < D₀)
    (hD₁ : 32 / 15 * M * r < D₁) (hD₁' : 3 / 2 * ε * r < D₁) :
    StrictDataM G N false D₀ D₁ (renEdat ν ε D φ α ξ) := by
  have hr0 : 0 ≤ r := (norm_nonneg ξ).trans hξ
  refine ⟨⟨fun x μ => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun x i => ?_, fun x => ?_⟩,
    fun h => absurd h (by simp)⟩
  · obtain ⟨h1, h2⟩ := hb.grad x μ
    have hsp := spacing_pos G (x := (x : CTorus d L N₁ m₁ K))
    have hlt : B / G.spacing (x : CTorus d L N₁ m₁ K) < D₀ / G.spacing (x : CTorus d L N₁ m₁ K) :=
      div_lt_div_of_pos_right (by linarith) hsp
    exact ⟨lt_of_le_of_lt h1 hlt, lt_of_le_of_lt h2 hlt⟩
  · have hsp := spacing_pos G (x := (x : CTorus d L N₁ m₁ K))
    have hlt : B / G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 <
        D₀ / G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 :=
      div_lt_div_of_pos_right (by linarith) (by positivity)
    exact lt_of_le_of_lt (hb.lap x) hlt
  · have e : (renEdat ν ε D φ α ξ).1 (x : CTorus d L N₁ m₁ K) = fun i => φ (x, i) :=
      renEdat_phi_eq φ α ξ x
    show vn ((renEdat ν ε D φ α ξ).1 (x : CTorus d L N₁ m₁ K)) < 3 / 2
    rw [e]; exact hphi x
  · exact lt_of_le_of_lt (renEdat_alpha_le hν0 hνℓ hb.alpha hξ hr x) hD₀
  · exact lt_of_le_of_lt (renEdat_f1_le hν0 hνℓ hM hξ hr x i) hD₁
  · exact lt_of_le_of_lt (renEdat_dPsi_le hε hΨ hξ x.2) hD₁'

end Generic

section Ren

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
  {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
  {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The bounds of the decoupled background and of the datum** for every complex cut `s` with
`‖s_P‖ ≤ e^κ` (physical setting `FlCore`).  With `δ = xiC1 d · ε`:
(1) `BgBounds` at `K₄ δ`; (2) the mass bound `ν ℓ² ‖h - φ_s‖ ≤ m_* ε`, `m_* = 3 + (K₄ + K₁) C₁`;
(3) `‖φ_s‖ < 3/2` on `Ω₁`; (4) `‖Ψ‖ ≤ 3/2` on the data sites. -/
theorem renDec_data_bounds_of_flCore
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {D : BgData Gp N} (hD : XiCOneReal Gp (compWeight L a₁) ν eps D)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) :
    BgBounds Gp D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D)
        (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D)
        (K4 d L N BG κ * (xiC1 d * eps)) ∧
      (∀ x : Gp.Ω 1, ν * Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
        vn (fun i => D.h x i - decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D (x, i)) ≤
        (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d) * eps) ∧
      (∀ x : Gp.Ω 1,
        vn (fun i => decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D (x, i)) < 3 / 2) ∧
      (∀ x ∈ dataSites Gp, vn (D.Ψ x) ≤ 3 / 2) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hε := hC.eps_pos
  have hC1pos : 0 < xiC1 d := by unfold xiC1; positivity
  have hδ : 0 < xiC1 d * eps := mul_pos hC1pos hε
  have hδ7 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hc1 : xiC1 d * eps ≤ bgC1 d L N := hδ7.trans (c7_le_bgC1 d L N BG κ)
  have hδ0 : xiC1 d * eps ≤ bgC0 d L N := hc1.trans (bgC1_le_bgC0 d L N hd0)
  have hK4 := (K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0).le
  have hDom : InDomainC Gp ν (xiC1 d * eps) (xiC1 d * eps) D :=
    xiCData_inDomainC hC.HBp hC.small1 hD.xiCOne
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  obtain ⟨φ, α, hid, huniq, -, -, hbd⟩ :=
    i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hs hδ le_rfl hδ0 hδ7 hνε hDom
  obtain ⟨e1, e2⟩ := decBg_eq hid huniq
  rw [e1, e2]
  obtain ⟨-, -, hb1, ⟨W⟩⟩ := hD.xiCOne.bg hC.HBp hC.small1 hε hc1
  have hphi := hC.phi_lt
  have hKδ := mul_nonneg hK4 hδ.le
  have hν0 := hC.HBp.mass
  have hΨ : ∀ x ∈ dataSites Gp, vn (D.Ψ x) ≤ 1 + 3 * (xiC1 d * eps) := fun x hx =>
    (W.vn_le hδ hx).trans (by linarith)
  refine ⟨hbd, fun x => ?_, fun x => ?_, fun x hx => ?_⟩
  · have hsp := spacing_pos Gp (x := (x : CTorus d L N₁ m₁ K))
    have hνℓ : ν * Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ 1 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsp.le (spacing_le Gp x.2) 2) hν0).trans
        hC.HBp.massLe
    have hνℓ0 : 0 ≤ ν * Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 := by positivity
    have m1 := XiCOne.mass_le hC.HBp hD.xiCOne x
    have v1 := hb1.val x
    have v2 := hbd.val x
    have t1 := vn_triangle (fun i => D.h x i) (fun i => bgFieldC Gp (compWeight L a₁) ν
      (bgC0 d L N) D (x, i)) (fun i => φ (x, i))
    have t2 := vn_triangle (fun i => bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D (x, i))
      (D.Ψ x) (fun i => φ (x, i))
    have s2 : vn (D.Ψ x - fun i => φ (x, i)) = vn ((fun i => φ (x, i)) - D.Ψ x) :=
      vn_sub_comm _ _
    have hT : vn ((fun i => D.h x i) - fun i => φ (x, i)) ≤
        vn (fun i => D.h x i - bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D (x, i)) +
          (bgK1 d L N * (xiC1 d * eps) + K4 d L N BG κ * (xiC1 d * eps)) := by
      have e1' : vn ((fun i => D.h x i) - fun i => φ (x, i)) ≤
          vn ((fun i => D.h x i) - fun i => bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D (x, i))
            + vn ((fun i => bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D (x, i)) -
              fun i => φ (x, i)) := t1
      have e2' : vn ((fun i => bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D (x, i)) -
              fun i => φ (x, i)) ≤
          vn ((fun i => bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D (x, i)) - D.Ψ x) +
            vn (D.Ψ x - fun i => φ (x, i)) := t2
      have e3 : vn ((fun i => bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D (x, i)) - D.Ψ x) ≤
          bgK1 d L N * (xiC1 d * eps) := v1
      have e4 : vn ((fun i => φ (x, i)) - D.Ψ x) ≤ K4 d L N BG κ * (xiC1 d * eps) := v2
      show vn ((fun i => D.h x i) - fun i => φ (x, i)) ≤ vn ((fun i => D.h x i) -
        fun i => bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D (x, i)) + _
      linarith
    have hT0 : 0 ≤ bgK1 d L N * (xiC1 d * eps) + K4 d L N BG κ * (xiC1 d * eps) := by
      have := bgK1_pos d L N
      positivity
    show ν * Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * vn ((fun i => D.h x i) -
      fun i => φ (x, i)) ≤ _
    calc ν * Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * vn ((fun i => D.h x i) -
          fun i => φ (x, i))
        ≤ ν * Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
          (vn (fun i => D.h x i - bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D (x, i)) +
            (bgK1 d L N * (xiC1 d * eps) + K4 d L N BG κ * (xiC1 d * eps))) :=
          mul_le_mul_of_nonneg_left hT hνℓ0
      _ = ν * Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
            vn (fun i => D.h x i - bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D (x, i)) +
          ν * Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
            (bgK1 d L N * (xiC1 d * eps) + K4 d L N BG κ * (xiC1 d * eps)) := by ring
      _ ≤ 3 * eps + 1 * (bgK1 d L N * (xiC1 d * eps) + K4 d L N BG κ * (xiC1 d * eps)) :=
          add_le_add m1 (mul_le_mul_of_nonneg_right hνℓ hT0)
      _ = (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d) * eps := by ring
  · have hxd : (x : CTorus d L N₁ m₁ K) ∈ dataSites Gp :=
      (mem_dataSites (G := Gp)).2 (Or.inl x.2)
    have v2 := hbd.val x
    have h3 := vn_le_sub_add (fun i => φ (x, i)) (D.Ψ x)
    have h2 := hΨ x hxd
    linarith
  · have h1 := hΨ x hx
    linarith

theorem renMass_field_le_of_flCore
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {D : BgData Gp N} (hD : XiCOneReal Gp (compWeight L a₁) ν eps D)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (x : Gp.Ω 1) :
    ν * Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      vn (fun i => D.h x i - decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D (x, i)) ≤
      (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d) * eps :=
  (renDec_data_bounds_of_flCore hC hD hs).2.1 x

theorem renMassStar_nonneg (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) :
    0 ≤ 3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hK4 := (K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0).le
  have := bgK1_pos d L N
  have : 0 < xiC1 d := by unfold xiC1; positivity
  positivity

theorem renSpacing_mass_le (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (x : Gp.Ω 1) : ν * Gp.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ 1 := by
  have hsp := spacing_pos Gp (x := (x : CTorus d L N₁ m₁ K))
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsp.le (spacing_le Gp x.2) 2)
    hC.HBp.mass).trans hC.HBp.massLe

/-- **Pointwise `DecHyp` (mode P)** at `(D₀, δ₁(r))`, `r = ‖ξ‖`, `D₀ = 2 K₄ δ + 3 r₀`,
`δ₁(r) = b_* ε r`, `b_* = 3/2 + (32/15) m_*`, for every complex cut `s` with `‖s_P‖ ≤ e^κ`,
`‖ξ‖ < r₀ ≤ 1/16`; the margin `D₀ ≤ 1` is the explicit hypothesis `hD₀`. -/
theorem renEdat_decHyp_of_flCore
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {D : BgData Gp N} (hD : XiCOneReal Gp (compWeight L a₁) ν eps D)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {r₀ : ℝ} (hr₀ : r₀ ≤ 1 / 16)
    {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ < r₀)
    (hD₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1) :
    DecHyp Gp (compWeight L a₁) ν false
      (renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D)
        (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D) ξ).2.1
      (renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D)
        (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D) ξ).1
      (renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D)
        (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D) ξ).2.2.1
      (renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D)
        (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D) ξ).2.2.2
      (2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀)
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * ‖ξ‖) := by
  obtain ⟨hb, hm, hp, hΨ⟩ := renDec_data_bounds_of_flCore hC hD hs
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hε := hC.eps_pos
  have hK4 := (K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0).le
  have hC1pos : 0 < xiC1 d := by unfold xiC1; positivity
  have hKδ := mul_nonneg hK4 (mul_pos hC1pos hε).le
  have hm0 := renMassStar_nonneg hC
  have hξ0 := norm_nonneg ξ
  refine renEdat_decHyp_of_bgBounds hC.Sp hb hKδ hC.HBp.mass (renSpacing_mass_le hC) hm hΨ
    (fun x => (hp x).le) hε.le (le_refl ‖ξ‖) (by linarith) (by linarith) hD₀ ?_ ?_
  · nlinarith [mul_nonneg hε.le hξ0]
  · nlinarith [mul_nonneg (mul_nonneg hm0 hε.le) hξ0]

/-- **Strict data on the fixed domain**: `StrictDataM … false D₀ D₁` with
`D₀ = 2 K₄ δ + 3 r₀`, `D₁ = b_* ε r₀`, for every complex cut `s` with `‖s_P‖ ≤ e^κ` and every
`‖ξ‖ < r₀ ≤ 1/16`, `0 < r₀` being implied.  Only `FlCore` is used: the factor 2 and the
`3 r₀` give the strict room, and `D₁ > 0` covers `ξ = 0`.  The strictness of the gradient and
Laplacian clauses comes from `BgBounds` at the non-strict constant `K₄ δ < D₀`. -/
theorem renEdat_strictDataM_of_flCore
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {D : BgData Gp N} (hD : XiCOneReal Gp (compWeight L a₁) ν eps D)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {r₀ : ℝ} (hr₀ : r₀ ≤ 1 / 16)
    {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ < r₀) :
    StrictDataM Gp N false (2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀)
      ((3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀)
      (renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D)
        (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D) ξ) := by
  obtain ⟨hb, hm, hp, hΨ⟩ := renDec_data_bounds_of_flCore hC hD hs
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hε := hC.eps_pos
  have hK4 := (K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0).le
  have hC1pos : 0 < xiC1 d := by unfold xiC1; positivity
  have hKδ := mul_nonneg hK4 (mul_pos hC1pos hε).le
  have hm0 := renMassStar_nonneg hC
  have hξ0 := norm_nonneg ξ
  have hr0 : 0 < r₀ := lt_of_le_of_lt hξ0 hξ
  refine renEdat_strictDataM_of_bgBounds hb hC.HBp.mass (renSpacing_mass_le hC) hm hΨ hp hε.le
    (le_refl ‖ξ‖) (by linarith) (by linarith) ?_ ?_
  · nlinarith [mul_pos hε hr0, mul_nonneg (mul_nonneg hm0 hε.le) (sub_nonneg.2 hξ.le)]
  · nlinarith [mul_pos hε hr0, mul_nonneg hε.le (sub_nonneg.2 hξ.le),
      mul_nonneg (mul_nonneg hm0 hε.le) hr0.le]

end Ren

section Margins

/-- **The margins have room** (abstract form).  If `A = 2 K₄ δ` satisfies `0 ≤ A < 1` and
`A < Δ` (`Δ` the `deltaStar'` value) and `β = b_* ε ≥ 0`, there is `r₀ ∈ (0, 1/16]` with
`A + 3 r₀ ≤ 1`, `A + 3 r₀ ≤ Δ` and `β r₀ ≤ Δ`. -/
theorem renMargins_exists_r₀ {A Δ β : ℝ} (hA0 : 0 ≤ A) (hA1 : A < 1) (hAΔ : A < Δ)
    (hβ : 0 ≤ β) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 16 ∧ A + 3 * r₀ ≤ 1 ∧ A + 3 * r₀ ≤ Δ ∧ β * r₀ ≤ Δ := by
  have hΔ : 0 < Δ := by linarith
  refine ⟨min (min (1 / 16) ((1 - A) / 3)) (min ((Δ - A) / 3) (Δ / (β + 1))), ?_, ?_, ?_, ?_, ?_⟩
  · have : 0 < Δ / (β + 1) := div_pos hΔ (by linarith)
    refine lt_min (lt_min (by norm_num) (by linarith)) (lt_min (by linarith) this)
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · have : min (min (1 / 16) ((1 - A) / 3)) (min ((Δ - A) / 3) (Δ / (β + 1))) ≤ (1 - A) / 3 :=
      ((min_le_left _ _).trans (min_le_right _ _))
    linarith
  · have : min (min (1 / 16) ((1 - A) / 3)) (min ((Δ - A) / 3) (Δ / (β + 1))) ≤ (Δ - A) / 3 :=
      ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  · have h : min (min (1 / 16) ((1 - A) / 3)) (min ((Δ - A) / 3) (Δ / (β + 1))) ≤ Δ / (β + 1) :=
      ((min_le_right _ _).trans (min_le_right _ _))
    calc β * min (min (1 / 16) ((1 - A) / 3)) (min ((Δ - A) / 3) (Δ / (β + 1)))
        ≤ β * (Δ / (β + 1)) := mul_le_mul_of_nonneg_left h hβ
      _ ≤ Δ := by
          rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
          nlinarith

/-- **Arithmetic satisfiability** of all the margins for fixed constants `K₄, K₁, C₁` and
`Δ > 0`: there are `ε₀, r₀ > 0`, `r₀ ≤ 1/16`, such that for every `0 < ε ≤ ε₀` the conditions
`phi_lt`, `D₀ ≤ 1`, `D₀ ≤ Δ` and `D₁ ≤ Δ` hold, with `δ = C₁ ε`, `D₀ = 2 K₄ δ + 3 r₀` and
`D₁ = b_* ε r₀`. -/
theorem renMargins_arith {K₄ K₁ C₁ Δ : ℝ} (hK4 : 0 ≤ K₄) (hK1 : 0 ≤ K₁) (hC1 : 0 < C₁)
    (hΔ : 0 < Δ) :
    ∃ ε₀ r₀ : ℝ, 0 < ε₀ ∧ 0 < r₀ ∧ r₀ ≤ 1 / 16 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      (3 + K₄) * (C₁ * ε) < 1 / 2 ∧ 2 * (K₄ * (C₁ * ε)) + 3 * r₀ ≤ 1 ∧
      2 * (K₄ * (C₁ * ε)) + 3 * r₀ ≤ Δ ∧
      (3 / 2 + 32 / 15 * (3 + (K₄ + K₁) * C₁)) * ε * r₀ ≤ Δ := by
  set Q : ℝ := (3 + K₄) * C₁ with hQ
  set b : ℝ := 3 / 2 + 32 / 15 * (3 + (K₄ + K₁) * C₁) with hb
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  refine ⟨min (min (1 / (4 * Q)) (Δ / (4 * Q))) (1 / b), min (1 / 16) (Δ / 6),
    lt_min (lt_min (by positivity) (by positivity)) (by positivity),
    lt_min (by norm_num) (by positivity), min_le_left _ _, fun ε hε hεle => ?_⟩
  have e1 : ε ≤ 1 / (4 * Q) := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have e2 : ε ≤ Δ / (4 * Q) := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have e3 : ε ≤ 1 / b := hεle.trans (min_le_right _ _)
  have r1 : min (1 / 16) (Δ / 6) ≤ 1 / 16 := min_le_left _ _
  have r2 : min (1 / 16) (Δ / 6) ≤ Δ / 6 := min_le_right _ _
  have r0 : 0 < min (1 / 16) (Δ / 6) := lt_min (by norm_num) (by positivity)
  have f1 : 4 * Q * ε ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at e1; linarith
  have f2 : 4 * Q * ε ≤ Δ := by
    rw [le_div_iff₀ (by positivity)] at e2; linarith
  have f3 : b * ε ≤ 1 := by
    rw [le_div_iff₀ hb0] at e3; linarith
  have hK : K₄ * (C₁ * ε) ≤ Q * ε := by
    have : Q * ε - K₄ * (C₁ * ε) = 3 * C₁ * ε := by rw [hQ]; ring
    nlinarith [mul_pos hC1 hε]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (3 + K₄) * (C₁ * ε) = Q * ε := by rw [hQ]; ring
    rw [this]; linarith
  · linarith
  · linarith
  · calc b * ε * min (1 / 16) (Δ / 6) ≤ 1 * min (1 / 16) (Δ / 6) :=
          mul_le_mul_of_nonneg_right (by linarith) r0.le
      _ ≤ Δ := by linarith

section Flcore

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
  {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
  {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The margins in the setting `FlCore`.**  Given `FlCore` and the one top-level margin
`2 K₄ δ < deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)` (not a consequence of `FlCore`,
whose `B_le` is stated with `BG₂`), the other three margins hold for a suitable `r₀ ∈ (0, 1/16]`. -/
theorem renMargins_exists_r₀_of_flCore
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hA : 2 * (K4 d L N BG κ * (xiC1 d * eps)) <
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 16 ∧
      2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1 ∧
      2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
        deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) ∧
      (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
        deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hε := hC.eps_pos
  have hK4 := (K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0).le
  have hC1pos : 0 < xiC1 d := by unfold xiC1; positivity
  have hKδ := mul_nonneg hK4 (mul_pos hC1pos hε).le
  have hphi := hC.phi_lt
  have hm0 := renMassStar_nonneg hC
  have h3 : 0 ≤ 3 * (xiC1 d * eps) := by positivity
  exact renMargins_exists_r₀ (by linarith) (by linarith) hA
    (mul_nonneg (by positivity) hε.le)

end Flcore

end Margins

end Balaban.Fluctuation
