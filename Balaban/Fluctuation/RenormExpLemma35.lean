/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Prop51Mass
public import Balaban.Fluctuation.RenormIdentity
public import Balaban.SmallField.XiProps
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Lemma 3.5 (ii): analyticity in `(ψ, h, ξ)` and the bound `K₂ ε |ξ|` (FLUCTUATION.md §3.6)

FLUCTUATION.md v2.3 §3.6, Lemma 3.5 (ii) (P4 (4.10)–(4.11), P6 (2.22)–(2.24)).  The landed part
(`RenormIdentity.lean`) identifies `(δφ, δα) = (φ_u - φ, α_u - α)` as the solution of BG
Proposition 5.1 for **real** renormalization parameters.  Here the parameters
`ξ = (ξ₁, ξ₂, ξ₃) = (ξ 0, ξ 1, ξ 2) ∈ ℂ³` are complex:

* `ζ = ε ξ₁` (`renZeta`), the lifted datum `δΨ = ζ ψ`;
* the unrenormalized mass `ν_u = ν (1 + ξ₂) / (1 + ξ₃)` (`renMassU`; the base mass `ν = ν_{k+1}`
  is fixed, so `ν_u` depends on `ξ`, and Proposition 5.1 is needed jointly in the data and the
  mass: `Balaban/Background/Prop51Mass.lean`);
* `f₁ = (ν_u - ν)(h - φ)` (`renF1`; `f₁ = 0` in the `ν`-free convention, where `ν = 0` in the
  variational problems).

The datum `ψ` (fine units: the lifted field `D.Ψ` with `h̃ = D.h`) ranges over the class domain
`Ξ^c_{k+1}(𝔹; 1, ε)` (`XiCOne`, the top level of the generating set).  The base is the background
`(φ, α) = (bgFieldC, bgMultC)` of `(ψ, h)` at the mass `ν` (Def-5(b)).

* `prop51Hyp_xi` (complete) and `prop51Hyp_xi_nuFree`: the `Ξ`-domain instantiation of the hypotheses
  (P1)–(P4) of Proposition 5.1 for the shifted multiplier, with `δ₁ = 8 ε |ξ|_∞` (complete) resp.
  `δ₁ = (3/2) ε |ξ|_∞` (`ν`-free);
* `IsRenSol` — the properties of the solution map `F : ((Ψ, h̃), ξ) ↦ (δφ, δα)`; `exists_isRenSol`,
  `exists_isRenSol_nuFree` (and `exists_isRenSol_params`, the inhabitation witness): there is one
  `F`, complex-analytic jointly in `(Ψ, h̃, ξ)` on `Ξ^c_{k+1}(1, ε) × {|ξ|_∞ < r}`, solving the
  complex-mass system, unique in `|δα|₂ ≤ c₆`, with
  `‖δφ‖_*, |δα|₂ ≤ 8 K₂ ε |ξ|_∞` (complete) resp. `≤ (3/2) K₂ ε |ξ|_∞` (`ν`-free);
* `IsRenSol.eq_zero`: `F = 0` at `ξ = 0`; `IsRenSol.eq_bg`: for real `ξ`, `F = (φ_u - φ, α_u - α)`
  with `(φ_u, α_u)` the small solution of the unrenormalized datum `((1 + ζ) ψ, h)` at `ν_u`.

Constants: P4 (4.10)–(4.11) has `7 K₂`, FLUCTUATION.md has `3 K₂`.  The `ν`-free bound `(3/2) K₂` is
sharper; the complete-convention `8 K₂` comes from the `Ξ^c` mass condition as landed
(`√ν ℓ |φ^r - h₀| < ε` on the real part and the displacement bounds, not a complex mass
condition, see `Balaban/SmallField/Xi.lean` item 4): `ν ℓ² |h - φ| < 3 ε`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Balaban.SmallField Finset Matrix

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Params

/-- The renormalization of the spin, `ζ = ε ξ₁` (`ξ₁ = ξ 0`). -/
def renZeta (ε : ℝ) (ξ : Fin 3 → ℂ) : ℂ := (ε : ℂ) * ξ 0

/-- The unrenormalized mass `ν_u = ν (1 + ξ₂) / (1 + ξ₃)` (`ξ₂ = ξ 1`, `ξ₃ = ξ 2`), i.e.
`ν (1 + ξ₂) = ν_u (1 + ξ₃)` as in `lemma35_i_complete`. -/
noncomputable def renMassU (ν : ℝ) (ξ : Fin 3 → ℂ) : ℂ := (ν : ℂ) * (1 + ξ 1) / (1 + ξ 2)

/-- The source `f₁ = (ν_u - ν)(h - φ)` of Lemma 3.5 (ii). -/
noncomputable def renF1 {G : GeneratingSet d L N₀ k ϱ} (ν : ℝ) (ξ : Fin 3 → ℂ)
    (h : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ) : G.Ω 1 × Fin N → ℂ :=
  fun p => (renMassU ν ξ - ν) * (h p.1 p.2 - φ p)

theorem one_add_ne_zero_of_norm {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ < 1) (i : Fin 3) : 1 + ξ i ≠ 0 := by
  intro h
  have e : ξ i = -1 := by linear_combination h
  have := norm_le_pi_norm ξ i
  rw [e, norm_neg, norm_one] at this
  linarith

theorem renMassU_relation (ν : ℝ) {ξ : Fin 3 → ℂ} (h : 1 + ξ 2 ≠ 0) :
    (ν : ℂ) * (1 + ξ 1) = renMassU ν ξ * (1 + ξ 2) := by
  unfold renMassU; field_simp

theorem renMassU_zero (ξ : Fin 3 → ℂ) : renMassU 0 ξ = 0 := by simp [renMassU]

theorem renF1_zero {G : GeneratingSet d L N₀ k ϱ} (ξ : Fin 3 → ℂ)
    (h : Torus d (N₀ * L ^ k) → Fin N → ℂ) (φ : G.Ω 1 × Fin N → ℂ) : renF1 0 ξ h φ = 0 := by
  funext p; simp [renF1, renMassU_zero]

theorem renMassU_sub_norm_le {ν : ℝ} (hν : 0 ≤ ν) {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ ≤ 1 / 16) :
    ‖renMassU ν ξ - ν‖ ≤ 32 / 15 * ν * ‖ξ‖ := by
  have h1 : ‖ξ 1‖ ≤ ‖ξ‖ := norm_le_pi_norm ξ 1
  have h2 : ‖ξ 2‖ ≤ ‖ξ‖ := norm_le_pi_norm ξ 2
  have hden : 15 / 16 ≤ ‖1 + ξ 2‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-ξ 2)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have hne : 1 + ξ 2 ≠ 0 := by
    intro h; rw [h, norm_zero] at hden; linarith
  have e : renMassU ν ξ - ν = ν * (ξ 1 - ξ 2) / (1 + ξ 2) := by
    unfold renMassU; field_simp; ring
  rw [e, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hν,
    div_le_iff₀ (by linarith)]
  have h12 : ‖ξ 1 - ξ 2‖ ≤ 2 * ‖ξ‖ := (norm_sub_le _ _).trans (by linarith)
  have hn := norm_nonneg ξ
  calc ν * ‖ξ 1 - ξ 2‖ ≤ ν * (2 * ‖ξ‖) := mul_le_mul_of_nonneg_left h12 hν
    _ ≤ 32 / 15 * ν * ‖ξ‖ * ‖1 + ξ 2‖ := by
        have := mul_nonneg hν hn
        nlinarith

theorem renMassU_ofReal (ν : ℝ) (t : Fin 3 → ℝ) :
    renMassU ν (fun i => (t i : ℂ)) = ((ν * (1 + t 1) / (1 + t 2) : ℝ) : ℂ) := by
  unfold renMassU; push_cast; ring

theorem renZeta_ofReal (ε : ℝ) (t : Fin 3 → ℝ) :
    renZeta ε (fun i => (t i : ℂ)) = ((ε * t 0 : ℝ) : ℂ) := by
  unfold renZeta; push_cast; ring

theorem norm_renZeta_le {ε : ℝ} (hε : 0 ≤ ε) (ξ : Fin 3 → ℂ) : ‖renZeta ε ξ‖ ≤ ε * ‖ξ‖ := by
  unfold renZeta
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm ξ 0) hε

end Params

section Domain

variable (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν ε : ℝ)

/-- **The class domain `Ξ^c_k(𝔹; 1, ε)`** (top level `n = k` of `𝔹`) as a predicate on data:
`D` realizes a member `(Ψ₀ + Ψ'', h₀ + h'')` of `XiC G a ν k 1 ε`. -/
def XiCOne (D : BgData G N) : Prop :=
  ∃ (Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ),
    XiC G a ν k 1 ε Ψ₀ h₀ Ψ'' h'' ∧ RealizesC D Ψ₀ h₀ Ψ'' h''

/-- The domain of Lemma 3.5 (ii): `((Ψ, h̃), ξ)` with `(Ψ, h̃)` the data of a member of
`Ξ^c_k(𝔹; 1, ε)` and `|ξ|_∞ < r`. -/
def renDom (r : ℝ) : Set (RawData d L N₀ k N × (Fin 3 → ℂ)) :=
  {q | ∃ D : BgData G N, XiCOne G a ν ε D ∧ q.1 = (D.Ψ, D.h) ∧ ‖q.2‖ < r}

variable {G a ν ε}

/-- A datum is determined by the values it realizes. -/
theorem realizesC_unique {D D' : BgData G N} {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ}
    {h₀ : Fin N → ℝ} {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (h1 : RealizesC D Ψ₀ h₀ Ψ'' h'') (h2 : RealizesC D' Ψ₀ h₀ Ψ'' h'') : D = D' := by
  classical
  have eΨ : D.Ψ = D'.Ψ := by
    funext x i
    by_cases hx : x ∈ dataSites G
    · exact (h1.1 x hx i).trans (h2.1 x hx i).symm
    · rw [D.Ψ_zero x hx, D'.Ψ_zero x hx]
  have eh : D.h = D'.h := by
    funext x i
    by_cases hx : x ∈ G.Ω 1
    · exact (h1.2 x hx i).trans (h2.2 x hx i).symm
    · rw [D.h_zero x hx, D'.h_zero x hx]
  cases D with
  | mk Ψ h hl1 hl2 hz1 hz2 =>
    cases D' with
    | mk Ψ' h' hl1' hl2' hz1' hz2' =>
      simp only at eΨ eh
      subst eΨ eh
      rfl

/-- (Ξ1) for the datum: `D ∈ Ψ̃^c(𝔹; C₁ ε, C₁ ε)`, `C₁ = xiC1 d`. -/
theorem XiCOne.inDomainC (H : BgHyp d L k ϱ a ν) (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    {D : BgData G N} (hD : XiCOne G a ν ε D) : InDomainC G ν (xiC1 d * ε) (xiC1 d * ε) D := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := hD
  exact ⟨Ψ₀, h₀, Ψ'', h'', xiC_one_subset H hsm hX, hR.1, hR.2⟩

/-- The background facts on `Ξ^c_k(𝔹; 1, ε)`: the datum lies in the union domain of Theorem 7.2,
`(bgFieldC, bgMultC)` is its small solution, with the bounds `K₁ δ`, `δ = C₁ ε`. -/
theorem XiCOne.bg (H : BgHyp d L k ϱ a ν) (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (hε : 0 < ε) (hc1 : xiC1 d * ε ≤ bgC1 d L N) {D : BgData G N} (hD : XiCOne G a ν ε D) :
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D ∧
      IsSmallSolution G a ν (bgC0 d L N) D (bgFieldC G a ν (bgC0 d L N) D)
        (bgMultC G a ν (bgC0 d L N) D) ∧
      BgBounds G D (bgFieldC G a ν (bgC0 d L N) D) (bgMultC G a ν (bgC0 d L N) D)
        (bgK1 d L N * (xiC1 d * ε)) ∧
      Nonempty (DataWit G ν (xiC1 d * ε) (xiC1 d * ε) D) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hδ0 : 0 < xiC1 d * ε := by have := one_le_xiC1 d; positivity
  have hDC := hD.inDomainC H hsm
  have hδc0 : xiC1 d * ε ≤ bgC0 d L N := hc1.trans (bgC1_le_bgC0 d L N hd0)
  have hνε : ν * ((L : ℝ) ^ k) ^ 2 * (xiC1 d * ε) ^ 2 ≤ (xiC1 d * ε) ^ 2 :=
    mul_le_of_le_one_left (sq_nonneg _) H.massLe
  have hDU : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D :=
    ⟨_, _, hδ0, le_rfl, hδc0, hc1, hνε, hDC⟩
  obtain ⟨-, hs, hb⟩ := theorem72 H hDU
  exact ⟨hDU, hs, hb _ _ hδ0 le_rfl hδc0 hc1 hνε hDC, DataWit.exists hDC⟩

/-- **The mass condition on `Ξ^c_k(𝔹; 1, ε)`**: `ν ℓ(x)² |h̃(x) - φ(x)| ≤ 3 ε` for the complex
background `φ = bgFieldC`.  From `√ν ℓ |φ^r - h₀| < ε` (`XiBounds.mass`),
`ν ℓ² |h''| < ε` (`XiCBounds.hAbs`) and `|φ^c - φ^r| < ε` (`XiCBounds.val`), with `ν ℓ² ≤ 1`. -/
theorem XiCOne.mass_le (H : BgHyp d L k ϱ a ν) {D : BgData G N} (hD : XiCOne G a ν ε D)
    (x : G.Ω 1) :
    ν * G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
      vn (fun i => D.h x i - bgFieldC G a ν (bgC0 d L N) D (x, i)) ≤ 3 * ε := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hR⟩ := hD
  obtain ⟨-, hε, Dr, Dc, hXr, hC, -, hb⟩ := hX
  obtain rfl : D = Dc := realizesC_unique hR hC
  obtain ⟨-, -, hbr⟩ := hXr
  set φc := bgFieldC G a ν (bgC0 d L N) D
  set φr := bgField G a ν Dr
  set ℓ := G.spacing (x : Torus d (N₀ * L ^ k)) with hℓ
  have hν0 := H.mass
  have hsp : 0 < ℓ := spacing_pos G
  have hνℓ : ν * ℓ ^ 2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsp.le (spacing_le G x.2) 2) hν0).trans
      H.massLe
  have hνℓ0 : 0 ≤ ν * ℓ ^ 2 := by positivity
  have hh : ∀ i, D.h x i = (h₀ i : ℂ) + h'' x i := hR.2 x x.2
  have e : (fun i => D.h x i - φc (x, i)) =
      ((fun i => (h₀ i : ℂ) - φr (x, i)) + fun i => h'' x i) + fun i => φr (x, i) - φc (x, i) := by
    funext i; simp only [Pi.add_apply, hh]; ring
  -- the real mass term
  have t1 : ν * ℓ ^ 2 * vn (fun i => (h₀ i : ℂ) - φr (x, i)) ≤ ε := by
    have hm := hbr.mass x
    have hsq : Real.sqrt ν * ℓ ≤ 1 := by
      have : Real.sqrt ν * ℓ = Real.sqrt (ν * ℓ ^ 2) := by
        rw [Real.sqrt_mul hν0, Real.sqrt_sq hsp.le]
      rw [this, Real.sqrt_le_one]
      exact hνℓ
    have hcomm : vn (fun i => (h₀ i : ℂ) - φr (x, i)) = vn (fun i => φr (x, i) - (h₀ i : ℂ)) := by
      rw [← vn_neg]; congr 1; funext i; ring
    have e2 : ν * ℓ ^ 2 = (Real.sqrt ν * ℓ) * (Real.sqrt ν * ℓ) := by
      have := Real.mul_self_sqrt hν0
      nlinarith
    rw [hcomm, e2, mul_assoc]
    have h0 : 0 ≤ Real.sqrt ν * ℓ := by positivity
    calc Real.sqrt ν * ℓ * (Real.sqrt ν * ℓ * vn (fun i => φr (x, i) - (h₀ i : ℂ)))
        ≤ 1 * ε := mul_le_mul hsq (by linarith [hm]) (mul_nonneg h0 (vn_nonneg _)) zero_le_one
      _ = ε := one_mul ε
  -- the displacement of `h`
  have t2 : ν * ℓ ^ 2 * vn (fun i => h'' x i) ≤ ε := by
    have := hb.hAbs x x.2
    have e3 : (1 * ε) ^ 2 / ε = ε := by field_simp
    rw [e3] at this
    exact this.le
  -- the displacement of the field
  have t3 : ν * ℓ ^ 2 * vn (fun i => φr (x, i) - φc (x, i)) ≤ ε := by
    have hv := hb.val x
    have hcomm : vn (fun i => φr (x, i) - φc (x, i)) = vn (fun i => φc (x, i) - φr (x, i)) := by
      rw [← vn_neg]; congr 1; funext i; ring
    rw [hcomm]
    calc ν * ℓ ^ 2 * vn (fun i => φc (x, i) - φr (x, i)) ≤ 1 * ε :=
          mul_le_mul hνℓ hv.le (vn_nonneg _) zero_le_one
      _ = ε := one_mul ε
  rw [e]
  have hsum' : vn (((fun i => (h₀ i : ℂ) - φr (x, i)) + fun i => h'' x i) +
      fun i => φr (x, i) - φc (x, i)) ≤ vn (fun i => (h₀ i : ℂ) - φr (x, i)) +
        vn (fun i => h'' x i) + vn (fun i => φr (x, i) - φc (x, i)) := by
    have a1 := vn_add ((fun i => (h₀ i : ℂ) - φr (x, i)) + fun i => h'' x i)
      (fun i => φr (x, i) - φc (x, i))
    have a2 := vn_add (fun i => (h₀ i : ℂ) - φr (x, i)) (fun i => h'' x i)
    linarith
  calc ν * ℓ ^ 2 * vn (((fun i => (h₀ i : ℂ) - φr (x, i)) + fun i => h'' x i) +
        fun i => φr (x, i) - φc (x, i))
      ≤ ν * ℓ ^ 2 * (vn (fun i => (h₀ i : ℂ) - φr (x, i)) + vn (fun i => h'' x i) +
          vn (fun i => φr (x, i) - φc (x, i))) := mul_le_mul_of_nonneg_left hsum' hνℓ0
    _ ≤ 3 * ε := by nlinarith

end Domain

section Hyp

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν ε : ℝ}

/-- The strict hypotheses (`StrictData`) from the non-strict ones of `Prop51Hyp` with strictly
larger parameters, when `|φ₀| < 3/2` on `Ω₁`. -/
theorem strictData_of_prop51Hyp {α₀ : G.Ω 1 → ℂ} {φ₀ δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {f₁ : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ δ₀' δ₁' : ℝ} (H : Prop51Hyp G a ν α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (h0 : δ₀ < δ₀') (h1 : δ₁ < δ₁') (hphi : ∀ x ∈ G.Ω 1, vn (φ₀ x) < 3 / 2) :
    StrictData G N δ₀' δ₁' (φ₀, α₀, δΨ, f₁) := by
  have hsp : ∀ x : Torus d (N₀ * L ^ k), 0 < G.spacing x := fun x => spacing_pos G
  refine ⟨fun x μ => ⟨?_, ?_⟩, fun x => ?_, fun x => hphi x x.2,
    fun x => (H.alpha0 x).trans_lt h0, fun x i => (H.f₁_bd x i).trans_lt h1,
    fun x => (H.dPsi x x.2).trans_lt h1, fun x => (H.g0 x).trans_lt h1,
    fun x => (H.gl x).trans_lt h1⟩
  · exact (H.smooth.grad x x.2 μ).1.trans_lt (div_lt_div_of_pos_right h0 (hsp x))
  · exact (H.smooth.grad x x.2 μ).2.trans_lt (div_lt_div_of_pos_right h0 (hsp x))
  · exact (H.smooth.lap x x.2).trans_lt (div_lt_div_of_pos_right h0 (by have := hsp x; positivity))

/-- **The `Ξ`-domain instantiation of Proposition 5.1** (FLUCTUATION.md §3.6, Lemma 3.5 (ii)),
for a bound `c_m` on the mass factor `ν ℓ² |h - φ|` and the scale `ε_ζ` of `ζ = ε_ζ ξ₁`: the data
`(φ̄, α + (ν_u - ν), ζ ψ, (ν_u - ν)(h - φ))` satisfy (P1)–(P4) with
`δ₀ = K₁ C₁ ε + 3 |ξ|_∞`, `δ₁ = ((3/2) ε_ζ + (32/15) c_m) |ξ|_∞`, and `|φ̄| < 3/2` on `Ω₁`. -/
theorem prop51Hyp_xi_aux (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {D : BgData G N} (hD : XiCOne G a ν ε D) {εζ cm : ℝ} (hεζ : 0 ≤ εζ) (hcm : 0 ≤ cm)
    (hm : ∀ x : G.Ω 1, ν * G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
      vn (fun i => D.h x i - bgFieldC G a ν (bgC0 d L N) D (x, i)) ≤ cm)
    {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ ≤ 1 / 16)
    (hK : bgK1 d L N * (xiC1 d * ε) + 3 * ‖ξ‖ ≤ deltaStar d L N)
    (hζ : (3 / 2 * εζ + 32 / 15 * cm) * ‖ξ‖ ≤ deltaStar d L N) :
    Prop51Hyp G a ν (bgMultC G a ν (bgC0 d L N) D + fun _ => renMassU ν ξ - ν)
      (barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D)) (fun x i => renZeta εζ ξ * D.Ψ x i)
      (renF1 ν ξ D.h (bgFieldC G a ν (bgC0 d L N) D))
      (bgK1 d L N * (xiC1 d * ε) + 3 * ‖ξ‖) ((3 / 2 * εζ + 32 / 15 * cm) * ‖ξ‖) ∧
    ∀ x ∈ G.Ω 1, vn (barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D) x) < 3 / 2 := by
  have hd0 : 0 < d := by have := H.hd; omega
  set δ := xiC1 d * ε with hδdef
  have hδ0 : 0 < δ := by have := one_le_xiC1 d; positivity
  obtain ⟨-, hs, hb1, ⟨W⟩⟩ := hD.bg H hsm hε hc1
  have hδc0 : δ ≤ bgC0 d L N := hc1.trans (bgC1_le_bgC0 d L N hd0)
  obtain ⟨hδa, -, -, hKc⟩ := bgC1_facts d L N hd0 hc1
  have hδ1024 : δ ≤ 1 / 1024 := (approxDelta_le d L hδa).1
  have hK1 := bgK1_pos d L N
  have hξ0 := norm_nonneg ξ
  have hK' : bgK1 d L N * δ ≤ deltaStar d L N := le_trans (by linarith) hK
  set φc := bgFieldC G a ν (bgC0 d L N) D
  set α := bgMultC G a ν (bgC0 d L N) D
  set δ₁ := (3 / 2 * εζ + 32 / 15 * cm) * ‖ξ‖ with hδ₁def
  have hδ₁0 : 0 ≤ δ₁ := by positivity
  have hvΨ : ∀ x ∈ dataSites G, vn (D.Ψ x) ≤ 1 + 3 * δ := fun x hx =>
    (W.vn_le hδ0 hx).trans (by linarith)
  have hdΨ : ∀ x ∈ dataSites G, vn (fun i => renZeta εζ ξ * D.Ψ x i) ≤ δ₁ := by
    intro x hx
    rw [vn_smul_complex]
    have hz := norm_renZeta_le hεζ ξ
    have h32 : vn (D.Ψ x) ≤ 3 / 2 := (hvΨ x hx).trans (by linarith)
    calc ‖renZeta εζ ξ‖ * vn (D.Ψ x) ≤ (εζ * ‖ξ‖) * (3 / 2) :=
          mul_le_mul hz h32 (vn_nonneg _) (by positivity)
      _ ≤ δ₁ := by
          rw [hδ₁def]
          have : 0 ≤ 32 / 15 * cm * ‖ξ‖ := by positivity
          nlinarith
  have hP0 := prop51Hyp_of_bgBounds H hδ0 hc1 W hδc0 hs.1.2 hb1 hK' hδ₁0 hζ hdΨ
  have hphi : ∀ x ∈ G.Ω 1, vn (barField G D.Ψ φc x) < 3 / 2 := by
    intro x hx
    have hbar : barField G D.Ψ φc x = fun i => φc (⟨x, hx⟩, i) := by
      funext i; simp [barField, hx]
    rw [hbar]
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    have h1 := hb1.val ⟨x, hx⟩
    have h2 := hvΨ x hxd
    have h3 := vn_le_sub_add (fun i => φc (⟨x, hx⟩, i)) (D.Ψ x)
    have h0 := bgC0_le d L N
    linarith
  have hν0 := H.mass
  have hmass : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖renMassU ν ξ - ν‖ ≤
      32 / 15 * ‖ξ‖ * (ν * G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2) := by
    intro x
    have h := renMassU_sub_norm_le hν0 hξ
    have hsp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
      have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k))); positivity
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖renMassU ν ξ - ν‖
        ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (32 / 15 * ν * ‖ξ‖) :=
          mul_le_mul_of_nonneg_left h hsp
      _ = 32 / 15 * ‖ξ‖ * (ν * G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2) := by ring
  have hνℓ : ∀ x : G.Ω 1, ν * G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 ≤ 1 := by
    intro x
    have hsp := spacing_pos G (x := (x : Torus d (N₀ * L ^ k)))
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsp.le (spacing_le G x.2) 2) hν0).trans
      H.massLe
  refine ⟨⟨hP0.green, by positivity, hδ₁0, hK, hζ,
    isSmoothField_mono hP0.smooth (by linarith), hP0.phiBd, fun x => ?_, fun x i => ?_,
    hP0.dPsi, hP0.g0, hP0.gl⟩, hphi⟩
  · -- the shifted multiplier
    have h1 := hb1.alpha x
    have h2 := hmass x
    have h3 := hνℓ x
    have hsp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
      have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k))); positivity
    simp only [Pi.add_apply]
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α x + (renMassU ν ξ - ν)‖
        ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (‖α x‖ + ‖renMassU ν ξ - ν‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hsp
      _ ≤ bgK1 d L N * δ + 32 / 15 * ‖ξ‖ * 1 := by
          rw [mul_add]
          exact add_le_add h1 (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity)))
      _ ≤ bgK1 d L N * δ + 3 * ‖ξ‖ := by linarith
  · -- the source `f₁`
    have h2 := hmass x
    have hm' := hm x
    have hsp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
      have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k))); positivity
    have hvi : ‖D.h x i - φc (x, i)‖ ≤ vn (fun i => D.h x i - φc (x, i)) :=
      norm_le_vn (fun i => D.h x i - φc (x, i)) i
    simp only [renF1, norm_mul]
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (‖renMassU ν ξ - ν‖ * ‖D.h x i - φc (x, i)‖)
        = (G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖renMassU ν ξ - ν‖) *
            ‖D.h x i - φc (x, i)‖ := by ring
      _ ≤ (32 / 15 * ‖ξ‖ * (ν * G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2)) *
            vn (fun i => D.h x i - φc (x, i)) :=
          mul_le_mul h2 hvi (norm_nonneg _) (by have := hνℓ x; positivity)
      _ = 32 / 15 * ‖ξ‖ * (ν * G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
            vn (fun i => D.h x i - φc (x, i))) := by ring
      _ ≤ 32 / 15 * ‖ξ‖ * cm := mul_le_mul_of_nonneg_left hm' (by positivity)
      _ ≤ δ₁ := by
          rw [hδ₁def]
          have : 0 ≤ 3 / 2 * εζ * ‖ξ‖ := by positivity
          nlinarith

/-- **The `Ξ_{k+1}`-domain instantiation of Proposition 5.1, complete convention**
(FLUCTUATION.md §3.6, Lemma 3.5 (ii)): for `ψ ∈ Ξ^c_{k+1}(1, ε)` and `|ξ|_∞ ≤ 1/16`, the data
`(φ̄, α + (ν_u - ν), ζ ψ, (ν_u - ν)(h - φ))` of the perturbed system at the reference mass `ν`
satisfy (P1)–(P4) with `δ₀ = K₁ C₁ ε + 3 |ξ|_∞` and `δ₁ = 8 ε |ξ|_∞`. -/
theorem prop51Hyp_xi (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {D : BgData G N} (hD : XiCOne G a ν ε D) {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ ≤ 1 / 16)
    (hK : bgK1 d L N * (xiC1 d * ε) + 3 * ‖ξ‖ ≤ deltaStar d L N)
    (hζ : 8 * ε * ‖ξ‖ ≤ deltaStar d L N) :
    Prop51Hyp G a ν (bgMultC G a ν (bgC0 d L N) D + fun _ => renMassU ν ξ - ν)
      (barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D)) (fun x i => renZeta ε ξ * D.Ψ x i)
      (renF1 ν ξ D.h (bgFieldC G a ν (bgC0 d L N) D))
      (bgK1 d L N * (xiC1 d * ε) + 3 * ‖ξ‖) (8 * ε * ‖ξ‖) := by
  have hξ0 := norm_nonneg ξ
  have hle : (3 / 2 * ε + 32 / 15 * (3 * ε)) * ‖ξ‖ ≤ 8 * ε * ‖ξ‖ := by nlinarith
  have hP := (prop51Hyp_xi_aux H hε hsm hc1 hD hε.le (by linarith) (hD.mass_le H) hξ hK
    (hle.trans hζ)).1
  exact { hP with
    δ₁_nn := by positivity
    δ₁_le := hζ
    f₁_bd := fun x i => (hP.f₁_bd x i).trans hle
    dPsi := fun x hx => (hP.dPsi x hx).trans hle
    g0 := fun x => (hP.g0 x).trans hle
    gl := fun x => (hP.gl x).trans hle }

/-- **The `Ξ_{k+1}`-domain instantiation of Proposition 5.1, `ν`-free convention**: mass `0` in the
variational problems, `f₁ = 0`, `δ₀ = K₁ C₁ ε + 3 |ξ|_∞`, `δ₁ = (3/2) ε |ξ|_∞`. -/
theorem prop51Hyp_xi_nuFree (H : BgHyp d L k ϱ a 0) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {D : BgData G N} (hD : XiCOne G a 0 ε D) {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ ≤ 1 / 16)
    (hK : bgK1 d L N * (xiC1 d * ε) + 3 * ‖ξ‖ ≤ deltaStar d L N)
    (hζ : 3 / 2 * ε * ‖ξ‖ ≤ deltaStar d L N) :
    Prop51Hyp G a 0 (bgMultC G a 0 (bgC0 d L N) D) (barField G D.Ψ (bgFieldC G a 0 (bgC0 d L N) D))
      (fun x i => renZeta ε ξ * D.Ψ x i) 0
      (bgK1 d L N * (xiC1 d * ε) + 3 * ‖ξ‖) (3 / 2 * ε * ‖ξ‖) := by
  have e : (3 / 2 * ε + 32 / 15 * (0 : ℝ)) * ‖ξ‖ = 3 / 2 * ε * ‖ξ‖ := by ring
  have hP := (prop51Hyp_xi_aux H hε hsm hc1 hD hε.le le_rfl (fun x => by simp) hξ hK
    (by rw [e]; exact hζ)).1
  rw [e] at hP
  have eα : (bgMultC G a 0 (bgC0 d L N) D + fun _ => renMassU 0 ξ - ((0 : ℝ) : ℂ)) =
      bgMultC G a 0 (bgC0 d L N) D := by
    funext x; simp [renMassU_zero]
  rw [eα, renF1_zero] at hP
  exact hP

end Hyp

section Analytic

variable (G : GeneratingSet d L N₀ k ϱ)

/-- The data of the perturbed system as a function of `((Ψ, h̃), ξ)`, for a background map
`F_bg : (Ψ, h̃) ↦ (φ, α)`: `((φ̄, α, ζ Ψ, (ν_u - ν)(h̃ - φ)), ν_u)`. -/
noncomputable def renRaw (ν ε : ℝ)
    (Fbg : RawData d L N₀ k N → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ))
    (q : RawData d L N₀ k N × (Fin 3 → ℂ)) : Edat G N × ℂ :=
  ((barField G q.1.1 (Fbg q.1).1, (Fbg q.1).2, fun x i => renZeta ε q.2 * q.1.1 x i,
    renF1 ν q.2 q.1.2 (Fbg q.1).1), renMassU ν q.2)

variable {G}

theorem analyticAt_renRaw (ν ε : ℝ)
    {Fbg : RawData d L N₀ k N → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}
    {q : RawData d L N₀ k N × (Fin 3 → ℂ)} (hF : AnalyticAt ℂ Fbg q.1) (hq : 1 + q.2 2 ≠ 0) :
    AnalyticAt ℂ (renRaw G ν ε Fbg) q := by
  have hFq : AnalyticAt ℂ (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => Fbg q'.1) q :=
    hF.comp (aa_fst' q)
  have hφ : ∀ (y : G.Ω 1) (i : Fin N),
      AnalyticAt ℂ (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => (Fbg q'.1).1 (y, i)) q :=
    fun y i => (aa_eval' (y, i) _).comp ((aa_fst' _).comp hFq)
  have hα : AnalyticAt ℂ (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => (Fbg q'.1).2) q :=
    (aa_snd' _).comp hFq
  have hΨ : ∀ (x : Torus d (N₀ * L ^ k)) (i : Fin N),
      AnalyticAt ℂ (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => q'.1.1 x i) q :=
    fun x i => by fun_prop
  have hhh : ∀ (x : Torus d (N₀ * L ^ k)) (i : Fin N),
      AnalyticAt ℂ (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => q'.1.2 x i) q :=
    fun x i => by fun_prop
  have hξ : ∀ j : Fin 3, AnalyticAt ℂ (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => q'.2 j) q :=
    fun j => by fun_prop
  have hm : AnalyticAt ℂ (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => renMassU ν q'.2) q := by
    unfold renMassU
    exact (analyticAt_const.mul (analyticAt_const.add (hξ 1))).div
      (analyticAt_const.add (hξ 2)) hq
  have hz : AnalyticAt ℂ (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) => renZeta ε q'.2) q := by
    unfold renZeta
    exact analyticAt_const.mul (hξ 0)
  unfold renRaw
  refine AnalyticAt.prod (AnalyticAt.prod ?_ (AnalyticAt.prod hα (AnalyticAt.prod ?_ ?_))) hm
  · refine analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_
    by_cases hx : x ∈ G.Ω 1
    · have e : (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) =>
          barField G q'.1.1 (Fbg q'.1).1 x i) = fun q' => (Fbg q'.1).1 (⟨x, hx⟩, i) := by
        funext q'; simp [barField, hx]
      rw [e]; exact hφ _ i
    · have e : (fun q' : RawData d L N₀ k N × (Fin 3 → ℂ) =>
          barField G q'.1.1 (Fbg q'.1).1 x i) = fun q' => q'.1.1 x i := by
        funext q'; simp [barField, hx]
      rw [e]; exact hΨ x i
  · exact analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => hz.mul (hΨ x i)
  · refine analyticAt_pi_iff.2 fun p => ?_
    unfold renF1
    exact (hm.sub analyticAt_const).mul ((hhh _ _).sub (hφ p.1 p.2))

variable (G)

/-- **The solution map of Lemma 3.5 (ii)** and its properties: `F ((Ψ, h̃), ξ) = (δφ, δα)` is
complex-analytic jointly in `(Ψ, h̃, ξ)` on `Ξ^c_k(𝔹; 1, ε) × {|ξ|_∞ < r}`, solves the perturbed
system with base `(φ̄, α) = (bgFieldC, bgMultC)` of `(Ψ, h̃)`, mass `ν_u`, lifted datum `ζ Ψ`
(`ζ = ε_ζ ξ₁`; the source has `ε_ζ = ε = ε_{k+1}`) and `f₁ = (ν_u - ν)(h̃ - φ)`, is unique in
`|δα|₂ ≤ c₆`, and `‖δφ‖_*, |δα|₂ ≤ K₂ B |ξ|_∞`. -/
structure IsRenSol (a : ℕ → ℝ) (ν εζ ε r B : ℝ)
    (F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) : Prop where
  analytic : AnalyticOnNhd ℂ F (renDom G a ν ε r)
  solves : ∀ D : BgData G N, XiCOne G a ν ε D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
    IsPerturbedM G a (renMassU ν ξ) (bgMultC G a ν (bgC0 d L N) D)
      (barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D))
      (pertSource G a (fun x i => renZeta εζ ξ * D.Ψ x i)
        (renF1 ν ξ D.h (bgFieldC G a ν (bgC0 d L N) D)))
      (F ((D.Ψ, D.h), ξ)).1 (F ((D.Ψ, D.h), ξ)).2
  small : ∀ D : BgData G N, XiCOne G a ν ε D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
    Small G (F ((D.Ψ, D.h), ξ)).2 (cK2 d L N * (B * ‖ξ‖))
  sup : ∀ D : BgData G N, XiCOne G a ν ε D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
    SupBounds G (F ((D.Ψ, D.h), ξ)).1 (cK2 d L N * (B * ‖ξ‖))
  unique : ∀ D : BgData G N, XiCOne G a ν ε D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
    ∀ (δφ' : G.Ω 1 × Fin N → ℂ) (δα' : G.Ω 1 → ℂ),
      IsPerturbedM G a (renMassU ν ξ) (bgMultC G a ν (bgC0 d L N) D)
        (barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D))
        (pertSource G a (fun x i => renZeta εζ ξ * D.Ψ x i)
          (renF1 ν ξ D.h (bgFieldC G a ν (bgC0 d L N) D))) δφ' δα' →
      Small G δα' (c6 d L N) → δφ' = (F ((D.Ψ, D.h), ξ)).1 ∧ δα' = (F ((D.Ψ, D.h), ξ)).2

variable {G}

/-- The construction of the solution map, for a bound `c_m` on the mass factor, the scale `ε_ζ`
of `ζ`, and a constant `B ≥ (3/2) ε_ζ + (32/15) c_m` (common to both conventions). -/
theorem exists_isRenSol_aux {a : ℕ → ℝ} {ν εζ ε r : ℝ} (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hεζ : 0 ≤ εζ) (hr : r ≤ 1 / 16) (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (hc1 : xiC1 d * ε ≤ bgC1 d L N) {cm B : ℝ} (hcm : 0 ≤ cm)
    (hm : ∀ D : BgData G N, XiCOne G a ν ε D → ∀ x : G.Ω 1,
      ν * G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        vn (fun i => D.h x i - bgFieldC G a ν (bgC0 d L N) D (x, i)) ≤ cm)
    (hB : 3 / 2 * εζ + 32 / 15 * cm ≤ B) (hB0 : 0 < B)
    (hK : bgK1 d L N * (xiC1 d * ε) + 3 * r ≤ deltaStar d L N)
    (hζ : B * r ≤ deltaStar d L N) :
    ∃ F, IsRenSol (N := N) G a ν εζ ε r B F := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨Fbg, hFan, hFeq⟩ := theorem72_analytic (G := G) (a := a) (ν := ν) (N := N) H
  have hδs := deltaStar_pos d L N hd0
  obtain ⟨sol, hsan, hsol⟩ := prop51_mass_analytic (N := N) hd0 (H.green (G := G)) hδs.le hδs.le
    le_rfl le_rfl
  -- the data at a point of the domain
  have hR : ∀ D : BgData G N, XiCOne G a ν ε D → ∀ ξ : Fin 3 → ℂ,
      renRaw G ν εζ Fbg ((D.Ψ, D.h), ξ) =
        ((barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D), bgMultC G a ν (bgC0 d L N) D,
          fun x i => renZeta εζ ξ * D.Ψ x i, renF1 ν ξ D.h (bgFieldC G a ν (bgC0 d L N) D)),
          renMassU ν ξ) := by
    intro D hD ξ
    have hDU := (hD.bg H hsm hε hc1).1
    simp only [renRaw, hFeq D hDU]
  -- the hypotheses of Proposition 5.1 at a point, with the point bound
  have hyp : ∀ D : BgData G N, XiCOne G a ν ε D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
      Prop51Hyp G a ν (bgMultC G a ν (bgC0 d L N) D + fun _ => renMassU ν ξ - ν)
        (barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D)) (fun x i => renZeta εζ ξ * D.Ψ x i)
        (renF1 ν ξ D.h (bgFieldC G a ν (bgC0 d L N) D))
        (bgK1 d L N * (xiC1 d * ε) + 3 * ‖ξ‖) (B * ‖ξ‖) ∧
      StrictData G N (deltaStar d L N) (deltaStar d L N)
        (massShift G N ν (renRaw G ν εζ Fbg ((D.Ψ, D.h), ξ))) := by
    intro D hD ξ hξ
    have hξ0 := norm_nonneg ξ
    have hle : (3 / 2 * εζ + 32 / 15 * cm) * ‖ξ‖ ≤ B * ‖ξ‖ :=
      mul_le_mul_of_nonneg_right hB hξ0
    obtain ⟨hP, hphi⟩ := prop51Hyp_xi_aux H hε hsm hc1 hD hεζ hcm (hm D hD) (hξ.le.trans hr)
      (by linarith) (hle.trans ((mul_le_mul_of_nonneg_left hξ.le hB0.le).trans hζ))
    have hP' : Prop51Hyp G a ν (bgMultC G a ν (bgC0 d L N) D + fun _ => renMassU ν ξ - ν)
        (barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D)) (fun x i => renZeta εζ ξ * D.Ψ x i)
        (renF1 ν ξ D.h (bgFieldC G a ν (bgC0 d L N) D))
        (bgK1 d L N * (xiC1 d * ε) + 3 * ‖ξ‖) (B * ‖ξ‖) :=
      { hP with
        δ₁_nn := by positivity
        δ₁_le := (mul_le_mul_of_nonneg_left hξ.le hB0.le).trans hζ
        f₁_bd := fun x i => (hP.f₁_bd x i).trans hle
        dPsi := fun x hx => (hP.dPsi x hx).trans hle
        g0 := fun x => (hP.g0 x).trans hle
        gl := fun x => (hP.gl x).trans hle }
    refine ⟨hP', ?_⟩
    rw [hR D hD ξ]
    exact strictData_of_prop51Hyp hP' (by linarith)
      (lt_of_lt_of_le (mul_lt_mul_of_pos_left hξ hB0) hζ) hphi
  refine ⟨fun q => sol (renRaw G ν εζ Fbg q), ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro q ⟨D, hD, hq1, hq2⟩
    have hDU := (hD.bg H hsm hε hc1).1
    have hFa : AnalyticAt ℂ Fbg q.1 := hFan _ ⟨D, hDU, hq1⟩
    have hne : 1 + q.2 2 ≠ 0 := one_add_ne_zero_of_norm (by linarith) 2
    have hS : StrictData G N (deltaStar d L N) (deltaStar d L N)
        (massShift G N ν (renRaw G ν εζ Fbg q)) := by
      have e : q = ((D.Ψ, D.h), q.2) := Prod.ext hq1 rfl
      rw [e]; exact (hyp D hD q.2 hq2).2
    exact (hsan _ hS).comp (analyticAt_renRaw ν εζ hFa hne)
  all_goals intro D hD ξ hξ
  all_goals obtain ⟨hP, hS⟩ := hyp D hD ξ hξ
  all_goals obtain ⟨hPs, -, -, hc6, hu⟩ := hsol _ hS
  all_goals rw [hR D hD ξ] at hPs hc6 hu ⊢
  all_goals obtain ⟨δφ, δα, hPp, hsp, hsupp, hup⟩ := prop51_mass_exists_unique hd0 hP
  all_goals obtain ⟨e1, e2⟩ := hup _ _ hPs hc6
  · exact hPs
  · rw [e2]; exact hsp
  · rw [e1]; exact hsupp
  · exact hu

/-- **Lemma 3.5 (ii), analyticity and bound, complete convention** (FLUCTUATION.md §3.6; P4
(4.10)–(4.11)).  For `ψ ∈ Ξ^c_{k+1}(1, ε)` and `ξ` in the polydisc `|ξ|_∞ < r ≤ 1/16`, with
`K₁ C₁ ε + 3 r ≤ δ_*` and `8 ε r ≤ δ_*`, the solution `(δφ, δα)` of the perturbed system at the
mass `ν_u = ν (1 + ξ₂)/(1 + ξ₃)` with `δΨ = ε ξ₁ ψ`, `f₁ = (ν_u - ν)(h - φ)` is one
complex-analytic function of `(ψ, h, ξ)`, with `‖δφ‖_*, |δα|₂ ≤ 8 K₂ ε |ξ|_∞`. -/
theorem exists_isRenSol {a : ℕ → ℝ} {ν ε r : ℝ} (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hr : r ≤ 1 / 16) (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    (hK : bgK1 d L N * (xiC1 d * ε) + 3 * r ≤ deltaStar d L N)
    (hζ : 8 * ε * r ≤ deltaStar d L N) :
    ∃ F, IsRenSol (N := N) G a ν ε ε r (8 * ε) F :=
  exists_isRenSol_aux H hε hε.le hr hsm hc1 (cm := 3 * ε) (by linarith)
    (fun D hD x => hD.mass_le H x) (by linarith) (by linarith) hK hζ

/-- **Lemma 3.5 (ii), analyticity and bound, `ν`-free convention**: mass `0` in the variational
problems and `f₁ = 0`; `‖δφ‖_*, |δα|₂ ≤ (3/2) K₂ ε |ξ|_∞`. -/
theorem exists_isRenSol_nuFree {a : ℕ → ℝ} {ε r : ℝ} (H : BgHyp d L k ϱ a 0) (hε : 0 < ε)
    (hr : r ≤ 1 / 16) (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1)
    (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    (hK : bgK1 d L N * (xiC1 d * ε) + 3 * r ≤ deltaStar d L N)
    (hζ : 3 / 2 * ε * r ≤ deltaStar d L N) :
    ∃ F, IsRenSol (N := N) G a 0 ε ε r (3 / 2 * ε) F :=
  exists_isRenSol_aux H hε hε.le hr hsm hc1 (cm := 0) le_rfl (fun D _ x => by simp)
    (by linarith) (by positivity) hK hζ

/-- **Inhabitation of `IsRenSol` for admissible parameters** (hard rule 10): for every generating
set and mass with the hypotheses of Theorem 5.2 there are `ε, r > 0` and a solution map. -/
theorem exists_isRenSol_params {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) :
    ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧ ∃ F, IsRenSol (N := N) G a ν ε ε r (8 * ε) F := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hδs := deltaStar_pos d L N hd0
  have hc1p : 0 < bgC1 d L N := by
    have h0 := bgC0_pos d L N hd0
    have hK := bgK1_pos d L N
    have hC := lemma53Const_pos d L
    have ha : 0 < approxDelta d L := approxDelta_pos d L
    unfold bgC1; positivity
  have hX := one_le_xiC1 d
  have hK1 := bgK1_pos d L N
  set c : ℝ := (4 * d + 6) * (2 * d + 1) with hc
  have hcp : 1 ≤ c := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [hc]; nlinarith
  -- choose `ε` small for all smallness conditions, then `r`
  set ε := min (1 / c) (min (bgC1 d L N / xiC1 d) (deltaStar d L N / (2 * bgK1 d L N * xiC1 d)))
    with hεdef
  have hεp : 0 < ε := by
    rw [hεdef]; refine lt_min (by positivity) (lt_min (by positivity) (by positivity))
  set r := min (1 / 16) (min (deltaStar d L N / 6) (deltaStar d L N / (8 * ε))) with hrdef
  have hrp : 0 < r := by
    rw [hrdef]; refine lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  refine ⟨ε, r, hεp, hrp, exists_isRenSol H hεp (min_le_left _ _) ?_ ?_ ?_ ?_⟩
  · have h1 : ε ≤ 1 / c := min_le_left _ _
    have : (4 * (d : ℝ) + 6) * ((2 * d + 1) * ε) = c * ε := by rw [hc]; ring
    rw [this]
    calc c * ε ≤ c * (1 / c) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 1 := by field_simp
  · have h1 : ε ≤ bgC1 d L N / xiC1 d := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by linarith)] at h1
    linarith
  · have h1 : ε ≤ deltaStar d L N / (2 * bgK1 d L N * xiC1 d) :=
      (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : r ≤ deltaStar d L N / 6 := (min_le_right _ _).trans (min_le_left _ _)
    nlinarith
  · have h2 : r ≤ deltaStar d L N / (8 * ε) := (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h2
    linarith

end Analytic

section Consequences

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν εζ ε r B : ℝ}
  {F : RawData d L N₀ k N × (Fin 3 → ℂ) → (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)}

/-- **Lemma 3.5 (ii): `(δφ, δα)` vanishes at `ξ = 0`.** -/
theorem IsRenSol.eq_zero (hF : IsRenSol G a ν εζ ε r B F) (hr : 0 < r) {D : BgData G N}
    (hD : XiCOne G a ν ε D) : F ((D.Ψ, D.h), 0) = 0 := by
  have h0 : ‖(0 : Fin 3 → ℂ)‖ < r := by simpa using hr
  have hs := hF.small D hD 0 h0
  have hsup := hF.sup D hD 0 h0
  simp only [norm_zero, mul_zero] at hs hsup
  refine Prod.ext ?_ ?_
  · funext p
    have := hsup.val (p.1 : Torus d (N₀ * L ^ k)) p.2
    rw [svec_of_mem] at this
    simpa using norm_le_zero_iff.1 this
  · funext x
    have h := hs x
    have hsp : 0 < G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
      have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k))); positivity
    have : ‖(F ((D.Ψ, D.h), 0)).2 x‖ ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos hsp hc
      linarith
    simpa using norm_le_zero_iff.1 this

/-- **Lemma 3.5 (ii), identification for real `ξ`**: for `ξ = t` real with `|t|_∞ < r`, and
`(φ_u, α_u)` a small solution (`|α_u|₂ < c₀`, `2 c₀ ≤ c₆`) of (EL) for the unrenormalized datum
`((1 + ε_ζ t₁) ψ, h)` at the mass `ν_u = ν (1 + t₂)/(1 + t₃)`, the solution map is
`F = (φ_u - φ, α_u - α)` with `(φ, α) = (bgFieldC, bgMultC)` of `(ψ, h)` at the mass `ν`. -/
theorem IsRenSol.eq_bg (hF : IsRenSol G a ν εζ ε r B F) (H : BgHyp d L k ϱ a ν) (hε : 0 < ε)
    (hsm : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc1 : xiC1 d * ε ≤ bgC1 d L N)
    {D Du : BgData G N} (hD : XiCOne G a ν ε D) {t : Fin 3 → ℝ}
    (ht : ‖(fun i => (t i : ℂ))‖ < r)
    (hΨ : ∀ x i, Du.Ψ x i = (1 + ((εζ * t 0 : ℝ) : ℂ)) * D.Ψ x i)
    (hh : ∀ x i, Du.h x i = D.h x i)
    {c₀ : ℝ} (hc₀ : 2 * c₀ ≤ c6 d L N) {φu : G.Ω 1 × Fin N → ℂ} {αu : G.Ω 1 → ℂ}
    (hφu : IsSmallSolution G a (ν * (1 + t 1) / (1 + t 2)) c₀ Du φu αu) :
    F ((D.Ψ, D.h), fun i => (t i : ℂ)) =
      (φu - bgFieldC G a ν (bgC0 d L N) D, αu - bgMultC G a ν (bgC0 d L N) D) := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨-, hs, hb, -⟩ := hD.bg H hsm hε hc1
  set φ := bgFieldC G a ν (bgC0 d L N) D
  set α := bgMultC G a ν (bgC0 d L N) D
  have hP := lemma35_ii_perturbed a (μ := ν) (μu := ν * (1 + t 1) / (1 + t 2)) (ζ := εζ * t 0)
    hΨ hh hs.1 hφu.1
  have hPM : IsPerturbedM G a (renMassU ν fun i => (t i : ℂ)) α
      (barField G D.Ψ φ)
      (pertSource G a (fun x i => renZeta εζ (fun i => (t i : ℂ)) * D.Ψ x i)
        (renF1 ν (fun i => (t i : ℂ)) D.h φ)) (φu - φ) (αu - α) := by
    rw [renMassU_ofReal, renZeta_ofReal]
    have ef : renF1 (G := G) ν (fun i => (t i : ℂ)) D.h φ =
        fun p => (((ν * (1 + t 1) / (1 + t 2)) - ν : ℝ) : ℂ) * (D.h p.1 p.2 - φ p) := by
      funext p; simp only [renF1, renMassU_ofReal]; push_cast; ring
    rw [ef, isPerturbedM_congr_base G a _ α (φ₀' := svec G φ)
      (fun x i => by simp [barField, svec_of_mem]), isPerturbedM_ofReal]
    exact hP
  have hsmall : Small G (αu - α) (c6 d L N) := by
    intro x
    have h1 := (hφu.2 x).le
    have h2 := hb.alpha x
    obtain ⟨-, -, -, hKc⟩ := bgC1_facts d L N hd0 hc1
    have hc0 : bgC0 d L N ≤ c6 d L N := bgC0_le_c6 d L N
    have hsp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
      have := spacing_pos G (x := (x : Torus d (N₀ * L ^ k))); positivity
    simp only [Pi.sub_apply]
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖αu x - α x‖
        ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (‖αu x‖ + ‖α x‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) hsp
      _ ≤ c6 d L N := by rw [mul_add]; linarith
  obtain ⟨e1, e2⟩ := hF.unique D hD _ ht _ _ hPM hsmall
  exact Prod.ext e1.symm e2.symm

end Consequences

end Balaban.Fluctuation
