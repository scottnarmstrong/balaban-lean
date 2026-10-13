/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormExpBounds
public import Balaban.Localization.Decoupled2Background
public import Balaban.Localization.I5Chain
public import Balaban.SmallField.FinalCutoff
public import Balaban.Fluctuation.InteractionEngine
public import Balaban.Localization.I5FluctFacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The decoupled background lies in the class `bgClass`, for every complex cut parameter

Toward the first localization principle `locC1` of `RenormExpInput`.  **`locC1` itself is NOT
proved here**; this file proves the class-membership input only.  It uses no zero class and is
independent of the choice of the generator.

**What `φ ∈ bgClass G ν c D` requires** (`RenormExpBounds.lean`, `bgClass`).  For every site
`x ∈ Ω₁`, with `ℓ(x)` the spacing, `Q` the block average and `φ̄` the extension of `φ` by `Ψ`:
(1) `|Ψ(x) - (Qφ)(x)| ≤ c`; (2) the forward and backward differences of `φ̄` in each direction
have norm at most `c / ℓ(x)`; (3) `ν ℓ(x)² |φ(x) - h(x)|² ≤ c²`.

**What the landed bounds give.**  `i4b_exists_unique` gives, for the decoupled background `φ_s`
(`|s_P| ≤ e^κ`) of a datum in the domain `Ψ̃^c(δ, δ)`, `δ = C₁ ε`, the bounds `BgBounds` with the
constant `K₄ δ`: `|φ_s - Ψ| ≤ K₄ δ` on `Ω₁` and `ℓ |∂φ̄_s| ≤ K₄ δ`.  At `s = 1` it is the true
background `bgFieldC` (`i4b_one`), which is in `bgClass G ν (2ε) D` (`XiCOneReal.mem_bgClass`).
Hence `|φ_s - φ_1| ≤ 2 K₄ δ` on `Ω₁`, and the triangle inequality gives (1) and (3) with
`2ε + 2 K₄ δ` (using that `Q` is linear with unit total weight and `ν ℓ² ≤ 1`), while (2) is
read off from `BgBounds.grad`.  So every class condition is covered; the constant is
`cK = 2 + 2 K₄ C₁`, `C₁ = xiC1 d`, depending only on `(d, L, N)` and the landed constants
`BG`, `κ`.  (No `bgK1` appears: `K₄` also bounds the `s = 1` field.)
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.FinalCutoff
  Balaban.Localization
  Finset Matrix

section Transfer

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {ν : ℝ}

/-- **Membership from nearness** to a field of the class: if `φ₁ ∈ bgClass G ν c₁ D`, `φ` is
within `r` of `φ₁` at every site of `Ω₁`, the gradient bound of `φ` holds with `c / ℓ`, and
`ν ℓ² ≤ 1`, then `φ ∈ bgClass G ν c D` for `c ≥ c₁ + r`. -/
theorem mem_bgClass_of_near (hν0 : 0 ≤ ν) (hνℓ : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    {D : BgData G N} {φ₁ φ : G.Ω 1 × Fin N → ℂ} {c₁ r c : ℝ}
    (hφ₁ : φ₁ ∈ bgClass G ν c₁ D) (hc : c₁ + r ≤ c)
    (hnear : ∀ x : G.Ω 1, vn (fun i => φ (x, i) - φ₁ (x, i)) ≤ r)
    (hgrad : ∀ x ∈ G.Ω 1, ∀ μ : Fin d,
      vn (fun i => barField G D.Ψ φ (x + Pi.single μ 1) i - barField G D.Ψ φ x i) ≤
        c / G.spacing x ∧
      vn (fun i => barField G D.Ψ φ (x - Pi.single μ 1) i - barField G D.Ψ φ x i) ≤
        c / G.spacing x) :
    φ ∈ bgClass G ν c D := by
  obtain ⟨h1, -, h3⟩ := hφ₁
  refine ⟨fun x hx => ?_, hgrad, fun x hx => ?_⟩
  · have hQ : vn (fun i => blockAvg G φ x i - blockAvg G φ₁ x i) ≤ r := by
      have e : (fun i => blockAvg G φ x i - blockAvg G φ₁ x i) =
          fun i => blockAvg G (φ - φ₁) x i - (0 : Fin N → ℂ) i := by
        funext i
        have := blockAvg_add (G := G) φ₁ (φ - φ₁) x i
        rw [add_sub_cancel] at this
        simp [this]
      rw [e]
      refine blockAvg_sub_const_le (φ - φ₁) 0 hx fun y hy _ => ?_
      simpa using hnear ⟨y, hy⟩
    have t := vn_triangle (D.Ψ x) (blockAvg G φ₁ x) (blockAvg G φ x)
    have t' : vn (fun i => D.Ψ x i - blockAvg G φ x i) ≤
        vn (fun i => D.Ψ x i - blockAvg G φ₁ x i) +
          vn (fun i => blockAvg G φ₁ x i - blockAvg G φ x i) := t
    have hs : vn (fun i => blockAvg G φ₁ x i - blockAvg G φ x i) =
        vn (fun i => blockAvg G φ x i - blockAvg G φ₁ x i) := vn_sub_comm _ _
    linarith [h1 x hx]
  · set ℓ := G.spacing x with hℓ
    have hℓ0 : 0 < ℓ := spacing_pos G
    have hℓk : ℓ ≤ (L : ℝ) ^ k := spacing_le G hx
    have hw1 : ν * ℓ ^ 2 ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hℓ0.le hℓk 2) hν0) hνℓ
    set w := Real.sqrt ν * ℓ with hw
    have hw2 : w ^ 2 = ν * ℓ ^ 2 := by
      rw [hw, mul_pow, Real.sq_sqrt hν0]
    have hw0 : 0 ≤ w := by positivity
    have hw1' : w ≤ 1 := by nlinarith
    have hA : w * vn (fun i => svec G φ₁ x i - D.h x i) ≤ c₁ := by
      have h3x := h3 x hx
      have hc0 : 0 ≤ c₁ := (vn_nonneg _).trans (h1 x hx)
      have : (w * vn (fun i => svec G φ₁ x i - D.h x i)) ^ 2 ≤ c₁ ^ 2 := by
        rw [mul_pow, hw2]; exact h3x
      exact (abs_le_of_sq_le_sq' this hc0).2
    have hB : w * vn (fun i => svec G φ x i - svec G φ₁ x i) ≤ r := by
      have hb : vn (fun i => svec G φ x i - svec G φ₁ x i) ≤ r := by
        have := hnear ⟨x, hx⟩
        have e1 : ∀ (ψ : G.Ω 1 × Fin N → ℂ) i, svec G ψ x i = ψ (⟨x, hx⟩, i) :=
          fun ψ i => svec_of_mem G ψ ⟨x, hx⟩ i
        simp only [e1]
        exact this
      calc _ ≤ 1 * r := mul_le_mul hw1' hb (vn_nonneg _) zero_le_one
        _ = r := one_mul r
    have t := vn_triangle (svec G φ x) (svec G φ₁ x) (D.h x)
    have t' : vn (fun i => svec G φ x i - D.h x i) ≤
        vn (fun i => svec G φ x i - svec G φ₁ x i) +
          vn (fun i => svec G φ₁ x i - D.h x i) := t
    have hX : w * vn (fun i => svec G φ x i - D.h x i) ≤ c := by
      nlinarith [mul_le_mul_of_nonneg_left t' hw0]
    have hX0 : 0 ≤ w * vn (fun i => svec G φ x i - D.h x i) :=
      mul_nonneg hw0 (vn_nonneg _)
    calc ν * ℓ ^ 2 * vn (fun i => svec G φ x i - D.h x i) ^ 2
        = (w * vn (fun i => svec G φ x i - D.h x i)) ^ 2 := by rw [mul_pow, hw2]
      _ ≤ c ^ 2 := pow_le_pow_left₀ hX0 hX 2

end Transfer

section Core

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {ν : ℝ}

/-- **The class bound from the two `BgBounds`.**  If `φ` and `φ₁` both satisfy `BgBounds` with
the constant `K₄ δ`, `δ = C₁ ε`, and `φ₁` is in `bgClass G ν (2ε) D`, then `φ` is in
`bgClass G ν ((2 + 2 K₄ C₁) ε) D`. -/
theorem mem_bgClass_of_bgBounds (hν0 : 0 ≤ ν) (hνℓ : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    {D : BgData G N} {φ φ₁ : G.Ω 1 × Fin N → ℂ} {α α₁ : G.Ω 1 → ℂ} {K₄ C₁ ε : ℝ}
    (hK : 0 ≤ K₄) (hC : 0 < C₁) (hε : 0 < ε)
    (hb : BgBounds G D φ α (K₄ * (C₁ * ε))) (hb1 : BgBounds G D φ₁ α₁ (K₄ * (C₁ * ε)))
    (hmem : φ₁ ∈ bgClass G ν (2 * ε) D) :
    φ ∈ bgClass G ν ((2 + 2 * K₄ * C₁) * ε) D := by
  have hKδ : 0 ≤ K₄ * (C₁ * ε) := by positivity
  refine mem_bgClass_of_near hν0 hνℓ (r := 2 * (K₄ * (C₁ * ε))) hmem
    (le_of_eq (by ring)) (fun x => ?_) (fun x hx μ => ?_)
  · have h1 := hb.val x
    have h2 := hb1.val x
    have t := vn_triangle (fun i => φ (x, i)) (D.Ψ x) (fun i => φ₁ (x, i))
    have t' : vn (fun i => φ (x, i) - φ₁ (x, i)) ≤
        vn (fun i => φ (x, i) - D.Ψ x i) + vn (fun i => D.Ψ x i - φ₁ (x, i)) := t
    have hs' : vn (fun i => D.Ψ x i - φ₁ (x, i)) = vn (fun i => φ₁ (x, i) - D.Ψ x i) :=
      vn_sub_comm _ _
    linarith
  · have hg := hb.grad ⟨x, hx⟩ μ
    have hsp : 0 < G.spacing x := spacing_pos G
    have hle : K₄ * (C₁ * ε) / G.spacing x ≤ (2 + 2 * K₄ * C₁) * ε / G.spacing x := by
      refine div_le_div_of_nonneg_right ?_ hsp.le
      nlinarith [mul_pos hC hε]
    exact ⟨hg.1.trans hle, hg.2.trans hle⟩

end Core

section Main

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
  {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
  {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **`renBgClass_dec`** (physical setting `FlCore`).  For a datum `D` of the fixed-`h` class
domain `Ξ^c(1, ε)` (`ε = eps`) and every complex cut-parameter vector `s` with `‖s_P‖ ≤ e^κ`,
the decoupled background field `decBgField` lies in `bgClass Gp ν (cK ε) D`, with
`cK = 2 + 2 K₄ C₁`, `C₁ = xiC1 d`, `K₄ = K4 d L N BG κ`. -/
theorem renBgClass_dec (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {D : BgData Gp N} (hD : XiCOneReal Gp (compWeight L a₁) ν eps D)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) :
    decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D ∈
      bgClass Gp ν ((2 + 2 * K4 d L N BG κ * xiC1 d) * eps) D := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hε := hC.eps_pos
  have hC1pos : 0 < xiC1 d := by unfold xiC1; positivity
  have hδ : 0 < xiC1 d * eps := mul_pos hC1pos hε
  have hδ7 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hc1 : xiC1 d * eps ≤ bgC1 d L N := hδ7.trans (c7_le_bgC1 d L N BG κ)
  have hδ0 : xiC1 d * eps ≤ bgC0 d L N := hc1.trans (bgC1_le_bgC0 d L N hd0)
  have hDom : InDomainC Gp ν (xiC1 d * eps) (xiC1 d * eps) D :=
    xiCData_inDomainC hC.HBp hC.small1 hD.xiCOne
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hsle := hs
  obtain ⟨φ, α, hid, huniq, -, -, hbd⟩ :=
    i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hsle hδ le_rfl hδ0 hδ7 hνε hDom
  obtain ⟨φ1, α1, hid1, -, -, -, hbd1⟩ :=
    i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM (s := fun _ => 1)
      (fun P => by simpa using Real.one_le_exp hC.hκ.le) hδ le_rfl hδ0 hδ7 hνε hDom
  have e1 := (decBg_eq hid huniq).1
  have e2 := (i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ le_rfl hδ0 hδ7 hνε hDom hid1).2.1
  have hmem := XiCOneReal.mem_bgClass hC.HBp hε hC.small1 hc1 hD
  rw [e2] at hmem
  rw [e1]
  exact mem_bgClass_of_bgBounds hC.HBp.mass hC.HBp.massLe
    (K4_pos hC.hS.fam.2.1 hd0).le hC1pos hε hbd hbd1 hmem

/-- **`renBgClass_dec2`**: the same for the cover version `Dec2.decBgField` of the decoupled
background (cover `C`, operator generating set `G`), with the hypotheses of
`Dec2.i4b_exists_unique` at `δ = C₁ ε`. -/
theorem renBgClass_dec2 {C : DecCover d L N₁ m₁ K}
    (hS : Dec2.DecSpecs d L Kc Cx c BG) (S : Dec2.CoverBase C Gp (compWeight L a₁) ν Kc Cx)
    (HB : BgHyp d L K ϱ (compWeight L a₁) ν) (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hε : 0 < eps)
    (hsm : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hδ7 : xiC1 d * eps ≤ c7 d L N BG κ)
    {D : BgData Gp N} (hD : XiCOneReal Gp (compWeight L a₁) ν eps D)
    {s : Dec2.DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) :
    Dec2.decBgField C Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D ∈
      bgClass Gp ν ((2 + 2 * K4 d L N BG κ * xiC1 d) * eps) D := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hC1pos : 0 < xiC1 d := by unfold xiC1; positivity
  have hδ : 0 < xiC1 d * eps := mul_pos hC1pos hε
  have hc1 : xiC1 d * eps ≤ bgC1 d L N := hδ7.trans (c7_le_bgC1 d L N BG κ)
  have hδ0 : xiC1 d * eps ≤ bgC0 d L N := hc1.trans (bgC1_le_bgC0 d L N hd0)
  have hDom : InDomainC Gp ν (xiC1 d * eps) (xiC1 d * eps) D :=
    xiCData_inDomainC HB hsm hD.xiCOne
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := HB.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  obtain ⟨φ, α, hid, huniq, -, -, hbd⟩ :=
    Dec2.i4b_exists_unique hS S HB hκ hM hs hδ le_rfl hδ0 hδ7 hνε hDom
  obtain ⟨φ1, α1, hid1, -, -, -, hbd1⟩ :=
    Dec2.i4b_exists_unique hS S HB hκ hM (s := fun _ => 1)
      (fun P => by simpa using Real.one_le_exp hκ) hδ le_rfl hδ0 hδ7 hνε hDom
  have e1 := (Dec2.decBg_eq hid huniq).1
  have e2 := (Dec2.i4b_one hS S HB hκ hM hδ le_rfl hδ0 hδ7 hνε hDom hid1).2.1
  have hmem := XiCOneReal.mem_bgClass HB hε hsm hc1 hD
  rw [e2] at hmem
  rw [e1]
  exact mem_bgClass_of_bgBounds HB.mass HB.massLe (K4_pos hS.fam.2.1 hd0).le hC1pos hε hbd hbd1
    hmem

/-- **The uniform bound on the polydisc** (consequence used by `locC1`): for any bound `M` of
`renC1On` on the whole class `bgClass Gp ν (cK ε) D`, at a fixed `ξ`, the decoupled background
gives `‖renC1On …‖ ≤ M` for every admissible `s`. -/
theorem norm_renC1On_dec_le_of_class (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {D : BgData Gp N} (hD : XiCOneReal Gp (compWeight L a₁) ν eps D)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {εζ M : ℝ} {ξ : Fin 3 → ℂ}
    {B : Finset (Torus d ((N₁ * L ^ m₁) * L ^ K))}
    (hM : ∀ φ ∈ bgClass Gp ν ((2 + 2 * K4 d L N BG κ * xiC1 d) * eps) D,
      ‖renC1On Gp (compWeight L a₁) ν εζ B D.Ψ D.h φ ξ‖ ≤ M) :
    ‖renC1On Gp (compWeight L a₁) ν εζ B D.Ψ D.h
      (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D) ξ‖ ≤ M :=
  hM _ (renBgClass_dec hC hD hs)

/-- **The explicit bound**: `‖C₁(B)‖ ≤ (d + 6) (cK ε)² ‖ξ‖ W(B)` at the decoupled background,
for `|ε_ζ| ≤ cK ε` and `‖ξ‖ ≤ 1/16`. -/
theorem norm_renC1On_dec_le (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {D : BgData Gp N} (hD : XiCOneReal Gp (compWeight L a₁) ν eps D)
    {s : DecParams Gp} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {εζ : ℝ} (hεζ0 : 0 ≤ εζ)
    (hεζ : εζ ≤ (2 + 2 * K4 d L N BG κ * xiC1 d) * eps) {ξ : Fin 3 → ℂ} (hξ : ‖ξ‖ ≤ 1 / 16)
    (B : Finset (Torus d ((N₁ * L ^ m₁) * L ^ K))) :
    ‖renC1On Gp (compWeight L a₁) ν εζ B D.Ψ D.h
      (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D) ξ‖ ≤
      (d + 6) * ((2 + 2 * K4 d L N BG κ * xiC1 d) * eps) ^ 2 * ‖ξ‖ * blockWeight Gp B := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hε := hC.eps_pos
  have hC1pos : 0 < xiC1 d := by unfold xiC1; positivity
  have hK := (K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0).le
  have hc0 : 0 ≤ (2 + 2 * K4 d L N BG κ * xiC1 d) * eps := by positivity
  have hδ7 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hc1 : xiC1 d * eps ≤ bgC1 d L N := hδ7.trans (c7_le_bgC1 d L N BG κ)
  obtain ⟨-, -, -, hΨ⟩ := hD.factors hC.HBp hε hC.small1 hc1
  exact norm_renC1On_le_of_mem hC.HBp.weights hC.HBp.mass hΨ hc0 (renBgClass_dec hC hD hs)
    hεζ0 hεζ hξ B

end Main

end Balaban.Fluctuation
