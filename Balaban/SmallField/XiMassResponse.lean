/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormExpLemma35
public import Balaban.Fluctuation.LocalClassInherit
public import Balaban.Localization.I5Xi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The mass response of the data domains and of the background (decision D2(b), Step 2, part 1)

`notes/phase1/D2B.md` §2, Step 2.  The mass `ν` of a background problem is moved to
`μ = ν (1 + t)`; the datum is kept.

* `inPsiTilde_massScale`, `inPsiTildeC_massScale`, `inDomainR_massScale`, `inDomainC_massScale`:
  the data domains at the mass `ν` lie in the data domains at every mass `μ ≤ (1 + s) ν`, with
  the radii multiplied by `1 + s` (every clause that contains the mass is linear in it);
* `inUnionDomainC_of_scaled`, `inUnionDomainR_of_scaled`, `inUnionDomainC_of_R`: the union domains;
* `xiC_withLevel`: the level of `Ξ^c` is only seen by the clause `hnorm`;
* `massResponse_single`: for a datum of `Ξ^c_k(𝔹; 1, e)` at the mass `ν` the complex background
  at the mass `μ` is the background at `ν` plus an increment `(δφ, δα)` with
  `‖δφ‖_*, |δα|₂ ≤ 8 K₂ e |t|`.  This is `exists_isRenSol` and `IsRenSol.eq_bg` with
  `ξ = (0, t, 0)`: the mass `ν_u = ν (1 + ξ₂)/(1 + ξ₃)` of Lemma 3.5 (ii) is `μ`.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Balaban.Fluctuation Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Scale

variable {G : GeneratingSet d L N₀ k ϱ}

theorem massScale_aux {ν μ s δ A B : ℝ} (hs : 0 ≤ s) (hμ : μ ≤ (1 + s) * ν) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (h : ν * A * B < δ ^ 2) : μ * A * B < ((1 + s) * δ) ^ 2 := by
  have h1 : μ * A * B ≤ (1 + s) * ν * A * B :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ hA) hB
  have h2 : (1 + s) * ν * A * B = (1 + s) * (ν * A * B) := by ring
  have h3 : (1 + s) * (ν * A * B) < (1 + s) * δ ^ 2 :=
    mul_lt_mul_of_pos_left h (by linarith)
  have h4 : (1 + s) * δ ^ 2 ≤ ((1 + s) * δ) ^ 2 := by nlinarith [sq_nonneg δ]
  linarith

/-- Every clause of `Ψ̃(δ)` that contains the mass is linear in it: `Ψ̃(ν, δ) ⊆ Ψ̃(μ, (1 + s) δ)`
for `μ ≤ (1 + s) ν`. -/
theorem inPsiTilde_massScale {ν μ δ s : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) (hμ : μ ≤ (1 + s) * ν)
    {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ} (H : InPsiTilde G ν δ Ψ h) :
    InPsiTilde G μ ((1 + s) * δ) Ψ h where
  layerConst := H.layerConst
  r1 x x' hxx' := (H.r1 x x' hxx').trans_le (le_mul_of_one_le_left hδ (by linarith))
  r2 x hx := (H.r2 x hx).trans_le (le_mul_of_one_le_left hδ (by linarith))
  r3 x hx := massScale_aux hs hμ (by positivity) (abs_nonneg _) (H.r3 x hx)
  r4 := massScale_aux hs hμ (by positivity) (abs_nonneg _) H.r4

theorem inPsiTildeC_massScale {ν μ δ ε s : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hμ : μ ≤ (1 + s) * ν) {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ}
    {Ψ' h' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (H : InPsiTildeC G ν δ ε Ψ h Ψ' h') :
    InPsiTildeC G μ ((1 + s) * δ) ((1 + s) * ε) Ψ h Ψ' h' where
  toInPsiTilde := inPsiTilde_massScale hs hδ hμ H.toInPsiTilde
  eps_pos := by positivity
  layerConst' := H.layerConst'
  hLayerConst' := H.hLayerConst'
  c1 x x' hxx' := (H.c1 x x' hxx').trans_le (le_mul_of_one_le_left hδ (by linarith))
  c2a x hx := (H.c2a x hx).trans_le (by nlinarith)
  c2b x hx := (H.c2b x hx).trans_le (le_mul_of_one_le_left hδ (by linarith))
  c3a x hx := by
    have h1 := H.c3a x hx
    have hA : 0 ≤ ((L : ℝ) ^ G.layerIndex x) ^ 2 := by positivity
    have hB : 0 ≤ vn (h' x) := vn_nonneg _
    have h2 : μ * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h' x) ≤
        (1 + s) * (ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h' x)) := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ hA) hB
      linarith
    have h3 : (1 + s) * (ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h' x)) <
        (1 + s) * (δ ^ 2 / ε) := mul_lt_mul_of_pos_left h1 (by linarith)
    have h4 : (1 + s) * (δ ^ 2 / ε) = ((1 + s) * δ) ^ 2 / ((1 + s) * ε) := by
      have : (1 + s) ≠ 0 := by linarith
      have : ε ≠ 0 := hε.ne'
      field_simp
    linarith
  c3b x hx := massScale_aux hs hμ (by positivity) (norm_nonneg _) (H.c3b x hx)

theorem inDomainR_massScale {ν μ δ s : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) (hμ : μ ≤ (1 + s) * ν)
    {D : BgData G N} (H : InDomainR G ν δ D) : InDomainR G μ ((1 + s) * δ) D := by
  obtain ⟨Ψ, h, hP, hΨ, hh⟩ := H
  exact ⟨Ψ, h, inPsiTilde_massScale hs hδ hμ hP, hΨ, hh⟩

theorem inDomainC_massScale {ν μ δ ε s : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hμ : μ ≤ (1 + s) * ν) {D : BgData G N} (H : InDomainC G ν δ ε D) :
    InDomainC G μ ((1 + s) * δ) ((1 + s) * ε) D := by
  obtain ⟨Ψ, h, Ψ', h', hP, hΨ, hh⟩ := H
  exact ⟨Ψ, h, Ψ', h', inPsiTildeC_massScale hs hδ hε hμ hP, hΨ, hh⟩

/-- The complex union domain at the mass `μ` from the domain `Ψ̃^c(δ, δ)` at the mass `ν`. -/
theorem inUnionDomainC_of_scaled {c₀ c₁ ν μ δ s : ℝ} (hd0 : 0 < δ) (hs : 0 ≤ s)
    (hμ : μ ≤ (1 + s) * ν) (hμ1 : μ * ((L : ℝ) ^ k) ^ 2 ≤ 1) (hc₁ : (1 + s) * δ ≤ c₁)
    (hc₀ : c₁ ≤ c₀) {D : BgData G N} (H : InDomainC G ν δ δ D) : InUnionDomainC G c₀ c₁ μ D := by
  have hp : 0 < (1 + s) * δ := by positivity
  refine ⟨(1 + s) * δ, (1 + s) * δ, hp, le_rfl, hc₁.trans hc₀, hc₁, ?_,
    inDomainC_massScale hs hd0.le hd0 hμ H⟩
  exact mul_le_of_le_one_left (sq_nonneg _) hμ1

theorem inUnionDomainR_of_scaled {c₁ ν μ δ s : ℝ} (hd0 : 0 < δ) (hs : 0 ≤ s)
    (hμ : μ ≤ (1 + s) * ν) (hc₁ : (1 + s) * δ ≤ c₁) {D : BgData G N} (H : InDomainR G ν δ D) :
    InUnionDomainR G c₁ μ D :=
  ⟨(1 + s) * δ, by positivity, hc₁, inDomainR_massScale hs hd0.le hμ H⟩

/-- Real data of the real union domain lie in the complex union domain (zero perturbation). -/
theorem inUnionDomainC_of_R {ν : ℝ} (hd : 0 < d) (hν : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    {D : BgData G N} (H : InUnionDomainR G (bgC1 d L N) ν D) :
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D := by
  obtain ⟨δ, hδ0, hδc, Ψ, h, hP, hΨ, hh⟩ := H
  have W := DataWit.ofReal (ν := ν) hδ0 hδ0 hP D hΨ hh
  exact ⟨δ, δ, hδ0, le_rfl, hδc.trans (bgC1_le_bgC0 d L N hd), hδc,
    mul_le_of_le_one_left (sq_nonneg _) hν, W.Ψ, W.h₀, W.Ψ', W.h', W.P, W.hΨ, W.hh⟩

end Scale

section Level

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν σ ε : ℝ}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- The level `n` of `Ξ^c_n` is seen only by the clause `hnorm`: a member of `Ξ^c_n` that
satisfies `ν L^{2m} | |h₀|² - 1 | < (σ ε)²` is a member of `Ξ^c_m`. -/
theorem xiC_withLevel {n m : ℕ} (hX : XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'')
    (hm : ν * ((L : ℝ) ^ m) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < (σ * ε) ^ 2) :
    XiC G a ν m σ ε Ψ₀ h₀ Ψ'' h'' := by
  obtain ⟨hσ, hε, Dr, Dc, ⟨hR, hDom, hbr⟩, hC, hDc, hb⟩ := hX
  exact ⟨hσ, hε, Dr, Dc, ⟨hR, hDom, { hbr with hnorm := hm }⟩, hC, hDc, hb⟩

end Level

section Single

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν μ : ℝ}

/-- **The mass response of the background of one datum** (BG Proposition 5.1 with the source
`(μ - ν)(h - φ)`; `exists_isRenSol` and `IsRenSol.eq_bg` for `ξ = (0, t, 0)`).  For a datum of
`Ξ^c_k(𝔹; 1, e)` at the mass `ν` and `μ = ν (1 + t)`, `|t| < r`: the datum lies in the complex
union domain at the mass `μ`, and the complex background at `μ` is the one at `ν` plus an
increment `(δφ, δα)` with `‖δφ‖_*, |δα|₂ ≤ 8 K₂ e |t|`.  The hypotheses `hsm`, `hc1`, `hK`, `hζ` are
those of `exists_isRenSol` (with `4 C₁ e ≤ c₁` so that the domain radius `(1 + |t|) C₁ e` is
at most `c₁ / 2`). -/
theorem massResponse_single (H : BgHyp d L k ϱ a ν) (H' : BgHyp d L k ϱ a μ) {e t r : ℝ}
    (hε : 0 < e) (hsm : (4 * d + 6) * ((2 * d + 1) * e) ≤ 1)
    (hc1 : 4 * (xiC1 d * e) ≤ bgC1 d L N) (hμ : μ = ν * (1 + t)) (ht1 : |t| ≤ 1)
    (htr : |t| < r) (hr : r ≤ 1 / 16)
    (hK : bgK1 d L N * (xiC1 d * e) + 3 * r ≤ deltaStar d L N)
    (hζ : 8 * e * r ≤ deltaStar d L N) {D : BgData G N} (hD : XiCOne G a ν e D) :
    InUnionDomainC G (bgC0 d L N) (bgC1 d L N) μ D ∧
      ∃ (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ),
        bgFieldC G a μ (bgC0 d L N) D = bgFieldC G a ν (bgC0 d L N) D + δφ ∧
        bgMultC G a μ (bgC0 d L N) D = bgMultC G a ν (bgC0 d L N) D + δα ∧
        SupBounds G δφ (cK2 d L N * (8 * e * |t|)) ∧ Small G δα (cK2 d L N * (8 * e * |t|)) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hC1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * e := by positivity
  have hc1' : xiC1 d * e ≤ bgC1 d L N := by linarith
  have ht0 := abs_nonneg t
  have hDC := hD.inDomainC H hsm
  have hμle : μ ≤ (1 + |t|) * ν := by
    rw [hμ, mul_comm ν]
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self t]) H.mass
  have hrad : (1 + |t|) * (xiC1 d * e) ≤ bgC1 d L N := by nlinarith
  have hDU : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) μ D :=
    inUnionDomainC_of_scaled hδ0 ht0 hμle H'.massLe hrad (bgC1_le_bgC0 d L N hd0) hDC
  refine ⟨hDU, ?_⟩
  obtain ⟨-, hsμ, hbμ⟩ := theorem72 H' hDU
  set φμ := bgFieldC G a μ (bgC0 d L N) D with hφμ
  set αμ := bgMultC G a μ (bgC0 d L N) D with hαμ
  set φν := bgFieldC G a ν (bgC0 d L N) D with hφν
  set αν := bgMultC G a ν (bgC0 d L N) D with hαν
  -- the multiplier at `μ` is small in the uniqueness class of `eq_bg`
  have hsmall : IsSmallSolution G a μ (c6 d L N / 2) D φμ αμ := by
    refine ⟨hsμ.1, fun x => ?_⟩
    have hDsc := inDomainC_massScale ht0 hδ0.le hδ0 hμle hDC
    have hb := hbμ ((1 + |t|) * (xiC1 d * e)) ((1 + |t|) * (xiC1 d * e)) (by positivity) le_rfl
      (hrad.trans (bgC1_le_bgC0 d L N hd0)) hrad
      (mul_le_of_le_one_left (sq_nonneg _) H'.massLe) hDsc
    have h2 := (bgC1_facts d L N hd0 (δ := 2 * ((1 + |t|) * (xiC1 d * e))) (by nlinarith)).2.2.2
    have h0 := bgC0_pos d L N hd0
    have h6 := bgC0_le_c6 d L N
    have := hb.alpha x
    nlinarith [bgK1_pos d L N]
  obtain ⟨F, hF⟩ := exists_isRenSol (G := G) (N := N) H hε hr hsm hc1' hK hζ
  set ξ : Fin 3 → ℂ := fun i => (((![0, t, 0] : Fin 3 → ℝ) i : ℝ) : ℂ) with hξ
  have hξle : ‖ξ‖ ≤ |t| := by
    refine (pi_norm_le_iff_of_nonneg ht0).2 fun i => ?_
    fin_cases i <;> simp [hξ]
  have hξr : ‖ξ‖ < r := hξle.trans_lt htr
  have heq := hF.eq_bg H hε hsm hc1' hD (Du := D) (t := ![0, t, 0]) hξr
    (fun x i => by simp) (fun x i => rfl) (c₀ := c6 d L N / 2) (by linarith)
    (φu := φμ) (αu := αμ) (by
      have e1 : ν * (1 + (![0, t, 0] : Fin 3 → ℝ) 1) / (1 + (![0, t, 0] : Fin 3 → ℝ) 2) = μ := by
        simp [hμ]
      rw [e1]; exact hsmall)
  have hV : cK2 d L N * (8 * e * ‖ξ‖) ≤ cK2 d L N * (8 * e * |t|) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hξle (by positivity))
      (cK2_pos d L N).le
  have hsup := hF.sup D hD ξ hξr
  have hsm' := hF.small D hD ξ hξr
  refine ⟨φμ - φν, αμ - αν, by abel, by abel, ?_, ?_⟩
  · rw [show (F ((D.Ψ, D.h), ξ)).1 = φμ - φν from (congrArg Prod.fst heq)] at hsup
    exact hsup.mono hV
  · rw [show (F ((D.Ψ, D.h), ξ)).2 = αμ - αν from (congrArg Prod.snd heq)] at hsm'
    exact fun x => (hsm' x).trans hV

end Single

end Balaban.SmallField
