/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ChiBridge
public import Balaban.LargeField.Background.CubeUnitBg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `χ_k = 1` near the constant configuration (A6-3, box localization, item (L0))

On the box `|w| ≤ p₁` of the last integral the block field is `ψ_k = h + β_k^{-1/2} C w`, within
`m = B β_k^{-1/2} p₁` of the constant unit vector `h` at every block; P4 (6.6) puts the cutoff of
the reference variable inside the small-field region, so `χ_k = 1` there.  Here:

* `inDomainR_liftSingle_near`: a block field within `m ≤ 1/2` of a unit vector `h` lifts to data in
  the real domain `Ψ̃(𝔹_q; ν, δ')` of every generating set at every mass `0 ≤ ν`, `ν L^{2q} ≤ 1`, for
  `3m < δ'` (the bonds differ by `≤ 2m`, `|ψ|² - 1 ≤ 5m/2`, and the direction defect
  `1 - ψ·h/|ψ| ≤ 2m²`);
* `reg_of_inDomainR_near`: from the domain `Ψ̃(𝔹_q; μ, δ')`, `K₁ δ' + m < δ` and data within `m` of
  the unit field `h̃` on the test set, the regularity predicate `Reg_q(G, D, δ; S, S)` holds at the
  mass `μ` (the field test `|φ - h̃| < δ/√ν` from `|φ - Ψ| ≤ K₁ δ'`; the other parts are
  `regParts_of_inDomainR`, BG Theorem 5.2 (3));
* `chiKLong_eq_one_of_near`, `chiY_eq_one_of_near`: `χ^ρ_q(□) = 1` and `χ_k(Y) = 1` for a block field
  within `m` of `h` at every block.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField

section Near

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem rn_eq_norm_toLp_sub (u v : Fin N → ℝ) :
    rn (fun i => u i - v i) =
      ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin N)) - WithLp.toLp 2 v‖ := by
  rw [rn_toLp_eq]
  rfl

/-- **The data of a near-constant block field lie in the real domain at every mass.**  If
`|ψ(z) - h| ≤ m ≤ 1/2` at every block, `|h| = 1`, `0 ≤ ν`, `ν L^{2q} ≤ 1` and `3 m < δ'`, then
`lift_q ψ ∈ Ψ̃(𝔹_q; ν, δ')`. -/
theorem inDomainR_liftSingle_near (G : GeneratingSet d L N₀ q ϱ) {ν : ℝ} (hν : 0 ≤ ν)
    (hν1 : ν * ((L : ℝ) ^ q) ^ 2 ≤ 1) (ψ : Torus d (N₀ * L ^ (q - q)) → Fin N → ℝ)
    (h : Fin N → ℝ) (hh : ∑ i, h i ^ 2 = 1) {m δ' : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1 / 2)
    (hmδ : 3 * m < δ') (hψ : ∀ z, rn (fun i => ψ z i - h i) ≤ m) :
    InDomainR G ν δ'
      (liftSingle G (fun z i => (ψ z i : ℂ)) (fun i => (h i : ℂ))) := by
  set e : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 h with he
  have hen : ‖e‖ = 1 := by
    have h1 : ‖e‖ ^ 2 = 1 := by rw [he, ← sum_sq_toLp, hh]
    have h0 : 0 ≤ ‖e‖ := norm_nonneg _
    nlinarith
  set u : Torus d (N₀ * L ^ (q - q)) → EuclideanSpace ℝ (Fin N) :=
    fun z => WithLp.toLp 2 (ψ z) with hu
  have hue : ∀ z, ‖u z - e‖ ≤ m := fun z => by
    have := hψ z
    rwa [rn_eq_norm_toLp_sub] at this
  have hun : ∀ z, 1 - m ≤ ‖u z‖ ∧ ‖u z‖ ≤ 1 + m := by
    intro z
    have h1 := norm_sub_norm_le (u z) e
    have h2 := norm_sub_norm_le e (u z)
    rw [norm_sub_rev] at h2
    have := hue z
    constructor <;> linarith
  have hδ'0 : 0 < δ' := by linarith
  refine ⟨blockLift q ψ, h, ⟨liftSingle_layerConst G ψ, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rintro x x' ⟨-, -, -, -, -, -, -, -⟩
    show rn (fun i => ψ (jBlock d L N₀ q q x) i - ψ (jBlock d L N₀ q q x') i) < δ'
    rw [rn_eq_norm_toLp_sub]
    have h1 := hue (jBlock d L N₀ q q x)
    have h2 := hue (jBlock d L N₀ q q x')
    have : ‖u (jBlock d L N₀ q q x) - u (jBlock d L N₀ q q x')‖ ≤
        ‖u (jBlock d L N₀ q q x) - e‖ + ‖u (jBlock d L N₀ q q x') - e‖ := by
      rw [norm_sub_rev (u (jBlock d L N₀ q q x')) e]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    show ‖u (jBlock d L N₀ q q x) - u (jBlock d L N₀ q q x')‖ < δ'
    linarith
  · intro x _
    show |∑ i, ψ (jBlock d L N₀ q q x) i ^ 2 - 1| < δ'
    rw [sum_sq_toLp]
    obtain ⟨h1, h2⟩ := hun (jBlock d L N₀ q q x)
    show |‖u (jBlock d L N₀ q q x)‖ ^ 2 - 1| < δ'
    set t := ‖u (jBlock d L N₀ q q x)‖
    rw [abs_lt]
    constructor <;> nlinarith
  · intro x _
    show ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      |1 - (∑ i, ψ (jBlock d L N₀ q q x) i * h i) / rn (ψ (jBlock d L N₀ q q x))| < δ' ^ 2
    set z := jBlock d L N₀ q q x
    have hrn : rn (ψ z) = ‖u z‖ := rn_toLp_eq _
    have hc : (∑ i, ψ z i * h i) = inner ℝ (u z) e := by
      simp [hu, he, PiLp.inner_apply, mul_comm]
    rw [hrn, hc]
    obtain ⟨ht1, ht2⟩ := hun z
    have hct0 := real_inner_le_norm (u z) e
    have hinner : inner ℝ (u z) e = 1 + inner ℝ (u z - e) e := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, hen]; ring
    have hdist0 : ‖u z - e‖ ^ 2 = ‖u z‖ ^ 2 - 2 * inner ℝ (u z) e + 1 := by
      rw [@norm_sub_sq_real, hen]; ring
    have habs0 := abs_real_inner_le_norm (u z - e) e
    set t := ‖u z‖
    set c := inner ℝ (u z) e
    have ht0 : 0 < t := by linarith
    have hct : c ≤ t := by rw [hen, mul_one] at hct0; exact hct0
    have hdist : ‖u z - e‖ ^ 2 = t ^ 2 - 2 * c + 1 := hdist0
    have hc1 : 1 - m ≤ c := by
      rw [hen, mul_one] at habs0
      have := hue z
      have h3 := (abs_le.1 (habs0.trans this)).1
      linarith
    have hm2 : ‖u z - e‖ ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hue z) 2
    have hdef : t - c ≤ m ^ 2 := by
      have hsum : 1 ≤ t + c := by linarith
      have hprod : (t - c) * (t + c) ≤ m ^ 2 := by nlinarith [sq_nonneg (c - 1), hdist, hm2]
      nlinarith [sq_nonneg (t - c)]
    have hratio : 0 ≤ 1 - c / t ∧ 1 - c / t ≤ 2 * m ^ 2 := by
      have e1 : 1 - c / t = (t - c) / t := by field_simp
      rw [e1]
      constructor
      · exact div_nonneg (by linarith) ht0.le
      · rw [div_le_iff₀ ht0]; nlinarith
    rw [abs_of_nonneg hratio.1]
    have hlay : G.layerIndex x ≤ q := by
      by_cases hx1 : x ∈ G.Ω 1
      · exact (G.layerIndex_spec hx1).2.1
      · have : G.layerIndex x = 0 := by
          unfold GeneratingSet.layerIndex
          split_ifs with hex
          · obtain ⟨j, hj1, hjq, hxj⟩ := hex
            exact absurd (G.layer_subset hj1 hjq hxj) hx1
          · rfl
        rw [this]; exact Nat.zero_le _
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    have hpow : ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ ((L : ℝ) ^ q) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 hlay) 2
    have hνl : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ 1 :=
      (mul_le_mul_of_nonneg_left hpow hν).trans hν1
    have hνl0 : 0 ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 := by positivity
    calc ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * (1 - c / t) ≤ 1 * (2 * m ^ 2) :=
          mul_le_mul hνl hratio.2 hratio.1 zero_le_one
      _ < δ' ^ 2 := by nlinarith
  · simp only [hh, sub_self, abs_zero, mul_zero]
    positivity
  · intro x hx i
    simp [liftSingle_Ψ G _ _ hx, blockLift]
  · intro x hx i
    simp [liftSingle_h G _ _ hx]

/-- **Regularity near the constant field, at any mass.**  If the data lie in `Ψ̃(𝔹_q; μ, δ')`,
`δ' ≤ c₁`, are within `m` of the unit field `h̃` on the test set `S ⊂ Ω_q`, and
`K₁ δ' + m < δ`, then `Reg_q(G, D, δ; S, S)` holds. -/
theorem reg_of_inDomainR_near {G : GeneratingSet d L N₀ q ϱ} {a : ℕ → ℝ} {μ : ℝ}
    (H : BgHyp d L q ϱ a μ) (hq : 1 ≤ q) {δ' δ m : ℝ} (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ bgC1 d L N)
    (hm0 : 0 ≤ m) (hK : bgK1 d L N * δ' + m < δ) {D : BgData G N} (hD : InDomainR G μ δ' D)
    (S : Finset (Torus d (N₀ * L ^ q))) (hS : ∀ x ∈ S, x ∈ G.Ω q)
    (hdata : ∀ x ∈ S, vn (fun i => D.Ψ x i - D.h x i) ≤ m)
    (hunit : ∀ x ∈ S, ∑ i, D.h x i * D.h x i = 1) : Reg G a μ D δ S S := by
  have hK1 : bgK1 d L N * δ' < δ := by linarith
  obtain ⟨h1, h2, h3, hval⟩ := regParts_of_inDomainR H hδ'0 hδ'1 hK1 hD hq S hS
  refine ⟨h1, h2, h3, ?_⟩
  intro hν x hx
  have hν1 : μ * ((L : ℝ) ^ q) ^ 2 ≤ 1 := H.massLe
  have hsq : Real.sqrt (μ * ((L : ℝ) ^ q) ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hν1
  have hsq0 : 0 < Real.sqrt (μ * ((L : ℝ) ^ q) ^ 2) := Real.sqrt_pos.2 hν
  have hδ0 : 0 < δ := by
    have := bgK1_pos d L N
    nlinarith
  constructor
  · have e : (fun i => bgFieldC G a μ (bgC0 d L N) D (x, i) - D.h (x : Torus d (N₀ * L ^ q)) i) =
        fun i => (bgFieldC G a μ (bgC0 d L N) D (x, i) - D.Ψ x i) + (D.Ψ x i - D.h x i) := by
      funext i; ring
    rw [e]
    have hle := (vn_add' _ _).trans (add_le_add (hval x) (hdata x hx))
    calc _ ≤ bgK1 d L N * δ' + m := hle
      _ < δ := hK
      _ ≤ δ / Real.sqrt (μ * ((L : ℝ) ^ q) ^ 2) := by
          rw [le_div_iff₀ hsq0]
          nlinarith
  · rw [hunit x hx, sub_self, norm_zero]
    positivity

end Near

section Cube

variable {d M1 N₁ L N q c n : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] [NeZero n]

/-- **`χ^ρ_q(□) = 1` near the constant field.**  For a block field within `m ≤ 1/2` of a unit vector
`h` at every block, at any mass `μ` of the cube `BgHyp`, with `3 m < δ' ≤ c₁` and
`K₁ δ' + m < δ`. -/
theorem chiKLong_eq_one_of_near {a : ℕ → ℝ} {μ δ : ℝ}
    (H : BgHyp d L q (minSep L M1) a μ) (hq : 1 ≤ q) (hm : N₁ * L ^ (q - q) = c * n)
    {h : Fin N → ℝ} (hh : ∑ i, h i ^ 2 = 1) (y0 : Torus d n) (ρ : ℕ)
    (ψ : BlockCfg d (M1 * N₁) L q q N) {m δ' : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1 / 2)
    (hmδ : 3 * m < δ') (hδ'1 : δ' ≤ bgC1 d L N) (hK : bgK1 d L N * δ' + m < δ)
    (hψ : ∀ z, rn (fun i => ψ z i - h i) ≤ m) :
    chiKLong (M1 := M1) (N₁ := N₁) (L := L) (q := q) (N := N) a μ δ h c n ρ y0 ψ = 1 := by
  set G := genCube (M1 := M1) (N₁ := N₁) (L := L) (q := q) c n y0 with hG
  have hδ'0 : 0 < δ' := by linarith
  have hδ0 : 0 < δ := by
    have := bgK1_pos d L N
    nlinarith
  have hD := inDomainR_liftSingle_near G H.mass H.massLe ψ h hh hm0 hm1 hmδ hψ
  have hdata : ∀ x ∈ cubeNbhd M1 N₁ L q c n 1 y0,
      vn (fun i => (cubeData (M1 := M1) (N₁ := N₁) (L := L) (q := q) h c n y0 ψ).Ψ x i -
        (cubeData (M1 := M1) (N₁ := N₁) (L := L) (q := q) h c n y0 ψ).h x i) ≤ m := by
    intro x hx
    have hxΩ : x ∈ G.Ω 1 :=
      G.Ω_antitone le_rfl hq (by omega) (cubeNbhd_one_subset hm y0 x hx)
    have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hxΩ)
    unfold cubeData
    rw [liftSingle_h G _ _ hxΩ, liftSingle_Ψ G _ _ hxd]
    have e : (fun i => (ψ.toC (jBlock d L (M1 * N₁) q q x) i - ((h i : ℝ) : ℂ))) =
        fun i => (((ψ (jBlock d L (M1 * N₁) q q x) i - h i : ℝ)) : ℂ) := by
      funext i; simp [BlockCfg.toC]
    rw [e, vn_ofReal]
    exact hψ _
  have hunit : ∀ x ∈ cubeNbhd M1 N₁ L q c n 1 y0,
      ∑ i, (cubeData (M1 := M1) (N₁ := N₁) (L := L) (q := q) h c n y0 ψ).h x i *
        (cubeData (M1 := M1) (N₁ := N₁) (L := L) (q := q) h c n y0 ψ).h x i = 1 := by
    intro x hx
    have hxΩ : x ∈ G.Ω 1 :=
      G.Ω_antitone le_rfl hq (by omega) (cubeNbhd_one_subset hm y0 x hx)
    unfold cubeData
    rw [liftSingle_h G _ _ hxΩ]
    have : ∑ i, h i * h i = 1 := by simpa [sq] using hh
    exact_mod_cast this
  refine charFn_eq_one ⟨?_, fun hν => ⟨fun x _ => ?_, ?_⟩⟩
  · exact reg_of_inDomainR_near H hq hδ'0 hδ'1 hm0 hK hD _ (cubeNbhd_one_subset hm y0) hdata hunit
  · have hsq : Real.sqrt (μ * ((L : ℝ) ^ q) ^ 2) ≤ 1 := Real.sqrt_le_one.mpr H.massLe
    have hsq0 : 0 < Real.sqrt (μ * ((L : ℝ) ^ q) ^ 2) := Real.sqrt_pos.2 hν
    have e : (fun i => ((ψ (jBlock d L (M1 * N₁) q q x) i : ℝ) : ℂ) - ((h i : ℝ) : ℂ)) =
        fun i => (((ψ (jBlock d L (M1 * N₁) q q x) i - h i : ℝ)) : ℂ) := by
      funext i; push_cast; ring
    show vn (fun i => ((ψ (jBlock d L (M1 * N₁) q q x) i : ℝ) : ℂ) - ((h i : ℝ) : ℂ)) <
      δ / Real.sqrt (μ * ((L : ℝ) ^ q) ^ 2)
    rw [e, vn_ofReal]
    have := hψ (jBlock d L (M1 * N₁) q q x)
    have hK1 : 0 ≤ bgK1 d L N * δ' := by have := bgK1_pos d L N; positivity
    calc _ ≤ m := this
      _ < δ := by linarith
      _ ≤ δ / Real.sqrt (μ * ((L : ℝ) ^ q) ^ 2) := by
          rw [le_div_iff₀ hsq0]; nlinarith
  · have he' : ∑ i, h i * h i = 1 := by simpa [sq] using hh
    have : ∑ i, ((h i : ℝ) : ℂ) * ((h i : ℝ) : ℂ) = 1 := by exact_mod_cast he'
    rw [this, sub_self, norm_zero]
    positivity

end Cube

section Small

open Balaban.LargeField.Def7

variable {S : Setting} {nn : ℕ → ℕ} [∀ k, NeZero (nn k)] {R : ℕ → ℝ} {M KK : ℕ} [NeZero M]
  [NeZero S.L] {k m₁ N : ℕ} {ϱ' : ℝ}

/-- **`χ_k(Y) = 1` near the constant unit field** (item (L0)): for every set `Y` of cubes, a block
field `ψ_k` within `m ≤ 1/2` of `hv` (`|hv| = 1`) at every block, with `3 m < δ' ≤ c₁` and
`K₁ δ' + m < δ_k`, under the cube `BgHyp` at the cutoff mass `μ_k`. -/
theorem chiY_eq_one_of_near (C : SFCtx S nn R M KK N k m₁ ϱ') (Y : Set (Torus S.d (nn k)))
    (ψk : BlockAt S nn M KK k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (hsum : ∑ i, hv i ^ 2 = 1)
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.mu k)) (hk : 1 ≤ k)
    {m δ' : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1 / 2) (hmδ : 3 * m < δ') (hδ'1 : δ' ≤ bgC1 S.d S.L N)
    (hK : bgK1 S.d S.L N * δ' + m < C.cs.delta k) (hψ : ∀ y, ‖ψk y - hv‖ ≤ m) :
    C.chiY Y ψk hv = 1 := by
  unfold SFCtx.chiY cubeProd
  refine Finset.prod_eq_one fun y0 _ => ?_
  refine chiKLong_eq_one_of_near H hk (by simp) hsum y0 _ _ hm0 hm1 hmδ hδ'1 hK fun z => ?_
  have := hψ (torusCast (histScale_eq C.geo.hM C.hnn le_rfl C.hkK) z)
  rw [rn_toLp_eq]
  exact this

end Small

end Balaban.RootFSpine
