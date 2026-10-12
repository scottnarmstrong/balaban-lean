/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6
public import Balaban.SmallField.XiD2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The bridge Def-6 to I-6: the analyticity domain (torus side)

The ball of radius `ρ` around the constant `e_{i₀}` lies in the analyticity domain
`XiDom = Ξ^c_j(𝔹; 1, ε_j)` of a polymer of the class, provided `N ρ < δ²` for some
`0 < δ ≤ min (c₀, c₁)` with `(2 K₁ + 2) δ ≤ ε_j` (`xiDom_of_close`).

**Radius relation.**  The conditions (C3) of the data domain `Ψ̃^c` bound the component of the
mass-weighted field `ν L^{2n} h'` along the background `φ` by `δ²` (quadratic), so the polydisc of
the premises of I-6 sits in `XiDom` only with radius `ρ ≍ ε_j²`, namely
`ρ = ε_j² / (2 N (2 K₁ + 2)²)` (for `ε_j ≤ (2 K₁ + 2) min (c₀, c₁)`); a radius `ρ ≍ ε_j` is
available only for the backgrounds of mass `0` (`β_k ν_k ≤ 1`).

Also: `bgHyp_of_class`, the standing hypotheses of the background theory from `Consts.Admissible`
and `CoeffBounds`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The level `n` of `XiC` enters only through the condition `hnorm`, which is void when
`|h₀| = 1`. -/
theorem xiC_level_irrel {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {a : ℕ → ℝ} {ν ε : ℝ}
    {n n' : ℕ} {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : CTorus d L N₁ m₁ k → Fin N → ℂ} (hh : ∑ i, h₀ i ^ 2 = 1)
    (h : SmallField.XiC G a ν n 1 ε Ψ₀ h₀ Ψ'' h'') : SmallField.XiC G a ν n' 1 ε Ψ₀ h₀ Ψ'' h'' := by
  obtain ⟨hσ, hε, Dr, Dc, ⟨hR, hU, hb⟩, hC, hDc, hbC⟩ := h
  refine ⟨hσ, hε, Dr, Dc, ⟨hR, hU, { hb with hnorm := ?_ }⟩, hC, hDc, hbC⟩
  rw [hh]; simp; positivity

/-- A field constant on the `j`-blocks is constant on the blocks of every layer `n ≤ j`. -/
theorem isLayerConstant_of_jBlock {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {j : ℕ}
    (hjk : j ≤ k) (hΩ : ∀ i, j < i → G.Ω i = ∅) {β : Type*}
    {f : CTorus d L N₁ m₁ k → β}
    (hf : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → f x = f x') :
    IsLayerConstant G f := by
  intro n hn1 hnk x hx x' hx'
  have hxn : x ∈ G.Ω n := (G.mem_layer.1 hx).1
  have hnj : n ≤ j := by
    by_contra h
    have := hΩ n (by omega)
    rw [this] at hxn; simp at hxn
  apply hf
  have hb := G.mem_blk.1 hx'
  unfold jBlock at hb ⊢
  have hℓ : N₁ * L ^ m₁ * L ^ k = L ^ n * (N₁ * L ^ m₁ * L ^ (k - n)) := by
    rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' (by omega)]
  have hm : N₁ * L ^ m₁ * L ^ (k - n) = L ^ (j - n) * (N₁ * L ^ m₁ * L ^ (k - j)) := by
    rw [mul_left_comm, ← pow_add]
    congr 2
    omega
  have key := fun y : CTorus d L N₁ m₁ k =>
    blockMap_pow_add (d := d) (L := L) (j := n) (k := j - n) hℓ hm y
  rw [Nat.add_sub_cancel' hnj] at key
  rw [← key x', ← key x, hb]


section Close

variable {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {j : ℕ}

omit [NeZero L] [NeZero N₁] in
theorem rn_single (i₀ : Fin N) : rn (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) = 1 := by
  unfold rn
  have : ∑ i, (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i ^ 2 = 1 := by
    simp [Pi.single_apply]
  rw [this]; simp

/-- **The data domain of a configuration close to the constant `e_{i₀}`**: a field `Ψ` with
`|Ψ - e| ≤ ρ` that is constant on the `j`-blocks, with a constant `h` with
`ν L^{2j} |h - e| ≤ ρ`, is in the complex data domain `Ψ̃^c(𝔹; δ, δ)` over the real datum
`(e, e)`, as soon as `N ρ < δ²`, `δ ≤ 1/16`. -/
theorem inPsiTildeC_of_close (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k) {ν δ ρ : ℝ}
    (hν : 0 ≤ ν) (i₀ : Fin N) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) (hρ0 : 0 < ρ)
    (hρ : (N : ℝ) * ρ < δ ^ 2) (Ψ : CTorus d L N₁ m₁ k → Fin N → ℂ) (c : Fin N → ℂ)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (hc : ∀ i, ν * ((L : ℝ) ^ j) ^ 2 * ‖c i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) :
    InPsiTildeC G ν δ δ (fun _ => Pi.single i₀ 1) (Pi.single i₀ 1)
      (fun x i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i)
      (fun _ i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hNρ2 : (N : ℝ) * ρ < δ := by nlinarith
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have hvn : ∀ x, vn (fun i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i) ≤ N * ρ :=
    fun x => vn_le_card_mul hρ0.le (hΨ x)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hlayer : ∀ x ∈ G.Ω 1, G.layerIndex x ≤ j := by
    intro x hx
    obtain ⟨-, -, hxl⟩ := G.layerIndex_spec hx
    by_contra h
    have := hΩ (G.layerIndex x) (by omega)
    have h2 := (G.mem_layer.1 hxl).1
    rw [this] at h2; simp at h2
  have hw : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ ν * ((L : ℝ) ^ j) ^ 2 := by
    intro x hx
    refine mul_le_mul_of_nonneg_left ?_ hν
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 (hlayer x hx)) 2
  have hhs : vn (fun i => ((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) *
      (c i - (Pi.single i₀ 1 : Fin N → ℂ) i)) ≤ N * ρ := by
    refine vn_le_card_mul hρ0.le fun i => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hc i
  have hhx : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      vn (fun i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i) ≤ N * ρ := by
    intro x hx
    have e := vn_smul_real (ν * ((L : ℝ) ^ j) ^ 2) (fun i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i)
    rw [abs_of_nonneg (by positivity)] at e
    calc _ ≤ ν * ((L : ℝ) ^ j) ^ 2 * vn (fun i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i) :=
          mul_le_mul_of_nonneg_right (hw x hx) (vn_nonneg _)
      _ ≤ _ := e ▸ hhs
  refine
    { layerConst := isLayerConstant_of_jBlock hjk hΩ (fun _ _ _ => rfl)
      r1 := fun x x' _ => ?_
      r2 := fun x _ => ?_
      r3 := fun x _ => ?_
      r4 := ?_
      eps_pos := hδ0
      layerConst' := isLayerConstant_of_jBlock hjk hΩ (fun x x' hb => by
        funext i; simp only [hΨb x x' hb])
      hLayerConst' := isLayerConstant_of_jBlock hjk hΩ (fun _ _ _ => rfl)
      c1 := fun x x' _ => ?_
      c2a := fun x _ => ?_
      c2b := fun x _ => ?_
      c3a := fun x hx => ?_
      c3b := fun x hx => ?_ }
  · simp [rn]; exact hδ0
  · simp [Pi.single_apply]; exact hδ0
  · rw [rn_single]
    have : ∑ i, (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i * (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i = 1 := by
      simp [Pi.single_apply]
    simp only [this, div_one, sub_self, abs_zero, mul_zero]
    positivity
  · have : ∑ i, (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i ^ 2 = 1 := by simp [Pi.single_apply]
    rw [this]; simp; positivity
  · have h1 : vn ((fun i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i) -
        fun i => Ψ x' i - (Pi.single i₀ 1 : Fin N → ℂ) i) ≤ N * (2 * ρ) := by
      refine vn_le_card_mul (by positivity) fun i => ?_
      have a1 := hΨ x i
      have a2 := hΨ x' i
      have : ((fun i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i) -
          fun i => Ψ x' i - (Pi.single i₀ 1 : Fin N → ℂ) i) i =
          (Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i) - (Ψ x' i - (Pi.single i₀ 1 : Fin N → ℂ) i) := rfl
      rw [this]
      exact (norm_sub_le _ _).trans (by linarith)
    nlinarith
  · have := hvn x
    nlinarith
  · have hu : ∀ i, (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ) = (Pi.single i₀ 1 : Fin N → ℂ) i := by
      intro i; by_cases h : i = i₀ <;> simp [h]
    simp only [hu]
    set u : Fin N → ℂ := fun i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i with hu'
    have e1 : ∑ i, ((Pi.single i₀ 1 : Fin N → ℂ) i + u i) * ((Pi.single i₀ 1 : Fin N → ℂ) i + u i) -
        ∑ i, (Pi.single i₀ 1 : Fin N → ℂ) i * (Pi.single i₀ 1 : Fin N → ℂ) i =
        2 * u i₀ + ∑ i, u i * u i := by
      rw [← Finset.sum_sub_distrib]
      have : ∀ i, ((Pi.single i₀ 1 : Fin N → ℂ) i + u i) * ((Pi.single i₀ 1 : Fin N → ℂ) i + u i) -
          (Pi.single i₀ 1 : Fin N → ℂ) i * (Pi.single i₀ 1 : Fin N → ℂ) i =
          2 * ((Pi.single i₀ 1 : Fin N → ℂ) i * u i) + u i * u i := fun i => by ring
      simp_rw [this]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 2
      simp [Pi.single_apply]
    rw [e1]
    have b1 : ‖u i₀‖ ≤ ρ := hΨ x i₀
    have b2 : ‖∑ i, u i * u i‖ ≤ (N * ρ) * (N * ρ) :=
      (norm_dot_le u u).trans (mul_le_mul (hvn x) (hvn x) (vn_nonneg _) (by positivity))
    calc _ ≤ ‖2 * u i₀‖ + ‖∑ i, u i * u i‖ := norm_add_le _ _
      _ ≤ 2 * ρ + (N * ρ) * (N * ρ) := by
          rw [norm_mul]; norm_num; linarith
      _ < δ := by
          have h1 : ρ ≤ N * ρ := by nlinarith
          have h2 : (N : ℝ) * ρ * (N * ρ) ≤ N * ρ := by
            have : (N : ℝ) * ρ ≤ 1 := by nlinarith
            nlinarith [mul_pos (by linarith : (0:ℝ) < N) hρ0]
          nlinarith
  · have e : δ ^ 2 / δ = δ := by field_simp
    rw [e]
    nlinarith [hhx x hx]
  · have hu : ∀ i, ((((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i) / rn (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) : ℝ) : ℂ) =
        (Pi.single i₀ 1 : Fin N → ℂ) i := by
      intro i; rw [rn_single]; by_cases h : i = i₀ <;> simp [h]
    simp only [hu]
    have e : ∑ i, (Pi.single i₀ 1 : Fin N → ℂ) i * (c i - (Pi.single i₀ 1 : Fin N → ℂ) i) =
        c i₀ - (Pi.single i₀ 1 : Fin N → ℂ) i₀ := by
      simp [Pi.single_apply]
    rw [e]
    have h1 : ‖c i₀ - (Pi.single i₀ 1 : Fin N → ℂ) i₀‖ ≤ vn (fun i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i) :=
      norm_le_vn (fun i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i) i₀
    calc _ ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (fun i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ N * ρ := hhx x hx
      _ < δ ^ 2 := hρ


/-- **The ball around the constant `e_{i₀}` lies in `Ξ^c_j(𝔹; 1, ε)`** (the domain inclusion of the
bridge, torus side): a field `Ψ`, constant on the `j`-blocks, with `|Ψ - e| ≤ ρ`, and a constant
`h = c` with `ν L^{2j} |c - e| ≤ ρ` lie in `XiDom` whenever `N ρ < δ²` for some
`0 < δ ≤ min (c₀, c₁)` with `(2 K₁ + 2) δ ≤ ε`.  So the radius is `ρ ≍ ε²`:
`ρ = ε² / (2 N (2 K₁ + 2)²)` is admissible when `ε ≤ (2 K₁ + 2) min (c₀, c₁)`.  -/
theorem xiDom_of_close {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν)
    (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k) {δ ρ ε : ℝ} (i₀ : Fin N) (hδ0 : 0 < δ)
    (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hρ0 : 0 < ρ)
    (hρ : (N : ℝ) * ρ < δ ^ 2) (hε : (2 * bgK1 d L N + 2) * δ ≤ ε)
    (Ψ : CTorus d L N₁ m₁ k → Fin N → ℂ) (c : Fin N → ℂ)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (hc : ∀ i, ν * ((L : ℝ) ^ j) ^ 2 * ‖c i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) :
    XiDom G a ν j ε Ψ (fun _ => c) := by
  have hP := inPsiTildeC_of_close (G := G) hΩ hjk H.mass i₀ hδ0 (hδc0.trans (bgC0_le d L N)) hρ0 hρ
    Ψ c hΨ hΨb hc
  have hK := bgK1_pos d L N
  have hX := psiTildeC_subset_xiC (G := G) (a := a) H hδ0 le_rfl hδc0 hδc1
    (by
      have := H.massLe
      nlinarith [sq_nonneg δ]) hP (εb := ε) (by nlinarith)
  have hX' := xiC_level_irrel (n' := j) (by simp [Pi.single_apply]) hX
  refine ⟨fun _ => Pi.single i₀ 1, Pi.single i₀ 1, fun x i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i,
    fun _ i => c i - (Pi.single i₀ 1 : Fin N → ℂ) i, fun x i => ?_, fun x i => ?_, hX'⟩
  · have hu : (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ) = (Pi.single i₀ 1 : Fin N → ℂ) i := by
      by_cases h : i = i₀ <;> simp [h]
    rw [hu]; ring
  · have hu : (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ) = (Pi.single i₀ 1 : Fin N → ℂ) i := by
      by_cases h : i = i₀ <;> simp [h]
    rw [hu]; ring

end Close



/-! ### The standing hypotheses of the background theory from the class -/

omit [NeZero L] [NeZero N₁] in
theorem aIdeal_mem {ak : ℝ} (hL : 3 ≤ L) (h1 : 9 / 10 * (1 - ((L : ℝ) ^ 2)⁻¹)⁻¹ ≤ ak)
    (h2 : ak < 3 / 2) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    aIdeal L k ak j ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  set q : ℝ := ((L : ℝ) ^ 2)⁻¹ with hqdef
  have hq : q ≤ 1 / 9 := by
    rw [hqdef, inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  have hq0 : 0 < q := by positivity
  have hpow : ∀ n : ℕ, ((L : ℝ) ^ n)⁻¹ ^ 2 = q ^ n := by
    intro n; rw [hqdef, ← inv_pow, ← pow_mul, mul_comm, pow_mul, inv_pow]
  have hpn : ∀ n : ℕ, 1 ≤ n → q ^ n ≤ q := fun n hn =>
    pow_le_of_le_one hq0.le (by linarith) (by omega)
  have hpn0 : ∀ n : ℕ, 0 < q ^ n := fun n => pow_pos hq0 n
  have hpn1 : ∀ n : ℕ, 1 ≤ n → q ^ n < 1 := fun n hn => by linarith [hpn n hn]
  unfold aIdeal
  rw [hpow, hpow]
  have hden : 0 < 1 - q ^ j := by linarith [hpn1 j hj]
  have hak : 9 / 10 ≤ ak := by
    have : (1 - q)⁻¹ ≥ 1 := by
      rw [ge_iff_le, one_le_inv₀ (by linarith)]; linarith
    nlinarith
  have hk1 : 1 ≤ k := hj.trans hjk
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hden]
    have : 1 - q ≤ 1 - q ^ k := by linarith [hpn k hk1]
    nlinarith [hpn0 j]
  · rw [div_le_iff₀ hden]
    have hq2 : 1 - q ^ j ≥ 8 / 9 := by linarith [hpn j hj]
    nlinarith [hpn0 k]


omit [NeZero N₁] in
theorem bgMass_nonneg {βk νk : ℝ} (h : 0 < νk) (L k : ℕ) : 0 ≤ bgMass L k βk νk := by
  unfold bgMass; split_ifs
  · exact le_rfl
  · positivity

omit [NeZero L] [NeZero N₁] in
/-- **The standing hypotheses of the background theory hold for the ideal flow and the mass of the
class** (`d ≥ 3`, `L ≥ 3`, `ϱ ≥ R₀(d, L)`, and the coefficient bounds (H.6)). -/
theorem bgHyp_of_class {P : Consts} {β ν a : ℕ → ℝ} (hP : P.Admissible d L)
    (hC : CoeffBounds d L k P β ν a) (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ) :
    BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) where
  hd := hd
  hL := hL
  hϱ := hϱ
  weights := fun _ hj hjk => aIdeal_mem hL hC.a_ge hC.a_lt hj hjk
  mass := bgMass_nonneg hC.nu_pos L k
  massLe := by
    have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
    unfold bgMass
    split_ifs
    · simp
    · have h1 := hP.νbar_le
      have h2 := hC.nu_le
      have e : ν k * ((L : ℝ) ^ k)⁻¹ ^ 2 * ((L : ℝ) ^ k) ^ 2 = ν k := by
        field_simp
      rw [e]
      have : ((L : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
      linarith

end Balaban.SmallField.Def6
