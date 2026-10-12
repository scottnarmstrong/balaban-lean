/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeDomain
public import Balaban.SmallField.Def6Inhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# (CONT) is satisfiable: `ContAtZero` for the Def-6 family witness

`Def6.ContAtZero` asks for a `ν`-independent nonempty set, open in the space of block-constant
fields, inside `XiDom` for small `ν`.  `xiDom_of_close_fld` is `xiDom_of_close` for a
block-constant (not necessarily constant) field `h`; `contAtZero_witness` is the clause for the
zero-terms family of `isSFFamily_witness`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Finset Filter Topology

section Close

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {j : ℕ}

/-- `inPsiTildeC_of_close` for a block-constant field `c` in place of a constant. -/
theorem inPsiTildeC_of_close_fld (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k) {ν δ ρ : ℝ}
    (hν : 0 ≤ ν) (i₀ : Fin N) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 16) (hρ0 : 0 < ρ)
    (hρ : (N : ℝ) * ρ < δ ^ 2) (Ψ : CTorus d L N₁ m₁ k → Fin N → ℂ) (c : CTorus d L N₁ m₁ k → Fin N → ℂ)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (hcb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → c x = c x')
    (hc : ∀ x i, ν * ((L : ℝ) ^ j) ^ 2 * ‖c x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) :
    InPsiTildeC G ν δ δ (fun _ => Pi.single i₀ 1) (Pi.single i₀ 1)
      (fun x i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i)
      (fun x i => c x i - (Pi.single i₀ 1 : Fin N → ℂ) i) := by
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
  have hhx : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      vn (fun i => c x i - (Pi.single i₀ 1 : Fin N → ℂ) i) ≤ N * ρ := by
    intro x hx
    have hhs : vn (fun i => ((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) *
        (c x i - (Pi.single i₀ 1 : Fin N → ℂ) i)) ≤ N * ρ := by
      refine vn_le_card_mul hρ0.le fun i => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hc x i
    have e := vn_smul_real (ν * ((L : ℝ) ^ j) ^ 2) (fun i => c x i - (Pi.single i₀ 1 : Fin N → ℂ) i)
    rw [abs_of_nonneg (by positivity)] at e
    calc _ ≤ ν * ((L : ℝ) ^ j) ^ 2 * vn (fun i => c x i - (Pi.single i₀ 1 : Fin N → ℂ) i) :=
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
      hLayerConst' := isLayerConstant_of_jBlock hjk hΩ (fun x x' hb => by
        funext i; simp only [hcb x x' hb])
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
    have e : ∑ i, (Pi.single i₀ 1 : Fin N → ℂ) i * (c x i - (Pi.single i₀ 1 : Fin N → ℂ) i) =
        c x i₀ - (Pi.single i₀ 1 : Fin N → ℂ) i₀ := by
      simp [Pi.single_apply]
    rw [e]
    have h1 : ‖c x i₀ - (Pi.single i₀ 1 : Fin N → ℂ) i₀‖ ≤ vn (fun i => c x i - (Pi.single i₀ 1 : Fin N → ℂ) i) :=
      norm_le_vn (fun i => c x i - (Pi.single i₀ 1 : Fin N → ℂ) i) i₀
    calc _ ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (fun i => c x i - (Pi.single i₀ 1 : Fin N → ℂ) i) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ N * ρ := hhx x hx
      _ < δ ^ 2 := hρ


/-- `xiDom_of_close` for a block-constant field `c` in place of a constant: **the ball around the constant `e_{i₀}` lies in `Ξ^c_j(𝔹; 1, ε)`** (the domain inclusion of the
bridge, torus side): a field `Ψ`, constant on the `j`-blocks, with `|Ψ - e| ≤ ρ`, and a constant
`h = c` with `ν L^{2j} |c - e| ≤ ρ` lie in `XiDom` whenever `N ρ < δ²` for some
`0 < δ ≤ min (c₀, c₁)` with `(2 K₁ + 2) δ ≤ ε`.  So the radius is `ρ ≍ ε²`:
`ρ = ε² / (2 N (2 K₁ + 2)²)` is admissible when `ε ≤ (2 K₁ + 2) min (c₀, c₁)`.  -/
theorem xiDom_of_close_fld {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν)
    (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k) {δ ρ ε : ℝ} (i₀ : Fin N) (hδ0 : 0 < δ)
    (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N) (hρ0 : 0 < ρ)
    (hρ : (N : ℝ) * ρ < δ ^ 2) (hε : (2 * bgK1 d L N + 2) * δ ≤ ε)
    (Ψ : CTorus d L N₁ m₁ k → Fin N → ℂ) (c : CTorus d L N₁ m₁ k → Fin N → ℂ)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (hcb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → c x = c x')
    (hc : ∀ x i, ν * ((L : ℝ) ^ j) ^ 2 * ‖c x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) :
    XiDom G a ν j ε Ψ c := by
  have hP := inPsiTildeC_of_close_fld (G := G) hΩ hjk H.mass i₀ hδ0 (hδc0.trans (bgC0_le d L N)) hρ0 hρ
    Ψ c hΨ hΨb hcb hc
  have hK := bgK1_pos d L N
  have hX := psiTildeC_subset_xiC (G := G) (a := a) H hδ0 le_rfl hδc0 hδc1
    (by
      have := H.massLe
      nlinarith [sq_nonneg δ]) hP (εb := ε) (by nlinarith)
  have hX' := xiC_level_irrel (n' := j) (by simp [Pi.single_apply]) hX
  refine ⟨fun _ => Pi.single i₀ 1, Pi.single i₀ 1, fun x i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i,
    fun x i => c x i - (Pi.single i₀ 1 : Fin N → ℂ) i, fun x i => ?_, fun x i => ?_, hX'⟩
  · have hu : (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ) = (Pi.single i₀ 1 : Fin N → ℂ) i := by
      by_cases h : i = i₀ <;> simp [h]
    rw [hu]; ring
  · have hu : (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ) = (Pi.single i₀ 1 : Fin N → ℂ) i := by
      by_cases h : i = i₀ <;> simp [h]
    rw [hu]; ring

end Close

section Witness

variable {m₁ k N₁ : ℕ} [NeZero N₁] {ϱ : ℝ}

/-- The data of the witness at the level `j`: the background hypotheses. -/
theorem bgHyp_witness {α₀ : ℝ} (hα : 0 < α₀) (hϱ : bgR0 3 3 ≤ ϱ) :
    BgHyp 3 3 k ϱ (aIdeal 3 k (witnessa k)) (bgMass 3 k (witnessβ k) (witnessν k k)) :=
  bgHyp_of_class (witnessConsts_admissible hα) (witness_coeff k) le_rfl le_rfl hϱ

/-- The ball of radius `ρ` around the constant `e₀` (in `ψ`, and in `ν_j⁻¹ b`) lies in `XiDom`,
for block-constant fields, with the witness mass. -/
theorem xiDom_ball_witness {α₀ : ℝ} (hα : 0 < α₀) (hϱ : bgR0 3 3 ≤ ϱ) {j : ℕ} (hjk : j ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (Ψ c : Fld 3 3 N₁ m₁ k 2),
      (∀ x i, ‖Ψ x i - (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) i‖ ≤ ρ) →
      (∀ x i, ‖c x i - (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) i‖ ≤ ρ) →
      IsBlockConstFld j Ψ → IsBlockConstFld j c →
      XiDom (levelGS j hjk : GeneratingSet 3 3 (N₁ * 3 ^ m₁) k ϱ) (aIdeal 3 k (witnessa k))
        (bgMass 3 k (witnessβ k) (witnessν k k)) j ε Ψ c := by
  have H := bgHyp_witness (k := k) hα hϱ
  have hK := bgK1_pos 3 3 2
  have h0 : 0 < bgC0 3 3 2 := bgC0_pos 3 3 2 (by norm_num)
  have h1 : 0 < bgC1 3 3 2 := Balaban.Localization.bgC1_pos' (d := 3) (L := 3) (N := 2) (by norm_num)
  set δ : ℝ := min (min (bgC0 3 3 2) (bgC1 3 3 2)) (ε / (2 * bgK1 3 3 2 + 2)) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min h0 h1) (by positivity)
  have hδc0 : δ ≤ bgC0 3 3 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδc1 : δ ≤ bgC1 3 3 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδε : (2 * bgK1 3 3 2 + 2) * δ ≤ ε := by
    have : δ ≤ ε / (2 * bgK1 3 3 2 + 2) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  refine ⟨δ ^ 2 / 4, by positivity, fun Ψ c hΨ hc hΨb hcb => ?_⟩
  have hmass : bgMass 3 k (witnessβ k) (witnessν k k) * ((3 : ℝ) ^ j) ^ 2 ≤ 1 := by
    have h2 := H.massLe
    have h3 := H.mass
    refine le_trans (mul_le_mul_of_nonneg_left ?_ h3) h2
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hjk) 2
  refine xiDom_of_close_fld (G := levelGS j hjk) H ?_ hjk (δ := δ) (ρ := δ ^ 2 / 4) (ε := ε)
    (0 : Fin 2) hδ0 hδc0 hδc1 (by positivity) (by push_cast; nlinarith [sq_pos_of_pos hδ0]) hδε
    Ψ c hΨ hΨb hcb ?_
  · intro i hi
    have : ¬ i ≤ j := by omega
    simp [levelGS, this]
  · intro x i
    refine le_trans ?_ (hc x i)
    calc _ ≤ 1 * ‖c x i - (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) i‖ :=
          mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
      _ = _ := one_mul _

/-- The pairs `(ψ, b)` with `ψ` and `r b` within `ρ` of the constant `e₀` (coordinatewise). -/
def ballPair (ρ r : ℝ) : Set (Fld 3 3 N₁ m₁ k 2 × Fld 3 3 N₁ m₁ k 2) :=
  {p | ∀ x i, ‖p.1 x i - (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) i‖ < ρ ∧ ‖(r • p.2) x i - (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) i‖ < ρ}

/-- The sets of (CONT) are open: finite intersections of strict coordinate conditions. -/
theorem isOpen_ballPair (ρ r : ℝ) : IsOpen (ballPair (N₁ := N₁) (m₁ := m₁) (k := k) ρ r) := by
  unfold ballPair
  simp only [Set.ofPred_forall]
  refine isOpen_iInter_of_finite fun x => isOpen_iInter_of_finite fun i => ?_
  have c1 : Continuous fun p : Fld 3 3 N₁ m₁ k 2 × Fld 3 3 N₁ m₁ k 2 =>
      ‖p.1 x i - (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) i‖ := by fun_prop
  have c2 : Continuous fun p : Fld 3 3 N₁ m₁ k 2 × Fld 3 3 N₁ m₁ k 2 =>
      ‖(r • p.2) x i - (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) i‖ := by
    simp only [Pi.smul_apply]; fun_prop
  exact (isOpen_lt c1 continuous_const).inter (isOpen_lt c2 continuous_const)

theorem nuIdeal_witness_pos (j : ℕ) : 0 < nuIdeal 3 k (witnessν k k) j := by
  unfold nuIdeal witnessν
  positivity

theorem isOpen_l1_lt : IsOpen {g : Fld 3 3 N₁ m₁ k 2 | l1 g < 1} := by
  refine isOpen_lt ?_ continuous_const
  unfold l1
  exact continuous_finsetSum _ fun x _ => continuous_vn.comp (continuous_apply x)

/-- **(CONT) is satisfiable**: the clause `ContAtZero` holds for the constant family of the zero
terms of `isSFFamily_witness` (any `α₀ > 0`, so in particular the witness class `P`). -/
theorem contAtZero_witness {α₀ : ℝ} (hα : 0 < α₀) (hϱ : bgR0 3 3 ≤ ϱ) :
    ContAtZero (d := 3) (L := 3) (m₁ := m₁) (k := k) (N := 2) (ϱ := ϱ) (witnessConsts α₀) N₁
      (fun _ => witnessβ) (fun _ => witnessa) (fun _ => witnessν k)
      (fun _ => zeroTerms 3 3 N₁ m₁ k 2 ϱ) := by
  -- the common ball
  have key : ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∃ ρ : ℝ, 0 < ρ ∧
      (∀ (Ψ c : Fld 3 3 N₁ m₁ k 2),
      (∀ x i, ‖Ψ x i - (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) i‖ ≤ ρ) →
      (∀ x i, ‖c x i - (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) i‖ ≤ ρ) →
      IsBlockConstFld j Ψ → IsBlockConstFld j c →
      XiDom (levelGS j hjk : GeneratingSet 3 3 (N₁ * 3 ^ m₁) k ϱ) (aIdeal 3 k (witnessa k))
        (bgMass 3 k (witnessβ k) (witnessν k k)) j ((witnessConsts α₀).eps 3 3 j) Ψ c) :=
    fun j _ hjk => xiDom_ball_witness hα hϱ hjk _ (eps_pos (P := witnessConsts α₀) hα j)
  have hpt : ∀ (j : ℕ) (ρ : ℝ), 0 < ρ →
      ((fun _ => (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) : Fld 3 3 N₁ m₁ k 2),
        (fun _ => (nuIdeal 3 k (witnessν k k) j : ℂ) • (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) :
          Fld 3 3 N₁ m₁ k 2)) ∈
      ballPair (N₁ := N₁) (m₁ := m₁) (k := k) ρ ((nuIdeal 3 k (witnessν k k) j)⁻¹) := by
    intro j ρ hρ x i
    have hn := (nuIdeal_witness_pos (k := k) j).ne'
    refine ⟨by simpa using hρ, ?_⟩
    have : ((nuIdeal 3 k (witnessν k k) j)⁻¹ • (fun _ => (nuIdeal 3 k (witnessν k k) j : ℂ) •
        (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) : Fld 3 3 N₁ m₁ k 2)) x i = (Pi.single (0 : Fin 2) 1 : Fin 2 → ℂ) i := by
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      rw [← mul_assoc]
      have h1 : (((nuIdeal 3 k (witnessν k k) j)⁻¹ : ℝ) : ℂ) *
          ((nuIdeal 3 k (witnessν k k) j : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ hn, Complex.ofReal_one]
      rw [h1, one_mul]
    rw [this]; simpa using hρ
  refine ⟨⟨witnessβ k, witnessa k, tendsto_const_nhds, tendsto_const_nhds⟩, ?_, ?_⟩
  · intro j hj1 hjk y X _ _
    obtain ⟨ρ, hρ, hX⟩ := key j hj1 hjk
    refine ⟨ballPair ρ ((nuIdeal 3 k (witnessν k k) j)⁻¹), isOpen_ballPair _ _,
      ⟨_, hpt j ρ hρ, ?_, ?_⟩, ?_, 0, ?_⟩
    · intro x x' _; rfl
    · intro x x' _; rfl
    · refine Filter.Eventually.of_forall fun ν p hp => ?_
      obtain ⟨hV, hb1, hb2⟩ := hp
      show XiDom ((zeroTerms 3 3 N₁ m₁ k 2 ϱ).gs j X) _ _ j _ _ _
      rw [zeroTerms_gs hjk X]
      refine hX p.1 _ (fun x i => (hV x i).1.le) (fun x i => (hV x i).2.le) hb1 ?_
      intro x x' h
      show (nuIdeal 3 k (witnessν k k) j)⁻¹ • p.2 x = (nuIdeal 3 k (witnessν k k) j)⁻¹ • p.2 x'
      rw [hb2 x x' h]
    · exact Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
      Filter.Eventually.of_forall fun n x _ => by simpa [zeroTerms] using hε
  · intro j hj1 hjk x X _ _
    obtain ⟨ρ, hρ, hX⟩ := key j hj1 hjk
    refine ⟨{p | (p.1, p.2.1) ∈ ballPair ρ ((nuIdeal 3 k (witnessν k k) j)⁻¹)} ∩
      {p | l1 p.2.2 < 1}, ?_, ⟨(_, _, 0), ⟨hpt j ρ hρ, ?_⟩, ?_, ?_⟩, ?_, 0, ?_⟩
    · exact ((isOpen_ballPair _ _).preimage (by fun_prop)).inter
        (isOpen_l1_lt.preimage (by fun_prop))
    · show l1 (0 : Fld 3 3 N₁ m₁ k 2) < 1
      simp [l1, vn]
    · intro x x' _; rfl
    · intro x x' _; rfl
    · refine Filter.Eventually.of_forall fun ν p hp => ?_
      obtain ⟨⟨hV, hl⟩, hb1, hb2⟩ := hp
      refine ⟨?_, hl⟩
      show XiDom ((zeroTerms 3 3 N₁ m₁ k 2 ϱ).gs j X) _ _ j _ _ _
      rw [zeroTerms_gs hjk X]
      refine hX p.1 _ (fun x i => (hV x i).1.le) (fun x i => (hV x i).2.le) hb1 ?_
      intro x x' h
      show (nuIdeal 3 k (witnessν k k) j)⁻¹ • p.2.1 x = (nuIdeal 3 k (witnessν k k) j)⁻¹ • p.2.1 x'
      rw [hb2 x x' h]
    · exact Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
      Filter.Eventually.of_forall fun n x _ => by simpa [zeroTerms] using hε

end Witness

end Balaban.SmallField.Def6
