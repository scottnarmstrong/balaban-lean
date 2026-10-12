module

public import Balaban.Multiscale.PathMetricBounds
public import Balaban.Localization.DecoupledWeighted
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A weight following a layer profile (for Lemma III.4.7)

For a positive profile `τ_1 ≥ τ_2 ≥ … ≥ τ_k` with `τ_i ≤ A₀ R^{j-i} τ_j` (`i ≤ j`) the function
`w(x) = max {1, sup_z (τ_1/τ_{n(z)}) e^{-γ d(z, x)}}` is a weight of rate `γ` (`profileWeight_isWeight`)
with `τ_1/τ_{n(x)} ≤ w(x)` and `w(x) τ_{n(x)} ≤ A₀ R τ_1` (`profileWeight_le`), provided `R ≤ e^{γ(ϱ-1)}`:
the path distance between layers `i < j` is at least `(ϱ - 1)(j - i - 1)` (`pathDist_separation`), which
beats the growth `R^{j-i}` of `1/τ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The profile hypotheses. -/
structure LayerProfile (k : ℕ) (τ : ℕ → ℝ) (A₀ R : ℝ) : Prop where
  pos : ∀ n, 1 ≤ n → n ≤ k → 0 < τ n
  anti : ∀ n, 1 ≤ n → n < k → τ (n + 1) ≤ τ n
  grow : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → τ i ≤ A₀ * R ^ (j - i) * τ j

theorem LayerProfile.anti' {k : ℕ} {τ : ℕ → ℝ} {A₀ R : ℝ} (h : LayerProfile k τ A₀ R) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ k) : τ j ≤ τ i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih =>
    have := h.anti m (by omega) (by omega)
    have := ih (by omega)
    linarith

/-- The sup-convolution weight of the profile. -/
noncomputable def profileWeight (G : GeneratingSet d L N₀ k ϱ) (γ : ℝ) (τ : ℕ → ℝ)
    (x : Torus d (N₀ * L ^ k)) : ℝ :=
  max 1 (⨆ z : G.Ω 1, (τ 1 / τ (G.layerIndex (z : Torus d (N₀ * L ^ k)))) *
    decay γ (G.pathDist z x))

theorem profileWeight_isWeight (G : GeneratingSet d L N₀ k ϱ) {γ : ℝ} (hγ : 0 ≤ γ) {τ : ℕ → ℝ}
    {A₀ R : ℝ} (hτ : LayerProfile k τ A₀ R) : IsWeight G γ (profileWeight G γ τ) := by
  have hg : ∀ z : G.Ω 1, 0 ≤ τ 1 / τ (G.layerIndex (z : Torus d (N₀ * L ^ k))) := by
    intro z
    obtain ⟨h1, h2, -⟩ := G.layerIndex_spec z.2
    have hk1 : 1 ≤ k := le_trans h1 h2
    exact div_nonneg (hτ.pos 1 le_rfl hk1).le (hτ.pos _ h1 h2).le
  refine ⟨fun x => le_max_left _ _, fun x y => ?_⟩
  have hdec := decay_le_one hγ (G.pathDist x y)
  have hdec0 := decay_nonneg γ (G.pathDist x y)
  have hwy : 1 ≤ profileWeight G γ τ y := le_max_left _ _
  unfold profileWeight at hwy ⊢
  rw [max_mul_of_nonneg _ _ hdec0]
  refine max_le (by simpa using hdec.trans hwy) ?_
  rw [Real.iSup_mul_of_nonneg hdec0]
  refine Real.iSup_le (fun z => ?_) (zero_le_one.trans (le_max_left _ _))
  have h1 : decay γ (G.pathDist z x) * decay γ (G.pathDist x y) ≤ decay γ (G.pathDist z y) := by
    rw [← decay_add_dist]
    exact decay_anti_dist hγ (G.pathDist_triangle z x y)
  calc τ 1 / τ (G.layerIndex (z : Torus d (N₀ * L ^ k))) * decay γ (G.pathDist z x) *
        decay γ (G.pathDist x y)
      = τ 1 / τ (G.layerIndex (z : Torus d (N₀ * L ^ k))) *
          (decay γ (G.pathDist z x) * decay γ (G.pathDist x y)) := by ring
    _ ≤ τ 1 / τ (G.layerIndex (z : Torus d (N₀ * L ^ k))) * decay γ (G.pathDist z y) :=
        mul_le_mul_of_nonneg_left h1 (hg z)
    _ ≤ ⨆ z : G.Ω 1, τ 1 / τ (G.layerIndex (z : Torus d (N₀ * L ^ k))) * decay γ (G.pathDist z y) :=
        le_ciSup (f := fun z : G.Ω 1 => τ 1 / τ (G.layerIndex (z : Torus d (N₀ * L ^ k))) *
          decay γ (G.pathDist z y)) (Set.finite_range _).bddAbove z
    _ ≤ _ := le_max_right _ _

theorem profileWeight_ge (G : GeneratingSet d L N₀ k ϱ) (γ : ℝ) (τ : ℕ → ℝ)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    τ 1 / τ (G.layerIndex x) ≤ profileWeight G γ τ x := by
  unfold profileWeight
  refine le_trans ?_ (le_max_right _ _)
  have := le_ciSup (f := fun z : G.Ω 1 => τ 1 / τ (G.layerIndex (z : Torus d (N₀ * L ^ k))) *
    decay γ (G.pathDist z x)) (Set.finite_range _).bddAbove ⟨x, hx⟩
  simpa [G.pathDist_self hx, decay] using this

/-- The key comparison: `τ_{n(x)}/τ_{n(z)} · e^{-γ d(z, x)} ≤ A₀ R`. -/
theorem ratio_decay_le (G : GeneratingSet d L N₀ k ϱ) (hϱ : 1 ≤ ϱ) {γ : ℝ} (hγ : 0 ≤ γ)
    {τ : ℕ → ℝ} {A₀ R : ℝ} (hA₀ : 1 ≤ A₀) (hR : 1 ≤ R) (hRγ : R ≤ Real.exp (γ * (ϱ - 1)))
    (hτ : LayerProfile k τ A₀ R) {x z : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hz : z ∈ G.Ω 1) :
    τ (G.layerIndex x) / τ (G.layerIndex z) * decay γ (G.pathDist z x) ≤ A₀ * R := by
  obtain ⟨hx1, hxk, hxl⟩ := G.layerIndex_spec hx
  obtain ⟨hz1, hzk, hzl⟩ := G.layerIndex_spec hz
  set a := G.layerIndex x with ha
  set b := G.layerIndex z with hb
  have hτa := hτ.pos a hx1 hxk
  have hτb := hτ.pos b hz1 hzk
  have hdec1 := decay_le_one hγ (G.pathDist z x)
  have hdec0 := decay_nonneg γ (G.pathDist z x)
  have hAR : 1 ≤ A₀ * R := by nlinarith
  rcases le_or_gt b a with hba | hab
  · have h1 : τ a ≤ τ b := hτ.anti' hz1 hba hxk
    have h2 : τ a / τ b ≤ 1 := (div_le_one hτb).2 h1
    calc τ a / τ b * decay γ (G.pathDist z x) ≤ 1 * 1 :=
          mul_le_mul h2 hdec1 hdec0 zero_le_one
      _ ≤ A₀ * R := by linarith
  · obtain ⟨t, ht⟩ : ∃ t, b = a + t + 1 := ⟨b - a - 1, by omega⟩
    have hgrow := hτ.grow a b hx1 hab.le hzk
    have hratio : τ a / τ b ≤ A₀ * R ^ (b - a) := by
      rw [div_le_iff₀ hτb]; exact hgrow
    have hsep := G.pathDist_separation hϱ hx1 hz1 hxk hzk hxl hzl
    have hn : a - b + (b - a) - 1 = t := by omega
    rw [hn] at hsep
    rw [G.pathDist_comm z x] at hdec1 hdec0 ⊢
    have hsep' : ENNReal.ofReal ((ϱ - 1) * (t : ℝ)) ≤ G.pathDist x z := hsep
    have hdecay : decay γ (G.pathDist x z) ≤ Real.exp (-(γ * ((ϱ - 1) * (t : ℝ)))) := by
      have := decay_anti_dist hγ hsep'
      rwa [decay_of_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (mul_nonneg (by linarith) (Nat.cast_nonneg _))] at this
    have hpow : R ^ (b - a) = R * R ^ t := by
      rw [show b - a = t + 1 by omega, pow_succ]; ring
    have hRt : R ^ t ≤ Real.exp (γ * (ϱ - 1) * (t : ℝ)) := by
      calc R ^ t ≤ (Real.exp (γ * (ϱ - 1))) ^ t := pow_le_pow_left₀ (by linarith) hRγ t
        _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
    have hE : Real.exp (γ * (ϱ - 1) * (t : ℝ)) * Real.exp (-(γ * ((ϱ - 1) * (t : ℝ)))) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    calc τ a / τ b * decay γ (G.pathDist x z) ≤ (A₀ * R ^ (b - a)) *
          Real.exp (-(γ * ((ϱ - 1) * (t : ℝ)))) :=
          mul_le_mul hratio hdecay hdec0 (by positivity)
      _ = A₀ * R * (R ^ t * Real.exp (-(γ * ((ϱ - 1) * (t : ℝ))))) := by rw [hpow]; ring
      _ ≤ A₀ * R * (Real.exp (γ * (ϱ - 1) * (t : ℝ)) *
            Real.exp (-(γ * ((ϱ - 1) * (t : ℝ))))) := by
          gcongr
      _ = A₀ * R := by rw [hE]; ring

theorem profileWeight_mul_le (G : GeneratingSet d L N₀ k ϱ) (hϱ : 1 ≤ ϱ) {γ : ℝ} (hγ : 0 ≤ γ)
    {τ : ℕ → ℝ} {A₀ R : ℝ} (hA₀ : 1 ≤ A₀) (hR : 1 ≤ R) (hRγ : R ≤ Real.exp (γ * (ϱ - 1)))
    (hτ : LayerProfile k τ A₀ R) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    profileWeight G γ τ x * τ (G.layerIndex x) ≤ A₀ * R * τ 1 := by
  obtain ⟨hx1, hxk, -⟩ := G.layerIndex_spec hx
  have hk1 : 1 ≤ k := le_trans hx1 hxk
  have hτa := hτ.pos _ hx1 hxk
  have hτ1 := hτ.pos 1 le_rfl hk1
  have hAR : 1 ≤ A₀ * R := by nlinarith
  unfold profileWeight
  rw [max_mul_of_nonneg _ _ hτa.le, Real.iSup_mul_of_nonneg hτa.le]
  refine max_le ?_ ?_
  · have : τ (G.layerIndex x) ≤ τ 1 := hτ.anti' le_rfl hx1 hxk
    nlinarith
  · refine Real.iSup_le (fun z => ?_) (by positivity)
    have hr := ratio_decay_le G hϱ hγ hA₀ hR hRγ hτ hx z.2
    obtain ⟨hz1, hzk, -⟩ := G.layerIndex_spec z.2
    have hτb := hτ.pos _ hz1 hzk
    calc τ 1 / τ (G.layerIndex (z : Torus d (N₀ * L ^ k))) * decay γ (G.pathDist z x) *
          τ (G.layerIndex x)
        = τ 1 * (τ (G.layerIndex x) / τ (G.layerIndex (z : Torus d (N₀ * L ^ k))) *
            decay γ (G.pathDist z x)) := by ring
      _ ≤ τ 1 * (A₀ * R) := mul_le_mul_of_nonneg_left hr hτ1.le
      _ = A₀ * R * τ 1 := by ring

end Balaban.LargeField
