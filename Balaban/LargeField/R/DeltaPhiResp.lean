module

public import Balaban.LargeField.R.DeltaPhiWeight
public import Balaban.Fluctuation.FarDecayUncond
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The layered response to a data change (P3 Proposition 2.1 in the form used by Lemma III.4.7)

For two real data `D, D'` of a generating set (same `h`, mass `ν`), with data change
`δΨ = D'.Ψ - D.Ψ` bounded layerwise, `|δΨ(x)| ≤ τ_{n(x)}` on `Ω₁` and `≤ τ_1` on the collar, for a profile
`τ` with `τ_i ≤ A₀ R^{j-i} τ_j` (`i ≤ j`) and `R ≤ e^{γ_w (ϱ - 1)}`, the difference of the backgrounds
`δφ = φ(D') - φ(D)` and of the multipliers `δα` satisfy on `Ω₁`
`|δφ|, ℓ|∂δφ|, ℓ²|Δδφ|, ℓ²|δα| ≤ K_w C_F A₀ R · τ_{n(x)}` (`layered_response`).

This is the layered form of P3 Proposition 2.1 / LOC I-4a: the weighted perturbation theorem
(`WeightedProp51S`, landed) is applied with the weight `profileWeight` which follows `1/τ` and moves by
the factor `e^{γ_w d}` along the path metric (the layers are `(ϱ - 1)`-apart, `pathDist_separation`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

section Local

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **The source bound at one site**: `ℓ(x)² |F_s(x)| ≤ C_F B` if `|δΨ(x)| ≤ B` and `|δΨ| ≤ B` at the
collar sites adjacent to `x` (a site with a collar neighbour has layer `1`). -/
theorem pertSource_local (S : GreenSetting G a ν) {δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (x : G.Ω 1) (i : Fin N) (hself : vn (δΨ x) ≤ B)
    (hcol : ∀ y ∈ collar G, Adj (x : Torus d (N₀ * L ^ k)) y → vn (δΨ y) ≤ B) :
    G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖pertSource G a δΨ (fun _ => 0) (x, i)‖ ≤
      cF d L * B := by
  classical
  set δΨ' : Torus d (N₀ * L ^ k) → Fin N → ℂ := fun y =>
    if y = (x : Torus d (N₀ * L ^ k)) ∨ (y ∈ collar G ∧ Adj (x : Torus d (N₀ * L ^ k)) y)
    then δΨ y else 0 with hδΨ'
  have h1 : ∀ y ∈ dataSites G, vn (δΨ' y) ≤ B := by
    intro y hy
    by_cases hc : y = (x : Torus d (N₀ * L ^ k)) ∨ (y ∈ collar G ∧ Adj (x : Torus d (N₀ * L ^ k)) y)
    · simp only [hδΨ', hc, ↓reduceIte]
      rcases hc with hc | hc
      · rw [hc]; exact hself
      · exact hcol y hc.1 hc.2
    · simp only [hδΨ', hc, ↓reduceIte]
      exact (vn_zero (N := N)).le.trans hB
  have h2 : pertSource G a δΨ (fun _ => 0) (x, i) = pertSource G a δΨ' (fun _ => 0) (x, i) := by
    unfold pertSource qStar boundaryTerm
    simp only [Pi.add_apply]
    congr 2
    · simp [hδΨ']
    · refine Finset.sum_congr rfl fun μ _ => ?_
      congr 1
      · by_cases hc : (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1 ∈ collar G
        · simp [hc, hδΨ', adj_add_single]
        · simp [hc]
      · by_cases hc : (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1 ∈ collar G
        · simp [hc, hδΨ', adj_sub_single]
        · simp [hc]
  rw [h2]
  exact pertSource_bound S hB h1 (fun x i => by simpa using hB) x i

end Local

section Bounds

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The bounds (2.49′)** in the layered form: on `Ω₁`, `|δφ|, ℓ|∂δφ|, ℓ²|Δδφ|, ℓ²|δα| ≤ K τ_{n(x)}`
(componentwise, as `SupBounds`). -/
structure LayerBounds (G : GeneratingSet d L N₀ k ϱ) (τ : ℕ → ℝ) (K : ℝ)
    (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) : Prop where
  val : ∀ (x : G.Ω 1) (i : Fin N), ‖δφ (x, i)‖ ≤ K * τ (G.layerIndex (x : Torus d (N₀ * L ^ k)))
  fwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
    G.spacing x * ‖svec G δφ (x + Pi.single μ 1) i - svec G δφ x i‖ ≤ K * τ (G.layerIndex x)
  bwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
    G.spacing x * ‖svec G δφ (x - Pi.single μ 1) i - svec G δφ x i‖ ≤ K * τ (G.layerIndex x)
  lap : ∀ x ∈ G.Ω 1, ∀ i : Fin N, G.spacing x ^ 2 * ‖∑ μ : Fin d, (2 * svec G δφ x i -
    svec G δφ (x + Pi.single μ 1) i - svec G δφ (x - Pi.single μ 1) i)‖ ≤ K * τ (G.layerIndex x)
  alpha : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖δα x‖ ≤
    K * τ (G.layerIndex (x : Torus d (N₀ * L ^ k)))

/-- From a weighted bound to a layered one. -/
theorem le_layer_of_weight {w v K t0 tx : ℝ} (ht0 : 0 < t0) (htx : 0 < tx) (hv : 0 ≤ v)
    (hw : t0 / tx ≤ w) (h : w * v ≤ K * t0) : v ≤ K * tx := by
  have h1 : t0 / tx * v ≤ K * t0 := (mul_le_mul_of_nonneg_right hw hv).trans h
  have h2 : t0 * v ≤ K * t0 * tx := by
    have := mul_le_mul_of_nonneg_right h1 htx.le
    have e : t0 / tx * v * tx = t0 * v := by field_simp
    linarith
  have h3 : t0 * v ≤ t0 * (K * tx) := by nlinarith
  exact le_of_mul_le_mul_left h3 ht0

end Bounds

section Core

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **The layered response (P3 Proposition 2.1 in the layered form; LOC I-4a)**, from the landed weighted
perturbation theorem.  `D, D'` are real data of the domain `𝒟_ℝ` (`δ, δ' ≤ c₁`), with the same `h`,
`δΨ = D'.Ψ - D.Ψ` satisfies `|δΨ| ≤ τ_{n(x)}` on `Ω₁` and `≤ τ₁` on the collar, and `τ` is a profile
with growth `R ≤ e^{γ_w (ϱ - 1)}`.  Then `δφ = φ(D') - φ(D)` and `δα = α(D') - α(D)` satisfy the layered
bounds with `K = K_w C_F A₀ R`. -/
theorem layered_response_core {Kw δw : ℝ} (hW : WeightedProp51S d L N Kw δw)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L K ϱ a ν)
    (hOp : Dec2.OpSetting G a ν) {D D' : BgData G N} {δ δ' : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ bgC1 d L N) (hD : InDomainR G ν δ D)
    (hδ0' : 0 < δ') (hδ' : δ' ≤ bgC1 d L N) (hD' : InDomainR G ν δ' D')
    (hK : bgK1 d L N * δ ≤ deltaStar d L N) (hKw : bgK1 d L N * δ ≤ δw)
    (hh : ∀ x i, D'.h x i = D.h x i)
    (hKk : 1 ≤ K) {τ : ℕ → ℝ} {A₀ R : ℝ} (hτ : LayerProfile K τ A₀ R) (hA₀ : 1 ≤ A₀)
    (hR : 1 ≤ R) (hRγ : R ≤ Real.exp (gammaW d * (ϱ - 1)))
    (hΩ : ∀ x ∈ G.Ω 1, vn (fun i => D'.Ψ x i - D.Ψ x i) ≤ τ (G.layerIndex x))
    (hcol : ∀ x ∈ collar G, vn (fun i => D'.Ψ x i - D.Ψ x i) ≤ τ 1)
    (hτs : τ 1 ≤ deltaStar d L N) (hτw : τ 1 ≤ δw) :
    LayerBounds G τ (Kw * (cF d L * (A₀ * R)))
      (bgField G a ν D' - bgField G a ν D) (bgMult G a ν D' - bgMult G a ν D) := by
  classical
  have hd3 : 3 ≤ d := H.hd
  have hd0 : 0 < d := by omega
  have hL2 : 2 ≤ L := by have := H.hL; omega
  have hγ : 0 ≤ gammaW d := gammaW_nonneg hd0
  have hGS : GreenSetting G a ν := H.green
  have hϱ1 : 1 < ϱ := hGS.sep_gt_one
  have hK1 := bgK1_pos d L N
  -- the two small solutions
  obtain ⟨φ, α, hs, hb, hu, hunit, hmin, huniq⟩ := bg_real H hδ0 hδ hD
  obtain ⟨φ', α', hs', hb', hu', hunit', hmin', huniq'⟩ := bg_real H hδ0' hδ' hD'
  have hbg : bgField G a ν D = φ := bgField_eq hmin huniq
  have hbg' : bgField G a ν D' = φ' := bgField_eq hmin' huniq'
  have hmult : bgMult G a ν D = α := by
    funext x
    unfold bgMult
    rw [hbg]
    exact mult_formula hs.1 x
  have hmult' : bgMult G a ν D' = α' := by
    funext x
    unfold bgMult
    rw [hbg']
    exact mult_formula hs'.1 x
  rw [hbg, hbg', hmult, hmult']
  -- the data change
  set δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ := fun x i => D'.Ψ x i - D.Ψ x i with hδΨ
  have hΨ : ∀ x i, D'.Ψ x i = D.Ψ x i + δΨ x i := fun x i => by simp [hδΨ]
  have hτ1 : 0 < τ 1 := hτ.pos 1 le_rfl hKk
  -- uniform bound of the data change
  have hdΨ : ∀ x ∈ dataSites G, vn (δΨ x) ≤ τ 1 := by
    intro x hx
    rcases (mem_dataSites G).1 hx with hx | hx
    · obtain ⟨hl1, hlk, -⟩ := G.layerIndex_spec hx
      exact (hΩ x hx).trans (hτ.anti' le_rfl hl1 hlk)
    · exact hcol x hx
  -- the hypotheses of Proposition 5.1 at the base point
  obtain ⟨Ψ₀, h₀, hP₀, hΨ₀, hhh⟩ := hD
  have W := DataWit.ofReal hδ0 hδ0 hP₀ D hΨ₀ hhh
  have hε : δ ≤ bgC0 d L N := hδ.trans (bgC1_le_bgC0 d L N hd0)
  have hunit1 : ∀ x : G.Ω 1, ∑ i, φ (x, i) * φ (x, i) = 1 := dot_eq_one_of_unit hunit
  have hP := prop51Hyp_of_bgBounds H hδ0 hδ W hε hunit1 hb hK hτ1.le hτs hdΨ
  have hc1 := (bgC1_facts d L N hd0 hδ).2.2.2
  have hc1' := (bgC1_facts d L N hd0 hδ').2.2.2
  have hsmall : Small G (α' - α) (c6 d L N) := by
    intro x
    simp only [Pi.sub_apply]
    have h1 := hb.alpha x
    have h2 := hb'.alpha x
    have hc6 : bgC0 d L N ≤ c6 d L N := min_le_left _ _
    calc G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α' x - α x‖
        ≤ G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * (‖α' x‖ + ‖α x‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
      _ ≤ c6 d L N := by
          have e : G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * (‖α' x‖ + ‖α x‖) =
            G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α' x‖ +
              G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α x‖ := by ring
          rw [e]; linarith
  have hper0 := isPerturbed_of_EL a hΨ hh (φ₀ := barField G D.Ψ φ) (fun (x : G.Ω 1) i => by simp [barField]) hs.1 hs'.1
  have hf : (fun p : G.Ω 1 × Fin N => ((ν - ν : ℝ) : ℂ) * (D.h p.1 p.2 - φ p)) = fun _ => 0 := by
    funext p; simp
  rw [hf] at hper0
  have hg : ∀ x : G.Ω 1, gdef G (barField G D.Ψ φ) x = 0 := fun x => by
    show ∑ i, barField G D.Ψ φ x i * barField G D.Ψ φ x i - 1 = 0
    have : ∀ i, barField G D.Ψ φ x i = φ (x, i) := fun i => by simp [barField]
    simp only [this, hs.1.2 x, sub_self]
  -- the weight
  have hw := profileWeight_isWeight G hγ hτ
  have hfs : ∀ (x : G.Ω 1) (i : Fin N),
      profileWeight G (gammaW d) τ (x : CTorus d L N₁ m₁ K) *
        (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖pertSource G a δΨ (fun _ => 0) (x, i)‖) ≤
      cF d L * (A₀ * R * τ 1) := by
    intro x i
    obtain ⟨hl1, hlk, -⟩ := G.layerIndex_spec x.2
    have hτx := hτ.pos _ hl1 hlk
    have hself : vn (δΨ (x : CTorus d L N₁ m₁ K)) ≤ τ (G.layerIndex (x : CTorus d L N₁ m₁ K)) :=
      hΩ x x.2
    have hcolx : ∀ y ∈ collar G, Adj (x : CTorus d L N₁ m₁ K) y →
        vn (δΨ y) ≤ τ (G.layerIndex (x : CTorus d L N₁ m₁ K)) := by
      intro y hy hadj
      have hy' : y ∉ G.Ω 1 := ((mem_collar G).1 hy).1
      have h1 : G.layerIndex (x : CTorus d L N₁ m₁ K) = 1 :=
        layerIndex_eq_one_of_adj_not_mem hϱ1 hL2 x.2 hy' hadj
      rw [h1]; exact hcol y hy
    have hloc := pertSource_local (a := a) (ν := ν) hGS (δΨ := δΨ)
      (B := τ (G.layerIndex (x : CTorus d L N₁ m₁ K))) hτx.le x i hself hcolx
    have hwx := profileWeight_mul_le G hϱ1.le hγ hA₀ hR hRγ hτ x.2
    have hcF := cF_pos d L
    calc profileWeight G (gammaW d) τ (x : CTorus d L N₁ m₁ K) *
          (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖pertSource G a δΨ (fun _ => 0) (x, i)‖)
        ≤ profileWeight G (gammaW d) τ x * (cF d L * τ (G.layerIndex (x : CTorus d L N₁ m₁ K))) :=
          mul_le_mul_of_nonneg_left hloc (hw.pos _).le
      _ = cF d L * (profileWeight G (gammaW d) τ x * τ (G.layerIndex (x : CTorus d L N₁ m₁ K))) := by
          ring
      _ ≤ cF d L * (A₀ * R * τ 1) := mul_le_mul_of_nonneg_left hwx hcF.le
  have hC : 0 ≤ cF d L * (A₀ * R * τ 1) := by
    have := cF_pos d L
    have : 0 ≤ A₀ * R := by nlinarith
    positivity
  obtain ⟨hSmall, hSup⟩ := hW G a ν α (barField G D.Ψ φ) δΨ (fun _ => 0) (bgK1 d L N * δ) (τ 1) hP hOp
    hg hKw hτw (profileWeight G (gammaW d) τ) hw _ hC hfs (φ' - φ) (α' - α) hper0 hsmall
  have hwge : ∀ x : G.Ω 1, τ 1 / τ (G.layerIndex (x : CTorus d L N₁ m₁ K)) ≤
      profileWeight G (gammaW d) τ (x : CTorus d L N₁ m₁ K) := fun x =>
    profileWeight_ge G (gammaW d) τ x.2
  have hrw : ∀ x : G.Ω 1, 0 < τ (G.layerIndex (x : CTorus d L N₁ m₁ K)) := fun x => by
    obtain ⟨hl1, hlk, -⟩ := G.layerIndex_spec x.2
    exact hτ.pos _ hl1 hlk
  have e : Kw * (cF d L * (A₀ * R * τ 1)) = Kw * (cF d L * (A₀ * R)) * τ 1 := by ring
  rw [e] at hSmall hSup
  have hs0 : ∀ y : CTorus d L N₁ m₁ K, 0 ≤ G.spacing y := fun y => (spacing_pos G).le
  refine ⟨fun x i => ?_, fun x hx μ i => ?_, fun x hx μ i => ?_, fun x hx i => ?_, fun x => ?_⟩
  · exact le_layer_of_weight hτ1 (hrw x) (norm_nonneg _) (hwge x) (hSup.val x i)
  · exact le_layer_of_weight hτ1 (hrw ⟨x, hx⟩) (mul_nonneg (hs0 x) (norm_nonneg _))
      (hwge ⟨x, hx⟩) (hSup.fwd x hx μ i)
  · exact le_layer_of_weight hτ1 (hrw ⟨x, hx⟩) (mul_nonneg (hs0 x) (norm_nonneg _))
      (hwge ⟨x, hx⟩) (hSup.bwd x hx μ i)
  · exact le_layer_of_weight hτ1 (hrw ⟨x, hx⟩) (mul_nonneg (pow_nonneg (hs0 x) 2) (norm_nonneg _))
      (hwge ⟨x, hx⟩) (hSup.lap x hx i)
  · exact le_layer_of_weight hτ1 (hrw x) (mul_nonneg (pow_nonneg (hs0 _) 2) (norm_nonneg _))
      (hwge x) (hSmall x)

end Core

section General

variable {d L N₀ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- `layered_response_core` for a generating set on the torus of side `N₀ L^k` with `N₀ = N₁ L^{m₁}`
(the form in which the landed weighted theorem is stated; `N₁ = N₀`, `m₁ = 0` always works). -/
theorem layered_response {Kw δw : ℝ} (hW : WeightedProp51S d L N Kw δw) [NeZero N₀] {N₁ m₁ : ℕ}
    [NeZero N₁] (hN : N₀ = N₁ * L ^ m₁) {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}
    (H : BgHyp d L k ϱ a ν) (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    {D D' : BgData G N} {δ δ' : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ bgC1 d L N) (hD : InDomainR G ν δ D)
    (hδ0' : 0 < δ') (hδ' : δ' ≤ bgC1 d L N) (hD' : InDomainR G ν δ' D')
    (hK : bgK1 d L N * δ ≤ deltaStar d L N) (hKw : bgK1 d L N * δ ≤ δw)
    (hh : ∀ x i, D'.h x i = D.h x i)
    (hKk : 1 ≤ k) {τ : ℕ → ℝ} {A₀ R : ℝ} (hτ : LayerProfile k τ A₀ R) (hA₀ : 1 ≤ A₀)
    (hR : 1 ≤ R) (hRγ : R ≤ Real.exp (gammaW d * (ϱ - 1)))
    (hΩ : ∀ x ∈ G.Ω 1, vn (fun i => D'.Ψ x i - D.Ψ x i) ≤ τ (G.layerIndex x))
    (hcol : ∀ x ∈ collar G, vn (fun i => D'.Ψ x i - D.Ψ x i) ≤ τ 1)
    (hτs : τ 1 ≤ deltaStar d L N) (hτw : τ 1 ≤ δw) :
    LayerBounds G τ (Kw * (cF d L * (A₀ * R)))
      (bgField G a ν D' - bgField G a ν D) (bgMult G a ν D' - bgMult G a ν D) := by
  subst hN
  exact layered_response_core hW H ⟨⟨H.hd, H.hL, H.mass, H.weights, hsep⟩, H.massLe⟩ hδ0 hδ hD hδ0' hδ' hD' hK hKw hh hKk hτ hA₀ hR hRγ hΩ hcol
    hτs hτw

/-- `LayerProfile` is inhabited: the constant profile. -/
theorem layerProfile_nonempty (k : ℕ) : LayerProfile k (fun _ => 1) 1 1 :=
  ⟨fun _ _ _ => one_pos, fun _ _ _ => le_rfl, fun i j _ _ _ => by simp⟩

end General

end Balaban.LargeField
