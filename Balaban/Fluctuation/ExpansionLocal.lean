module

public import Balaban.Fluctuation.ExpansionBounds
public import Balaban.Fluctuation.ExpansionNuFree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Lemma 2.3 (d): locality and the cubic bound of the interaction

`V^{(k)}(ψ') = ½⟨α¹, φ'·φ'⟩ + ½⟨φ₂, H_k φ₂⟩` is a sum of the density `interactionDensity` over the
fine torus (`interactionV_eq_sum`), hence over the blocks `B_{n+1}(z)`: `V^{(k)} = ∑_z V^{(k)}(z)`
(`interactionV_local`; all scalar products restricted to the block, P4 (2.28)).

`density_bound`: pointwise, using `φ'·φ' = -2 φ_{k+1}·φ₂` (the constraint and `φ_{k+1}·φ¹ = 0`),
the bound of `φ₂` and `α¹`, the coercivity of `α_{k+1}` and the bound of `H_k` (weights `a_m ≤ 2`,
mass `ν L^{2K} ≤ 1`).  `interaction_block_bound`: for every block
`|V^{(k)}(z)| ≤ C_loc K₂² (s²/R) (L^{n+1})^d / (L^n)²`, the form `C_V L^d |ψ'|³` of FLUCTUATION
(2.28) in fine units (`s²/R = s³/ρ`, `ρ = R s`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.Multiscale Balaban.Background Finset Matrix

section Local

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L N₀ K ϱ} {G' : GeneratingSet d L N₀ K ϱ'} {a₁ ν : ℝ} {n : ℕ}

/-- A block mean is bounded by the maximum over the block. -/
theorem norm_blockMean_le' {m : ℕ} (hm : m ≤ K) (w : Torus d (N₀ * L ^ K) → ℂ)
    (x : Torus d (N₀ * L ^ K)) {B : ℝ} (hw : ∀ y ∈ G.blk m x, ‖w y‖ ≤ B) :
    ‖blockMean G m w x‖ ≤ B := by
  unfold blockMean
  have hc := card_blk_cast G m hm x
  have hp : (0 : ℝ) < ((L : ℝ) ^ m) ^ d := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp)]
  have hsum : ‖∑ y ∈ G.blk m x, w y‖ ≤ ((G.blk m x).card : ℝ) * B := by
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hw
  rw [hc] at hsum
  calc (((L : ℝ) ^ m) ^ d)⁻¹ * ‖∑ y ∈ G.blk m x, w y‖ ≤
        (((L : ℝ) ^ m) ^ d)⁻¹ * (((L : ℝ) ^ m) ^ d * B) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hp.le)
    _ = B := by field_simp

/-- `‖∑ᵢ pᵢ qᵢ‖ ≤ N P Q`. -/
theorem norm_sum_mul_le {p q : Fin N → ℂ} {P Q : ℝ} (hp : ∀ i, ‖p i‖ ≤ P) (hq : ∀ i, ‖q i‖ ≤ Q) :
    ‖∑ i, p i * q i‖ ≤ N * P * Q := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖p i * q i‖ ≤ ∑ _i : Fin N, P * Q := Finset.sum_le_sum fun i _ => by
        rw [norm_mul]
        exact mul_le_mul (hp i) (hq i) (norm_nonneg _) ((norm_nonneg _).trans (hp i))
    _ = N * P * Q := by simp [Finset.sum_const]; ring

/-- The density of `V^{(k)}` at a site `x` of the fine torus:
`v(x) = ½ α¹(x) φ'(x)·φ'(x) + ½ φ₂(x)·(H_k φ₂)(x)`. -/
noncomputable def interactionDensity (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (φ' : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ K)) : ℂ :=
  (1 / 2) * zeroExt (G.Ω 1) (alphaOne h a ν α₁ φ₁ (qStar G a ψ')) x *
      ∑ i, svec G φ' x i * svec G φ' x i +
    (1 / 2) * ∑ i, svec G (φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ')) x i *
      svec G (liftOp N (opHk h a ν α₁) *ᵥ (φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ'))) x i

theorem pair_eq_torus {m : ℕ} (hG : IsLevel G m) (u v : G.Ω 1 × Fin N → ℂ) :
    pair G u v = ∑ x, ∑ i, svec G u x i * svec G v x i := by
  unfold pair
  rw [Fintype.sum_prod_type]
  rw [← hG.sum_ΩC (fun x => ∑ i, svec G u x i * svec G v x i)]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  rw [svec_of_mem, svec_of_mem]

/-- `V^{(k)}` is the sum of its density over the fine torus. -/
theorem interactionV_eq_sum {m : ℕ} (hG : IsLevel G m) (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ)
    (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ) (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (φ' : G.Ω 1 × Fin N → ℂ) :
    interactionV h a ν α₁ φ₁ ψ' φ' = ∑ x, interactionDensity h a ν α₁ φ₁ ψ' φ' x := by
  unfold interactionV interactionDensity
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum, ← hG.sum_ΩC (fun x => 1 / 2 * zeroExt (G.Ω 1) (alphaOne h a ν α₁ φ₁
      (qStar G a ψ')) x * ∑ i, svec G φ' x i * svec G φ' x i)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [zeroExt_mem]
    simp only [svec_of_mem]
    ring
  · rw [pair_eq_torus hG, Finset.mul_sum]

/-- **The pointwise bound for the density of `V^{(k)}`.**  Let `φ₂ = φ' - φ^{(1)}` satisfy
`‖φ₂‖_* ≤ V`, `|α^{(1)}|₂ ≤ Q`, let the base multiplier satisfy the coercivity bound
`|α_{k+1}| ≤ c/(2 ℓ²)`, the base field `|φ_{k+1}| ≤ 3/2` and the constraint give
`φ'·φ' = -2 φ_{k+1}·φ₂`.  Then (units `ℓ = L^m`, weights `a_m ≤ 2`, mass `ν ℓ_K² ≤ 1`)
`|v(x)| ≤ (N / ℓ²) · (3/2 · Q V + ½ (4 + c/2) V²)`. -/
theorem density_bound {m : ℕ} (hG : IsLevel G m) (hm : m ≤ K) {a : ℕ → ℝ}
    (ha : a m ∈ Set.Icc (1 / 2 : ℝ) 2) {ν : ℝ} (hν0 : 0 ≤ ν) (hν : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1)
    (h : Precedes G G') (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ)
    (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ) (φ' : G.Ω 1 × Fin N → ℂ) {V Q c : ℝ}
    (hu : SupBounds G (φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ')) V)
    (hα1 : Small G (alphaOne h a ν α₁ φ₁ (qStar G a ψ')) Q)
    (hαB : ∀ x : G.Ω 1, ‖h.restrictα α₁ x‖ ≤ c / (2 * ((L : ℝ) ^ m) ^ 2))
    (hφb : ∀ (x : G.Ω 1) i, ‖fieldBase h φ₁ x i‖ ≤ 3 / 2)
    (hsq : ∀ x : G.Ω 1, ∑ i, φ' (x, i) * φ' (x, i) =
      -2 * ∑ i, fieldBase h φ₁ x i * (φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ')) (x, i))
    (hc : 0 ≤ c) (x : Torus d (N₀ * L ^ K)) :
    ‖interactionDensity h a ν α₁ φ₁ ψ' φ' x‖ ≤
      (N / ((L : ℝ) ^ m) ^ 2) * ((3 / 2) * Q * V + (1 / 2) * (4 + c / 2) * V ^ 2) := by
  have hxΩ : x ∈ G.Ω 1 := (hG x).1
  have hlay : G.layerIndex x = m := (hG x).2
  set xx : G.Ω 1 := ⟨x, hxΩ⟩ with hxx
  have hℓ : G.spacing x = (L : ℝ) ^ m := by unfold GeneratingSet.spacing; rw [hlay]
  have hℓ0 : 0 < (L : ℝ) ^ m := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set u := φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ') with hudef
  have hsv : ∀ y i, svec G u y i = u (⟨y, (hG y).1⟩, i) := svec_eq_apply hG u
  have hV : ∀ i, ‖u (xx, i)‖ ≤ V := fun i => by
    have := hu.val x i
    rwa [hsv x i] at this
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp [interactionDensity]
  have hV0 : 0 ≤ V := (norm_nonneg _).trans (hV ⟨0, hN⟩)
  have hα1x : ‖alphaOne h a ν α₁ φ₁ (qStar G a ψ') xx‖ ≤ Q / ((L : ℝ) ^ m) ^ 2 := by
    have := hα1 xx
    have e : G.spacing (xx : Torus d (N₀ * L ^ K)) = (L : ℝ) ^ m := hℓ
    rw [e] at this
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hQ0 : 0 ≤ Q := by
    have := hα1 xx
    exact (mul_nonneg (by positivity) (norm_nonneg _)).trans this
  -- the first term
  have hT1 : ‖zeroExt (G.Ω 1) (alphaOne h a ν α₁ φ₁ (qStar G a ψ')) x *
      ∑ i, svec G φ' x i * svec G φ' x i‖ ≤
      (Q / ((L : ℝ) ^ m) ^ 2) * (2 * (N * (3 / 2) * V)) := by
    rw [norm_mul, zeroExt_mem _ _ xx]
    have e1 : ∑ i, svec G φ' x i * svec G φ' x i = ∑ i, φ' (xx, i) * φ' (xx, i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [svec_eq_apply hG φ' x i]
    rw [e1, hsq xx, norm_mul]
    have hn := norm_sum_mul_le (p := fun i => fieldBase h φ₁ xx i)
      (q := fun i => u (xx, i)) (P := 3 / 2) (Q := V) (fun i => hφb xx i) hV
    refine mul_le_mul hα1x ?_ (by positivity) (by positivity)
    have : ‖(-2 : ℂ)‖ = 2 := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hn (by norm_num)
  -- the second term
  have hHu : ∀ i, ‖svec G (liftOp N (opHk h a ν α₁) *ᵥ u) x i‖ ≤
      (V / ((L : ℝ) ^ m) ^ 2) * (4 + c / 2) := fun i => by
    rw [svec_eq_apply hG]
    show ‖(liftOp N (dirichletOperator G a ν (h.restrictα α₁)) *ᵥ u) (xx, i)‖ ≤ _
    rw [H_alpha_apply, H0_apply]
    have hlap : ‖lapVec G u (xx, i)‖ ≤ V / ((L : ℝ) ^ m) ^ 2 := by
      have := hu.lap x hxΩ i
      rw [hℓ] at this
      rw [le_div_iff₀ (by positivity)]
      have e : lapVec G u (xx, i) = ∑ μ : Fin d, (2 * svec G u x i -
          svec G u (x + Pi.single μ 1) i - svec G u (x - Pi.single μ 1) i) := rfl
      rw [e]
      linarith
    have hblk : ‖blockVec G a u (xx, i)‖ ≤ 2 * V / ((L : ℝ) ^ m) ^ 2 := by
      show ‖blockTerm G a (zeroExt (G.Ω 1) (fun z => u (z, i))) x‖ ≤ _
      rw [blockTerm_zeroExt_eq, hlay, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hb : ‖blockMean G m (zeroExt (G.Ω 1) (fun z => u (z, i))) x‖ ≤ V :=
        norm_blockMean_le' hm _ x (fun y _ => by
          have := hu.val y i
          exact this)
      have ha0 : |a m / ((L : ℝ) ^ m) ^ 2| ≤ 2 / ((L : ℝ) ^ m) ^ 2 := by
        rw [abs_of_nonneg (div_nonneg (by linarith [ha.1]) (by positivity))]
        exact div_le_div_of_nonneg_right ha.2 (by positivity)
      calc |a m / ((L : ℝ) ^ m) ^ 2| * ‖blockMean G m (zeroExt (G.Ω 1) (fun z => u (z, i))) x‖
          ≤ (2 / ((L : ℝ) ^ m) ^ 2) * V := mul_le_mul ha0 hb (norm_nonneg _) (by positivity)
        _ = 2 * V / ((L : ℝ) ^ m) ^ 2 := by ring
    have hnu : ‖(ν : ℂ) * u (xx, i)‖ ≤ V / ((L : ℝ) ^ m) ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hν0]
      have hLm : (L : ℝ) ^ m ≤ (L : ℝ) ^ K := by
        have : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
        exact pow_le_pow_right₀ this hm
      have hν' : ν ≤ 1 / ((L : ℝ) ^ m) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hℓ0.le hLm 2) hν0]
      calc ν * ‖u (xx, i)‖ ≤ (1 / ((L : ℝ) ^ m) ^ 2) * V :=
            mul_le_mul hν' (hV i) (norm_nonneg _) (by positivity)
        _ = V / ((L : ℝ) ^ m) ^ 2 := by ring
    have hnα : ‖h.restrictα α₁ xx * u (xx, i)‖ ≤ (c / 2) * (V / ((L : ℝ) ^ m) ^ 2) := by
      rw [norm_mul]
      calc ‖h.restrictα α₁ xx‖ * ‖u (xx, i)‖ ≤ (c / (2 * ((L : ℝ) ^ m) ^ 2)) * V :=
            mul_le_mul (hαB xx) (hV i) (norm_nonneg _) (by positivity)
        _ = (c / 2) * (V / ((L : ℝ) ^ m) ^ 2) := by field_simp
    have t1 := norm_add_le (lapVec G u (xx, i) + blockVec G a u (xx, i) + (ν : ℂ) * u (xx, i))
      (h.restrictα α₁ (xx, i).1 * u (xx, i))
    have t2 := norm_add_le (lapVec G u (xx, i) + blockVec G a u (xx, i)) ((ν : ℂ) * u (xx, i))
    have t3 := norm_add_le (lapVec G u (xx, i)) (blockVec G a u (xx, i))
    have e2 : 2 * V / ((L : ℝ) ^ m) ^ 2 = 2 * (V / ((L : ℝ) ^ m) ^ 2) := by ring
    calc _ ≤ V / ((L : ℝ) ^ m) ^ 2 + 2 * (V / ((L : ℝ) ^ m) ^ 2) + V / ((L : ℝ) ^ m) ^ 2 +
          (c / 2) * (V / ((L : ℝ) ^ m) ^ 2) := by
          rw [e2] at hblk
          linarith
      _ = _ := by ring
  have hT2 : ‖∑ i, svec G u x i * svec G (liftOp N (opHk h a ν α₁) *ᵥ u) x i‖ ≤
      N * V * ((V / ((L : ℝ) ^ m) ^ 2) * (4 + c / 2)) :=
    norm_sum_mul_le (fun i => hu.val x i) hHu
  unfold interactionDensity
  have hh2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  calc _ ≤ ‖(1 / 2 : ℂ) * zeroExt (G.Ω 1) (alphaOne h a ν α₁ φ₁ (qStar G a ψ')) x *
          ∑ i, svec G φ' x i * svec G φ' x i‖ +
        ‖(1 / 2 : ℂ) * ∑ i, svec G u x i * svec G (liftOp N (opHk h a ν α₁) *ᵥ u) x i‖ :=
        norm_add_le _ _
    _ ≤ (1 / 2) * ((Q / ((L : ℝ) ^ m) ^ 2) * (2 * (N * (3 / 2) * V))) +
        (1 / 2) * (N * V * ((V / ((L : ℝ) ^ m) ^ 2) * (4 + c / 2))) := by
        refine add_le_add ?_ ?_
        · rw [mul_assoc, norm_mul, hh2]
          exact mul_le_mul_of_nonneg_left hT1 (by norm_num)
        · rw [norm_mul, hh2]
          exact mul_le_mul_of_nonneg_left hT2 (by norm_num)
    _ = _ := by ring

/-- The facts at the base point `(ψ^{(k)}, φ_{k+1}, α_{k+1})` used for the bounds of `V^{(k)}`:
the linearised system for `(φ¹, α¹)`, the coercivity of `α_{k+1}` and the bound `|φ_{k+1}| ≤ 3/2`. -/
theorem base_facts {m : ℕ} (ha₁ : 0 < a₁) (hG : IsLevel G m) (hG' : IsLevel G' (m + 1))
    (hp : m + 1 ≤ K) (H : BgHyp d L K ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L K ϱ' (compWeight L a₁) ν) (D' : BgData G' N)
    (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C2 d L N) ν D')
    (S : G.Ω 1 × Fin N → ℂ) :
    (liftOp N (opHk (hG.precedes hG' hp) (compWeight L a₁) ν
        (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')) *ᵥ
        phiOne (hG.precedes hG' hp) (compWeight L a₁) ν
          (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') S +
      fieldMul (fieldBase (hG.precedes hG' hp) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')) *ᵥ
        alphaOne (hG.precedes hG' hp) (compWeight L a₁) ν
          (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') S = S) ∧
    ((fieldMul (fieldBase (hG.precedes hG' hp) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')))ᵀ *ᵥ
        phiOne (hG.precedes hG' hp) (compWeight L a₁) ν
          (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') S = 0) ∧
    (∀ x : G.Ω 1, ‖(hG.precedes hG' hp).restrictα
        (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D') x‖ ≤
      coerciveConst d / (2 * ((L : ℝ) ^ m) ^ 2)) ∧
    (∀ (x : G.Ω 1) i, ‖fieldBase (hG.precedes hG' hp)
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') x i‖ ≤ 3 / 2) := by
  obtain ⟨δs, Φ, St, hΦ⟩ := base_standing ha₁ hG hG' hp H H' D' hD'
  set h := hG.precedes hG' hp with hh'
  set a := compWeight L a₁ with ha
  set φ₁ := bgFieldC G' a ν (bgC0 d L N) D' with hφ₁
  set α₁ := bgMultC G' a ν (bgC0 d L N) D' with hα₁
  have hHu : IsUnit (opHk h a ν α₁) :=
    dirichletOperator_isUnit G St.pos St.mass St.weights _ St.alpha
  have hHA : opHk h a ν α₁ * (opHk h a ν α₁)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hHu)
  have hΦ' : restrictField G Φ = fieldBase h φ₁ := funext fun x => funext fun i => hΦ x i
  have hM : IsUnit (constraintForm (opHk h a ν α₁)⁻¹ (fieldBase h φ₁)) := by
    rw [← hΦ']; exact constraintForm_isUnit St
  obtain ⟨E1, E2⟩ := linResp_facts (N := N) hHA hM S
  refine ⟨E1, E2, fun x => ?_, fun x i => ?_⟩
  · have := St.alpha x
    have e : G.spacing (x : Torus d (N₀ * L ^ K)) = (L : ℝ) ^ m := by
      unfold GeneratingSet.spacing; rw [(hG x).2]
    rw [e] at this
    exact this
  · have hb := St.field.bound x x.2
    have e : Φ x i = fieldBase h φ₁ x i := hΦ x i
    have hc : ‖Φ x i‖ ≤ vn (Φ x) := by
      unfold vn
      exact PiLp.norm_apply_le (WithLp.toLp 2 (Φ x)) i
    rw [← e]
    linarith

/-- The constant of the cubic bound of `V^{(k)}(z)`. -/
noncomputable def locConst (d N : ℕ) : ℝ := N * (7 + coerciveConst d / 2)

/-- The block sum of the density: `V^{(k)}(z) = ∑_{x ∈ B_{n+1}(z)} v(x)`. -/
noncomputable def interactionBlock (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ) (α₁ : G'.Ω 1 → ℂ)
    (φ₁ : G'.Ω 1 × Fin N → ℂ) (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (φ' : G.Ω 1 × Fin N → ℂ) (m : ℕ) (z : Torus d (N₀ * L ^ (K - m))) : ℂ :=
  ∑ x ∈ Finset.univ.filter (fun x : Torus d (N₀ * L ^ K) => jBlock d L N₀ K m x = z),
    interactionDensity h a ν α₁ φ₁ ψ' φ' x

/-- **Locality of `V^{(k)}`**: `V^{(k)} = ∑_z V^{(k)}(z)`, the sum over the blocks `B_{n+1}(z)`. -/
theorem interactionV_local {m : ℕ} (hG : IsLevel G m) (h : Precedes G G') (a : ℕ → ℝ) (ν : ℝ)
    (α₁ : G'.Ω 1 → ℂ) (φ₁ : G'.Ω 1 × Fin N → ℂ) (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (φ' : G.Ω 1 × Fin N → ℂ) (j : ℕ) :
    interactionV h a ν α₁ φ₁ ψ' φ' = ∑ z : Torus d (N₀ * L ^ (K - j)),
      interactionBlock h a ν α₁ φ₁ ψ' φ' j z := by
  classical
  rw [interactionV_eq_sum hG]
  exact (Finset.sum_fiberwise Finset.univ (fun x : Torus d (N₀ * L ^ K) => jBlock d L N₀ K j x)
    (fun x => interactionDensity h a ν α₁ φ₁ ψ' φ' x)).symm

/-- **Lemma 2.3 (d): the cubic bound for `V^{(k)}(z)`** (in fine units: the factor
`(L^{n+1})^d / (L^n)² = L^{n(d-2)} L^d` is the volume of the block over the square of the scale).
Under the hypotheses of `expansion_bounds`, for every block `z`,
`|V^{(k)}(z)| ≤ C_loc K₂² (s²/R) (L^{n+1})^d / (L^n)²`, `s²/R = s³/ρ` for `ρ = R s`. -/
theorem interaction_block_bound (ha₁ : 0 < a₁) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (H : BgHyp d L K ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L K ϱ' (compWeight L a₁) ν) (D' : BgData G' N)
    (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C3 d L N) ν D') (D : BgData G N)
    (hh : ∀ x i, D.h x i = D'.h x i) {s R : ℝ} (hs : 0 ≤ s) (hR : 2 ≤ R)
    (hψs : ∀ x, vn (compTangent hG hG' hp (compWeight L a₁)
      (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D x) ≤ s)
    (hdisc : ∀ t : ℂ, ‖t‖ < R → InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν
      ((composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
        (tangentData D (composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    (hRs : R * s ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * s) < bgC0 d L N / 2)
    (z : Torus d (N₀ * L ^ (K - (n + 1)))) :
    ‖interactionBlock (hG.precedes hG' hp) (compWeight L a₁) ν
        (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')
        (compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D)
        (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D -
          (hG.precedes hG' hp).restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D'))
        (n + 1) z‖ ≤
      locConst d N * cK2 d L N ^ 2 * (s ^ 2 / R) * ((L : ℝ) ^ (n + 1)) ^ d /
        ((L : ℝ) ^ n) ^ 2 := by
  classical
  have hn := hG.bounds
  have hd0 : 0 < d := by have := H.hd; omega
  have hD'2 : InUnionDomainC G' (bgC0 d L N) (thm73C2 d L N) ν D' :=
    InUnionDomainC.mono (thm73C3_le_thm73C2 d L N) hD'
  have hD'1 : InUnionDomainC G' (bgC0 d L N) (thm73C1 d L N) ν D' :=
    InUnionDomainC.mono (thm73C2_le_thm73C1 d L N) hD'2
  have hD'3 : InUnionDomainC G' (bgC0 d L N) (bgC1 d L N) ν D' := by
    obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hD'1
    exact ⟨δ, ε, hδ0, hδε, hε, (thm73_small (L := L) (N := N) hd0 hδ0 hδc).1, hνε, hDC⟩
  obtain ⟨-, -, -, h4, h5, -⟩ := expansion_bounds ha₁ hG hG' hp H H' D' hD' D hh hs hR hψs hdisc
    hRs hsmall
  obtain ⟨hf1, hf2, hα, hφb⟩ := base_facts ha₁ hG hG' hp H H' D' hD'2
    (qStar G (compWeight L a₁) (compTangent hG hG' hp (compWeight L a₁)
      (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D))
  set h := hG.precedes hG' hp with hh'
  set a := compWeight L a₁ with ha
  set φ₁ := bgFieldC G' a ν (bgC0 d L N) D' with hφ₁
  set α₁ := bgMultC G' a ν (bgC0 d L N) D' with hα₁
  set φD := bgFieldC G a ν (bgC0 d L N) D with hφD
  set ψ' := compTangent hG hG' hp a φ₁ D' D with hψ'
  set φ' : G.Ω 1 × Fin N → ℂ := φD - h.restrictφ φ₁ with hφ'
  -- D is in the domain: the endpoint of the disc
  have hhB : D.h = (composeData h a φ₁ D').h := funext fun x => funext fun i => by
    rw [hh x i, composeData_h hG hG' hp]
  have hDc : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D := by
    have := hdisc 1 (by rw [norm_one]; linarith)
    rwa [lineAt_tangent D (composeData h a φ₁ D') hhB] at this
  have hφDc := (theorem72 H hDc).2.1.1.2
  have hφ₁c := (theorem72 H' hD'3).2.1.1.2
  have hcon : ∀ x : G.Ω 1, ∑ i, fieldBase h φ₁ x i * φ' (x, i) =
      -(1 / 2) * ∑ i, φ' (x, i) * φ' (x, i) := fun x => by
    have e1 := hφDc x
    have e2 : ∑ i, fieldBase h φ₁ x i * fieldBase h φ₁ x i = 1 := hφ₁c (h.incl x)
    have e3 : ∑ i, φD (x, i) * φD (x, i) = ∑ i, fieldBase h φ₁ x i * fieldBase h φ₁ x i +
        2 * ∑ i, fieldBase h φ₁ x i * φ' (x, i) + ∑ i, φ' (x, i) * φ' (x, i) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : φD (x, i) = fieldBase h φ₁ x i + φ' (x, i) := by
        simp only [hφ', Pi.sub_apply, fieldBase]; ring
      rw [this]; ring
    linear_combination (1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * e2 - (1 / 2 : ℂ) * e3
  have hsq : ∀ x : G.Ω 1, ∑ i, φ' (x, i) * φ' (x, i) =
      -2 * ∑ i, fieldBase h φ₁ x i * (φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ')) (x, i) := by
    intro x
    have hE := congrFun hf2 x
    rw [fieldMul_transpose_mulVec] at hE
    simp only [Pi.zero_apply] at hE
    have : ∑ i, fieldBase h φ₁ x i * (φ' - phiOne h a ν α₁ φ₁ (qStar G a ψ')) (x, i) =
        ∑ i, fieldBase h φ₁ x i * φ' (x, i) := by
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      rw [hE, sub_zero]
    rw [this, hcon x]; ring
  -- the pointwise bound
  have hc0 : 0 ≤ coerciveConst d := (by
    unfold coerciveConst
    have := poincareConst_pos hd0
    positivity)
  have hKs : 0 ≤ cK2 d L N * s := mul_nonneg (cK2_pos (d := d) (L := L) (N := N)).le hs
  have hdens := fun x => density_bound hG hn.2 (H.weights _ hn.1 hn.2) H.mass H.massLe h α₁ φ₁ ψ' φ'
    h5 h4 hα hφb hsq hc0 x
  -- the block bound
  have hℓ0 : 0 < ((L : ℝ) ^ n) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set Bd : ℝ := (N / ((L : ℝ) ^ n) ^ 2) * ((3 / 2) * (cK2 d L N * s) * (2 * (cK2 d L N * s) / R) +
    (1 / 2) * (4 + coerciveConst d / 2) * (2 * (cK2 d L N * s) / R) ^ 2) with hBd
  have hR0 : 0 < R := by linarith
  have hBd_le : Bd ≤ (N / ((L : ℝ) ^ n) ^ 2) * ((7 + coerciveConst d / 2) *
      ((cK2 d L N * s) ^ 2 / R)) := by
    rw [hBd]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have e1 : (3 / 2) * (cK2 d L N * s) * (2 * (cK2 d L N * s) / R) =
        3 * ((cK2 d L N * s) ^ 2 / R) := by field_simp
    have e2 : (1 / 2) * (4 + coerciveConst d / 2) * (2 * (cK2 d L N * s) / R) ^ 2 =
        2 * (4 + coerciveConst d / 2) * ((cK2 d L N * s) ^ 2 / R ^ 2) := by field_simp
    rw [e1, e2]
    have hq : (cK2 d L N * s) ^ 2 / R ^ 2 ≤ (cK2 d L N * s) ^ 2 / R / 2 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (cK2 d L N * s), mul_nonneg (sq_nonneg (cK2 d L N * s)) hR0.le]
    have h4c : 0 ≤ 4 + coerciveConst d / 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hq h4c, div_nonneg (sq_nonneg (cK2 d L N * s)) hR0.le]
  have hBd0 : 0 ≤ Bd := by
    rw [hBd]; positivity
  have hcard : ((Finset.univ.filter (fun x : Torus d (N₀ * L ^ K) =>
      jBlock d L N₀ K (n + 1) x = z)).card : ℝ) ≤ ((L : ℝ) ^ (n + 1)) ^ d := by
    by_cases hz : (Finset.univ.filter (fun x : Torus d (N₀ * L ^ K) =>
        jBlock d L N₀ K (n + 1) x = z)).Nonempty
    · obtain ⟨y, hy⟩ := hz
      have hyz : jBlock d L N₀ K (n + 1) y = z := (Finset.mem_filter.1 hy).2
      have e : Finset.univ.filter (fun x : Torus d (N₀ * L ^ K) => jBlock d L N₀ K (n + 1) x = z)
          = G'.blk (n + 1) y := by
        ext x
        rw [Finset.mem_filter, GeneratingSet.mem_blk, hyz]
        simp
      rw [e, card_blk G' (n + 1) hp y]
      push_cast
      exact le_rfl
    · rw [Finset.not_nonempty_iff_eq_empty.1 hz, Finset.card_empty]
      simp only [Nat.cast_zero]
      positivity
  unfold interactionBlock
  calc _ ≤ ∑ x ∈ Finset.univ.filter (fun x : Torus d (N₀ * L ^ K) =>
          jBlock d L N₀ K (n + 1) x = z), ‖interactionDensity h a ν α₁ φ₁ ψ' φ' x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x ∈ Finset.univ.filter (fun x : Torus d (N₀ * L ^ K) =>
          jBlock d L N₀ K (n + 1) x = z), Bd := Finset.sum_le_sum fun x _ => hdens x
    _ = (Finset.univ.filter (fun x : Torus d (N₀ * L ^ K) =>
          jBlock d L N₀ K (n + 1) x = z)).card * Bd := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((L : ℝ) ^ (n + 1)) ^ d * Bd := mul_le_mul_of_nonneg_right hcard hBd0
    _ ≤ ((L : ℝ) ^ (n + 1)) ^ d * ((N / ((L : ℝ) ^ n) ^ 2) * ((7 + coerciveConst d / 2) *
          ((cK2 d L N * s) ^ 2 / R))) := mul_le_mul_of_nonneg_left hBd_le (by positivity)
    _ = _ := by unfold locConst; field_simp

end Local

end Balaban.Fluctuation
