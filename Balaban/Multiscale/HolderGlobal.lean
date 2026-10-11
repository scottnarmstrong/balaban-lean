/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.PointwiseHolderMain
public import Balaban.Multiscale.GlobalBound

/-!
# The Hölder bound for all pairs of P2 (3.17) (GREEN.md G-2(iii) for all pairs)

* `tildeDelta G x`: the set `Δ̃(y)` for the block `Δ(y)` of `x` at the layer of `x`: the points of
  `Ω₁` whose own layer block touches (`ℓ^∞`-distance `≤ 1` to) the block of `x`.
* `HolderSeminormLE G g θ σ C`: `|g|_{(θ),σ} ≤ C` for a bond function `g` (the value `g(x)` of the
  bond `{x, x + e_ν}` at its lower endpoint, in a fixed direction `ν`, is
  `ũ(x + e_ν) - ũ(x)`), i.e.
  `ℓ(x)^σ ‖z‖^{-(1-θ)} |g(x') - g(x)| ≤ C` for every `x ∈ Ω₁`, `x' ∈ Δ̃(x)`, `x ≠ x'`, and every lift
  `x' = x + z`, `z ∈ ℤ^d` (the minimal lift is among them, and the others give weaker bounds).
* `holder_pair_decay`: the pair bound `ℓ² |Δ∂u| ≤ (B/θ) ℓ^θ ‖z‖^{1-θ} (e^{-γ d(x,y')} +
  e^{-γ d(x',y')}) ℓ_{j'}² M_f`;
* `holder_global`: `|∂ G f|_{(θ),2-θ} ≤ (B/θ) |f|₂`;
* `global_g2iv`: all four terms of G-2(iv) in one statement.
-/

@[expose] public section

noncomputable section

namespace Balaban.Multiscale

open Finset Matrix Balaban Balaban.LatticeGreen

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- `Δ̃(x)`: points `x'` of `Ω₁` such that the layer block of `x'` touches the block of `x` at the
layer of `x` (P2 (3.17): the union of the blocks of `Ω₁` touching `Δ(y)`). -/
def tildeDelta (G : GeneratingSet d L N₀ k ϱ) (x : Torus d (N₀ * L ^ k)) :
    Set (Torus d (N₀ * L ^ k)) :=
  {x' | x' ∈ G.Ω 1 ∧ ∃ p q : Torus d (N₀ * L ^ k),
    jBlock d L N₀ k (G.layerIndex x) p = jBlock d L N₀ k (G.layerIndex x) x ∧
    jBlock d L N₀ k (G.layerIndex x') q = jBlock d L N₀ k (G.layerIndex x') x' ∧
    ∃ w : Fin d → ℤ, ‖w‖ ≤ 1 ∧ q = liftPt p w}

/-- The Hölder seminorm bound `|g|_{(θ),σ} ≤ C` of P2 (3.17) for the bond function
`x ↦ g (x + e_ν) - g x` (all directions `ν`). -/
def HolderSeminormLE (G : GeneratingSet d L N₀ k ϱ) (g : Torus d (N₀ * L ^ k) → ℂ)
    (θ σ C : ℝ) : Prop :=
  ∀ x ∈ G.Ω 1, ∀ x' ∈ tildeDelta G x, x ≠ x' → ∀ z : Fin d → ℤ, liftPt x z = x' →
    ∀ ν : Fin d, (G.spacing x) ^ σ * (‖z‖ ^ (1 - θ))⁻¹ *
      ‖(g (x' + Pi.single ν 1) - g x') - (g (x + Pi.single ν 1) - g x)‖ ≤ C

omit [NeZero N₀] [NeZero L] in
theorem one_le_norm_of_ne_zero {z : Fin d → ℤ} (hz : z ≠ 0) : 1 ≤ ‖z‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
  have h1 := norm_le_pi_norm z i
  rw [Int.norm_eq_abs] at h1
  have h2 : (1 : ℤ) ≤ |z i| := Int.one_le_abs hi
  have h3 : (1 : ℝ) ≤ |(z i : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast h2
  linarith

/-- Points of `Δ̃(x)` lie in a layer at most one below the layer of `x`. -/
theorem layer_le_of_tildeDelta (G : GeneratingSet d L N₀ k ϱ) (hρ : (d : ℝ) < ϱ)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hx' : x' ∈ tildeDelta G x) :
    G.layerIndex x ≤ G.layerIndex x' + 1 := by
  obtain ⟨hx'Ω, p, q, hp, hq, w, hw, hqw⟩ := hx'
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
  obtain ⟨hj1', hjk', hxl'⟩ := G.layerIndex_spec hx'Ω
  by_contra hcon
  push Not at hcon
  have hpl : p ∈ G.layer (G.layerIndex x) := (G.mem_layer_iff hj1 hjk hp).2 hxl
  have hql : q ∈ G.layer (G.layerIndex x') := (G.mem_layer_iff hj1' hjk' hq).2 hxl'
  have hqn : q ∉ G.Ω (G.layerIndex x' + 1) := (G.mem_layer.1 hql).2
  have hpΩ : p ∈ G.Ω (G.layerIndex x' + 1 + 1) :=
    G.Ω_antitone (by omega) (by omega) (by omega) (G.mem_layer.1 hpl).1
  have hs := G.separation (G.layerIndex x' + 1) (by omega) (by omega) q hqn p hpΩ
  have h1 : Green.torusDist d (N₀ * L ^ k) p q ≤ d := by
    have := torusDist_liftPt_le (L := L) p w
    rw [← hqw] at this
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [norm_nonneg w]
  have h2 : Green.torusDist d (N₀ * L ^ k) q p = Green.torusDist d (N₀ * L ^ k) p q :=
    torusDist_comm' q p
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h3 : (1 : ℝ) ≤ (L : ℝ) ^ (G.layerIndex x' + 1) := one_le_pow₀ hL1
  have hϱ0 : 0 ≤ ϱ := le_trans (Nat.cast_nonneg d) hρ.le
  nlinarith

/-- Proposition 4.8 in the form with the decay factor `decay` (`0` at infinite distance). -/
theorem U_le_decay (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ K2 : ℝ, 0 ≤ K2 ∧ ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
      (S : PtSetting G 1) {Mf : ℝ}, 0 ≤ Mf → (∀ i, ‖S.f i‖ ≤ Mf) →
      ∀ {x : Torus d (N₀ * L ^ k)}, x ∈ G.Ω 1 →
      S.U x ≤ K2 * decay (agmonRate d / 2) (G.pathDist x S.y') * ((L : ℝ) ^ (2 * S.j') * Mf) := by
  obtain ⟨K2, hK2, h48⟩ := prop48 hd hL 1 zero_le_one
  refine ⟨K2, hK2, ?_⟩
  intro k N₀ _ ϱ G S Mf hMf0 hMf x hx
  obtain ⟨h1, h2⟩ := h48 G S hMf0 hMf hx
  have hF0 : 0 ≤ (L : ℝ) ^ (2 * S.j') * Mf := by positivity
  by_cases ht : G.pathDist x S.y' = ⊤
  · rw [h2 ht]; simp [decay, ht]
  · have := h1 ht
    simpa [decay, ht] using this

/-- **The pair bound with decay at both points.**  For `x, x' ∈ Ω₁` with `ℓ(x) ≤ L ℓ(x')` (that is
`layer x ≤ layer x' + 1`) and any lift `x' = x + z`, `z ≠ 0`:
`ℓ(x)² |∂_ν u(x') - ∂_ν u(x)| ≤ (B/θ) ℓ(x)^θ ‖z‖^{1-θ} (e^{-γ d(x,y')} + e^{-γ d(x',y')}) ℓ_{j'}² M_f`. -/
theorem holder_pair_decay (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
      (G : GeneratingSet d L N₀ k ϱ) (S : PtSetting G 1) {Mf : ℝ}, 0 ≤ Mf →
      (∀ i, ‖S.f i‖ ≤ Mf) →
      ∀ {x x' : Torus d (N₀ * L ^ k)}, x ∈ G.Ω 1 → x' ∈ G.Ω 1 →
      G.layerIndex x ≤ G.layerIndex x' + 1 → ∀ {z : Fin d → ℤ}, 1 ≤ ‖z‖ → liftPt x z = x' →
      ∀ (ν : Fin d),
      (G.spacing x) ^ 2 * ‖(S.ut (x' + Pi.single ν 1) - S.ut x') -
          (S.ut (x + Pi.single ν 1) - S.ut x)‖ ≤
        (B / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
          ((decay (agmonRate d / 2) (G.pathDist x S.y') +
            decay (agmonRate d / 2) (G.pathDist x' S.y')) *
            ((L : ℝ) ^ (2 * S.j') * Mf)) := by
  classical
  obtain ⟨B0, hB0, h49⟩ := prop49 hd hL
  obtain ⟨K2, hK2, hU⟩ := U_le_decay hd hL
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  refine ⟨B0 + d * L * (L + 1) * K2, by positivity, ?_⟩
  intro θ hθ0 hθ1 k N₀ _ ϱ G S Mf hMf0 hMf x x' hx hx' hlay z hz1 hzx ν
  subst hzx
  set F : ℝ := (L : ℝ) ^ (2 * S.j') * Mf with hF
  have hF0 : 0 ≤ F := by positivity
  set X : ℝ := (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) with hX
  have hz0 : (0 : ℝ) < ‖z‖ := by linarith
  have hsp0 := spacing_pos G (x := x)
  have hX0 : 0 ≤ X := by positivity
  set dx := decay (agmonRate d / 2) (G.pathDist x S.y') with hdx
  set dx' := decay (agmonRate d / 2) (G.pathDist (liftPt x z) S.y') with hdx'
  have hdx0 := decay_nonneg (agmonRate d / 2) (G.pathDist x S.y')
  have hdx'0 := decay_nonneg (agmonRate d / 2) (G.pathDist (liftPt x z) S.y')
  have hθ' : 1 ≤ 1 / θ := by rw [le_div_iff₀ hθ0]; linarith
  set Dn := ‖(S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)) -
      (S.ut (x + Pi.single ν 1) - S.ut x)‖ with hDn
  have hD0 : 0 ≤ Dn := norm_nonneg _
  have hBθ : ∀ {c : ℝ}, 0 ≤ c → c ≤ B0 + d * L * (L + 1) * K2 → ∀ {T : ℝ}, 0 ≤ T →
      c / θ * X * T ≤ (B0 + d * L * (L + 1) * K2) / θ * X * T := by
    intro c hc hcB T hT
    have : c / θ ≤ (B0 + d * L * (L + 1) * K2) / θ := div_le_div_of_nonneg_right hcB hθ0.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hX0) hT
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
  have hcase : (2 ≤ G.layerIndex x ∧ (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (G.layerIndex x - 1)) ∨
      (G.spacing x ≤ d * L * ‖z‖) := by
    by_cases hj : G.layerIndex x = 1
    · right
      have : G.spacing x = L := by rw [GeneratingSet.spacing, hj, pow_one]
      rw [this]
      have h1 : (1 : ℝ) ≤ d * ‖z‖ := by nlinarith
      nlinarith
    · by_cases hz : (d : ℝ) * ‖z‖ ≤ (L : ℝ) ^ (G.layerIndex x - 1)
      · left; exact ⟨by omega, hz⟩
      · right
        push Not at hz
        have e : G.spacing x = L * (L : ℝ) ^ (G.layerIndex x - 1) := by
          unfold GeneratingSet.spacing
          rw [← pow_succ']; congr 1; omega
        rw [e]
        nlinarith
  rcases hcase with hA | hB
  · -- nearby pair: Proposition 4.9
    obtain ⟨hfin, hinf⟩ := h49 hθ0 hθ1 G S hMf0 hMf hx hz1 hx' (Or.inr hA) ν
    by_cases ht : G.pathDist x S.y' = ⊤
    · have h0 := hinf ht
      have : Dn = 0 := by rw [hDn, h0, norm_zero]
      rw [this, mul_zero]
      have : 0 ≤ (B0 + d * L * (L + 1) * K2) / θ * X * ((dx + dx') * F) := by positivity
      exact this
    · have h1 := hfin ht
      have e : Real.exp (-(agmonRate d / 2 * (G.pathDist x S.y').toReal)) = dx := by
        simp [hdx, decay, ht]
      rw [e] at h1
      refine h1.trans ?_
      have : B0 / θ * X * (dx * F) ≤ (B0 + d * L * (L + 1) * K2) / θ * X * ((dx + dx') * F) := by
        have h2 : dx * F ≤ (dx + dx') * F := by nlinarith
        have h3 : B0 / θ * X * ((dx + dx') * F) ≤
            (B0 + d * L * (L + 1) * K2) / θ * X * ((dx + dx') * F) := by
          apply hBθ hB0 (by have : 0 ≤ (d : ℝ) * L * (L + 1) * K2 := by positivity
                            linarith) (by positivity)
        have h4 : 0 ≤ B0 / θ * X := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h2 h4]
      exact this
  · -- far pair: bound `U` at both points
    have hℓ1 : (1 : ℝ) ≤ G.spacing x := G.spacing_ge_one x
    have hK1 : (1 : ℝ) ≤ d * L := by nlinarith
    have hℓK : G.spacing x ≤ (d * L) * X :=
      le_const_rpow_mul hℓ1 hz1 hK1 hθ0 hθ1 (Or.inr hB)
    have hsp' : G.spacing x ≤ L * G.spacing (liftPt x z) := by
      unfold GeneratingSet.spacing
      calc (L : ℝ) ^ G.layerIndex x ≤ (L : ℝ) ^ (G.layerIndex (liftPt x z) + 1) :=
            pow_le_pow_right₀ hL1 hlay
        _ = _ := by rw [pow_succ']
    have h1 := S.spacing_mul_norm_le_U (y := x) ν
    have h2 := S.spacing_mul_norm_le_U (y := liftPt x z) ν
    have hUx := hU G S hMf0 hMf hx
    have hUx' := hU G S hMf0 hMf hx'
    have hn := norm_sub_le (S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z))
      (S.ut (x + Pi.single ν 1) - S.ut x)
    have hL0 : (0 : ℝ) ≤ L := by linarith
    have hn0 := norm_nonneg (S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z))
    have h5 : G.spacing x * Dn ≤ L * (K2 * dx' * F) + K2 * dx * F := by
      calc G.spacing x * Dn ≤ G.spacing x * (‖S.ut (liftPt x z + Pi.single ν 1) -
            S.ut (liftPt x z)‖ + ‖S.ut (x + Pi.single ν 1) - S.ut x‖) :=
            mul_le_mul_of_nonneg_left hn hsp0.le
        _ = G.spacing x * ‖S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)‖ +
            G.spacing x * ‖S.ut (x + Pi.single ν 1) - S.ut x‖ := by ring
        _ ≤ L * (K2 * dx' * F) + K2 * dx * F := by
            refine add_le_add ?_ (h1.trans hUx)
            calc G.spacing x * ‖S.ut (liftPt x z + Pi.single ν 1) - S.ut (liftPt x z)‖ ≤
                (L * G.spacing (liftPt x z)) * ‖S.ut (liftPt x z + Pi.single ν 1) -
                  S.ut (liftPt x z)‖ := mul_le_mul_of_nonneg_right hsp' hn0
              _ = L * (G.spacing (liftPt x z) * ‖S.ut (liftPt x z + Pi.single ν 1) -
                  S.ut (liftPt x z)‖) := by ring
              _ ≤ L * (K2 * dx' * F) := mul_le_mul_of_nonneg_left (h2.trans hUx') hL0
    have hT : 0 ≤ (dx + dx') * F := by positivity
    have h6 : L * (K2 * dx' * F) + K2 * dx * F ≤ (L + 1) * K2 * ((dx + dx') * F) := by
      have : 0 ≤ (L : ℝ) * (K2 * dx * F) := by positivity
      have : 0 ≤ K2 * dx' * F := by positivity
      nlinarith
    calc G.spacing x ^ 2 * Dn = G.spacing x * (G.spacing x * Dn) := by ring
      _ ≤ ((d * L) * X) * ((L + 1) * K2 * ((dx + dx') * F)) :=
          mul_le_mul hℓK (h5.trans h6) (by positivity) (by positivity)
      _ = ((d * L * (L + 1) * K2) * X) * ((dx + dx') * F) := by ring
      _ ≤ (d * L * (L + 1) * K2) / θ * X * ((dx + dx') * F) := by
          have : (d * L * (L + 1) * K2 : ℝ) ≤ d * L * (L + 1) * K2 / θ :=
            le_div_self (by positivity) hθ0 hθ1.le
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hX0) hT
      _ ≤ _ := by
          exact hBθ (by positivity) (le_add_of_nonneg_left hB0) hT

/-- The zero extension of the solution `G_D(α) f`. -/
def greenSol (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (f : G.Ω 1 → ℂ) : Torus d (N₀ * L ^ k) → ℂ :=
  zeroExt (G.Ω 1) ((dirichletOperator G a ν α)⁻¹ *ᵥ f)

/-- **The global Hölder bound** (GREEN.md G-2(iii) for all pairs, summed; the Hölder part of
G-2(iv)): `|∂ G f|_{(θ),2-θ} ≤ (B/θ) |f|₂`, `B = B(d, L)`. -/
theorem holder_global (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
      (G : GeneratingSet d L N₀ k ϱ)
      {a : ℕ → ℝ} {ν : ℝ}, 0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 →
      IsAdmissibleWeights k a → ∀ {α : G.Ω 1 → ℂ},
      (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      2 * d * Real.log L ≤ agmonRate d / 2 / 2 * (ϱ - 1) → ∀ (f : G.Ω 1 → ℂ) {Cf : ℝ},
      0 ≤ Cf → (∀ x : G.Ω 1, (G.spacing (x : Torus d (N₀ * L ^ k))) ^ 2 * ‖f x‖ ≤ Cf) →
      HolderSeminormLE G (greenSol G a ν α f) θ (2 - θ) (B / θ * Cf) := by
  classical
  obtain ⟨B1, hB1, hpair⟩ := holder_pair_decay (d := d) (L := L) hd hL
  have hcc : 0 ≤ countConst d L (agmonRate d / 2) := tsum_nonneg fun m => by positivity
  refine ⟨B1 * (2 * countConst d L (agmonRate d / 2)), by positivity, ?_⟩
  intro θ hθ0 hθ1 k N₀ _ ϱ G a ν hν0 hν1 ha α hα hϱ f Cf hCf hf
  have hε := agmonRate_pos (d := d) (by omega)
  have hγ0 : 0 < agmonRate d / 2 := by positivity
  have hL3 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hlog : 0 < Real.log L := Real.log_pos hL3
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hϱ1 : 1 < ϱ := by
    by_contra hcon
    push Not at hcon
    have : agmonRate d / 2 / 2 * (ϱ - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have : 0 < 2 * d * Real.log L := by positivity
    linarith
  have hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < (L : ℝ) ^ d), Real.log_pow]
    apply Real.exp_le_exp.2
    have h1 : 0 < ϱ - 1 := by linarith
    have : 0 ≤ agmonRate d / 2 * (ϱ - 1) := by positivity
    nlinarith
  let S : G.Ω 1 → PtSetting G 1 := fun y =>
    { a := a, ν := ν, α := α, f := blockPiece G f y
      j' := G.layerIndex (y : Torus d (N₀ * L ^ k)), y' := y
      hd := hd, hL := hL, hν0 := hν0, hν1 := hν1, ha := ha, hα := hα, hϱ := hϱ1.le, hsep := hsep
      hj'1 := (G.layerIndex_spec y.2).1, hj'k := (G.layerIndex_spec y.2).2.1
      hy' := (G.layerIndex_spec y.2).2.2
      hsupp := by
        intro z hz
        by_contra hne
        exact hz (by simp [blockPiece, hne]) }
  have hfeq : f = ∑ y : G.Ω 1, (siteWeight G y : ℂ) • blockPiece G f y := by
    funext z
    rw [Finset.sum_apply]
    simpa using (sum_siteWeight_blockPiece G f z).symm
  have hu : (dirichletOperator G a ν α)⁻¹ *ᵥ f =
      ∑ y : G.Ω 1, (siteWeight G y : ℂ) • (S y).u := by
    conv_lhs => rw [hfeq]
    rw [Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul]
    exact Finset.sum_congr rfl fun y _ => rfl
  have hut : ∀ p, greenSol G a ν α f p =
      ∑ y : G.Ω 1, (siteWeight G y : ℂ) * (S y).ut p := by
    intro p
    unfold greenSol
    rw [hu]
    simp only [PtSetting.ut, zeroExt]
    split_ifs with h
    · simp [Finset.sum_apply]
    · simp
  -- the data of one piece
  have hMfb : ∀ y : G.Ω 1, ∃ Mf : ℝ, 0 ≤ Mf ∧ (∀ i, ‖(S y).f i‖ ≤ Mf) ∧
      (L : ℝ) ^ (2 * (S y).j') * Mf = Cf := by
    intro y
    obtain ⟨hj1, hjk, hyl⟩ := G.layerIndex_spec y.2
    have hsp : G.spacing (y : Torus d (N₀ * L ^ k)) =
        (L : ℝ) ^ G.layerIndex (y : Torus d (N₀ * L ^ k)) := G.spacing_eq hj1 hjk hyl
    have hLp : (0 : ℝ) < (L : ℝ) ^ G.layerIndex (y : Torus d (N₀ * L ^ k)) := by
      have : (0 : ℝ) < L := by linarith
      positivity
    refine ⟨Cf / ((L : ℝ) ^ G.layerIndex (y : Torus d (N₀ * L ^ k))) ^ 2, by positivity, ?_, ?_⟩
    · intro i
      change ‖blockPiece G f y i‖ ≤ _
      unfold blockPiece
      split_ifs with h
      · have h1 := hf i
        rw [mem_layer_of_blockPiece G y i h, hsp] at h1
        rw [le_div_iff₀ (by positivity)]
        linarith
      · simpa using (by positivity : (0 : ℝ) ≤ Cf / ((L : ℝ) ^ G.layerIndex
          (y : Torus d (N₀ * L ^ k))) ^ 2)
    · change (L : ℝ) ^ (2 * G.layerIndex (y : Torus d (N₀ * L ^ k))) * _ = Cf
      rw [pow_mul']
      field_simp
  intro x hx x' hx'T hne z hz ν'
  have hx'Ω : x' ∈ G.Ω 1 := hx'T.1
  have hρ : (d : ℝ) < ϱ := by
    have := rho_large (S ⟨x, hx⟩)
    linarith
  have hlay := layer_le_of_tildeDelta G hρ hx hx'T
  have hz1 : 1 ≤ ‖z‖ := by
    refine one_le_norm_of_ne_zero ?_
    rintro rfl
    rw [liftPt_zero] at hz
    exact hne hz
  have hz0 : (0 : ℝ) < ‖z‖ := by linarith
  have hsp0 := spacing_pos G (x := x)
  set X : ℝ := (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) with hX
  have hX0 : 0 < X := by positivity
  subst hz
  have hdiff : (greenSol G a ν α f (liftPt x z + Pi.single ν' 1) - greenSol G a ν α f (liftPt x z)) -
      (greenSol G a ν α f (x + Pi.single ν' 1) - greenSol G a ν α f x) =
      ∑ y : G.Ω 1, (siteWeight G y : ℂ) * (((S y).ut (liftPt x z + Pi.single ν' 1) -
        (S y).ut (liftPt x z)) - ((S y).ut (x + Pi.single ν' 1) - (S y).ut x)) := by
    simp_rw [hut, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hpc : ∀ y : G.Ω 1, (G.spacing x) ^ 2 * ‖((S y).ut (liftPt x z + Pi.single ν' 1) -
        (S y).ut (liftPt x z)) - ((S y).ut (x + Pi.single ν' 1) - (S y).ut x)‖ ≤
      B1 / θ * X * ((decay (agmonRate d / 2) (G.pathDist x y) +
        decay (agmonRate d / 2) (G.pathDist (liftPt x z) y)) * Cf) := by
    intro y
    obtain ⟨Mf, hMf0, hMf, hF⟩ := hMfb y
    have := hpair hθ0 hθ1 G (S y) hMf0 hMf hx hx'Ω hlay hz1 rfl ν'
    rw [hF] at this
    exact this
  have hsum := sum_siteWeight_decay_le G hϱ1 hγ0 hϱ hx
  have hsum' := sum_siteWeight_decay_le G hϱ1 hγ0 hϱ hx'Ω
  have hmain : (G.spacing x) ^ 2 * ‖(greenSol G a ν α f (liftPt x z + Pi.single ν' 1) -
      greenSol G a ν α f (liftPt x z)) -
      (greenSol G a ν α f (x + Pi.single ν' 1) - greenSol G a ν α f x)‖ ≤
      B1 / θ * X * (2 * countConst d L (agmonRate d / 2) * Cf) := by
    rw [hdiff]
    calc _ ≤ (G.spacing x) ^ 2 * ∑ y : G.Ω 1, siteWeight G y * ‖((S y).ut (liftPt x z +
          Pi.single ν' 1) - (S y).ut (liftPt x z)) - ((S y).ut (x + Pi.single ν' 1) -
          (S y).ut x)‖ := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) (by positivity)
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (siteWeight_nonneg G _)]
      _ = ∑ y : G.Ω 1, siteWeight G y * ((G.spacing x) ^ 2 * ‖((S y).ut (liftPt x z +
          Pi.single ν' 1) - (S y).ut (liftPt x z)) - ((S y).ut (x + Pi.single ν' 1) -
          (S y).ut x)‖) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ ∑ y : G.Ω 1, siteWeight G y * (B1 / θ * X * ((decay (agmonRate d / 2)
          (G.pathDist x y) + decay (agmonRate d / 2) (G.pathDist (liftPt x z) y)) * Cf)) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hpc y) (siteWeight_nonneg G _)
      _ = B1 / θ * X * Cf * (∑ y : G.Ω 1, siteWeight G y * decay (agmonRate d / 2)
            (G.pathDist x y) + ∑ y : G.Ω 1, siteWeight G y * decay (agmonRate d / 2)
            (G.pathDist (liftPt x z) y)) := by
          rw [← Finset.sum_add_distrib, Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ B1 / θ * X * Cf * (countConst d L (agmonRate d / 2) + countConst d L (agmonRate d / 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add hsum hsum') (by positivity)
      _ = _ := by ring
  -- divide by `X`
  have hsig : (G.spacing x) ^ (2 - θ) * (‖z‖ ^ (1 - θ))⁻¹ = (G.spacing x) ^ 2 / X := by
    rw [hX, Real.rpow_sub hsp0, Real.rpow_two]
    have : 0 < ‖z‖ ^ (1 - θ) := by positivity
    have : 0 < (G.spacing x) ^ θ := by positivity
    field_simp
  rw [hsig, div_mul_eq_mul_div, div_le_iff₀ hX0]
  calc _ ≤ B1 / θ * X * (2 * countConst d L (agmonRate d / 2) * Cf) := hmain
    _ = _ := by ring

/-- **G-2(iv), all four terms in one statement.**  For `|f|₂ ≤ C_f` (that is `ℓ² |f| ≤ C_f` on
`Ω₁`) and `g = ũ`, `u = G_D(α) f`: `|u|₀`, `|∂u|₁` (spacing at either endpoint of a bond),
`|Δ^D u|₂` are `≤ B C_f` and `|∂u|_{(θ),2-θ} ≤ (B/θ) C_f` (equivalently
`B_θ⁻¹ |∂u|_{(θ),2-θ} ≤ B C_f`, `B_θ = B/θ`), with `B = B(d, L)` independent of `θ ∈ (0,1)`,
`k`, the volume, `a`, `ν`, `α`. -/
theorem global_g2iv (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
      (G : GeneratingSet d L N₀ k ϱ)
      {a : ℕ → ℝ} {ν : ℝ}, 0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 →
      IsAdmissibleWeights k a → ∀ {α : G.Ω 1 → ℂ},
      (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      2 * d * Real.log L ≤ agmonRate d / 2 / 2 * (ϱ - 1) → ∀ (f : G.Ω 1 → ℂ) {Cf : ℝ},
      0 ≤ Cf → (∀ x : G.Ω 1, (G.spacing (x : Torus d (N₀ * L ^ k))) ^ 2 * ‖f x‖ ≤ Cf) →
      (∀ {x : Torus d (N₀ * L ^ k)}, x ∈ G.Ω 1 →
        ‖greenSol G a ν α f x‖ ≤ B * Cf ∧
        (∀ μ : Fin d, G.spacing x * ‖greenSol G a ν α f (x + Pi.single μ 1) -
            greenSol G a ν α f x‖ ≤ B * Cf ∧
          (x + Pi.single μ 1 ∈ G.Ω 1 →
            G.spacing (x + Pi.single μ 1) * ‖greenSol G a ν α f (x + Pi.single μ 1) -
              greenSol G a ν α f x‖ ≤ B * Cf)) ∧
        (G.spacing x) ^ 2 * ‖∑ μ : Fin d, (2 * greenSol G a ν α f x -
          greenSol G a ν α f (x + Pi.single μ 1) - greenSol G a ν α f (x - Pi.single μ 1))‖ ≤
          B * Cf) ∧
      HolderSeminormLE G (greenSol G a ν α f) θ (2 - θ) (B / θ * Cf) := by
  obtain ⟨B1, hB1, hG⟩ := global_bound (d := d) (L := L) hd hL
  obtain ⟨B2, hB2, hH⟩ := holder_global (d := d) (L := L) hd hL
  refine ⟨B1 + B2, by positivity, ?_⟩
  intro θ hθ0 hθ1 k N₀ _ ϱ G a ν hν0 hν1 ha α hα hϱ f Cf hCf hf
  refine ⟨fun {x} hx => ?_, ?_⟩
  · have h := hG G hν0 hν1 ha hα hϱ f hCf hf hx
    have hm : B1 * Cf ≤ (B1 + B2) * Cf := by nlinarith
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1.trans hm, fun μ => ⟨(h2 μ).1.trans hm, fun hx' => ((h2 μ).2 hx').trans hm⟩,
      h3.trans hm⟩
  · have h := hH hθ0 hθ1 G hν0 hν1 ha hα hϱ f hCf hf
    intro x hx x' hx' hne z hz ν'
    refine (h x hx x' hx' hne z hz ν').trans ?_
    have : B2 / θ * Cf ≤ (B1 + B2) / θ * Cf := by
      apply mul_le_mul_of_nonneg_right _ hCf
      exact div_le_div_of_nonneg_right (by linarith) hθ0.le
    exact this

end Balaban.Multiscale
