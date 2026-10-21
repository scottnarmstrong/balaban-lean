/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelTowerFamily
public import Balaban.Inhabited.StepTowerCollarScales

/-!
# The conditions on constants of the new level on the local generating sets (route R-LOC, L5)

`StepTowerG.newLevel_localFamily_of_class` (the clauses (A1)–(A5) of the new level at a step of a
tower) takes, besides the class and the chain, conditions on the constants of the step: the numerics
of the new level `NewLevelNumerics`, the radii `c_ψ, r, R₁, R, U` of the zero-source and bridge marks
with the smallness `hsmZ` of the zero-source bound, the marked radius of the old terms (`hca`), the
smallness of the class constants against the cap of Theorem 3.4 (`hsmO`), and the (DL-gap) of the
charts of the old terms at their birth masses.  Here they are shown to hold together with the
constants of the class chain:

* the base tower: `exists_collarBase_newLevel` — a tower `T₀` with `CollarBase` (the chain's
  constants), the closeness ratio `K₂ Q ≤ θ` for any `θ > 0` and `NewLevelNumerics`;
  `NewLevelNumerics.nonempty_scale` carries the numerics to the towers `T_k` of smaller radius;
* the radii, for `β ≥ β₀` uniformly in the scale `k`: every condition reduces to
  `K p₁^n ≤ c₀ L^{-α(k+1)} √β_k` (`n = 1, 3`, `α = (d-2)/2 - γ`, `β_k = β L^{k(d-2)}`,
  `p₁ ≤ A₁ (log β_k)^p`), which holds for `β ≥ β₀` at every `k` since
  `L^{-α(k+1)} √β_k = L^{-α} β^{1/2-s} β_k^s`, `s = γ/(d-2)` (`exists_beta_pLog_pow_le`);
  `newLevel_radii_of` (the radii and `hsmZ`, through `energyBdScaled_le_step`),
  `newLevel_markedRad_of` (`hmr`, `hca`, `hsmO`);
* the (DL-gap) `(2E + 2(N+1)K₂E²)(1 + 2 K_m τ₁) ≤ ε_j`, `E = t + K₂ δ₃ + K₂ δ_fl`: with the chain's
  radii `E ≤ λ ε_k (q (1 + K₂ Q) + (1 - q)/4)`, so it holds when this factor is at most `2/5`
  (`L^{-α} ≤ 1/16`, `K₂ Q ≤ 1/16`, `λ ≤ 17/16`: `L` large, the block of the tower large, `r₀`
  small), `(N + 1) K₂ ε₁ ≤ 1/8` (`α₀` small) and `2 K_m τ₁ ≤ 1/9` (the flow constant `c₈` small)
  (`newLevel_dlGap`);
* `exists_newLevelConstants`: all of these at once.

The lower bound on `L` is `L^{(d-2)/2 - γ} ≥ 16`; it is the only new condition on `L` (Root-F chooses
`L`), and it is compatible with the ties of `PrefixInput` (which bound `L` from below only).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.Inhabited.MarkBudgetAudit
  Balaban.Inhabited.LevelStep Filter Topology

section Asymptotic

/-- The exponent identity `L^{-α(k+1)} √(β L^{k(d-2)}) = L^{-α} β^{1/2-s} (β L^{k(d-2)})^s` with
`α = (d-2)/2 - γ`, `s = γ/(d-2)`. -/
theorem scale_sqrt_eq {d L : ℕ} (hd : 3 ≤ d) (hL : 1 ≤ L) {β γ : ℝ} (hβ : 0 < β) (k : ℕ) :
    (L : ℝ) ^ (-((((d : ℝ) - 2) / 2 - γ) * ((k : ℝ) + 1))) *
        Real.sqrt (β * (L : ℝ) ^ (k * (d - 2))) =
      (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) * β ^ (1 / 2 - γ / ((d : ℝ) - 2)) *
        (β * (L : ℝ) ^ (k * (d - 2))) ^ (γ / ((d : ℝ) - 2)) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hD : (1 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set D : ℝ := (d : ℝ) - 2 with hDdef
  have hD0 : D ≠ 0 := by linarith
  have hX0 : (0 : ℝ) < (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hX : (L : ℝ) ^ (k * (d - 2)) = (L : ℝ) ^ ((k : ℝ) * D) := by
    rw [← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [Real.sqrt_eq_rpow, Real.mul_rpow hβ.le hX0.le, Real.mul_rpow hβ.le hX0.le, hX,
    ← Real.rpow_mul hL0.le, ← Real.rpow_mul hL0.le]
  have hsplit : β ^ (1 / 2 : ℝ) = β ^ (1 / 2 - γ / D) * β ^ (γ / D) := by
    rw [← Real.rpow_add hβ]; ring_nf
  rw [hsplit]
  have hLsplit : (L : ℝ) ^ ((k : ℝ) * D * (1 / 2)) =
      (L : ℝ) ^ ((((d : ℝ) - 2) / 2 - γ) * k) * (L : ℝ) ^ ((k : ℝ) * D * (γ / D)) := by
    rw [← Real.rpow_add hL0]
    congr 1
    have e : (k : ℝ) * D * (γ / D) = k * γ := by field_simp
    rw [e, hDdef]; ring
  rw [hLsplit]
  have hLk : (L : ℝ) ^ (-((((d : ℝ) - 2) / 2 - γ) * ((k : ℝ) + 1))) *
      (L : ℝ) ^ ((((d : ℝ) - 2) / 2 - γ) * k) = (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) := by
    rw [← Real.rpow_add hL0]
    congr 1
    ring
  calc (L : ℝ) ^ (-((((d : ℝ) - 2) / 2 - γ) * ((k : ℝ) + 1))) *
        (β ^ (1 / 2 - γ / D) * β ^ (γ / D) *
          ((L : ℝ) ^ ((((d : ℝ) - 2) / 2 - γ) * k) * (L : ℝ) ^ ((k : ℝ) * D * (γ / D))))
      = ((L : ℝ) ^ (-((((d : ℝ) - 2) / 2 - γ) * ((k : ℝ) + 1))) *
          (L : ℝ) ^ ((((d : ℝ) - 2) / 2 - γ) * k)) * β ^ (1 / 2 - γ / D) *
          (β ^ (γ / D) * (L : ℝ) ^ ((k : ℝ) * D * (γ / D))) := by ring
    _ = _ := by rw [hLk]

/-- **The scale-uniform threshold for the logarithmic radius.**  For `d ≥ 3`, `L ≥ 1`,
`0 < γ < 1/2`, `α = (d-2)/2 - γ`, every `n`, `K ≥ 0` and `c₀ > 0` there is `β₀ ≥ 1` such that for
`β ≥ β₀`, every scale `k` and every `0 ≤ p₁ ≤ A₁ (log β_k)^p`, `β_k = β L^{k(d-2)}`:
`K p₁^n ≤ c₀ L^{-α(k+1)} √β_k`. -/
theorem exists_beta_pLog_pow_le {d L : ℕ} (hd : 3 ≤ d) (hL : 1 ≤ L) {A₁ : ℝ} (hA : 0 ≤ A₁)
    (p n : ℕ) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1 / 2) {K c₀ : ℝ} (hK : 0 ≤ K) (hc₀ : 0 < c₀) :
    ∃ β₀ : ℝ, 1 ≤ β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ k : ℕ, ∀ p₁ : ℝ, 0 ≤ p₁ →
      p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      K * p₁ ^ n ≤ c₀ * ((L : ℝ) ^ (-((((d : ℝ) - 2) / 2 - γ) * ((k : ℝ) + 1))) *
        Real.sqrt (β * (L : ℝ) ^ (k * (d - 2)))) := by
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hD : (1 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set s : ℝ := γ / ((d : ℝ) - 2) with hs
  have hs0 : 0 < s := div_pos hγ0 (by linarith)
  have hs1 : s ≤ γ := div_le_self hγ0.le hD
  have he0 : 0 < 1 / 2 - s := by linarith
  set Cl : ℝ := (((p * n : ℕ) : ℝ) / s) ^ (p * n) with hCl
  have hCl0 : 0 ≤ Cl := by positivity
  set Y : ℝ := K * (A₁ ^ n * Cl) * (L : ℝ) ^ (((d : ℝ) - 2) / 2 - γ) / c₀ with hY
  have hY0 : 0 ≤ Y := by positivity
  refine ⟨max 1 (Y ^ (1 / (1 / 2 - s))), le_max_left _ _, fun β hβ k p₁ hp0 hp => ?_⟩
  have hβ1 : 1 ≤ β := (le_max_left _ _).trans hβ
  have hβ0 : 0 < β := by linarith
  have hX1 : (1 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := one_le_pow₀ (by exact_mod_cast hL)
  set b : ℝ := β * (L : ℝ) ^ (k * (d - 2)) with hb
  have hb1 : 1 ≤ b := by nlinarith
  have hb0 : 0 < b := by linarith
  -- the logarithmic radius against `b^s`
  have hlog : Real.log b ^ (p * n) ≤ Cl * b ^ s := by
    rcases Nat.eq_zero_or_pos (p * n) with h0 | h0
    · rw [hCl, h0]
      simp only [pow_zero, one_mul]
      exact Real.one_le_rpow hb1 hs0.le
    · exact Balaban.Fluctuation.log_pow_le_rpow hb1 hs0 h0
  have hpL : 0 ≤ pLog A₁ p b := pLog_nonneg hA p hb1
  have hpn : p₁ ^ n ≤ A₁ ^ n * (Cl * b ^ s) := by
    calc p₁ ^ n ≤ (pLog A₁ p b) ^ n := pow_le_pow_left₀ hp0 hp n
      _ = A₁ ^ n * Real.log b ^ (p * n) := by unfold pLog; rw [mul_pow, ← pow_mul]
      _ ≤ A₁ ^ n * (Cl * b ^ s) := mul_le_mul_of_nonneg_left hlog (by positivity)
  -- the threshold
  have hβY : Y ≤ β ^ (1 / 2 - s) := by
    have h1 : Y ^ (1 / (1 / 2 - s)) ≤ β := (le_max_right _ _).trans hβ
    have h2 := Real.rpow_le_rpow (by positivity) h1 he0.le
    rwa [← Real.rpow_mul hY0, one_div_mul_cancel he0.ne', Real.rpow_one] at h2
  rw [scale_sqrt_eq hd hL hβ0 k]
  have hLa : 0 < (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) := Real.rpow_pos_of_pos hL0 _
  have hLa' : (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) * (L : ℝ) ^ (((d : ℝ) - 2) / 2 - γ) = 1 := by
    rw [← Real.rpow_add hL0]; simp
  have hbs : 0 ≤ b ^ s := (Real.rpow_pos_of_pos hb0 _).le
  have key : K * (A₁ ^ n * Cl) ≤ c₀ * ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) * β ^ (1 / 2 - s)) := by
    have h3 : K * (A₁ ^ n * Cl) = c₀ * (L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) * Y := by
      rw [hY]
      calc K * (A₁ ^ n * Cl) = K * (A₁ ^ n * Cl) * ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) *
            (L : ℝ) ^ (((d : ℝ) - 2) / 2 - γ)) * (c₀ / c₀) := by
            rw [hLa', div_self hc₀.ne']; ring
        _ = _ := by ring
    rw [h3, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hβY hLa.le) hc₀.le
  calc K * p₁ ^ n ≤ K * (A₁ ^ n * (Cl * b ^ s)) := mul_le_mul_of_nonneg_left hpn hK
    _ = K * (A₁ ^ n * Cl) * b ^ s := by ring
    _ ≤ c₀ * ((L : ℝ) ^ (-(((d : ℝ) - 2) / 2 - γ)) * β ^ (1 / 2 - s)) * b ^ s :=
        mul_le_mul_of_nonneg_right key hbs
    _ = _ := by ring

end Asymptotic

section Radii

/-- **The block energy of the zero-source marks at the step's radii**: with `V = c t`, `δ = t`,
`a_k ≤ 2`, `energyBdScaled ≤ L^d L^{k(d-2)} t² (N (1 + c)² + (d + 1 + ρ) N c² / 2)`. -/
theorem energyBdScaled_le_step {d L N : ℕ} [NeZero L] (hd : 2 ≤ d) {a : ℕ → ℝ} {k : ℕ}
    (ha : a k ≤ 2) {c t ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) :
    energyBdScaled d L N a k (c * t) t ρ ≤
      (L : ℝ) ^ d * (L : ℝ) ^ (k * (d - 2)) * t ^ 2 *
        ((N : ℝ) * (1 + c) ^ 2 + ((d : ℝ) + 1 + ρ) * N * c ^ 2 / 2) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hL0 : (0 : ℝ) < L := by linarith
  set x : ℝ := (L : ℝ) ^ k with hx
  have hx0 : 0 < x := by positivity
  have hy : (L : ℝ) ^ (k + 1) = x * L := by rw [hx, pow_succ]
  have hxd : x ^ d = (L : ℝ) ^ (k * (d - 2)) * x ^ 2 := by
    have e : k * d = k * (d - 2) + k * 2 := by rw [← Nat.mul_add, Nat.sub_add_cancel hd]
    rw [hx, ← pow_mul, ← pow_mul, ← pow_add, e]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hX : (0 : ℝ) ≤ (L : ℝ) ^ (k * (d - 2)) := by positivity
  have hLd : (0 : ℝ) ≤ (L : ℝ) ^ d := by positivity
  have hL2 : 1 ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
  unfold energyBdScaled
  rw [hy, mul_pow, hxd]
  have e : (L : ℝ) ^ (k * (d - 2)) * x ^ 2 * (L : ℝ) ^ d *
      ((1 / 2) * (a k / x ^ 2) * (N * (t + c * t) * (t + c * t)) +
        (1 / 2) * (d * (N * (c * t / x) * (c * t / x)) +
          ((1 + ρ) / (x * L) ^ 2) * (N * (c * t) * (c * t)))) =
      (L : ℝ) ^ d * (L : ℝ) ^ (k * (d - 2)) * t ^ 2 *
        ((1 / 2) * a k * N * (1 + c) ^ 2 + (1 / 2) * (d * N * c ^ 2 +
          (1 + ρ) / (L : ℝ) ^ 2 * N * c ^ 2)) := by
    field_simp
  rw [e]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h1 : (1 + ρ) / (L : ℝ) ^ 2 ≤ 1 + ρ := div_le_self (by linarith) hL2
  have h2 : (1 / 2) * a k * N * (1 + c) ^ 2 ≤ N * (1 + c) ^ 2 := by
    have : 0 ≤ (N : ℝ) * (1 + c) ^ 2 := by positivity
    nlinarith
  have h3 : (1 + ρ) / (L : ℝ) ^ 2 * N * c ^ 2 ≤ (1 + ρ) * N * c ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hN) (sq_nonneg c)
  nlinarith

/-- The constant of the zero-source smallness `hsmZ` of the new level at the block exponent `m₁`, the
fluctuation constant `c = K₂'` and `ρ = ρ₄`: `24 c₁ (L^{1+m₁})^d L^d C_E (16 √N (C_max + 1))³`,
`C_E = N (1 + c)² + (d + 1 + ρ) N c² / 2`. -/
noncomputable def zeroSourceConst (d L N m₁ : ℕ) (κ c ρ : ℝ) : ℝ :=
  24 * c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d * (L : ℝ) ^ d *
    ((N : ℝ) * (1 + c) ^ 2 + ((d : ℝ) + 1 + ρ) * N * c ^ 2 / 2) *
    (16 * Real.sqrt N * (covSupMaxC d L N κ + 1)) ^ 3

theorem zeroSourceConst_nonneg {d L N m₁ : ℕ} [NeZero L] {κ c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (hd : 0 < d)
    (hL : 3 ≤ L) : 0 ≤ zeroSourceConst d L N m₁ κ c ρ := by
  have := covSupMaxC_nonneg_general (N := N) hd hL κ
  have := one_le_c1 d L
  unfold zeroSourceConst
  positivity

/-- **The radii of the zero-source and bridge marks of the new level.**  At a step of radius `t`,
coupling `β`, block coupling `b = β L^{k(d-2)}` and cutoff radius `p₁`, if
`64 √N (C_max + 1) p₁ ≤ t √b` and `K_Z p₁³ ≤ cap · t √b` (`K_Z = zeroSourceConst`), the radii
`c_ψ = t √b/(8 √N (C_max + 1))`, `r = c_ψ/(2 p₁)`, `R₁ = 2`, `R = 17/8`, `U = 17/16` satisfy the
radius conditions of the zero-source and bridge marks and the smallness `hsmZ` against `cap`. -/
theorem newLevel_radii_of {d L N : ℕ} [NeZero L] [NeZero N] (hd : 3 ≤ d) (hL : 3 ≤ L)
    {κ BG BG₂ t β b p₁ cap : ℝ} {k m₁ : ℕ} (hk : 1 ≤ k) (ht : 0 < t) (hβ : 0 < β)
    (hb : b = β * (L : ℝ) ^ (k * (d - 2))) (hp : 0 < p₁) (hBG₂ : 0 ≤ famConst d L BG₂ κ)
    (hρ : 0 ≤ rho4 d L N BG κ)
    (h1 : 64 * Real.sqrt N * (covSupMaxC d L N κ + 1) * p₁ ≤ t * Real.sqrt b)
    (h3 : zeroSourceConst d L N m₁ κ (cK2' d L N (famConst d L BG₂ κ)) (rho4 d L N BG κ) *
      p₁ ^ 3 ≤ cap * (t * Real.sqrt b)) :
    ∃ cψ r R₁ R U : ℝ, 0 ≤ cψ ∧ 2 * p₁ ≤ cψ ∧
      corrU * markedRad d L N k 1 κ cψ (((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < t ∧ 1 < R₁ ∧ 0 < r ∧
      (2 * R₁ + r) * p₁ ≤ cψ ∧ 0 < R ∧
      (R + R) * markedRad d L N k 1 κ cψ (((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) < t ∧ 2 * U ≤ R ∧
      17 / 16 ≤ U ∧
      8 * (|β| * (6 * (1 / 2) * c1 d L * ((L : ℝ) ^ (1 + m₁)) ^ d *
        ‖energyBdScaled d L N (compWeight L 1) k (cK2' d L N (famConst d L BG₂ κ) * t) t
          (rho4 d L N BG κ)‖ / r ^ 3)) ≤ cap := by
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hb0 : 0 < b := by rw [hb]; positivity
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  have hsN : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
  set C : ℝ := covSupMaxC d L N κ + 1 with hC
  have hC1 : 1 ≤ C := by have := covSupMaxC_nonneg_general (N := N) hd0 hL κ; linarith
  set X : ℝ := t * Real.sqrt b with hX
  have hX0 : 0 < X := mul_pos ht hsb
  set cψ : ℝ := X / (8 * Real.sqrt N * C) with hcψ
  have hcψ0 : 0 < cψ := by positivity
  have h8 : 8 * p₁ ≤ cψ := by
    rw [hcψ, le_div_iff₀ (by positivity)]; nlinarith
  set r : ℝ := cψ / (2 * p₁) with hr
  have hr0 : 0 < r := by positivity
  -- the marked radius at `c_ψ`
  have hmem := compWeight_one_mem hL hk
  set Ck : ℝ := covSupConstC d L N (compWeight L (1 : ℝ) k) κ with hCk
  have hCk0 : 0 ≤ Ck := covSupConstC_nonneg hd0 hL (by linarith [hmem.1]) κ
  have hCkC : Ck ≤ C - 1 := by
    have := covSupConstC_le_covSupMaxC (N := N) hd0 hL κ hmem
    linarith
  have hamp : ‖(((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ = (Real.sqrt b)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hb0.le _),
      Real.rpow_neg hb0.le, ← Real.sqrt_eq_rpow]
  have hmR : markedRad d L N k 1 κ cψ (((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) = Ck * t / (8 * C) := by
    show Real.sqrt N * (‖(((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ * (Ck * cψ)) = Ck * t / (8 * C)
    rw [hamp, hcψ, hX]
    field_simp
  have hmR8 : markedRad d L N k 1 κ cψ (((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ≤ t / 8 := by
    rw [hmR, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨cψ, r, 2, 17 / 8, 17 / 16, hcψ0.le, by linarith, ?_, by norm_num, hr0, ?_, by norm_num,
    ?_, by norm_num, le_rfl, ?_⟩
  · unfold corrU; nlinarith
  · have e : (2 * 2 + r) * p₁ = 4 * p₁ + cψ / 2 := by rw [hr]; field_simp; ring
    rw [e]; linarith
  · nlinarith
  · -- the zero-source smallness
    have hEB := energyBdScaled_le_step (d := d) (L := L) (N := N) (by omega) (k := k)
      hmem.2 (c := cK2' d L N (famConst d L BG₂ κ))
      (ρ := rho4 d L N BG κ) (cK2'_nonneg hBG₂) hρ (t := t)
    have hc0 : 0 ≤ cK2' d L N (famConst d L BG₂ κ) := cK2'_nonneg hBG₂
    have hEB0 : 0 ≤ energyBdScaled d L N (compWeight L 1) k
        (cK2' d L N (famConst d L BG₂ κ) * t) t (rho4 d L N BG κ) :=
      energyBdScaled_nonneg (by linarith [hmem.1]) (by positivity) ht.le hρ
    rw [Real.norm_of_nonneg hEB0, abs_of_pos hβ]
    set c := cK2' d L N (famConst d L BG₂ κ) with hc
    set ρ := rho4 d L N BG κ with hρdef
    set CE : ℝ := (N : ℝ) * (1 + c) ^ 2 + ((d : ℝ) + 1 + ρ) * N * c ^ 2 / 2 with hCE
    have hCE0 : 0 ≤ CE := by positivity
    have hc1 := one_le_c1 d L
    set Lm : ℝ := ((L : ℝ) ^ (1 + m₁)) ^ d with hLm
    have hLm0 : 0 ≤ Lm := by positivity
    have hbt : β * ((L : ℝ) ^ (k * (d - 2)) * t ^ 2) = X ^ 2 := by
      rw [hX, mul_pow, Real.sq_sqrt hb0.le, hb]; ring
    have hr3 : r ^ 3 = X ^ 3 / (16 * Real.sqrt N * C) ^ 3 / p₁ ^ 3 := by
      rw [hr, hcψ]; field_simp; ring
    have hKZ : zeroSourceConst d L N m₁ κ c ρ =
        24 * c1 d L * Lm * (L : ℝ) ^ d * CE * (16 * Real.sqrt N * C) ^ 3 := by
      rw [zeroSourceConst, hCE, hC, hLm]
    calc 8 * (β * (6 * (1 / 2) * c1 d L * Lm * energyBdScaled d L N (compWeight L 1) k (c * t) t ρ /
          r ^ 3))
        ≤ 8 * (β * (6 * (1 / 2) * c1 d L * Lm *
            ((L : ℝ) ^ d * (L : ℝ) ^ (k * (d - 2)) * t ^ 2 * CE) / r ^ 3)) := by
          gcongr
      _ = zeroSourceConst d L N m₁ κ c ρ * p₁ ^ 3 / X := by
          rw [hKZ, hr3]
          have e2 : β * (6 * (1 / 2) * c1 d L * Lm *
              ((L : ℝ) ^ d * (L : ℝ) ^ (k * (d - 2)) * t ^ 2 * CE)) =
              3 * c1 d L * Lm * (L : ℝ) ^ d * CE * (β * ((L : ℝ) ^ (k * (d - 2)) * t ^ 2)) := by
            ring
          rw [mul_div_assoc', e2, hbt]
          field_simp
          ring
      _ ≤ cap := by
          rw [div_le_iff₀ hX0]; exact h3

/-- **The marked radius of the old terms and the smallness of the class constants.**  If
`64 √N (C_max + 1) p₁ ≤ m t √b` and `3 √N (C_max + 1) K_O p₁ ≤ cap · m t √b`, then for every
`δ₁ ≥ m t` the marked radius at `p₁` is positive, `corrU ≤ δ₁/(2 markedRad)` (`hca`) and
`corrU/(δ₁/(2 markedRad)) · K_O ≤ cap` (`hsmO`). -/
theorem newLevel_markedRad_of {d L N : ℕ} [NeZero L] [NeZero N] (hd : 3 ≤ d) (hL : 3 ≤ L)
    {κ t b p₁ δ₁ m cap KO : ℝ} {k : ℕ} (hk : 1 ≤ k) (ht : 0 < t) (hb : 0 < b) (hp : 0 < p₁)
    (hm : 0 < m) (hδ : m * t ≤ δ₁) (hcap : 0 < cap) (hKO : 0 ≤ KO)
    (h1 : 64 * Real.sqrt N * (covSupMaxC d L N κ + 1) * p₁ ≤ m * (t * Real.sqrt b))
    (h2 : 3 * Real.sqrt N * (covSupMaxC d L N κ + 1) * KO * p₁ ≤ cap * (m * (t * Real.sqrt b))) :
    0 < markedRad d L N k 1 κ p₁ (((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ∧
      corrU ≤ δ₁ / (2 * markedRad d L N k 1 κ p₁ (((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) ∧
      corrU / (δ₁ / (2 * markedRad d L N k 1 κ p₁ (((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)))) * KO ≤
        cap := by
  have hd0 : 0 < d := by omega
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsN : 0 < Real.sqrt (N : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
  set C : ℝ := covSupMaxC d L N κ + 1 with hC
  have hC1 : 1 ≤ C := by have := covSupMaxC_nonneg_general (N := N) hd0 hL κ; linarith
  have hmem := compWeight_one_mem hL hk
  set Ck : ℝ := covSupConstC d L N (compWeight L (1 : ℝ) k) κ with hCk
  have hCk0 : 0 < Ck := covSupConstC_pos hd0 hL (by linarith [hmem.1]) κ
  have hCkC : Ck ≤ C - 1 := by
    have := covSupConstC_le_covSupMaxC (N := N) hd0 hL κ hmem
    linarith
  have hamp : ‖(((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ = (Real.sqrt b)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hb.le _),
      Real.rpow_neg hb.le, ← Real.sqrt_eq_rpow]
  have hmR : markedRad d L N k 1 κ p₁ (((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) =
      Real.sqrt N * Ck * p₁ / Real.sqrt b := by
    show Real.sqrt N * (‖(((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))‖ * (Ck * p₁)) = _
    rw [hamp]; field_simp
  have hmR0 : 0 < markedRad d L N k 1 κ p₁ (((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
    rw [hmR]; positivity
  -- `2 corrU markedRad ≤ m t`
  have hle : 2 * corrU * markedRad d L N k 1 κ p₁ (((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) ≤ m * t := by
    rw [hmR, corrU, mul_div_assoc', div_le_iff₀ hsb]
    have : Real.sqrt N * Ck * p₁ ≤ Real.sqrt N * C * p₁ := by
      have := mul_le_mul_of_nonneg_left (by linarith : Ck ≤ C) hsN.le
      exact mul_le_mul_of_nonneg_right this hp.le
    nlinarith
  have hδ0 : 0 < δ₁ := lt_of_lt_of_le (mul_pos hm ht) hδ
  have hcu := corrU_pos
  refine ⟨hmR0, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    linarith
  · rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hδ0]
    have h3 : corrU * (2 * markedRad d L N k 1 κ p₁ (((b ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) * KO ≤
        3 * Real.sqrt N * C * KO * p₁ / Real.sqrt b := by
      rw [hmR, corrU]
      rw [le_div_iff₀ hsb]
      have e : 17 / 16 * (2 * (Real.sqrt ↑N * Ck * p₁ / Real.sqrt b)) * KO * Real.sqrt b =
          17 / 8 * Real.sqrt ↑N * Ck * p₁ * KO := by field_simp; ring
      rw [e]
      have : Real.sqrt N * Ck * p₁ * KO ≤ Real.sqrt N * C * p₁ * KO := by
        have := mul_le_mul_of_nonneg_left (by linarith : Ck ≤ C) hsN.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hp.le) hKO
      have h0 : 0 ≤ Real.sqrt N * C * p₁ * KO := by positivity
      nlinarith
    have h4 : 3 * Real.sqrt N * C * KO * p₁ / Real.sqrt b ≤ cap * (m * t) := by
      rw [div_le_iff₀ hsb]; nlinarith
    have h5 : cap * (m * t) ≤ cap * δ₁ := mul_le_mul_of_nonneg_left hδ hcap.le
    linarith

end Radii

section DLGap

/-- **The (DL-gap) at the chain's radii.**  For the class radii `ε` (antitone, positive, with
`ε_{k+1} ≤ q ε_k`), the radii of the chain `t = λ ε_{k+1}`, `δ₃ = Q t`,
`δ_fl = F min(t, η λ ε_k)` with `K₂ F η = (1 - q)/4`, if `λ (q (1 + K₂ Q) + (1 - q)/4) ≤ 2/5`,
`(N + 1) K ε₁ ≤ 1/8` and `(1 + 16 (N + 1) K) 2τ ≤ 1/9`, then
`(2E + 2(N + 1) K E²)(1 + (1 + 16 (N + 1) K) 2τ) ≤ ε_j` for every `1 ≤ j ≤ k`,
`E = t + K₂ δ₃ + K₂ δ_fl`. -/
theorem newLevel_dlGap {N : ℕ} {ε : ℕ → ℝ} (hε : Antitone ε) (hpos : ∀ j, 0 < ε j) {k : ℕ}
    (hk : 1 ≤ k) {q lam K₂ K Q F η τ t : ℝ} (hgap : ε (k + 1) ≤ q * ε k)
    (hK₂ : 0 ≤ K₂) (hQ : 0 ≤ Q) (hF : 0 ≤ F) (hη : 0 ≤ η) (hlam : 0 ≤ lam)
    (ht : t = lam * ε (k + 1)) (hKFη : K₂ * F * η = (1 - q) / 4)
    (hρ : lam * (q * (1 + K₂ * Q) + (1 - q) / 4) ≤ 2 / 5) (hK : 0 ≤ K)
    (hquad : ((N : ℝ) + 1) * K * ε 1 ≤ 1 / 8)
    (hτ : (1 + 16 * ((N : ℝ) + 1) * K) * (2 * τ) ≤ 1 / 9) :
    ∀ j, 1 ≤ j → j ≤ k →
      (2 * (t + K₂ * (Q * t) + K₂ * (F * min t (η * (lam * ε k)))) + 2 * ((N : ℝ) + 1) *
        (K * (t + K₂ * (Q * t) + K₂ * (F * min t (η * (lam * ε k)))) ^ 2)) *
        (1 + (1 + 16 * ((N : ℝ) + 1) * K) * (2 * τ)) ≤ ε j := by
  intro j hj1 hjk
  set E : ℝ := t + K₂ * (Q * t) + K₂ * (F * min t (η * (lam * ε k))) with hE
  have hk0 := hpos k
  have ht0 : 0 ≤ t := by rw [ht]; exact mul_nonneg hlam (hpos _).le
  have hmin0 : 0 ≤ min t (η * (lam * ε k)) := le_min ht0 (by positivity)
  have hE0 : 0 ≤ E := by positivity
  -- `E ≤ (2/5) ε_k`
  have hmin : min t (η * (lam * ε k)) ≤ η * (lam * ε k) := min_le_right _ _
  have hE1 : E ≤ lam * (q * (1 + K₂ * Q) + (1 - q) / 4) * ε k := by
    have h1 : K₂ * (F * min t (η * (lam * ε k))) ≤ K₂ * F * η * (lam * ε k) := by
      have := mul_le_mul_of_nonneg_left hmin (mul_nonneg hK₂ hF)
      nlinarith
    have h2 : t * (1 + K₂ * Q) ≤ lam * (q * ε k) * (1 + K₂ * Q) := by
      rw [ht]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgap hlam)
        (by positivity)
    rw [hKFη] at h1
    calc E = t * (1 + K₂ * Q) + K₂ * (F * min t (η * (lam * ε k))) := by rw [hE]; ring
      _ ≤ lam * (q * ε k) * (1 + K₂ * Q) + (1 - q) / 4 * (lam * ε k) := add_le_add h2 h1
      _ = _ := by ring
  have hE2 : E ≤ 2 / 5 * ε k := hE1.trans (mul_le_mul_of_nonneg_right hρ hk0.le)
  -- the quadratic term
  have hεk1 : ε k ≤ ε 1 := hε hk
  have hq1 : ((N : ℝ) + 1) * K * E ≤ 1 / 20 := by
    have hNK : 0 ≤ ((N : ℝ) + 1) * K := by positivity
    calc ((N : ℝ) + 1) * K * E ≤ ((N : ℝ) + 1) * K * (2 / 5 * ε 1) :=
          mul_le_mul_of_nonneg_left (hE2.trans (by nlinarith)) hNK
      _ = 2 / 5 * (((N : ℝ) + 1) * K * ε 1) := by ring
      _ ≤ 2 / 5 * (1 / 8) := by nlinarith
      _ = 1 / 20 := by norm_num
  have hA : 2 * E + 2 * ((N : ℝ) + 1) * (K * E ^ 2) ≤ 21 / 25 * ε k := by
    have : 2 * E + 2 * ((N : ℝ) + 1) * (K * E ^ 2) = 2 * E * (1 + ((N : ℝ) + 1) * K * E) := by
      ring
    rw [this]
    have h1 : 2 * E * (1 + ((N : ℝ) + 1) * K * E) ≤ 2 * E * (21 / 20) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hB0 : 0 ≤ 2 * E + 2 * ((N : ℝ) + 1) * (K * E ^ 2) := by positivity
  calc (2 * E + 2 * ((N : ℝ) + 1) * (K * E ^ 2)) * (1 + (1 + 16 * ((N : ℝ) + 1) * K) * (2 * τ))
      ≤ (2 * E + 2 * ((N : ℝ) + 1) * (K * E ^ 2)) * (1 + 1 / 9) :=
        mul_le_mul_of_nonneg_left (by linarith) hB0
    _ ≤ 21 / 25 * ε k * (1 + 1 / 9) := mul_le_mul_of_nonneg_right hA (by norm_num)
    _ ≤ ε k := by nlinarith
    _ ≤ ε j := hε hjk

/-- The factor `λ (q (1 + K₂ Q) + (1 - q)/4)` of the (DL-gap) is at most `2/5` when
`q ≤ 1/16`, `K₂ Q ≤ 1/16` and `λ ≤ 17/16`. -/
theorem dlGap_factor_le {q lam KQ : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 16) (hKQ0 : 0 ≤ KQ)
    (hKQ : KQ ≤ 1 / 16) (hlam : lam ≤ 17 / 16) :
    lam * (q * (1 + KQ) + (1 - q) / 4) ≤ 2 / 5 := by
  have h1 : q * (1 + KQ) ≤ 1 / 16 * (17 / 16) := by
    have := mul_le_mul hq (by linarith : 1 + KQ ≤ 17 / 16) (by linarith) (by norm_num)
    linarith
  have h2 : q * (1 + KQ) + (1 - q) / 4 ≤ 1 / 16 * (17 / 16) + 1 / 4 := by linarith
  have h3 : 0 ≤ q * (1 + KQ) + (1 - q) / 4 := by nlinarith
  calc lam * (q * (1 + KQ) + (1 - q) / 4) ≤ 17 / 16 * (1 / 16 * (17 / 16) + 1 / 4) :=
        mul_le_mul hlam h2 h3 (by norm_num)
    _ ≤ 2 / 5 := by norm_num

end DLGap

section Tower

/-- **`NewLevelNumerics` at a smaller step radius**: the numerics at `(t, ε′)` give the numerics at
`(l t, l ε′)`, `0 < l ≤ 1` (`ChainNum.scale`, `FlNum.scale`; the margins of the covariance chart are
monotone in the radius). -/
theorem NewLevelNumerics.nonempty_scale {d L N m₁ : ℕ} [NeZero L]
    {c BG κ t c₂ BG₂ δc r₀ eps' l : ℝ}
    (h : NewLevelNumerics d L N m₁ c BG κ t c₂ BG₂ δc r₀ eps') (hd : 0 < d) (hBG : 0 ≤ BG)
    (hBG₂ : 0 ≤ BG₂) (hl0 : 0 < l) (hl1 : l ≤ 1) :
    Nonempty (NewLevelNumerics d L N m₁ c BG κ (l * t) c₂ BG₂ δc r₀ (l * eps')) := by
  have he := h.chain'.eps_pos
  have hδ₃ := h.chain'.δ₃_nn
  have hX : 0 ≤ xiC1 d := le_trans zero_le_one (one_le_xiC1 d)
  have hK4 : 0 ≤ K4 d L N BG κ := (K4_pos hBG hd).le
  have hx : xiC1 d * (l * eps') ≤ xiC1 d * eps' :=
    mul_le_mul_of_nonneg_left (by nlinarith) hX
  have hx0 : 0 ≤ xiC1 d * (l * eps') := by positivity
  have hmono : decDomMargin d L N BG κ (xiC1 d * (l * eps')) ≤
      decDomMargin d L N BG κ (xiC1 d * eps') := by
    unfold decDomMargin
    have h1 := mul_le_mul_of_nonneg_left hx hK4
    have h2 : 0 ≤ K4 d L N BG κ * (xiC1 d * (l * eps')) := by positivity
    have h3 : K4 d L N BG κ * (xiC1 d * (l * eps')) + 2 * (1 + 3 * (xiC1 d * (l * eps'))) ≤
        K4 d L N BG κ * (xiC1 d * eps') + 2 * (1 + 3 * (xiC1 d * eps')) := by linarith
    have h4 := mul_le_mul h1 h3 (by positivity) (by positivity)
    linarith
  exact ⟨{
    hSm := h.hSm
    c₂m := h.c₂m
    hS2m := h.hS2m
    hM2m := h.hM2m
    c₃ := h.c₃
    hS3 := h.hS3
    hM3 := h.hM3
    hMXd := h.hMXd
    hle := mul_le_mul_of_nonneg_left h.hle hl0.le
    hεr := by
      have := mul_le_mul_of_nonneg_left h.hεr hl0.le
      linarith
    δ₃' := l * h.δ₃'
    δfl' := l * h.δfl'
    chain' := h.chain'.scale hl0 hl1
    fl' := h.fl'.scale hl0 hl1 he hδ₃ hd hBG hBG₂
    dm' := hmono.trans_lt h.dm'
    α' := (mul_le_mul_of_nonneg_left hx hK4).trans_lt h.α' }⟩

/-- **The base tower of the new level** (hard rule 10 for the conditions of L5): for every cover
index `m₀`, ratio `0 < q < 1` and `θ > 0` there are `κ_min`, a tower `T₀` and a label rate `κ_dec`
with `CollarBase` (the base tower of the class chain), the closeness ratio
`K₂ N composedCloseBound(…, C_{Ξ1}, 4 d L³ + L) ≤ θ` and `NewLevelNumerics` at the gate radius
`(2 K₁ + 2) C₁ T₀.t` (`exists_newLevelNumerics_gen` with the closeness ratio as the predicate on
the block, at `κ_min` of `StepTowerG.exists_labelRate`). -/
theorem exists_collarBase_newLevel (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (m₀ : ℕ) {q θ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hθ : 0 < θ) :
    ∃ (κmin : ℝ) (T₀ : StepTowerG d L N κmin) (κdec : ℝ), CollarBase d L N m₀ q T₀ κdec ∧
      xiK2 d L N * ((N : ℝ) * composedCloseBound d L N T₀.m₁ T₀.BG T₀.κ (xiC1 d)
        (4 * (d : ℝ) * (L : ℝ) ^ 3 + L)) ≤ θ ∧
      Nonempty (NewLevelNumerics d L N T₀.m₁ T₀.c T₀.BG T₀.κ T₀.t T₀.c₂ T₀.BG₂ T₀.δc
        (4 * (d : ℝ) * (L : ℝ) ^ 3 + L) ((2 * bgK1 d L N + 2) * xiC1 d * T₀.t)) := by
  obtain ⟨κmin, hlo, hk⟩ :=
    StepTowerG.exists_labelRate d L N m₀ (max (stepHullMinG d L) (1 / thm73C3 d L N))
  have hθ' : 0 < min θ ((1 - q) / (2 * q)) := lt_min hθ (div_pos (by linarith) (by positivity))
  obtain ⟨T, δ₃, δfl, hm, h0, h1, h2, hNLN, hPM⟩ := exists_newLevelNumerics_gen d L N hd hL hN
    ((le_max_right _ _).trans hlo) (4 * (d : ℝ) * (L : ℝ) ^ 3 + L)
    (fun BG κ m₁ => xiK2 d L N * ((N : ℝ) * composedCloseBound d L N m₁ BG κ (xiC1 d)
      (4 * (d : ℝ) * (L : ℝ) ^ 3 + L)) ≤ min θ ((1 - q) / (2 * q)))
    (fun _ _ hBG => exists_pow_close_leG hd hL hBG hθ')
  obtain ⟨κdec, h3, h4⟩ := hk T h0
  exact ⟨κmin, T, κdec, ⟨(le_max_left _ _).trans hlo, hm, h0, h3, h4, ⟨δ₃, δfl, h1, h2⟩,
    hPM.trans (min_le_right _ _)⟩, hPM.trans (min_le_left _ _), hNLN⟩

end Tower

end Balaban.Inhabited
