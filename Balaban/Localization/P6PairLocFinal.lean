/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairLocComposed

/-!
# `p6_action_at_one_real` with the numerical binders discharged (VMOD-11 row 8)

Discharged for the P6 pair: `DecSpecs` (`decSpecs_exists`, the constants `c'`, `BG` depend only on
`d, L`), `5 < c n_{k+1}` (`c ≥ 14`), `2 ≤ m₁` (from `4L² ≤ L^{m₁}`), and `3 ≤ d`, `3 ≤ L`,
`0 ≤ ν`, `ν L^{2(k+1)} ≤ 1`, admissibility of the weights (all fields of `BgHyp`, which stays a typing
hypothesis of the background).  Remaining source premises: `M₁ = L^{m₁}`, `4L² ≤ L^{m₁}`, the row-6
separation `2 d log L ≤ agmonRate/16 (ϱ - 1)`, the decoupling scale `c' e^{N₀ κ} ≤ L^{m₁}`, and the
domain parameters `δ, ε` of the data.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale

theorem mixedKc_nonneg {d : ℕ} (L : ℕ) [NeZero L] (hd : 3 ≤ d) : 0 ≤ Dec2.mixedKc d L :=
  (Dec2.cutKp_nonneg hd).trans (le_max_left _ _)

/-- `DecSpecs` for the mixed constants exists for every `d, L ≥ 3`. -/
theorem p6_decSpecs_exists {d L : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ c BG : ℝ, Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG :=
  Dec2.decSpecs_exists hd hL (mixedKc_nonneg L hd) (Cchi_nonneg d L)

theorem five_lt_mul_of_fourteen_le {c n : ℕ} (hc : 14 ≤ c) [NeZero n] : 5 < c * n := by
  have := Nat.pos_of_ne_zero (NeZero.ne n)
  nlinarith

theorem two_le_of_four_sq_le {L m : ℕ} (hL : 2 ≤ L) (h : 4 * L ^ 2 ≤ L ^ m) : 2 ≤ m := by
  by_contra hm
  have hm' : m ≤ 1 := by omega
  have : L ^ m ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) hm'
  nlinarith

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.LargeField
  Balaban.Multiscale.GeneratingSet RegionHistory

set_option linter.unusedSectionVars false

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))
  (hk : k + 1 ≤ K) {m₁ : ℕ}

/-- **`p6_action_at_one` for the real step** with the binders of `DecSpecs`, `5 < c n`, `2 ≤ m₁`
and the `BgHyp`-implied facts discharged: for the geometry `M₁ = L^{m₁}`, `4L² ≤ L^{m₁}` and the
row-6 separation, there are constants `c', BG` (depending only on `d, L`) such that for every
decoupling scale `κ` with `c' e^{N₀κ} ≤ L^{m₁}` and every pair of data in the domains `𝒟`, the
decoupled cube action difference at `s ≡ 1` is `realStepAct`. -/
theorem p6_action_at_one_real_final (hM1 : g.M1 = S.L ^ m₁) (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁)
    {a₁ ν β : ℝ}
    (hsep : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1))
    (H0 : BgHyp S.d S.L (k + 1) (minSep S.L g.M1) (compWeight S.L a₁) ν) :
    ∃ c' BG : ℝ, Dec2.DecSpecs S.d S.L (Dec2.mixedKc S.d S.L) (Cchi S.d S.L) c' BG ∧
      ∀ {κ : ℝ}, 0 ≤ κ → c' * Real.exp (N0 S.d S.L * κ) ≤ (S.L : ℝ) ^ m₁ →
      ∀ {δ0 ε0 δ1 ε1 : ℝ},
        0 < δ0 → δ0 ≤ ε0 → ε0 ≤ bgC0 S.d S.L N → δ0 ≤ c7 S.d S.L N BG κ →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε0 ^ 2 ≤ δ0 ^ 2 →
        0 < δ1 → δ1 ≤ ε1 → ε1 ≤ bgC0 S.d S.L N → δ1 ≤ c7 S.d S.L N BG κ →
        ν * ((S.L : ℝ) ^ (k + 1)) ^ 2 * ε1 ^ 2 ≤ δ1 ^ 2 →
      ∀ (u : StepFields S.d (g.M1 * (g.c * n (k + 1))) S.L k N),
        InDomainC (locGen g Hl k Zc hZc hk) ν δ0 ε0
          (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2) →
        InDomainC (bdGen g Hl k hk) ν δ1 ε1 (bdDataC g Hl k hk u.1 u.2.1 u.2.2) →
      ∀ (Q : Finset (Torus S.d (g.M1 * (g.c * n (k + 1)) * S.L ^ (k + 1)))),
      (β : ℂ) * (cubeActionStar (castN (p6_side hM1) (locGen g Hl k Zc hZc hk))
          (compWeight S.L a₁) ν (castCube (p6_side hM1) Q)
          (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)).Ψ
          (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)).h
          ((castN_precedes (p6_side hM1) (locGen_precedes_bd g Hl k Zc hZc hk)).restrictφ
            (Dec2.decBgField (realCover g Hl k hk hM1)
              (castN (p6_side hM1) (bdGen g Hl k hk)) (compWeight S.L a₁) ν
              (rho4 S.d S.L N BG κ) (fun _ => 1)
              (castBg (p6_side hM1) (bdDataC g Hl k hk u.1 u.2.1 u.2.2)))) -
        cubeActionStar (castN (p6_side hM1) (locGen g Hl k Zc hZc hk)) (compWeight S.L a₁) ν
          (castCube (p6_side hM1) Q)
          (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)).Ψ
          (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)).h
          (Dec2.decBgField (realCover g Hl k hk hM1)
            (castN (p6_side hM1) (locGen g Hl k Zc hZc hk)) (compWeight S.L a₁) ν
            (rho4 S.d S.L N BG κ) (fun _ => 1)
            (castBg (p6_side hM1) (locDataC g Hl k Zc hZc hk u.1 u.2.1 u.2.2)))) =
      realStepAct g Hl k Zc hZc hk a₁ ν β Q u := by
  obtain ⟨c', BG, hS⟩ := p6_decSpecs_exists (d := S.d) (L := S.L) H0.hd H0.hL
  refine ⟨c', BG, hS, fun {κ} hκ hMκ {δ0 ε0 δ1 ε1} hδ0 hδε0 hε0 hc0 hν0 hδ1 hδε1 hε1 hc1 hν1 u hD0 hD1
    Q => ?_⟩
  exact p6_action_at_one_real' g Hl k Zc hZc hk hM1 (two_le_of_four_sq_le Hl.F.ok.two_le_L hM) hM
    (five_lt_mul_of_fourteen_le g.hc) H0.hd H0.hL H0.mass H0.massLe H0.weights hsep hS H0 hκ hMκ
    hδ0 hδε0 hε0 hc0 hν0 hδ1 hδε1 hε1 hc1 hν1 u hD0 hD1 Q

end Balaban.Fluctuation
