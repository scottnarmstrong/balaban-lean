/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ActionConvWitnessFull

/-!
# An inhabitant of `ActionConvInput` with a nonzero correction

On the window of `ActionConvWitnessFull` the correction `C = windowAction - Awin` vanishes.  Here
the same geometry, couplings and constant configuration are used, but the window action of scale
`k` is taken with the mass `ν_k = 2` instead of the chain's mass `ν_2 = 1`, and the cube has weight
`wt = |X_0|` (its number of sites).

## The computation of `C` (T1)

With constant data, `h = 0` and `φ ≡ e₀` (a unit vector) one has `A_D(a, ν; ψ, φ) = (ν/2)|D|`
(`actionRegionC_const`).  Both sources of a nonzero correction were examined.

* (b) `cost ≠ 0` needs two different Euler-Lagrange configurations `φ_{n-1} ≠ φ_n` on a region with
  boundary; with constant configurations the cost is `0` (`counterC_const`, `starPair_const`), and a
  second constant unit field would need a second proved `IsEL` datum and a proved
  `unit` constraint for it, as in `CancelWitness`.  Not done here.
* (a) `bgRem ≠ 0`: `bgRem_0 = T_{0,2} - β_k A_{X_0}(a_k, ν_k) = β_2 |X_0|/2 - β_2 (ν_k/2)|X_0|`.
  With `ν_k = 2` this is `-β_2 |X_0|/2 ≠ 0`.  Then `windowAction = β_2 |X_0|`,
  `Awin = T_{0,1} + T_{1,2} = β_2 |X_0|/2` and `C = windowAction - Awin = β_2 |X_0| / 2 ≠ 0`
  (with `β_2 = L^{2(d-2)}`).  This case is proved.

## Constants and bounds per field (T2)

`K_conv = c_C = c_W = γ_w = 1`, `K_bg = β_2 e`, `M = 3`, `M₁ = 1`, `R̂ ≡ 2`, `δ₁ ≡ 1`; `mcount_0 = |X_0|`.
* `cube_bound`, `wall_bound`, `p7_first`: the quantities are `0` (cost vanishes), bounds `≥ 0`.
* `window_decay`: `‖bgRem_0‖ = β_2 |X_0|/2`; the bound is `K_bg e^{-1} |X_0| = β_2 |X_0|`
  (slack factor `2`); `bgRem_1 = 0`.
* `variational_bound`, `analytic_T`, `analytic_win`: as in `ActionConvWitnessFull`.

## Findings (T4)

(a) The bound of `window_conversion` is `(9/(1 - L^{-2γ}) + β_2 e) |X_0|` against the true value
`β_2 |X_0|/2`; the factor is `2 (9/(1 - L^{-2γ}) + β_2 e)/β_2`, slack mainly from `K_bg`'s `e` and
the `p7` part, which is not used.  (b) No field becomes unsatisfiable.  `window_decay` with
`γ_w > 0` and positive exponent forces `K_bg ≥ e^{γ_w ⋯} ‖bgRem‖/mcount`, here
`K_bg ≥ e β_2/2`: the constant must dominate `β_k` (the size of the action per cube), and with a
fixed `K_bg` the decay in the exponent `M (R̂_{j-1} - 1) - 2M₁` cannot make `bgRem` small, since
`bgRem` is fixed by the data; it is consistent only because `R̂` and `M` are fixed numbers.
With weight `1` per cube instead of `|X_0|`, `K_bg` would have to grow with the cube size.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.Inhabited.ActionConvNonzero

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.LargeField
  Balaban.LargeField.ActionConv Balaban.SmallField Balaban.Inhabited Balaban.Inhabited.ActionConvFull
  Finset

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁]

/-- The one-cube decomposition with the cube weighted by its number of sites. -/
noncomputable def stepCard {G : GeneratingSet d L (N₁ * L ^ m₁) K (PsiZeroWitness.ϱ d L)}
    (X : Region G) : StepDecomp X :=
  { stepSingle X with
    wt := fun _ => (X.sites.card : ℝ)
    wt_nonneg := fun _ => Nat.cast_nonneg _ }

theorem stepCard_total {G : GeneratingSet d L (N₁ * L ^ m₁) K (PsiZeroWitness.ϱ d L)}
    (X : Region G) : (stepCard X).total = X.sites.card := by
  unfold StepDecomp.total
  show ∑ _i : Unit, (X.sites.card : ℝ) = _
  simp

/-- The decompositions: `stepCard` for `X_0`, the empty one for `X_j = ∅`. -/
noncomputable def DR' (hK : 1 ≤ K) :
    (j : ℕ) → StepDecomp (XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK j)
  | 0 => stepCard _
  | _ + 1 => StepDecomp.empty

section Window

variable {U : Type*} (S : Set U) (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hK : 1 ≤ K)

/-- The window of `ActionConvWitnessFull` with window mass `ν_k = 2` and cube weight `|X_0|`. -/
noncomputable def Wn : WindowSetup d L (N₁ * L ^ m₁) K 2 S 0 2 :=
  { Wd S hd3 hL hK (m₁ := m₁) (N₁ := N₁) with
    νk := 2
    decomp := DR' hK
    mcount := fun j => (DR' hK j).total
    mcount_eq := fun _ => rfl }

local notation "W₀" => Wn S hd3 hL hK (m₁ := m₁) (N₁ := N₁)

theorem mcount_zero : (W₀).mcount 0 = (XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card :=
  stepCard_total _

theorem mcount_one : (W₀).mcount 1 = 0 := by
  show (StepDecomp.empty (G := GG d L N₁ m₁ K)).total = 0
  exact Finset.sum_eq_zero fun i _ => (i : Empty).elim

theorem mcount_sum : ∑ j ∈ Finset.Ico 0 2, (W₀).mcount j =
    (XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card := by
  have : Finset.Ico 0 2 = {0, 1} := by decide
  rw [this, Finset.sum_pair (by norm_num), mcount_zero, mcount_one]; simp

theorem T_chain (u : U) (n : ℕ) :
    ((W₀).chain 0).T u n = (betaF d L n : ℂ) * ((nuF d L n : ℂ) / 2 *
      ((XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card : ℂ)) := by
  unfold ConvChain.T
  exact congrArg _ (actionRegionC_const hK _ _ _)

theorem windowAction_val (u : U) : (W₀).windowAction u =
    (betaF d L 2 : ℂ) * (((XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card : ℂ)) := by
  unfold WindowSetup.windowAction
  have := actionRegionC_const hK (XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0) (aF d L 2) 2
  show (betaF d L 2 : ℂ) * actionRegionC (XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0)
    (aF d L 2) 2 (Dd d L N₁ m₁ K) (phi d L N₁ m₁ K) = _
  rw [this]; push_cast; ring

theorem Awin_val (u : U) : (W₀).Awin u =
    (betaF d L 2 : ℂ) * (((XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card : ℂ)) / 2 := by
  have hb : (betaF d L 2 : ℂ) ≠ 0 := by exact_mod_cast (betaF_pos (d := d) (by omega : 1 < L) 2).ne'
  have hb1 : (betaF d L 1 : ℂ) ≠ 0 := by exact_mod_cast (betaF_pos (d := d) (by omega : 1 < L) 1).ne'
  have e : Finset.Ico 0 2 = {0, 1} := by decide
  unfold WindowSetup.Awin
  rw [e, Finset.sum_pair (by norm_num)]
  have h1 := T_chain S hd3 hL hK (m₁ := m₁) (N₁ := N₁) u 1
  have h2 : ((W₀).chain 1).T u 2 = 0 := by
    show (betaF d L 2 : ℂ) * actionRegionC (Region.bot : Region (GG d L N₁ m₁ K)) (aF d L 2)
      (nuF d L 2) (Dd d L N₁ m₁ K) (phi d L N₁ m₁ K) = 0
    rw [actionRegionC_bot, mul_zero]
  rw [h1, h2, add_zero]
  unfold nuF
  push_cast
  field_simp

/-- **The correction is nonzero**: `windowAction - Awin = β_2 |X_0| / 2 ≠ 0`. -/
theorem correction_val (u : U) : (W₀).windowAction u - (W₀).Awin u =
    (betaF d L 2 : ℂ) * (((XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card : ℂ)) / 2 := by
  rw [windowAction_val, Awin_val]; ring

theorem correction_ne_zero (u : U) : (W₀).windowAction u - (W₀).Awin u ≠ 0 := by
  rw [correction_val]
  have hb : (betaF d L 2 : ℂ) ≠ 0 := by exact_mod_cast (betaF_pos (d := d) (by omega : 1 < L) 2).ne'
  have hcard : ((XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card : ℂ) ≠ 0 := by
    exact_mod_cast (XR_zero_nonempty (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK).card_pos.ne'
  exact div_ne_zero (mul_ne_zero hb hcard) (by norm_num)

theorem bgRem_zero (u : U) : (W₀).bgRem u 0 =
    -((betaF d L 2 : ℂ) * (((XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card : ℂ)) / 2) := by
  have hb1 : (betaF d L 2 : ℂ) ≠ 0 := by exact_mod_cast (betaF_pos (d := d) (by omega : 1 < L) 2).ne'
  unfold WindowSetup.bgRem
  have h := T_chain S hd3 hL hK (m₁ := m₁) (N₁ := N₁) u 2
  have h2 := actionRegionC_const hK (XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0) (aF d L 2) 2
  show ((W₀).chain 0).T u 2 - (betaF d L 2 : ℂ) *
    actionRegionC (XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0) (aF d L 2) 2
      (Dd d L N₁ m₁ K) (phi d L N₁ m₁ K) = _
  rw [h, h2]
  have : (nuF d L 2 : ℂ) = 1 := by rw [nuF_two]; simp
  rw [this]; push_cast; ring

theorem bgRem_one (u : U) : (W₀).bgRem u 1 = 0 := by
  unfold WindowSetup.bgRem
  show (betaF d L 2 : ℂ) * actionRegionC (Region.bot : Region (GG d L N₁ m₁ K)) (aF d L 2)
      (nuF d L 2) (Dd d L N₁ m₁ K) (phi d L N₁ m₁ K) -
    (betaF d L 2 : ℂ) * actionRegionC (Region.bot : Region (GG d L N₁ m₁ K)) (aF d L 2) 2
      (Dd d L N₁ m₁ K) (phi d L N₁ m₁ K) = 0
  rw [actionRegionC_bot, actionRegionC_bot]; simp

variable [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- **`ActionConvInput` on the window with nonzero correction.**  Constants `K_conv = c_C = c_W =
γ_w = 1`, `K_bg = β_2 e`, `M = 3`, `M₁ = 1`, `R̂ ≡ 2`, `δ₁ ≡ 1`; see the module doc for the fields. -/
theorem actionConvInput_nonzero (ε : ℕ → ℝ) :
    Nonempty (ActionConvInput (Wn S hd3 hL hK (m₁ := m₁) (N₁ := N₁)) 1 (betaF d L 2 * Real.exp 1)
      1 3 1 1 1 ε (fun _ => 2) (fun _ _ _ => 1)) := by
  have hV : 0 ≤ cK2 d L 2 * 1 := by have := cK2_pos d L 2; positivity
  have hbp := betaF_pos (d := d) (L := L) (by omega : 1 < L) 2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j _ n _ _ u _
    refine ⟨?_, ?_⟩
    · show Small (GG d L N₁ m₁ K) (alphaF d L N₁ m₁ K - alphaF d L N₁ m₁ K) (cK2 d L 2 * 1)
      intro x
      simpa using hV
    · show SupBounds (GG d L N₁ m₁ K) (phi d L N₁ m₁ K - phi d L N₁ m₁ K) (cK2 d L 2 * 1)
      rw [sub_self]
      exact supBounds_zero' hV
  · intro j _ n _ _
    have h : AnalyticOnNhd ℂ (fun _ : U => ((W₀).chain j).T 0 n) S := analyticOnNhd_const
    exact h
  · intro j _ n _ _ u _ i
    refine le_trans (le_of_eq ?_) (mul_nonneg zero_le_one (((W₀).decomp j).wt_nonneg i))
    simp [Wn, Wd, chainF, counterC_const hK]
  · intro j _ n _ _ u _ q
    refine le_trans (le_of_eq ?_) (mul_nonneg zero_le_one (((W₀).decomp j).wt_nonneg _))
    simp [Wn, Wd, chainF, starPairOn_const]
  · intro j _ n _ _ u _
    have hc0 : ((W₀).chain j).cost u n = 0 :=
      cost_eq_zero S hd3 hL hK (m₁ := m₁) (N₁ := N₁) j n u
    rw [hc0, norm_zero]
    have hb : ∀ n, 0 ≤ ((W₀).chain j).β n := fun n => (betaF_pos (by omega) n).le
    exact mul_nonneg (mul_nonneg zero_le_one (div_nonneg (mul_nonneg (hb _) (sq_nonneg _))
      (mul_nonneg (hb _) (sq_nonneg _)))) ((W₀).mcount_nonneg j)
  · intro j hj u _
    have hj' : j = 0 ∨ j = 1 := by simp at hj; omega
    have hm := (W₀).mcount_nonneg j
    have hex : Real.exp (-1 * (3 * (((fun _ : ℕ => (2 : ℝ)) (j - 1)) - 1) - 2 * 1)) =
        (Real.exp 1)⁻¹ := by
      rw [← Real.exp_neg]; norm_num
    rw [hex]
    rcases hj' with rfl | rfl
    · rw [bgRem_zero, mcount_zero, norm_neg]
      have hc : ((XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card : ℝ) ≥ 0 :=
        Nat.cast_nonneg _
      have : ‖(betaF d L 2 : ℂ) * (((XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card : ℂ)) / 2‖
          = betaF d L 2 * (XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card / 2 := by
        rw [norm_div, norm_mul]
        simp [abs_of_pos hbp]
      rw [this]
      have he' : Real.exp 1 * (Real.exp 1)⁻¹ = 1 := mul_inv_cancel₀ (Real.exp_pos 1).ne'
      have e2 : betaF d L 2 * Real.exp 1 * (Real.exp 1)⁻¹ * ((XR (d := d) (L := L) (N₁ := N₁)
          (m₁ := m₁) hK 0).sites.card : ℝ) = betaF d L 2 * (XR (d := d) (L := L) (N₁ := N₁)
          (m₁ := m₁) hK 0).sites.card := by
        rw [mul_assoc (betaF d L 2), he']
        ring
      rw [e2]
      nlinarith [mul_nonneg hbp.le hc]
    · rw [bgRem_one, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg hbp.le (Real.exp_pos 1).le)
        (inv_nonneg.2 (Real.exp_pos 1).le)) hm
  · intro j _
    have h : AnalyticOnNhd ℂ (fun _ : U => ((W₀).βk : ℂ) *
        actionRegionC ((W₀).Xw j) (W₀).ak (W₀).νk ((W₀).Datw 0) ((W₀).φw 0)) S := analyticOnNhd_const
    exact h

/-- **`window_conversion` on the window with nonzero correction** (`η = 0`, `γ = α = (d-2)/4`,
`α₀ = 1`, `K_conv = 1`, `K_bg = β_2 e`): the correction is `C u = β_2 |X_0| / 2 ≠ 0`, and the bound is
`(9/(1 - L^{-2γ}) + β_2 e) |X_0|`. -/
theorem window_conversion_nonzero :
    ∃ C : U → ℂ, (∀ u ∈ S, (W₀).windowAction u = (W₀).Awin u + C u) ∧ AnalyticOnNhd ℂ C S ∧
      (∀ u ∈ S, ‖C u‖ ≤ (9 * Real.exp (2 * 0) * 1 / (1 - (L : ℝ) ^ (-(2 * (((d : ℝ) - 2) / 4)))) +
        betaF d L 2 * Real.exp 1) * ∑ j ∈ Finset.Ico 0 2, (W₀).mcount j) ∧
      ∀ u ∈ S, C u = (betaF d L 2 : ℂ) * (((XR (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) hK 0).sites.card : ℂ)) / 2 ∧
        C u ≠ 0 := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd3
  have I := (actionConvInput_nonzero S hd3 hL hK (m₁ := m₁) (N₁ := N₁)
    (epsSeq L (((d : ℝ) - 2) / 4) 1)).some
  obtain ⟨C, h1, h2, h3⟩ := window_conversion I
    (γ := ((d : ℝ) - 2) / 4) (η := 0) (α := ((d : ℝ) - 2) / 4) (α₀ := 1)
    (by omega) (by omega) (by linarith) one_pos rfl (by ring)
    (fun j _ => ⟨1, one_pos, fun _ => 1, fun _ => by simp, fun n _ _ => by
      simp [Wn, Wd, chainF, betaF]⟩)
    zero_le_one (mul_nonneg (betaF_pos (by omega) 2).le (Real.exp_pos 1).le) zero_le_one
    (fun j _ => by norm_num)
  refine ⟨C, h1, h2, h3, fun u hu => ?_⟩
  have hC : C u = (W₀).windowAction u - (W₀).Awin u := by linear_combination -(h1 u hu)
  rw [hC]
  exact ⟨correction_val S hd3 hL hK u, correction_ne_zero S hd3 hL hK u⟩

end Window

/-- The concrete instance `d = L = 3`, `N₁ = 6`, `m₁ = 0`, `K = 2`, `S = ℂ`: `ActionConvInput`
holds with a nonzero correction. -/
theorem actionConvInput_nonzero_witness (ε : ℕ → ℝ) :
    Nonempty (ActionConvInput (Wn (Set.univ : Set ℂ) (d := 3) (L := 3) (N₁ := 6) (m₁ := 0) (K := 2)
      (by norm_num) (by norm_num) (by norm_num)) 1
      (betaF 3 3 2 * Real.exp 1) 1 3 1 1 1 ε (fun _ => 2) (fun _ _ _ => 1)) :=
  actionConvInput_nonzero (U := ℂ) Set.univ (d := 3) (L := 3) (N₁ := 6) (m₁ := 0) (K := 2)
    (by norm_num) (by norm_num) (by norm_num) ε

/-- **Hypothesis-free**: `window_conversion` on the concrete instance with the correction
`C u = β_2 |X_0|/2 ≠ 0` (here `β_2 = 3^2`). -/
theorem window_conversion_nonzero_witness :
    ∃ u ∈ (Set.univ : Set ℂ), (Wn (Set.univ : Set ℂ) (d := 3) (L := 3) (N₁ := 6) (m₁ := 0) (K := 2)
        (by norm_num) (by norm_num) (by norm_num)).windowAction u -
      (Wn (Set.univ : Set ℂ) (d := 3) (L := 3) (N₁ := 6) (m₁ := 0) (K := 2)
        (by norm_num) (by norm_num) (by norm_num)).Awin u ≠ 0 ∧
    ∃ C : ℂ → ℂ, (∀ u ∈ (Set.univ : Set ℂ),
        (Wn (Set.univ : Set ℂ) (d := 3) (L := 3) (N₁ := 6) (m₁ := 0) (K := 2)
          (by norm_num) (by norm_num) (by norm_num)).windowAction u =
        (Wn (Set.univ : Set ℂ) (d := 3) (L := 3) (N₁ := 6) (m₁ := 0) (K := 2)
          (by norm_num) (by norm_num) (by norm_num)).Awin u + C u) ∧
      AnalyticOnNhd ℂ C Set.univ ∧
      (∀ u ∈ (Set.univ : Set ℂ), ‖C u‖ ≤
        (9 * Real.exp (2 * 0) * 1 / (1 - ((3 : ℕ) : ℝ) ^ (-(2 * ((((3 : ℕ) : ℝ) - 2) / 4)))) +
          betaF 3 3 2 * Real.exp 1) *
        ∑ j ∈ Finset.Ico 0 2,
          (Wn (Set.univ : Set ℂ) (d := 3) (L := 3) (N₁ := 6) (m₁ := 0) (K := 2)
            (by norm_num) (by norm_num) (by norm_num)).mcount j) ∧
      ∀ u ∈ (Set.univ : Set ℂ), C u ≠ 0 := by
  have h := window_conversion_nonzero (U := ℂ) Set.univ (d := 3) (L := 3) (N₁ := 6) (m₁ := 0)
    (K := 2) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C, h1, h2, h3, h4⟩ := h
  refine ⟨0, Set.mem_univ _, correction_ne_zero (U := ℂ) Set.univ (d := 3) (L := 3) (N₁ := 6) (m₁ := 0)
    (K := 2) (by norm_num) (by norm_num) (by norm_num) 0, C, h1, h2, h3, fun u hu => (h4 u hu).2⟩

end Balaban.Inhabited.ActionConvNonzero
