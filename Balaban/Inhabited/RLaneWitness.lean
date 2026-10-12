/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.InhabitedRipeRemoval
public import Balaban.LargeField.R.ZeroDomainSepRho
public import Balaban.LargeField.R.PsiZeroWindowRipe
public import Balaban.LargeField.R.PsiZeroFinal
public import Balaban.Localization.CompWeightAdmissible
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The reference minimizer `ψ⁰_k` at the actual ripe window of the history with a ripe removal

LF-RECONSTRUCTION Definition III.3.1, Lemmas III.3.2 and III.3.3.

Dictionary (the R lane at a ripe component `Z` of `Z^pre_k`, `k = T`):

* the generating set `G′` to which `psiZero_exists_unique` is applied is the boundary piece
  `𝔹_k(U_k)` of the window, `windowBdry H Z g = (windowOfHistory H Z g _ _).bdry`, on the torus
  `Torus d (M n_k L^k)`, with separation `winSep g = min {L M R_base, 5 L M₁}`;
* the box `Z₀ = box b₀ w` of `k`-blocks is the one of `exists_window_box`
  (`jBlock x ∈ box b₀ w ↔ the k-block of x lies in Zzero`, `1 ≤ w_i ≤ 3 c₀ + 4`);
* the region is `X = ripeX H Z`, the `k`-blocks of the fine set of `U_k^∼ = bdryUnb H Z`.

Verdict of the hypotheses of `psiZero_exists_unique` at the window (all proved):
`hw1`, `hwD` (`exists_window_box`); `hm` (`3 c₀ + 6 ≤ M n_k`, `ripeRem_hn`); `hXreg`
(`ripeX_hXreg`); `hΩ : OverTop` (`windowBdry_overTop`); `hdata` (`ripeX_hdata` with
`windowBdry_dataSites_cube`, the range of the minimal generating set); `BgHyp d L k ϱ′ a 0` at
`ϱ′ = winSep g` (`wS_bgHyp`, from `5 L M₁ ≥ R₀(3,3)`).  The standing condition (Λ18) on the radii
(`wS_h18`) and `2 c₀ + 10 ≤ [R̂₀]` (`wS_hR0`) hold for the radii of the witness.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.Inhabited.RLane

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.Localization
  Balaban.LargeField.RegionHistory

section Numerics

open Balaban.LargeField.JointWitness Balaban.Inhabited.RadiiSet

/-- The analytic threshold is at least `40`. -/
theorem forty_le_anaThreshold : 40 ≤ anaThreshold := by
  refine le_trans ?_ (le_max_left _ _)
  have hx : (37 / 40 : ℝ) ≤ (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ)))) := by
    have h1 : ((37 / 40 : ℝ) ^ (10 : ℕ)) ≤ (1 / 2 : ℝ) := by norm_num
    have h2 : ((37 / 40 : ℝ) ^ (10 : ℕ)) ^ (1 / 10 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : ((37 / 40 : ℝ) ^ (10 : ℕ)) ^ (1 / 10 : ℝ) = 37 / 40 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h4 : (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ)))) = (1 / 2 : ℝ) ^ (1 / 10 : ℝ) := by
      rw [Real.rpow_neg (by norm_num), one_div (2 : ℝ), Real.inv_rpow (by norm_num)]
      norm_num
    rw [h4]; linarith
  have hlt : (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ)))) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem log_three_lt : Real.log 3 < 11 / 10 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 : Real.exp (11 / 10) ^ 10 = Real.exp 1 ^ 11 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h3 : (3 : ℝ) ^ 10 < Real.exp 1 ^ 11 := by
    have : (2.7182818283 : ℝ) ^ 11 < Real.exp 1 ^ 11 :=
      pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
    refine lt_of_lt_of_le ?_ this.le
    norm_num
  by_contra hcon
  push Not at hcon
  have : Real.exp (11 / 10) ^ 10 ≤ 3 ^ 10 := pow_le_pow_left₀ (Real.exp_pos _).le hcon 10
  linarith

/-- The scales `λ_j` of the genuine-radii setting are at least `40`. -/
theorem wS_lam_ge (j : ℕ) : 40 ≤ wS.lam j := by
  have h := wβ_spec.2.2
  have h40 := forty_le_anaThreshold
  have hj : (0 : ℝ) ≤ (j : ℝ) * Real.log 3 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  show 40 ≤ Real.log (wβ * (5 / 4)) + 1 + (j : ℝ) * Real.log 3
  linarith

/-- **The standing condition (Λ18)** on the radii `R_j = R_base λ_j²` of the witness. -/
theorem wS_h18 :
    ∀ j, wS.Rb * (wS.lam j + wS.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (wS.Rb * wS.lam j ^ 2 - 1) := by
  intro j
  have hl := wS_lam_ge j
  have hc := log_three_lt
  have hRb : wS.Rb = 32 := rfl
  have hθ : wS.θp = Real.log 3 := rfl
  rw [hRb, hθ]
  have hc0 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  nlinarith [mul_nonneg (sub_nonneg.2 hl) (sub_nonneg.2 hl),
    mul_nonneg (sub_nonneg.2 hl) (sub_nonneg.2 hc.le), mul_nonneg hc0.le (sub_nonneg.2 hc.le)]

/-- `2 c₀ + 10 ≤ [R̂₀]` for the witness. -/
theorem wS_hR0 : 2 * wS.c0 + 10 ≤ wS.lateR 0 := by
  have hl := wS_lam_ge 0
  have hc : wS.c0 = 10 := rfl
  rw [hc]
  unfold Balaban.LargeField.Setting.lateR
  apply Nat.le_floor
  have hRb : wS.Rb = 32 := rfl
  rw [hRb]
  push_cast
  nlinarith

/-- **`BgHyp d L k ϱ′ a 0` at the separation of the window pieces** `ϱ′ = winSep g`
(`min {L M R_base, 5 L M₁} = 5 L M₁ ≥ R₀(3, 3)`), with the weights `compWeight L a₁`, `a₁ = 1`. -/
theorem wS_bgHyp (n : ℕ → ℕ) (k : ℕ) :
    BgHyp wS.d wS.L k (winSep (wGeo n)) (compWeight wS.L 1) 0 where
  hd := le_rfl
  hL := le_rfl
  hϱ := by
    have h0 := bgR0_le_minSep
    have hM1 : (1 : ℝ) ≤ M1 := by exact_mod_cast M1_pos
    show bgR0 3 3 ≤ min ((3 : ℝ) * ((14 * M1 : ℕ) : ℝ) * 32) (minSep 3 M1)
    refine le_min ?_ ?_
    · push_cast at h0 ⊢
      nlinarith
    · unfold minSep
      push_cast at h0 ⊢
      linarith
  weights := isAdmissibleWeights_compWeight (L := wS.L) (by show 3 ≤ 3; norm_num)
    (by norm_num) (by norm_num) k
  mass := le_rfl
  massLe := by simp

end Numerics

section Generic

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K) [NeZero S.L] [NeZero S.M] {k : ℕ} (Z : H.Comp k)
  (g : Geo S n R S.M)

theorem dataSites_castN_cast {d L N₀ N₀' k : ℕ} [NeZero N₀] [NeZero N₀'] [NeZero L] {ϱ : ℝ}
    (h : N₀ = N₀') (G : GeneratingSet d L N₀ k ϱ) (x : Torus d (N₀' * L ^ k))
    (hx : x ∈ dataSites (GeneratingSet.castN h G)) :
    torusCast (by rw [h]) x ∈ dataSites G := by
  subst h
  exact hx

theorem dataSites_relax {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
    (G : GeneratingSet d L N₀ k ϱ) (h : ϱ' ≤ ϱ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ dataSites (G.relax h)) : x ∈ dataSites G := by
  rw [mem_dataSites] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl hx
  · right
    rw [mem_collar] at hx ⊢
    exact hx

/-- The generating set `G′ = 𝔹_k(U_k)` of the R lane is the boundary piece of the window. -/
theorem windowBdry_eq_bdry (hkK : k ≤ K) (hW : H.RipeWindow k Z) :
    windowBdry H Z g = (windowOfHistory H Z g hkK hW).bdry := rfl

/-- **`hdU` for the boundary piece** (Lemma II.2.3 (c), range of the minimal generating set): the
data sites `Ω₁ ∪ C(Ω₁)` of `𝔹_k(U_k)` have their `π_k`-cube in `U_k^∼`. -/
theorem windowBdry_dataSites_cube (hnn : ∀ i, i < k → n i = S.L * n (i + 1))
    {x : Torus S.d (S.M * n k * S.L ^ k)} (hx : x ∈ dataSites (windowBdry H Z g)) :
    cubeMap n S.L S.M k k x ∈ bdryUnb H Z := by
  have h1 := dataSites_relax _ _ (dataSites_castN_cast (geo_base_eq g) _ x hx)
  have hP : g.M1 * (g.c * n k) * S.L ^ k = (S.L ^ k * (g.c * g.M1)) * n k := by
    rw [nn_eq_pow' hnn le_rfl, ← pow_sub_mul_pow S.L le_rfl]
    ring
  have hM12 : 12 * g.M1 ≤ g.c * g.M1 := Nat.mul_le_mul_right _ (by have := g.hc; omega)
  obtain ⟨y, hy, hd⟩ := minimalGenSet_range (X := fineMin g k (bdryU H Z)) H.F.ok.two_le_L le_rfl
    hM12 hP (x := torusCast (by rw [geo_base_eq g]) x) h1
  rw [fineMin, mem_cubePre] at hy
  rw [cubeMap_eq_castBlock (g := g) k x]
  exact mem_nbhd.2 ⟨_, hy, hd⟩

/-- **`hΩ` for the boundary piece**: the blocks of `Z₀ ∪ shellOut Z₀` lie over the top layer
`Ω_k(𝔹_k(U_k)) = U_k` (they lie in `Z ⊆ U_k`; Lemma III.3.2 (d)). -/
theorem windowBdry_overTop (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) (hkK : k ≤ K) (hk : 1 ≤ k)
    {b0 : Torus S.d (S.M * n k * S.L ^ (k - k))} {w : Fin S.d → ℕ}
    (hbx : ∀ x : Torus S.d (S.M * n k * S.L ^ k), (jBlock S.d S.L (S.M * n k) k k x ∈ box b0 w ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z)) :
    OverTop (windowBdry H Z g) (box b0 w ∪ shellOut (box b0 w)) := by
  intro x hx
  have hl := H.mem_locFine_of_mem_box_shell H.F.ok (H.eight_le_L_mul_lateR k) hR hkK hk Z hbx hx
  have h := (H.mem_locFine_k hkK).1 hl
  exact windowBdry_top_mem (H := H) (Z := Z) (g := g)
    (subset_nbhd (⌊R (k - 1)⌋₊ + 1) _ h)

/-- **`hdata` for the boundary piece**: the `k`-blocks of the data sites of `𝔹_k(U_k)` lie in
`X = ripeX H Z`. -/
theorem windowBdry_hdata (hkK : k ≤ K) :
    ∀ x ∈ dataSites (windowBdry H Z g), jBlock S.d S.L (S.M * n k) k k x ∈ H.ripeX Z :=
  H.ripeX_hdata Z _ (fun _ hx => windowBdry_dataSites_cube H Z g
    (fun i hi => H.F.hnn i (lt_of_lt_of_le hi hkK)) hx)

/-- **Lemma III.3.3 at the actual ripe window** (T2/T3): every hypothesis of
`psiZero_exists_unique` holds for `G′ = 𝔹_k(U_k)` (`windowBdry`), the box `Z₀` of
`exists_window_box` and `X = ripeX H Z`, so there are `K₆, c₁₁ > 0` such that for `0 < δ ≤ c₁₁`
and `ψ_k ∈ Ψ̃(X ∖ Z₀; δ)` problem (2.34) has exactly one solution in `Ψ̃(X; K₆ δ)`.  The
premises are the standing source data of the window (`S.Good`, (Λ18), the radii, the torus side
`3 c₀ + 6 ≤ M n_k`, `BgHyp` at `winSep`). -/
theorem psiZero_exists_unique_ripe (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (hR0 : 2 * S.c0 + 10 ≤ S.lateR 0) (hkK : k ≤ K) (W : H.RipeWindow k Z)
    (hk0 : k ≤ k0) (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hk : 1 ≤ k)
    (hR : ∀ j, R j = S.Rb * S.lam j ^ 2) (hd : 2 ≤ S.d) (hn : 3 * S.c0 + 6 ≤ S.M * n k)
    (a : ℕ → ℝ) (hBg : BgHyp S.d S.L k (winSep g) a 0) (N : ℕ) [NeZero N] :
    ∃ (b0 : Torus S.d (S.M * n k * S.L ^ (k - k))) (w : Fin S.d → ℕ),
      (∀ i, 1 ≤ w i ∧ w i ≤ 3 * S.c0 + 4) ∧
      (∀ x : Torus S.d (S.M * n k * S.L ^ k), (jBlock S.d S.L (S.M * n k) k k x ∈ box b0 w ↔
        blockMap (S.L ^ k) (S.M * n k) x ∈ H.Zzero k Z)) ∧
      ∃ K c11 : ℝ, 0 < K ∧ 0 < c11 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ c11 →
        ∀ ψk : BlockField S.d S.L (S.M * n k) k N,
          TubeOn (windowBdry H Z g) (ripeX H Z \ box b0 w) δ ψk →
            ∃! ψ, PsiZeroSol (windowBdry H Z g) a b0 w (ripeX H Z) (K * δ) ψk ψ := by
  obtain ⟨b0, w, hw, hbx⟩ := H.exists_window_box G h18 hR0 hkK W hk0 hT
  refine ⟨b0, w, hw, hbx, ?_⟩
  exact psiZero_exists_unique (N := N) (windowBdry H Z g) a hd hk b0 w (fun i => (hw i).1)
    (fun i => (hw i).2) (D := 3 * S.c0 + 4)
    (by simpa using (by omega : 3 * S.c0 + 4 + 2 ≤ S.M * n k))
    (H.ripeX_hXreg hR hkK hk Z hbx) (windowBdry_overTop H Z g hR hkK hk hbx)
    (windowBdry_hdata H Z g hkK) hBg

end Generic

section Concrete

open Balaban.Inhabited.RipeRemoval Balaban.Inhabited.RadiiSet Balaban.Inhabited RadiiHist

/-- `4 ρ_j + 21 ≤ n_j` for the scales `1 ≤ j ≤ T` of the history. -/
theorem ripeRem_hT : ∀ j, 1 ≤ j → j ≤ Tstar wS →
    4 * wS.rho j + 21 ≤ side wS (bigN wS) (Tstar wS + 1) j := by
  intro k _ hk
  have hk' : k ∈ Finset.range (Tstar wS + 1) := Finset.mem_range.mpr (by omega)
  have h1 : 4 * wS.rho k + 21 ≤ ∑ j ∈ Finset.range (Tstar wS + 1), (4 * wS.rho j + 21) :=
    Finset.single_le_sum (f := fun j => 4 * wS.rho j + 21) (fun _ _ => Nat.zero_le _) hk'
  have h2 : bigN wS ≤ side wS (bigN wS) (Tstar wS + 1) k := by
    unfold RadiiHist.side
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _)))
  have h3 : bigN wS = 1 + ∑ j ∈ Finset.range (Tstar wS + 1), (4 * wS.rho j + 21) := rfl
  omega

/-- **The torus is large against `D₀`**: `3 c₀ + 6 ≤ M n_T` (`c₀ = 10`, `M = 14 M₁`,
`n_T ≥ N ≥ 22`). -/
theorem ripeRem_hn :
    3 * wS.c0 + 6 ≤ wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS) := by
  have hT := ripeRem_hT (Tstar wS) (one_le_Tstar _) le_rfl
  have hM : 14 ≤ wS.M := by
    show 14 ≤ 14 * M1
    have := M1_pos; omega
  have hc : wS.c0 = 10 := rfl
  rw [hc]
  nlinarith

/-- **Lemma III.3.3 at the actual ripe window of `ripeRemHistory`** (T2/T3).  The unique component
`Z` of `Z^pre_T` is removed and ripe; for the boundary piece `G′ = 𝔹_T(U_T)` of its window, the box
`Z₀` and `X = ripeX Z` the reference problem (2.34) has exactly one solution in the tube, for data
in the tube (every hypothesis of `psiZero_exists_unique` verified at this window). -/
theorem ripeRem_psiZero_exists_unique (N : ℕ) [NeZero N] :
    ∃ Z : ripeRemHistory.Comp (Tstar wS), Z.1 ∈ ripeRemHistory.rem (Tstar wS) ∧
      wS.Ripe (Tstar wS) (ripeRemHistory.bk (Tstar wS) Z) ∧
      ∃ hW : ripeRemHistory.RipeWindow (Tstar wS) Z,
        (windowOfHistory ripeRemHistory Z (wGeo _) (Nat.le_succ _) hW).Hyp ∧
        ∃ (b0 : Torus wS.d (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS) *
            wS.L ^ (Tstar wS - Tstar wS))) (w : Fin wS.d → ℕ),
          (∀ i, 1 ≤ w i ∧ w i ≤ 3 * wS.c0 + 4) ∧
          (∀ x : Torus wS.d (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS) *
              wS.L ^ Tstar wS),
            (jBlock wS.d wS.L (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS)) (Tstar wS)
              (Tstar wS) x ∈ box b0 w ↔
              blockMap (wS.L ^ Tstar wS) (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS)) x ∈
                ripeRemHistory.Zzero (Tstar wS) Z)) ∧
          ∃ K c11 : ℝ, 0 < K ∧ 0 < c11 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ c11 →
            ∀ ψk : BlockField wS.d wS.L (wS.M * side wS (bigN wS) (Tstar wS + 1) (Tstar wS))
                (Tstar wS) N,
              TubeOn (windowOfHistory ripeRemHistory Z (wGeo _) (Nat.le_succ _) hW).bdry
                  (ripeX ripeRemHistory Z \ box b0 w) δ ψk →
                ∃! ψ, PsiZeroSol (windowOfHistory ripeRemHistory Z (wGeo _) (Nat.le_succ _) hW).bdry
                  (compWeight wS.L 1) b0 w (ripeX ripeRemHistory Z) (K * δ) ψk ψ := by
  obtain ⟨Z, hrem, hrip, hW, hhyp⟩ := ripeRemHistory_windowOfHistory_hyp
  refine ⟨Z, hrem, hrip, hW, hhyp, ?_⟩
  exact psiZero_exists_unique_ripe ripeRemHistory Z (wGeo _) wS_good wS_h18 wS_hR0 (Nat.le_succ _)
    hW le_rfl ripeRem_hT (one_le_Tstar _) (fun j => wR_eq j) (by show 2 ≤ 3; norm_num)
    ripeRem_hn _ (wS_bgHyp _ _) N

end Concrete

end Balaban.Inhabited.RLane
