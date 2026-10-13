/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepIdentityFibreObs
public import Balaban.Fluctuation.RootTermFamily
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The zero-class observable coefficients as a family with the root's clauses

For a fixed chart datum `D` of the fibre `h ≡ h₀`, the coefficients `mObs y i (rawOf D, g) T'` of
`obsFamily_pair_fibre_fromTower` (with `q = 1`) are regrouped by `rootTermFamily_of_cubeFamily`
into a family `U x X g` indexed by site, polymer and source, with the root's support, locality,
analyticity and decay clauses, and with the paired sum
`∑ x, ∑ X, ∑ i, g x i * U x X g i = β_U^{-1/2} ∑ y, ∑ i, g y i * ℳ₀(y; g)_i`.
The family `mObs` and its bound constant are chosen before the datum and the decay rate.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

open Classical in
/-- **The zero-class observable coefficients with the root's clauses.**  At the scale data of
`obsFamily_pair_fibre_fromTower` with `q = 1` there are a bound constant `B ≥ 0` and a family
`mObs y i θ T'` (chosen before the datum), such that for every chart datum `D` of the fibre
and every `κroot > 0` with `c1 3 3 * κroot ≤ (3/2) κ_dec` there is `U x X g` that vanishes unless
`x ∈ X` and `X` is a polymer, is local in `g` on `X`, is analytic in `g` on the unit `ℓ¹` ball,
is bounded by `B e^{(3/2) κ_dec} e^{-κroot |X| / (M 3^{k+1})^3}` on the half ball, and pairs with
the source to `β_U^{-1/2} ∑ g ℳ₀`. -/
theorem rootTermFamily_obs_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (_h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      ∀ (_ : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ _hp : 0 < S.p₁,
      ∃ (B : ℝ) (mObs : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → physParam 2 S →
          Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
            Set.univ) → ℂ), 0 ≤ B ∧
        ∀ (D : BgData S.G' 2) (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' S.a S.ν (k + 1) 1 T.t D →
          ∀ κroot : ℝ, 0 < κroot → c1 3 3 * κroot ≤ 3 / 2 * T.κdec →
          ∃ U : CTorus 3 3 N₁ T.m₁ (k + 1) → Finset (CTorus 3 3 N₁ T.m₁ (k + 1)) →
              (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ) → (Fin 2 → ℂ),
            (∀ x X, ¬ (x ∈ X ∧ IsPolymer 3 ((N₁ * 3 ^ T.m₁) * 3 ^ (k + 1))
                (3 ^ (T.m₁ + 1) * 3 ^ (k + 1)) X) → U x X = 0) ∧
            (∀ x X g g', (∀ y ∈ X, g y = g' y) → U x X g = U x X g') ∧
            (∀ x X, AnalyticOnNhd ℂ (U x X)
              {g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ | ∑ y, ∑ i, ‖g y i‖ < 1}) ∧
            (∀ x X g, ∑ y, ∑ i, ‖g y i‖ ≤ 1 / 2 →
              ‖U x X g‖ ≤ B * Real.exp (3 / 2 * T.κdec) *
                Real.exp (-κroot * (X.card : ℝ) /
                  ((3 ^ (T.m₁ + 1) * 3 ^ (k + 1) : ℕ) : ℝ) ^ 3)) ∧
            (∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∀ x i, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), U x X g i =
                ∑ T', mObs x i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub 2 S.G'), g) T') ∧
            ∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
              ∑ x, ∑ X : Finset (CTorus 3 3 N₁ T.m₁ (k + 1)), ∑ i, g x i * U x X g i =
                ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                  ∑ y : CTorus 3 3 N₁ T.m₁ (k + 1), ∑ i : Fin 2,
                    g y i * (S.withDatum D hDh).M0C
                      (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g y i := by
  classical
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ := obsFamily_pair_fibre_fromTower T hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ Dsc S hS hp
  obtain ⟨Lb, hLb, Lab, εH, hεH, A, mObs, -, hsite, hval⟩ :=
    H k hk N₁ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ 1 one_pos le_rfl Dsc S hS hp
  have hrate := obsFamilyRate_eq_tower T
  have hcl : ∀ y i, ∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
      (K := k + 1) 1 (k + 1) Set.univ),
      AnalyticOnNhd ℂ (fun θ => mObs y i θ T') (physVq S S.a₁ S.ν T.t 1) ∧
      (∀ θ ∈ physVq S S.a₁ S.ν T.t 1, mObs y i θ T' ≠ 0 →
        rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
      (∀ θ ∈ physVq S S.a₁ S.ν T.t 1, ∀ θ' ∈ physVq S S.a₁ S.ν T.t 1,
        agreeOn (thickSet S.G' (sitesOf T'))
          (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (θ'.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) →
        (∀ x ∈ sitesOf T', θ.2 x = θ'.2 x) → mObs y i θ T' = mObs y i θ' T') := by
    intro y i T'
    obtain ⟨-, -, -, -, -, -, -, -, hfam⟩ := hsite y i (by
      subst hS
      exact obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) _ le_rfl
        (Dsc.covers.2 (y, i)).1 (Dsc.covers.2 (y, i)).2.2.1)
    exact ⟨(hfam T').1, (hfam T').2.2.1, (hfam T').2.2.2.1⟩
  have hb : ∀ y i, ∃ b : ℝ, ∀ T', ∀ θ ∈ physVq S S.a₁ S.ν T.t 1,
      ‖mObs y i θ T'‖ ≤ b * Real.exp (-(3 / 2 * T.κdec) * dExt T') := by
    intro y i
    obtain ⟨-, -, -, -, -, -, -, -, hfam⟩ := hsite y i (by
      subst hS
      exact obsDomains_isDj (X₁f := LocalCover.nbhdF 1 y) _ le_rfl
        (Dsc.covers.2 (y, i)).1 (Dsc.covers.2 (y, i)).2.2.1)
    exact ⟨_, fun T' θ hθ => by
      have := (hfam T').2.1 θ hθ
      rw [show Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T') =
        Real.exp (-(3 / 2 * T.κdec) * dExt T') by rw [hrate]] at this
      exact this⟩
  choose b hb using hb
  refine ⟨∑ y, ∑ i, |b y i|, mObs, ?_, ?_⟩
  · positivity
  intro D hDh hX κroot hκ hc
  have hmem : ∀ g : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
      ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub 2 S.G'), g) ∈ physVq S S.a₁ S.ν T.t 1 := by
    intro g hg
    rw [physVq_one]
    exact ⟨⟨D, hX, rfl⟩, hg⟩
  have hBnn : 0 ≤ ∑ y, ∑ i, |b y i| := by positivity
  have hN3 : (3 : ℕ) ∣ N₁ := h3N
  obtain ⟨U, h1, h2, h3', h4, h5⟩ := rootTermFamily_of_cubeFamily (d := 3) (L := 3) (N₁ := N₁)
    (m₁ := T.m₁) (K := k + 1) (N := 2) hN3
    (fun y i g T' => mObs y i ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub 2 S.G'), g) T')
    (κ := κroot) (lam := 3 / 2 * T.κdec) (B := ∑ y, ∑ i, |b y i|) hκ hc hBnn
    (fun x i g hg T' h0 => (hcl x i T').2.1 _ (hmem g hg) h0)
    (fun x i T' g hg g' hg' hag =>
      (hcl x i T').2.2 _ (hmem g hg) _ (hmem g' hg') (fun _ _ => ⟨rfl, rfl⟩) hag)
    (fun x i T' => (hcl x i T').1.comp
      (analyticOnNhd_const.prod analyticOnNhd_id) (fun g hg => hmem g hg))
    (fun x i T' g hg => by
      refine (hb x i T' _ (hmem g (by linarith))).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      refine (le_abs_self _).trans ?_
      exact (Finset.single_le_sum (f := fun i => |b x i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)).trans
        (Finset.single_le_sum (f := fun y => ∑ i, |b y i|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ x)))
  refine ⟨U, h1, h2, h3', h4, fun g hg x i => h5 g hg x i, fun g hg => ?_⟩
  rw [pairing_of_regroup (fun y i g T' => mObs y i
    ((⟨rawOf D, rawOf_mem_rawSub D⟩ : rawSub 2 S.G'), g) T') U g (fun x i => h5 g hg x i)]
  exact (hval D hDh hX g hg).2.symm

end Balaban.Inhabited
