/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfConstTerm
public import Balaban.Spine.FinalSfUniv
public import Balaban.Spine.FinalRegroupAct
public import Balaban.Spine.FinalBoxTorus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The remainder terms of the last scale as activities

A6-3, gas layer. The remainder `ℛ^{(k)}(T; h, h, g) = Σ_{n ≤ m} Σ_{X ∈ 𝒟_k} ℛ^{(k)}_n(X; h, h, g)` at
the constant configuration (P5 (1.16)–(1.17); the part of the exponent `X₀` of `constExponentR`)
read on the torus `𝕋_ℓ` as activities of the polymers `X` of `𝒟_k` (`rObs`, the instance of
`polyObs` for the terms `rObsTerm`):

* `sum_rObs_eq`, `sum_rObs_eq_Rres`: `Σ_X rObs(X; g) = ℛ^{(k)}(T; h, h, g)`;
* `rObs_eq_zero_of_not_isPolymer`, `rObs_local`, `rObs_analytic`: they vanish off the scale-`k`
  polymers of Root-F, depend on `g|_X` only and are analytic on the unit `ℓ¹` ball;
* `norm_rObs_sub_le`: the increments are at most `2 m β_k^{-2} e^{-κ_flow d_k(X)}` (P5 H4,
  `RTermsH4`, with the factor `fac = 1` of the class); `norm_rObs_sub_le_exp`: in Root-F's form,
  `2 m β_k^{-2} e^{κ_flow} e^{-κ_R |X|/(M L^k)^d}` when `c₁ (κ_R + 1) ≤ κ_flow`;
* `torusClausesAt_rObs`: regrouped at the scale `k + 1` (`regroupFam`), the four per-torus clauses
  at the rate `κ_R - d log L - 1` (the split-rate regrouping `norm_regroupAt_sub_le` at
  `λ = d log L`).
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.Multiscale Balaban.Background

namespace Balaban.RootFSpine

section Def

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The term of the remainder activities**: `Σ_{n=1}^{m₀+m₁} ℛ^{(k)}_n(X; h, h, g)` on the
Def-6 torus `N₁`, at the constant configuration `ψ = h`. -/
noncomputable def rObsTerm (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    (ℓ N₁ : ℕ) [NeZero N₁] (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  ∑ nn ∈ Finset.Icc 1 (m₀ + m₁),
    sf.Rt N₁ nn (sfPre N₁ ℓ X) (Def6.constFld (hC hv)) (Def6.constFld (hC hv))
      (fun y => g (sfSite ℓ y))

/-- **The remainder activities of the last scale** on the torus `𝕋_ℓ`: the terms `rObsTerm` on the
polymers of `𝒟_k` (`polyObs` at the scale `k`). -/
noncomputable def rObs (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    (ℓ : ℕ) (X : Finset (Torus d ℓ)) (g : Torus d ℓ → Fin N → ℂ) : ℂ :=
  polyObs (L := L) (m₁ := m₁) (k := k) m₀ (fun ℓ N₁ _ _ => rObsTerm sf m₀ hv ℓ N₁) ℓ k X g

open Classical in
/-- **`Σ_X rObs(X; g)` on a torus `ℓ = N₁ L^{m₁} L^k`** is the double sum of the remainder terms
over the polymers of `𝒟_k`, the source read through `sfSite`. -/
theorem sum_rObs_eq (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    {N₁ ℓ : ℕ} [NeZero N₁] [NeZero ℓ] (hℓ : ℓ = N₁ * L ^ m₁ * L ^ k) (hk1 : 1 ≤ k)
    (g : Torus d ℓ → Fin N → ℂ) :
    ∑ X : Finset (Torus d ℓ), rObs sf m₀ hv ℓ X g =
      ∑ nn ∈ Finset.Icc 1 (m₀ + m₁), ∑ᶠ X ∈ {X : Set (CTorus d L N₁ m₁ k) |
          Def6.IsPolyDom m₀ k X},
        sf.Rt N₁ nn X (Def6.constFld (hC hv)) (Def6.constFld (hC hv))
          (fun y => g (sfSite ℓ y)) := by
  subst hℓ
  have hL : ∀ X : Finset (Torus d (N₁ * L ^ m₁ * L ^ k)),
      rObs sf m₀ hv (N₁ * L ^ m₁ * L ^ k) X g =
        ∑ nn ∈ Finset.Icc 1 (m₀ + m₁),
          if Def6.IsPolyDom m₀ k (X : Set (CTorus d L N₁ m₁ k)) then
            sf.Rt N₁ nn (X : Set (CTorus d L N₁ m₁ k)) (Def6.constFld (hC hv))
              (Def6.constFld (hC hv)) (fun y => g (sfSite (N₁ * L ^ m₁ * L ^ k) y)) else 0 := by
    intro X
    unfold rObs
    rw [polyObs_eq_explicit]
    by_cases hP : Def6.IsPolyDom m₀ k (X : Set (CTorus d L N₁ m₁ k))
    · simp only [hk1, le_rfl, hP, and_self, ↓reduceIte]
      unfold rObsTerm
      rw [sfPre_eq_coe]
    · simp [hP]
  simp_rw [hL]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun nn _ => ?_
  rw [finsum_mem_eq_toFinset_sum, Set.toFinset_ofPred, Finset.sum_filter]
  exact Fintype.sum_equiv Fintype.finsetEquivSet _ _ fun X => rfl

end Def

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

open Classical in
/-- **`Σ_X rObs(X; g) = ℛ^{(k)}(T; h, h, g)`** on the torus of a context: the remainder of the
small-field factor of the whole torus at the constant configuration. -/
theorem sum_rObs_eq_Rres (C : SFCtx S n R M K N k m₁ ϱ) (hv : EuclideanSpace ℝ (Fin N))
    (hk1 : 1 ≤ k) (g : GIdx S n M K N → ℂ) :
    ∑ X : Finset (Torus S.d (M * n K * S.L ^ K)),
        rObs C.sf C.m₀ hv (M * n K * S.L ^ K) X (fun x i => g (x, i)) =
      C.Rres Set.univ (fun _ => hv) hv g := by
  rw [sum_rObs_eq C.sf C.m₀ hv (fine_eq_def6 C) hk1, Rres_univ, sfG_eq_sfSite C g]
  rfl

end Ctx


section Clauses

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **Support**: the remainder activities vanish off the scale-`k` polymers of Root-F. -/
theorem rObs_eq_zero_of_not_isPolymer (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ)
    (hv : EuclideanSpace ℝ (Fin N)) {N₁ M : ℕ} [NeZero N₁] (hN : L ^ m₀ ∣ N₁)
    (hM : M = L ^ (m₀ + m₁)) {X : Finset (Torus d (N₁ * L ^ m₁ * L ^ k))}
    (hX : ¬ IsPolymer d (N₁ * L ^ m₁ * L ^ k) (M * L ^ k) X)
    (g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ) :
    rObs sf m₀ hv (N₁ * L ^ m₁ * L ^ k) X g = 0 :=
  polyObs_eq_zero_of_not_isPolymer hN hM _ (fun h => hX h.2) g

/-- **Locality**: the remainder activities depend on `g|_X` only (the clause `loc` of P5 H4). -/
theorem rObs_local {P6 : Def6.Consts} {sf : SFData d L m₁ k N ϱ} {fac : ℕ → ℝ}
    (hRt : ∀ (N₁ : ℕ) [NeZero N₁], RTermsH4 (ϱ := ϱ) P6 sf.β sf.ν sf.a N₁ (sf.Rt N₁) fac)
    (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N)) {ℓ : ℕ} (X : Finset (Torus d ℓ))
    {g g' : Torus d ℓ → Fin N → ℂ} (hgg : ∀ y ∈ X, g y = g' y) :
    rObs sf m₀ hv ℓ X g = rObs sf m₀ hv ℓ X g' := by
  refine polyObs_local m₀ _ X fun hN => ?_
  have : NeZero (ℓ / (L ^ m₁ * L ^ k)) := ⟨hN⟩
  unfold rObsTerm
  refine Finset.sum_congr rfl fun nn _ => ?_
  exact (hRt (ℓ / (L ^ m₁ * L ^ k))).loc nn _ _ _ _ _ _ _ fun z hz => ⟨rfl, rfl, hgg _ hz⟩

end Clauses

section Bound

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **The constant configuration is in the domain of the remainder terms** (`Ξ^c_k(·; 1, ε_k)` of
P5 H4, `xiDom_const`; the top generating set has no layers above `k`). -/
theorem rObsTerm_constDom {P6 : Def6.Consts} {sf : SFData d L m₁ k N ϱ} {N₁ : ℕ} [NeZero N₁]
    (hBgR : BgHyp d L k ϱ (Def6.aIdeal L k (sf.a k)) (Def6.bgMass L k (sf.β k) (sf.ν k)))
    (hε : 0 < P6.eps d L k) (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1) :
    Def6.XiDom (Def6.topGS d L N₁ m₁ k ϱ) (Def6.aIdeal L k (sf.a k))
      (Def6.bgMass L k (sf.β k) (sf.ν k)) k (P6.eps d L k) (Def6.constFld (hC hv))
      (Def6.constFld (hC hv)) :=
  xiDom_const hBgR (fun i hi => by simp [Def6.topGS, levelGS, show ¬ i ≤ k by omega]) le_rfl hε
    (fun i => hv i) (sum_sq_eq_one_of_norm_eq_one hv hunit)

open Classical in
/-- The remainder activities on the torus `ℓ = N₁ L^{m₁} L^k`, written on the sites of the Def-6
torus. -/
theorem rObs_eq_explicit (sf : SFData d L m₁ k N ϱ) (m₀ : ℕ) (hv : EuclideanSpace ℝ (Fin N))
    {N₁ : ℕ} [NeZero N₁] (hk1 : 1 ≤ k) (X : Finset (Torus d (N₁ * L ^ m₁ * L ^ k)))
    (g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ) :
    rObs sf m₀ hv (N₁ * L ^ m₁ * L ^ k) X g =
      if Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ k
          (X : Set (CTorus d L N₁ m₁ k)) then
        ∑ nn ∈ Finset.Icc 1 (m₀ + m₁), sf.Rt N₁ nn (X : Set (CTorus d L N₁ m₁ k))
          (Def6.constFld (hC hv)) (Def6.constFld (hC hv)) g
      else 0 := by
  classical
  unfold rObs
  rw [polyObs_eq_explicit]
  by_cases hP : Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ k
      (X : Set (CTorus d L N₁ m₁ k))
  · simp only [hk1, le_rfl, hP, and_self, ↓reduceIte]
    unfold rObsTerm
    simp only [sfPre_eq_coe, sfSite_eq_self]
  · simp [hP]

/-- **Analyticity** of the remainder activities on the unit `ℓ¹` ball (P5 H4, analyticity on the
domain, at the constant configuration). -/
theorem rObs_analytic {P6 : Def6.Consts} {sf : SFData d L m₁ k N ϱ} {fac : ℕ → ℝ}
    (hRt : ∀ (N₁ : ℕ) [NeZero N₁], RTermsH4 (ϱ := ϱ) P6 sf.β sf.ν sf.a N₁ (sf.Rt N₁) fac)
    (hBgR : BgHyp d L k ϱ (Def6.aIdeal L k (sf.a k)) (Def6.bgMass L k (sf.β k) (sf.ν k)))
    (hε : 0 < P6.eps d L k) (hk1 : 1 ≤ k) (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    {N₁ : ℕ} [NeZero N₁] (X : Finset (Torus d (N₁ * L ^ m₁ * L ^ k))) :
    AnalyticOnNhd ℂ (rObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) X) {g | ∑ y, ∑ i, ‖g y i‖ < 1} := by
  classical
  have e := funext fun g => rObs_eq_explicit sf P6.m₀ hv hk1 X g
  rw [e]
  by_cases hP : Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P6.m₀ k
      (X : Set (CTorus d L N₁ m₁ k))
  · simp only [hP, ↓reduceIte]
    refine Finset.analyticOnNhd_fun_sum _ fun nn hnn => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hnn
    have hA := (hRt N₁).analytic nn h1 h2 _ hP
    have hΦ : AnalyticOnNhd ℂ (fun g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ =>
        ((Def6.constFld (hC hv) : Fld d L N₁ m₁ k N),
          (Def6.constFld (hC hv) : Fld d L N₁ m₁ k N), g))
        {g | ∑ y, ∑ i, ‖g y i‖ < 1} :=
      analyticOnNhd_const.prod (analyticOnNhd_const.prod analyticOnNhd_id)
    exact hA.comp hΦ fun g hg => ⟨rObsTerm_constDom hBgR hε hv hunit, fun _ => Set.mem_univ _,
      (l1_le_sum g).trans_lt hg⟩
  · simp only [hP, ↓reduceIte]
    exact analyticOnNhd_const

/-- **The bound of the remainder activities** on a polymer of `𝒟_k` (P5 H4 with `fac = 1`, at `g`
and at `0`): `‖q(X; g) - q(X; 0)‖ ≤ 2 m β_k^{-2} e^{-κ_flow d_k(X)}`, `m = m₀ + m₁`, `β_k ≥ 1`. -/
theorem norm_rObs_sub_le {P6 : Def6.Consts} {sf : SFData d L m₁ k N ϱ}
    (hRt : ∀ (N₁ : ℕ) [NeZero N₁], RTermsH4 (ϱ := ϱ) P6 sf.β sf.ν sf.a N₁ (sf.Rt N₁) fun _ => 1)
    (hBgR : BgHyp d L k ϱ (Def6.aIdeal L k (sf.a k)) (Def6.bgMass L k (sf.β k) (sf.ν k)))
    (hε : 0 < P6.eps d L k) (hk1 : 1 ≤ k) (hβ : 1 ≤ sf.β k) (hv : EuclideanSpace ℝ (Fin N))
    (hunit : ‖hv‖ = 1) {N₁ : ℕ} [NeZero N₁] {X : Finset (Torus d (N₁ * L ^ m₁ * L ^ k))}
    (hP : Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P6.m₀ k
      (X : Set (CTorus d L N₁ m₁ k)))
    {g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ} (hg : ∑ y, ∑ i, ‖g y i‖ < 1) :
    ‖rObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) X g - rObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) X 0‖ ≤
      2 * ((P6.m₀ + m₁ : ℕ) : ℝ) * ((sf.β k)⁻¹) ^ 2 *
        Real.exp (-P6.κ * sizeJ P6.m₀ k (X : Set (CTorus d L N₁ m₁ k))) := by
  classical
  rw [rObs_eq_explicit sf P6.m₀ hv hk1 X g, rObs_eq_explicit sf P6.m₀ hv hk1 X 0]
  simp only [hP, ↓reduceIte]
  have hdom := rObsTerm_constDom (N₁ := N₁) hBgR hε hv hunit
  have hb0 : 0 ≤ (sf.β k)⁻¹ := inv_nonneg.2 (by linarith)
  have hb1 : (sf.β k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ
  set E := Real.exp (-P6.κ * sizeJ P6.m₀ k (X : Set (CTorus d L N₁ m₁ k))) with hE
  have hterm : ∀ nn ∈ Finset.Icc 1 (P6.m₀ + m₁), ∀ g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ,
      ∑ y, ∑ i, ‖g y i‖ < 1 →
      ‖sf.Rt N₁ nn (X : Set (CTorus d L N₁ m₁ k)) (Def6.constFld (hC hv))
        (Def6.constFld (hC hv)) g‖ ≤ ((sf.β k)⁻¹) ^ 2 * E := by
    intro nn hnn g hg
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hnn
    refine ((hRt N₁).bound nn h1 h2 _ hP _ _ g hdom (fun _ => Set.mem_univ _)
      ((l1_le_sum g).trans_lt hg)).trans ?_
    rw [one_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    exact pow_le_pow_of_le_one hb0 hb1 (by omega)
  have h0 : ∑ y, ∑ i, ‖(0 : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ) y i‖ < 1 := by simp
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ nn ∈ Finset.Icc 1 (P6.m₀ + m₁), 2 * (((sf.β k)⁻¹) ^ 2 * E) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun nn hnn =>
          (norm_sub_le _ _).trans (by linarith [hterm nn hnn g hg, hterm nn hnn 0 h0]))
    _ = _ := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring


/-- **The bound of the remainder activities in Root-F's form**: on the torus `ℓ = N₁ L^{m₁} L^k`,
for every `X`, `‖q(X; g) - q(X; 0)‖ ≤ 2 m β_k^{-2} e^{κ_flow} e^{-κ_R |X|/(M L^k)^d}` when
`c₁ (κ_R + 1) ≤ κ_flow` (`|X| ≤ c₁ (M L^k)^d (1 + d_k(X))`, `G1_card`; `decay_arith`). -/
theorem norm_rObs_sub_le_exp {P6 : Def6.Consts} {sf : SFData d L m₁ k N ϱ}
    (hRt : ∀ (N₁ : ℕ) [NeZero N₁], RTermsH4 (ϱ := ϱ) P6 sf.β sf.ν sf.a N₁ (sf.Rt N₁) fun _ => 1)
    (hBgR : BgHyp d L k ϱ (Def6.aIdeal L k (sf.a k)) (Def6.bgMass L k (sf.β k) (sf.ν k)))
    (hε : 0 < P6.eps d L k) (hk1 : 1 ≤ k) (hβ : 1 ≤ sf.β k) (hv : EuclideanSpace ℝ (Fin N))
    (hunit : ‖hv‖ = 1) {N₁ M : ℕ} [NeZero N₁] (hN : L ^ P6.m₀ ∣ N₁) (hM : M = L ^ (P6.m₀ + m₁))
    {κR : ℝ} (hκR : 0 < κR) (hκf : Fluctuation.c1 d L * (κR + 1) ≤ P6.κ)
    (X : Finset (Torus d (N₁ * L ^ m₁ * L ^ k))) {g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ}
    (hg : ∑ y, ∑ i, ‖g y i‖ < 1) :
    ‖rObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) X g - rObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) X 0‖ ≤
      2 * ((P6.m₀ + m₁ : ℕ) : ℝ) * ((sf.β k)⁻¹) ^ 2 * Real.exp P6.κ *
        Real.exp (-κR * (X.card : ℝ) / (((M * L ^ k : ℕ) : ℝ)) ^ d) := by
  classical
  set B0 : ℝ := 2 * ((P6.m₀ + m₁ : ℕ) : ℝ) * ((sf.β k)⁻¹) ^ 2 with hB0
  have hB0n : 0 ≤ B0 := by positivity
  by_cases hP : Def6.IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P6.m₀ k
      (X : Set (CTorus d L N₁ m₁ k))
  · refine (norm_rObs_sub_le hRt hBgR hε hk1 hβ hv hunit hP hg).trans ?_
    have hG := Fluctuation.G1_card (m₀ := P6.m₀) hN le_rfl (isDj_of_isPolyDom hP)
    have hs : 0 ≤ sizeJ P6.m₀ k (X : Set (CTorus d L N₁ m₁ k)) :=
      treeLenCovOne_nonneg P6.m₀ k _
    have hcs : ((cellSide L P6.m₀ m₁ k : ℕ) : ℝ) = ((M * L ^ k : ℕ) : ℝ) := by
      unfold cellSide; rw [hM, ← pow_add]; congr 2; omega
    have had : 0 < (((M * L ^ k : ℕ) : ℝ)) ^ d := by
      rw [← hcs]; have := cellSide_pos (L := L) P6.m₀ m₁ k; positivity
    have hcard : ((X : Set (CTorus d L N₁ m₁ k)).ncard : ℝ) = X.card := by
      rw [Set.ncard_coe_finset]
    have hc1 : 0 ≤ Fluctuation.c1 d L := by unfold Fluctuation.c1; positivity
    have hc9 : B0 ≤ 2 * B0 * Real.exp P6.κ / 2 * Real.exp (-P6.κ) := by
      rw [show 2 * B0 * Real.exp P6.κ / 2 * Real.exp (-P6.κ) =
        B0 * (Real.exp P6.κ * Real.exp (-P6.κ)) by ring, ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, mul_one]
    have hdec := decay_arith (κ := κR) (κf := P6.κ) (c9 := 2 * B0 * Real.exp P6.κ) (c9f := B0)
      (s := sizeJ P6.m₀ k (X : Set (CTorus d L N₁ m₁ k))) (card := (X.card : ℝ))
      (ad := (((M * L ^ k : ℕ) : ℝ)) ^ d) (c1 := Fluctuation.c1 d L) hκR had hs hc1
      (by positivity) (by rw [← hcard, ← hcs]; exact hG) hκf hc9
    calc B0 * Real.exp (-P6.κ * sizeJ P6.m₀ k (X : Set (CTorus d L N₁ m₁ k)))
        ≤ 2 * B0 * Real.exp P6.κ / 2 * Real.exp (-κR * (X.card : ℝ) / (((M * L ^ k : ℕ) : ℝ)) ^ d) :=
          hdec
      _ = _ := by rw [hB0]; ring
  · rw [rObs_eq_explicit sf P6.m₀ hv hk1 X g, rObs_eq_explicit sf P6.m₀ hv hk1 X 0]
    simp only [hP, ↓reduceIte, sub_zero, norm_zero]
    positivity

/-- **The remainder activities regrouped at the scale `k + 1`** on a torus
`ℓ = N₁ L^{m₁} L^k`, `N₁ = L^{m₀} L m'`: the four clauses of `TorusClausesAt` with the amplitude
`2 m β_k^{-2} e^{κ_flow}` and the rate `κ_R - d log L - 1` (the regrouping with the split rate
`λ = d log L`, `norm_regroupAt_sub_le`; `L^d log(1 + L^{-d}) ≤ 1`). -/
theorem torusClausesAt_rObs {P6 : Def6.Consts} {sf : SFData d L m₁ k N ϱ}
    (hRt : ∀ (N₁ : ℕ) [NeZero N₁], RTermsH4 (ϱ := ϱ) P6 sf.β sf.ν sf.a N₁ (sf.Rt N₁) fun _ => 1)
    (hBgR : BgHyp d L k ϱ (Def6.aIdeal L k (sf.a k)) (Def6.bgMass L k (sf.β k) (sf.ν k)))
    (hε : 0 < P6.eps d L k) (hk1 : 1 ≤ k) (hβ : 1 ≤ sf.β k) (hv : EuclideanSpace ℝ (Fin N))
    (hunit : ‖hv‖ = 1) {M : ℕ} (hM : M = L ^ (P6.m₀ + m₁)) {N₁ m' : ℕ} [NeZero N₁] [NeZero m']
    [NeZero (L * m')] [NeZero (N₁ * L ^ m₁ * L ^ k)] (hN₁ : N₁ = L ^ P6.m₀ * (L * m'))
    {κR : ℝ} (hκR : 0 < κR) (hκRL : (d : ℝ) * Real.log L ≤ κR)
    (hκf : Fluctuation.c1 d L * (κR + 1) ≤ P6.κ) :
    TorusClausesAt d N L M k (κR - d * Real.log L - 1)
      (2 * ((P6.m₀ + m₁ : ℕ) : ℝ) * ((sf.β k)⁻¹) ^ 2 * Real.exp P6.κ) (N₁ * L ^ m₁ * L ^ k)
      (regroupFam M L k (fun ℓ => rObs sf P6.m₀ hv ℓ) (N₁ * L ^ m₁ * L ^ k) (k + 1)) := by
  have hN : L ^ P6.m₀ ∣ N₁ := ⟨L * m', hN₁⟩
  have hℓ : N₁ * L ^ m₁ * L ^ k = M * L ^ k * (L * m') := by rw [hN₁, hM, pow_add]; ring
  have hs : 0 < M * L ^ k := by
    rw [hM]; exact Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
      (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _)
  have hS : ∀ Y, ¬ IsPolymer d (N₁ * L ^ m₁ * L ^ k) (M * L ^ k) Y → ∀ g,
      rObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) Y g = rObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) Y 0 :=
    fun Y hY g => by
      rw [rObs_eq_zero_of_not_isPolymer sf P6.m₀ hv hN hM hY g,
        rObs_eq_zero_of_not_isPolymer sf P6.m₀ hv hN hM hY 0]
  have hA : ∀ Y, AnalyticOnNhd ℂ (rObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) Y)
      {g | ∑ y, ∑ i, ‖g y i‖ < 1} := fun Y => rObs_analytic hRt hBgR hε hk1 hv hunit Y
  have hLoc : ∀ Y (g g' : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ), (∀ y ∈ Y, g y = g' y) →
      rObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) Y g = rObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) Y g' :=
    fun Y g g' hgg => rObs_local hRt P6.m₀ hv Y hgg
  have hB : ∀ Y, IsPolymer d (N₁ * L ^ m₁ * L ^ k) (M * L ^ k) Y →
      ∀ g : Torus d (N₁ * L ^ m₁ * L ^ k) → Fin N → ℂ, ∑ y, ∑ i, ‖g y i‖ < 1 →
      ‖rObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) Y g - rObs sf P6.m₀ hv (N₁ * L ^ m₁ * L ^ k) Y 0‖ ≤
        2 * ((P6.m₀ + m₁ : ℕ) : ℝ) * ((sf.β k)⁻¹) ^ 2 * Real.exp P6.κ *
          Real.exp (-κR * (Y.card : ℝ) / (((M * L ^ k : ℕ) : ℝ)) ^ d) :=
    fun Y _ g hg => norm_rObs_sub_le_exp hRt hBgR hε hk1 hβ hv hunit hN hM hκR hκf Y hg
  have hB0 : 0 ≤ 2 * ((P6.m₀ + m₁ : ℕ) : ℝ) * ((sf.β k)⁻¹) ^ 2 * Real.exp P6.κ := by
    have : 0 ≤ (sf.β k)⁻¹ := inv_nonneg.2 (by linarith)
    positivity
  have hsupp := regroup_support (M := M) (L := L) (k := k)
    (t := fun ℓ => rObs sf P6.m₀ hv ℓ) (ℓ := N₁ * L ^ m₁ * L ^ k) hS
  have hana := regroup_analytic (M := M) (L := L) (k := k)
    (t := fun ℓ => rObs sf P6.m₀ hv ℓ) (ℓ := N₁ * L ^ m₁ * L ^ k) hA
  have hloc := regroup_local (M := M) (L := L) (k := k)
    (t := fun ℓ => rObs sf P6.m₀ hv ℓ) (ℓ := N₁ * L ^ m₁ * L ^ k) hLoc
  refine ⟨fun X hX g => hsupp (k + 1) X (fun h => hX h.2) g, fun X => hana (k + 1) X,
    fun X g g' hgg => hloc (k + 1) X g g' hgg, fun X g hg => ?_⟩
  rw [regroupFam_succ, regroupFam_succ]
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hcore := norm_regroupAt_sub_le (lam := (d : ℝ) * Real.log L) hℓ hs hB0 hκRL hS hB X hg
  refine hcore.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB0)
  have hlog : (L : ℝ) ^ d * Real.log (1 + Real.exp (-((d : ℝ) * Real.log L))) ≤ 1 := by
    have hLd : 0 < (L : ℝ) ^ d := by positivity
    have he : Real.exp (-((d : ℝ) * Real.log L)) = ((L : ℝ) ^ d)⁻¹ := by
      rw [Real.exp_neg, ← Real.log_pow, Real.exp_log hLd]
    rw [he]
    have hpos : (0 : ℝ) < 1 + ((L : ℝ) ^ d)⁻¹ := by positivity
    have hl : Real.log (1 + ((L : ℝ) ^ d)⁻¹) ≤ ((L : ℝ) ^ d)⁻¹ := by
      linarith [Real.log_le_sub_one_of_pos hpos]
    calc (L : ℝ) ^ d * Real.log (1 + ((L : ℝ) ^ d)⁻¹) ≤ (L : ℝ) ^ d * ((L : ℝ) ^ d)⁻¹ :=
          mul_le_mul_of_nonneg_left hl hLd.le
      _ = 1 := mul_inv_cancel₀ hLd.ne'
  have hP : 0 ≤ (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d := by positivity
  have e1 : ∀ c : ℝ, -c * (X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d =
      -c * ((X.card : ℝ) / ((M : ℝ) * (L : ℝ) ^ (k + 1)) ^ d) := fun c => by ring
  rw [e1, e1]
  nlinarith

end Bound

end Balaban.RootFSpine
