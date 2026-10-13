/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCollarCentered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Fibres and regrouped terms for the centred collar hull

The fibre count, the regrouped family, its sum identity and decay bound, and the covariance of the
fibre and of the regrouped family under the generated symmetry group, for the centred collar hull
`detCollarHullC q` (odd block size `L = 2 q + 1` for the symmetry statements).  The landed
statements for the hull of `DetCollarHull.lean` are the case `q = 1`.

* `detCollarFibreC_one`, `detCollarGroupedC_one`: the case `q = 1` is the landed fibre and the
  landed regrouped family.
* `detCollarHullC_fibre`: the number of `T` with centred hull `X` is at most
  `2^{c₁ (1 + sizeJ X)}`.
* `sum_detCollarGroupedC`, `detCollarGroupedC_bound`: total sum, and decay bound with the landed
  `hullRate`, `hullConst`.
* `cubeAct_mem_detCollarFibreC_iff`, `image_cubeAct_detCollarFibreC`, `detCollarGroupedC_comp`:
  covariance under `GenSymm` for `L = 2 q + 1`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Background Balaban.Localization.DecEquiv

section Fibre

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- The regrouped family `e⁺(X) = ∑_{H_q(T) = X} e(T)` for the centred hull. -/
noncomputable def detCollarGroupedC {E : Type*} [AddCommMonoid E] (q : ℕ) (e : Finset 𝔅 → E)
    (X : Set (CTorus d L N₁ m₁ K)) : E :=
  ∑ T ∈ detCollarFibreC (m₀ := m₀) q X, e T

/-- At `q = 1` the centred fibre is the landed fibre. -/
theorem detCollarFibreC_one (hN : L ^ m₀ ∣ N₁) (X : Set (CTorus d L N₁ m₁ K)) :
    detCollarFibreC (m₀ := m₀) 1 X = detCollarFibre m₀ X := by
  ext T
  rw [mem_detCollarFibreC, mem_detCollarFibre, detCollarHullC_one hN]

/-- At `q = 1` the centred regrouped family is the landed one. -/
theorem detCollarGroupedC_one {E : Type*} [AddCommMonoid E] (hN : L ^ m₀ ∣ N₁)
    (e : Finset 𝔅 → E) (X : Set (CTorus d L N₁ m₁ K)) :
    detCollarGroupedC 1 e X = detCollarGrouped e X := by
  unfold detCollarGroupedC detCollarGrouped
  rw [detCollarFibreC_one hN]

/-- **Fibre count.**  For `X ∈ 𝒟_K`, the number of sets `T` with `H_q(T) = X` is at most
`2^{c₁ (1 + sizeJ X)}`. -/
theorem detCollarHullC_fibre {q : ℕ} (hN : L ^ m₀ ∣ N₁) {X : Set (CTorus d L N₁ m₁ K)}
    (hX : IsDj m₀ K X) :
    ((detCollarFibreC (m₀ := m₀) q X).card : ℝ) ≤ (2 : ℝ) ^ (c1 d L * (1 + sizeJ m₀ K X)) := by
  classical
  have hsub : detCollarFibreC (m₀ := m₀) q X ⊆ (blocksOf m₀ K Set.univ X).powerset := by
    intro T hT
    rw [mem_detCollarFibreC] at hT
    refine Finset.mem_powerset.2 fun b hb => mem_blocksOf.2 ?_
    rw [← hT]
    exact box_subset_detCollarHullC hb
  have h1 : (detCollarFibreC (m₀ := m₀) q X).card ≤ 2 ^ (blocksOf m₀ K Set.univ X).card := by
    simpa using Finset.card_le_card hsub
  have h2 : (((blocksOf m₀ K Set.univ X).card : ℕ) : ℝ) ≤ c1 d L * (1 + sizeJ m₀ K X) :=
    card_blocksOf_le hN (le_refl K) hX
  calc ((detCollarFibreC (m₀ := m₀) q X).card : ℝ)
      ≤ ((2 ^ (blocksOf m₀ K Set.univ X).card : ℕ) : ℝ) := by exact_mod_cast h1
    _ = (2 : ℝ) ^ (((blocksOf m₀ K Set.univ X).card : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]; push_cast; rfl
    _ ≤ (2 : ℝ) ^ (c1 d L * (1 + sizeJ m₀ K X)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h2

/-- **The sum identity**: regrouping does not change the total. -/
theorem sum_detCollarGroupedC {E : Type*} [AddCommMonoid E] (q : ℕ) (e : Finset 𝔅 → E) :
    ∑ X ∈ (Finset.univ : Finset (Finset 𝔅)).image (detCollarHullC q),
        detCollarGroupedC q e X = ∑ T, e T := by
  classical
  have := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Finset 𝔅)))
    (t := (Finset.univ : Finset (Finset 𝔅)).image (detCollarHullC q)) (g := detCollarHullC q)
    (f := e) (fun T hT => Finset.mem_image_of_mem _ hT)
  rw [← this]
  refine Finset.sum_congr rfl fun X _ => ?_
  unfold detCollarGroupedC
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext T
  rw [mem_detCollarFibreC]
  simp

/-- **The regrouped bound** for the centred hull, with the landed `hullRate`, `hullConst`.
Needs `q + 1 ≤ L` (the centred box contains the cube). -/
theorem detCollarGroupedC_bound {q : ℕ} (hq : q + 1 ≤ L) (hN : L ^ m₀ ∣ N₁) {c lam : ℝ}
    (hc : 0 ≤ c) (hlam : 0 ≤ lam) (e : Finset 𝔅 → ℂ)
    (hsupp : ∀ T, e T ≠ 0 → IsPolyDom m₀ K (sitesOf T))
    (hb : ∀ T, ‖e T‖ ≤ c * Real.exp (-lam * dExt T)) (X : Set (CTorus d L N₁ m₁ K)) :
    ‖detCollarGroupedC q e X‖ ≤
      hullConst d L lam c * Real.exp (-hullRate d L lam * sizeJ m₀ K X) := by
  classical
  have hB := collarB_nonneg d L
  have hpos : 0 ≤ hullConst d L lam c * Real.exp (-hullRate d L lam * sizeJ m₀ K X) := by
    unfold hullConst; positivity
  by_cases hex : ∃ T ∈ detCollarFibreC (m₀ := m₀) q X, e T ≠ 0
  swap
  · push Not at hex
    have : detCollarGroupedC q e X = 0 := Finset.sum_eq_zero hex
    rw [this, norm_zero]; exact hpos
  obtain ⟨T0, hT0, hne⟩ := hex
  have hX : IsDj m₀ K X := by
    rw [← mem_detCollarFibreC.1 hT0]
    exact (detCollarHullC_isDj hq hN (hsupp T0 hne)).1
  set s := sizeJ m₀ K X with hs
  set M : ℝ := c * Real.exp (-lam * (s - collarB d L) / (1 + collarB d L)) with hM
  have hterm : ∀ T ∈ detCollarFibreC (m₀ := m₀) q X, ‖e T‖ ≤ M := by
    intro T hT
    by_cases h0 : e T = 0
    · rw [h0, norm_zero, hM]; positivity
    · have hTX := mem_detCollarFibreC.1 hT
      have h1 := (detCollarHullC_sizeJ_le hq hN (hsupp T h0)).2
      rw [hTX] at h1
      refine (hb T).trans ?_
      rw [hM]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hc
      have hp : 0 < 1 + collarB d L := by linarith
      rw [le_div_iff₀ hp]
      nlinarith
  have hfib := detCollarHullC_fibre (q := q) hN hX
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  calc ‖detCollarGroupedC q e X‖ ≤ ∑ T ∈ detCollarFibreC (m₀ := m₀) q X, ‖e T‖ :=
        norm_sum_le _ _
    _ ≤ ∑ T ∈ detCollarFibreC (m₀ := m₀) q X, M := Finset.sum_le_sum hterm
    _ = (detCollarFibreC (m₀ := m₀) q X).card * M := by simp
    _ ≤ (2 : ℝ) ^ (c1 d L * (1 + s)) * M := mul_le_mul_of_nonneg_right hfib hM0
    _ = hullConst d L lam c * Real.exp (-hullRate d L lam * s) := by
        rw [Real.rpow_def_of_pos (by norm_num), hM, hullConst, hullRate]
        have hp : (1 + collarB d L) ≠ 0 := by linarith
        have : Real.log 2 * (c1 d L * (1 + s)) + -lam * (s - collarB d L) / (1 + collarB d L) =
            (lam * collarB d L / (1 + collarB d L) + c1 d L * Real.log 2) +
              -(lam / (1 + collarB d L) - c1 d L * Real.log 2) * s := by
          field_simp
          ring
        calc Real.exp (Real.log 2 * (c1 d L * (1 + s))) *
              (c * Real.exp (-lam * (s - collarB d L) / (1 + collarB d L)))
            = c * Real.exp (Real.log 2 * (c1 d L * (1 + s)) +
                -lam * (s - collarB d L) / (1 + collarB d L)) := by
              rw [Real.exp_add]; ring
          _ = _ := by rw [this, Real.exp_add]; ring

/-- `T` has centred hull `X` exactly when `σ • T` has centred hull `σ '' X`. -/
theorem cubeAct_mem_detCollarFibreC_iff {q : ℕ} (hL : L = 2 * q + 1) (hN : L ^ m₀ ∣ N₁)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (h : GenSymm L N₁ m₁ K K m₀ σ)
    {X : Set (CTorus d L N₁ m₁ K)} {T : Finset 𝔅} :
    cubeAct σ T ∈ detCollarFibreC (m₀ := m₀) q (σ '' X) ↔ T ∈ detCollarFibreC (m₀ := m₀) q X := by
  rw [mem_detCollarFibreC, mem_detCollarFibreC, detCollarHullC_cubeAct_genSymm hL hN h]
  exact σ.injective.image_injective.eq_iff

/-- `σ •` maps the centred fibre of `X` bijectively onto the fibre of `σ '' X`: image form. -/
theorem image_cubeAct_detCollarFibreC {q : ℕ} (hL : L = 2 * q + 1) (hN : L ^ m₀ ∣ N₁)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (h : GenSymm L N₁ m₁ K K m₀ σ)
    (X : Set (CTorus d L N₁ m₁ K)) :
    (detCollarFibreC (m₀ := m₀) q X).image (cubeAct σ) = detCollarFibreC (m₀ := m₀) q (σ '' X) := by
  classical
  have hg := genSymm_mem_pavingSymGroup h
  ext T'
  rw [Finset.mem_image]
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact (cubeAct_mem_detCollarFibreC_iff hL hN h).2 hT
  · intro hT'
    refine ⟨cubeAct σ⁻¹ T', ?_, ?_⟩
    · have e : cubeAct σ (cubeAct σ⁻¹ T') = T' := by
        simpa using cubeAct_cubeAct hN (inv_mem hg) T'
      exact (cubeAct_mem_detCollarFibreC_iff hL hN h).1 (by rw [e]; exact hT')
    · simpa using cubeAct_cubeAct hN (inv_mem hg) T'

/-- **Regrouping is covariant**: if `e' (σ • T) = e T` for all `T`, then
`e⁺' (σ '' X) = e⁺ X` for `L = 2 q + 1` and every `σ` of the generated group. -/
theorem detCollarGroupedC_comp {E : Type*} [AddCommMonoid E] {q : ℕ} (hL : L = 2 * q + 1)
    (hN : L ^ m₀ ∣ N₁) {σ : Equiv.Perm (CTorus d L N₁ m₁ K)}
    (h : GenSymm L N₁ m₁ K K m₀ σ)
    {e e' : Finset 𝔅 → E} (he : ∀ T, e' (cubeAct σ T) = e T) (X : Set (CTorus d L N₁ m₁ K)) :
    detCollarGroupedC q e' (σ '' X) = detCollarGroupedC q e X := by
  unfold detCollarGroupedC
  rw [← image_cubeAct_detCollarFibreC hL hN h X,
    Finset.sum_image (fun T _ T' _ e => cubeAct_injective hN (genSymm_mem_pavingSymGroup h) e)]
  exact Finset.sum_congr rfl fun T _ => he T

end Fibre

section DetStep

open Balaban.Analysis Matrix

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} {m₀ : ℕ}
  {z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))} {eps κ'' cdet : ℝ}

/-- **The regrouped determinant terms** for the centred hull:
`det⁺_q(X; D) = ∑_{H_q(T) = X} term D T`. -/
noncomputable def DetExpansionLocC.detGroupedC (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (q : ℕ) (D : BgData S.G' N) (X : Set (CTorus d L N₁ m₁ (k + 1))) : ℂ :=
  detCollarGroupedC q (fun T => E.term D T) X

/-- At `q = 1` the centred regrouped determinant terms are the landed ones. -/
theorem DetExpansionLocC.detGroupedC_one (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    (hN : L ^ m₀ ∣ N₁) (D : BgData S.G' N) (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    E.detGroupedC 1 D X = E.detGrouped D X :=
  detCollarGroupedC_one hN _ X

theorem DetExpansionLocC.detGroupedC_sum (E : DetExpansionLocC S m₀ z eps κ'' cdet) (q : ℕ)
    {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (K := k + 1) m₀ (k + 1) Set.univ))).image (detCollarHullC q), E.detGroupedC q D X =
      rootTrace S.G' S.a S.a₁ S.ν (unitQ S.G') (unitP S.G') (S.blockU z) (fun _ => 1)
        (svec S.G' (bgFieldC S.G' S.a S.ν (bgC0 d L N) D))
        (bgMultC S.G' S.a S.ν (bgC0 d L N) D) := by
  rw [E.sum_eq D hD]
  exact sum_detCollarGroupedC q (fun T => E.term D T)

theorem DetExpansionLocC.detGroupedC_bound (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    {q : ℕ} (hq : q + 1 ≤ L) (hN : L ^ m₀ ∣ N₁) (hc : 0 ≤ cdet) (hκ : 0 ≤ κ'')
    {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (X : Set (CTorus d L N₁ m₁ (k + 1))) :
    ‖E.detGroupedC q D X‖ ≤
      hullConst d L κ'' cdet * Real.exp (-hullRate d L κ'' * sizeJ m₀ (k + 1) X) :=
  detCollarGroupedC_bound hq hN hc hκ (fun T => E.term D T)
    (fun T hT => (E.anchor D hD T hT).2) (E.bound D hD) X

theorem DetExpansionLocC.detGroupedC_anchor (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    {q : ℕ} (hq : q + 1 ≤ L) (hN : L ^ m₀ ∣ N₁)
    {D : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    {X : Set (CTorus d L N₁ m₁ (k + 1))} (hX : E.detGroupedC q D X ≠ 0) :
    IsPolyDom m₀ (k + 1) X ∧
      box (rootCube (m₀ := m₀) (K := k + 1) z).1 (cellSide L m₀ m₁ (k + 1)) ⊆ X := by
  obtain ⟨T, hT, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hX
  have hTX := mem_detCollarFibreC.1 hT
  obtain ⟨hroot, hpoly⟩ := E.anchor D hD T hne
  subst hTX
  exact ⟨isPolyDom_of_isDj (detCollarHullC_isDj hq hN hpoly).1, box_subset_detCollarHullC hroot⟩

theorem DetExpansionLocC.detGroupedC_local (E : DetExpansionLocC S m₀ z eps κ'' cdet)
    {q : ℕ} (hq : 1 ≤ q) (hL : q + 2 ≤ L) (hN : L ^ m₀ ∣ N₁) (h3 : 3 ≤ L ^ (m₀ + m₁))
    {D D₂ : BgData S.G' N} (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps D)
    (hD₂ : XiCData S.G' S.a S.ν (k + 1) 1 eps D₂)
    {X : Set (CTorus d L N₁ m₁ (k + 1))}
    (h : ∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) :
    E.detGroupedC q D X = E.detGroupedC q D₂ X := by
  unfold DetExpansionLocC.detGroupedC detCollarGroupedC
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTX := mem_detCollarFibreC.1 hT
  refine E.term_eq_of_agree_cellNear hN h3 hD hD₂ T fun v ⟨x, hx, hxv⟩ => h v ?_
  rw [← hTX]
  exact cellNear_mem_detCollarHullC hq hL hN hx hxv

end DetStep

section Record

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ} {m₀ : ℕ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

open Classical in
/-- **Covariance of the centred regrouped determinant terms** under every symmetry of the
generated group, for `L = 2 q + 1`: the statement of `exists_detExpansionLocC_grouped_sym` with
`detGroupedC q`. -/
theorem exists_detExpansionLocC_groupedC_sym
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hδc : 0 ≤ δc)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hconn : HatConn S.G') (hN : L ^ m₀ ∣ N₁)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (hG : IsLevel S.G' (k + 1)) {q : ℕ} (hL : L = 2 * q + 1)
    {σ : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (h : GenSymm L N₁ m₁ (k + 1) (k + 1) m₀ σ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    ∃ (E : DetExpansionLocC S m₀ z eps
        ((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
        ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))))
      (E' : DetExpansionLocC S m₀ (rootAct σ z) eps
        ((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
        ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))))),
      ∃ Sy : LatSymm S.G' S.G' σ,
        (∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
          XiCData S.G' S.a S.ν (k + 1) 1 eps (Sy.sym D)) ∧
        (∀ (D : BgData S.G' N) T, E'.term (Sy.sym D) (cubeAct σ T) = E.term D T) ∧
        ∀ (D : BgData S.G' N) (X : Set (CTorus d L N₁ m₁ (k + 1))),
          E'.detGroupedC q (Sy.sym D) (σ '' X) = E.detGroupedC q D X := by
  obtain ⟨E, E', Sy, h1, h2⟩ := exists_detExpansionLocC_sym S hC hδc hMX hdm hα hsm hconn hN hz
    hG h z
  exact ⟨E, E', Sy, h1, h2, fun D X => detCollarGroupedC_comp hL hN h (h2 D) X⟩

end Record

end Balaban.Fluctuation
