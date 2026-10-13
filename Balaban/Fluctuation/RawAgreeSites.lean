/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocExpUnion
public import Balaban.Fluctuation.MarkFibreSitesOf
public import Balaban.Fluctuation.ParamActivityPhysical
public import Balaban.Fluctuation.ParamActivitySubspace
public import Balaban.Fluctuation.PhysicalTerms
public import Balaban.Fluctuation.RenormExpBounds

/-!
# Agreement on a set of sites: the two languages

The interface `IsLocExp` states locality through `RawAgree Y` for a finset `Y` of sites, while the
coefficient families state it through `agreeOn A` and `physRestrict A` for a set `A` of sites.
This file proves the bridge between the two: `RawAgree Y p p' ↔ agreeOn ↑Y p p'`, the description of
equality of `physRestrict` on `physIncl` of two parameters as agreement of the raw datum and of the
source, the transport of a locality statement of a coefficient function on `physV` to the `local_`
clause of `IsLocExp`, and the identity of the size functionals `renDY = sizeJ = dExt`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Multiscale

variable {d L N₁ m₁ K k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-! ### T1: finsets and sets of sites -/

omit [NeZero N₁] [NeZero L] in
/-- `RawAgree Y` is `agreeOn` on the underlying set of `Y` (the site types coincide). -/
theorem rawAgree_iff_agreeOn (Y : Finset (CTorus d L N₁ m₁ K))
    (p p' : RawData d L (N₁ * L ^ m₁) K N) :
    RawAgree Y p p' ↔ agreeOn (↑Y : Set (CTorus d L N₁ m₁ K)) p p' :=
  Iff.rfl

omit [NeZero N₁] [NeZero L] in
/-- `RawAgree Y` for a finset `Y` whose underlying set is `A`. -/
theorem rawAgree_iff_agreeOn_of_coe_eq {Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Set (CTorus d L N₁ m₁ K)} (hY : (↑Y : Set (CTorus d L N₁ m₁ K)) = A)
    (p p' : RawData d L (N₁ * L ^ m₁) K N) : RawAgree Y p p' ↔ agreeOn A p p' := by
  subst hY; exact Iff.rfl

omit [NeZero N₁] [NeZero L] in
/-- Agreement on `sitesOf T` in the language of `RawAgree`. -/
theorem rawAgree_iff_agreeOn_sitesOf {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
    {T : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω)}
    {Y : Finset (CTorus d L N₁ m₁ K)} (hY : (↑Y : Set (CTorus d L N₁ m₁ K)) = sitesOf T)
    (p p' : RawData d L (N₁ * L ^ m₁) K N) : RawAgree Y p p' ↔ agreeOn (sitesOf T) p p' :=
  rawAgree_iff_agreeOn_of_coe_eq hY p p'

/-! ### T2: the parameter space -/

section Param

variable (S : StepSetting d L N₁ m₁ k N ϱ)

/-- Equal restrictions of `physIncl` of two parameters to a set `A` of sites are the same as
agreement of the raw data on `A` together with equality of the sources on `A`. -/
theorem physRestrict_physIncl_eq_iff (A : Set (CTorus d L N₁ m₁ (k + 1))) (θ θ' : physParam N S) :
    physRestrict A (physIncl N S θ) = physRestrict A (physIncl N S θ') ↔
      agreeOn A (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (θ'.1 : RawData d L (N₁ * L ^ m₁)
        (k + 1) N) ∧ ∀ x ∈ A, θ.2 x = θ'.2 x := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · have := congrFun h ⟨x, hx⟩
      simp only [physRestrict, physIncl_apply, Prod.mk.injEq] at this
      exact ⟨this.1, this.2.1⟩
    · have := congrFun h ⟨x, hx⟩
      simp only [physRestrict, physIncl_apply, Prod.mk.injEq] at this
      exact this.2.2
  · rintro ⟨h1, h2⟩
    funext x
    simp only [physRestrict, physIncl_apply, Prod.mk.injEq]
    exact ⟨(h1 x.1 x.2).1, (h1 x.1 x.2).2, h2 x.1 x.2⟩

/-- The same, for a finset `Y` of sites. -/
theorem physRestrict_physIncl_eq_iff_rawAgree (Y : Finset (CTorus d L N₁ m₁ (k + 1)))
    (θ θ' : physParam N S) :
    physRestrict (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) (physIncl N S θ) =
        physRestrict (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) (physIncl N S θ') ↔
      RawAgree Y (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)
        (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∧ ∀ x ∈ Y, θ.2 x = θ'.2 x :=
  physRestrict_physIncl_eq_iff S _ θ θ'

/-- A datum in the chart with real fixed `h` is in the chart `Ξ^c`: `XiCOneReal` is the case
`h'' = 0` of `XiCData` with `σ = 1`. -/
theorem xiCData_of_xiCOneReal {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν ε : ℝ}
    {D : BgData G N} (h : XiCOneReal G a ν ε D) : XiCData G a ν K 1 ε D := by
  obtain ⟨Ψ₀, h₀, Ψ'', hX, hR⟩ := h
  exact ⟨Ψ₀, h₀, Ψ'', 0, hX, hR⟩

/-- The datum of `XiCOneReal` with a source in the unit `ℓ¹` ball is a point of `physSΛ`, and
`⟨rawOf D, _⟩ , g₀` is a point of `physV`. -/
theorem mem_physV_of_xiCOneReal {a₁ ν eps : ℝ} {D : BgData S.G' N}
    (hD : XiCOneReal S.G' (compWeight L a₁) ν eps D)
    {g₀ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hg : g₀ ∈ l1Ball d L N₁ m₁ (k + 1) N) :
    ((⟨rawOf D, rawOf_mem_rawSub D⟩ : ↥(rawSub N S.G')), g₀) ∈ physV S a₁ ν eps :=
  ⟨⟨D, xiCData_of_xiCOneReal hD, rfl⟩, hg⟩

open Classical in
/-- **Transport of locality to the `local_` clause of `IsLocExp`.**  Let `c` be a function on the
parameter space with `c θ = c θ'` whenever `θ, θ' ∈ physV` have equal restrictions to a set `A`
contained in `↑Y`.  Let `Dom` be a class of data with `(rawOf D, g₀) ∈ physSΛ` for `Dom D`
(for `Dom = XiCOneReal …` this is `mem_physV_of_xiCOneReal`).  Then the term
`q ↦ c (q.1, g₀)` (zero off `rawSub`) satisfies the `local_` clause at `Y` on `expDom S.G' Dom r`. -/
theorem local_of_physRestrict {a₁ ν eps r : ℝ} (Dom : BgData S.G' N → Prop)
    (Y : Finset (CTorus d L N₁ m₁ (k + 1))) (A : Set (CTorus d L N₁ m₁ (k + 1)))
    (hAY : A ⊆ (↑Y : Set (CTorus d L N₁ m₁ (k + 1)))) (c : physParam N S → ℂ)
    (g₀ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (hDom : ∀ D, Dom D → (rawOf D, g₀) ∈ physSΛ S a₁ ν eps)
    (hc : ∀ θ ∈ physV S a₁ ν eps, ∀ θ' ∈ physV S a₁ ν eps,
      physRestrict A (physIncl N S θ) = physRestrict A (physIncl N S θ') → c θ = c θ') :
    ∀ q ∈ expDom S.G' Dom r, ∀ q' ∈ expDom S.G' Dom r, q.2 = q'.2 →
      RawAgree Y q.1 q'.1 →
      (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) =>
        if h : q.1 ∈ (rawSub N S.G' : Set _) then c (⟨q.1, h⟩, g₀) else 0) q =
      (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) =>
        if h : q.1 ∈ (rawSub N S.G' : Set _) then c (⟨q.1, h⟩, g₀) else 0) q' := by
  rintro q ⟨D, hD, h1, -⟩ q' ⟨D', hD', h1', -⟩ - hag
  have e1 : q.1 = rawOf D := h1
  have e1' : q'.1 = rawOf D' := h1'
  rw [e1, e1'] at hag
  simp only [e1, e1']
  simp only [SetLike.mem_coe, rawOf_mem_rawSub, dite_true]
  refine hc _ (hDom D hD) _ (hDom D' hD') ?_
  rw [physRestrict_physIncl_eq_iff]
  exact ⟨fun x hx => hag x (hAY hx), fun _ _ => rfl⟩

end Param

/-! ### T3: the size functional -/

section Size

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- On the sites of a cube set `T` at the level `K` of the generating set, `renDY = sizeJ`. -/
theorem renDY_eq_sizeJ_sitesOf (hG : IsLevel G K) (T : Finset 𝔅)
    (Y : Finset (CTorus d L N₁ m₁ K)) (hY : (↑Y : Set (CTorus d L N₁ m₁ K)) = sitesOf T) :
    renDY G m₀ Y = sizeJ m₀ K (sitesOf T) := by
  rw [renDY_eq_sizeJ hG, hY]

/-- On a polymer cube set, `renDY = sizeJ = dExt`. -/
theorem renDY_eq_dExt_of_isPolyDom (hN : L ^ m₀ ∣ N₁) (hG : IsLevel G K) (T : Finset 𝔅)
    (hT : IsPolyDom m₀ K (sitesOf T)) (Y : Finset (CTorus d L N₁ m₁ K))
    (hY : (↑Y : Set (CTorus d L N₁ m₁ K)) = sitesOf T) :
    renDY G m₀ Y = sizeJ m₀ K (sitesOf T) ∧ sizeJ m₀ K (sitesOf T) = dExt T :=
  ⟨renDY_eq_sizeJ_sitesOf hG T Y hY, ((markFibre_sitesOf.{0} (K := K) hN).1 T hT).2.symm⟩

end Size

end Balaban.Fluctuation
