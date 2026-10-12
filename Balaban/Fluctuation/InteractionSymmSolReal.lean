/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionSymmSolConj
public import Balaban.Fluctuation.InteractionSymmSolRot

/-!
# Reality of the expansion terms of a functional of `(φ_{k+1}, δφ, Θ, ψ')`

`fnOfDecSol_conj`: for real data `u = (Θ, ψ')` the expanded function satisfies
`F(u, conj s) = conj F(u, s)` on the polydisc if the functional `Φ` is real; `evTermSol_real` is
the resulting reality of the terms.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix
  Balaban.Fluctuation

local notation "cj" => starRingEnd ℂ

section Terms

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ K)}
variable {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ K)}

/-- Real data `u = (Θ, ψ')` of the expansion. -/
def IsRealU (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) : Prop :=
  IsRealRaw u.1 ∧ ∀ x i, (u.2 x i).im = 0

/-- The fluctuation datum of a conjugated background is the conjugated fluctuation datum, for
real `Ψ`. -/
theorem flEdat_conj (φα : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Ψ ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) (hΨ : ∀ x i, (Ψ x i).im = 0) :
    flEdat Gp Hm (fun p => cj (φα.1 p), fun x => cj (φα.2 x)) Ψ ψ' =
      (DecEquiv.cjSite (flEdat Gp Hm φα Ψ ψ').1, fun x => cj ((flEdat Gp Hm φα Ψ ψ').2.1 x),
        (flEdat Gp Hm φα Ψ ψ').2.2.1, (flEdat Gp Hm φα Ψ ψ').2.2.2) := by
  classical
  unfold flEdat
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext x i
    simp only [barField, DecEquiv.cjSite]
    by_cases h : x ∈ Gp.Ω 1
    · simp [h]
    · simp only [h, dite_false]
      exact (Complex.conj_eq_iff_im.2 (hΨ x i)).symm
  · funext y
    simp only [flAlpha]
    split_ifs <;> simp

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **The function expanded for a real functional is real** on the polydisc, for real data. -/
theorem fnOfDecSol_conj
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) δφ u, IsRealU u →
      cj (Φ bg δφ u) = Φ (fun p => cj (bg.1 p), fun x => cj (bg.2 x)) (fun p => cj (δφ p)) u)
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) (hreal : IsRealU u)
    {s : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ}
    (hs : s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ)
      (fun _ => Real.exp κ)) :
    fnOfDec Gp Hm X₁f F₁ Sol Φ u (cjv s) = cj (fnOfDec Gp Hm X₁f F₁ Sol Φ u s) := by
  obtain ⟨⟨D, hD, hDu⟩, hψ⟩ := hu
  obtain ⟨u1, ψ'⟩ := u
  have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 hs'
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  have hcs : ∀ i, ‖cjv s i‖ < Real.exp κ := fun i => by simpa [cjv] using hs' i
  have hsx' : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (cjv s) P‖ <
      Real.exp κ := norm_extParams_lt hE1 hcs
  have hs1' := extParams_hs1 (X₁f := X₁f) (Gp := Gp) (cjv s)
  have hDu' : u1 = rawOf D := hDu
  subst hDu'
  have hDreal : D.IsReal := fun x i => hreal.1 x i
  have hψreal : ∀ x, DecEquiv.IsRealVec (ψ' x) := fun x =>
    DecEquiv.isRealVec_of_im fun i => hreal.2 x i
  have hΨreal : ∀ x i, (D.Ψ x i).im = 0 := fun x i => (hDreal x i).1
  have hext : extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (cjv s) =
      fun P => cj (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P) := by
    classical
    funext P
    unfold extParams cjv
    split_ifs <;> simp
  obtain ⟨φ, α, δφ, δα, hI, hF, hstr, hS, -⟩ := point_facts_core hC hF₁ hSol hsx hs1 hD hψ
  obtain ⟨φ', α', δφ', δα', hI', hF', hstr', hS', -⟩ :=
    point_facts_core hC hF₁ hSol hsx' hs1' hD hψ
  have hcj := F₁_conj hC hF₁ hsx hD hDreal
  have hF'' : F₁ (fun P => cj (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P), rawOf D) =
      (fun p => cj (φ p), fun x => cj (α x)) := by rw [hcj, hF]
  rw [hext] at hF'
  have hpa : (φ', α') = (fun p => cj (φ p), fun x => cj (α x)) := by rw [← hF', hF'']
  obtain ⟨h1, h2⟩ := Prod.mk.inj hpa
  subst φ'
  subst α'
  have hE := flEdat_conj (Gp := Gp) (Hm := Hm) (φ, α) D.Ψ ψ' hΨreal
  have hSolr := Sol_conj hSol hsx
    (φ₀ := (flEdat Gp Hm (φ, α) D.Ψ ψ').1) (α₀ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.1)
    (δΨ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.1) (f₁ := (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.2)
    hψreal (by intro p; simp [flEdat]) hstr (by rw [← hE]; exact hstr')
  have key : Sol (fun P => cj (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P),
      flEdat Gp Hm (fun p => cj (φ p), fun x => cj (α x)) D.Ψ ψ') =
      (fun p => cj ((Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
        flEdat Gp Hm (φ, α) D.Ψ ψ')).1 p),
       fun x => cj ((Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
        flEdat Gp Hm (φ, α) D.Ψ ψ')).2 x)) := by
    rw [hE]; exact hSolr
  unfold fnOfDec
  show Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (cjv s), rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (cjv s),
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (cjv s),
          rawOf D)) D.Ψ ψ')).1 (rawOf D, ψ') = _
  rw [hext, hF'']
  erw [key]
  show _ = cj (Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D))
    (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s,
      flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D)) D.Ψ ψ')).1
    (rawOf D, ψ'))
  rw [hF, hΦ (φ, α) _ (rawOf D, ψ') hreal]

/-- **The expansion terms of a real functional are real for real data.** -/
theorem evTermSol_real
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ}
    (hΦ : ∀ (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) δφ u, IsRealU u →
      cj (Φ bg δφ u) = Φ (fun p => cj (bg.1 p), fun x => cj (bg.2 x)) (fun p => cj (δφ p)) u)
    (Y : Set (CTorus d L N₁ m₁ K))
    {u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁) (hreal : IsRealU u) :
    cj (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ X₁
        (fnOfDec Gp Hm X₁f F₁ Sol Φ) Y u) =
      evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ X₁
        (fnOfDec Gp Hm X₁f F₁ Sol Φ) Y u :=
  evTerm_conj _ (Real.one_lt_exp_iff.2 hC.hκ) X₁ Y
    fun _ hs => fnOfDecSol_conj hC hF₁ hSol hΦ hu hreal hs

end Terms

end Balaban.Localization
