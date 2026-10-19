/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.BgTransport
public import Balaban.Fluctuation.ParamActivitySubspace
public import Balaban.Fluctuation.HatLabelsDirect
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Direct-label terms computed on a background generating set

Ruling R8 (P3 pp. 78-79, (4.44)-(4.47)): the terms of the new level are recomputed inside each term
on a background generating set `Gb`; the hat variable of the step is restricted to the unit
lattice of `Gb` by `Tr.res`, and the raw datum of the step is read by the term through `Tr.dat`.

`DirectTerms` is already generic in the map `emb` from the hat variable to the variables of the
expansion, and `DirectTermsFamilyOn` in the parameter map `J`; the generating set enters through
these two maps only.  Hence:

* `DirectTermsBg S m₀ hp Gb Tr embB …`: `DirectTerms` with the embedding `embB ∘ Tr.res` of the hat
  variable of the step through the unit lattice of `Gb` (`embB` defined on that lattice).  At
  `Gb = S.G'`, `Tr = BgTransport.self`, it is `DirectTerms` (`directTermsBg_self`, by `rfl`), so
  every lemma on `DirectTerms`, `DirectTermsFamily`, `DirectTermsFamilyOn`, `labelAct_of_directTerms`,
  `dtAct`, `labelActFamilyOn`, `paramMarkFamilyOn_of_marks` applies to the terms on `Gb`;
* `physInclTr Tr`: the parameter map of the step's parameter space `physParam N S = rawSub × sources`
  into the ambient space `RawData × sources` of data of `Gb`, `θ ↦ (Tr.dat θ.1, θ.2)`;
* `physVTr Tr a₁ ν eps`: the parameters whose datum read through `Tr` lies in the admissible set
  `physSΛBg Gb a₁ ν eps` of `Gb`, open in `physParam N S` (`isOpen_physVTr`);
* `physical_directTermsFamilyOn_Tr`: the relative family hypothesis over `physVTr` with
  `J = physInclTr Tr`;
* `physInclTr_self`, `physVTr_self`: for the step's own transport, `physIncl` and `physV`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Metric

section Direct

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {Λ F' : Type}
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
  (hp : 0 < S.p₁)
  (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) (Tr : BgTransport S.G' Gb N)

/-- **The direct-label input computed on a background generating set `Gb`.**  `DirectTerms` with
the variables of the expansion `embB (Tr.res ψ̂)`, the hat variable `ψ̂` of the step restricted to
the unit lattice of `Gb` by the transport.  For `Gb = S.G'` and `Tr = BgTransport.self` this is
`DirectTerms` (`directTermsBg_self`). -/
abbrev DirectTermsBg (embB : (unitPts Gb × Fin N → ℂ) → F') (ρ Rσ εU a : ℝ) (Θ₀ : Λ)
    (SΛ : Set Λ) (XW : Set (F' × F')) (val : F' → F' → ℂ → Λ → ℂ)
    (AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop)
    (AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop) : Type :=
  DirectTerms S m₀ hp (fun ψ => embB (Tr.res ψ)) ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF

/-- **At the step's own set the terms on `Gb` are the landed direct terms.** -/
theorem directTermsBg_self (emb : (S.U × Fin N → ℂ) → F') (ρ Rσ εU a : ℝ) (Θ₀ : Λ)
    (SΛ : Set Λ) (XW : Set (F' × F')) (val : F' → F' → ℂ → Λ → ℂ)
    (AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop)
    (AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop) :
    DirectTermsBg S m₀ hp S.G' (BgTransport.self S.hG') emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF =
      DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF := rfl

/-- **`DirectTermsBg` is inhabited with a nonempty family** (`nonempty_directTerms`): the terms on
`Gb` are zero and the family of domains is `{univ}`, for every step, transport and `εU ≥ 0`. -/
theorem nonempty_directTermsBg (ρ Rσ εU a : ℝ) (hεU : 0 ≤ εU) :
    ∃ I : DirectTermsBg S m₀ hp Gb Tr (F' := Unit) (fun _ => ()) ρ Rσ εU a (0 : ℂ) Set.univ
      Set.univ (fun _ _ _ _ => (0 : ℂ)) (fun _ _ _ => True) (fun _ _ _ => True),
      I.𝒴.Nonempty :=
  nonempty_directTerms S m₀ hp ρ Rσ εU a hεU

end Direct

section Param

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  (Tr : BgTransport S.G' Gb N)

/-- **The parameter map of the terms on `Gb`**: the parameter `θ = (raw datum, source)` of the step
goes to the datum `(Tr.dat θ.1, θ.2)` of `Gb`, in the ambient space of raw data and sources. -/
noncomputable def physInclTr : physParam N S →L[ℂ] RawData d L (N₁ * L ^ m₁) (k + 1) N ×
    (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :=
  ((LinearMap.toContinuousLinearMap Tr.dat).prodMap (ContinuousLinearMap.id ℂ _)).comp
    (physIncl N S)

theorem physInclTr_apply (e : physParam N S) :
    physInclTr S Tr e = (Tr.dat (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), e.2) := rfl

/-- **The admissible parameters of the terms on `Gb`**: those whose datum read through `Tr` lies in
the admissible set `physSΛBg Gb a₁ ν eps` of `Gb`. -/
def physVTr (a₁ ν eps : ℝ) : Set (physParam N S) :=
  physInclTr S Tr ⁻¹' physSΛBg Gb a₁ ν eps

/-- For the step's own transport the parameter map is `physIncl`. -/
theorem physInclTr_self : physInclTr S (BgTransport.self (N := N) S.hG') = physIncl N S :=
  ContinuousLinearMap.ext fun _ => rfl

/-- For the step's own transport the admissible set is `physV`. -/
theorem physVTr_self (a₁ ν eps : ℝ) :
    physVTr S (BgTransport.self (N := N) S.hG') a₁ ν eps = physV S a₁ ν eps := by
  unfold physVTr physV physVBg
  rw [physInclTr_self]
  rfl

/-- **`physVTr` is open** in the parameter space of the step: it is the preimage of the open set
`physVBg` of the parameter space of `Gb` under `θ ↦ (Tr.dat θ.1, θ.2)`, which is continuous. -/
theorem isOpen_physVTr (hT : Tr.Reads) (a₁ ν eps : ℝ)
    (H : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν) : IsOpen (physVTr S Tr a₁ ν eps) := by
  have hc : Continuous (fun e : physParam N S =>
      ((⟨Tr.dat (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), hT (bgOfRaw e.1.1 e.1.2)⟩ :
        rawSub N Gb), e.2) : physParam N S → physParamBg N Gb) := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_snd
    exact (LinearMap.continuous_of_finiteDimensional Tr.dat).comp
      (continuous_subtype_val.comp continuous_fst)
  exact (isOpen_physVBg Gb a₁ ν eps H).preimage hc

/-- **The relative family hypothesis for the terms on `Gb`.**  If the diagonal terms are continuous
on the admissible set `physSΛBg Gb` of `Gb`, then `DirectTermsFamilyOn` holds over the parameters
`physVTr` of the step with the parameter map `physInclTr`, for the source agreement `physAgΘ`
(raw datum of `Gb` and source on `Y`). -/
theorem physical_directTermsFamilyOn_Tr (hT : Tr.Reads) (m₀ : ℕ) {F' : Type} {hp : 0 < S.p₁}
    {embB : (unitPts Gb × Fin N → ℂ) → F'} {ρ Rσ εU a a₁ ν eps : ℝ}
    {Θ₀ : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)}
    {XW : Set (F' × F')} {val : F' → F' → ℂ →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
    {I : DirectTermsBg S m₀ hp Gb Tr embB ρ Rσ εU a Θ₀ (physSΛBg Gb a₁ ν eps) XW val
      (physAgΘ S) AgF}
    (hcont : DiagCont (fun ψ => embB (Tr.res ψ)) XW (physSΛBg Gb a₁ ν eps) Rσ I.𝒴 I.T)
    (H : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν) :
    DirectTermsFamilyOn S m₀ (physInclTr S Tr) I (physVTr S Tr a₁ ν eps) where
  isOpen := isOpen_physVTr S Tr hT a₁ ν eps H
  sub := fun _ ⟨_, he, h⟩ => h ▸ he
  agΘ := fun _ _ Y => physAgΘ_refl S Y _
  cont := fun Y hY σ hσ Θ ⟨_, he, h⟩ => hcont Y hY σ hσ Θ (h ▸ he)

end Param

end Balaban.Fluctuation
