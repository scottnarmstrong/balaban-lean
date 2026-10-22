/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoDec2
public import Balaban.Polymer.LocalIsoBg
public import Balaban.Localization.Decoupled2Background
public import Balaban.Background.Equivariance
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the decoupled background and fluctuation problems

For a pair (cover `coverOf Gc`, operator set `H`) carried by the box map onto (`coverOf Hc`, `H'`)
(`OmegaIso Gc Hc ρ`, `OmegaIso H H' ρ`), the decoupled problems of Theorems I-4a and I-4b are
conjugate under the bijections `e` of the sites and `cubeEquiv` of the centres:

* `decFixed_iff`: the fixed-point equation `δα = 𝒩_s(δα)` of Theorem I-4a at corresponding data;
* `isDecBg_iff`: the decoupled background system of Theorem I-4b at data corresponding on the box
  of radius `ρ + 1`;
* `decBgField_eq`, `decBgMult_eq`: the decoupled background field and multiplier (unique choice);
* `decBg_value_eq`: **the values of maps with the defining property of the pair of Theorem
  I-4b** on the two tori correspond (uniqueness on the second torus, existence on the first);
* `decSol_value_eq`: **the values of maps with the defining property of the analytic solution of
  Theorem I-4a** correspond (uniqueness in the ball on the second torus).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Matrix

variable {d L N₁ N₁' m₁ K N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ' ϱc ϱc' : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)

namespace OmegaIso

variable {Gc : GeneratingSet d L (N₁ * L ^ m₁) K ϱc} {Hc : GeneratingSet d L (N₁' * L ^ m₁) K ϱc'}
  {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H' : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'}
  {ρ : ℕ} (hC : OmegaIso Gc Hc ρ) (hH : OmegaIso H H' ρ)

include hC hH

/-- The entries of the Green family of the decoupled problem at corresponding potentials. -/
theorem decG_entry (a : ℕ → ℝ) (ν : ℝ) {s : Dec2.DecParams (coverOf Gc)}
    {s' : Dec2.DecParams (coverOf Hc)} (hs : ∀ q : cubeIdx Gc, s' (hC.cubeEquiv q) = s q)
    (α : H.Ω 1 → ℂ) (α' : H'.Ω 1 → ℂ) (hα : ∀ x, α' (hH.e x) = α x) (x y : H.Ω 1) :
    Dec2.decG (coverOf Hc) H' a ν s' α' (hH.e x) (hH.e y) =
      Dec2.decG (coverOf Gc) H a ν s α x y :=
  entry_of_submatrix hH.e (hC.decG_submatrix hH a ν hs hα) x y

/-- **The fixed-point equation of Theorem I-4a at corresponding data.** -/
theorem decFixed_iff (a : ℕ → ℝ) (ν : ℝ) {s : Dec2.DecParams (coverOf Gc)}
    {s' : Dec2.DecParams (coverOf Hc)} (hs : ∀ q : cubeIdx Gc, s' (hC.cubeEquiv q) = s q)
    (ιU : Bool) {α₀ : H.Ω 1 → ℂ} {α₀' : H'.Ω 1 → ℂ} (hα₀ : ∀ x, α₀' (hH.e x) = α₀ x)
    {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} {φ₀' : CTorus d L N₁' m₁ K → Fin N → ℂ}
    (hφ : ∀ x : H.Ω 1, φ₀' (hH.e x) = φ₀ x)
    {Fs : H.Ω 1 × Fin N → ℂ} {Fs' : H'.Ω 1 × Fin N → ℂ} (hF : ∀ x i, Fs' (hH.e x, i) = Fs (x, i))
    {δα : H.Ω 1 → ℂ} {δα' : H'.Ω 1 → ℂ} (hδ : ∀ x, δα' (hH.e x) = δα x) :
    Dec2.DecFixed (coverOf Hc) H' a ν s' ιU α₀' φ₀' Fs' δα' ↔
      Dec2.DecFixed (coverOf Gc) H a ν s ιU α₀ φ₀ Fs δα := by
  have key : ∀ x, Nmap H' (dirichletOperator H' a ν α₀') ιU φ₀' Fs'
      (dphi H' (Dec2.decG (coverOf Hc) H' a ν s') α₀' φ₀' Fs' δα') (hH.e x) =
      Nmap H (dirichletOperator H a ν α₀) ιU φ₀ Fs
        (dphi H (Dec2.decG (coverOf Gc) H a ν s) α₀ φ₀ Fs δα) x := fun x =>
    Nmap_corr hH.e (entry_of_submatrix hH.e (hH.dirichletOperator_submatrix a ν hα₀)) ιU hφ hF
      (dphi_corr hH.e (fun α α' hα => hC.decG_entry hH a ν hs α α' hα) hα₀ hφ hF hδ) x
  unfold Dec2.DecFixed
  constructor
  · intro h
    funext x
    have := congrFun h (hH.e x)
    rwa [key, hδ] at this
  · intro h
    funext x'
    obtain ⟨x, rfl⟩ := hH.e.surjective x'
    rw [key, hδ, h]

omit hC in
/-- The approximate field of corresponding data at the sites of `Ω₁`. -/
theorem approxField_site (a : ℕ → ℝ) (ν : ℝ) {D : BgData H N} {D' : BgData H' N}
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h) (x : H.Ω 1) :
    approxField H' a ν D'.Ψ D'.h (hH.e x) = approxField H a ν D.Ψ D.h x :=
  hH.approxField_eq a ν hΨ hh (hH.inBox_succ x.2)

omit hC in
/-- The approximate field of corresponding data corresponds on the box of radius `ρ + 1`. -/
theorem approxField_corr (a : ℕ → ℝ) (ν : ℝ) {D : BgData H N} {D' : BgData H' N}
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h) :
    FieldCorr (ρ + 1) (approxField H a ν D.Ψ D.h) (approxField H' a ν D'.Ψ D'.h) :=
  fun _ hz => hH.approxField_eq a ν hΨ hh hz

/-- **The decoupled background system of Theorem I-4b at corresponding data.** -/
theorem isDecBg_iff (a : ℕ → ℝ) (ν ρb : ℝ) {s : Dec2.DecParams (coverOf Gc)}
    {s' : Dec2.DecParams (coverOf Hc)} (hs : ∀ q : cubeIdx Gc, s' (hC.cubeEquiv q) = s q)
    {D : BgData H N} {D' : BgData H' N}
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h)
    {φ : H.Ω 1 × Fin N → ℂ} {φ' : H'.Ω 1 × Fin N → ℂ} (hφ : ∀ x i, φ' (hH.e x, i) = φ (x, i))
    {α : H.Ω 1 → ℂ} {α' : H'.Ω 1 → ℂ} (hα : ∀ x, α' (hH.e x) = α x) :
    Dec2.IsDecBg (coverOf Hc) H' a ν ρb s' D' φ' α' ↔
      Dec2.IsDecBg (coverOf Gc) H a ν ρb s D φ α := by
  have hA := hH.approxField_site a ν hΨ hh
  have hR : ∀ x i, Background.residual H' a ν D' (approxField H' a ν D'.Ψ D'.h) (hH.e x, i) =
      Background.residual H a ν D (approxField H a ν D.Ψ D.h) (x, i) :=
    fun x i => hH.residual_eq a ν hΨ hh (hH.approxField_corr a ν hΨ hh) x i
  have h0 : ∀ x, (0 : H'.Ω 1 → ℂ) (hH.e x) = (0 : H.Ω 1 → ℂ) x := fun _ => rfl
  have hfix := hC.decFixed_iff hH a ν hs true h0 hA hR hα
  have hdphi : ∀ x i, dphi H' (Dec2.decG (coverOf Hc) H' a ν s') 0
      (approxField H' a ν D'.Ψ D'.h)
      (Background.residual H' a ν D' (approxField H' a ν D'.Ψ D'.h)) α' (hH.e x, i) =
      dphi H (Dec2.decG (coverOf Gc) H a ν s) 0 (approxField H a ν D.Ψ D.h)
        (Background.residual H a ν D (approxField H a ν D.Ψ D.h)) α (x, i) :=
    dphi_corr hH.e (fun α α' hα => hC.decG_entry hH a ν hs α α' hα) h0 hA hR hα
  have hsmall := small_corr_iff hH.e (fun x => hH.spacing_eq x.2) hα ρb
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hsmall.1 h1, hfix.1 h2, ?_⟩
    funext p
    obtain ⟨x, i⟩ := p
    have := congrFun h3 (hH.e x, i)
    simp only at this
    rwa [hφ, hA, hdphi] at this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hsmall.2 h1, hfix.2 h2, ?_⟩
    funext p
    obtain ⟨x', i⟩ := p
    obtain ⟨x, rfl⟩ := hH.e.surjective x'
    simp only
    rw [hφ, hA, hdphi, h3]

/-- The bijection of the candidate pairs `(φ, α)` of the two sets. -/
def pairEquiv : ((H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ)) ≃ ((H'.Ω 1 × Fin N → ℂ) × (H'.Ω 1 → ℂ)) :=
  Equiv.prodCongr (Equiv.arrowCongr (hH.e.prodCongr (Equiv.refl (Fin N))) (Equiv.refl ℂ))
    (Equiv.arrowCongr hH.e (Equiv.refl ℂ))

omit hC in
theorem pairEquiv_fst (p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ)) (x : H.Ω 1) (i : Fin N) :
    (hH.pairEquiv (N := N) p).1 (hH.e x, i) = p.1 (x, i) := by
  simp [pairEquiv]

omit hC in
theorem pairEquiv_snd (p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ)) (x : H.Ω 1) :
    (hH.pairEquiv (N := N) p).2 (hH.e x) = p.2 x := by
  simp [pairEquiv]

/-- **The decoupled background field and multiplier** of corresponding data, at corresponding
sites. -/
theorem decBgField_eq (a : ℕ → ℝ) (ν ρb : ℝ) {s : Dec2.DecParams (coverOf Gc)}
    {s' : Dec2.DecParams (coverOf Hc)} (hs : ∀ q : cubeIdx Gc, s' (hC.cubeEquiv q) = s q)
    {D : BgData H N} {D' : BgData H' N}
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h) :
    (∀ x i, Dec2.decBgField (coverOf Hc) H' a ν ρb s' D' (hH.e x, i) =
      Dec2.decBgField (coverOf Gc) H a ν ρb s D (x, i)) ∧
    (∀ x, Dec2.decBgMult (coverOf Hc) H' a ν ρb s' D' (hH.e x) =
      Dec2.decBgMult (coverOf Gc) H a ν ρb s D x) := by
  have hPQ : ∀ p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ),
      Dec2.IsDecBg (coverOf Gc) H a ν ρb s D p.1 p.2 ↔
        Dec2.IsDecBg (coverOf Hc) H' a ν ρb s' D' (hH.pairEquiv p).1 (hH.pairEquiv p).2 :=
    fun p => (hC.isDecBg_iff hH a ν ρb hs hΨ hh (hH.pairEquiv_fst p)
      (hH.pairEquiv_snd p)).symm
  refine ⟨fun x i => ?_, fun x => ?_⟩
  · have h := dite_existsUnique_equiv (P := fun p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ) =>
      Dec2.IsDecBg (coverOf Gc) H a ν ρb s D p.1 p.2)
      (Q := fun p : (H'.Ω 1 × Fin N → ℂ) × (H'.Ω 1 → ℂ) =>
      Dec2.IsDecBg (coverOf Hc) H' a ν ρb s' D' p.1 p.2) hH.pairEquiv hPQ (fun p => p.1 (x, i))
      (fun p => p.1 (hH.e x, i)) (fun p => (hH.pairEquiv_fst p x i).symm) 0
    unfold Dec2.decBgField
    have e1 : (if Hh : ∃! p : (H'.Ω 1 × Fin N → ℂ) × (H'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Hc) H' a ν ρb s' D' p.1 p.2 then Hh.exists.choose.1 else 0)
          (hH.e x, i) = if Hh : ∃! p : (H'.Ω 1 × Fin N → ℂ) × (H'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Hc) H' a ν ρb s' D' p.1 p.2 then
          Hh.exists.choose.1 (hH.e x, i) else 0 := by
      split_ifs <;> rfl
    have e2 : (if Hh : ∃! p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gc) H a ν ρb s D p.1 p.2 then Hh.exists.choose.1 else 0)
          (x, i) = if Hh : ∃! p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gc) H a ν ρb s D p.1 p.2 then
          Hh.exists.choose.1 (x, i) else 0 := by
      split_ifs <;> rfl
    rw [e1, e2, h]
  · have h := dite_existsUnique_equiv (P := fun p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ) =>
      Dec2.IsDecBg (coverOf Gc) H a ν ρb s D p.1 p.2)
      (Q := fun p : (H'.Ω 1 × Fin N → ℂ) × (H'.Ω 1 → ℂ) =>
      Dec2.IsDecBg (coverOf Hc) H' a ν ρb s' D' p.1 p.2) hH.pairEquiv hPQ (fun p => p.2 x)
      (fun p => p.2 (hH.e x)) (fun p => (hH.pairEquiv_snd p x).symm) 0
    unfold Dec2.decBgMult
    have e1 : (if Hh : ∃! p : (H'.Ω 1 × Fin N → ℂ) × (H'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Hc) H' a ν ρb s' D' p.1 p.2 then Hh.exists.choose.2 else 0)
          (hH.e x) = if Hh : ∃! p : (H'.Ω 1 × Fin N → ℂ) × (H'.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Hc) H' a ν ρb s' D' p.1 p.2 then
          Hh.exists.choose.2 (hH.e x) else 0 := by
      split_ifs <;> rfl
    have e2 : (if Hh : ∃! p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gc) H a ν ρb s D p.1 p.2 then Hh.exists.choose.2 else 0) x =
        if Hh : ∃! p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ),
          Dec2.IsDecBg (coverOf Gc) H a ν ρb s D p.1 p.2 then Hh.exists.choose.2 x else 0 := by
      split_ifs <;> rfl
    rw [e1, e2, h]

/-- **The values of maps with the defining property of the pair of Theorem I-4b correspond.**
`F` and `F'` are maps on the two tori with the uniqueness property of the decoupled background
system at the parameters `s`, `s'` and the data `D`, `D'` (`hF`, `hF'`: the defining property of
`Dec2.i4b_analytic` at these points); if the system has a solution on the first torus, the values
of the two maps correspond. -/
theorem decBg_value_eq (a : ℕ → ℝ) (ν ρb : ℝ) {s : Dec2.DecParams (coverOf Gc)}
    {s' : Dec2.DecParams (coverOf Hc)} (hs : ∀ q : cubeIdx Gc, s' (hC.cubeEquiv q) = s q)
    {D : BgData H N} {D' : BgData H' N}
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h)
    {Fv : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ)} {Fv' : (H'.Ω 1 × Fin N → ℂ) × (H'.Ω 1 → ℂ)}
    (hF : ∀ φ α, Dec2.IsDecBg (coverOf Gc) H a ν ρb s D φ α → Fv = (φ, α))
    (hF' : ∀ φ α, Dec2.IsDecBg (coverOf Hc) H' a ν ρb s' D' φ α → Fv' = (φ, α))
    (hex : ∃ φ α, Dec2.IsDecBg (coverOf Gc) H a ν ρb s D φ α) :
    (∀ x i, Fv'.1 (hH.e x, i) = Fv.1 (x, i)) ∧ ∀ x, Fv'.2 (hH.e x) = Fv.2 x := by
  obtain ⟨φ, α, hsol⟩ := hex
  have h1 := hF φ α hsol
  have hsol' : Dec2.IsDecBg (coverOf Hc) H' a ν ρb s' D' (hH.pairEquiv (φ, α)).1
      (hH.pairEquiv (φ, α)).2 :=
    (hC.isDecBg_iff hH a ν ρb hs hΨ hh (hH.pairEquiv_fst (φ, α))
      (hH.pairEquiv_snd (φ, α))).2 hsol
  have h2 := hF' _ _ hsol'
  rw [h1, h2]
  exact ⟨fun x i => hH.pairEquiv_fst (φ, α) x i, fun x => hH.pairEquiv_snd (φ, α) x⟩

/-- **The values of maps with the defining property of the analytic solution of Theorem I-4a
correspond.**  `δα = (Sol p).2` solves the fixed-point equation with the field `(Sol p).1` and lies
in the ball of radius `r`; `(Sol' p').2` is the unique solution in the ball on the second torus
(`hU'`) with the field `(Sol' p').1`; the data of the two problems correspond. -/
theorem decSol_value_eq (a : ℕ → ℝ) (ν : ℝ) {s : Dec2.DecParams (coverOf Gc)}
    {s' : Dec2.DecParams (coverOf Hc)} (hs : ∀ q : cubeIdx Gc, s' (hC.cubeEquiv q) = s q)
    (ιU : Bool) {α₀ : H.Ω 1 → ℂ} {α₀' : H'.Ω 1 → ℂ} (hα₀ : ∀ x, α₀' (hH.e x) = α₀ x)
    {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} {φ₀' : CTorus d L N₁' m₁ K → Fin N → ℂ}
    (hφ : ∀ x : H.Ω 1, φ₀' (hH.e x) = φ₀ x)
    {Fs : H.Ω 1 × Fin N → ℂ} {Fs' : H'.Ω 1 × Fin N → ℂ} (hF : ∀ x i, Fs' (hH.e x, i) = Fs (x, i))
    {r : ℝ} {v : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ)} {v' : (H'.Ω 1 × Fin N → ℂ) × (H'.Ω 1 → ℂ)}
    (hv1 : v.1 = dphi H (Dec2.decG (coverOf Gc) H a ν s) α₀ φ₀ Fs v.2)
    (hv2 : Dec2.DecFixed (coverOf Gc) H a ν s ιU α₀ φ₀ Fs v.2) (hv3 : Small H v.2 r)
    (hv1' : v'.1 = dphi H' (Dec2.decG (coverOf Hc) H' a ν s') α₀' φ₀' Fs' v'.2)
    (hU' : ∀ δα', Small H' δα' r → Dec2.DecFixed (coverOf Hc) H' a ν s' ιU α₀' φ₀' Fs' δα' →
      δα' = v'.2) :
    (∀ x i, v'.1 (hH.e x, i) = v.1 (x, i)) ∧ ∀ x, v'.2 (hH.e x) = v.2 x := by
  set δα' : H'.Ω 1 → ℂ := fun x' => v.2 (hH.e.symm x') with hδdef
  have hδ : ∀ x, δα' (hH.e x) = v.2 x := fun x => by simp [hδdef]
  have hsm : Small H' δα' r :=
    (small_corr_iff hH.e (fun x => hH.spacing_eq x.2) hδ r).2 hv3
  have hfix : Dec2.DecFixed (coverOf Hc) H' a ν s' ιU α₀' φ₀' Fs' δα' :=
    (hC.decFixed_iff hH a ν hs ιU hα₀ hφ hF hδ).2 hv2
  have he : δα' = v'.2 := hU' δα' hsm hfix
  have h2 : ∀ x, v'.2 (hH.e x) = v.2 x := fun x => by rw [← he, hδ]
  refine ⟨fun x i => ?_, h2⟩
  rw [hv1, hv1']
  exact dphi_corr hH.e (fun α α' hα => hC.decG_entry hH a ν hs α α' hα) hα₀ hφ hF h2 x i

end OmegaIso

end Balaban.Polymer.LocalIso
