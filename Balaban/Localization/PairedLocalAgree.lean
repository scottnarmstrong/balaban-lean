/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.PairedLocalGraph
public import Balaban.Localization.I5FluctLocal
public import Balaban.Localization.I5FluctData
public import Balaban.Localization.Decoupled2FpBackground

/-!
# Exact agreement and the two-field locality implication (VMOD-12 §2)

* `relParams`: the extension of a family `s` indexed by `J` to the cover-cube parameters relative to
  `X₁` (VMOD-12 §2: `1` off the parameter cubes, `s_i` at `c i`, `0` on the remaining parameter
  cubes), with its three properties.
* `PairedAg` (2.1): the cube-indexed agreement relation.
* `paired_fields_agree`: the paired incidence unions of the background operator `H_∂` and the old
  fluctuation operator `H_-` give the agreement of the decoupled background fields on `Y ∩ Ω₁(H_∂)`,
  of the multipliers on `SYF_{H_∂}(Y)`, and of the decoupled fluctuation fields on `Y ∩ Ω₁(H_-)`,
  by `Dec2.i4b_local_fp` and `Dec2.i4a_local_fpS`; no `Precedes H_- H_∂` is used.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}

section Params

variable (C : DecCover d L N₁ m₁ K) (X₁ : Finset (CTorus d L N₁ m₁ K)) {ι : Type*}
  (c : ι → ℕ × CTorus d L N₁ m₁ K) (J : Finset ι) (s : ι → ℂ)

open Classical in
/-- **The extension of `s` to the cover-cube parameters relative to `X₁`** (VMOD-12 §2): `1` off
`C.parCubes X₁`, `s_i` at a parameter cube `c i`, `i ∈ J`, and `0` on the remaining parameter
cubes. -/
noncomputable def relParams : Dec2.DecParams C := fun P =>
  if P.1 ∈ C.parCubes X₁ then (if h : ∃ i ∈ J, c i = P.1 then s h.choose else 0) else 1

variable {C X₁ c J s}

theorem extS_relParams_nonpar {P : ℕ × CTorus d L N₁ m₁ K} (hP : P ∉ C.parCubes X₁) :
    Dec2.extS C (relParams C X₁ c J s) P = 1 := by
  unfold Dec2.extS relParams
  split_ifs with h1 <;> simp_all

theorem extS_relParams_zero {P : ℕ × CTorus d L N₁ m₁ K} (hP : P ∈ C.parCubes X₁)
    (hJ : P ∉ J.image c) : Dec2.extS C (relParams C X₁ c J s) P = 0 := by
  classical
  have hc : P ∈ C.cubeIdx := (Finset.mem_filter.1 hP).1
  unfold Dec2.extS relParams
  have : ¬ ∃ i ∈ J, c i = P := fun ⟨i, hi, e⟩ => hJ (Finset.mem_image.2 ⟨i, hi, e⟩)
  simp [hc, hP, this]

theorem extS_relParams_param (hinj : Set.InjOn c J) {i : ι} (hi : i ∈ J)
    (hP : c i ∈ C.parCubes X₁) : Dec2.extS C (relParams C X₁ c J s) (c i) = s i := by
  classical
  have hc : c i ∈ C.cubeIdx := (Finset.mem_filter.1 hP).1
  unfold Dec2.extS relParams
  have hex : ∃ j ∈ J, c j = c i := ⟨i, hi, rfl⟩
  simp only [hc, hP, hex, dite_true, ite_true]
  rw [show hex.choose = i from hinj hex.choose_spec.1 hi hex.choose_spec.2]

theorem norm_extS_relParams_le {R : ℝ} (hR : 1 ≤ R) (hs : ∀ i, ‖s i‖ ≤ R) (P : C.cubeIdx) :
    ‖relParams C X₁ c J s P‖ ≤ R := by
  unfold relParams
  split_ifs with h1 h2
  · exact hs _
  · exact (norm_zero (E := ℂ)).trans_le (by linarith)
  · simpa using hR

/-- The `hag` binder of `Dec2.i4b_local_fp`/`i4a_local_fpS` from the parameter hypothesis of
`LocalityAEOn`: the cells of `A` inside `Y` carry equal parameters. -/
theorem extS_relParams_agree {s' : ι → ℂ} (hinj : Set.InjOn c J) {Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} (hA : ∀ P ∈ A, ∀ x ∈ cubeP P, x ∈ Y)
    (hs : ∀ i ∈ J, (∀ x ∈ cubeP (c i), x ∈ Y) → s i = s' i) :
    ∀ P ∈ J.image c, P ∈ A →
      Dec2.extS C (relParams C X₁ c J s) P = Dec2.extS C (relParams C X₁ c J s') P := by
  intro P hP hPA
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP
  by_cases hpc : c i ∈ C.parCubes X₁
  · rw [extS_relParams_param hinj hi hpc, extS_relParams_param hinj hi hpc]
    exact hs i hi (hA _ hPA)
  · rw [extS_relParams_nonpar hpc, extS_relParams_nonpar hpc]

end Params

variable (Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ') in
/-- **(2.1) The cube-indexed agreement relation**: agreement of the raw background data on the
`resDep`-thickening of `Y` at the sites of `Ω₁(H_∂)`, and of the old fluctuation datum on `Y` and
its nearest neighbours. -/
def PairedAg (Y : Finset (CTorus d L N₁ m₁ K)) (u u' : RawData d L (N₁ * L ^ m₁) K N)
    (ψ ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ) : Prop :=
  agreeOn (thickSet Hb (↑Y : Set (CTorus d L N₁ m₁ K))) u u' ∧
    ∀ y ∈ psiThick (↑Y : Set (CTorus d L N₁ m₁ K)), ψ y = ψ' y

theorem PairedAg.refl (Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ') (Y : Finset (CTorus d L N₁ m₁ K))
    (u : RawData d L (N₁ * L ^ m₁) K N) (ψ : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    PairedAg Hb Y u u ψ ψ := ⟨agreeOn_refl _ u, fun _ _ => rfl⟩

theorem PairedAg.mono (Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ') {Y Y' : Finset (CTorus d L N₁ m₁ K)}
    (h : Y ⊆ Y') {u u' : RawData d L (N₁ * L ^ m₁) K N} {ψ ψ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hA : PairedAg Hb Y' u u' ψ ψ') : PairedAg Hb Y u u' ψ ψ' :=
  ⟨agreeOn_mono (thickSet_mono (Finset.coe_subset.2 h)) hA.1,
    fun y hy => hA.2 y (psiThick_mono (Finset.coe_subset.2 h) hy)⟩

section Fields

variable {C : DecCover d L N₁ m₁ K} {Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {Kc Cx : ℝ}

/-- **Paired field locality (VMOD-12 §2)**: the agreement of the decoupled background fields of
`H_∂`, of the multipliers on `SYF_{H_∂}(Y)`, and of the decoupled old fluctuation fields on
`Y ∩ Ω₁(H_-)` from the paired incidence unions `(Y, A_∂)`, `(Y, A_-)` of the two operators and the
relation `PairedAg` (2.1).  The hypotheses are those of `Dec2.i4b_local_fp` for `H_∂` and
`Dec2.i4a_local_fpS` for `H_-` on the data `flEdat` (no `Precedes H_- H_∂`), the parameter
extension rule of `relParams`, and the unions with their cell conclusions. -/
theorem paired_fields_agree
    {c₁ BG cstar BG₂ κ δ ε δ₀ δ₁ : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c₁ BG)
    (Sb : Dec2.FootLocal C Hb a ν Kc Cx) (HB : BgHyp d L K ϱ' a ν) (hκ : 0 ≤ κ)
    (hM : c₁ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D D₂ : BgData Hb N}
    (hD : InDomainC Hb ν δ ε D) (hD₂ : InDomainC Hb ν δ ε D₂)
    (hF : Dec2.FamSpec d L Kc Cx cstar BG₂) (Sm : Dec2.FootLocal C Hm a ν Kc Cx)
    (hM₂ : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (cc : ι → ℕ × CTorus d L N₁ m₁ K) {J : Finset ι}
    (hinj : Set.InjOn cc J) {s s' : ι → ℂ} (hs : s ∈ supN J (Real.exp κ))
    (hs' : s' ∈ supN J (Real.exp κ))
    {X₁ Y : Finset (CTorus d L N₁ m₁ K)} {Ab Am : Finset (ℕ × CTorus d L N₁ m₁ K)}
    (hIb : Dec2.IsIncUnion C Hb a ν X₁ (J.image cc) Y Ab)
    (hIm : Dec2.IsIncUnion C Hm a ν X₁ (J.image cc) Y Am)
    (hAb : ∀ P ∈ Ab, ∀ x ∈ cubeP P, x ∈ Y) (hAm : ∀ P ∈ Am, ∀ x ∈ cubeP P, x ∈ Y)
    (hpar : ∀ i ∈ J, (∀ x ∈ cubeP (cc i), x ∈ Y) → s i = s' i)
    {ψ ψ₂ : CTorus d L N₁ m₁ K → Fin N → ℂ} (hAg : PairedAg Hb Y (rawOf D) (rawOf D₂) ψ ψ₂)
    {φ φ₂ : Hb.Ω 1 × Fin N → ℂ} {α α₂ : Hb.Ω 1 → ℂ}
    (h : Dec2.IsDecBg C Hb a ν (rho4 d L N BG κ) (relParams C X₁ cc J s) D φ α)
    (h₂ : Dec2.IsDecBg C Hb a ν (rho4 d L N BG κ) (relParams C X₁ cc J s') D₂ φ₂ α₂)
    (Hh : DecHyp Hm a ν false (flEdat Hb Hm (φ, α) D.Ψ ψ).2.1 (flEdat Hb Hm (φ, α) D.Ψ ψ).1
      (flEdat Hb Hm (φ, α) D.Ψ ψ).2.2.1 (flEdat Hb Hm (φ, α) D.Ψ ψ).2.2.2 δ₀ δ₁)
    (Hh' : DecHyp Hm a ν false (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).2.1
      (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).1 (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).2.2.1
      (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).2.2.2 δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {δα δα' : Hm.Ω 1 → ℂ}
    (hfix : Dec2.DecFixed C Hm a ν (relParams C X₁ cc J s) false (flEdat Hb Hm (φ, α) D.Ψ ψ).2.1
      (flEdat Hb Hm (φ, α) D.Ψ ψ).1
      (pertSource Hm a (flEdat Hb Hm (φ, α) D.Ψ ψ).2.2.1 (flEdat Hb Hm (φ, α) D.Ψ ψ).2.2.2) δα)
    (hsm : Small Hm δα (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)))
    (hfix' : Dec2.DecFixed C Hm a ν (relParams C X₁ cc J s') false
      (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).2.1 (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).1
      (pertSource Hm a (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).2.2.1
        (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).2.2.2) δα')
    (hsm' : Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))) :
    (∀ x : Hb.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF C Hb a ν X₁ (J.image cc) Y → α x = α₂ x) ∧
    (∀ y : Hb.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N, φ (y, i) = φ₂ (y, i)) ∧
    (∀ x : Hm.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Dec2.SYF C Hm a ν X₁ (J.image cc) Y → δα x = δα' x) ∧
    (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi Hm (Dec2.decG C Hm a ν (relParams C X₁ cc J s)) (flEdat Hb Hm (φ, α) D.Ψ ψ).2.1
        (flEdat Hb Hm (φ, α) D.Ψ ψ).1
        (pertSource Hm a (flEdat Hb Hm (φ, α) D.Ψ ψ).2.2.1 (flEdat Hb Hm (φ, α) D.Ψ ψ).2.2.2)
        δα (y, i) =
      dphi Hm (Dec2.decG C Hm a ν (relParams C X₁ cc J s')) (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).2.1
        (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).1
        (pertSource Hm a (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).2.2.1
          (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).2.2.2) δα' (y, i)) := by
  classical
  have hR : (1 : ℝ) ≤ Real.exp κ := Real.one_le_exp hκ
  have hn1 : ∀ P, ‖relParams C X₁ cc J s P‖ ≤ Real.exp κ := fun P =>
    norm_extS_relParams_le hR (fun i => (hs.2 i).le) P
  have hn2 : ∀ P, ‖relParams C X₁ cc J s' P‖ ≤ Real.exp κ := fun P =>
    norm_extS_relParams_le hR (fun i => (hs'.2 i).le) P
  have hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ →
      Dec2.extS C (relParams C X₁ cc J s) P = 1 ∧ Dec2.extS C (relParams C X₁ cc J s') P = 1 :=
    fun P _ hP => ⟨extS_relParams_nonpar hP, extS_relParams_nonpar hP⟩
  have hs0 : ∀ P ∈ C.parCubes X₁, P ∉ J.image cc →
      Dec2.extS C (relParams C X₁ cc J s) P = 0 ∧ Dec2.extS C (relParams C X₁ cc J s') P = 0 :=
    fun P hP hJ => ⟨extS_relParams_zero hP hJ, extS_relParams_zero hP hJ⟩
  have hagb := extS_relParams_agree (C := C) (X₁ := X₁) hinj hAb hpar
  have hagm := extS_relParams_agree (C := C) (X₁ := X₁) hinj hAm hpar
  have hdata : ∀ x : Hb.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y →
      ∀ y ∈ resDep Hb (x : CTorus d L N₁ m₁ K), D.Ψ y = D₂.Ψ y ∧ (y ∈ Hb.Ω 1 → D.h y = D₂.h y) := by
    intro x hx y hy
    have := hAg.1 y (Or.inr ⟨x, Finset.mem_coe.2 hx, x.2, hy⟩)
    exact ⟨this.1, fun _ => this.2⟩
  obtain ⟨hαSY, hφY⟩ := Dec2.i4b_local_fp hS Sb HB hκ hM hn1 hn2 hδ0 hδε hε hδ hνε hD hD₂ hIb hs1
    hs0 hagb hdata h h₂
  have hDA : Dec2.DataAgreeS Hm N Y (Dec2.SYF C Hm a ν X₁ (J.image cc) Y)
      (flEdat Hb Hm (φ, α) D.Ψ ψ).2.1 (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).2.1
      (flEdat Hb Hm (φ, α) D.Ψ ψ).1 (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).1
      (flEdat Hb Hm (φ, α) D.Ψ ψ).2.2.1 (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).2.2.1
      (flEdat Hb Hm (φ, α) D.Ψ ψ).2.2.2 (flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂).2.2.2 := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun y hy hxy => ?_,
      fun x hx i => rfl⟩
    · show flAlpha Hb Hm α x = flAlpha Hb Hm α₂ x
      by_cases hxb : (x : CTorus d L N₁ m₁ K) ∈ Hb.Ω 1
      · simp only [flAlpha, hxb, ↓reduceDIte]
        exact hαSY ⟨x, hxb⟩ (Dec2.SYF_cross hIb x.2 hxb hx)
      · simp [flAlpha, hxb]
    · have hxY : (x : CTorus d L N₁ m₁ K) ∈ Y := hx
      funext i
      show barField Hb D.Ψ φ x i = barField Hb D₂.Ψ φ₂ x i
      by_cases hxb : (x : CTorus d L N₁ m₁ K) ∈ Hb.Ω 1
      · simp only [barField, hxb, ↓reduceDIte]
        exact hφY ⟨x, hxb⟩ hxY i
      · simp only [barField, hxb, ↓reduceDIte]
        exact congrFun (hAg.1 x (Or.inl (Finset.mem_coe.2 hxY))).1 i
    · exact hAg.2 x (Or.inl (Finset.mem_coe.2 hx))
    · obtain ⟨x, hx, hadj⟩ := hxy
      exact hAg.2 y (Or.inr ⟨x, Finset.mem_coe.2 hx, hadj⟩)
  have hfl := Dec2.i4a_local_fpS hF Sm hκ hM₂ hn1 hn2 Hh Hh' hδ₀ hδ₁ hIm hs1 hs0 hagm hDA hfix hsm
    hfix' hsm'
  exact ⟨hαSY, hφY, hfl.1, hfl.2⟩

end Fields

end Balaban.Localization
