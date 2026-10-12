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

theorem relParams_univ_eq [Fintype ι] (hinj : Function.Injective c) (hs : s ∈ supportedOn J) :
    relParams C X₁ c Finset.univ s = relParams C X₁ c J s := by
  classical
  funext P
  unfold relParams
  by_cases h1 : P.1 ∈ C.parCubes X₁
  · simp only [h1, ite_true]
    by_cases hu : ∃ i, c i = P.1
    · obtain ⟨i, hi⟩ := hu
      have hu' : ∃ i ∈ (Finset.univ : Finset ι), c i = P.1 := ⟨i, Finset.mem_univ _, hi⟩
      have e1 : hu'.choose = i := hinj (hu'.choose_spec.2.trans hi.symm)
      simp only [hu', ↓reduceDIte]
      rw [e1]
      by_cases hJ : i ∈ J
      · have hJ' : ∃ j ∈ J, c j = P.1 := ⟨i, hJ, hi⟩
        have e2 : hJ'.choose = i := hinj (hJ'.choose_spec.2.trans hi.symm)
        simp only [hJ', ↓reduceDIte]
        rw [e2]
      · have hJ' : ¬ ∃ j ∈ J, c j = P.1 := fun ⟨j, hj, hjP⟩ => hJ (by
          have : j = i := hinj (hjP.trans hi.symm)
          exact this ▸ hj)
        simp only [hJ', ↓reduceDIte]
        exact hs i hJ
    · have hu' : ¬ ∃ i ∈ (Finset.univ : Finset ι), c i = P.1 := fun ⟨i, _, hi⟩ => hu ⟨i, hi⟩
      have hJ' : ¬ ∃ j ∈ J, c j = P.1 := fun ⟨i, _, hi⟩ => hu ⟨i, hi⟩
      simp only [hu', hJ', ↓reduceDIte]
  · simp [h1]

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

section Composite

variable {ϱx : ℝ} {C : DecCover d L N₁ m₁ K} {Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {Kc Cx : ℝ}

variable (C Hb Hm) in
/-- The raw datum of `𝔹_k(X)` from the background field of `H_∂` and the fluctuation field of
`H_-` (`D1rawFl` for an arbitrary cover `C`; P3 (4.17), (4.21)). -/
noncomputable def pairedRaw (Gx : GeneratingSet d L (N₁ * L ^ m₁) K ϱx) (a : ℕ → ℝ)
    (Fb : Dec2.DecParams C × RawData d L (N₁ * L ^ m₁) K N →
      (Hb.Ω 1 × Fin N → ℂ) × (Hb.Ω 1 → ℂ))
    (Sol : Dec2.DecParams C × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (s : Dec2.DecParams C)
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) :
    RawData d L (N₁ * L ^ m₁) K N :=
  (fun x i => composeField Gx Hb a (Fb (s, u.1)).1 u.1.1 x i +
      composeField Gx Hm a (Sol (s, flEdat Hb Hm (Fb (s, u.1)) u.1.1 u.2)).1 u.2 x i,
    fun x i => by classical exact if x ∈ Gx.Ω 1 then u.1.2 x i else 0)

variable (C Hb Hm ν) in
/-- **The admissible data** of the paired composite: the raw background data of the domain
`Ψ̃^c(δ, ε)` of `H_∂`, with a layer datum `ψ`, such that for every parameter vector of modulus at
most `e^κ` the decoupled background problem of `H_∂` has a solution `(φ, α)` whose extension
`flEdat` satisfies the hypotheses of `Dec2.i4a_local_fpS` on `H_-` (the strict mixed domain). -/
def PairedDomain (a : ℕ → ℝ) (BG κ δ ε δ₀ δ₁ : ℝ) :
    Set (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) :=
  {p | ∃ D : BgData Hb N, rawOf D = p.1 ∧ InDomainC Hb ν δ ε D ∧
    ∀ s : Dec2.DecParams C, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∃ (φ : Hb.Ω 1 × Fin N → ℂ) (α : Hb.Ω 1 → ℂ),
        Dec2.IsDecBg C Hb a ν (rho4 d L N BG κ) s D φ α ∧
        DecHyp Hm a ν false (flEdat Hb Hm (φ, α) D.Ψ p.2).2.1 (flEdat Hb Hm (φ, α) D.Ψ p.2).1
          (flEdat Hb Hm (φ, α) D.Ψ p.2).2.2.1 (flEdat Hb Hm (φ, α) D.Ψ p.2).2.2.2 δ₀ δ₁}

end Composite

section Locality

variable {ϱx : ℝ} {C : DecCover d L N₁ m₁ K} {Hb : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {Kc Cx : ℝ}

/-- **The two-field locality implication (VMOD-12 §2), in the `LocalityAEOn` form.**  For the
composite `E ∘ pairedRaw` of the background field of `H_∂` and the fluctuation field of `H_-`:
given, for every family `J`, the paired incidence unions `(Y_J, A_∂)`, `(Y_J, A_-)` with cells in
`Y_J` (VMOD-12 (1.3), the P6 instances being OPEN-P6-GRAPH-BRIDGE), the dependency sites of the
compositions with both operators in `X₁ ⊆ Y_J` (OPEN-P6-AFFINE-DOMAIN), and the solution selectors
`Fb`, `Sol` characterised on admissible data, `E ∘ pairedRaw` is local for the agreement relation
`PairedAg`.  No `Precedes H_- H_∂` appears. -/
theorem paired_locality
    {c₁ BG cstar BG₂ κ δ ε δ₀ δ₁ : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c₁ BG)
    (Sb : Dec2.FootLocal C Hb a ν Kc Cx) (HB : BgHyp d L K ϱ' a ν) (hκ : 0 ≤ κ)
    (hM : c₁ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (hF : Dec2.FamSpec d L Kc Cx cstar BG₂) (Sm : Dec2.FootLocal C Hm a ν Kc Cx)
    (hM₂ : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {ι : Type*} [DecidableEq ι] [Fintype ι] (cc : ι → ℕ × CTorus d L N₁ m₁ K)
    (hinj : Function.Injective cc) (X₁ : Finset (CTorus d L N₁ m₁ K))
    (Yf : Finset ι → Finset (CTorus d L N₁ m₁ K))
    (hXY : ∀ J, ∀ y ∈ X₁, y ∈ Yf J)
    (hG : ∀ J : Finset ι, ∃ Ab Am : Finset (ℕ × CTorus d L N₁ m₁ K),
      Dec2.IsIncUnion C Hb a ν X₁ (J.image cc) (Yf J) Ab ∧
      Dec2.IsIncUnion C Hm a ν X₁ (J.image cc) (Yf J) Am ∧
      (∀ P ∈ Ab, ∀ x ∈ cubeP P, x ∈ Yf J) ∧ (∀ P ∈ Am, ∀ x ∈ cubeP P, x ∈ Yf J))
    (Gx : GeneratingSet d L (N₁ * L ^ m₁) K ϱx)
    (hdepb : ∀ x ∈ dataSites Gx, ∀ y ∈ composeDep Gx Hb x, y ∈ X₁)
    (hdepm : ∀ x ∈ dataSites Gx, ∀ y ∈ composeDep Gx Hm x, y ∈ X₁)
    {Fb : Dec2.DecParams C × RawData d L (N₁ * L ^ m₁) K N →
      (Hb.Ω 1 × Fin N → ℂ) × (Hb.Ω 1 → ℂ)}
    (hFb : ∀ (s : Dec2.DecParams C) (D : BgData Hb N), (∀ P, ‖s P‖ ≤ Real.exp κ) →
      InDomainC Hb ν δ ε D → ∀ (φ : Hb.Ω 1 × Fin N → ℂ) (α : Hb.Ω 1 → ℂ),
        Dec2.IsDecBg C Hb a ν (rho4 d L N BG κ) s D φ α → Fb (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams C × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams C × Edat Hm N, (∀ P, ‖p.1 P‖ ≤ Real.exp κ) →
      DecHyp Hm a ν false p.2.2.1 p.2.1 p.2.2.2.1 p.2.2.2.2 δ₀ δ₁ →
        (Sol p).1 = dphi Hm (Dec2.decG C Hm a ν p.1) p.2.2.1 p.2.1
          (pertSource Hm a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed C Hm a ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm a p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)))
    (E : RawData d L (N₁ * L ^ m₁) K N → ℂ) :
    LocalityAEOn (Real.exp κ) (PairedDomain C Hb Hm ν a BG κ δ ε δ₀ δ₁)
      (fun i : ι => Pset m₁ (cc i)) (fun J => (↑(Yf J) : Set (CTorus d L N₁ m₁ K)))
      (fun J u u' => PairedAg Hb (Yf J) u.1 u'.1 u.2 u'.2)
      (fun u s => E (pairedRaw C Hb Hm Gx a Fb Sol (relParams C X₁ cc Finset.univ s) u)) := by
  classical
  rintro J ⟨u, ψ⟩ ⟨u', ψ₂⟩ ⟨D, hDu, hD, hex⟩ ⟨D₂, hDu₂, hD₂, hex₂⟩ s s' hs hs' hpar hAg
  simp only at hDu hDu₂
  subst hDu hDu₂
  obtain ⟨Ab, Am, hIb, hIm, hAb, hAm⟩ := hG J
  show E (pairedRaw C Hb Hm Gx a Fb Sol (relParams C X₁ cc Finset.univ s) (rawOf D, ψ)) =
    E (pairedRaw C Hb Hm Gx a Fb Sol (relParams C X₁ cc Finset.univ s') (rawOf D₂, ψ₂))
  rw [relParams_univ_eq hinj hs.1, relParams_univ_eq hinj hs'.1]
  have hR : (1 : ℝ) ≤ Real.exp κ := Real.one_le_exp hκ
  have hn1 : ∀ P, ‖relParams C X₁ cc J s P‖ ≤ Real.exp κ := fun P =>
    norm_extS_relParams_le hR (fun i => (hs.2 i).le) P
  have hn2 : ∀ P, ‖relParams C X₁ cc J s' P‖ ≤ Real.exp κ := fun P =>
    norm_extS_relParams_le hR (fun i => (hs'.2 i).le) P
  obtain ⟨φ, α, hI, Hh⟩ := hex _ hn1
  obtain ⟨φ₂, α₂, hI₂, Hh₂⟩ := hex₂ _ hn2
  have hF1 := hFb _ D hn1 hD φ α hI
  have hF2 := hFb _ D₂ hn2 hD₂ φ₂ α₂ hI₂
  obtain ⟨hfld, hfix, hsm⟩ := hSol (relParams C X₁ cc J s, flEdat Hb Hm (φ, α) D.Ψ ψ) hn1 Hh
  obtain ⟨hfld₂, hfix₂, hsm₂⟩ := hSol (relParams C X₁ cc J s', flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂) hn2 Hh₂
  have hparJ : ∀ i ∈ J, (∀ x ∈ cubeP (cc i), x ∈ Yf J) → s i = s' i := by
    intro i hi hsub
    refine hpar i hi (fun x hx => ?_)
    exact Finset.mem_coe.2 (hsub x (mem_cubeP.2 hx))
  obtain ⟨hα, hφ, hδα, hdphi⟩ := paired_fields_agree hS Sb HB hκ hM hδ0 hδε hε hδ hνε hD hD₂ hF Sm
    hM₂ (cc := cc) (hinj.injOn) hs hs' hIb hIm hAb hAm hparJ hAg hI hI₂ Hh Hh₂ hδ₀ hδ₁ hfix hsm
    hfix₂ hsm₂
  have hXs : ∀ x ∈ dataSites Gx, ∀ y ∈ composeDep Gx Hb x, y ∈ Yf J := fun x hx y hy =>
    hXY J y (hdepb x hx y hy)
  have hXm : ∀ x ∈ dataSites Gx, ∀ y ∈ composeDep Gx Hm x, y ∈ Yf J := fun x hx y hy =>
    hXY J y (hdepm x hx y hy)
  have hself : ∀ x ∈ dataSites Gx, x ∈ Yf J := fun x hx =>
    hXs x hx x (self_mem_composeDep x)
  dsimp only [pairedRaw]
  rw [hF1, hF2]
  refine congrArg E (Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_))
  · by_cases hx : x ∈ dataSites Gx
    · dsimp only
      congr 1
      · refine composeField_congr (G := Gx) (G' := Hb) a (fun y hy jj => ?_)
          (fun jj => congrFun (hAg.1 x (Or.inl (Finset.mem_coe.2 (hself x hx)))).1 jj) i
        have hyY := hXs x hx y hy
        by_cases hyΩ : y ∈ Hb.Ω 1
        · rw [svec_of_mem' _ hyΩ jj, svec_of_mem' _ hyΩ jj]
          exact hφ ⟨y, hyΩ⟩ hyY jj
        · rw [svec_of_not_mem Hb _ hyΩ jj, svec_of_not_mem Hb _ hyΩ jj]
      · refine composeField_congr (G := Gx) (G' := Hm) a (fun y hy jj => ?_)
          (fun jj => congrFun (hAg.2 x (Or.inl (Finset.mem_coe.2 (hself x hx)))) jj) i
        have hyY := hXm x hx y hy
        by_cases hyΩ : y ∈ Hm.Ω 1
        · rw [svec_of_mem' _ hyΩ jj, svec_of_mem' _ hyΩ jj]
          change (Sol (relParams C X₁ cc J s, flEdat Hb Hm (φ, α) D.Ψ ψ)).1 (⟨y, hyΩ⟩, jj) =
            (Sol (relParams C X₁ cc J s', flEdat Hb Hm (φ₂, α₂) D₂.Ψ ψ₂)).1 (⟨y, hyΩ⟩, jj)
          rw [hfld, hfld₂]
          exact hdphi ⟨y, hyΩ⟩ hyY jj
        · rw [svec_of_not_mem Hm _ hyΩ jj, svec_of_not_mem Hm _ hyΩ jj]
    · dsimp only
      rw [composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx,
        composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx]
  · dsimp only
    by_cases hx : x ∈ Gx.Ω 1
    · simp only [hx, ↓reduceIte]
      have hxd : x ∈ dataSites Gx := (mem_dataSites Gx).2 (Or.inl hx)
      exact congrFun (hAg.1 x (Or.inl (Finset.mem_coe.2 (hself x hxd)))).2 i
    · simp [hx]

end Locality

end Balaban.Localization
