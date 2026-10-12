/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DomainLemma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# (AE2): locality of the composite function (LOCALIZATION.md §4.4)

If the decoupling vectors `s, s'` vanish outside a family `𝒞`, agree on the cubes of `𝒞` inside
`Y(𝒞)`, and the data `Θ, Θ'` agree on the thickening of `Y(𝒞)` by the dependency sets `resDep`
of Theorem I-4b, then `𝒯(s; Θ) = 𝒯(s'; Θ')` (`fan_local`), because the first-stage composed data
`D1raw` coincide: the decoupled background fields agree on `Y(𝒞)` (`i4b_local`) and the sites read
by `ψ(𝔹_k(X), 𝔹_{k+1})` lie in `X₁ ⊆ Y(𝒞)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix

section Geometry

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {m₀ : ℕ} {j : ℕ}
variable {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

theorem X1_subset_Omega1 (hS : CovSetup G m₀ j X 𝒦X) :
    X1 G m₀ j 𝒦X ⊆ ↑(G.Ω 1) := by
  intro x hx
  have hK : 1 ≤ K := by have := hS.hjK; omega
  exact G.layer_subset hK le_rfl (X1_layer hx)

theorem Pset_subset_Omega1 (hS : CovSetup G m₀ j X 𝒦X) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) : Pset m₁ q ⊆ ↑(G.Ω 1) := by
  obtain ⟨⟨hq1, hqK⟩, -, -⟩ := (mem_cubeIdx G).1 hq
  intro x hx
  have h1 := Dsites_subset_layer (G := G) (m₀ := m₀) q (Pset_subset_Dsites hS.hU hS.hN hq hx)
  exact G.layer_subset hq1 hqK h1

variable {ι : Type*} {c : ι → ℕ × CTorus d L N₁ m₁ K}

theorem patchUnion_subset_Omega1 (hS : CovSetup G m₀ j X 𝒦X) (hc : ∀ i, c i ∈ cubeIdx G)
    (C : Finset ι) :
    patchUnion (X1 G m₀ j 𝒦X) (fun i => Pset m₁ (c i)) C ⊆ ↑(G.Ω 1) := by
  intro x hx
  rcases hx with hx | hx
  · exact X1_subset_Omega1 hS hx
  · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact Pset_subset_Omega1 hS (hc i) hxi

omit [NeZero N₁] [NeZero L] in
/-- `Y(𝒞)` is closed under adjacency inside `V(𝒞)`. -/
theorem compY_closed {X₁ : Set (CTorus d L N₁ m₁ K)} {C : Finset ι} {x y : CTorus d L N₁ m₁ K}
    (hx : x ∈ compY c X₁ C)
    (hy : y ∈ patchUnion X₁ (fun i => Pset m₁ (c i)) C) (hxy : Adj x y) :
    y ∈ compY c X₁ C := by
  by_cases hxy' : x = y
  · rw [← hxy']; exact hx
  · obtain ⟨x0, hx0, hpath⟩ := hx
    have hxV : x ∈ patchUnion X₁ (fun i => Pset m₁ (c i)) C :=
      componentOf_subset (latGraph d ((N₁ * L ^ m₁) * L ^ K)) (fun _ h => Or.inl h) ⟨x0, hx0, hpath⟩
    exact ⟨x0, hx0, hpath.tail ⟨⟨hxy', hxy⟩, hxV, hy⟩⟩

end Geometry

section Local

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}

variable (Gp) in
/-- The thickening of a set of sites by the dependency sets `resDep` of Theorem I-4b. -/
def thickSet (Y : Set (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  Y ∪ {y | ∃ x ∈ Y, x ∈ Gp.Ω 1 ∧ y ∈ resDep Gp x}

/-- Two raw data agree on a set of sites. -/
def agreeOn (A : Set (CTorus d L N₁ m₁ K)) (u u' : RawData d L (N₁ * L ^ m₁) K N) : Prop :=
  ∀ x ∈ A, u.1 x = u'.1 x ∧ u.2 x = u'.2 x

theorem thickSet_mono {Y Y' : Set (CTorus d L N₁ m₁ K)} (h : Y ⊆ Y') :
    thickSet Gp Y ⊆ thickSet Gp Y' := by
  rintro y (hy | ⟨x, hx, hxΩ, hyx⟩)
  · exact Or.inl (h hy)
  · exact Or.inr ⟨x, h hx, hxΩ, hyx⟩

omit [NeZero N₁] [NeZero L] in
theorem agreeOn_mono {A A' : Set (CTorus d L N₁ m₁ K)} (h : A ⊆ A')
    {u u' : RawData d L (N₁ * L ^ m₁) K N} (hu : agreeOn A' u u') : agreeOn A u u' :=
  fun x hx => hu x (h hx)

theorem mem_Vset_iff {ι : Type*} [DecidableEq ι] (c : ι → ℕ × CTorus d L N₁ m₁ K)
    {X₁ : Finset (CTorus d L N₁ m₁ K)} (C : Finset ι) {x : CTorus d L N₁ m₁ K} :
    x ∈ Vset X₁ (C.image c) ↔ x ∈ patchUnion (↑X₁ : Set (CTorus d L N₁ m₁ K))
      (fun i => Pset m₁ (c i)) C := by
  classical
  unfold Vset patchUnion
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_coe,
    Set.mem_union, Set.mem_iUnion, exists_prop]
  constructor
  · rintro (h | ⟨P, ⟨i, hi, rfl⟩, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, mem_cubeP.1 hx⟩
  · rintro (h | ⟨i, hi, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c i, ⟨i, hi, rfl⟩, mem_cubeP.2 hx⟩

variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **(AE2): locality of the composite.** -/
theorem fan_local (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    (E : RawData d L (N₁ * L ^ m₁) K N → ℂ) :
    LocalityAEOn (Real.exp κ) (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ K)))
      (fun C u u' => agreeOn (thickSet Gp (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ K)) C)) u u')
      (fun u s => E (D2raw Gk Gj (compWeight L a₁) Fk (D1raw Gp Gk (compWeight L a₁) F₁
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, u)))) := by
  classical
  intro C u u' hu hu'
  obtain ⟨D, hD, rfl⟩ := hu
  obtain ⟨D', hD', rfl⟩ := hu'
  intro s s' hs hs' hag hAg
  set cc : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℕ × CTorus d L N₁ m₁ K := fun i => i.1.1 with hcc
  have hd0 : 0 < d := by have := hB.HBp.hd; omega
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hB.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ := norm_extParams_lt hE1 (fun i => hs.2 i)
  have hsx' : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s' P‖ < Real.exp κ := norm_extParams_lt hE1 (fun i => hs'.2 i)
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  have hs1' := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s'
  obtain ⟨φ, α, hI, hFeq, -, hD1, -⟩ := point_facts hB hF₁ hFk hsx hs1 hD
  obtain ⟨φ', α', hI', hFeq', -, hD1', -⟩ := point_facts hB hF₁ hFk hsx' hs1' hD'
  show E (D2raw Gk Gj (compWeight L a₁) Fk (D1raw Gp Gk (compWeight L a₁) F₁
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, rawOf D))) = E (D2raw Gk Gj (compWeight L a₁) Fk
      (D1raw Gp Gk (compWeight L a₁) F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s', rawOf D')))
  rw [hD1, hD1']
  -- notation
  set Yc : Set (CTorus d L N₁ m₁ K) := compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C with hYc
  set Y : Finset (CTorus d L N₁ m₁ K) := Finset.univ.filter (· ∈ Yc) with hY
  set 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K) := C.image cc with h𝒞
  have hmemY : ∀ x, x ∈ Y ↔ x ∈ Yc := fun x => by simp [hY]
  have hcc_mem : ∀ i, cc i ∈ cubeIdx Gp := fun i => i.1.2
  have hX₁Ω : (↑X₁f : Set (CTorus d L N₁ m₁ K)) ⊆ ↑(Gp.Ω 1) := fun x hx =>
    X1_subset_Omega1 hcov (hX₁ ▸ hx)
  have hPatchΩ : patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ K)) (fun i => Pset m₁ (cc i)) C ⊆
      ↑(Gp.Ω 1) := by
    intro x hx
    rcases hx with hx | hx
    · exact hX₁Ω hx
    · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
      exact Pset_subset_Omega1 hcov (hcc_mem i) hxi
  have hYsub : Yc ⊆ patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ K)) (fun i => Pset m₁ (cc i)) C :=
    componentOf_subset _ (fun _ h => Or.inl h)
  -- the component property
  have hYnn : IsNnComp ((Vset X₁f 𝒞).filter fun x => x ∈ Gp.Ω 1) Y := by
    refine ⟨fun x hx => ?_, fun x hx y hy hadj => ?_⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter]
      exact ⟨(mem_Vset_iff cc C).2 (hYsub hxY), hPatchΩ (hYsub hxY)⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter] at hy
      exact (hmemY y).2 (compY_closed hxY ((mem_Vset_iff cc C).1 hy.1) hadj)
  -- parameters
  have hdisj_of : ∀ P : ↥(cubeIdx Gp), P.1 ∈ parCubes Gp X₁f → Disjoint (Pset m₁ P.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) := by
    intro P hP
    by_contra hnd
    have hsub := Pset_subset_of_not_disjoint (hX₁ ▸ hcov.polySetup) P.2 hnd
    unfold parCubes at hP
    rw [Finset.mem_filter] at hP
    apply hP.2
    intro y hy
    have := hsub (mem_cubeP.1 hy)
    exact Finset.mem_coe.1 this
  have hs1E : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁f →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) P = 1 ∧ extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s') P = 1 := by
    intro P hP hPn
    unfold extS
    simp only [hP, ↓reduceDIte]
    exact ⟨hs1 P hP hPn, hs1' P hP hPn⟩
  have hs0E : ∀ P ∈ parCubes Gp X₁f, P ∉ 𝒞 →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) P = 0 ∧ extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s') P = 0 := by
    intro P hP hP𝒞
    have hPc : P ∈ cubeIdx Gp := (Finset.mem_filter.1 hP).1
    have hd := hdisj_of ⟨P, hPc⟩ hP
    unfold extS
    simp only [hPc, ↓reduceDIte]
    have hi : (⟨⟨P, hPc⟩, hd⟩ : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))) ∉ C := fun hi =>
      hP𝒞 (Finset.mem_image.2 ⟨_, hi, rfl⟩)
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s ⟨P, hPc⟩ = s ⟨⟨P, hPc⟩, hd⟩ from extParams_par s ⟨⟨P, hPc⟩, hd⟩,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s' ⟨P, hPc⟩ = s' ⟨⟨P, hPc⟩, hd⟩ from extParams_par s' ⟨⟨P, hPc⟩, hd⟩]
    exact ⟨hs.1 _ hi, hs'.1 _ hi⟩
  have hagE : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) P = extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s') P := by
    intro P hP𝒞 hSub
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    have hsub : Pset m₁ (cc i) ⊆ Yc := by
      intro x hx
      have hxΩ : x ∈ Gp.Ω 1 := Pset_subset_Omega1 hcov (hcc_mem i) hx
      exact (hmemY x).1 (hSub ⟨x, hxΩ⟩ (mem_cubeP.2 hx))
    have := hag i hi hsub
    unfold extS
    simp only [hcc_mem i, ↓reduceDIte]
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s ⟨cc i, hcc_mem i⟩ = s i from extParams_par s i,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s' ⟨cc i, hcc_mem i⟩ = s' i from extParams_par s' i]
    exact this
  -- the data domain
  have hc1 := one_le_xiC1 d
  have hε := hB.num.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hB.num.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hB.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hB.HBp hB.num.small1 hD
  have hDom' := xiCData_inDomainC hB.HBp hB.num.small1 hD'
  have hdata : ∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ Y → ∀ y ∈ resDep Gp (x : CTorus d L N₁ m₁ K),
      D.Ψ y = D'.Ψ y ∧ (y ∈ Gp.Ω 1 → D.h y = D'.h y) := by
    intro x hx y hy
    have := hAg y (Or.inr ⟨x, (hmemY x).1 hx, x.2, hy⟩)
    exact ⟨this.1, fun _ => this.2⟩
  obtain ⟨-, key⟩ := i4b_local hB.hS hB.Sp hconn hB.HBp hB.hκ.le hB.hM
    (fun P => (hsx P).le) (fun P => (hsx' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom hDom' hYnn hs1E hs0E
    hagE hdata hI hI'
  -- the composed data coincide
  have hXY : ∀ y ∈ X₁f, y ∈ Yc := fun y hy => subset_compY (↑X₁f : Set (CTorus d L N₁ m₁ K)) C (Finset.mem_coe.2 hy)
  have hXthick : ∀ y ∈ X₁f, D.Ψ y = D'.Ψ y ∧ D.h y = D'.h y := fun y hy =>
    hAg y (Or.inl (hXY y hy))
  refine congrArg _ ?_
  refine congrArg _ ?_
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · show composeField Gk Gp (compWeight L a₁) φ D.Ψ x i = composeField Gk Gp (compWeight L a₁) φ' D'.Ψ x i
    by_cases hx : x ∈ dataSites Gk
    · refine composeField_congr (G := Gk) (G' := Gp) (compWeight L a₁) (fun y hy jj => ?_)
        (fun jj => congrFun (hXthick x (hB.dep x hx x (self_mem_composeDep x))).1 jj) i
      have hyX := hB.dep x hx y hy
      have hyΩ : y ∈ Gp.Ω 1 := hX₁Ω (Finset.mem_coe.2 hyX)
      rw [svec_of_mem' φ hyΩ jj, svec_of_mem' φ' hyΩ jj]
      exact key ⟨y, hyΩ⟩ ((hmemY y).2 (hXY y hyX)) jj
    · rw [composeField_of_not_mem _ φ D.Ψ hx i, composeField_of_not_mem _ φ' D'.Ψ hx i]
  · show (if x ∈ Gk.Ω 1 then D.h x i else 0) = (if x ∈ Gk.Ω 1 then D'.h x i else 0)
    by_cases hx : x ∈ Gk.Ω 1
    · simp only [hx, ↓reduceIte]
      have hxd : x ∈ dataSites Gk := (mem_dataSites Gk).2 (Or.inl hx)
      exact congrFun (hXthick x (hB.dep x hxd x (self_mem_composeDep x))).2 i
    · simp [hx]

end Local

end Balaban.Localization
