/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5FluctGeom
public import Balaban.Localization.I5FluctFan
public import Balaban.Localization.I5Local
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# (AE2): locality of the composite with the fluctuation (LOCALIZATION.md §4.4)

If the decoupling vectors `s, s'` vanish outside a family `𝒞`, agree on the cubes of `𝒞` inside
`Y(𝒞)`, and the data `(Θ, ψ')`, `(Θ', ψ'')` agree on the thickening of `Y(𝒞)` (for `Θ`: by the
dependency sets `resDep`; for the layer-constant `ψ'`: on `Y(𝒞)` and its neighbours), then the
composites agree
(`fan_local_fl`).  The background fields agree by Theorem I-4b (iv) (nearest-neighbour components);
the fluctuation fields by Theorem I-4a (e) in footprint form (`Dec2.i4a_local_fpS`), for the
parameter-incidence graph of `(C, H⁻)`, of which the components `Y(𝒞)` are unions
(`incUnion_of_nnComp`); the direct term `κ ψ'` of the composed fluctuation (P3 (4.17)) reads `ψ'`
only on the data sites of `𝔹_k(X)`, inside `X₁ ⊆ Y(𝒞)`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis Finset Matrix

section Local

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ₂} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

/-- The set `Y` and its nearest neighbours. -/
def psiThick (Y : Set (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  {y | y ∈ Y ∨ ∃ x ∈ Y, Adj x y}

omit [NeZero N₁] [NeZero L] in
theorem psiThick_mono {Y Y' : Set (CTorus d L N₁ m₁ K)} (h : Y ⊆ Y') : psiThick Y ⊆ psiThick Y' := by
  rintro y (hy | ⟨x, hx, hxy⟩)
  · exact Or.inl (h hy)
  · exact Or.inr ⟨x, h hx, hxy⟩

variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **(AE2): locality of the composite with the fluctuation.** -/
theorem fan_local_fl (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Fk : RawData d L (N₁ * L ^ m₁) K N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (E : RawData d L (N₁ * L ^ m₁) K N → ℂ) :
    LocalityAEOn (Real.exp κ) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBallLC Hm δ₁)
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ K)))
      (fun C u u' => agreeOn (thickSet Gp (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ K)) C)) u.1 u'.1 ∧
        ∀ y ∈ psiThick (compY
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ K)) C), u.2 y = u'.2 y)
      (fun u s => E (D2raw Gk Gj (compWeight L a₁) Fk (D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) u))) := by
  classical
  rintro C ⟨u, ψ⟩ ⟨u', ψ'⟩ ⟨⟨D, hD, rfl⟩, hψ, hψc⟩ ⟨⟨D', hD', rfl⟩, hψ', hψc'⟩ s s' hs hs' hag hAg
  obtain ⟨hAgΘ, hAgψ⟩ := hAg
  set cc : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℕ × CTorus d L N₁ m₁ K :=
    fun i => i.1.1 with hcc
  have hd0 : 0 < d := by have := hB.HBp.hd; omega
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hB.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs.2 i)
  have hsx' : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s' P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs'.2 i)
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  have hs1' := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s'
  obtain ⟨φ, α, δφ, hI, hFeq, hstrict, hδφ, hX3, hrawD, hD2, hX2⟩ :=
    point_facts_fl hB hF hF₁ hFk hSol hsx hs1 hD hψ hψc
  obtain ⟨φ', α', δφ', hI', hFeq', hstrict', hδφ', hX3', hrawD', hD2', hX2'⟩ :=
    point_facts_fl hB hF hF₁ hFk hSol hsx' hs1' hD' hψ' hψc'
  show E (D2raw Gk Gj (compWeight L a₁) Fk (D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) (rawOf D, ψ))) =
    E (D2raw Gk Gj (compWeight L a₁) Fk (D1rawFl Gp Gk Hm (compWeight L a₁) F₁ Sol
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s') (rawOf D', ψ')))
  rw [hrawD, hrawD']
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
  have hYnn : IsNnComp ((Vset X₁f 𝒞).filter fun x => x ∈ Gp.Ω 1) Y := by
    refine ⟨fun x hx => ?_, fun x hx y hy hadj => ?_⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter]
      exact ⟨(mem_Vset_iff cc C).2 (hYsub hxY), hPatchΩ (hYsub hxY)⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter] at hy
      exact (hmemY y).2 (compY_closed hxY ((mem_Vset_iff cc C).1 hy.1) hadj)
  have hdisj_of : ∀ P : ↥(cubeIdx Gp), P.1 ∈ parCubes Gp X₁f →
      Disjoint (Pset m₁ P.1) (↑X₁f : Set (CTorus d L N₁ m₁ K)) := by
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
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) P = 1 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s') P = 1 := by
    intro P hP hPn
    unfold extS
    simp only [hP, ↓reduceDIte]
    exact ⟨hs1 P hP hPn, hs1' P hP hPn⟩
  have hs0E : ∀ P ∈ parCubes Gp X₁f, P ∉ 𝒞 →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) P = 0 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s') P = 0 := by
    intro P hP hP𝒞
    have hPc : P ∈ cubeIdx Gp := (Finset.mem_filter.1 hP).1
    have hd := hdisj_of ⟨P, hPc⟩ hP
    unfold extS
    simp only [hPc, ↓reduceDIte]
    have hi : (⟨⟨P, hPc⟩, hd⟩ : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))) ∉ C := fun hi =>
      hP𝒞 (Finset.mem_image.2 ⟨_, hi, rfl⟩)
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s ⟨P, hPc⟩ =
        s ⟨⟨P, hPc⟩, hd⟩ from extParams_par s ⟨⟨P, hPc⟩, hd⟩,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s' ⟨P, hPc⟩ =
        s' ⟨⟨P, hPc⟩, hd⟩ from extParams_par s' ⟨⟨P, hPc⟩, hd⟩]
    exact ⟨hs.1 _ hi, hs'.1 _ hi⟩
  have hsub : ∀ P ∈ 𝒞, (∀ x ∈ cubeP P, x ∈ Y) →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) P =
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s') P := by
    intro P hP𝒞 hSub
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    have hsub : Pset m₁ (cc i) ⊆ Yc := by
      intro x hx
      have hxΩ : x ∈ Gp.Ω 1 := Pset_subset_Omega1 hcov (hcc_mem i) hx
      exact (hmemY x).1 (hSub x (mem_cubeP.2 hx))
    have := hag i hi hsub
    unfold extS
    simp only [hcc_mem i, ↓reduceDIte]
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s ⟨cc i, hcc_mem i⟩ = s i from
        extParams_par s i,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s' ⟨cc i, hcc_mem i⟩ = s' i from
        extParams_par s' i]
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
    have := hAgΘ y (Or.inr ⟨x, (hmemY x).1 hx, x.2, hy⟩)
    exact ⟨this.1, fun _ => this.2⟩
  have hagE : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) P =
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s') P := by
    intro P hP𝒞 hSub
    refine hsub P hP𝒞 (fun x hx => ?_)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    exact hSub ⟨x, Pset_subset_Omega1 hcov (hcc_mem i) (mem_cubeP.1 hx)⟩ hx
  -- the background fields agree
  obtain ⟨hαSY, hφY⟩ := i4b_local hB.hS hB.Sp hconn hB.HBp hB.hκ.le hB.hM
    (fun P => (hsx P).le) (fun P => (hsx' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom hDom' hYnn
    hs1E hs0E hagE hdata hI hI'
  -- the geometry of the pair
  have SL : Dec2.CoverLocal (coverOf Gp) Gp (compWeight L a₁) ν (Dec2.selfKc d L) (Cchi d L) :=
    Dec2.coverLocal_self hB.Sp
  have hconn' : Dec2.HatConn (coverOf Gp) Gp := hconn
  have h𝒞c : ∀ P ∈ 𝒞, P ∈ (coverOf Gp).cubeIdx := by
    intro P hP
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hP
    exact hcc_mem i
  have hsubΩ : ∀ x, x ∈ Hm.Ω 1 → x ∈ Gp.Ω 1 := fun x hx => hF.hPmp.mem_Ω1 hx
  obtain ⟨A, hIU, hAcube⟩ := incUnion_of_nnComp SL hconn' hsubΩ hrow h𝒞c hYnn
  -- the fluctuation fields agree
  set e := flEdat Gp Hm (φ, α) D.Ψ ψ with he
  set e' := flEdat Gp Hm (φ', α') D'.Ψ ψ' with he'
  obtain ⟨hfld, hfix, hs6, hsK, hdp, huniq⟩ := hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s, e) hsx hstrict
  obtain ⟨hfld', hfix', hs6', hsK', hdp', huniq'⟩ :=
    hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) s', e') hsx' hstrict'
  have hOp := hF.SM.toCoverBase.toOpSetting.toGreen
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hB.hS.fam.2.1 hd0).le hδ0.le)
  have Hh : DecHyp Hm (compWeight L a₁) ν false e.2.1 e.1 e.2.2.1 e.2.2.2
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hF.num.δ₁_pos.le
      hF.num.B_one hstrict
  have Hh' : DecHyp Hm (compWeight L a₁) ν false e'.2.1 e'.1 e'.2.2.1 e'.2.2.2
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hF.num.δ₁_pos.le
      hF.num.B_one hstrict'
  have hDA : Dec2.DataAgreeS Hm N Y (Dec2.SYF (coverOf Gp) Hm (compWeight L a₁) ν X₁f 𝒞 Y)
      e.2.1 e'.2.1 e.1 e'.1 e.2.2.1 e'.2.2.1 e.2.2.2 e'.2.2.2 := by
    refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun y hy hxy => ?_, fun x hx i => rfl⟩
    · have := hαSY ⟨x, hsubΩ x x.2⟩ (SYF_subset_SY SL hconn' hsubΩ hYnn hx)
      show flAlpha Gp Hm α x = flAlpha Gp Hm α' x
      rw [flAlpha_of_prec hF.hPmp, flAlpha_of_prec hF.hPmp]
      exact this
    · have hxΩ := hsubΩ x x.2
      funext i
      show barField Gp D.Ψ φ x i = barField Gp D'.Ψ φ' x i
      simp only [barField, hxΩ, ↓reduceDIte]
      exact hφY ⟨x, hxΩ⟩ hx i
    · exact hAgψ x (Or.inl ((hmemY x).1 hx))
    · obtain ⟨x, hx, hadj⟩ := hxy
      exact hAgψ y (Or.inr ⟨x, (hmemY x).1 hx, hadj⟩)
  have hflloc := Dec2.i4a_local_fpS hF.hS2.fam hF.SM hB.hκ.le hF.hM2 (fun P => (hsx P).le)
    (fun P => (hsx' P).le) Hh Hh' hF.num.B_le hF.num.δ₁_le hIU hs1E hs0E
    (fun P hP hPA => hsub P hP (hAcube P hPA).2) hDA
    hfix hs6 hfix' hs6'
  have hδeq : ∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i, δφ (y, i) = δφ' (y, i) := by
    intro y hy i
    rw [← hδφ, ← hδφ', hfld, hfld']
    exact hflloc.2 y hy i
  -- the composed data coincide
  have hXY : ∀ y ∈ X₁f, y ∈ Yc := fun y hy =>
    subset_compY (↑X₁f : Set (CTorus d L N₁ m₁ K)) C (Finset.mem_coe.2 hy)
  have hXthick : ∀ y ∈ X₁f, D.Ψ y = D'.Ψ y ∧ D.h y = D'.h y := fun y hy =>
    hAgΘ y (Or.inl (hXY y hy))
  refine congrArg E (congrArg (D2raw Gk Gj (compWeight L a₁) Fk) ?_)
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · show (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ hψc).Ψ x i =
      (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ' δφ' D' ψ' hψc').Ψ x i
    rw [flDatum_Ψ, flDatum_Ψ]
    by_cases hx : x ∈ dataSites Gk
    · congr 1
      · refine composeField_congr (G := Gk) (G' := Gp) (compWeight L a₁) (fun y hy jj => ?_)
          (fun jj => congrFun (hXthick x (hB.dep x hx x (self_mem_composeDep x))).1 jj) i
        have hyX := hB.dep x hx y hy
        have hyΩ : y ∈ Gp.Ω 1 := hX₁Ω (Finset.mem_coe.2 hyX)
        rw [svec_of_mem' φ hyΩ jj, svec_of_mem' φ' hyΩ jj]
        exact hφY ⟨y, hyΩ⟩ ((hmemY y).2 (hXY y hyX)) jj
      · refine composeField_congr (G := Gk) (G' := Hm) (compWeight L a₁) (fun y hy jj => ?_)
          (fun jj => congrFun (hAgψ x (Or.inl (hXY x (hF.depm x hx x
            (self_mem_composeDep x))))) jj) i
        have hyX := hF.depm x hx y hy
        by_cases hyΩ : y ∈ Hm.Ω 1
        · rw [svec_of_mem' δφ hyΩ jj, svec_of_mem' δφ' hyΩ jj]
          exact hδeq ⟨y, hyΩ⟩ ((hmemY y).2 (hXY y hyX)) jj
        · rw [svec_of_not_mem Hm δφ hyΩ jj, svec_of_not_mem Hm δφ' hyΩ jj]
    · rw [composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx,
        composeField_of_not_mem _ _ _ hx, composeField_of_not_mem _ _ _ hx]
  · show (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ δφ D ψ hψc).h x i =
      (flDatum Gk hB.hP hF.hPm (compWeight L a₁) φ' δφ' D' ψ' hψc').h x i
    rw [flDatum_h, flDatum_h]
    show (if x ∈ Gk.Ω 1 then D.h x i else 0) = (if x ∈ Gk.Ω 1 then D'.h x i else 0)
    by_cases hx : x ∈ Gk.Ω 1
    · simp only [hx, ↓reduceIte]
      have hxd : x ∈ dataSites Gk := (mem_dataSites Gk).2 (Or.inl hx)
      exact congrFun (hXthick x (hB.dep x hxd x (self_mem_composeDep x))).2 i
    · simp [hx]

end Local

end Balaban.Localization
