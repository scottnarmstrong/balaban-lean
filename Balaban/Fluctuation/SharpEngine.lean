/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.SharpFan
public import Balaban.Fluctuation.InteractionHatLC

/-!
# Sharp locality of the fan and the sharp engine, layer-constant variant

`fanHL_local_dir`: `fanH_local_dir` for the functionals on `FlRealLC` (layer-constant
fluctuation), by the same proof.  `i5_functional_hat_dir` and `i5_functional_hatLC_dir` feed the
sharp fan locality (`fanH_local_dir`, `fanHL_local_dir`) into the landed sharp engine
`i5_functional_hat_dir_of_fan`, `i5_functional_hatLC_dir_of_fan`.

These theorems are for functionals that read the fluctuation variable `ψ'` only on `Z`
(`hΦlocDir`).  That the four physical summands satisfy this premise is NOT proved here;
`PhysicalSharpLoc` and `physical_directTerms` remain open.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Finset Matrix

section Fan

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **(AE2), locality, for a functional of the decoupled objects with the fluctuation decoupled by
the cover parameters.**  If `Φ` depends on the triple only through its values on a set
`Z ⊆ X₁`, the composite is local in `(Θ, ψ̂)`, with agreement of `ψ̂` on the unit points of the
thick set. -/
theorem fanHL_local_dir (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X) (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
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
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    {Z Zα : Set (CTorus d L N₁ m₁ (k + 1))} (hZ : Z ⊆ ↑X₁f) (hBM : BlockMargin Gp X₁f Zα)
    (hΦlocDir : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ∀ t' ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i)) →
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Zα → t.1.2 y = t'.1.2 y) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i)) →
      agreeOn (thickSet Gp Z) t.2.2.1 t'.2.2.1 → (∀ y ∈ Z, t.2.2.2 y = t'.2.2.2 y) →
      Φ t.1 t.2.1 t.2.2 = Φ t'.1 t'.2.1 t'.2.2) :
    LocalityAEOn (Real.exp κ)
      (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun C u u' => AgHatDir hG' (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)) ) C) u u')
      (fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
            u.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
        (u.1, hatPsiF Gp a₁ ν hG' cc F₁
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) := by
  classical
  rintro C ⟨u, ψh⟩ ⟨u', ψh₂⟩ ⟨⟨D, hD, rfl⟩, hψh⟩ ⟨⟨D', hD', rfl⟩, hψh₂⟩ s s' hs hs' hag hAg
  obtain ⟨hAgΘ, hAgψ⟩ := hAg
  set cmap : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℕ × CTorus d L N₁ m₁ (k + 1) :=
    fun i => i.1.1 with hcc
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs.2 i)
  have hsx' : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s' P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs'.2 i)
  have hs1 := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s
  have hs1' := extParams_hs1 (X₁f := X₁f) (Gp := Gp) s'
  have hψ : hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s)
      (rawOf D) ψh ∈ FlBall Hm δ₁ :=
    (hatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hF₁ hsx hD hψh).1
  have hψ₂ : hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s')
      (rawOf D') ψh₂ ∈ FlBall Hm δ₁ :=
    (hatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hF₁ hsx' hD' hψh₂).1
  set ψ := hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s)
    (rawOf D) ψh with hψdef
  set ψ₂ := hatPsiF Gp a₁ ν hG' cc F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s')
    (rawOf D') ψh₂ with hψ₂def
  obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
    point_facts_core hC hF₁ hSol hsx hs1 hD hψ
  obtain ⟨φ', α', δφ', δα', hI', hFeq', hstrict', hSeq', hmem'⟩ :=
    point_facts_core hC hF₁ hSol hsx' hs1' hD' hψ₂
  show Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
          D.Ψ ψ)).1 (rawOf D, ψ) =
    Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', rawOf D'))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s',
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', rawOf D'))
          D'.Ψ ψ₂)).1 (rawOf D', ψ₂)
  rw [hFeq, hFeq', hSeq, hSeq']
  -- notation
  set Yc : Set (CTorus d L N₁ m₁ (k + 1)) := compY cmap (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C with hYc
  set Y : Finset (CTorus d L N₁ m₁ (k + 1)) := Finset.univ.filter (· ∈ Yc) with hY
  set 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1)) := C.image cmap with h𝒞
  have hmemY : ∀ x, x ∈ Y ↔ x ∈ Yc := fun x => by simp [hY]
  have hcc_mem : ∀ i, cmap i ∈ cubeIdx Gp := fun i => i.1.2
  have hX₁Ω : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) ⊆ ↑(Gp.Ω 1) := fun x hx =>
    X1_subset_Omega1 hcov (hX₁ ▸ hx)
  have hPatchΩ : patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) (fun i => Pset m₁ (cmap i)) C ⊆
      ↑(Gp.Ω 1) := by
    intro x hx
    rcases hx with hx | hx
    · exact hX₁Ω hx
    · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 hx
      exact Pset_subset_Omega1 hcov (hcc_mem i) hxi
  have hYsub : Yc ⊆ patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) (fun i => Pset m₁ (cmap i)) C :=
    componentOf_subset _ (fun _ h => Or.inl h)
  have hYnn : IsNnComp ((Vset X₁f 𝒞).filter fun x => x ∈ Gp.Ω 1) Y := by
    refine ⟨fun x hx => ?_, fun x hx y hy hadj => ?_⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter]
      exact ⟨(mem_Vset_iff cmap C).2 (hYsub hxY), hPatchΩ (hYsub hxY)⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter] at hy
      exact (hmemY y).2 (compY_closed hxY ((mem_Vset_iff cmap C).1 hy.1) hadj)
  have hdisj_of : ∀ P : ↥(cubeIdx Gp), P.1 ∈ parCubes Gp X₁f →
      Disjoint (Pset m₁ P.1) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) := by
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
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P = 1 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P = 1 := by
    intro P hP hPn
    unfold extS
    simp only [hP, ↓reduceDIte]
    exact ⟨hs1 P hP hPn, hs1' P hP hPn⟩
  have hs0E : ∀ P ∈ parCubes Gp X₁f, P ∉ 𝒞 →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P = 0 ∧
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P = 0 := by
    intro P hP hP𝒞
    have hPc : P ∈ cubeIdx Gp := (Finset.mem_filter.1 hP).1
    have hd := hdisj_of ⟨P, hPc⟩ hP
    unfold extS
    simp only [hPc, ↓reduceDIte]
    have hi : (⟨⟨P, hPc⟩, hd⟩ : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))) ∉ C := fun hi =>
      hP𝒞 (Finset.mem_image.2 ⟨_, hi, rfl⟩)
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s ⟨P, hPc⟩ =
        s ⟨⟨P, hPc⟩, hd⟩ from extParams_par s ⟨⟨P, hPc⟩, hd⟩,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s' ⟨P, hPc⟩ =
        s' ⟨⟨P, hPc⟩, hd⟩ from extParams_par s' ⟨⟨P, hPc⟩, hd⟩]
    exact ⟨hs.1 _ hi, hs'.1 _ hi⟩
  have hsub : ∀ P ∈ 𝒞, (∀ x ∈ cubeP P, x ∈ Y) →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P =
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P := by
    intro P hP𝒞 hSub
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    have hsub : Pset m₁ (cmap i) ⊆ Yc := by
      intro x hx
      have hxΩ : x ∈ Gp.Ω 1 := Pset_subset_Omega1 hcov (hcc_mem i) hx
      exact (hmemY x).1 (hSub x (mem_cubeP.2 hx))
    have := hag i hi hsub
    unfold extS
    simp only [hcc_mem i, ↓reduceDIte]
    rw [show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s ⟨cmap i, hcc_mem i⟩ = s i from
        extParams_par s i,
      show extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s' ⟨cmap i, hcc_mem i⟩ = s' i from
        extParams_par s' i]
    exact this
  -- the data domain
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
  have hDom' := xiCData_inDomainC hC.HBp hC.small1 hD'
  have hdata : ∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ y ∈ resDep Gp (x : CTorus d L N₁ m₁ (k + 1)),
      D.Ψ y = D'.Ψ y ∧ (y ∈ Gp.Ω 1 → D.h y = D'.h y) := by
    intro x hx y hy
    have := hAgΘ y (Or.inr ⟨x, (hmemY x).1 hx, x.2, hy⟩)
    exact ⟨this.1, fun _ => this.2⟩
  have hagE : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) P =
        extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s') P := by
    intro P hP𝒞 hSub
    refine hsub P hP𝒞 (fun x hx => ?_)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    exact hSub ⟨x, Pset_subset_Omega1 hcov (hcc_mem i) (mem_cubeP.1 hx)⟩ hx
  have hYYc : (↑Y : Set (CTorus d L N₁ m₁ (k + 1))) = Yc := by
    ext x; exact hmemY x
  -- the background fields agree
  obtain ⟨hαSY, hφY⟩ := i4b_local hC.hS hC.Sp hconn hC.HBp hC.hκ.le hC.hM
    (fun P => (hsx P).le) (fun P => (hsx' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom hDom' hYnn
    hs1E hs0E hagE hdata hI hI'
  -- the geometry of the pair
  have SL : Dec2.CoverLocal (coverOf Gp) Gp (compWeight L a₁) ν (Dec2.selfKc d L) (Cchi d L) :=
    Dec2.coverLocal_self hC.Sp
  have hconn' : Dec2.HatConn (coverOf Gp) Gp := hconn
  have h𝒞c : ∀ P ∈ 𝒞, P ∈ (coverOf Gp).cubeIdx := by
    intro P hP
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hP
    exact hcc_mem i
  have hsubΩ : ∀ x, x ∈ Hm.Ω 1 → x ∈ Gp.Ω 1 := fun x hx => hC.hPmp.mem_Ω1 hx
  obtain ⟨A, hIU, hAcube⟩ := incUnion_of_nnComp SL hconn' hsubΩ hrow h𝒞c hYnn
  -- the fluctuation fields agree
  set e := flEdat Gp Hm (φ, α) D.Ψ ψ with he
  set e' := flEdat Gp Hm (φ', α') D'.Ψ ψ₂ with he'
  obtain ⟨hfld, hfix, hs6, hsK, hdp, huniq⟩ := hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, e) hsx hstrict
  obtain ⟨hfld', hfix', hs6', hsK', hdp', huniq'⟩ :=
    hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', e') hsx' hstrict'
  have hOp := hC.SM.toCoverBase.toOpSetting.toGreen
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  have Hh : DecHyp Hm (compWeight L a₁) ν false e.2.1 e.1 e.2.2.1 e.2.2.2
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict
  have Hh' : DecHyp Hm (compWeight L a₁) ν false e'.2.1 e'.1 e'.2.2.1 e'.2.2.2
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict'
  have hX₁cell : IsCellUnion (L ^ (k + 1)) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) := by
    rw [hX₁]; exact X1_isCellUnion_unit hcov.hN
  have h𝒞' : ∀ P ∈ 𝒞, P ∈ cubeIdx Gp := h𝒞c
  have hdataY : ∀ z ∈ Y, D.Ψ z = D'.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D'.h z) := fun z hz => by
    have := hAgΘ z (Or.inl ((hmemY z).1 hz))
    exact ⟨this.1, fun _ => this.2⟩
  have hh : ∀ b : unitPts Gp, UnitOut Gp Y b → ∀ i, ψh (b, i) = ψh₂ (b, i) := by
    intro b hb i
    obtain ⟨x, -, hxb⟩ := (mem_unitPts Gp).1 b.2
    have hxΩ : x ∈ Gp.Ω 1 := by rw [hG'.Ω_one]; exact Finset.mem_univ _
    have hxY : x ∈ Y := hb ⟨x, hxΩ⟩ (by simp only [hxb])
    have hbx : b = unitPt hG' x := Subtype.ext hxb.symm
    rw [hbx]
    exact hAgψ x ((hmemY x).1 hxY) i
  have hψY := hatPsiF_rows hC hk hG' cc hconn hMX hdm hα hsm hF₁ hsx hsx' hD hD' hYnn hs1E hs0E
    hagE hX₁cell h𝒞' hdataY ψh ψh₂ hh
  have hOp := hC.SM.toCoverBase.toOpSetting.toGreen
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  set e := flEdat Gp Hm (φ, α) D.Ψ ψ with he
  set e' := flEdat Gp Hm (φ', α') D'.Ψ ψ₂ with he'
  obtain ⟨hfld, hfix, hs6, hsK, hdp, huniq⟩ := hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, e) hsx hstrict
  obtain ⟨hfld', hfix', hs6', hsK', hdp', huniq'⟩ :=
    hSol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', e') hsx' hstrict'
  have Hh : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α) (barField Gp D.Ψ φ) ψ 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict
  have Hh' : DecHyp Hm (compWeight L a₁) ν false (flAlpha Gp Hm α') (barField Gp D'.Ψ φ') ψ₂ 0
      (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ :=
    StrictDataM.hyp hOp hB0 hC.δ₁_pos.le hC.B_one hstrict'
  have h1 : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, e)).1 = δφ :=
    congrArg Prod.fst hSeq
  have h2 : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', e')).1 = δφ' :=
    congrArg Prod.fst hSeq'
  have h1' : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, e)).2 = δα :=
    congrArg Prod.snd hSeq
  have h2' : (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s', e')).2 = δα' :=
    congrArg Prod.snd hSeq'
  rw [h1'] at hfld hfix hs6
  rw [h2'] at hfld' hfix' hs6'
  have hflc := fluct_correction_rows_of_agree_on_component hC hk hG' hG cc hconn hrow hMX hdm hα
    hsm hF₁ hsx hsx' hD hD' hYnn hs1E hs0E hagE hX₁cell h𝒞' hdataY ψh ψh₂ hh hI hI' Hh Hh'
    hfix hs6 hfix' hs6'
  have hδeq : ∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i, δφ (y, i) = δφ' (y, i) := by
    intro y hy i
    rw [← h1, ← h2, hfld, hfld']
    exact hflc.2 y hy i
  have hZY : ∀ y ∈ Z, y ∈ Yc := fun y hy =>
    subset_compY (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C (hZ hy)
  have hXY' : ∀ x ∈ X₁f, x ∈ Y := fun x hx => (hmemY x).2 (subset_compY
    (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C (Finset.mem_coe.2 hx))
  have hαeq : ∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Zα → α y = α' y := by
    intro y hy
    obtain ⟨z, hz, hyz, hQ, hhat⟩ := hBM y hy y.2
    refine hαSY y (Finset.mem_biUnion.2 ⟨z, Finset.mem_filter.2 ⟨hz, ?_, ?_⟩, hyz⟩)
    · intro P hP hPpar
      exact absurd hPpar (hQ P hP)
    · intro x hx
      exact hXY' _ (hhat x hx)
  refine hΦlocDir _ ⟨hmem, isLayerConstant_liftC hG hG' _⟩ _ ⟨hmem', isLayerConstant_liftC hG hG' _⟩ (fun y hy i => ?_) (fun y hy => hαeq y hy) (fun y hy i => ?_) ?_ ?_
  · exact hφY y ((hmemY _).2 (hZY _ hy)) i
  · exact hδeq y ((hmemY _).2 (hZY _ hy)) i
  · exact agreeOn_mono (thickSet_mono (fun y hy => hZY y hy)) hAgΘ
  · exact fun y hy => hψY y ((hmemY y).2 (hZY y hy))


/-- **Theorem I-5 for a functional of the decoupled objects, sharp form.**  `i5_functional_hat`
with the functional premise `hΦlocDir` (the functional reads `ψ'` only on `Z`) and the conclusion
for `AgHatDir`: the term `Ev_Y` depends on the hat variable only at the unit points of the sites of
`Y`.  Obtained from `i5_functional_hat_dir_of_fan` and `fanH_local_dir`. -/
theorem i5_functional_hat_dir (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hΦbd : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ‖Φ t.1 t.2.1 t.2.2‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {Z Zα : Set (CTorus d L N₁ m₁ (k + 1))} (hZ : Z ⊆ ↑X₁f) (hBM : BlockMargin Gp X₁f Zα)
    (hΦlocDir : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ∀ t' ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i)) →
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Zα → t.1.2 y = t'.1.2 y) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i)) →
      agreeOn (thickSet Gp Z) t.2.2.1 t'.2.2.1 → (∀ y ∈ Z, t.2.2.2 y = t'.2.2.2 y) →
      Φ t.1 t.2.1 t.2.2 = Φ t'.1 t'.2.1 t'.2.2) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))))
          (rawOf D, liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  exact i5_functional_hat_dir_of_fan hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb hΦan hΦbd
    (fun {F₁} hF₁ {Sol} hSol => fanH_local_dir hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hF₁ hSol hZ
      hBM hΦlocDir)

/-- **Theorem I-5, sharp form, layer-constant fluctuation.**  As `i5_functional_hat_dir` for the
functional on `FlRealLC`; obtained from `i5_functional_hatLC_dir_of_fan` and `fanHL_local_dir`. -/
theorem i5_functional_hatLC_dir (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hΦbd : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ‖Φ t.1 t.2.1 t.2.2‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    {Z Zα : Set (CTorus d L N₁ m₁ (k + 1))} (hZ : Z ⊆ ↑X₁f) (hBM : BlockMargin Gp X₁f Zα)
    (hΦlocDir : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ∀ t' ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i)) →
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Zα → t.1.2 y = t'.1.2 y) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i)) →
      agreeOn (thickSet Gp Z) t.2.2.1 t'.2.2.1 → (∀ y ∈ Z, t.2.2.2 y = t'.2.2.2 y) →
      Φ t.1 t.2.1 t.2.2 = Φ t'.1 t'.2.1 t'.2.2) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))))
          (rawOf D, liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' → Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  exact i5_functional_hatLC_dir_of_fan hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb hΦan hΦbd
    (fun {F₁} hF₁ {Sol} hSol => fanHL_local_dir hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov hX₁ hconn hrow hF₁ hSol hZ
      hBM hΦlocDir)


omit hC in
/-- **A non-constant instance of the premise `hΦlocDir`**: the coordinate `i` of the fluctuation
variable `ψ'` at a site `y₀` of `Z` reads `ψ'` only on `Z`.  Since `ψ'` is a free component of the
triple, this functional is not constant in general; it shows that the premise is satisfied by a
functional that genuinely reads `ψ'`. -/
theorem hΦlocDir_psiCoord {T : Set (((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))}
    {Z Zα : Set (CTorus d L N₁ m₁ (k + 1))} {y₀ : CTorus d L N₁ m₁ (k + 1)} (hy₀ : y₀ ∈ Z)
    (i : Fin N) :
    ∀ t ∈ T, ∀ t' ∈ T,
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i)) →
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Zα → t.1.2 y = t'.1.2 y) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i)) →
      agreeOn (thickSet Gp Z) t.2.2.1 t'.2.2.1 → (∀ y ∈ Z, t.2.2.2 y = t'.2.2.2 y) →
      (fun (_ : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) (_ : Hm.Ω 1 × Fin N → ℂ)
        (r : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
          r.2 y₀ i) t.1 t.2.1 t.2.2 =
      (fun (_ : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) (_ : Hm.Ω 1 × Fin N → ℂ)
        (r : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) =>
          r.2 y₀ i) t'.1 t'.2.1 t'.2.2 :=
  fun _ _ _ _ _ _ _ _ hψ => congrFun (hψ y₀ hy₀) i

/-- **The expansion engine for the sharp agreement relation.**  As `i5_functional_hat_dir_of_fan`,
with the fan locality hypothesis and the locality clause of the conclusion for raw data agreeing on
the domain `Y` itself (not on `thickSet Y`) and hat variables agreeing at the unit points of `Y`.
Instance of `i5_functional_rel_of_fan`.
The last conjunct exhibits the terms, as in `i5_functional_rel_of_fan`. -/
theorem i5_functional_hat_rawY_of_fan (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
        (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hΦbd : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ‖Φ t.1 t.2.1 t.2.2‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (hfan : ∀ {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
      (_ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
        InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
          (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
      {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
      (_ : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
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
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)),
      LocalityAEOn (Real.exp κ)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => Pset m₁ i.1.1)
        (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun C u u' => agreeOn (compY
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u.1 u'.1 ∧
          ∀ y ∈ compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
            (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C,
            ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i))
        (fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
          (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
            flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
              u.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
                (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
          (u.1, hatPsiF Gp a₁ ν hG' cc F₁
            (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))))
          (rawOf D, liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) ∧
      ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
          (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
        (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
        (∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
          InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
            (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
            F₁ (s, rawOf D) = (φ, α)) ∧
        (∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
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
                (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)) ∧
        Ev = evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X)
          (fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
            (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
              flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
                u.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
                  (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
            (u.1, hatPsiF Gp a₁ ν hG' cc F₁
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)) := by
  obtain ⟨Ev, h1', h2', h3', h4', h5'⟩ := i5_functional_rel_of_fan hC
    (fun Y u u' => agreeOn Y u.1 u'.1 ∧
      ∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i))
    (fun h u u' hu => ⟨agreeOn_mono h hu.1, fun y hy i => hu.2 y (h hy) i⟩)
    (fun _ u => ⟨agreeOn_refl _ u.1, fun _ _ _ => rfl⟩) hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov
    hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb hΦan hΦbd hfan
  exact ⟨Ev, h1', fun Y u hu u' hu' ha hb => h2' Y u hu u' hu' ⟨ha, hb⟩, h3', h4', h5'⟩

/-- **The expansion engine for the sharp agreement relation, layer-constant fluctuation.**  As
`i5_functional_hat_rawY_of_fan` for the functional on `FlRealLC`; instance of
`i5_functional_relLC_of_fan`. -/
theorem i5_functional_hatLC_rawY_of_fan (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
        (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hΦbd : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ‖Φ t.1 t.2.1 t.2.2‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (hfan : ∀ {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
      (_ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
        InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
          (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
      {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
      (_ : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
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
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)),
      LocalityAEOn (Real.exp κ)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => Pset m₁ i.1.1)
        (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun C u u' => agreeOn (compY
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u.1 u'.1 ∧
          ∀ y ∈ compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
            (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C,
            ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i))
        (fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
          (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
            flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
              u.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
                (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
          (u.1, hatPsiF Gp a₁ ν hG' cc F₁
            (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))))
          (rawOf D, liftC hG' (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψh)) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        agreeOn Y u.1 u'.1 → (∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i)) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖Ev Y u‖ ≤ Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) := by
  obtain ⟨Ev, h1', h2', h3', h4'⟩ := i5_functional_relLC_of_fan hC
    (fun Y u u' => agreeOn Y u.1 u'.1 ∧
      ∀ y ∈ Y, ∀ i, u.2 (unitPt hG' y, i) = u'.2 (unitPt hG' y, i))
    (fun h u u' hu => ⟨agreeOn_mono h hu.1, fun y hy i => hu.2 y (h hy) i⟩)
    (fun _ u => ⟨agreeOn_refl _ u.1, fun _ _ _ => rfl⟩) hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hcov
    hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb hΦan hΦbd hfan
  exact ⟨Ev, h1', fun Y u hu u' hu' ha hb => h2' Y u hu u' hu' ⟨ha, hb⟩, h3', h4'⟩

end Fan

end Balaban.Localization
