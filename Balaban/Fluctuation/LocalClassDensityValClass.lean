/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityValFamily

/-!
# The datum-indexed coefficient family of `ℰ₁^{(k+1)}` for a general class (blocker 6, item (1))

For a class member `C` the Theorem 3.1 (a) expansion of `ℰ₁^{(k+1)}(z)` is run at every datum `Θ`
of the chart with one activity family `A Θ` (the label sum of the class exponent `W₁^C`) and one
family of marks indexed by `ι₀ ⊕ ι₁`: the marks `G₀ Θ` of the zero class (the derivative of
`W₁^0`) and marks `G₁ Θ` of the inherited energy (the derivative of `ℰ_k`).

`classE1Family_of_marks`: if `(A, G₀ ⊕ G₁)` is a `ParamMarkFamily` over the parameters `physV`
of the chart, with the block dependence and holomorphy in the interpolation variable at every
parameter, locality of the activities and marks on the sites of `T`, the root cube in every mark
label, the numerical hypotheses of Theorem 3.4, and the three value identities at every chart datum
(activity, zero marks, inherited marks), then the coefficients
`c Θ T = gsumCoeff μ Lab (A Θ) (y0 ⊕ y1) (G₀ Θ ⊕ G₁ Θ) T` are analytic on `physV`, equal at two
parameters whose `(raw datum, source)` agree on `sitesOf T`, bounded by
`C_PE (∑ F0 e^{-κ₀ 𝗱} + ∑ F1 e^{-κ₀ 𝗱}) e^{-κ' d_Ext T}`, non-zero only on rooted polymer sets with
`d_Ext T = sizeJ`, and `ℰ₁^{(k+1)}(z)` at the raw datum of every chart datum `D` (any field) is
`∑_T c (rawOf D, 0) T`.  The old densities `ℰ^{(j)}` are required to be analytic at the composed
pairs of the path (`hE`), which gives the split of the derivative of `W₁^C`.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer Matrix Filter Topology MeasureTheory

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)

/-- The raw datum of a chart datum lies in the admissible parameters (with zero source). -/
theorem rawOf_zero_mem_physV {D : BgData S.G' N} (hX : XiCData S.G' S.a S.ν (k + 1) 1 eps D) :
    ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
      (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) ∈ physV S S.a₁ S.ν eps :=
  ⟨⟨D, hX, rfl⟩, by
    change (∑ x : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N, ‖(0 : ℂ)‖) < 1
    simp⟩

open Classical in
/-- **The coefficient family of `ℰ₁^{(k+1)}` of a class member at every chart datum.**  See the
module doc-string. -/
theorem classE1Family_of_marks {m₀ : ℕ} (hp : 0 < S.p₁) (hle : S.p₁ ≤ pp)
    {Lb : Type} [Fintype Lb]
    (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ Lb)
    (hN : L ^ m₀ ∣ N₁)
    {ι₀ ι₁ : Type} [Fintype ι₀] [Fintype ι₁] (hι₀ : Nonempty ι₀) (y0 : ι₀ → Lb) (y1 : ι₁ → Lb)
    {εH κH κG κ0 κ' Kc : ℝ} (F0 : ι₀ → ℝ) (F1 : ι₁ → ℝ)
    {𝒰 : Set ℂ} {Q : Set (∀ b, (S.blockSplit m₀ hp).Ωb b)}
    (A : physParam N S → ℂ → LabelAct Lab (S.blockSplit m₀ hp).Ωb εH κH κ0 Kc)
    (G₀ : physParam N S → ι₀ → ℂ → (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ)
    (G₁ : physParam N S → ι₁ → ℂ → (∀ b, (S.blockSplit m₀ hp).Ωb b) → ℂ)
    (hfam : ParamMarkFamily (S.blockSplit m₀ hp).μ Lab A (Sum.elim y0 y1)
      (fun θ => Sum.elim (G₀ θ) (G₁ θ)) κG (Sum.elim F0 F1) (physV S S.a₁ S.ν eps) 𝒰 Q)
    (hdep₀ : ∀ θ i u, DepOn (blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y0 i))) (G₀ θ i u))
    (hdep₁ : ∀ θ j u, DepOn (blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y1 j))) (G₁ θ j u))
    (holA : ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ y Φ,
      DifferentiableOn ℂ (fun u => (A θ u).H y Φ) 𝒰)
    (holG₀ : ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ i Φ, DifferentiableOn ℂ (fun u => G₀ θ i u Φ) 𝒰)
    (holG₁ : ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ j Φ, DifferentiableOn ℂ (fun u => G₁ θ j u Φ) 𝒰)
    (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 + 1 ≤ Kc) (hεpos : 0 < εH)
    (hF0 : ∀ i, 0 < F0 i) (hF1 : ∀ j, 0 < F1 j) (hκ' : 0 ≤ κ') (hκG : κH ≤ κG)
    (hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH)
    (hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
      Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L)))
    (z : RootIdx d L N₁ m₁ (k + 1))
    (hroot₀ : ∀ i, rootCube (m₀ := m₀) z ∈ blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y0 i)))
    (hroot₁ : ∀ j, rootCube (m₀ := m₀) z ∈ blocksOf m₀ (k + 1) Set.univ (Lab.ysite (y1 j)))
    (hAloc : ∀ T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ), ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ θ' ∈ physV S S.a₁ S.ν eps,
      physRestrict (N := N) (sitesOf T) (physIncl N S θ) =
        physRestrict (sitesOf T) (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ y, Lab.ysite y ⊆ Yhat Set.univ (sitesOf T) →
        (A θ (s : ℂ)).H y = (A θ' (s : ℂ)).H y)
    (hG₀loc : ∀ T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ), ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ θ' ∈ physV S S.a₁ S.ν eps,
      physRestrict (N := N) (sitesOf T) (physIncl N S θ) =
        physRestrict (sitesOf T) (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ i, Lab.ysite (y0 i) ⊆ Yhat Set.univ (sitesOf T) →
        G₀ θ i (s : ℂ) = G₀ θ' i (s : ℂ))
    (hG₁loc : ∀ T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ), ∀ θ ∈ physV S S.a₁ S.ν eps, ∀ θ' ∈ physV S S.a₁ S.ν eps,
      physRestrict (N := N) (sitesOf T) (physIncl N S θ) =
        physRestrict (sitesOf T) (physIncl N S θ') →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ j, Lab.ysite (y1 j) ⊆ Yhat Set.univ (sitesOf T) →
        G₁ θ j (s : ℂ) = G₁ θ' j (s : ℂ))
    (hE : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x : S.E, ‖x‖ ≤ S.p₁ → ∀ j ∈ Finset.Icc 1 k,
      AnalyticAt ℂ
        (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N => Edens C.m₀ C.Tm j p.1 p.2)
        (Jr.PJ j (rawOf D, (s : ℂ) • yhat x)))
    (hW : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
        Jr.W1 C (rawOf D, (s : ℂ) • yhat x) =
          ∑ y, (A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) (s : ℂ)).H y
            ((S.blockSplit m₀ hp).restr x))
    (hF₀ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : S.E, ‖x‖ ≤ S.p₁ →
        ∑ i, G₀ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) i (s : ℂ)
            ((S.blockSplit m₀ hp).restr x) =
          (fderiv ℂ (fun w : S.EC => Jr.W1 (zeroClass d L N₁ m₁ k N ϱ) (rawOf D, w))
            ((s : ℂ) • yhat x))
            ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)))
    (hF₁ : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
        (fderiv ℂ (fun w : S.EC => Jr.EJ C (rawOf D, w)) ((s : ℂ) • yhat x))
            ((Jr.Mx (rawOf D))⁻¹ *ᵥ S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)) =
          ∑ j, G₁ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) j (s : ℂ)
            ((S.blockSplit m₀ hp).restr x)) :
    (∀ T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ),
      AnalyticOnNhd ℂ (fun θ => gsumCoeff (S.blockSplit m₀ hp).μ Lab (A θ) (Sum.elim y0 y1)
          (Sum.elim (G₀ θ) (G₁ θ)) T) (physV S S.a₁ S.ν eps) ∧
        (∀ θ ∈ physV S S.a₁ S.ν eps, ∀ θ' ∈ physV S S.a₁ S.ν eps,
          physRestrict (N := N) (sitesOf T) (physIncl N S θ) =
            physRestrict (sitesOf T) (physIncl N S θ') →
          gsumCoeff (S.blockSplit m₀ hp).μ Lab (A θ) (Sum.elim y0 y1) (Sum.elim (G₀ θ) (G₁ θ)) T =
            gsumCoeff (S.blockSplit m₀ hp).μ Lab (A θ') (Sum.elim y0 y1)
              (Sum.elim (G₀ θ') (G₁ θ')) T) ∧
        (∀ θ ∈ physV S S.a₁ S.ν eps,
          ‖gsumCoeff (S.blockSplit m₀ hp).μ Lab (A θ) (Sum.elim y0 y1)
              (Sum.elim (G₀ θ) (G₁ θ)) T‖ ≤
            CPE d L Kc κH κ0 κ' * ((∑ i, F0 i * Real.exp (-κ0 * Lab.dl (y0 i))) +
              ∑ j, F1 j * Real.exp (-κ0 * Lab.dl (y1 j))) * Real.exp (-κ' * dExt T)) ∧
        (∀ θ, gsumCoeff (S.blockSplit m₀ hp).μ Lab (A θ) (Sum.elim y0 y1)
            (Sum.elim (G₀ θ) (G₁ θ)) T ≠ 0 →
          rootCube (m₀ := m₀) z ∈ T ∧ IsPolyDom m₀ (k + 1) (sitesOf T) ∧
            dExt T = sizeJ m₀ (k + 1) (sitesOf T))) ∧
      ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
        Jr.E1locJ C z (rawOf D) = ∑ T, gsumCoeff (S.blockSplit m₀ hp).μ Lab
          (A ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))) (Sum.elim y0 y1)
          (Sum.elim (G₀ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
            (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
            (G₁ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
              (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))) T := by
  have hι : Nonempty (ι₀ ⊕ ι₁) := hι₀.elim fun i => ⟨Sum.inl i⟩
  have hF01 : ∀ i, 0 < Sum.elim F0 F1 i := fun i => by
    cases i with
    | inl i => exact hF0 i
    | inr j => exact hF1 j
  have hdep : ∀ θ i u, DepOn (blocksOf m₀ (k + 1) Set.univ (Lab.ysite (Sum.elim y0 y1 i)))
      (Sum.elim (G₀ θ) (G₁ θ) i u) := fun θ i u => by
    cases i with
    | inl i => exact hdep₀ θ i u
    | inr j => exact hdep₁ θ j u
  have hroot : ∀ i, rootCube (m₀ := m₀) z ∈
      blocksOf m₀ (k + 1) Set.univ (Lab.ysite (Sum.elim y0 y1 i)) := fun i => by
    cases i with
    | inl i => exact hroot₀ i
    | inr j => exact hroot₁ j
  refine ⟨fun T => ?_, fun D hX => ?_⟩
  · have hmain := paramMarked_analytic_local_bound (m₀ := m₀) (j := k + 1) (Ω := Set.univ)
      (S.blockSplit m₀ hp).μ hN le_rfl isPiUnion_univ_K hfam hdep hκ0 hKc hεpos hι hF01 hκ' hκG
      hκ hε T (fun θ => physRestrict (N := N) (sitesOf T) (physIncl N S θ))
      (fun θ hθ θ' hθ' h s hs y hy => hAloc T θ hθ θ' hθ' h s hs y hy)
      (fun θ hθ θ' hθ' h s hs i hi => by
        cases i with
        | inl i => exact hG₀loc T θ hθ θ' hθ' h s hs i hi
        | inr j => exact hG₁loc T θ hθ θ' hθ' h s hs j hi)
    refine ⟨hmain.1, hmain.2.1, fun θ hθ => ?_, fun θ hne => ?_⟩
    · have hb := hmain.2.2 θ hθ
      rw [Fintype.sum_sum_type] at hb
      exact hb
    · exact ⟨mem_of_gsumCoeff_ne_zero_of_labels hN (S.blockSplit m₀ hp).μ (A θ) _ _
          (hfam.meas θ) (hdep θ) (hfam.bound θ) hκ0 hKc hεpos hF01 hκ' hκG hκ hε hroot hne,
        (gsumCoeff_ne_zero_active hN (S.blockSplit m₀ hp).μ (A θ) _ _ (hfam.meas θ) (hdep θ)
          (hfam.bound θ) hκ0 hKc hεpos hF01 hκ' hκG hκ hε hne).2⟩
  · have hθ := rawOf_zero_mem_physV hX
    refine Jr.E1locJ_eq_sum_gsumCoeff_of_marks C hp Lab hι (Sum.elim y0 y1) hN hfam.isOpenU
      hfam.seg _ _ (hfam.meas _) (hdep _) (hfam.bound _) (holA _ hθ) (fun i Φ => ?_) hκ0 hKc
      hεpos hF01 hκ' hκG hκ hε z (rawOf D) (hW D hX) (fun s hs => ?_)
    · cases i with
      | inl i => exact holG₀ _ hθ i Φ
      | inr j => exact holG₁ _ hθ j Φ
    · filter_upwards [S.ae_ball hp, hF₁ D hX s hs] with x hx h1
      have hxn : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp x).1 hx
      refine (Jr.fderiv_W1_eq_sum_elim C ⟨D, hX, rfl⟩
        (smul_yhat_le (S := S) (S.abs_mul_le_of_mem hle hs hxn.le)) (hE D hX s hs x hxn.le) _
        _ _ (hF₀ D hX s hs x hxn.le).symm h1).trans (Finset.sum_congr rfl fun i _ => ?_)
      cases i <;> rfl

end Balaban.Fluctuation.StepSetting.JointRep

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)

open Classical in
/-- **The input `hval` at one root on the whole class domain**: if at the root `z` the
representative `E0locJ z` is the sum of a cube-set family `e` at the raw datum of every datum of the
chart (any field), then at every pair `q` of the class domain `Ξ^c_{k+1}(𝔹; 1, ε)`, `ε ≤ eps`, the
density at the root site of `z` is the sum of the family at the cut-off of `q`.  (The landed
`densE0_rootSite_eq_sum`, applied to the family equal to `e` at `z` and to the one-term family
`E0locJ` at the other roots.) -/
theorem densE0_rootSite_eq_sum_of_root {m₀ : ℕ} (z : RootIdx d L N₁ m₁ (k + 1))
    (e : physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ)
    (hval : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      Jr.E0locJ C z (rawOf D) = ∑ T, e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), 0) T)
    {ε : ℝ} (hε : ε ≤ eps) {q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hq : XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2) :
    Jr.densE0 C (rootSite z) q = ∑ T,
      (if h : clipRaw S.G' q ∈ rawSub N S.G' then e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), 0) T
        else 0) := by
  let e' : RootIdx d L N₁ m₁ (k + 1) → physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ := fun z' θ T =>
    if z' = z then e θ T else if T = ∅ then Jr.E0locJ C z' (θ.1 : RawData d L (N₁ * L ^ m₁)
      (k + 1) N) else 0
  have hval' : ∀ z' (D : BgData S.G' N), XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      Jr.E0locJ C z' (rawOf D) =
        ∑ T, e' z' ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), 0) T := by
    intro z' D hD
    by_cases hz : z' = z
    · subst hz
      simp only [e', ite_true]
      exact hval D hD
    · simp only [e', hz, ite_false]
      rw [Finset.sum_ite_eq' Finset.univ (∅ : Finset (CubeB (d := d) (L := L) (N₁ := N₁)
        (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ))]
      simp only [Finset.mem_univ, ite_true]
  have h := Jr.densE0_rootSite_eq_sum C e' hval' hε hq z
  simpa only [e', ite_true] using h

end Balaban.Fluctuation.StepSetting.JointRep
