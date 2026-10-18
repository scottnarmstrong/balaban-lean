/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityFamilyRoot

/-!
# The marks family of the inherited energy of a class (`LocalClassDensityFamilyMarks`)

The family `G₁` of (M2) (`e0CoeffFamily_class_fromTower`) for a class with inherited labels: for a
finite family of labels `τ` (degree `jL τ`, site `yL τ`, domain `XL τ`) with their settings and
given maps (`exists_classOldLabel_maps`), a root `z`, the clamp radius `ρ` and a disc `‖u‖ < a` of
first marks, the index set is the set of rooted pairs `markedIdx` of the label domains, and the mark
of a pair `q = (τ, Y)` is, at a parameter `θ` whose raw datum lies in the chart and `‖u‖ < a`,

  `G₁ θ q u Φ = β ∂_t|₀ evDec … Eτ … (blockU z) u t Y (θ.1, S.hatOf 1 ρ hp Φ)`

(the block index `1` of (M2)), and `0` otherwise (the hypothesis `hG₁` gives `G₁` by this formula).

* `classMarksFamily_fields`: the fields of the marks: measurable, depending only on the blocks of
  the bridge label `bridge 1 z Y` (a domain of `𝒟_{k+1}` for the index `1` containing the root
  cube), bounded by `|β| β⁻¹ E₀ e^{-κ₀ d(X) - 2κ_dec d(Y)} / b` for every parameter, mark and
  configuration, analytic in `(θ, u)` on `physV × {‖u‖ < a}` (the field `holG` of
  `ParamMarkFamily`), continuous in the configuration and holomorphic in `u` there.
* `StepSetting.JointRep.classMarksFamily_sum_eq_deriv`: **the sum identity of the marks at every
  datum of the chart**: for `s ∈ [0, 1]`, `1 < a` and a real field `x` with `|x(u)| ≤ ρ < p⁺`,
  the sum of the marks at `(rawOf D, 0)`, `s` and the block configuration of `x` is the sum over
  the labels of the derivatives at `0` of `t ↦ ℰ^{(j)}(y, X; Jr.PJ j (rawOf D, s ψ̂ + t v_z))`
  (`deriv_classLabel_PJ_eq_sum_marked_joint_of` label by label; the pairs left out of `markedIdx`
  contribute zero, `classOldMarkedLocal_rootedMarks_of`).

The locality of the marks in the parameter is `classMarksFamily_local`
(`LocalClassDensityFamilyLocal`), the identity (M2) with the Fréchet derivative of `ℰ_k` is
`classMarksFamily_ae_fderiv_eq_sum` (`LocalClassDensityFamilyDeriv`).  Not treated: the bound in the
form `F1 j e^{-(2κ_dec - 1) 𝗱(y1 j)}` with the decay of `F1` in the label size (the comparison of
`d^cov_{C.m₀}(Y)` with `𝗱` of the bridge label at the block index `1`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Balaban.SmallField.GsSpec Balaban.Analysis Balaban.Polymer Finset Matrix

section Family

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable (S : StepSetting d L N₁ m₁ k N ϱ) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

open Classical in
/-- **The fields of the marks family, with the label charts replaced by any sets containing the
composed step data** (`h𝒮`).  `classMarksFamily_fields_gen` is the case of the label charts. -/
theorem classMarksFamily_fields_gen_onSet {ι : Type*} [Fintype ι]
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
    (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂)
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hG : IsLevel Hm k) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {𝒮 : ι → Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (𝒮 τ))
    (hEbd : ∀ τ, ∀ r ∈ 𝒮 τ,
      ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat Hm N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small Hm (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L a₁) ν (bgC0 d L N) D))
    (hN : L ^ m₀ ∣ N₁) (hm1 : 1 ≤ m₀) (hd : 3 ≤ d) (hL : 2 ≤ L)
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {a bb : ℝ} (ha : 0 ≤ a) (hbb : 0 < bb)
    (hab : (a + bb) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ∧ ‖u‖ < a then
        (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) a₁ ν S.hG'
          cc (F₁ q.1.1) (Sol q.1.1)
          (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) Hm (compWeight L a₁)
            (Fk q.1.1)
            (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
          (S.blockU z) u t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
      else 0)
    (h𝒮 : ∀ τ, ∀ t ∈ FlRealLC S.G' Hm a₁ ν BG κ eps (X₁f τ) BG₂ δ₁,
      D2raw (Gk τ) (Gj τ) (compWeight L a₁) (Fk τ)
        (d1Triple S.G' (Gk τ) Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2) ∈ 𝒮 τ) :
    (∀ θ q u, Measurable (G₁ θ q u)) ∧
    (∀ θ (q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z}) u,
      DepOn (blocksOf 1 (k + 1) Set.univ (bridge 1 z q.1.2)) (G₁ θ q u)) ∧
    (∀ θ (q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z}) u Φ,
      ‖G₁ θ q u Φ‖ ≤ ‖(S.β : ℂ)‖ * ((S.β⁻¹ * Bτ q.1.1) *
      Real.exp (-κ₀ * treeLenCovOne m₀ (jL q.1.1) (XL q.1.1) -
        2 * κdec * treeLenCov S.G' m₀ q.1.2) / bb)) ∧
    (∀ q Φ, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => G₁ r.1 q r.2 Φ)
      (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
    (∀ q, ∀ θ ∈ physV S a₁ ν eps, ∀ u ∈ Metric.ball (0 : ℂ) a, Continuous (G₁ θ q u)) ∧
    (∀ θ ∈ physV S a₁ ν eps, ∀ q Φ,
      DifferentiableOn ℂ (fun u => G₁ θ q u Φ) (Metric.ball (0 : ℂ) a)) ∧
    (∀ q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z}, IsDj 1 (k + 1) (bridge 1 z q.1.2) ∧
      rootCube (m₀ := 1) z ∈ blocksOf 1 (k + 1) Set.univ (bridge 1 z q.1.2)) := by
  classical
  set CHr := XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps with hCHr
  -- the per-label block marks and rooted marks
  have hBM := fun τ => classOldMarkedLocal_blockMarks_gen_onSet (h𝒮 := h𝒮 τ)
      S hb₁ hbC (Eτ τ) (hBτ τ) hβ (hB τ)
    (hF τ) hG cc hcψ hMX hdm hα hsm (hcov τ) (hX₁ τ) hconn hrow (hopt τ) hκ₀ hκdec hκ h1 hlog
    (hEan τ) (hEbd τ) (hF₁an τ) (hF₁ τ) (hSolan τ) (hSolprop τ) (hFkan τ) (hFk τ) (S.blockU z) 1
    hρ hρc hp
  have hmemq : ∀ q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z},
      q.1.2 ∈ polyDom S.G' (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) ∧
        (psiThick q.1.2 ∩ fineBlock z).Nonempty := by
    intro q
    have hq : (q.1.1, q.1.2) ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z := q.2
    obtain ⟨h1, -, h3⟩ := mem_markedIdx.1 hq
    exact ⟨h1, h3⟩
  have hRT := fun (q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z}) =>
    (classOldMarkedLocal_rootedMarks_gen_onSet (h𝒮 := h𝒮 q.1.1)
      S hb₁ hbC (Eτ q.1.1) (hBτ q.1.1) hβ (hB q.1.1)
      (hF q.1.1) hG cc hcψ hMX hdm hα hsm (hcov q.1.1) (hX₁ q.1.1) hconn hrow (hopt q.1.1) hκ₀
      hκdec hκ h1 hlog (hEan q.1.1) (hEbd q.1.1) (hF₁an q.1.1) (hF₁ q.1.1) (hSolan q.1.1)
      (hSolprop q.1.1) (hFkan q.1.1) (hFk q.1.1) hN hm1 hd hL z hρ hρc hp (hmemq q).1).1 (hmemq q).2
  have hum : ∀ q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z}, ∀ u : ℂ, ‖u‖ < a →
      (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ := fun q u hu =>
    mem_markedRadiusSet_of_pos (flCore_of (hB q.1.1) (hF q.1.1)).δ₁_pos hab hu.le
      (by rw [norm_zero]; exact hbb.le)
  have hpos : ∀ θ u, (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖u‖ < a →
      ∀ q, G₁ θ q u = fun Φ => (S.β : ℂ) *
        deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) a₁ ν
          S.hG' cc (F₁ q.1.1) (Sol q.1.1)
          (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) Hm (compWeight L a₁)
            (Fk q.1.1) (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
          (S.blockU z) u t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0 :=
      fun θ u hc q => by
    funext Φ
    rw [hG₁, ite_eq_left hc]
  have hneg : ∀ θ u, ¬ ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖u‖ < a) →
      ∀ q, G₁ θ q u = fun _ => 0 := fun θ u hc q => by
    funext Φ
    rw [hG₁, ite_eq_right hc]
  have hholG : ∀ q Φ, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => G₁ r.1 q r.2 Φ)
      (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a) := by
    intro q Φ
    have hexpr := (hBM q.1.1).2.2.2 q.1.2 Φ a bb ha hbb hab
    refine ((analyticOnNhd_const (v := (S.β : ℂ))).mul hexpr).congr
      ((isOpen_physV S a₁ ν eps (hB q.1.1).HBp).prod Metric.isOpen_ball) ?_
    intro r hr
    have hc : (r.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖r.2‖ < a :=
      ⟨hr.1.1, mem_ball_zero_iff.1 hr.2⟩
    show _ = G₁ r.1 q r.2 Φ
    rw [hpos r.1 r.2 hc q]
  refine ⟨?_, ?_, ?_, hholG, ?_, ?_, ?_⟩
  · intro θ q u
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖u‖ < a
    · rw [hpos θ u hc q]
      exact ((hBM q.1.1).2.1 q.1.2 _ hc.1 u (hum q u hc.2)).2.const_mul _
    · rw [hneg θ u hc q]
      exact measurable_const
  · intro θ q u
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖u‖ < a
    · rw [hpos θ u hc q]
      intro Φ Φ' h
      exact congrArg (fun w => (S.β : ℂ) * w) ((hRT q).2.2.2.2 _ hc.1 u (hum q u hc.2) Φ Φ' h)
    · rw [hneg θ u hc q]
      intro Φ Φ' _
      rfl
  · intro θ q u Φ
    by_cases hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖u‖ < a
    · rw [hpos θ u hc q, norm_mul]
      exact mul_le_mul_of_nonneg_left
        ((hBM q.1.1).2.2.1 q.1.2 _ hc.1 a bb bb ha hbb.le hbb le_rfl hab u hc.2.le Φ)
        (norm_nonneg _)
    · rw [hneg θ u hc q, norm_zero]
      exact mul_nonneg (norm_nonneg _) (div_nonneg (mul_nonneg (mul_nonneg
        (inv_nonneg.2 hβ.le) (hBτ q.1.1)) (Real.exp_pos _).le) hbb.le)
  · intro q θ hθ u hu
    have hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈ CHr ∧ ‖u‖ < a :=
      ⟨hθ.1, mem_ball_zero_iff.1 hu⟩
    rw [hpos θ u hc q]
    exact continuous_const.mul ((hBM q.1.1).2.1 q.1.2 _ hc.1 u (hum q u hc.2)).1
  · intro θ hθ q Φ
    refine AnalyticOnNhd.differentiableOn ?_
    exact (hholG q Φ).comp (f := fun u : ℂ => (θ, u))
      (fun _ _ => analyticAt_const.prod analyticAt_id) (fun u hu => ⟨hθ, hu⟩)
  · intro q
    exact ⟨(hRT q).1, (hRT q).2.2.1⟩

open Classical in
/-- **The fields of the marks family of the inherited energy.**  For a finite family of labels of
the class `C` with their settings, given maps and the hypotheses of
`classOldMarkedLocal_rootedMarks_of`, a root `z`, a clamp radius `0 < ρ ≤ c_ψ` and radii `a ≥ 0`,
`b > 0` with `(a + b) · markedRad < δ₁`, the marks `G₁` of the rooted pairs `q = (τ, Y)` of
`markedIdx` (given by `hG₁`) are measurable, depend only on the blocks of `bridge 1 z Y`, are
bounded by `|β| β⁻¹ E₀ e^{-κ₀ d(X) - 2κ_dec d(Y)} / b`, are analytic in `(θ, u)` on
`physV × {‖u‖ < a}`, are continuous in the configuration and holomorphic in `u` for
`θ ∈ physV`, and the bridge label is a domain of `𝒟_{k+1}` (index `1`) containing the root
cube. -/
theorem classMarksFamily_fields_gen {ι : Type*} [Fintype ι]
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
    (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂)
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hG : IsLevel Hm k) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (XiCRaw (Gj τ) (compWeight L a₁) ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ XiCRaw (Gj τ) (compWeight L a₁) ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat Hm N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small Hm (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L a₁) ν (bgC0 d L N) D))
    (hN : L ^ m₀ ∣ N₁) (hm1 : 1 ≤ m₀) (hd : 3 ≤ d) (hL : 2 ≤ L)
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {a bb : ℝ} (ha : 0 ≤ a) (hbb : 0 < bb)
    (hab : (a + bb) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ∧ ‖u‖ < a then
        (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) a₁ ν S.hG'
          cc (F₁ q.1.1) (Sol q.1.1)
          (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) Hm (compWeight L a₁)
            (Fk q.1.1)
            (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
          (S.blockU z) u t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
      else 0) :
    (∀ θ q u, Measurable (G₁ θ q u)) ∧
    (∀ θ (q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z}) u,
      DepOn (blocksOf 1 (k + 1) Set.univ (bridge 1 z q.1.2)) (G₁ θ q u)) ∧
    (∀ θ (q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z}) u Φ,
      ‖G₁ θ q u Φ‖ ≤ ‖(S.β : ℂ)‖ * ((S.β⁻¹ * Bτ q.1.1) *
      Real.exp (-κ₀ * treeLenCovOne m₀ (jL q.1.1) (XL q.1.1) -
        2 * κdec * treeLenCov S.G' m₀ q.1.2) / bb)) ∧
    (∀ q Φ, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => G₁ r.1 q r.2 Φ)
      (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
    (∀ q, ∀ θ ∈ physV S a₁ ν eps, ∀ u ∈ Metric.ball (0 : ℂ) a, Continuous (G₁ θ q u)) ∧
    (∀ θ ∈ physV S a₁ ν eps, ∀ q Φ,
      DifferentiableOn ℂ (fun u => G₁ θ q u Φ) (Metric.ball (0 : ℂ) a)) ∧
    (∀ q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z}, IsDj 1 (k + 1) (bridge 1 z q.1.2) ∧
      rootCube (m₀ := 1) z ∈ blocksOf 1 (k + 1) Set.univ (bridge 1 z q.1.2)) :=
  classMarksFamily_fields_gen_onSet S hb₁ hbC Eτ Bτ hBτ hβ jL XL Gk Gj X₀ X₁f 𝒦X hB hF hG cc hcψ hMX
    hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁ hF₁an hF₁ Sol hSolan
    hSolprop Fk hFkan hFk hN hm1 hd hL z hρ hρc hp ha hbb hab G₁ hG₁
    (fun τ _ ht => d2raw_d1Triple_mem_xiCRaw hb₁ hbC (hB τ) (hF τ) (hFk τ) ht)

open Classical in
/-- **The fields of the marks family of the inherited energy.**  For a finite family of labels of
the class `C` with their settings, given maps and the hypotheses of
`classOldMarkedLocal_rootedMarks_of`, a root `z`, a clamp radius `0 < ρ ≤ c_ψ` and radii `a ≥ 0`,
`b > 0` with `(a + b) · markedRad < δ₁`, the marks `G₁` of the rooted pairs `q = (τ, Y)` of
`markedIdx` (given by `hG₁`) are measurable, depend only on the blocks of `bridge 1 z Y`, are
bounded by `|β| β⁻¹ E₀ e^{-κ₀ d(X) - 2κ_dec d(Y)} / b`, are analytic in `(θ, u)` on
`physV × {‖u‖ < a}`, are continuous in the configuration and holomorphic in `u` for
`θ ∈ physV`, and the bridge label is a domain of `𝒟_{k+1}` (index `1`) containing the root
cube. -/
theorem classMarksFamily_fields {ι : Type*} [Fintype ι]
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    (hβ : 0 < S.β) (hE₀ : 0 ≤ P.E₀)
    (jL : ι → ℕ) (yL : ι → CTorus d L N₁ m₁ (k + 1)) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k) (hXp : ∀ τ, IsPolyDom C.m₀ (jL τ) (XL τ))
    (hy : ∀ τ, yL τ ∈ XL τ)
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (C.Tm.gs (jL τ) (XL τ)) a₁ ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl (X₁f τ))
    (hG : IsLevel Hm k) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' C.m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' C.m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L C.m₀ m₁ (jL τ)) E₀ = treeLenCovOne C.m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ τ, ∀ r ∈ XiCRaw (C.Tm.gs (jL τ) (XL τ)) (compWeight L a₁) ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom (jL τ) (C.Tm.gs (jL τ) (XL τ)) r.1 r.2)
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat Hm N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi Hm (Dec2.decG (coverOf S.G') Hm (compWeight L a₁) ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small Hm (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L a₁) ν (bgC0 d L N) D))
    (hN : L ^ C.m₀ ∣ N₁) (hm1 : 1 ≤ C.m₀) (hd : 3 ≤ d) (hL : 2 ≤ L)
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hp : 0 < S.p₁)
    {a bb : ℝ} (ha : 0 ≤ a) (hbb : 0 < bb)
    (hab : (a + bb) * markedRad d L N k a₁ κ cψ cc < δ₁)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ∧ ‖u‖ < a then
        (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) C.m₀ (jL q.1.1) (𝒦X q.1.1) a₁ ν S.hG'
          cc (F₁ q.1.1) (Sol q.1.1)
          (eTermFun S.G' (Gk q.1.1) (C.Tm.gs (jL q.1.1) (XL q.1.1)) Hm (compWeight L a₁)
            (Fk q.1.1)
            (fun r => (S.β : ℂ)⁻¹ * C.Tm.E (jL q.1.1) (yL q.1.1) (XL q.1.1) r.1 r.2))
          (S.blockU z) u t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
      else 0) :
    (∀ θ q u, Measurable (G₁ θ q u)) ∧
    (∀ θ (q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ)) z}) u,
      DepOn (blocksOf 1 (k + 1) Set.univ (bridge 1 z q.1.2)) (G₁ θ q u)) ∧
    (∀ θ (q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ)) z}) u Φ,
      ‖G₁ θ q u Φ‖ ≤ ‖(S.β : ℂ)‖ * ((S.β⁻¹ * P.E₀) *
      Real.exp (-κ₀ * treeLenCovOne C.m₀ (jL q.1.1) (XL q.1.1) -
        2 * κdec * treeLenCov S.G' C.m₀ q.1.2) / bb)) ∧
    (∀ q Φ, AnalyticOnNhd ℂ (fun r : physParam N S × ℂ => G₁ r.1 q r.2 Φ)
      (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
    (∀ q, ∀ θ ∈ physV S a₁ ν eps, ∀ u ∈ Metric.ball (0 : ℂ) a, Continuous (G₁ θ q u)) ∧
    (∀ θ ∈ physV S a₁ ν eps, ∀ q Φ,
      DifferentiableOn ℂ (fun u => G₁ θ q u Φ) (Metric.ball (0 : ℂ) a)) ∧
    (∀ q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ)) z}, IsDj 1 (k + 1) (bridge 1 z q.1.2) ∧
      rootCube (m₀ := 1) z ∈ blocksOf 1 (k + 1) Set.univ (bridge 1 z q.1.2)) := by
  have hraw := fun τ => classOldEnergy_chart_radius_raw (N := N) (b := b) C hm hcl hκP hE₀ a₁ ν
    δ₃ eps δfl (hj1 τ) (hjk τ) (hXp τ) (hy τ) (hchart τ)
  exact classMarksFamily_fields_gen S hb₁ hbC
    (fun τ r => C.Tm.E (jL τ) (yL τ) (XL τ) r.1 r.2) (fun _ => P.E₀) (fun _ => hE₀) hβ jL XL Gk
    (fun τ => C.Tm.gs (jL τ) (XL τ)) X₀ X₁f 𝒦X hB hF hG cc hcψ hMX hdm hα hsm hcov hX₁ hconn hrow
    hopt hκ₀ hκdec hκ h1 hlog (fun τ => (hraw τ).1) (fun τ => (hraw τ).2) F₁ hF₁an hF₁ Sol hSolan
    hSolprop Fk hFkan hFk hN hm1 hd hL z hρ hρc hp ha hbb hab G₁ hG₁

end Family

section FamilyIdentity

namespace StepSetting.JointRep

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ₁ ϱ₂ : ℝ}
variable {S : StepSetting d L N₁ m₁ k N ϱ} {eps pp : ℝ} (Jr : S.JointRep eps pp)
  {c BG κ r₀ δ₃ Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

open Classical in
/-- **The sum identity of the marks family, with the label charts replaced by any sets containing
the composed step data** (`h𝒮`).  `classMarksFamily_sum_eq_deriv_gen` is the case of the label
charts. -/
theorem classMarksFamily_sum_eq_deriv_gen_onSet {ι : Type*} [Fintype ι]
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
    (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k)
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (hlocE : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
      Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂
      δ₁ δfl (X₁f τ))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {𝒮 : ι → Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (𝒮 τ))
    (hEbd : ∀ τ, ∀ r ∈ 𝒮 τ,
      ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N → ((stepG d L N₁ m₁ k
        ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi (stepG d L N₁ m₁ k ϱ) (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ
              p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N
            (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
              p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' =
                (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
    (hS : ∀ τ, GsSpecStrong (jL τ) ((hjk τ).trans (Nat.le_succ k)) (XL τ)
      (Gj τ))
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hN : L ^ m₀ ∣ N₁) (hm1 : 1 ≤ m₀) (hd : 3 ≤ d) (hL : 2 ≤ L)
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 < bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
          S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1.1) (Sol q.1.1)
          (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) (Fk q.1.1)
            (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
          (S.blockU z) u t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
      else 0)
    (h𝒮 : ∀ τ, ∀ t ∈ FlRealLC S.G' (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν BG κ eps (X₁f τ) BG₂ δ₁,
      D2raw (Gk τ) (Gj τ) (compWeight L S.a₁) (Fk τ)
        (d1Triple S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) t.1.1 t.2.1 t.2.2) ∈ 𝒮 τ) :
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : S.E, (∀ u, ‖x u‖ ≤ ρ) →
      ∑ q, G₁ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) q (s : ℂ) ((S.blockSplit 1 hp).restr x) =
        ∑ τ, deriv (fun t : ℂ => Eτ τ (Jr.PJ (jL τ) (rawOf D, (s : ℂ) • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
            S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))))) 0 := by
  classical
  intro D hD s hs x hx
  have hΘ : rawOf D ∈ XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps := ⟨D, hD, rfl⟩
  have hsn : ‖(s : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
  have hca : ‖(s : ℂ)‖ < a := lt_of_le_of_lt hsn ha1
  have hhat : S.hatOf 1 ρ hp ((S.blockSplit 1 hp).restr x) = yhat x := S.hatOf_restr 1 hρ hp x hx
  have hyρ : ∀ p, ‖yhat x p‖ ≤ ρ := fun p => by
    show ‖((x p.1 p.2 : ℝ) : ℂ)‖ ≤ ρ
    rw [Complex.norm_real]
    exact (PiLp.norm_apply_le (x p.1) p.2).trans (hx p.1)
  have hyx : ∀ p, ‖yhat x p‖ ≤ cψ := fun p => (hyρ p).trans hρc
  have hspp : ∀ p, ‖((s : ℂ) • yhat x) p‖ < pp := fun p => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    calc ‖(s : ℂ)‖ * ‖yhat x p‖ ≤ 1 * ρ :=
          mul_le_mul hsn (hyρ p) (norm_nonneg _) zero_le_one
      _ < pp := by rw [one_mul]; exact hρpp
  have hum : ∀ τ, (‖(s : ℂ)‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := fun τ =>
    mem_markedRadiusSet_of_pos (flCore_of (hB τ) (hF τ)).δ₁_pos hab hca.le
      (by rw [norm_zero]; exact hbb.le)
  have hsr : ∀ τ, ‖(s : ℂ)‖ * (Real.sqrt N * (‖((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L S.a₁ k) κ * cψ))) < δ₁ := fun τ => by
    have := hum τ
    rw [norm_zero, add_zero] at this
    exact this
  -- the marks at the datum
  set F : ι × Set (CTorus d L N₁ m₁ (k + 1)) → ℂ := fun q => (S.β : ℂ) *
    deriv (fun t : ℂ => evDec (X₁f q.1) m₀ (jL q.1) (𝒦X q.1) S.a₁ S.ν S.hG'
      ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1) (Sol q.1)
      (eTermFun S.G' (Gk q.1) (Gj q.1) (stepG d L N₁ m₁ k ϱ)
        (compWeight L S.a₁) (Fk q.1)
        (fun r => (S.β : ℂ)⁻¹ * Eτ q.1 r))
      (S.blockU z) (s : ℂ) t q.2 (rawOf D, yhat x)) 0 with hFdef
  have hval : ∀ q : {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z},
      G₁ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) q (s : ℂ) ((S.blockSplit 1 hp).restr x) =
        F q.1 := by
    intro q
    rw [hG₁, ite_eq_left ⟨hΘ, hca⟩, hhat]
  -- the pairs left out of `markedIdx` contribute zero
  have hzero : ∀ τ, ∀ Y ∈ polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ),
      (τ, Y) ∉ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z → F (τ, Y) = 0 := by
    intro τ Y hY hnot
    have hmiss : psiThick Y ∩ fineBlock z = ∅ := by
      by_contra hne
      exact hnot (mem_markedIdx.2 ⟨hY, ⟨rootSite z, trivial, rootSite_mem_fineBlock z⟩,
        Set.nonempty_iff_ne_empty.2 hne⟩)
    have h0 := (classOldMarkedLocal_rootedMarks_gen_onSet (h𝒮 := h𝒮 τ)
        S hb₁ hbC (Eτ τ) (hBτ τ) hβ (hB τ) (hF τ)
      S.hG ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hMX hdm hα hsm (hcov τ) (hX₁ τ) hconn hrow
      (hopt τ) hκ₀ hκdec hκ h1 hlog (hEan τ) (hEbd τ) (hF₁an τ) (hF₁ τ) (hSolan τ) (hSolprop τ)
      (hFkan τ) (hFk τ) hN hm1 hd hL z hρ hρc hp hY).2 hmiss
      (s : ℂ) (hum τ) (rawOf D, yhat x) ⟨hΘ, hyx⟩
    show (S.β : ℂ) * _ = 0
    rw [h0, mul_zero]
  -- the mark identity of every label
  have hid := fun τ => Jr.deriv_classLabel_PJ_eq_sum_marked_joint_gen_onSet (h𝒮 := h𝒮 τ)
      hb₁ hbC (Eτ τ) (hBτ τ)
    (hj1 τ) (hjk τ) (hlocE τ) (hS τ) (hB τ) (hF τ) hc7 hR hsmR hRs hsmall hnum hnum' hcψ hMX hdm
    hα hsm (hcov τ) (hX₁ τ) hconn hrow (hopt τ) hκ₀ hκdec hκ h1 hlog (hEan τ) (hEbd τ) hβ
    (hF₁an τ)
    (hF₁ τ) (hSolan τ) (hSolprop τ) (hFkan τ) (hFk τ) D hD z x hyx (s : ℂ) hspp (hsr τ)
  rw [Finset.sum_congr rfl fun q _ => hval q, Finset.sum_coe_sort _ F,
    sum_markedIdx_eq _ _ z F hzero]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [(hid τ).1, Finset.mul_sum]

open Classical in
/-- **The sum identity of the marks family at every datum of the chart.**  For a step `S`
(`Hm = stepG`, `cc = β_k^{-1/2}`), a finite family of labels with their settings and given maps
(the hypotheses of `classMarksFamily_fields` and of `deriv_classLabel_PJ_eq_sum_marked`), `1 < a`
and `ρ < p⁺`: at every datum `D` of the chart, every `s ∈ [0, 1]` and every real field `x` with
`|x(u)| ≤ ρ`, the sum of the marks `G₁ (rawOf D, 0) q s` at the block configuration of `x` is the
sum over the labels of `∂_t|₀ ℰ^{(j)}(y, X; Jr.PJ j (rawOf D, s ψ̂ + t v_z))`,
`v_z = C^{-1/2} 1_{B(z)} C^{1/2} ψ̂`, `ψ̂ = yhat x`. -/
theorem classMarksFamily_sum_eq_deriv_gen {ι : Type*} [Fintype ι]
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {m₀ : ℕ} (Eτ : ι → RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ) (Bτ : ι → ℝ)
    (hBτ : ∀ τ, 0 ≤ Bτ τ) (hβ : 0 < S.β)
    (jL : ι → ℕ) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k)
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (hlocE : ∀ τ Ψ Ψ' h h', (∀ x ∈ XL τ, Ψ x = Ψ' x ∧ h x = h' x) →
      Eτ τ (Ψ, h) = Eτ τ (Ψ', h'))
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (Gj τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂
      δ₁ δfl (X₁f τ))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jL τ)) E₀ = treeLenCovOne m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEan : ∀ τ, AnalyticOnNhd ℂ (Eτ τ) (XiCRaw (Gj τ) (compWeight L S.a₁) S.ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    (hEbd : ∀ τ, ∀ r ∈ XiCRaw (Gj τ) (compWeight L S.a₁) S.ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      ‖Eτ τ r‖ ≤ Bτ τ * Real.exp (-(κdec - 1) * treeLenCovOne m₀ (jL τ) (XL τ)))
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N → ((stepG d L N₁ m₁ k
        ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi (stepG d L N₁ m₁ k ϱ) (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ
              p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N
            (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
              p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' =
                (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
    (hS : ∀ τ, GsSpecStrong (jL τ) ((hjk τ).trans (Nat.le_succ k)) (XL τ)
      (Gj τ))
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hN : L ^ m₀ ∣ N₁) (hm1 : 1 ≤ m₀) (hd : 3 ≤ d) (hL : 2 ≤ L)
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 < bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
          S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1.1) (Sol q.1.1)
          (eTermFun S.G' (Gk q.1.1) (Gj q.1.1) (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) (Fk q.1.1)
            (fun r => (S.β : ℂ)⁻¹ * Eτ q.1.1 r))
          (S.blockU z) u t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
      else 0) :
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : S.E, (∀ u, ‖x u‖ ≤ ρ) →
      ∑ q, G₁ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) q (s : ℂ) ((S.blockSplit 1 hp).restr x) =
        ∑ τ, deriv (fun t : ℂ => Eτ τ (Jr.PJ (jL τ) (rawOf D, (s : ℂ) • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
            S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x))))) 0 :=
  Jr.classMarksFamily_sum_eq_deriv_gen_onSet hb₁ hbC Eτ Bτ hBτ hβ jL XL hj1 hjk Gk Gj hlocE X₀ X₁f
    𝒦X hB hF hcψ hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog hEan hEbd F₁ hF₁an hF₁
    Sol hSolan hSolprop Fk hFkan hFk hS hc7 hR hsmR hRs hsmall hnum hnum' hN hm1 hd hL z hρ hρc hρpp
    hp ha1 hbb hab G₁ hG₁ (fun τ _ ht => d2raw_d1Triple_mem_xiCRaw hb₁ hbC (hB τ) (hF τ) (hFk τ) ht)

open Classical in
/-- **The sum identity of the marks family at every datum of the chart.**  For a step `S`
(`Hm = stepG`, `cc = β_k^{-1/2}`), a finite family of labels with their settings and given maps
(the hypotheses of `classMarksFamily_fields` and of `deriv_classLabel_PJ_eq_sum_marked`), `1 < a`
and `ρ < p⁺`: at every datum `D` of the chart, every `s ∈ [0, 1]` and every real field `x` with
`|x(u)| ≤ ρ`, the sum of the marks `G₁ (rawOf D, 0) q s` at the block configuration of `x` is the
sum over the labels of `∂_t|₀ ℰ^{(j)}(y, X; Jr.PJ j (rawOf D, s ψ̂ + t v_z))`,
`v_z = C^{-1/2} 1_{B(z)} C^{1/2} ψ̂`, `ψ̂ = yhat x`. -/
theorem classMarksFamily_sum_eq_deriv {ι : Type*} [Fintype ι]
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d)
    {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm)
    (hβ : 0 < S.β) (hE₀ : 0 ≤ P.E₀)
    (jL : ι → ℕ) (yL : ι → CTorus d L N₁ m₁ (k + 1)) (XL : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hj1 : ∀ τ, 1 ≤ jL τ) (hjk : ∀ τ, jL τ ≤ k) (hXp : ∀ τ, IsPolyDom C.m₀ (jL τ) (XL τ))
    (hy : ∀ τ, yL τ ∈ XL τ)
    (Gk : ι → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (X₀ X₁f : ι → Finset (CTorus d L N₁ m₁ (k + 1))) (𝒦X : ι → Set (CTorus d L N₁ m₁ (k + 1)))
    (hB : ∀ τ, BgSetting N S.G' (Gk τ) (C.Tm.gs (jL τ) (XL τ)) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀ τ)
      (X₁f τ) (jL τ))
    (hF : ∀ τ, FlSetting N S.G' (Gk τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂
      δ₁ δfl (X₁f τ))
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : ∀ τ, CovSetup S.G' C.m₀ (jL τ) (XL τ) (𝒦X τ))
    (hX₁ : ∀ τ, (↑(X₁f τ) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' C.m₀ (jL τ) (𝒦X τ))
    (hconn : HatConn S.G')
    (hrow : RowInHat (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν)
    (hopt : ∀ τ, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XL τ) ∧ MeetsOne C.m₀ (jL τ) (𝒦X τ) W₀ ∧
        bondCost (scaleW L C.m₀ m₁ (jL τ)) E₀ = treeLenCovOne C.m₀ (jL τ) (XL τ))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ C.m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hκP : κdec - 1 ≤ P.κ)
    (hchart : ∀ τ, ∀ r ∈ XiCRaw (C.Tm.gs (jL τ) (XL τ)) (compWeight L S.a₁) S.ν (jL τ) b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
      Dom.dom (jL τ) (C.Tm.gs (jL τ) (XL τ)) r.1 r.2)
    (F₁ : ι → DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
    (hF₁an : ∀ τ, AnalyticOnNhd ℂ (F₁ τ) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData S.G' N, InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ τ, ∀ (s : DecParams S.G') (D : BgData S.G' N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC S.G' (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : S.G'.Ω 1 × Fin N → ℂ)
        (α : S.G'.Ω 1 → ℂ), IsDecBg S.G' (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ τ (s, rawOf D) = (φ, α))
    (Sol : ι → Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N → ((stepG d L N₁ m₁ k
        ϱ).Ω 1 × Fin N → ℂ) × ((stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ))
    (hSolan : ∀ τ, AnalyticOnNhd ℂ (Sol τ) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ τ, ∀ p : Dec2.DecParams (coverOf S.G') × Edat (stepG d L N₁ m₁ k ϱ) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (stepG d L N₁ m₁ k ϱ) N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol τ p).1 = dphi (stepG d L N₁ m₁ k ϱ) (Dec2.decG (coverOf S.G') (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ
              p).2 ∧
        Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
            p.2.2.1 p.2.1
          (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol τ p).2 ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (stepG d L N₁ m₁ k ϱ) (Sol τ p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (stepG d L N₁ m₁ k ϱ) (Sol τ p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (stepG d L N₁ m₁ k ϱ).Ω 1 → ℂ, Small (stepG d L N₁ m₁ k ϱ) δα' (c6' d L N
            (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf S.G') (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) S.ν p.1 false
              p.2.2.1 p.2.1
            (pertSource (stepG d L N₁ m₁ k ϱ) (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' =
                (Sol τ p).2))
    (Fk : ∀ τ, RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Gk τ).Ω 1 × Fin N → ℂ) × ((Gk τ).Ω 1 → ℂ))
    (hFkan : ∀ τ, AnalyticOnNhd ℂ (Fk τ) {p | ∃ D : BgData (Gk τ) N,
      InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ τ, ∀ D : BgData (Gk τ) N, InUnionDomainC (Gk τ) (bgC0 d L N) (bgC1 d L N) S.ν D →
      Fk τ (rawOf D) = (bgFieldC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D,
        bgMultC (Gk τ) (compWeight L S.a₁) S.ν (bgC0 d L N) D))
    (hS : ∀ τ, GsSpecStrong (jL τ) ((hjk τ).trans (Nat.le_succ k)) (XL τ)
      (C.Tm.gs (jL τ) (XL τ)))
    (hc7 : c7 d L N BG κ ≤ thm73C3 d L N) {R : ℝ} (hR : 2 ≤ R)
    (hsmR : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    (hRs : R * δ₁ ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hN : L ^ C.m₀ ∣ N₁) (hm1 : 1 ≤ C.m₀) (hd : 3 ≤ d) (hL : 2 ≤ L)
    (z : RootIdx d L N₁ m₁ (k + 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ cψ) (hρpp : ρ < pp)
    (hp : 0 < S.p₁) {a bb : ℝ} (ha1 : 1 < a) (hbb : 0 < bb)
    (hab : (a + bb) * markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (G₁ : physParam N S →
      {q // q ∈ markedIdx (fun _ => (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun τ => polyDom S.G' (X₁f τ) C.m₀ (jL τ) (𝒦X τ)) z} →
      ℂ → (∀ b, (S.blockSplit 1 hp).Ωb b) → ℂ)
    (hG₁ : ∀ θ q u Φ, G₁ θ q u Φ =
      if (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < a then
        (S.β : ℂ) * deriv (fun t : ℂ => evDec (X₁f q.1.1) C.m₀ (jL q.1.1) (𝒦X q.1.1) S.a₁ S.ν
          S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ q.1.1) (Sol q.1.1)
          (eTermFun S.G' (Gk q.1.1) (C.Tm.gs (jL q.1.1) (XL q.1.1)) (stepG d L N₁ m₁ k ϱ)
            (compWeight L S.a₁) (Fk q.1.1)
            (fun r => (S.β : ℂ)⁻¹ * C.Tm.E (jL q.1.1) (yL q.1.1) (XL q.1.1) r.1 r.2))
          (S.blockU z) u t q.1.2
          ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), S.hatOf 1 ρ hp Φ)) 0
      else 0) :
    ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : S.E, (∀ u, ‖x u‖ ≤ ρ) →
      ∑ q, G₁ ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'),
          (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) q (s : ℂ) ((S.blockSplit 1 hp).restr x) =
        ∑ τ, deriv (fun t : ℂ => C.Tm.E (jL τ) (yL τ) (XL τ)
          (Jr.PJ (jL τ) (rawOf D, (s : ℂ) • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
            S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)))).1
          (Jr.PJ (jL τ) (rawOf D, (s : ℂ) • yhat x + t • ((Jr.Mx (rawOf D))⁻¹ *ᵥ
            S.maskUC z (Jr.Mx (rawOf D) *ᵥ yhat x)))).2) 0 := by
  have hraw := fun τ => classOldEnergy_chart_radius_raw (N := N) (b := b) C hm hcl hκP hE₀ S.a₁ S.ν
    δ₃ eps δfl (hj1 τ) (hjk τ) (hXp τ) (hy τ) (hchart τ)
  exact Jr.classMarksFamily_sum_eq_deriv_gen hb₁ hbC
    (fun τ r => C.Tm.E (jL τ) (yL τ) (XL τ) r.1 r.2) (fun _ => P.E₀) (fun _ => hE₀) hβ jL XL hj1
    hjk Gk (fun τ => C.Tm.gs (jL τ) (XL τ))
    (fun τ Ψ Ψ' h h' hag => hcl.localE (jL τ) (yL τ) (XL τ) Ψ Ψ' h h' hag) X₀ X₁f 𝒦X hB hF hcψ
    hMX hdm hα hsm hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog (fun τ => (hraw τ).1)
    (fun τ => (hraw τ).2) F₁ hF₁an hF₁ Sol hSolan hSolprop Fk hFkan hFk hS hc7 hR hsmR hRs hsmall hnum hnum' hN hm1 hd hL z hρ hρc hρpp hp ha1 hbb hab G₁ hG₁

end StepSetting.JointRep

end FamilyIdentity

end Balaban.Fluctuation
