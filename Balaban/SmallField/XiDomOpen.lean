/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.XiCRawOpen
public import Balaban.SmallField.Def6Terms
import Mathlib.Tactic.Linarith

/-!
# The class domain `XiDom` is open relative to the layer-constant fields

The field domain `XiDom` is a cylinder over the subspace `layerSub` of layer-constant pairs: not open in
the space of fields, open relative to the layer-constant fields (`xiDom_eventually`).  (This file
holds the section moved from `Balaban/Inhabited/XiCRawOpenWitness.lean`, so that the frame bridges
of `Def6BridgeLift` can use it.)
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Filter Topology

section Rescale

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}

/-- The numerical comparisons behind the rescaling `(σ, ε) ↦ (1, ε')`, `1 ≤ σ`, `σ² ε ≤ ε'`. -/
theorem rescale_nums {σ ε ε' : ℝ} (hσ : 1 ≤ σ) (he : 0 < ε) (hle : σ ^ 2 * ε ≤ ε') :
    σ * ε ≤ 1 * ε' ∧ σ ^ 2 * ε ≤ 1 ^ 2 * ε' ∧ (σ * ε) ^ 2 ≤ (1 * ε') ^ 2 ∧ ε ≤ ε' ∧
      (σ * ε) ^ 2 / ε ≤ (1 * ε') ^ 2 / ε' := by
  have hσ0 : 0 ≤ σ := by linarith
  have h1 : σ * ε ≤ σ ^ 2 * ε := by
    nlinarith [mul_nonneg (mul_nonneg hσ0 he.le) (sub_nonneg.2 hσ)]
  have h2 : ε ≤ σ * ε := by nlinarith
  have hp : 0 < ε' := lt_of_lt_of_le he (h2.trans (h1.trans hle))
  have h3 : σ * ε ≤ ε' := h1.trans hle
  refine ⟨by linarith, by linarith, ?_, by linarith, ?_⟩
  · have := mul_self_le_mul_self (by positivity : 0 ≤ σ * ε) (by linarith : σ * ε ≤ 1 * ε')
    nlinarith
  · have e1 : (σ * ε) ^ 2 / ε = σ ^ 2 * ε := by field_simp
    have e2 : (1 * ε') ^ 2 / ε' = ε' := by field_simp
    rw [e1, e2]; exact hle

/-- `Ξ_n(𝔹; σ, ε)` inequalities weaken to `(1, ε')` when `1 ≤ σ` and `σ² ε ≤ ε'`
(`grad`, `collarBond`, `mass` carry `σ ε ≤ ε'`; `lap`, `mult`, `close` carry `σ² ε ≤ ε'`; `hnorm`
carries `(σ ε)² ≤ ε'²`). -/
theorem xiBounds_rescale {ν σ ε ε' : ℝ} {n : ℕ} {D : BgData G N} {h₀ : Fin N → ℝ}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} (hσ : 1 ≤ σ) (he : 0 < ε) (hle : σ ^ 2 * ε ≤ ε')
    (hb : XiBounds G ν n σ ε D h₀ φ α) : XiBounds G ν n 1 ε' D h₀ φ α := by
  obtain ⟨n1, n2, n3, -, -⟩ := rescale_nums hσ he hle
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x hx => ?_, fun z hz z' hz' hadj => ?_,
    fun z => ?_, ?_⟩
  · have hs := spacing_pos G (x := x)
    exact ⟨(hb.grad x hx μ).1.trans_le (div_le_div_of_nonneg_right n1 hs.le),
      (hb.grad x hx μ).2.trans_le (div_le_div_of_nonneg_right n1 hs.le)⟩
  · have hs := spacing_pos G (x := x)
    exact (hb.lap x hx).trans_le (div_le_div_of_nonneg_right n2 (by positivity))
  · exact (hb.mult x).trans_le n2
  · exact (hb.close x hx).trans_le n2
  · exact (hb.collarBond z hz z' hz' hadj).trans_le n1
  · exact (hb.mass z).trans_le n1
  · exact hb.hnorm.trans_le n3

/-- `Ξ^c_n(𝔹; σ, ε)` displacement inequalities weaken to `(1, ε')` when `1 ≤ σ`,
`σ² ε ≤ ε'` (and `0 < ε`). -/
theorem xiCBounds_rescale {ν σ ε ε' : ℝ} {Dr Dc : BgData G N}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φr φc : G.Ω 1 × Fin N → ℂ}
    {αr αc : G.Ω 1 → ℂ} (hσ : 1 ≤ σ) (he : 0 < ε) (hle : σ ^ 2 * ε ≤ ε')
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) :
    XiCBounds G ν 1 ε' Dr Dc Ψ'' h'' φr φc αr αc := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := rescale_nums hσ he hle
  refine ⟨fun x hx μ => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' hadj => ?_, fun x hx => ?_, fun x => ?_⟩
  · have hs := spacing_pos G (x := x)
    exact ⟨(hb.grad x hx μ).1.trans_le (div_le_div_of_nonneg_right n1 hs.le),
      (hb.grad x hx μ).2.trans_le (div_le_div_of_nonneg_right n1 hs.le)⟩
  · have hs := spacing_pos G (x := x)
    exact (hb.lap x hx).trans_le (div_le_div_of_nonneg_right n2 (by positivity))
  · exact (hb.mult x).trans_le n2
  · exact (hb.val x).trans_le n4
  · exact (hb.close x hx).trans_le n2
  · exact (hb.collarBond z hz z' hz' hadj).trans_le n1
  · exact (hb.hAbs x hx).trans_le n5
  · exact (hb.hDot x).trans_le n3

/-- The displacement inequalities depend on the displacements only through their values on
`Ω₁ ∪ C(Ω₁)` (`Ψ''`) and on `Ω₁` (`h''`). -/
theorem xiCBounds_congr {ν σ ε : ℝ} {Dr Dc : BgData G N}
    {Ψ'' h'' Ψ''₂ h''₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φr φc : G.Ω 1 × Fin N → ℂ}
    {αr αc : G.Ω 1 → ℂ} (hΨ : ∀ x ∈ dataSites G, ∀ i, Ψ''₂ x i = Ψ'' x i)
    (hh : ∀ x ∈ G.Ω 1, ∀ i, h''₂ x i = h'' x i)
    (hb : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) :
    XiCBounds G ν σ ε Dr Dc Ψ''₂ h''₂ φr φc αr αc where
  grad := hb.grad
  lap := hb.lap
  mult := hb.mult
  val := hb.val
  close x hx := by
    have e : (fun i => Ψ''₂ x i - blockAvg G (φc - φr) x i) =
        fun i => Ψ'' x i - blockAvg G (φc - φr) x i := by
      funext i; rw [hΨ x ((mem_dataSites G).2 (Or.inl hx)) i]
    rw [e]; exact hb.close x hx
  collarBond z hz z' hz' hadj := by
    have e : (fun i => Ψ''₂ z i - Ψ''₂ z' i) = fun i => Ψ'' z i - Ψ'' z' i := by
      funext i
      rw [hΨ z ((mem_dataSites G).2 (Or.inr hz)) i, hΨ z' ((mem_dataSites G).2 (Or.inr hz')) i]
    rw [e]; exact hb.collarBond z hz z' hz' hadj
  hAbs x hx := by
    have e : h''₂ x = h'' x := funext (hh x hx)
    rw [e]; exact hb.hAbs x hx
  hDot x := by
    have e : ∀ i, h''₂ (x : Torus d (N₀ * L ^ k)) i = h'' (x : Torus d (N₀ * L ^ k)) i :=
      hh _ x.2
    simp only [e]; exact hb.hDot x

/-- **Same-centre rescaling of `Ξ^c_n(𝔹; σ, ε)`** (exact statement): for `1 ≤ σ` and
`σ² ε ≤ ε'`, a member of `Ξ^c_n(𝔹; σ, ε)` with centre `(Ψ₀, h₀)` and displacement `(Ψ'', h'')` is
a member of `Ξ^c_n(𝔹; 1, ε')` with the same centre, and with any displacement `(Ψ''₂, h''₂)`
agreeing with `(Ψ'', h'')` on `Ω₁ ∪ C(Ω₁)` (resp. `Ω₁`).  Direction of the monotonicity: every
bound of `XiBounds`/`XiCBounds` is increasing in `ε` and in `σ`; `grad`, `collarBond`, `mass`
scale as `σ ε`, `lap`, `mult`, `close`, `hAbs` as `σ² ε`, `val` as `ε`, `hDot`, `hnorm` as
`(σ ε)²`; the real-part and union-domain conditions do not involve `(σ, ε)`. -/
theorem xiC_rescale_of_agree {a : ℕ → ℝ} {ν σ ε ε' : ℝ} {n : ℕ}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' Ψ''₂ h''₂ : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hσ : 1 ≤ σ) (hle : σ ^ 2 * ε ≤ ε')
    (hΨ : ∀ x ∈ dataSites G, ∀ i, Ψ''₂ x i = Ψ'' x i) (hh : ∀ x ∈ G.Ω 1, ∀ i, h''₂ x i = h'' x i)
    (hX : XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'') : XiC G a ν n 1 ε' Ψ₀ h₀ Ψ''₂ h''₂ := by
  obtain ⟨-, he, Dr, Dc, hXr, hR, hU, hb⟩ := hX
  have hε' : ε ≤ ε' := (rescale_nums hσ he hle).2.2.2.1
  refine ⟨one_pos, he.trans_le hε', Dr, Dc,
    ⟨hXr.1, hXr.2.1, xiBounds_rescale hσ he hle hXr.2.2⟩,
    ⟨fun x hx i => by rw [hR.1 x hx i, hΨ x hx i],
      fun x hx i => by rw [hR.2 x hx i, hh x hx i]⟩, hU,
    xiCBounds_congr hΨ hh (xiCBounds_rescale hσ he hle hb)⟩

/-- **Same-centre rescaling of `Ξ^c_n(𝔹; σ, ε)`** with the same displacement. -/
theorem xiC_rescale {a : ℕ → ℝ} {ν σ ε ε' : ℝ} {n : ℕ}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (hσ : 1 ≤ σ) (hle : σ ^ 2 * ε ≤ ε')
    (hX : XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'') : XiC G a ν n 1 ε' Ψ₀ h₀ Ψ'' h'' :=
  xiC_rescale_of_agree hσ hle (fun _ _ _ => rfl) (fun _ _ _ => rfl) hX

end Rescale

section Dom

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- Cutting a pair of fields off outside the data sites. -/
noncomputable def clipRaw (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (r : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) : RawData d L (N₁ * L ^ m₁) K N :=
  (fun x i => if x ∈ dataSites G then r.1 x i else 0, fun x i => if x ∈ G.Ω 1 then r.2 x i else 0)

theorem continuous_clipRaw (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) :
    Continuous (clipRaw (N := N) G) := by
  classical
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun x => continuous_pi fun i => ?_
    by_cases hx : x ∈ dataSites G
    · simp only [hx, ↓reduceIte]; fun_prop
    · simp only [hx, ↓reduceIte]; fun_prop
  · refine continuous_pi fun x => continuous_pi fun i => ?_
    by_cases hx : x ∈ G.Ω 1
    · simp only [hx, ↓reduceIte]; fun_prop
    · simp only [hx, ↓reduceIte]; fun_prop

/-- The fields that are constant on the blocks of every layer. -/
def layerSub (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) :
    Set (Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) :=
  {r | IsLayerConstant G r.1 ∧ IsLayerConstant G r.2}

theorem clipRaw_mem_rawSub (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    {r : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N} (hr : r ∈ layerSub G) :
    clipRaw G r ∈ rawSub N G := by
  classical
  have : clipRaw G r = rawOf (BgData.clip G r.1 r.2 hr.1 hr.2) := by
    refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
    · by_cases hx : x ∈ dataSites G <;> simp [clipRaw, rawOf, BgData.clip, hx]
    · by_cases hx : x ∈ G.Ω 1 <;> simp [clipRaw, rawOf, BgData.clip, hx]
  rw [this]; exact rawOf_mem_rawSub _

/-- **The class domain `XiDom` is open relative to the layer-constant fields.**  (It is not open
in the space of all fields: it is a cylinder over the subspace `layerSub`, since
`Ψ = Ψ₀ + Ψ''` must be constant on blocks on the data sites.)  If `(Ψ, h) ∈ XiDom`, then every
pair of layer-constant fields near `(Ψ, h)` lies in `XiDom` (same level, kernel sequence, mass and
radius). -/
theorem xiDom_eventually {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {n : ℕ}
    {ε : ℝ} (H : BgHyp d L K ϱ a ν) {Ψ h : Fld d L N₁ m₁ K N} (hX : XiDom G a ν n ε Ψ h) :
    ∀ᶠ r in 𝓝[layerSub G] ((Ψ, h) : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N),
      XiDom G a ν n ε r.1 r.2 := by
  classical
  obtain ⟨Ψ₀, h₀, Ψ'', h'', e1, e2, hXC⟩ := hX
  obtain ⟨hσ, hε, Dr, Dc, hXr, hC, hU, hb⟩ := hXC
  have hc0 : clipRaw G ((Ψ, h) : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) = rawOf Dc := by
    refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
    · by_cases hx : x ∈ dataSites G
      · simp only [clipRaw, rawOf, hx, ↓reduceIte]
        rw [hC.1 x hx i, e1 x i]
      · simp only [clipRaw, rawOf, hx, ↓reduceIte]
        rw [Dc.Ψ_zero x hx]; rfl
    · by_cases hx : x ∈ G.Ω 1
      · simp only [clipRaw, rawOf, hx, ↓reduceIte]
        rw [hC.2 x hx i, e2 x i]
      · simp only [clipRaw, rawOf, hx, ↓reduceIte]
        rw [Dc.h_zero x hx]; rfl
  have hXD : XiCData G a ν n 1 ε Dc := ⟨Ψ₀, h₀, Ψ'', h'', ⟨hσ, hε, Dr, Dc, hXr, hC, hU, hb⟩, hC⟩
  have ev := xiCRaw_eventually H hXD
  have hT : Filter.Tendsto (clipRaw (N := N) G) (𝓝[layerSub G] ((Ψ, h) : Fld d L N₁ m₁ K N ×
      Fld d L N₁ m₁ K N)) (𝓝[(rawSub N G : Set _)] (rawOf Dc)) := by
    rw [← hc0]
    exact tendsto_nhdsWithin_iff.2 ⟨((continuous_clipRaw G).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun r hr => clipRaw_mem_rawSub G hr⟩
  filter_upwards [hT.eventually ev] with r hr
  obtain ⟨Dd, ⟨Ψ₁, h₁, Ψ₂, h₂, hXC₂, hR₂⟩, heq⟩ := hr
  refine ⟨Ψ₁, h₁, fun x i => r.1 x i - Ψ₁ x i, fun x i => r.2 x i - (h₁ i : ℂ),
    fun x i => by ring, fun x i => by ring, ?_⟩
  refine xiC_rescale_of_agree (σ := 1) (ε := ε) (ε' := ε) le_rfl (by simp) (fun x hx i => ?_)
    (fun x hx i => ?_) hXC₂
  · have h1 := hR₂.1 x hx i
    have h2 : Dd.Ψ x i = r.1 x i := by
      have := congrFun (congrFun (congrArg Prod.fst heq) x) i
      simpa [clipRaw, rawOf, hx] using this.symm
    show r.1 x i - Ψ₁ x i = Ψ₂ x i
    rw [← h2, h1]; ring
  · have h1 := hR₂.2 x hx i
    have h2 : Dd.h x i = r.2 x i := by
      have := congrFun (congrFun (congrArg Prod.snd heq) x) i
      simpa [clipRaw, rawOf, hx] using this.symm
    show r.2 x i - (h₁ i : ℂ) = h₂ x i
    rw [← h2, h1]; ring

end Dom

end Balaban.Fluctuation
