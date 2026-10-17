/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityHAnalytic

/-!
# The expansion identity off the fibre: continuation in `h` is not available (blocker 6, item (3))

The question: does the expansion identity `hDz` (`Σ_{Y ∋ y} TE y Y q = 𝒟(y)(q)`, P4 (2.57),
(4.22)) on the whole class domain follow from its fibre version (the pairs `q = (Ψ, h)` with `h`
a real constant) by analytic continuation in `h`?

**Answer: no.**  The two sides are analytic on the class domain (for the density: the
representative `densE0` of `LocalClassDensityHAnalytic`), but the pairs with constant field are
not a set of uniqueness for analytic functions on the class domain as soon as the field may vary
between two sites of `Ω₁`: the linear function `q ↦ q.2 x i - q.2 x' i` vanishes at every pair with
constant field (real or complex, any value) and is not zero on the class domain
(`exists_analytic_constField_zero_ne_zero_xiDom`, and the same on the chart,
`exists_analytic_constField_zero_ne_zero_xiCRaw`).  Adding it to either side of an identity keeps
the identity on the fibre and breaks it off the fibre.  The identity theorem would need the
agreement set to have non-empty interior in the (relatively open) domain, or to be a maximal
totally real set; the constant fields form a real subspace of dimension `N` of a complex space of
dimension `N · #(blocks of Ω₁)`.

**What the identity needs instead.**  The identity must be proved at every pair of the domain
directly, i.e. at every datum `D` of the chart with arbitrary field:
* the density at `D`: `densE0 y q = E0locH (blockIndex y)` at the datum of `clipRaw 𝔹 q`
  (`densE0_eq`, `LocalClassDensityHAnalytic`); this is now defined and analytic (item (2));
* `hval` at `D`: a cube-set expansion `E0locH z = Σ_T e(rawOf D) z T` at every datum `D` of the
  chart (not only on the fibre);
* `hrepl` at `D`: the replacement identity of the terms recomputed on `𝔹_{k+1}(Y⁺)` at the pairs of
  the domain.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Matrix Filter Topology

section Uniqueness

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- A datum of the chart `Ξ^c_n(𝔹; 1, ε)` gives a pair of the class domain `Ξ^c_n(𝔹; 1, ε)`
(`XiDom`, the pair of the witness of `XiCData`) with the same field on `Ω₁` and the same cut-off. -/
theorem exists_xiDom_of_xiCData {a : ℕ → ℝ} {ν ε : ℝ} {n : ℕ} {D : BgData G N}
    (hD : XiCData G a ν n 1 ε D) :
    ∃ q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N, XiDom G a ν n ε q.1 q.2 ∧
      (∀ x ∈ G.Ω 1, q.2 x = D.h x) ∧ clipRaw G q = rawOf D := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hXi, hR⟩ := hD
  refine ⟨(fun x i => (Ψ₀ x i : ℂ) + Ψ'' x i, fun x i => (h₀ i : ℂ) + h'' x i),
    ⟨Ψ₀, h₀, Ψ'', h'', fun _ _ => rfl, fun _ _ => rfl, hXi⟩, fun x hx => ?_,
    clipRaw_eq_rawOf_of_realizesC hR (fun _ _ => rfl) (fun _ _ => rfl)⟩
  funext i
  exact (hR.2 x hx i).symm

/-- The linear function `Θ ↦ Θ.2 x i - Θ.2 x' i` of the raw data is analytic. -/
theorem analyticAt_rawField_sub (x x' : Torus d ((N₁ * L ^ m₁) * L ^ K)) (i : Fin N)
    (Θ : RawData d L (N₁ * L ^ m₁) K N) :
    AnalyticAt ℂ (fun Θ : RawData d L (N₁ * L ^ m₁) K N => Θ.2 x i - Θ.2 x' i) Θ := by
  have h : ∀ y : Torus d ((N₁ * L ^ m₁) * L ^ K),
      AnalyticAt ℂ (fun Θ : RawData d L (N₁ * L ^ m₁) K N => Θ.2 y i) Θ := fun y =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt _).comp
      (((ContinuousLinearMap.proj (R := ℂ)
        (φ := fun _ : Torus d ((N₁ * L ^ m₁) * L ^ K) => Fin N → ℂ) y).analyticAt _).comp
        analyticAt_snd)
  exact (h x).sub (h x')

/-- **Field directions separating two blocks exist**: on a generating set of one level `n` (every
site in `Ω₁`, of layer `n`), the indicator of the `n`-block of a site `x` is constant on the
blocks, and it separates `x` from every site `x'` of another `n`-block. -/
theorem exists_fieldDir_sep {n : ℕ} (hG : IsLevel G n) {x x' : Torus d ((N₁ * L ^ m₁) * L ^ K)}
    (hxx' : jBlock d L (N₁ * L ^ m₁) K n x' ≠ jBlock d L (N₁ * L ^ m₁) K n x) (i : Fin N) :
    ∃ w : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ, IsLayerConstant G w ∧
      (∀ y, y ∉ G.Ω 1 → w y = 0) ∧ w x i ≠ w x' i := by
  classical
  refine ⟨fun y _ => if jBlock d L (N₁ * L ^ m₁) K n y = jBlock d L (N₁ * L ^ m₁) K n x then 1
    else 0, fun m hm1 hmK y hy y' hy' => ?_, fun y hy => absurd (hG y).1 hy, ?_⟩
  · have hm : m = n := by rw [← G.layerIndex_eq hm1 hmK hy, (hG y).2]
    subst hm
    have hb := GeneratingSet.mem_blk.1 hy'
    funext j
    simp only [hb]
  · simp [hxx']

/-- **The data with constant field are not a set of uniqueness on the chart.**  If a datum `D` of
the chart has the same field at two sites `x, x'` of `Ω₁` and a field direction `w` of the data
subspace separates them, the analytic function `Θ ↦ Θ.2 x i - Θ.2 x' i` vanishes at the raw datum
of every datum whose field is constant on `Ω₁` (in particular on the fibre of every step) and does
not vanish at some raw datum of the chart. -/
theorem exists_analytic_constField_zero_ne_zero_xiCRaw {a : ℕ → ℝ} {ν σ ε : ℝ} {n : ℕ}
    (H : BgHyp d L K ϱ a ν) {D : BgData G N} (hD : XiCData G a ν n σ ε D)
    {w : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ}
    (hw : IsLayerConstant G w) (hw0 : ∀ x, x ∉ G.Ω 1 → w x = 0)
    {x x' : Torus d ((N₁ * L ^ m₁) * L ^ K)} (hx : x ∈ G.Ω 1) (hx' : x' ∈ G.Ω 1) {i : Fin N}
    (hDx : D.h x i = D.h x' i) (hwx : w x i ≠ w x' i) :
    ∃ F : RawData d L (N₁ * L ^ m₁) K N → ℂ, (∀ Θ, AnalyticAt ℂ F Θ) ∧
      (∀ (D' : BgData G N) (c : Fin N → ℂ), (∀ y ∈ G.Ω 1, ∀ j, D'.h y j = c j) →
        F (rawOf D') = 0) ∧
      ∃ Θ ∈ XiCRaw G a ν n σ ε, F Θ ≠ 0 := by
  refine ⟨fun Θ => Θ.2 x i - Θ.2 x' i, analyticAt_rawField_sub x x' i,
    fun D' c hc => ?_, ?_⟩
  · show D'.h x i - D'.h x' i = 0
    rw [hc x hx i, hc x' hx' i, sub_self]
  · obtain ⟨c, -, -, hcX, hne⟩ := exists_xiCRaw_field_ne H hD hw hw0 hDx hwx one_pos
    exact ⟨_, hcX, sub_ne_zero.2 hne⟩

/-- **The pairs with constant field are not a set of uniqueness on the class domain.**  Under the
hypotheses of `exists_analytic_constField_zero_ne_zero_xiCRaw` (with `σ = 1`), the analytic
function `q ↦ q.2 x i - q.2 x' i` of the pairs of fields vanishes at every pair whose field is
constant (in particular at every pair of the fibre version of `hDz`) and does not vanish at some
pair of the class domain `Ξ^c_n(𝔹; 1, ε)` (`XiDom`).  Hence an identity between analytic functions
on the class domain is not implied by the identity at the pairs with constant field. -/
theorem exists_analytic_constField_zero_ne_zero_xiDom {a : ℕ → ℝ} {ν ε : ℝ} {n : ℕ}
    (H : BgHyp d L K ϱ a ν) {D : BgData G N} (hD : XiCData G a ν n 1 ε D)
    {w : Torus d ((N₁ * L ^ m₁) * L ^ K) → Fin N → ℂ}
    (hw : IsLayerConstant G w) (hw0 : ∀ x, x ∉ G.Ω 1 → w x = 0)
    {x x' : Torus d ((N₁ * L ^ m₁) * L ^ K)} (hx : x ∈ G.Ω 1) (hx' : x' ∈ G.Ω 1) {i : Fin N}
    (hDx : D.h x i = D.h x' i) (hwx : w x i ≠ w x' i) :
    ∃ F : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N → ℂ, (∀ q, AnalyticAt ℂ F q) ∧
      (∀ (q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) (c : Fin N → ℂ),
        (∀ y, q.2 y = c) → F q = 0) ∧
      ∃ q, XiDom G a ν n ε q.1 q.2 ∧ F q ≠ 0 := by
  refine ⟨fun q => q.2 x i - q.2 x' i, fun q => analyticAt_rawField_sub x x' i q,
    fun q c hc => ?_, ?_⟩
  · show q.2 x i - q.2 x' i = 0
    rw [hc x, hc x', sub_self]
  · obtain ⟨c, -, -, ⟨D', hD', hraw⟩, hne⟩ :=
      exists_xiCRaw_field_ne H hD hw hw0 hDx hwx one_pos
    obtain ⟨q, hq, hqh, -⟩ := exists_xiDom_of_xiCData hD'
    refine ⟨q, hq, ?_⟩
    show q.2 x i - q.2 x' i ≠ 0
    rw [hqh x hx, hqh x' hx']
    have e : (D'.h x i, D'.h x' i) =
        ((rawOf D + c • ((0, w) : RawData d L (N₁ * L ^ m₁) K N)).2 x i,
          (rawOf D + c • ((0, w) : RawData d L (N₁ * L ^ m₁) K N)).2 x' i) := by
      rw [hraw]; rfl
    simp only [Prod.mk.injEq] at e
    rw [e.1, e.2]
    exact sub_ne_zero.2 hne

end Uniqueness

end Balaban.Fluctuation
