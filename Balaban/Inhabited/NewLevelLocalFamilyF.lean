/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassRot
public import Balaban.Fluctuation.LocalClassChart
public import Balaban.Fluctuation.ParamActivitySubspace
public import Balaban.Fluctuation.Prop33SymmDef
public import Balaban.Fluctuation.BgTransport

/-!
# A family of the pair of fields from a family of the parameters of local generating sets

Route R-LOC, L5: the family of the new level recomputed on the local generating set `Gb T` of the
polymer `T` is a function `c T` of the parameters of `Gb T`.  Read at the pair of fields `p` through
the datum of `Gb T` (`clipRaw (Gb T) p`, projected onto the data of `Gb T` by a continuous linear
retraction `π_b T`, with zero sources), and set to `0` off a class of polymers (`gate`), it becomes
a family `f T p` of the pair of fields.  The clauses (A1)–(A5) of `newLabels_castInputs_of_localFamily`
for `f` follow from the corresponding clauses of `c T` on the parameters.

* `localFamily_of_coeff`: (A1) analyticity on the chart of `Gb T` of radius `ε`, (A2) the bound,
  (A3) locality on the chart of radius `ε_loc`, (A4) rotation invariance, (A5) the read identity.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Multiscale Balaban.Background Balaban.Localization
  Balaban.SmallField Balaban.SmallField.Def6 Matrix

section F

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb : ℝ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) 1 (k + 1)
  Set.univ

/-- The datum of a parameter read from a pair of fields: the cut-off to the data of `G`, projected
onto the data of `G`, with zero sources. -/
theorem clipRaw_mem_rawSub_of_xiDom {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
    {a : ℕ → ℝ} {ν ε : ℝ} {p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : XiDom G a ν (k + 1) ε p.1 p.2) : clipRaw G p ∈ rawSub N G :=
  XiCRaw_subset_rawSub _ _ _ _ _ _ (clipRaw_mem_xiCRaw_of_xiDom le_rfl hp)

open Classical in
/-- **The family of the pair of fields from families of the parameters of local generating sets**
(route R-LOC, L5).  Let `Gb T` be generating sets with retractions `π_b T` onto their data, `c T` a
function of the parameters of `Gb T` and `gate` a class of polymers.  If, for the polymers of the
class, `c T` is analytic and bounded by `b T ≥ 0` on the parameters `physVBg (Gb T) ε_an`
(`ε ≤ ε_an`), takes equal values at two parameters with zero sources of the chart of radius `ε_loc`
whose data agree on `Y⁺ T` (which contains the sites read by the data), is invariant under the real
rotations on `physVBg (Gb T) ε_an`, and equals the step's coefficient `e (π q, 0) T` at the datum
read from a pair `q` of the step chart; and if `e (π q, 0) T = 0` off the class; then
`f T p = c T (π_b T (clipRaw (Gb T) p), 0)` on the class and `0` off it satisfies (A1)–(A5). -/
theorem localFamily_of_coeff {S : StepSetting d L N₁ m₁ k N ϱ}
    (Gb : Finset 𝔅 → GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb)
    (Ypl : Finset 𝔅 → Set (CTorus d L N₁ m₁ (k + 1))) (gate : Finset 𝔅 → Prop)
    (πb : ∀ T, RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N (Gb T))
    (hπb : ∀ T r (h : r ∈ rawSub N (Gb T)), πb T r = ⟨r, h⟩)
    (c : ∀ T, physParamBg N (Gb T) → ℂ) {a₁ ν ε εan εloc : ℝ} (hεan : ε ≤ εan)
    (hc1 : ∀ T, gate T → AnalyticOnNhd ℂ (c T) (physVBg N (Gb T) a₁ ν εan))
    (b : Finset 𝔅 → ℝ) (hb0 : ∀ T, 0 ≤ b T)
    (hc2 : ∀ T, gate T → ∀ θ ∈ physVBg N (Gb T) a₁ ν εan, ‖c T θ‖ ≤ b T)
    (hc3 : ∀ T, gate T → ∀ θ θ' : physParamBg N (Gb T),
      (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw (Gb T) (compWeight L a₁) ν (k + 1) 1 εloc →
      (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw (Gb T) (compWeight L a₁) ν (k + 1) 1 εloc → θ.2 = 0 → θ'.2 = 0 →
      (∀ x ∈ Ypl T, (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 x =
          (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).1 x ∧
        (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 x =
          (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N).2 x) → c T θ = c T θ')
    (hc4 : ∀ T, gate T → ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
      ∀ θ ∈ physVBg N (Gb T) a₁ ν εan, ∀ θ' ∈ physVBg N (Gb T) a₁ ν εan,
      (θ'.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) =
        rotRaw (cmat Q) (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) → c T θ' = c T θ)
    (e : physParam N S → Finset 𝔅 → ℂ)
    (π : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] rawSub N S.G')
    (hc5 : ∀ T, gate T → ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      XiDom S.G' (compWeight L a₁) ν (k + 1) ε q.1 q.2 →
      c T (πb T (clipRaw (Gb T) q), 0) = e (π (clipRaw S.G' q), 0) T)
    (he0 : ∀ T, ¬ gate T → ∀ q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      XiDom S.G' (compWeight L a₁) ν (k + 1) ε q.1 q.2 → e (π (clipRaw S.G' q), 0) T = 0) :
    ∃ f : Finset 𝔅 → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ,
      (∀ T, AnalyticOnNhd ℂ (f T) {p | XiDom (Gb T) (compWeight L a₁) ν (k + 1) ε p.1 p.2}) ∧
      (∀ T, ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
        XiDom (Gb T) (compWeight L a₁) ν (k + 1) ε p.1 p.2 → ‖f T p‖ ≤ b T) ∧
      (∀ T, ∀ p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
        XiDom (Gb T) (compWeight L a₁) ν (k + 1) εloc p.1 p.2 →
        XiDom (Gb T) (compWeight L a₁) ν (k + 1) εloc p'.1 p'.2 →
        (∀ x ∈ Ypl T, p.1 x = p'.1 x ∧ p.2 x = p'.2 x) → f T p = f T p') ∧
      (∀ T, ∀ Q : Matrix (Fin N) (Fin N) ℝ, Qᵀ * Q = 1 →
        ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
        XiDom (Gb T) (compWeight L a₁) ν (k + 1) ε p.1 p.2 →
        f T (rotField (cmat Q) p.1, rotField (cmat Q) p.2) = f T p) ∧
      (∀ T (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
        XiDom S.G' (compWeight L a₁) ν (k + 1) ε q.1 q.2 → f T q = e (π (clipRaw S.G' q), 0) T) := by
  -- the parameter read from a pair of fields
  set θb : ∀ T, Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → physParamBg N (Gb T) :=
    fun T p => (πb T (clipRaw (Gb T) p), 0) with hθbdef
  have hθb1 : ∀ T {ε' : ℝ} (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      XiDom (Gb T) (compWeight L a₁) ν (k + 1) ε' p.1 p.2 →
      ((θb T p).1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) = clipRaw (Gb T) p := by
    intro T ε' p hp
    show ((πb T (clipRaw (Gb T) p) : rawSub N (Gb T)) : RawData d L (N₁ * L ^ m₁) (k + 1) N) = _
    rw [hπb T _ (clipRaw_mem_rawSub_of_xiDom hp)]
  have hθbX : ∀ T {ε' ε'' : ℝ} (hε' : ε' ≤ ε'')
      (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      XiDom (Gb T) (compWeight L a₁) ν (k + 1) ε' p.1 p.2 →
      ((θb T p).1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw (Gb T) (compWeight L a₁) ν (k + 1) 1 ε'' := by
    intro T ε' ε'' hε' p hp
    rw [hθb1 T p hp]
    exact clipRaw_mem_xiCRaw_of_xiDom hε' hp
  have hl1 : (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) ∈ l1Ball d L N₁ m₁ (k + 1) N := by
    show ∑ x, ∑ i, ‖(0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) x i‖ < 1
    simp
  have hθbV : ∀ T (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N),
      XiDom (Gb T) (compWeight L a₁) ν (k + 1) ε p.1 p.2 →
      θb T p ∈ physVBg N (Gb T) a₁ ν εan := fun T p hp => ⟨hθbX T hεan p hp, hl1⟩
  refine ⟨fun T p => if gate T then c T (θb T p) else 0, fun T => ?_, fun T p hp => ?_,
    fun T p p' hp hp' hag => ?_, fun T Q hQ p hp => ?_, fun T q hq => ?_⟩
  · -- (A1)
    by_cases hg : gate T
    · simp only [hg, ↓reduceIte]
      intro p hp
      have hθan : AnalyticAt ℂ (θb T) p := by
        have hA : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
            πb T (clipRaw (Gb T) p)) p :=
          ((πb T).comp (LinearMap.toContinuousLinearMap (clipRawL (N := N) (Gb T)))).analyticAt p
        exact hA.prod analyticAt_const
      exact (hc1 T hg (θb T p) (hθbV T p hp)).comp hθan
    · simp only [hg, ↓reduceIte]
      exact analyticOnNhd_const
  · -- (A2)
    by_cases hg : gate T
    · simp only [hg, ↓reduceIte]
      exact hc2 T hg _ (hθbV T p hp)
    · simp only [hg, ↓reduceIte, norm_zero]
      exact hb0 T
  · -- (A3)
    by_cases hg : gate T
    · simp only [hg, ↓reduceIte]
      refine hc3 T hg _ _ (hθbX T le_rfl p hp) (hθbX T le_rfl p' hp') rfl rfl fun x hx => ?_
      rw [hθb1 T p hp, hθb1 T p' hp']
      obtain ⟨h1, h2⟩ := hag x hx
      constructor
      · funext i
        simp only [clipRaw, h1]
      · funext i
        simp only [clipRaw, h2]
    · simp only [hg, ↓reduceIte]
  · -- (A4)
    by_cases hg : gate T
    · simp only [hg, ↓reduceIte]
      have hmem : rotRaw (cmat Q) (clipRaw (Gb T) p) ∈
          XiCRaw (Gb T) (compWeight L a₁) ν (k + 1) 1 εan :=
        rotRaw_mem hQ (clipRaw_mem_xiCRaw_of_xiDom hεan hp)
      have hrot : ((θb T (rotField (cmat Q) p.1, rotField (cmat Q) p.2)).1 :
          RawData d L (N₁ * L ^ m₁) (k + 1) N) = rotRaw (cmat Q) (clipRaw (Gb T) p) := by
        show ((πb T (clipRaw (Gb T) (rotField (cmat Q) p.1, rotField (cmat Q) p.2)) :
          rawSub N (Gb T)) : RawData d L (N₁ * L ^ m₁) (k + 1) N) = _
        rw [clipRaw_rot, hπb T _ (XiCRaw_subset_rawSub _ _ _ _ _ _ hmem)]
      have hmem' : ((θb T (rotField (cmat Q) p.1, rotField (cmat Q) p.2)).1 :
          RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw (Gb T) (compWeight L a₁) ν (k + 1) 1 εan := by
        rw [hrot]; exact hmem
      refine hc4 T hg Q hQ (θb T p) (hθbV T p hp) _ ⟨hmem', hl1⟩ ?_
      rw [hrot, hθb1 T p hp]
    · simp only [hg, ↓reduceIte]
  · -- (A5)
    by_cases hg : gate T
    · simp only [hg, ↓reduceIte]
      exact hc5 T hg q hq
    · simp only [hg, ↓reduceIte]
      exact (he0 T hg q hq).symm

end F

end Balaban.Inhabited
