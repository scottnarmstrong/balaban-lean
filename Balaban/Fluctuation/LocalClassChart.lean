/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.XiCRawOpenWitness
public import Balaban.Fluctuation.LocalPairCollar
public import Balaban.SmallField.GsSpecClass

/-!
# The class chart of the local successor terms

The terms of a class member are functions of a pair of fields `(Ψ, h)` on the fine torus,
analytic on the class domain `Ξ^c_j(𝔹; 1, ε_j)` (`XiDom`, the field `dom` of `xiFieldDom`).  The
terms recomputed on a local generating set `𝔹 = 𝔹_{k+1}(Y⁺)` (P3 (4.46)-(4.47), printed pp. 78-79)
are functions of the raw datum of `𝔹`, analytic on the chart `Ξ^c(𝔹; 1, ε')` of the expansion
(`XiCRaw`).  The two are related by the cut-off `clipRaw 𝔹` of a pair of fields outside the data
sites of `𝔹` (resp. outside `Ω₁(𝔹)` for `h`).

* `clipRaw_eq_rawOf_of_realizesC`, `clipRaw_mem_xiCRaw_of_xiDom`: **the chart nesting**.  A point
  of the class domain `Ξ^c_j(𝔹; 1, ε)` is cut off to a raw datum of `Ξ^c_j(𝔹; 1, ε')` for
  `ε ≤ ε'` (P3 (4.46): the class radius `ε_{k+1}` of the new terms is at most the radius `ε'` of
  the expansion, whose test (4.37) `ε' + (K₂ + 1) δ₃ ≤ ε_k` is the hypothesis of the engine).
* `analyticAt_clipRaw`, `analyticOnNhd_comp_clipRaw_of_xiDom`, `norm_comp_clipRaw_le_of_xiDom`:
  a function analytic (bounded) on the chart of the expansion gives, composed with the cut-off, a
  function analytic (bounded) on the class domain; `analyticOnNhd_comp_clipRaw_xiFieldDom`,
  `norm_comp_clipRaw_le_xiFieldDom`: the same in the form of the clauses `analyticE` and `boundE`
  of `SFTermClauses` for the field domain `xiFieldDom`.
* `localB_collar_gsSpecStrong_of_subset`, `localB_collar_gs_spec`: the clauses `gsStrong` and
  `gs_spec` for the generating set `𝔹_{k+1}(Y⁺)` of the polymer `Y` (from
  `localB_collar_gsSpecStrong` and `Y ⊆ Y⁺`).
* `supDist_of_mem_symGroupBy`, `collar_image_of_mem_pavingSymGroup`, `localB_collar_pavingGS`:
  the elements of the paving group are isometries of the sup-distance of sites, so the collar
  commutes with them, `(r Y)⁺ = r Y⁺`, and the clause `pavingGS` holds for `Y ↦ 𝔹_{k+1}(Y⁺)`
  (from `pavingGS_localB`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.LargeField

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ}

/-- The cut-off of a pair of fields realizing a datum `D` (on the data sites, resp. on `Ω₁`) is the
raw pair of `D`. -/
theorem clipRaw_eq_rawOf_of_realizesC {D : BgData G N}
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : CTorus d L N₁ m₁ k → Fin N → ℂ} (hR : RealizesC D Ψ₀ h₀ Ψ'' h'')
    {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N}
    (hΨ : ∀ x i, p.1 x i = (Ψ₀ x i : ℂ) + Ψ'' x i) (hh : ∀ x i, p.2 x i = (h₀ i : ℂ) + h'' x i) :
    clipRaw G p = rawOf D := by
  classical
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · show (if x ∈ dataSites G then p.1 x i else 0) = D.Ψ x i
    by_cases hx : x ∈ dataSites G
    · simp only [hx, ↓reduceIte]
      rw [hΨ x i, hR.1 x hx i]
    · simp only [hx, ↓reduceIte]
      rw [D.Ψ_zero x hx]; rfl
  · show (if x ∈ G.Ω 1 then p.2 x i else 0) = D.h x i
    by_cases hx : x ∈ G.Ω 1
    · simp only [hx, ↓reduceIte]
      rw [hh x i, hR.2 x hx i]
    · simp only [hx, ↓reduceIte]
      rw [D.h_zero x hx]; rfl

/-- **The chart nesting** (P3 (4.46)).  A pair of fields of the class domain
`Ξ^c_j(𝔹; 1, ε)` (`XiDom`) cut off outside the data sites of `𝔹` is a raw datum of the chart
`Ξ^c_j(𝔹; 1, ε')` of the expansion (`XiCRaw`) for every `ε' ≥ ε`: the datum is the complex datum
`D^c` of the witness of `XiDom`. -/
theorem clipRaw_mem_xiCRaw_of_xiDom {a : ℕ → ℝ} {ν ε ε' : ℝ} {j : ℕ} (hε : ε ≤ ε')
    {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N} (hp : XiDom G a ν j ε p.1 p.2) :
    clipRaw G p ∈ XiCRaw G a ν j 1 ε' := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hΨ, hh, hXi⟩ := hp
  obtain ⟨-, -, Dr, Dc, -, hC, -, -⟩ := id hXi
  refine ⟨Dc, ⟨Ψ₀, h₀, Ψ'', h'', ?_, hC⟩, clipRaw_eq_rawOf_of_realizesC hC hΨ hh⟩
  exact xiC_rescale_of_agree le_rfl (by simpa using hε) (fun _ _ _ => rfl) (fun _ _ _ => rfl) hXi

/-- The cut-off is linear in the pair of fields, hence analytic. -/
theorem analyticAt_clipRaw (p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N) :
    AnalyticAt ℂ (clipRaw (N := N) G) p := by
  classical
  refine AnalyticAt.prod (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
    (analyticAt_pi_iff.2 fun x => analyticAt_pi_iff.2 fun i => ?_)
  · by_cases hx : x ∈ dataSites G
    · simp only [hx, ↓reduceIte]
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt _).comp
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ k => Fin N → ℂ)
          x).analyticAt _).comp analyticAt_fst)
    · simp only [hx, ↓reduceIte]
      exact analyticAt_const
  · by_cases hx : x ∈ G.Ω 1
    · simp only [hx, ↓reduceIte]
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) i).analyticAt _).comp
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : CTorus d L N₁ m₁ k => Fin N → ℂ)
          x).analyticAt _).comp analyticAt_snd)
    · simp only [hx, ↓reduceIte]
      exact analyticAt_const

/-- **A function analytic on the chart of the expansion is analytic on the class domain after the
cut-off** (`ε ≤ ε'`, `clipRaw_mem_xiCRaw_of_xiDom`). -/
theorem analyticOnNhd_comp_clipRaw_of_xiDom {a : ℕ → ℝ} {ν ε ε' : ℝ} {j : ℕ} (hε : ε ≤ ε')
    {F : RawData d L (N₁ * L ^ m₁) k N → ℂ} (hF : AnalyticOnNhd ℂ F (XiCRaw G a ν j 1 ε')) :
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => F (clipRaw G p))
      {p | XiDom G a ν j ε p.1 p.2} := fun p hp =>
  (hF _ (clipRaw_mem_xiCRaw_of_xiDom hε hp)).comp (analyticAt_clipRaw p)

/-- **A bound on the chart of the expansion is a bound on the class domain after the cut-off.** -/
theorem norm_comp_clipRaw_le_of_xiDom {a : ℕ → ℝ} {ν ε ε' : ℝ} {j : ℕ} (hε : ε ≤ ε')
    {F : RawData d L (N₁ * L ^ m₁) k N → ℂ} {B : ℝ}
    (hF : ∀ r ∈ XiCRaw (N := N) G a ν j 1 ε', ‖F r‖ ≤ B)
    {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N} (hp : XiDom G a ν j ε p.1 p.2) :
    ‖F (clipRaw G p)‖ ≤ B :=
  hF _ (clipRaw_mem_xiCRaw_of_xiDom hε hp)

/-- **The clause `analyticE` for a term recomputed on a generating set `𝔹`**, field domain
`xiFieldDom a ν εseq`: the term `(Ψ, h) ↦ F(clipRaw 𝔹 (Ψ, h))` is analytic on the class domain
of level `j` over `𝔹` when `F` is analytic on the chart `Ξ^c_j(𝔹; 1, ε')`, `ε_j ≤ ε'`. -/
theorem analyticOnNhd_comp_clipRaw_xiFieldDom {a : ℕ → ℝ} {ν ε' : ℝ} {εseq : ℕ → ℝ} {j : ℕ}
    (hε : εseq j ≤ ε') {F : RawData d L (N₁ * L ^ m₁) k N → ℂ}
    (hF : AnalyticOnNhd ℂ F (XiCRaw G a ν j 1 ε')) :
    AnalyticOnNhd ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => F (clipRaw G p))
      {p | (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ k N ϱ).dom j G p.1 p.2} :=
  analyticOnNhd_comp_clipRaw_of_xiDom hε hF

/-- **The bound of a term recomputed on `𝔹` on the class domain** (form of the clause `boundE`,
field domain `xiFieldDom a ν εseq`, `ε_j ≤ ε'`). -/
theorem norm_comp_clipRaw_le_xiFieldDom {a : ℕ → ℝ} {ν ε' : ℝ} {εseq : ℕ → ℝ} {j : ℕ}
    (hε : εseq j ≤ ε') {F : RawData d L (N₁ * L ^ m₁) k N → ℂ} {B : ℝ}
    (hF : ∀ r ∈ XiCRaw (N := N) G a ν j 1 ε', ‖F r‖ ≤ B)
    {p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N}
    (hp : (xiFieldDom a ν εseq : FieldDom d L N₁ m₁ k N ϱ).dom j G p.1 p.2) :
    ‖F (clipRaw G p)‖ ≤ B :=
  norm_comp_clipRaw_le_of_xiDom hε hF hp

end Chart

section Spec

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱl : ℝ}

/-- **The clause `gsStrong` for the generating set `𝔹_{k+1}(Y⁺)` of the polymer `Y`**: the strong
specification of the local set holds for `Y` itself, since `Y ⊆ Y⁺` (`localB_collar_subset`) and
every field of `GsSpecStrong` is a statement about the sites of the polymer
(`localB_collar_gsSpecStrong`). -/
theorem localB_collar_gsSpecStrong_of_subset (hk : k + 1 ≤ k + 1)
    (hsep : ϱl ≤ minSep L (L ^ m₁)) {Y Yp : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁)) :
    GsSpecStrong (k + 1) hk Y (localB (k + 1) hk Yp hsep) := by
  have h := localB_collar_gsSpecStrong (Y := Y) hk hsep hYp
  have hsub := localB_collar_subset hYp
  exact { subset := fun z hz => h.subset (hsub hz)
          noAbove := h.noAbove
          topLayer := fun z hz => h.topLayer z (hsub hz)
          layerEq := fun z hz => h.layerEq z (hsub hz)
          blkEq := fun z hz => h.blkEq z (hsub hz) }

/-- **The clause `gs_spec` for the generating set `𝔹_{k+1}(Y⁺)` of the polymer `Y`**:
`Y ⊆ Ω₁(𝔹_{k+1}(Y⁺))` and no layer above `k + 1`. -/
theorem localB_collar_gs_spec (hk : k + 1 ≤ k + 1)
    (hsep : ϱl ≤ minSep L (L ^ m₁)) {Y Yp : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁)) :
    Y ⊆ ↑((localB (k + 1) hk Yp hsep).Ω 1) ∧
      ∀ i, k + 1 < i → (localB (k + 1) hk Yp hsep).Ω i = ∅ := by
  have h := localB_collar_gsSpecStrong_of_subset hk hsep hYp
  exact ⟨h.subset, h.noAbove⟩

end Spec

section Paving

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱl : ℝ}

omit [NeZero L] [NeZero N₁] in
/-- The translations of `symGroupBy` preserve the sup-distance of fine sites. -/
theorem supDist_transBy (s : ℕ) (μ : Fin d) (x y : CTorus d L N₁ m₁ k) :
    supDist (transBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ x)
      (transBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ y) = supDist x y := by
  have h : ∀ i, cycNorm (N₁ * L ^ m₁ * L ^ k)
      ((transBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ x) i -
        (transBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ y) i) =
      cycNorm (N₁ * L ^ m₁ * L ^ k) (x i - y i) := fun i => by
    simp [transBy]
  simp only [supDist, h]

/-- The reflections of `symGroupBy` preserve the sup-distance of fine sites. -/
theorem supDist_flipBy (s : ℕ) (μ : Fin d) (x y : CTorus d L N₁ m₁ k) :
    supDist (flipBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ x)
      (flipBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ y) = supDist x y := by
  have h : ∀ i, cycNorm (N₁ * L ^ m₁ * L ^ k)
      ((flipBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ x) i -
        (flipBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s μ y) i) =
      cycNorm (N₁ * L ^ m₁ * L ^ k) (x i - y i) := fun i => by
    by_cases hi : i = μ
    · subst hi
      simp only [flipBy, Equiv.coe_fn_mk, Function.update_self]
      rw [show (s : ZMod (N₁ * L ^ m₁ * L ^ k)) - 1 - x i - ((s : ZMod _) - 1 - y i) =
        y i - x i by ring]
      exact cycNorm_sub_comm _ _
    · simp only [flipBy, Equiv.coe_fn_mk, Function.update_of_ne hi]
  simp only [supDist, h]

omit [NeZero L] [NeZero N₁] in
/-- The coordinate exchanges of `symGroupBy` preserve the sup-distance of fine sites. -/
theorem supDist_swapJ (μ ν : Fin d) (x y : CTorus d L N₁ m₁ k) :
    supDist (swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν x)
      (swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν y) = supDist x y := by
  refine le_antisymm (supDist_le_iff.2 fun i => ?_) (supDist_le_iff.2 fun i => ?_)
  · exact cycNorm_le_supDist x y (Equiv.swap μ ν i)
  · have := cycNorm_le_supDist (swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν x)
      (swapJ (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) μ ν y) (Equiv.swap μ ν i)
    simpa [swapJ] using this

/-- **The elements of `symGroupBy s` are isometries of the sup-distance of fine sites.** -/
theorem supDist_of_mem_symGroupBy {s : ℕ} {g : Equiv.Perm (CTorus d L N₁ m₁ k)}
    (hg : g ∈ symGroupBy (N₁ := N₁) (m₁ := m₁) (k := k) (L := L) s) (x y : CTorus d L N₁ m₁ k) :
    supDist (g x) (g y) = supDist x y := by
  unfold symGroupBy at hg
  induction hg using Subgroup.closure_induction generalizing x y with
  | mem g hg =>
    rcases hg with (⟨μ, rfl⟩ | ⟨μ, rfl⟩) | ⟨μ, ν, rfl⟩
    · exact supDist_transBy s μ x y
    · exact supDist_flipBy s μ x y
    · exact supDist_swapJ μ ν x y
  | one => rfl
  | mul a b _ _ h1 h2 => rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, h2]
  | inv a _ h =>
    have := h (a⁻¹ x) (a⁻¹ y)
    simpa using this.symm

/-- **The collar commutes with the paving symmetries**: for `r` in the paving group of level
`k + 1`, the collar `(r Y)⁺` (the `𝒞_{k+1}`-cubes meeting the closed `2 M₁ L^{k+1}`-neighbourhood of
`r Y`) is `r Y⁺`.  `r` preserves the sup-distance of sites (`supDist_of_mem_symGroupBy`) and the
`𝒞_{k+1}`-cubes (`localCube_of_mem_symGroupBy`). -/
theorem collar_image_of_mem_pavingSymGroup {m₀ : ℕ} {r : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    {Y Yp Yp' : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hYp' : ∀ z, z ∈ Yp' ↔ ∃ x ∈ r '' Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁)) :
    Yp' = r '' Yp := by
  have hcube : ∀ x y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast (r x) : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast (r y) : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ↔
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast x : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) := fun x y => by
    rw [← supDist_eq_zero, localCube_of_mem_symGroupBy (s := cellSide L m₀ m₁ (k + 1))
      (fun n hn => pow_dvd_pow L (by omega)) le_rfl hr le_rfl x y, supDist_eq_zero]
  have hdist : ∀ x y : CTorus d L N₁ m₁ (k + 1), supDist (r x) (r y) = supDist x y :=
    supDist_of_mem_symGroupBy hr
  ext z
  rw [hYp', Set.mem_image_equiv]
  constructor
  · rintro ⟨x, ⟨x0, hx0, rfl⟩, y, hcy, hd⟩
    refine (hYp _).2 ⟨x0, hx0, r.symm y, ?_, ?_⟩
    · rw [← hcube, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hcy
    · rw [← hdist, Equiv.apply_symm_apply]; exact hd
  · intro hz
    obtain ⟨x0, hx0, y0, hcy, hd⟩ := (hYp _).1 hz
    refine ⟨r x0, ⟨x0, hx0, rfl⟩, r y0, ?_, ?_⟩
    · have := (hcube y0 (r.symm z)).2 hcy
      rwa [Equiv.apply_symm_apply] at this
    · rw [hdist]; exact hd

/-- **The clause `pavingGS` for the generating sets `Y ↦ 𝔹_{k+1}(Y⁺)`**: for `r` in the paving
group of level `k + 1`, `Ω_n(𝔹_{k+1}((r Y)⁺)) = r Ω_n(𝔹_{k+1}(Y⁺))` (`collar_image_of_mem_pavingSymGroup`
and `pavingGS_localB`). -/
theorem localB_collar_pavingGS (hk : k + 1 ≤ k + 1) (hsep : ϱl ≤ minSep L (L ^ m₁)) {m₀ : ℕ}
    {r : Equiv.Perm (CTorus d L N₁ m₁ (k + 1))}
    (hr : r ∈ pavingSymGroup (N₁ := N₁) (m₁ := m₁) (k := k + 1) (d := d) L m₀ (k + 1))
    {Y Yp Yp' : Set (CTorus d L N₁ m₁ (k + 1))}
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hYp' : ∀ z, z ∈ Yp' ↔ ∃ x ∈ r '' Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁)) (n : ℕ) :
    (((localB (k + 1) hk Yp' hsep).Ω n : Finset (CTorus d L N₁ m₁ (k + 1))) :
        Set (CTorus d L N₁ m₁ (k + 1))) =
      r '' (((localB (k + 1) hk Yp hsep).Ω n : Finset (CTorus d L N₁ m₁ (k + 1))) :
        Set (CTorus d L N₁ m₁ (k + 1))) := by
  rw [collar_image_of_mem_pavingSymGroup hr hYp hYp']
  exact pavingGS_localB hr n

end Paving

end Balaban.Localization
