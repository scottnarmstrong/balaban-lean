/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairCollar
public import Balaban.Fluctuation.LocalPairHatLift
public import Balaban.Fluctuation.LocalClassLatTau
public import Balaban.Fluctuation.LocalSetDetFlCore
public import Balaban.SmallField.LocalGeneratorRestriction
public import Balaban.Fluctuation.BgTransportReads

/-!
# The local generating sets of the new level in the replacement theory (`LocalPairCast`)

The replacement of P3 pp. 78-79 (`LocalPairDepth`, `LocalPairLevelInner`, `LocalPairHatLift`,
`LocalPairCollar`, `LocalClassTau`) is stated for the literal local generator
`𝔹_{k+1}(Y) = localB (k + 1) … Y` at the cube size `M₁ = L^{m₁}` of the step torus.  The local
generating set of a label polymer of the new level is `castG hc (localB (k + 1) … Y' hsep)`: the set
`𝔹_{k+1}(Y')` of the torus `(N₁', m₁')`, `N₁' L^{m₁'} = N₁ L^{m₁}`, `m₁ ≤ m₁'`,
`ϱ ≤ minSep L L^{m₁'}`, transported to the step torus.

Every theorem of those files is now a statement for an arbitrary generating set `Gl` (the cores
`level_layer_iff_of_mem_top`, `level_mem_cubeIdx_iff_of_mem_top`, `level_inner_cross`,
`level_active_cross`, `level_dich_cross`, `level_row_cross`, `hatBox_top_of_active`,
`hat_of_active`, `tau_off_top`, `tau_top`, `tau_norm_lt`, `topLayer_of_near`, `topLayer_of_mem`,
`depth_deep`, `depth_res_fl`, `depth_act`, `depth_approxDep`, `depth_compose`, `drop_Ω_one_of_mem`,
`drop_layer_iff_of_top`, `replacement_coverBases`, `core_mem_of_active`, `localHatLift_eq_hatPsiF`,
`collar_margin_of_top`, `tauExt_*`), whose hypotheses on `Gl` are only: the sup-separation
`SupSep Gl m₁`, the cube alignment `CubeAligned Gl m₁` (or the cell condition on the top layer), the
dropped set `Gd` with the layers of `Gl` up to `k` and no layer `k + 1`, and the margin; the landed
`localB` statements are their instances.  Here the hypotheses are verified for the cast sets:

* `castG_localB_top_sameCell`: the top layer of `castG hc (localB (k + 1) … Y' hsep)` is the set of
  sites whose cell of side `L^{k+1+m₁'}` lies in `Y'` (read through the cast);
* `castG_localB_supSep`, `castG_localB_cubeAligned`, `castG_localB_top_union`: sup-separation,
  cube alignment and the cell condition at the step's cube size `m₁ ≤ m₁'`;
* `castG_localB_drop_Ω`: the layers `n ≤ k` of the fluctuation set
  `castG hc (localB k … Ω_k(𝔹_{k+1}(Y')))` are those of `𝔹_{k+1}(Y')`
  (`castG_localB_drop_top`, of `LocalSetDetFlCore`, gives that it has no layer `k + 1`);
* `castG_localB_collar_margin`: the margin of the replacement from `R ⊆ Y` for the cast set built on
  the collar `Y'⁺` of the transported label;
* `castG_localB_tauExt_eq_one`: `hσ1` for the cast set;
* `BgTransport.canon_gdat_eq_levelRestrict`, `canon_gdat_xiCData`, `castG_canon_gdat_xiCData`,
  `canon_gdat_xiCData_of_xiCData`, `canon_gdat_eq_of_mem_one`: the datum read by the canonical
  transport is the restriction of the step's datum, lies in the chart of any generating set `Gb`
  (in particular of the cast set) at the radius `(2 K₁ + 2) C₁ ε` when the step's datum lies in the
  step chart of radius `ε`, and agrees with the step's datum on `Ω₁(Gb)`;
* `castG_localB_xiDom_of_ambient_xiDom`: the chart of the step restricts to the chart of the cast set
  (the radius loss `c₀ + (2 K₁ + 1) c₁` of the recomputation of the backgrounds is explicit).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.SmallField.Def6 Balaban.Fluctuation

section CastSets

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {N₁' m₁' : ℕ} [NeZero N₁'] {ϱ ϱ' : ℝ}

omit [NeZero N₁] [NeZero L] [NeZero N₁'] in
/-- Cells are read on the values of the coordinates, so the cast of tori of the same side
preserves them. -/
theorem sameCell_torusCast_iff {a n n' : ℕ} [NeZero n] (h : n = n') (x y : Torus d n) :
    SameCell a (torusCast x : Torus d n') (torusCast y : Torus d n') ↔ SameCell a x y := by
  unfold SameCell
  simp only [torusCast_val h]

/-- **The top layer of the cast local generating set** (P3 (4.4)): a site of the step torus lies in
`Ω_{k+1}(castG hc (𝔹_{k+1}(Y')))` iff every site of its cell of side `L^{k+1+m₁'}` has its image in
`Y'` (`Y'` a set of the torus `(N₁', m₁')`). -/
theorem castG_localB_top_sameCell (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    (hk : k + 1 ≤ k + 1) (Y' : Set (CTorus d L N₁' m₁' (k + 1)))
    (hsep : ϱ ≤ minSep L (L ^ m₁')) (x : CTorus d L N₁ m₁ (k + 1)) :
    x ∈ (castG hc (localB (k + 1) hk Y' hsep)).Ω (k + 1) ↔
      ∀ w : CTorus d L N₁ m₁ (k + 1), SameCell (L ^ (k + 1 + m₁')) w x →
        (torusCast w : CTorus d L N₁' m₁' (k + 1)) ∈ Y' := by
  have hceq : N₁ * L ^ m₁ * L ^ (k + 1) = N₁' * L ^ m₁' * L ^ (k + 1) := by rw [hc]
  rw [mem_castG_Ω, mem_localB_Ω_top_sameCell]
  constructor
  · intro h w hw
    exact h _ ((sameCell_torusCast_iff hceq w x).2 hw)
  · intro h w hw
    have hw' : SameCell (L ^ (k + 1 + m₁')) (torusCast w : CTorus d L N₁ m₁ (k + 1))
        (torusCast (torusCast x : CTorus d L N₁' m₁' (k + 1)) : CTorus d L N₁ m₁ (k + 1)) :=
      (sameCell_torusCast_iff hceq.symm w _).2 hw
    rw [torusCast_torusCast hceq] at hw'
    have := h _ hw'
    rwa [torusCast_torusCast hceq.symm] at this

/-- **The cast local generating set is sup-separated at the step's cube size** (`m₁ ≤ m₁'`). -/
theorem castG_localB_supSep (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm : m₁ ≤ m₁') {j : ℕ}
    (hj : j ≤ k + 1) (X' : Set (CTorus d L N₁' m₁' (k + 1))) (hsep : ϱ ≤ minSep L (L ^ m₁')) :
    SupSep (castG hc (localB j hj X' hsep)) m₁ :=
  supSep_of_le (supSep_castG hc (localB_supSep hj X' hsep)) hm

/-- **The cast local generating set is cube aligned at the step's cube size** (`2 ≤ m₁ ≤ m₁'`). -/
theorem castG_localB_cubeAligned (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hm : m₁ ≤ m₁') {j : ℕ} (hj : j ≤ k + 1) (X' : Set (CTorus d L N₁' m₁' (k + 1)))
    (hsep : ϱ ≤ minSep L (L ^ m₁')) :
    CubeAligned (castG hc (localB j hj X' hsep)) m₁ :=
  cubeAligned_of_le (cubeAligned_castG hc (localB_cubeAligned hj X' hsep (by omega))) hm₁ hm
    (dvd_mul_left _ _)

/-- **The top layer of the cast local generating set is a union of cells of side
`L^{k+1+m₁}`.** -/
theorem castG_localB_top_union (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hm : m₁ ≤ m₁') (hk : k + 1 ≤ k + 1) (X' : Set (CTorus d L N₁' m₁' (k + 1)))
    (hsep : ϱ ≤ minSep L (L ^ m₁')) (x y : CTorus d L N₁ m₁ (k + 1))
    (hxy : SameCell (L ^ (k + 1 + m₁)) x y) :
    x ∈ (castG hc (localB (k + 1) hk X' hsep)).Ω (k + 1) ↔
      y ∈ (castG hc (localB (k + 1) hk X' hsep)).Ω (k + 1) :=
  (castG_localB_cubeAligned hc hm₁ hm hk X' hsep).union (k + 1) (by omega) le_rfl x y hxy

/-- **The layers `n ≤ k` of the cast fluctuation set are those of the cast local generating set**:
`𝔹_k(Y') = castG hc (localB k … Ω_k(𝔹_{k+1}(Y')))` and `𝔹_{k+1}(Y')` have the same layers up to
`k`. -/
theorem castG_localB_drop_Ω (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hA : k + 1 ≤ k + 1)
    (hB : k ≤ k + 1) (X' : Set (CTorus d L N₁' m₁' (k + 1))) (hsep : ϱ ≤ minSep L (L ^ m₁'))
    (hsep' : ϱ' ≤ minSep L (L ^ m₁')) {n : ℕ} (hn : n ≤ k) :
    (castG hc (localB k hB (↑((localB (k + 1) hA X' hsep).Ω k) :
        Set (CTorus d L N₁' m₁' (k + 1))) hsep')).Ω n =
      (castG hc (localB (k + 1) hA X' hsep)).Ω n := by
  ext x
  rw [mem_castG_Ω, mem_castG_Ω, localB_drop_Ω hA hB X' hsep hsep' hn]

/-- **The margin of the replacement for the cast set built on the collar.**  Let `Y` be a label of
the step torus, `Y'` its image on the torus `(N₁', m₁')` (`hY'`) and `Yp'` the collar of `Y'` there
(`hYp'`: `z ∈ Yp'` iff a site of `Y'` is within sup-distance `2 L^{k+1+m₁'}` of a site of the
`𝒞_{k+1}`-cube of `z`).  For `m₁ ≤ m₁'` and a read region `R ⊆ Y`, every site within sup-distance
`2 L^{k+1+m₁}` of `R` lies in the top layer of `castG hc (𝔹_{k+1}(Yp'))`: the hypothesis `hmar` of
the replacement lemmas for the cast set. -/
theorem castG_localB_collar_margin (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm : m₁ ≤ m₁')
    (hk : k + 1 ≤ k + 1) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    {Y' Yp' : Set (CTorus d L N₁' m₁' (k + 1))} (hsep : ϱ ≤ minSep L (L ^ m₁'))
    (hY' : ∀ x' : CTorus d L N₁' m₁' (k + 1),
      x' ∈ Y' ↔ (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ Y)
    (hYp' : ∀ z, z ∈ Yp' ↔ ∃ x ∈ Y', ∃ y : CTorus d L N₁' m₁' (k + 1),
      fineCubeIdx (L ^ m₁') N₁' L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁' * N₁' * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁') N₁' L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁' * N₁' * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁'))
    {R : Finset (CTorus d L N₁ m₁ (k + 1))} (hRY : ∀ x ∈ R, x ∈ Y) :
    ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) →
      y ∈ (castG hc (localB (k + 1) hk Yp' hsep)).Ω (k + 1) := by
  have hceq : N₁ * L ^ m₁ * L ^ (k + 1) = N₁' * L ^ m₁' * L ^ (k + 1) := by rw [hc]
  refine collar_margin_of_top (Y := Y) (Yp := {w | (torusCast w : CTorus d L N₁' m₁' (k + 1)) ∈ Yp'})
    hm (castG_localB_top_sameCell hc hk Yp' hsep) (fun z => ?_) hRY
  show (torusCast z : CTorus d L N₁' m₁' (k + 1)) ∈ Yp' ↔ _
  rw [hYp']
  constructor
  · rintro ⟨x', hx', y', hfc, hd⟩
    refine ⟨torusCast x', (hY' x').1 hx', torusCast y', ?_, ?_⟩
    · have h1 := (fineCubeIdx_top_iff_sameCell (d := d) (L := L) (N₁ := N₁') (m₁ := m₁') (k := k)
        y' (torusCast z)).1 hfc
      have h2 := (sameCell_torusCast_iff hceq.symm y' (torusCast z : CTorus d L N₁' m₁' (k + 1))).2 h1
      rwa [torusCast_torusCast hceq] at h2
    · rwa [supDist_torusCast_val hceq.symm]
  · rintro ⟨x, hx, y, hy, hd⟩
    refine ⟨torusCast x, ?_, torusCast y, ?_, ?_⟩
    · rw [hY']; rwa [torusCast_torusCast hceq]
    · refine (fineCubeIdx_top_iff_sameCell (d := d) (L := L) (N₁ := N₁') (m₁ := m₁') (k := k)
        (torusCast y) (torusCast z)).2 ?_
      exact (sameCell_torusCast_iff hceq y z).2 hy
    · rwa [supDist_torusCast_val hceq]

/-- **`hσ1` for the cast set**: `τ (extParams 𝔹_{k+1} X₁ w)` is `1` at every cube of the cover of
`castG hc (𝔹_{k+1}(Yp'))` contained in `X₁f`, for `X₁f ⊆ X₁` and `X₁f ⊆ Y` (`𝔹_{k+1}` a level
set, `Yp'` the collar of the image `Y'` of `Y`).  The instance of `tauExt_eq_one` at the margin
`castG_localB_collar_margin`. -/
theorem castG_localB_tauExt_eq_one {ϱp : ℝ} {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱp}
    (hG' : IsLevel Gp (k + 1)) (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hm : m₁ ≤ m₁')
    (hk : k + 1 ≤ k + 1) {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    {Y' Yp' : Set (CTorus d L N₁' m₁' (k + 1))} (hsep : ϱ ≤ minSep L (L ^ m₁'))
    (hY' : ∀ x' : CTorus d L N₁' m₁' (k + 1),
      x' ∈ Y' ↔ (torusCast x' : CTorus d L N₁ m₁ (k + 1)) ∈ Y)
    (hYp' : ∀ z, z ∈ Yp' ↔ ∃ x ∈ Y', ∃ y : CTorus d L N₁' m₁' (k + 1),
      fineCubeIdx (L ^ m₁') N₁' L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁' * N₁' * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁') N₁' L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁' * N₁' * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁'))
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hX₁f : ∀ x ∈ X₁f, x ∈ X₁) (hX₁Y : ∀ x ∈ X₁f, x ∈ Y) :
    ∀ (w : ParIdx Gp X₁ → ℂ) (P : ℕ × CTorus d L N₁ m₁ (k + 1))
      (hP : P ∈ (coverOf (castG hc (localB (k + 1) hk Yp' hsep))).cubeIdx),
      P ∉ (coverOf (castG hc (localB (k + 1) hk Yp' hsep))).parCubes X₁f →
      (fun P : ↥(coverOf (castG hc (localB (k + 1) hk Yp' hsep))).cubeIdx =>
          if P.1.2 ∈ (castG hc (localB (k + 1) hk Yp' hsep)).Ω (k + 1) then
            Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0) ⟨P, hP⟩ = 1 :=
  tauExt_eq_one hG' hX₁f fun x hx => castG_localB_collar_margin hc hm hk hsep hY' hYp'
    (R := X₁f) hX₁Y x hx x (by rw [supDist_self]; exact Nat.zero_le _)

/-- **The chart of the step restricts to the chart of the cast local generating set** (P3 (4.44)-(4.47),
`localB_xiDom_of_ambient_xiDom` for `castG hc (localB (k + 1) … Y' hsep)`): a pair of fields in the
chart `Ξ^c_{k+1}(Gp; 1, ε)` of the step's level set lies in the chart of the cast set of radius
`ε_loc` once `ε_loc ≥ c₀ + (2 K₁ + 1) c₁` (the explicit loss of the recomputation of the
backgrounds on `Gb`). -/
theorem castG_localB_xiDom_of_ambient_xiDom {ϱp : ℝ} {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱp}
    (hG : IsLevel Gp (k + 1)) (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hk : k + 1 ≤ k + 1)
    (Y' : Set (CTorus d L N₁' m₁' (k + 1))) (hsep : ϱ ≤ minSep L (L ^ m₁')) {N : ℕ}
    {A : ℕ → ℝ} {μ εamb εloc : ℝ} (H : BgHyp d L (k + 1) ϱ A μ) (hμ : 0 ≤ μ)
    (hbudget : bgC0 d L N + (2 * bgK1 d L N + 1) * bgC1 d L N ≤ εloc)
    {Ψ h : Fld d L N₁ m₁ (k + 1) N} (hAmb : XiDom Gp A μ (k + 1) εamb Ψ h) :
    XiDom (castG hc (localB (k + 1) hk Y' hsep)) A μ (k + 1) εloc Ψ h :=
  xiDom_of_ambient_xiDom_of_isLevel hG (Nat.le_add_left 1 k) le_rfl
    (castG hc (localB (k + 1) hk Y' hsep)).top H hμ hbudget hAmb

/-- **The datum of `Gb` read by the canonical transport is the restriction of the step's datum**:
`(BgTransport.canon Gp Gb N).gdat D = levelRestrict D` for a level set `Gp` (of level `k + 1`) and
any generating set `Gb` of the same torus. -/
theorem BgTransport.canon_gdat_eq_levelRestrict {ϱp ϱb : ℝ} {N : ℕ}
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱp}
    {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} (hG : IsLevel Gp (k + 1))
    (D : BgData Gp N) :
    (BgTransport.canon Gp Gb N).gdat (BgTransport.reads_canon hG) D =
      levelRestrict hG (Nat.le_add_left 1 k) le_rfl Gb.top D := by
  classical
  refine BgData.eq_of_raw ?_
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · by_cases hx : x ∈ dataSites Gb <;>
      simp [BgTransport.gdat, BgTransport.canon, bgOfRaw, clipRawL, clipRaw, levelRestrict,
        BgData.clip, rawOf, hx]
  · by_cases hx : x ∈ Gb.Ω 1 <;>
      simp [BgTransport.gdat, BgTransport.canon, bgOfRaw, clipRawL, clipRaw, levelRestrict,
        BgData.clip, rawOf, hx]

/-- **The datum read by the canonical transport lies in the chart of `Gb`** (any generating set
`Gb` of the torus).  For a datum `D` of the step in the data domain `InDomainC` (at `δ ≤ ε`) of the
level set `Gp`, the datum `(BgTransport.canon Gp Gb N).gdat D` lies in the chart
`Ξ^c_{k+1}(Gb; 1, ε_b)` for `ε + (2 K₁ + 1) δ ≤ ε_b` (`xiCData_levelRestrict`; the radius loss of the
recomputation of the backgrounds is explicit). -/
theorem canon_gdat_xiCData {ϱp ϱb : ℝ} {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱp}
    {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} (hG : IsLevel Gp (k + 1)) {N : ℕ}
    {A : ℕ → ℝ} {μ δ ε εb : ℝ} (H : BgHyp d L (k + 1) ϱb A μ) (hμ : 0 ≤ μ) (hδ0 : 0 < δ)
    (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδc : δ ≤ bgC1 d L N)
    (hμε : μ * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (hεb : ε + (2 * bgK1 d L N + 1) * δ ≤ εb) (D : BgData Gp N) (hD : InDomainC Gp μ δ ε D) :
    XiCData Gb A μ (k + 1) 1 εb
      ((BgTransport.canon Gp Gb N).gdat (BgTransport.reads_canon hG) D) := by
  rw [BgTransport.canon_gdat_eq_levelRestrict hG]
  exact xiCData_levelRestrict hG (Nat.le_add_left 1 k) le_rfl Gb.top H hμ hδ0 hδε hε hδc hμε hεb D
    hD

/-- **The datum read by a term on the cast local generating set lies in its chart.**  For a datum
`D` of the step in the data domain `InDomainC` (at `δ ≤ ε`) of the level set `Gp`, the datum
`(BgTransport.canon Gp Gb N).gdat D` of `Gb = castG hc (localB (k + 1) … Y' hsep)` lies in the chart
`Ξ^c_{k+1}(Gb; 1, ε_b)` for `ε + (2 K₁ + 1) δ ≤ ε_b` (the instance `Gb = castG …` of
`canon_gdat_xiCData`). -/
theorem castG_canon_gdat_xiCData {ϱp : ℝ} {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱp}
    (hG : IsLevel Gp (k + 1)) (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁) (hk : k + 1 ≤ k + 1)
    (Y' : Set (CTorus d L N₁' m₁' (k + 1))) (hsep : ϱ ≤ minSep L (L ^ m₁')) {N : ℕ}
    {A : ℕ → ℝ} {μ δ ε εb : ℝ} (H : BgHyp d L (k + 1) ϱ A μ) (hμ : 0 ≤ μ) (hδ0 : 0 < δ)
    (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδc : δ ≤ bgC1 d L N)
    (hμε : μ * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (hεb : ε + (2 * bgK1 d L N + 1) * δ ≤ εb) (D : BgData Gp N) (hD : InDomainC Gp μ δ ε D) :
    XiCData (castG hc (localB (k + 1) hk Y' hsep)) A μ (k + 1) 1 εb
      ((BgTransport.canon Gp (castG hc (localB (k + 1) hk Y' hsep)) N).gdat
        (BgTransport.reads_canon hG) D) :=
  canon_gdat_xiCData hG H hμ hδ0 hδε hε hδc hμε hεb D hD

/-- **The radius of the read datum, for any generating set `Gb`** (P3 (4.44)-(4.47)): for a datum
`D` of the chart `Ξ^c_{k+1}(Gp; 1, ε)` of the step's level set, the datum of `Gb` read by the
canonical transport lies in the chart `Ξ^c_{k+1}(Gb; 1, ε′)` for every `ε′ ≥ (2 K₁ + 2) C₁ ε` (the
data domain `Ψ̃^c(C₁ ε, C₁ ε)` of the chart, `xiCData_inDomainC`, restricted to `Gb`, and the
backgrounds recomputed on `Gb`, `canon_gdat_xiCData`). -/
theorem canon_gdat_xiCData_of_xiCData {ϱp ϱb : ℝ}
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱp}
    {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} (hG : IsLevel Gp (k + 1)) {N : ℕ}
    {a₁ ν ε ε' : ℝ} (HBp : BgHyp d L (k + 1) ϱp (compWeight L a₁) ν)
    (H : BgHyp d L (k + 1) ϱb (compWeight L a₁) ν) (hε : 0 < ε)
    (hsmall : (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1) (hc0 : xiC1 d * ε ≤ bgC0 d L N)
    (hc1 : xiC1 d * ε ≤ bgC1 d L N) (hε' : (2 * bgK1 d L N + 2) * xiC1 d * ε ≤ ε')
    (D : BgData Gp N) (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 ε D) :
    XiCData Gb (compWeight L a₁) ν (k + 1) 1 ε'
      ((BgTransport.canon Gp Gb N).gdat (BgTransport.reads_canon hG) D) := by
  have hDom := xiCData_inDomainC HBp hsmall hD
  have hδ0 : 0 < xiC1 d * ε := mul_pos (lt_of_lt_of_le one_pos (one_le_xiC1 d)) hε
  have hμε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * ε) ^ 2 ≤ (xiC1 d * ε) ^ 2 := by
    have := HBp.massLe
    nlinarith [sq_nonneg (xiC1 d * ε)]
  exact canon_gdat_xiCData hG H HBp.mass hδ0 le_rfl hc0 hc1 hμε (by nlinarith) D hDom

/-- **The read datum agrees with the datum of the step on the first domain of `Gb`** (both
fields; `Ω₁(Gb)` lies in the data sites of `Gb`). -/
theorem canon_gdat_eq_of_mem_one {ϱp ϱb : ℝ} {N : ℕ}
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱp}
    {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb} (hG : IsLevel Gp (k + 1))
    (D : BgData Gp N) {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ Gb.Ω 1) :
    D.Ψ x = ((BgTransport.canon Gp Gb N).gdat (BgTransport.reads_canon hG) D).Ψ x ∧
      D.h x = ((BgTransport.canon Gp Gb N).gdat (BgTransport.reads_canon hG) D).h x := by
  rw [BgTransport.canon_gdat_eq_levelRestrict hG]
  exact ⟨(levelRestrict_Ψ hG (Nat.le_add_left 1 k) le_rfl Gb.top D
      ((mem_dataSites _).2 (Or.inl hx))).symm,
    (levelRestrict_h hG (Nat.le_add_left 1 k) le_rfl Gb.top D hx).symm⟩

end CastSets

end Balaban.Localization
