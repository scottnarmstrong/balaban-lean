/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2BackgroundLocal
public import Balaban.Localization.Decoupled2XAnalytic

/-!
# The instance `C = H`: the landed decoupled layer is the generalized one

For a generating set `G` with the standing hypotheses `DGSetting G a ν` the pair `(coverOf G, G)` is
`CoverLocal` (`coverLocal_self`, with `Kc = selfKc d L`, the constant of the landed (NC3) for the
cube operators, and `Cx = Cchi d L`), and the generalized objects at `C = H` are the landed ones
by definition (`Gs_self` etc.).  Hence the generalized theorems at `coverOf G` are statements about
the landed objects; `dg2_sup_self` and `i4a_local_self` recover the landed statements from the
generalized ones.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-! ### The generalized objects at `C = H` are the landed ones -/

theorem DecParams_self : DecParams (coverOf G) = Balaban.Localization.DecParams G := rfl

theorem extS_self (s : Balaban.Localization.DecParams G) :
    extS (coverOf G) s = Balaban.Localization.extS G s := rfl

theorem sProd_self (s : ℕ × CTorus d L N₁ m₁ K → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) :
    (coverOf G).sProd s q = Balaban.Localization.sProd G s q := rfl

theorem Qset_self (q : ℕ × CTorus d L N₁ m₁ K) :
    (coverOf G).Qset q = Balaban.Localization.Qset G q := rfl

theorem parCubes_self (X₁ : Finset (CTorus d L N₁ m₁ K)) :
    (coverOf G).parCubes X₁ = Balaban.Localization.parCubes G X₁ := rfl

theorem chiD_self (q : ℕ × CTorus d L N₁ m₁ K) :
    chiD (coverOf G) G q = Balaban.Localization.chiD G q := rfl

theorem Kz_self (a : ℕ → ℝ) (ν : ℝ) (q : ℕ × CTorus d L N₁ m₁ K) :
    Kz (coverOf G) G a ν q = Balaban.Localization.Kz G a ν q := rfl

theorem Gstar_self (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ K → ℂ) :
    Gstar (coverOf G) G a ν α s = Balaban.Localization.Gstar G a ν α s := rfl

theorem Kcal_self (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ K → ℂ) :
    Kcal (coverOf G) G a ν α s = Balaban.Localization.Kcal G a ν α s := rfl

/-- **`Gs (coverOf G) G = Gs G`**: the decoupled Green's operator of the cover of `G` and the
operator of `G` is the landed one. -/
theorem Gs_self (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ K → ℂ) :
    Gs (coverOf G) G a ν α s = Balaban.Localization.Gs G a ν α s := rfl

theorem decG_self (a : ℕ → ℝ) (ν : ℝ) (s : Balaban.Localization.DecParams G) :
    decG (coverOf G) G a ν s = Balaban.Localization.decG G a ν s := rfl

theorem HatConn_self : HatConn (coverOf G) G ↔ Balaban.Localization.HatConn G := Iff.rfl

theorem Zs_self (s : ℕ × CTorus d L N₁ m₁ K → ℂ) :
    Zs (coverOf G) s = Balaban.Localization.Zs G s := rfl

theorem Yreg_self (s : ℕ × CTorus d L N₁ m₁ K → ℂ) :
    Yreg (coverOf G) G s = Balaban.Localization.Yreg G s := rfl

theorem Core_self (s : ℕ × CTorus d L N₁ m₁ K → ℂ) :
    Core (coverOf G) s = Balaban.Localization.Core G s := rfl

theorem ZY_self (X₁ : Finset (CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))
    (Y : Finset (CTorus d L N₁ m₁ K)) :
    ZY (coverOf G) G X₁ 𝒞 Y = Balaban.Localization.ZY G X₁ 𝒞 Y := rfl

theorem SY_self (X₁ : Finset (CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))
    (Y : Finset (CTorus d L N₁ m₁ K)) :
    SY (coverOf G) G X₁ 𝒞 Y = Balaban.Localization.SY G X₁ 𝒞 Y := rfl

theorem Gdiff_self (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ K → ℂ)
    (f : G.Ω 1 → ℂ) (y : CTorus d L N₁ m₁ K) :
    Gdiff (coverOf G) G a ν α s f y = Balaban.Localization.Gdiff G a ν α s f y := rfl

/-! ### `coverLocal_self` -/

open Classical in
/-- The constant of the landed (NC3) for the cube operators (`cubeBlockBounds_exists`). -/
noncomputable def selfKc (d L : ℕ) [NeZero L] : ℝ :=
  if h : 3 ≤ d ∧ 3 ≤ L then Classical.choose (cubeBlockBounds_exists (d := d) (L := L) h.1 h.2)
  else 0

theorem selfKc_nonneg {d L : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) : 0 ≤ selfKc d L := by
  unfold selfKc
  split_ifs with h
  · exact (Classical.choose_spec (cubeBlockBounds_exists (d := d) (L := L) h.1 h.2)).1
  · exact absurd ⟨hd, hL⟩ h

theorem selfKc_spec {d L : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) {N₁ m₁ K : ℕ} [NeZero N₁]
    {ϱ : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}
    (S : DGSetting G a ν) {α : G.Ω 1 → ℂ} (hα : AdmPot G α)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    CubeBlockBounds G a ν α q (selfKc d L) := by
  unfold selfKc
  split_ifs with h
  · exact (Classical.choose_spec (cubeBlockBounds_exists (d := d) (L := L) h.1 h.2)).2 G S hα hq
  · exact absurd ⟨hd, hL⟩ h

open Classical in
/-- **The pair `(coverOf G, G)` satisfies `CoverGeom`** with the constant `Cchi d L`. -/
theorem coverGeom_self (S : DGSetting G a ν) :
    CoverGeom (coverOf G) G a ν (Cchi d L) where
  hd := S.hd
  hL := S.hL
  mass := S.mass
  massLe := S.massLe
  weights := S.weights
  sep := S.sep
  blockAligned q hq :=
    box_blockAligned S.aligned S.cover_sep (by have := S.hL; omega) hq
  chi_unit q hq x z hx hz := by
    obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hx
    have hd0 : 0 < d := by have := S.hd; omega
    have hL2 : 2 ≤ L := by have := S.hL; omega
    rcases hz with rfl | ⟨μ, hμ⟩
    · exact chi_nbr_mem_unit S.aligned hL2 hn1 hnK hxl (⟨0, hd0⟩ : Fin d) (Or.inl rfl) hq
    · exact chi_nbr_mem_unit S.aligned hL2 hn1 hnK hxl μ (Or.inr hμ) hq
  sum_chi x hx := by
    obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hx
    have hd0 : 0 < d := by have := S.hd; omega
    exact sum_chi S.aligned (by have := S.hL; omega) hn1 hnK hxl ⟨0, hd0⟩
  chi_smooth q hq :=
    chiField_isSmooth S.aligned S.cover_sep (by have := S.hd; omega) (by have := S.hL; omega) hq
  inner_near q hq x hx y hy hnear := by
    obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hx
    exact inner_of_near S.cover_sep S.hM (by have := S.hL; omega) hq hn1 hnK hxl
      (inBox_of_chi_ne_zero hy) hnear
  card_box x hx := by
    classical
    obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hx
    have hcard := card_inBox_le (G := G) S.cover_sep (by have := S.hL; omega : 1 ≤ L) hn1 hnK hxl
      (s := 5 / 2) (by norm_num) 5 (by norm_num)
    have hf : (cubeIdx G).filter (fun q => x ∈ intBox q) =
        (cubeIdx G).filter (fun q => InBox m₁ q.1 q.2 (5 / 2 * (L : ℝ) ^ (q.1 + m₁)) x) :=
      Finset.filter_congr fun q _ => mem_intBox
    exact hf ▸ hcard
  card_qset q hq := card_Qset_le S.aligned S.cover_sep S.hM (by have := S.hL; omega) hq

/-- **The pair `(coverOf G, G)` satisfies `CoverBase`** with the constants `selfKc d L` and
`Cchi d L`. -/
theorem coverBase_self (S : DGSetting G a ν) :
    CoverBase (coverOf G) G a ν (selfKc d L) (Cchi d L) where
  toCoverGeom := coverGeom_self S
  nc hα _ hq := selfKc_spec S.hd S.hL G S hα hq

/-- **The geometry of the cover of `G` for the locality** (`CoverLocalGeom`). -/
theorem coverLocalGeom_self (S : DGSetting G a ν) :
    CoverLocalGeom (coverOf G) G a ν (Cchi d L) where
  toCoverGeom := coverGeom_self S
  idx_range q hq := ((mem_cubeIdx G).1 hq).1
  idx_base q hq := ((mem_cubeIdx G).1 hq).2.2
  chi_supp _ _ _ h := inBox_of_chi_ne_zero h
  cubeP_sub q hq x hx := cubeP_subset_Ω S hq hx
  own_cover x hx := by
    obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec hx
    exact ⟨_, own_mem_cubeIdx S.aligned hn1 hnK hxl, mem_cubeP.2 (ownBase_sameCell x)⟩

/-- **The pair `(coverOf G, G)` satisfies `CoverLocal`.** -/
theorem coverLocal_self (S : DGSetting G a ν) :
    CoverLocal (coverOf G) G a ν (selfKc d L) (Cchi d L) where
  toCoverBase := coverBase_self S
  idx_range := (coverLocalGeom_self S).idx_range
  idx_base := (coverLocalGeom_self S).idx_base
  chi_supp := (coverLocalGeom_self S).chi_supp
  cubeP_sub := (coverLocalGeom_self S).cubeP_sub
  own_cover := (coverLocalGeom_self S).own_cover
  row_mem_hat _ hz α _ hx _ h := row_mem_hatBox S hz α hx h

/-! ### The landed specifications follow from the generalized ones -/

/-- The landed `FamSpec` follows from the generalized one at `C = H`. -/
theorem famSpec_of_dec2 {c BG : ℝ} (h : FamSpec d L (selfKc d L) (Cchi d L) c BG) :
    Balaban.Localization.FamSpec d L c BG :=
  ⟨h.1, h.2.1, fun {_ _ _} _ {_} G {_} {_} S {_} hκ hM {_} hs N =>
    h.2.2 (coverOf G) G (coverBase_self S) hκ hM hs N⟩

/-- The landed `Dg2Spec` follows from the generalized one at `C = H`. -/
theorem dg2Spec_of_dec2 {c BG : ℝ} (h : Dg2Spec d L (selfKc d L) (Cchi d L) c BG) :
    Balaban.Localization.Dg2Spec d L c BG :=
  ⟨h.1, h.2.1, fun {_ _ _} _ {_} G {_} {_} S {_} hα {_} hκ hM {_} hs {_} hw f {_} hC hf =>
    h.2.2 (coverOf G) G (coverBase_self S) hα hκ hM hs hw f hC hf⟩

/-- The landed `CloseSpec` follows from the generalized one at `C = H`. -/
theorem closeSpec_of_dec2 {c BG : ℝ} (h : CloseSpec d L (selfKc d L) (Cchi d L) c BG) :
    Balaban.Localization.CloseSpec d L c BG :=
  ⟨h.1, h.2.1, fun {_ _ _} _ {_} G {_} {_} S {_} hα {_} hκ hM {_} hs {_} hW f {_} hC hf =>
    h.2.2 (coverOf G) G (coverBase_self S) hα hκ hM hs hW f hC hf⟩

/-- The landed `OneSpec` follows from the generalized one at `C = H`. -/
theorem oneSpec_of_dec2 {c : ℝ} (h : OneSpec d L (selfKc d L) (Cchi d L) c) :
    Balaban.Localization.OneSpec d L c :=
  ⟨h.1, fun {_ _ _} _ {_} G {_} {_} S {_} hα hM =>
    h.2 (coverOf G) G (coverBase_self S) hα hM⟩

/-- The landed `AnSpec` follows from the generalized one at `C = H`. -/
theorem anSpec_of_dec2 {c : ℝ} (h : AnSpec d L (selfKc d L) (Cchi d L) c) :
    Balaban.Localization.AnSpec d L c :=
  ⟨h.1, fun {_ _ _} _ {_} G {_} {_} S {_} hκ hM x y =>
    h.2 (coverOf G) G (coverBase_self S) hκ hM x y⟩

/-- The landed `DecSpecs` follow from the generalized ones at `C = H`. -/
theorem decSpecs_of_dec2 {c BG : ℝ} (h : DecSpecs d L (selfKc d L) (Cchi d L) c BG) :
    Balaban.Localization.DecSpecs d L c BG :=
  ⟨famSpec_of_dec2 h.fam, dg2Spec_of_dec2 h.dg2, closeSpec_of_dec2 h.close,
    oneSpec_of_dec2 h.one, anSpec_of_dec2 h.an⟩

/-- Constants for all the inputs of the landed I-4a, from the generalized development. -/
theorem decSpecs_exists_of_dec2 (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ c BG : ℝ, Balaban.Localization.DecSpecs d L c BG := by
  obtain ⟨c, BG, h⟩ := decSpecs_exists (d := d) (L := L) (Kc := selfKc d L) (Cx := Cchi d L) hd hL
    (selfKc_nonneg hd hL) (Cchi_nonneg d L)
  exact ⟨c, BG, decSpecs_of_dec2 h⟩

/-! ### The x-variant at `C = H` -/

section XSelf

variable {k : ℕ} {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}

theorem Kzx_self (a : ℕ → ℝ) (aT x ν : ℝ) (q : ℕ × CTorus d L N₁ m₁ (k + 1)) :
    Kzx (coverOf G) G a aT x ν q = Balaban.Localization.Kzx G a aT x ν q := rfl

theorem Gstarx_self (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) :
    Gstarx (coverOf G) G a aT x ν α s = Balaban.Localization.Gstarx G a aT x ν α s := rfl

theorem Kcalx_self (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) :
    Kcalx (coverOf G) G a aT x ν α s = Balaban.Localization.Kcalx G a aT x ν α s := rfl

/-- **`Gsx (coverOf G) G = Gsx G`**: the x-variant decoupled Green's operator of the cover of `G`
and the operator of `G` is the landed one. -/
theorem Gsx_self (a : ℕ → ℝ) (aT x ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) :
    Gsx (coverOf G) G a aT x ν α s = Balaban.Localization.Gsx G a aT x ν α s := rfl

theorem cstarX_self (d L : ℕ) : cstarX d L (Cchi d L) = Balaban.Localization.cstarX d L := rfl

/-- **The pair `(coverOf G, G)` satisfies `XCover`.** -/
theorem xCover_self (S : XSetting G a aT ν) : XCover (coverOf G) G a aT ν (Cchi d L) where
  toCoverGeom := coverGeom_self S.dg
  hk := S.hk
  haT1 := S.haT1
  haT2 := S.haT2

/-- **The pair `(coverOf G, G)` satisfies `XCoverLocal`.** -/
theorem xCoverLocal_self (S : XSetting G a aT ν) :
    XCoverLocal (coverOf G) G a aT ν (Cchi d L) where
  toXCover := xCover_self S
  idx_range := (coverLocalGeom_self S.dg).idx_range
  idx_base := (coverLocalGeom_self S.dg).idx_base
  chi_supp := (coverLocalGeom_self S.dg).chi_supp
  cubeP_sub := (coverLocalGeom_self S.dg).cubeP_sub
  own_cover := (coverLocalGeom_self S.dg).own_cover

/-- The landed (DG1) for the x-variant, from the generalized one at `C = H`. -/
theorem dg1x_of_dec2 {α : G.Ω 1 → ℂ} (S : XSetting G a aT ν) (hα : AdmPot G α) (hx : 0 ≤ x) {κ : ℝ}
    (hκ : 0 ≤ κ) (hMκ : Balaban.Localization.cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ)
    {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : IsAgmonWeight G r) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ xAgmonRate d L) (f : G.Ω 1 → ℂ) :
    agmonSource G ε r (Balaban.Localization.Kcalx G a aT x ν α s *ᵥ f) ≤
      (1 / 16) * agmonSource G ε r f :=
  dg1x (xCover_self S) (Cchi_nonneg d L) hα hx hκ hMκ hs hr hε0 hε1 f

end XSelf

end Balaban.Localization.Dec2
