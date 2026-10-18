/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusBoundTube
public import Balaban.SmallField.IrrelTorusSum
public import Balaban.SmallField.Def6InfD2

/-!
# The label functional as the termwise `Itw` of the label pulled back at its centre

For a label `(j, y, X)` of a torus, the blocks of `X` are placed in `ℤ^d` relative to `y` by
`S = {unlift (x - y) : x ∈ X aligned}`, and a field `Ψ` constant on the `j`-blocks is pulled back to
`ψ_y(s) = Ψ(y + ibase s)`.  For the one-polymer family of `premisesTermAniso_centred` (the term of
the label pulled back at `y`, extended to the anisotropic tube):

* `unlift_sub_eq_iff`, `mem_placeSet`, `placeSet_inj`: the placement of the blocks;
* `shiftField_pack`, `hOf_pack_smul`, `shiftField_refPt`, `shiftField_line`, `shiftField_slice`,
  …: the pulled-back fields of the configurations used below;
* `tensA_centred`, `fderivB_centred`, `tensB_centred`, `term_refPt_centred`: the tensors of the
  pulled-back term at the reference point are the tensors of the label term at the constant
  field `e_{i₀}` (`a_X(x)`, `∂_h ℰ(y,X)·e_{i₀}/ν_j`, `B_X(x,x')`, `f_X(P₀)`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter Topology

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-! ### The placement of the blocks of a polymer relative to its centre -/

section Place

variable {j : ℕ}

omit [NeZero L] [NeZero N₁] in
theorem unlift_congr_of_jBlock {w w' : CTorus d L N₁ m₁ k}
    (h : jBlock d L (N₁ * L ^ m₁) k j w = jBlock d L (N₁ * L ^ m₁) k j w') :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j w =
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j w' := by
  funext μ; simp only [unlift, h]

omit [NeZero L] [NeZero N₁] in
theorem jBlock_eq_of_unlift_eq {w w' : CTorus d L N₁ m₁ k}
    (h : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j w =
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j w') :
    jBlock d L (N₁ * L ^ m₁) k j w = jBlock d L (N₁ * L ^ m₁) k j w' := by
  funext μ
  have := congrFun h μ
  simp only [unlift] at this
  exact ZMod.valMinAbs_inj.1 this

/-- **The block of `x` relative to `y`**: for aligned `x, y`, `unlift (z - y) = unlift (x - y)`
iff `z` lies in the `j`-block of `x`. -/
theorem unlift_sub_eq_iff (hjk : j ≤ k) {y x : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (hx : Aligned (L ^ j) x) (z : CTorus d L N₁ m₁ k) :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) =
        unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) ↔
      cbase (L ^ j) z = x := by
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k := by rw [side_eq hjk]; exact dvd_mul_right _ _
  have hny : Aligned (L ^ j) (-y) := aligned_neg hdvd hy
  have hxy : Aligned (L ^ j) (x - y) := by rw [sub_eq_add_neg]; exact aligned_add hdvd hx hny
  constructor
  · intro h
    have hc := cbase_pow_eq_of_jBlock hjk (jBlock_eq_of_unlift_eq h)
    rw [cbase_eq_self_of_aligned hxy, sub_eq_neg_add, cbase_add_aligned hdvd hny] at hc
    calc cbase (L ^ j) z = (-y + cbase (L ^ j) z) + y := by abel
      _ = (-y + x) + y := by rw [hc]; abel
      _ = x := by abel
  · intro h
    refine unlift_congr_of_jBlock (jBlock_sub_eq_of_jBlock_eq hjk hy ?_)
    rw [← h, jBlock_cbase]

/-- The base of the block of `z` is `y` plus the base of the block placed at `unlift (z - y)`. -/
theorem add_ibase_unlift_sub (hjk : j ≤ k) {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (z : CTorus d L N₁ m₁ k) :
    y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
      (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y)) = cbase (L ^ j) z := by
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k := by rw [side_eq hjk]; exact dvd_mul_right _ _
  have hc : Aligned (L ^ j) (cbase (L ^ j) z) := aligned_cbase z
  have hcy : Aligned (L ^ j) (cbase (L ^ j) z - y) := by
    rw [sub_eq_add_neg]; exact aligned_add hdvd hc (aligned_neg hdvd hy)
  rw [((unlift_sub_eq_iff hjk hy hc z).2 rfl), ibase_unlift_of_aligned hjk hcy]
  abel

open Classical in
/-- Every site of `X` is placed in `S = {unlift (x - y) : x ∈ X aligned}`. -/
theorem mem_placeSet {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k) {y : CTorus d L N₁ m₁ k}
    (hy : Aligned (L ^ j) y) {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom m₀ j X)
    {z : CTorus d L N₁ m₁ k} (hz : z ∈ X) :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈
      (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
        (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)) :=
  Finset.mem_image.2 ⟨cbase (L ^ j) z, Finset.mem_filter.2 ⟨Finset.mem_univ _, aligned_cbase z,
    hX.block_closed hjk hN hz (jBlock_cbase z).symm⟩,
    ((unlift_sub_eq_iff hjk hy (aligned_cbase z) z).2 rfl).symm⟩

/-- The placement is injective on the aligned sites. -/
theorem placeSet_inj (hjk : j ≤ k) {y x x' : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (hx : Aligned (L ^ j) x) (hx' : Aligned (L ^ j) x')
    (h : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) =
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y)) : x = x' := by
  rw [unlift_sub_eq_iff hjk hy hx' x, cbase_eq_self_of_aligned hx] at h
  exact h

omit [NeZero L] [NeZero N₁] in
theorem ibase_zero (j : ℕ) :
    ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (0 : Site d) = 0 := by
  funext μ; simp [ibase]

omit [NeZero L] [NeZero N₁] in
theorem ibase_eU (j : ℕ) (μ : Fin d) :
    ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (eU μ) =
      (L ^ j) • (Pi.single μ 1 : CTorus d L N₁ m₁ k) := by
  funext ν
  by_cases h : ν = μ
  · subst h; simp [ibase, eU]
  · simp [ibase, eU, h]

end Place

/-! ### The pulled-back fields of the configurations -/

section Fields

variable {j : ℕ} {i₀ : Fin N} {S : Finset (Site d)}

omit [NeZero L] [NeZero N₁] in
theorem shiftField_refPt (ν : ℝ) (y z : CTorus d L N₁ m₁ k) :
    fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S (refPt i₀ ν S) (z - y) =
      Pi.single i₀ 1 := by
  funext i
  simp only [fieldOf]
  split_ifs <;> simp [refPt_inl]

omit [NeZero L] [NeZero N₁] in
theorem hOf_refPt {ν : ℝ} (hν : ν ≠ 0) :
    hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (refPt i₀ ν S) =
      constFld (Pi.single i₀ 1) := by
  have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  funext z i
  simp only [hOf, refPt_inr, constFld]
  field_simp

omit [NeZero L] [NeZero N₁] in
theorem hOf_pack_smul {ν : ℝ} (hν : ν ≠ 0) (ψ : Site d → Spin N) (hv : Fin N → ℂ) :
    hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S ψ ((ν : ℂ) • hv)) = constFld hv := by
  have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  funext z i
  simp only [hOf, pack, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, constFld]
  field_simp

/-- **The pulled-back field of the pulled-back configuration**: on `X`, the field of the
configuration `pack S ψ_y b`, `ψ_y(s) = Ψ(y + ibase s)`, placed at `y`, is `Ψ` (for `Ψ` constant on
the `j`-blocks and `S` containing the placements of the sites of `X`). -/
theorem shiftField_pack (hjk : j ≤ k) {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    {X : Set (CTorus d L N₁ m₁ k)}
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S)
    {Ψ : Fld d L N₁ m₁ k N}
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    (b : Spin N) {z : CTorus d L N₁ m₁ k} (hz : z ∈ X) :
    fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
        (pack S (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)) b)
        (z - y) = Ψ z := by
  have hm := hS z hz
  funext i
  simp only [fieldOf, hm, ↓reduceDIte, pack, Sum.elim_inl]
  rw [add_ibase_unlift_sub hjk hy z]
  exact congrFun (hΨb _ _ (jBlock_cbase z)) i

/-- **Adding a spin coordinate**: for `s = unlift (x - y)`, `x` aligned, the field placed at `y` of
the configuration `c + t δ_{(s, i)}` is that of `c` plus `t δ_{(x, i)}` (`blockDir`). -/
theorem shiftField_add_single (hjk : j ≤ k) {y x : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (hx : Aligned (L ^ j) x)
    (hm : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) ∈ S) (i : Fin N) (c : Cfg d N S)
    (t : ℂ) (z : CTorus d L N₁ m₁ k) :
    fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
        (c + t • Pi.single (Sum.inl (⟨_, hm⟩, i)) 1) (z - y) =
      fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y) +
        t • blockDir (N := N) L j x i z := by
  funext i'
  have key := unlift_sub_eq_iff hjk hy hx z
  by_cases h1 : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S
  · simp only [fieldOf, h1, ↓reduceDIte, Pi.add_apply, Pi.smul_apply, smul_eq_mul, blockDir]
    by_cases h2 : cbase (L ^ j) z = x ∧ i' = i
    · have he : (Sum.inl (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y), h1⟩, i') :
          Idx d N S) = Sum.inl (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y), hm⟩, i) :=
        congrArg Sum.inl (Prod.ext (Subtype.ext (key.2 h2.1)) h2.2)
      rw [he, Pi.single_eq_same, ite_eq_left h2]
    · have he : ¬ ((Sum.inl (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y), h1⟩, i') :
          Idx d N S) = Sum.inl (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y), hm⟩,
            i)) := by
        intro he
        apply h2
        have he2 := Sum.inl_injective he
        exact ⟨key.1 (congrArg (fun q : ↥S × Fin N => q.1.1) he2), congrArg Prod.snd he2⟩
      rw [Pi.single_eq_of_ne he, ite_eq_right h2]
  · have h2 : ¬ (cbase (L ^ j) z = x ∧ i' = i) := fun h => h1 (by rw [key.2 h.1]; exact hm)
    simp only [fieldOf, h1, ↓reduceDIte, Pi.add_apply, Pi.smul_apply, smul_eq_mul, blockDir, h2,
      ↓reduceIte, mul_zero, add_zero]

omit [NeZero L] [NeZero N₁] in
/-- Adding a spin coordinate does not change the field `h`. -/
theorem hOf_add_single_inl {ν : ℝ} (c : Cfg d N S) (p : ↥S × Fin N) (t : ℂ) :
    hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (c + t • Pi.single (Sum.inl p) 1) =
      hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c := by
  funext z i
  simp [hOf]

omit [NeZero L] [NeZero N₁] in
/-- Adding a field coordinate does not change the spin field. -/
theorem shiftField_add_single_inr (c : Cfg d N S) (i : Fin N) (t : ℂ) (w : CTorus d L N₁ m₁ k) :
    fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S (c + t • Pi.single (Sum.inr i) 1) w =
      fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c w := by
  funext i'
  simp only [fieldOf]
  split_ifs <;> simp

omit [NeZero L] [NeZero N₁] in
/-- The field `h` along the longitudinal field coordinate: `e_{i₀} + (t/ν) e_{i₀}`. -/
theorem hOf_refPt_add_single_inr {ν : ℝ} (hν : ν ≠ 0) (t : ℂ) :
    hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S
        (refPt i₀ ν S + t • Pi.single (Sum.inr i₀) 1) =
      constFld (Pi.single i₀ 1) + t • ((ν : ℂ)⁻¹ • constFld (Pi.single i₀ 1)) := by
  have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν
  funext z i
  by_cases h : i = i₀
  · subst h
    simp only [hOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, refPt_inr, constFld,
      Pi.single_eq_same]
    field_simp
  · simp only [hOf, Pi.add_apply, Pi.smul_apply, smul_eq_mul, refPt_inr, constFld,
      Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun h' => h (Sum.inr_injective h'))]
    simp

end Fields

/-! ### The tensors of the pulled-back term at the reference point -/

section Tensors

variable {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)} {i₀ : Fin N}
  {r : ℝ}

omit [NeZero L] [NeZero N₁] in
theorem eventually_line_mem_polyAniso (hr0 : 0 < r) (v : Cfg d N S) :
    ∀ᶠ t : ℂ in 𝓝 0, refPt i₀ ν S + t • v ∈ polyAniso i₀ ν r S := by
  have hc : Continuous fun t : ℂ => refPt i₀ ν S + t • v := by fun_prop
  refine hc.continuousAt.preimage_mem_nhds ?_
  simp only [zero_smul, add_zero]
  exact isOpen_polyAniso.mem_nhds (refPt_mem_polyAniso hr0)

/-- **The reference field lies in the domain of the term.** -/
theorem xiDom_ref (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν) (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (hX : IsPolyDom P.m₀ j X) (i₀ : Fin N) (hrad : AnisoRadiusOK d L N P j r) :
    XiDom (Tm.gs j X) a μ j (P.eps d L j) (constFld (Pi.single i₀ 1))
      (constFld (Pi.single i₀ 1)) := by
  obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hrad
  have hNB : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
  have h := xiDom_shift_poly (y := 0) (S := ∅) hBg (hcl.gs_spec j hj1 hjk X hX).2 hjk hν hμν i₀
    (fun μ => by simp) hδ0 hδc0 hδc1 hr0 hr1 (aniK_old i₀ hr0 hrδ).2 hε (refPt_mem_polyAniso hr0)
  have e1 : (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ (∅ : Finset (Site d))
      (refPt i₀ ν ∅) (z - 0)) = constFld (Pi.single i₀ 1) := funext fun z => shiftField_refPt ν 0 z
  rwa [e1, hOf_refPt hν.ne'] at h

theorem analyticAt_term_ref (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν) (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X) (i₀ : Fin N)
    (hrad : AnisoRadiusOK d L N P j r) :
    AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm.E j y X p.1 p.2)
      (constFld (Pi.single i₀ 1), constFld (Pi.single i₀ 1)) :=
  hcl.analyticE j hj1 hjk y X hX hyX _ (xiDom_ref hcl hBg hν hμν hj1 hjk hX i₀ hrad)

variable (hT : TubeHypA i₀ ν r (fun c : Cfg d N S =>
    Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y))
      (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c)))
include hT

/-- **`f_X(P₀)`**: the pulled-back term at the reference point is the term at the constant fields. -/
theorem term_refPt_centred (hν : 0 < ν) (hr0 : 0 < r) :
    trickFnA i₀ ν r (fun c : Cfg d N S =>
        Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y))
          (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c)) (refPt i₀ ν S) =
      Tm.E j y X (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1)) := by
  rw [trickFnA_of_poly hT (refPt_mem_polyAniso hr0)]
  congr 1
  · exact funext fun z => shiftField_refPt ν y z
  · exact hOf_refPt hν.ne'

/-- **`a_X(x)`**: the derivative of the pulled-back term at the reference point in the direction of
the spin coordinate `(unlift (x - y), i₀)` is the derivative of the label term at the constant
fields in the direction of the block of `x`. -/
theorem tensA_centred (hjk : j ≤ k) (hy : Aligned (L ^ j) y) (hν : 0 < ν) (hr0 : 0 < r)
    (hE : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm.E j y X p.1 p.2)
      (constFld (Pi.single i₀ 1), constFld (Pi.single i₀ 1)))
    {x : CTorus d L N₁ m₁ k} (hx : Aligned (L ^ j) x)
    (hm : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) ∈ S) :
    tensA i₀ ν S (trickFnA i₀ ν r (fun c : Cfg d N S =>
        Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y))
          (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c))) ⟨_, hm⟩ =
      fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1))) (constFld (Pi.single i₀ 1))
        (blockDir L j x i₀) := by
  have hAT := hT.trickFnA_analytic _ (polyAniso_subset_tubeAniso (refPt_mem_polyAniso hr0))
  have hg : AnalyticAt ℂ (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1)))
      (constFld (Pi.single i₀ 1)) :=
    AnalyticAt.comp (f := fun Ψ' : Fld d L N₁ m₁ k N => (Ψ', constFld (Pi.single i₀ 1))) hE
      (analyticAt_id.prod analyticAt_const)
  unfold tensA
  refine fderiv_eq_of_eventually_line hAT.differentiableAt hg.differentiableAt ?_
  filter_upwards [eventually_line_mem_polyAniso hr0 (Pi.single (Sum.inl (⟨_, hm⟩, i₀)) 1)]
    with t ht
  rw [trickFnA_of_poly hT ht]
  congr 1
  · funext z
    rw [shiftField_add_single hjk hy hx hm i₀ _ t z, shiftField_refPt]
    rfl
  · rw [hOf_add_single_inl, hOf_refPt hν.ne']

/-- **`∂_v f_X(P₀)`**: the derivative of the pulled-back term at the reference point in the
longitudinal field coordinate is `ν_j⁻¹ ∂_h ℰ(y, X)(P₀)·e_{i₀}`. -/
theorem fderivB_centred (hν : 0 < ν) (hr0 : 0 < r)
    (hE : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm.E j y X p.1 p.2)
      (constFld (Pi.single i₀ 1), constFld (Pi.single i₀ 1))) :
    fderiv ℂ (trickFnA i₀ ν r (fun c : Cfg d N S =>
        Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y))
          (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c))) (refPt i₀ ν S)
        (Pi.single (Sum.inr i₀) 1) =
      (ν : ℂ)⁻¹ * fderiv ℂ (fun h' => Tm.E j y X (constFld (Pi.single i₀ 1)) h')
        (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1)) := by
  have hAT := hT.trickFnA_analytic _ (polyAniso_subset_tubeAniso (refPt_mem_polyAniso hr0))
  have hg : AnalyticAt ℂ (fun h' : Fld d L N₁ m₁ k N => Tm.E j y X (constFld (Pi.single i₀ 1)) h')
      (constFld (Pi.single i₀ 1)) :=
    AnalyticAt.comp (f := fun h' : Fld d L N₁ m₁ k N => (constFld (Pi.single i₀ 1), h')) hE
      (analyticAt_const.prod analyticAt_id)
  have e : (ν : ℂ)⁻¹ * fderiv ℂ (fun h' => Tm.E j y X (constFld (Pi.single i₀ 1)) h')
      (constFld (Pi.single i₀ 1)) (constFld (Pi.single i₀ 1)) =
      fderiv ℂ (fun h' => Tm.E j y X (constFld (Pi.single i₀ 1)) h') (constFld (Pi.single i₀ 1))
        ((ν : ℂ)⁻¹ • constFld (Pi.single i₀ 1)) := by
    rw [map_smul, smul_eq_mul]
  rw [e]
  refine fderiv_eq_of_eventually_line hAT.differentiableAt hg.differentiableAt ?_
  filter_upwards [eventually_line_mem_polyAniso hr0 (Pi.single (Sum.inr i₀) 1)] with t ht
  rw [trickFnA_of_poly hT ht]
  congr 1
  · funext z
    rw [shiftField_add_single_inr, shiftField_refPt]
    rfl
  · exact hOf_refPt_add_single_inr hν.ne' t

/-- **`B_X(x, x')`**: the second derivative of the pulled-back term at the reference point in the
spin coordinates `(unlift (x - y), i₁)`, `(unlift (x' - y), i₁)` is that of the label term at the
constant fields in the directions of the blocks of `x, x'`. -/
theorem tensB_centred (hjk : j ≤ k) (hy : Aligned (L ^ j) y) (hν : 0 < ν) (hr0 : 0 < r)
    (hr1 : r ≤ 1)
    (hE : AnalyticAt ℂ (fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N => Tm.E j y X p.1 p.2)
      (constFld (Pi.single i₀ 1), constFld (Pi.single i₀ 1)))
    (i₁ : Fin N) {x x' : CTorus d L N₁ m₁ k} (hx : Aligned (L ^ j) x) (hx' : Aligned (L ^ j) x')
    (hm : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) ∈ S)
    (hm' : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x' - y) ∈ S) :
    tensB i₀ i₁ ν S (trickFnA i₀ ν r (fun c : Cfg d N S =>
        Tm.E j y X (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y))
          (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c))) ⟨_, hm⟩ ⟨_, hm'⟩ =
      D2 (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1))) (constFld (Pi.single i₀ 1))
        (blockDir L j x i₁) (blockDir L j x' i₁) := by
  have hAT := hT.trickFnA_analytic _ (polyAniso_subset_tubeAniso (refPt_mem_polyAniso hr0))
  have hg : AnalyticAt ℂ (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1)))
      (constFld (Pi.single i₀ 1)) :=
    AnalyticAt.comp (f := fun Ψ' : Fld d L N₁ m₁ k N => (Ψ', constFld (Pi.single i₀ 1))) hE
      (analyticAt_id.prod analyticAt_const)
  unfold tensB
  refine D2_congr_slice hAT hg (δ := r ^ 2 / 2) (by positivity) fun s t hs ht => ?_
  have hmem : refPt i₀ ν S + s • Pi.single (Sum.inl (⟨_, hm⟩, i₁)) 1 +
      t • Pi.single (Sum.inl (⟨_, hm'⟩, i₁)) 1 ∈ polyAniso i₀ ν r S := by
    refine ball_subset_polyAniso hr0 hr1 ?_
    rw [mem_ball, dist_eq_norm, add_assoc, add_sub_cancel_left]
    have h1 : ‖s • (Pi.single (Sum.inl (⟨_, hm⟩, i₁)) 1 : Cfg d N S)‖ ≤ ‖s‖ := by
      rw [norm_smul, Pi.norm_single, norm_one, mul_one]
    have h2 : ‖t • (Pi.single (Sum.inl (⟨_, hm'⟩, i₁)) 1 : Cfg d N S)‖ ≤ ‖t‖ := by
      rw [norm_smul, Pi.norm_single, norm_one, mul_one]
    calc _ ≤ _ := norm_add_le _ _
      _ < r ^ 2 := by linarith
  rw [trickFnA_of_poly hT hmem]
  congr 1
  · funext z
    rw [shiftField_add_single hjk hy hx' hm' i₁ _ t z, shiftField_add_single hjk hy hx hm i₁ _ s z,
      shiftField_refPt]
    rfl
  · rw [hOf_add_single_inl, hOf_add_single_inl, hOf_refPt hν.ne']

end Tensors

end Balaban.SmallField.Def6v2
