/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.LocalGeneratorPhysicalObstruction
public import Balaban.SmallField.GsSpecCounter

/-!
# Restricting a whole-level datum to a local generating set

The raw fields of P3 (4.44) are retained on the data sites of the local set and set to zero
elsewhere.  This is the restriction needed before recomputing the local background in
P3 (4.46)-(4.47), printed pp. 78-79.
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField
  Balaban.SmallField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  {j : ℕ} {hj : j ≤ k} {X : Set (CTorus d L N₁ m₁ k)}
  {hsep : ϱ ≤ minSep L (L ^ m₁)}

/-- A field constant on the whole-level `j` blocks is constant on the finer blocks of
`localB`, whose layers have indices at most `j`. -/
theorem localB_layerConstant_of_levelGS
    (hj1 : 1 ≤ j) {β : Type*} {f : CTorus d L N₁ m₁ k → β}
    (hf : IsLayerConstant
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) f) :
    IsLayerConstant (localB j hj X hsep) f := by
  intro n hn1 hnk x hx x' hx'
  have hnj : n ≤ j := by
    by_contra h
    have h' : j < n := by omega
    have hxΩ := (localB j hj X hsep).mem_layer.1 hx |>.1
    rw [localB_Ω_of_gt h'] at hxΩ
    exact Finset.notMem_empty _ hxΩ
  have hblock : jBlock d L (N₁ * L ^ m₁) k j x =
      jBlock d L (N₁ * L ^ m₁) k j x' :=
    jBlock_eq_of_le hnj hj (GeneratingSet.mem_blk.1 hx') |>.symm
  have hxamb : x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ') j hj).layer j := by
    simp [GeneratingSet.mem_layer, levelGS]
  exact hf j hj1 hj x hxamb x' (GeneratingSet.mem_blk.2 hblock.symm)

/-- The raw datum restricted to the sites of `localB` (P3 (4.44)). -/
noncomputable def localBRestrict (hj1 : 1 ≤ j)
    (D : BgData
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) N) :
    BgData (localB j hj X hsep) N :=
  BgData.clip (localB j hj X hsep) D.Ψ D.h
    (localB_layerConstant_of_levelGS hj1 D.Ψ_layerConst)
    (localB_layerConstant_of_levelGS hj1 D.h_layerConst)

/-- Restriction retains the spin field on the local data sites. -/
theorem localBRestrict_Ψ (hj1 : 1 ≤ j)
    (D : BgData
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) N)
    {x : CTorus d L N₁ m₁ k} (hx : x ∈ dataSites (localB j hj X hsep)) :
    (localBRestrict (X := X) (hsep := hsep) hj1 D).Ψ x = D.Ψ x := by
  classical
  simp [localBRestrict, BgData.clip, hx]

/-- Restriction retains the external field on the local first domain. -/
theorem localBRestrict_h (hj1 : 1 ≤ j)
    (D : BgData
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) N)
    {x : CTorus d L N₁ m₁ k} (hx : x ∈ (localB j hj X hsep).Ω 1) :
    (localBRestrict (X := X) (hsep := hsep) hj1 D).h x = D.h x := by
  classical
  simp [localBRestrict, BgData.clip, hx]

/-- Every block used by the restricted datum is contained in its ambient `j` block. -/
theorem localB_blockSet_subset_levelGS (hj1 : 1 ≤ j)
    {x y : CTorus d L N₁ m₁ k} (hx : x ∈ dataSites (localB j hj X hsep))
    (hy : y ∈ blockSet (localB j hj X hsep) x) :
    y ∈ blockSet
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) x := by
  let G := localB j hj X hsep
  let G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ' := levelGS j hj
  have hxamb : x ∈ G'.Ω 1 := localB_dataSites_subset_levelGS_omega_one hj1 hj hx
  rw [blockSet_of_mem G' hxamb]
  rcases (mem_dataSites G).1 hx with hxΩ | hxcol
  · rw [blockSet_of_mem G hxΩ] at hy
    have hprec : Precedes G G' := localB_precedes_levelGS
    have hmem := blk_subset_blk' hprec hxΩ hy
    simpa [G', levelGS_layerIndex (ϱ := ϱ') hj1 hj] using hmem
  · have hxnot : x ∉ G.Ω 1 := ((mem_collar G).1 hxcol).1
    rw [blockSet_of_not_mem G hxnot, Finset.mem_singleton] at hy
    subst y
    exact G'.mem_blk.2 rfl

/-- A new local interface pair is an ambient interface pair.  Both endpoints and both
blocks are inside the whole-level first domain. -/
theorem localB_interface_levelGS (hj1 : 1 ≤ j)
    {x x' : CTorus d L N₁ m₁ k}
    (hxx' : IsInterfacePair (localB j hj X hsep) x x') :
    IsInterfacePair
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) x x' := by
  let G := localB j hj X hsep
  let G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ' := levelGS j hj
  obtain ⟨hx, hx', _, y, hy, y', hy', hadj⟩ := hxx'
  refine ⟨(mem_dataSites G').2 (Or.inl (localB_dataSites_subset_levelGS_omega_one hj1 hj hx)),
    (mem_dataSites G').2 (Or.inl (localB_dataSites_subset_levelGS_omega_one hj1 hj hx')),
    Or.inl (by rw [levelGS_layerIndex (ϱ := ϱ') hj1 hj,
      levelGS_layerIndex (ϱ := ϱ') hj1 hj]),
    y, localB_blockSet_subset_levelGS hj1 hx hy,
    y', localB_blockSet_subset_levelGS hj1 hx' hy', hadj⟩

/-- The mass weight of a local layer does not exceed that of the ambient `j` layer. -/
theorem localB_massWeight_le {μ : ℝ} (hμ : 0 ≤ μ) (x : CTorus d L N₁ m₁ k) :
    μ * ((L : ℝ) ^ (localB j hj X hsep).layerIndex x) ^ 2 ≤
      μ * ((L : ℝ) ^ j) ^ 2 := by
  have hL : (1 : ℝ) ≤ L := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hindex : (localB j hj X hsep).layerIndex x ≤ j :=
    layerIndex_le_of_Ω_empty _ (localB_Ω_of_gt (Nat.lt_succ_self j)) x
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL hindex) 2) hμ

/-- Restriction preserves the small-field data inequalities, including the new local
collar pairs.  The local mass weights are smaller because its layers have index at most `j`. -/
theorem localB_inPsiTildeC_of_levelGS (hj1 : 1 ≤ j) {μ δ ε : ℝ} (hμ : 0 ≤ μ)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : CTorus d L N₁ m₁ k → Fin N → ℂ}
    (hP : InPsiTildeC
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj)
      μ δ ε Ψ₀ h₀ Ψ'' h'') :
    InPsiTildeC (localB j hj X hsep) μ δ ε Ψ₀ h₀ Ψ'' h'' := by
  let G := localB j hj X hsep
  let G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ' := levelGS j hj
  have hsite : ∀ x, x ∈ dataSites G → x ∈ dataSites G' := by
    intro x hx
    exact (mem_dataSites G').2
      (Or.inl (localB_dataSites_subset_levelGS_omega_one hj1 hj hx))
  have homega : ∀ x, x ∈ G.Ω 1 → x ∈ G'.Ω 1 := by
    intro x hx
    exact localB_dataSites_subset_levelGS_omega_one hj1 hj
      ((mem_dataSites G).2 (Or.inl hx))
  refine {
    toInPsiTilde := {
      layerConst := localB_layerConstant_of_levelGS hj1 hP.layerConst
      r1 := fun x x' hxx' => hP.r1 x x' (localB_interface_levelGS hj1 hxx')
      r2 := fun x hx => hP.r2 x (hsite x hx)
      r3 := fun x hx => by
        calc
          _ ≤ μ * ((L : ℝ) ^ j) ^ 2 *
              |1 - (∑ i, Ψ₀ x i * h₀ i) / rn (Ψ₀ x)| :=
                mul_le_mul_of_nonneg_right (localB_massWeight_le (hsep := hsep) hμ x)
                  (abs_nonneg _)
          _ < δ ^ 2 := by
            simpa [G', levelGS_layerIndex (ϱ := ϱ') hj1 hj] using hP.r3 x (hsite x hx)
      r4 := hP.r4 }
    eps_pos := hP.eps_pos
    layerConst' := localB_layerConstant_of_levelGS hj1 hP.layerConst'
    hLayerConst' := localB_layerConstant_of_levelGS hj1 hP.hLayerConst'
    c1 := fun x x' hxx' => hP.c1 x x' (localB_interface_levelGS hj1 hxx')
    c2a := fun x hx => hP.c2a x (hsite x hx)
    c2b := fun x hx => hP.c2b x (hsite x hx)
    c3a := fun x hx => by
      calc
        _ ≤ μ * ((L : ℝ) ^ j) ^ 2 * vn (h'' x) :=
          mul_le_mul_of_nonneg_right (localB_massWeight_le (hsep := hsep) hμ x)
            (vn_nonneg _)
        _ < δ ^ 2 / ε := by
          simpa [G', levelGS_layerIndex (ϱ := ϱ') hj1 hj] using hP.c3a x (homega x hx)
    c3b := fun x hx => by
      calc
        _ ≤ μ * ((L : ℝ) ^ j) ^ 2 *
            ‖∑ i, ((Ψ₀ x i / rn (Ψ₀ x) : ℝ) : ℂ) * h'' x i‖ :=
          mul_le_mul_of_nonneg_right (localB_massWeight_le (hsep := hsep) hμ x)
            (norm_nonneg _)
        _ < δ ^ 2 := by
          simpa [G', levelGS_layerIndex (ϱ := ϱ') hj1 hj] using hP.c3b x (homega x hx) }

/-- A whole-level complex data-domain point remains in the local data domain after the
raw fields are clipped to the local sites. -/
theorem localB_inDomainC_restrict (hj1 : 1 ≤ j) {μ δ ε : ℝ} (hμ : 0 ≤ μ)
    (D : BgData
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) N)
    (hD : InDomainC _ μ δ ε D) :
    InDomainC (localB j hj X hsep) μ δ ε
      (localBRestrict (X := X) (hsep := hsep) hj1 D) := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hP, hΨ, hh⟩ := hD
  refine ⟨Ψ₀, h₀, Ψ'', h'', localB_inPsiTildeC_of_levelGS hj1 hμ hP, ?_, ?_⟩
  · intro x hx i
    rw [localBRestrict_Ψ hj1 D hx]
    exact hΨ x ((mem_dataSites _).2
      (Or.inl (localB_dataSites_subset_levelGS_omega_one hj1 hj hx))) i
  · intro x hx i
    rw [localBRestrict_h hj1 D hx]
    exact hh x (by simp [levelGS, hj1]) i

/-- The clipped datum belongs to the local union of complex small-field data domains. -/
theorem localB_inUnionDomainC_restrict (hj1 : 1 ≤ j) {μ : ℝ} (hμ : 0 ≤ μ)
    (D : BgData
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) N)
    (hD : InUnionDomainC _ (bgC0 d L N) (bgC1 d L N) μ D) :
    InUnionDomainC (localB j hj X hsep) (bgC0 d L N) (bgC1 d L N) μ
      (localBRestrict (X := X) (hsep := hsep) hj1 D) := by
  obtain ⟨δ, ε, hδ, hδε, hε, hδc, hμε, hDC⟩ := hD
  exact ⟨δ, ε, hδ, hδε, hε, hδc, hμε, localB_inDomainC_restrict hj1 hμ D hDC⟩

/-- In particular, restriction of an ambient `XiCData` point meets the local small-field
conditions of P2 (1.12). -/
theorem localB_smallField_restrict (hj1 : 1 ≤ j) {A : ℕ → ℝ} {μ σ ε : ℝ} (hμ : 0 ≤ μ)
    (D : BgData
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) N)
    (hD : XiCData _ A μ j σ ε D) :
    InUnionDomainC (localB j hj X hsep) (bgC0 d L N) (bgC1 d L N) μ
      (localBRestrict (X := X) (hsep := hsep) hj1 D) :=
  localB_inUnionDomainC_restrict hj1 hμ D (xiCData_unionC hD)

/-- Recomputing the real and complex backgrounds on `localB` places the clipped datum in
`XiCData` at radius `ε + (2 K₁ + 1) δ`.  The radius loss is explicit. -/
theorem localB_xiCData_restrict (hj1 : 1 ≤ j) {A : ℕ → ℝ} {μ δ ε εb : ℝ}
    (H : BgHyp d L k ϱ A μ) (hμ : 0 ≤ μ)
    (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N)
    (hδc : δ ≤ bgC1 d L N)
    (hμε : μ * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (hεb : ε + (2 * bgK1 d L N + 1) * δ ≤ εb)
    (D : BgData
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj) N)
    (hD : InDomainC _ μ δ ε D) :
    XiCData (localB j hj X hsep) A μ j 1 εb
      (localBRestrict (X := X) (hsep := hsep) hj1 D) := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hP, hΨ, hh⟩ :=
    localB_inDomainC_restrict (X := X) (hsep := hsep) hj1 hμ D hD
  refine ⟨Ψ₀, h₀, Ψ'', h'', ?_, ⟨hΨ, hh⟩⟩
  have hXi := psiTildeC_subset_xiC (G := localB j hj X hsep) H
    hδ0 hδε hε hδc hμε hP hεb
  exact xiC_level_mono hj hμ
    (Nat.one_le_iff_ne_zero.2 (NeZero.ne L)) hXi

/-- A local `XiCData` point at scale one realizes the same full raw pair in the local
class chart.  Off the local data sites, the free displacement is adjusted to the raw pair. -/
theorem localB_xiDom_of_xiCData_one {A : ℕ → ℝ} {μ ε ε' : ℝ}
    (hε : ε ≤ ε') {D : BgData (localB j hj X hsep) N}
    (hD : XiCData (localB j hj X hsep) A μ j 1 ε D)
    {Ψ h : Fld d L N₁ m₁ k N}
    (hΨ : ∀ x ∈ dataSites (localB j hj X hsep), ∀ i, Ψ x i = D.Ψ x i)
    (hh : ∀ x ∈ (localB j hj X hsep).Ω 1, ∀ i, h x i = D.h x i) :
    XiDom (localB j hj X hsep) A μ j ε' Ψ h := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hXi, hR⟩ := hD
  refine ⟨Ψ₀, h₀, fun x i => Ψ x i - (Ψ₀ x i : ℂ),
    fun x i => h x i - (h₀ i : ℂ), fun x i => by ring,
    fun x i => by ring, ?_⟩
  refine xiC_rescale_of_agree (σ := 1) (ε := ε) (ε' := ε') le_rfl (by simpa using hε)
    (fun x hx i => ?_) (fun x hx i => ?_) hXi
  · rw [hΨ x hx i, hR.1 x hx i]
    ring
  · rw [hh x hx i, hR.2 x hx i]
    ring

/-- The ambient chart restricts to the local chart when the class radius pays the
explicit data-domain loss `c₀ + (2 K₁ + 1)c₁`. -/
theorem localB_xiDom_of_ambient_xiDom (hj1 : 1 ≤ j) {A : ℕ → ℝ}
    {μ εamb εloc : ℝ} (H : BgHyp d L k ϱ A μ) (hμ : 0 ≤ μ)
    (hbudget : bgC0 d L N + (2 * bgK1 d L N + 1) * bgC1 d L N ≤ εloc)
    {Ψ h : Fld d L N₁ m₁ k N}
    (hAmb : XiDom
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ') j hj)
      A μ j εamb Ψ h) :
    XiDom (localB j hj X hsep) A μ j εloc Ψ h := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hΨ, hh, hXi⟩ := hAmb
  obtain ⟨hσ, hε, Dr, Dc, hXR, hC, hU, hBC⟩ := hXi
  obtain ⟨δ, ε, hδ0, hδε, hεc, hδc, hμε, hDC⟩ := hU
  have hcoeff : 0 ≤ 2 * bgK1 d L N + 1 := by
    have := bgK1_pos d L N
    linarith
  have hεb : ε + (2 * bgK1 d L N + 1) * δ ≤ εloc :=
    (add_le_add hεc (mul_le_mul_of_nonneg_left hδc hcoeff)).trans hbudget
  have hLoc : XiCData (localB j hj X hsep) A μ j 1 εloc
      (localBRestrict (X := X) (hsep := hsep) hj1 Dc) :=
    localB_xiCData_restrict hj1 H hμ hδ0 hδε hεc hδc hμε hεb Dc hDC
  refine localB_xiDom_of_xiCData_one le_rfl hLoc (fun x hx i => ?_)
    (fun x hx i => ?_)
  · rw [localBRestrict_Ψ hj1 Dc hx]
    rw [hΨ x i, hC.1 x ((mem_dataSites _).2
      (Or.inl (localB_dataSites_subset_levelGS_omega_one hj1 hj hx))) i]
  · rw [localBRestrict_h hj1 Dc hx]
    rw [hh x i, hC.2 x (by simp [levelGS, hj1]) i]

/-- Pointwise `hsub` for the low-index class domain.  The required radius inequality
displays the loss incurred by local recomputation. -/
theorem localB_xiFieldDom_of_ambient_xiDom (hj1 : 1 ≤ j)
    {hsep : bgR0 d L ≤ minSep L (L ^ m₁)} {ϱhi : ℝ}
    {A : ℕ → ℝ} {μ εamb : ℝ} {εseq : ℕ → ℝ}
    (H : BgHyp d L k (bgR0 d L) A μ) (hμ : 0 ≤ μ)
    (hbudget : bgC0 d L N + (2 * bgK1 d L N + 1) * bgC1 d L N ≤ εseq j)
    {Ψ h : Fld d L N₁ m₁ k N}
    (hAmb : XiDom
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱhi) j hj)
      A μ j εamb Ψ h) :
    (xiFieldDom A μ εseq : FieldDom d L N₁ m₁ k N (bgR0 d L)).dom j
      (localB j hj X hsep) Ψ h :=
  localB_xiDom_of_ambient_xiDom hj1 H hμ hbudget hAmb

end Balaban.SmallField.GsSpec
