/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoOps
public import Balaban.Polymer.LocalIsoAlg
public import Balaban.Background.ApproxResidual
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the data of the background problem

For two generating sets carried onto each other by the box map (`OmegaIso G H ρ`) and data of the
two tori corresponding on the box of radius `ρ + 1` (`DataCorr`), the data of the background
problem correspond at corresponding sites:

* `OmegaIso.blockIdx_image`, `OmegaIso.interp_eq`: the blocks of the interpolation and the
  interpolated field;
* `OmegaIso.locSol_eq`, `OmegaIso.approxField_eq`: the local solutions and the approximate field
  `φ₀` at the sites of the box of radius `ρ + 1`;
* `OmegaIso.source_eq`, `OmegaIso.residual_eq`: the source `S(Ψ, h̃)` and the residual
  `f₀ = S - H_D(0) φ₀`;
* `OmegaIso.qStar_eq`, `OmegaIso.boundaryTerm_eq`, `OmegaIso.pertSource_eq`: the source `F_s` of
  the perturbed problem.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Matrix

variable {d L N₁ N₁' m₁ K N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ ϱ' : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)
local notation "cm" => (Prod.map id bm : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁' m₁ K)

/-- **Two fields of the two tori correspond on the box of radius `r`.** -/
def FieldCorr (r : ℕ) (Ψ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Ψ' : CTorus d L N₁' m₁ K → Fin N → ℂ) :
    Prop :=
  ∀ z, InBox d r ((N₁ * L ^ m₁) * L ^ K) z → Ψ' (bm z) = Ψ z

namespace OmegaIso

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {H : GeneratingSet d L (N₁' * L ^ m₁) K ϱ'}
  {ρ : ℕ}

/-! ### The blocks of the interpolation -/

theorem blockBase_inBox (hI : OmegaIso G H ρ) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ blockIdx G) :
    InBox d ρ ((N₁ * L ^ m₁) * L ^ K) q.2 := by
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := (mem_blockIdx G).1 hq
  exact hI.boxG _ (G.layer_subset h1 h2 h3)

theorem blockBase_inBox' (hI : OmegaIso G H ρ) {q : ℕ × CTorus d L N₁' m₁ K}
    (hq : q ∈ blockIdx H) : InBox d ρ ((N₁' * L ^ m₁) * L ^ K) q.2 := by
  obtain ⟨⟨h1, h2⟩, h3, -⟩ := (mem_blockIdx H).1 hq
  exact hI.boxH _ (H.layer_subset h1 h2 h3)

theorem mem_blockIdx_map (hI : OmegaIso G H ρ) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ blockIdx G) : cm q ∈ blockIdx H := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (mem_blockIdx G).1 hq
  have hb := hI.blockBase_inBox hq
  exact (mem_blockIdx H).2 ⟨⟨h1, h2⟩,
    (hI.layer_iff (inBox_mono (Nat.le_succ ρ) hb) h1 h2).2 h3, isBase_boxMap h2 h4⟩

theorem exists_blockIdx_of (hI : OmegaIso G H ρ) {q' : ℕ × CTorus d L N₁' m₁ K}
    (hq' : q' ∈ blockIdx H) : ∃ q ∈ blockIdx G, cm q = q' := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (mem_blockIdx H).1 hq'
  have hb := hI.blockBase_inBox' hq'
  have hlt : 2 * ρ + 1 < (N₁ * L ^ m₁) * L ^ K := by have := hI.two_lt.1; omega
  have hxb : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (bm' q'.2) := inBox_boxMap hlt hb
  have hback : bm (bm' q'.2) = q'.2 := boxMap_boxMap hlt hb
  refine ⟨(q'.1, bm' q'.2), (mem_blockIdx G).2 ⟨⟨h1, h2⟩, ?_, isBase_boxMap h2 h4⟩, ?_⟩
  · refine (hI.layer_iff (inBox_mono (Nat.le_succ ρ) hxb) h1 h2).1 ?_
    rw [hback]; exact h3
  · show ((q'.1, bm (bm' q'.2)) : ℕ × CTorus d L N₁' m₁ K) = q'
    rw [hback]

theorem blockIdx_injOn (hI : OmegaIso G H ρ) : Set.InjOn cm (↑(blockIdx G) : Set _) := by
  intro q hq q₂ hq₂ h
  have hlt : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K := by have := hI.two_lt.2; omega
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h1 (boxMap_inj (hm' := hlt) (hI.blockBase_inBox hq) (hI.blockBase_inBox hq₂) h2)

/-- **The blocks of the interpolation of `H` are the images of those of `G`.** -/
theorem blockIdx_image (hI : OmegaIso G H ρ) : (blockIdx G).image cm = blockIdx H := by
  ext q'
  constructor
  · intro h
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 h
    exact hI.mem_blockIdx_map hq
  · intro h
    obtain ⟨q, hq, rfl⟩ := hI.exists_blockIdx_of h
    exact Finset.mem_image_of_mem _ hq

/-- The bump of a block of the box at a site of the box. -/
theorem bump_eq (hI : OmegaIso G H ρ) {m : ℕ} (hm : m ≤ K) {x y0 : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) (hy0 : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y0) :
    bump m (bm y0) (bm x) = bump m y0 x := by
  have hLm : L ^ m ≤ L ^ K := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) hm
  have h1 := hI.two_lt.1; have h2 := hI.two_lt.2
  exact bump_boxMap m x y0 hx hy0 (by omega) (by omega) (by omega) (by omega)

/-- The denominator of the interpolation weights at a site of the box. -/
theorem denom_eq (hI : OmegaIso G H ρ) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) : denom H (bm x) = denom G x := by
  unfold denom
  rw [← hI.blockIdx_image, Finset.sum_image hI.blockIdx_injOn]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨⟨-, h2⟩, -, -⟩ := (mem_blockIdx G).1 hq
  exact hI.bump_eq h2 hx (hI.blockBase_inBox hq)

/-- **The interpolated field at a site of the box**, for values corresponding at the bases of the
blocks. -/
theorem interp_eq (hI : OmegaIso G H ρ) {Φ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {Φ' : CTorus d L N₁' m₁ K → Fin N → ℂ} (hΦ : ∀ q ∈ blockIdx G, Φ' (bm q.2) = Φ q.2)
    {x : CTorus d L N₁ m₁ K} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    interp H Φ' (bm x) = interp G Φ x := by
  unfold interp
  rw [← hI.blockIdx_image, Finset.sum_image hI.blockIdx_injOn]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨⟨-, h2⟩, -, -⟩ := (mem_blockIdx G).1 hq
  have hw : weight H (cm q) (bm x) = weight G q x := by
    unfold weight
    rw [hI.denom_eq hx]
    exact congrArg (· / denom G x) (hI.bump_eq h2 hx (hI.blockBase_inBox hq))
  show ((weight H (cm q) (bm x) : ℝ) : ℂ) • Φ' (bm q.2) = _
  rw [hw, hΦ q hq]

/-! ### The approximate field and the residual -/

/-- The mass of the block at a site of `Ω₁`. -/
theorem blockMass_eq (hI : OmegaIso G H ρ) (ν : ℝ) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) :
    blockMass H ν (bm x) = blockMass G ν x := by
  unfold blockMass; rw [hI.layerIndex_eq hx]

/-- **The local solutions at a site of the box of radius `ρ + 1`.** -/
theorem locSol_eq (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (ν : ℝ)
    {Ψ h : CTorus d L N₁ m₁ K → Fin N → ℂ} {Ψ' h' : CTorus d L N₁' m₁ K → Fin N → ℂ}
    {y : CTorus d L N₁ m₁ K} (hy : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) y)
    (hΨ : Ψ' (bm y) = Ψ y) (hh : h' (bm y) = h y) :
    locSol H a ν Ψ' h' (bm y) = locSol G a ν Ψ h y := by
  unfold locSol
  by_cases hmem : y ∈ G.Ω 1
  · have hmem' : bm y ∈ H.Ω 1 := (hI.mem_iff hy).2 hmem
    simp only [hmem, hmem', ↓reduceIte]
    rw [hI.layerIndex_eq hmem, hI.blockMass_eq ν hmem, hΨ, hh]
  · have hmem' : bm y ∉ H.Ω 1 := fun h => hmem ((hI.mem_iff hy).1 h)
    simp only [hmem, hmem', ↓reduceIte]
    rw [hΨ]

/-- **The approximate field `φ₀` at a site of the box of radius `ρ + 1`**, for data corresponding
on that box. -/
theorem approxField_eq (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (ν : ℝ)
    {Ψ h : CTorus d L N₁ m₁ K → Fin N → ℂ} {Ψ' h' : CTorus d L N₁' m₁ K → Fin N → ℂ}
    (hΨ : FieldCorr (ρ + 1) Ψ Ψ') (hh : FieldCorr (ρ + 1) h h')
    {x : CTorus d L N₁ m₁ K} (hx : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) x) :
    approxField H a ν Ψ' h' (bm x) = approxField G a ν Ψ h x := by
  unfold approxField
  by_cases hmem : x ∈ G.Ω 1
  · have hxρ := hI.boxG x hmem
    have hmem' : bm x ∈ H.Ω 1 := (hI.mem_iff hx).2 hmem
    simp only [hmem, hmem', ↓reduceIte]
    rw [hI.layerIndex_eq hmem]
    split_ifs
    · exact hI.locSol_eq a ν hx (hΨ x hx) (hh x hx)
    · congr 1
      refine hI.interp_eq (fun q hq => ?_) hxρ
      have hq1 := inBox_mono (Nat.le_succ ρ) (hI.blockBase_inBox hq)
      exact hI.locSol_eq a ν hq1 (hΨ _ hq1) (hh _ hq1)
  · have hmem' : bm x ∉ H.Ω 1 := fun h => hmem ((hI.mem_iff hx).1 h)
    simp only [hmem, hmem', ↓reduceIte, hI.collar_iff hx]
    split_ifs
    · exact hI.locSol_eq a ν hx (hΨ x hx) (hh x hx)
    · rfl

/-- The image of a site of `Ω₁` and its neighbours lie in the box of radius `ρ + 1`. -/
theorem nbr_inBox (hI : OmegaIso G H ρ) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) (μ : Fin d) :
    InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) (x + Pi.single μ 1) ∧
      InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) (x - Pi.single μ 1) := by
  have h1 := hI.two_lt.1
  exact ⟨inBox_add_single (by omega) (hI.boxG x hx) μ,
    inBox_sub_single (by omega) (hI.boxG x hx) μ⟩

/-- **The source `S(Ψ, h̃)`** at corresponding sites of `Ω₁`, for data corresponding on the box of
radius `ρ + 1`. -/
theorem source_eq (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (ν : ℝ) {D : BgData G N} {D' : BgData H N}
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h) (x : G.Ω 1) (i : Fin N) :
    source H a ν D' (hI.e x, i) = source G a ν D (x, i) := by
  have hiso := gsIso_of_omega (N₁ := N₁) (N₁' := N₁') a ν (ρ := ρ) hI.hK hI.two_lt.1 hI.two_lt.2
    hI.boxG hI.boxH (fun z hz n h1 h2 => hI.corr z hz n h1 h2)
  exact hiso.source N D D' (fun z hz => ⟨(hΨ z hz).symm, (hh z hz).symm⟩) x _ i

/-- **The residual `f₀ = S - H_D(0) φ₀`** at corresponding sites of `Ω₁`, for data and fields
corresponding on the box of radius `ρ + 1`. -/
theorem residual_eq (hI : OmegaIso G H ρ) (a : ℕ → ℝ) (ν : ℝ) {D : BgData G N} {D' : BgData H N}
    (hΨ : FieldCorr (ρ + 1) D.Ψ D'.Ψ) (hh : FieldCorr (ρ + 1) D.h D'.h)
    {φ : CTorus d L N₁ m₁ K → Fin N → ℂ} {φ' : CTorus d L N₁' m₁ K → Fin N → ℂ}
    (hφ : FieldCorr (ρ + 1) φ φ') (x : G.Ω 1) (i : Fin N) :
    Background.residual H a ν D' φ' (hI.e x, i) = Background.residual G a ν D φ (x, i) := by
  unfold Background.residual
  simp only [Pi.sub_apply]
  rw [hI.source_eq a ν hΨ hh x i]
  congr 1
  refine liftOp_mulVec_corr hI.e (entry_of_submatrix hI.e
    (hI.dirichletOperator_submatrix a ν (fun _ => rfl))) (fun y j => ?_) x i
  show φ' (bm (y : CTorus d L N₁ m₁ K)) j = φ y j
  rw [hφ _ (hI.inBox_succ y.2)]

/-- The term `Q* a Ψ` at corresponding sites of `Ω₁`. -/
theorem qStar_eq (hI : OmegaIso G H ρ) (a : ℕ → ℝ) {Ψ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {Ψ' : CTorus d L N₁' m₁ K → Fin N → ℂ} (hΨ : FieldCorr (ρ + 1) Ψ Ψ') (x : G.Ω 1)
    (i : Fin N) : qStar H a Ψ' (hI.e x, i) = qStar G a Ψ (x, i) := by
  unfold qStar
  simp only [coe_e]
  rw [hI.layerIndex_eq x.2, hΨ _ (hI.inBox_succ x.2)]

/-- The collar term `𝔟(Ψ)` at corresponding sites of `Ω₁`. -/
theorem boundaryTerm_eq (hI : OmegaIso G H ρ) {Ψ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {Ψ' : CTorus d L N₁' m₁ K → Fin N → ℂ} (hΨ : FieldCorr (ρ + 1) Ψ Ψ') (x : G.Ω 1)
    (i : Fin N) : boundaryTerm H Ψ' (hI.e x, i) = boundaryTerm G Ψ (x, i) := by
  unfold boundaryTerm
  have hxb := hI.boxG x x.2
  have h1 := hI.two_lt.1; have h2 := hI.two_lt.2
  refine Finset.sum_congr rfl fun μ _ => ?_
  obtain ⟨hp, hm⟩ := hI.nbr_inBox x.2 μ
  have e1 : ((hI.e x : H.Ω 1) : CTorus d L N₁' m₁ K) + Pi.single μ 1 =
      bm ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) := by
    rw [coe_e, boxMap_add_single (ρ := ρ) (by omega) (by omega) hxb μ]
  have e2 : ((hI.e x : H.Ω 1) : CTorus d L N₁' m₁ K) - Pi.single μ 1 =
      bm ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) := by
    rw [coe_e, boxMap_sub_single (ρ := ρ) (by omega) (by omega) hxb μ]
  simp only [e1, e2, hI.collar_iff hp, hI.collar_iff hm, hΨ _ hp, hΨ _ hm]

/-- **The source `F_s = Q* a δΨ + 𝔟(δΨ) + f₁` of the perturbed problem.** -/
theorem pertSource_eq (hI : OmegaIso G H ρ) (a : ℕ → ℝ) {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {δΨ' : CTorus d L N₁' m₁ K → Fin N → ℂ} (hΨ : FieldCorr (ρ + 1) δΨ δΨ')
    {f₁ : G.Ω 1 × Fin N → ℂ} {f₁' : H.Ω 1 × Fin N → ℂ} (hf : ∀ x i, f₁' (hI.e x, i) = f₁ (x, i))
    (x : G.Ω 1) (i : Fin N) :
    pertSource H a δΨ' f₁' (hI.e x, i) = pertSource G a δΨ f₁ (x, i) := by
  unfold pertSource
  simp only [Pi.add_apply]
  rw [hI.qStar_eq a hΨ x i, hI.boundaryTerm_eq hΨ x i, hf]

end OmegaIso

end Balaban.Polymer.LocalIso
