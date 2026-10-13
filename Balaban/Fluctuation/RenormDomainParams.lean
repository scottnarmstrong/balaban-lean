/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormLocFibre
public import Balaban.Fluctuation.RenormExpBounds
public import Balaban.Fluctuation.InteractionEngine
public import Balaban.Fluctuation.InteractionLevelPair
public import Balaban.Inhabited.XiCDomains
public import Balaban.Localization.DomainLemma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The domain inclusion and the parameter identification for the renormalization localization

`locC1` itself is NOT proved here, and neither are `locC2` and `locDφ`.  This file is the zero
class of the localization of `RenormExpInput`: two short facts that the later steps use, both
independent of the choice of the generating set beyond the hypotheses stated.

**Leaf 1 (the data domain).**  A datum of `XiCOneReal` (a real `Ψ₀`, a real constant `h₀` and a
complex `Ψ''`, with no complex displacement of `h`) is a datum of `XiCData G a ν K 1 ε`
(`xiCData_of_xiCOneReal`), hence, under the smallness and `c₇` margin of `FlCore`, a point of the
data domain `Ψ̃^c(δ, δ)` with `δ = C₁ ε` (`inDomainC_of_xiCOneReal`) and of the union domain at
the margin `c₇` (`renXiCOneReal_inUnionC7`).  The union domain is the hypothesis on the datum of
the decoupled background theorems.

**Leaf 2 (the parameters).**  The label type `RenLabel G X₁` of the renormalization cover is the
same set as `ParIdx G X₁`, the free parameters of the physical cover (the cubes whose patch misses
`X₁`): `renLabelEquiv`.  With the setup `PolySetup G m₀ X₁`, a cube of the cover is a parameter
cube (`parCubes`) exactly when its patch misses `X₁` (`mem_parCubes_iff_disjoint`), so the
parameter cubes are the range of `renCube` (`coe_parCubes_eq_range_renCube`).  Evaluation of
`extParams` on a vector indexed by labels: `renExt_label`, `renExt_one`, and the zero and one laws
at a cut vector (`renExt_extS_zero`, `renExt_extS_label`, `renExt_one_of_not_mem_parCubes`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis Finset

section Leaf1

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The definitional inclusion.**  A datum of `XiCOneReal G a ν ε` is a datum of
`XiCData G a ν K 1 ε`: the same witnesses, with `h'' = 0`. -/
theorem xiCData_of_xiCOneReal {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν ε : ℝ}
    {D : BgData G N} (h : XiCOneReal G a ν ε D) : XiCData G a ν K 1 ε D := by
  obtain ⟨Ψ₀, h₀, Ψ'', hX, hR⟩ := h
  exact ⟨Ψ₀, h₀, Ψ'', 0, hX, hR⟩

/-- Under `FlCore`, a datum of `XiCOneReal` lies in the data domain `Ψ̃^c(δ, δ)`,
`δ = C₁ ε`. -/
theorem inDomainC_of_xiCOneReal
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {D : BgData Gp N}
    (hD : XiCOneReal Gp (compWeight L a₁) ν eps D) :
    InDomainC Gp ν (xiC1 d * eps) (xiC1 d * eps) D :=
  xiCData_inDomainC hC.HBp hC.small1 (xiCData_of_xiCOneReal hD)

/-- **A datum of `XiCOneReal` lies in the union domain at the margin `c₇`.**  Under `FlCore`
(its smallness `small1` and its margin `c7le`): the datum premise of the decoupled background
theorems `i4b_*`, with `δ = C₁ ε`, `0 < δ ≤ bgC0`, `δ ≤ c₇`. -/
theorem renXiCOneReal_inUnionC7
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {D : BgData Gp N}
    (hD : XiCOneReal Gp (compWeight L a₁) ν eps D) :
    InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hδ0 : 0 < xiC1 d * eps := by
    have := one_le_xiC1 d
    have := hC.eps_pos
    positivity
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N :=
    hδ1.trans ((c7_le_bgC1 d L N BG κ).trans (bgC1_le_bgC0 d L N hd0))
  exact inUnionDomainC_of_inDomainC hC.HBp hδ0 hδ0' hδ1 (inDomainC_of_xiCOneReal hC hD)

end Leaf1

section Leaf2

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- **The labels are the free parameters**: `RenLabel G X₁` and `ParIdx G X₁` are the same
subtype of cubes of the cover, nested in the two possible ways. -/
def renLabelEquiv (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (X₁ : Set (CTorus d L N₁ m₁ K)) :
    RenLabel G X₁ ≃ ParIdx G X₁ where
  toFun i := ⟨⟨i.1, i.2.1⟩, i.2.2⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem renLabelEquiv_cube (X₁ : Set (CTorus d L N₁ m₁ K)) (i : RenLabel G X₁) :
    ((renLabelEquiv G X₁ i).1 : ℕ × CTorus d L N₁ m₁ K) = renCube G X₁ i := rfl

/-- The extension `extParams` evaluated at a label is the value of the vector at that label. -/
theorem renExt_label (X₁ : Set (CTorus d L N₁ m₁ K)) (t : RenLabel G X₁ → ℂ) (i : RenLabel G X₁) :
    extParams G X₁ (t ∘ (renLabelEquiv G X₁).symm) ⟨renCube G X₁ i, renCube_mem G X₁ i⟩ =
      t i := by
  have := extParams_par (G := G) (X₁ := X₁) (t ∘ (renLabelEquiv G X₁).symm)
    (renLabelEquiv G X₁ i)
  exact this.trans (by simp)

/-- At the all-ones vector of labels the extension is the all-ones parameter vector. -/
theorem renExt_one (X₁ : Set (CTorus d L N₁ m₁ K)) :
    extParams G X₁ ((1 : RenLabel G X₁ → ℂ) ∘ (renLabelEquiv G X₁).symm) = fun _ => 1 := by
  have : ((1 : RenLabel G X₁ → ℂ) ∘ (renLabelEquiv G X₁).symm) = 1 := rfl
  rw [this]
  exact extParams_one

/-- **The parameter cubes are the cubes whose patch misses `X₁`**, for `X₁` a union of aligned
cubes (`PolySetup`; for the physical cover, `CovSetup.polySetup`). -/
theorem mem_parCubes_iff_disjoint {m₀ : ℕ} {X₁f : Finset (CTorus d L N₁ m₁ K)}
    (hS : PolySetup G m₀ (↑X₁f : Set (CTorus d L N₁ m₁ K))) {P : ℕ × CTorus d L N₁ m₁ K}
    (hP : P ∈ cubeIdx G) :
    P ∈ parCubes G X₁f ↔ Disjoint (Pset m₁ P) (↑X₁f : Set (CTorus d L N₁ m₁ K)) := by
  constructor
  · intro hPar
    by_contra hnd
    have hsub := Pset_subset_of_not_disjoint hS hP hnd
    unfold parCubes at hPar
    rw [Finset.mem_filter] at hPar
    apply hPar.2
    intro y hy
    exact Finset.mem_coe.1 (hsub (mem_cubeP.1 hy))
  · intro hdisj
    unfold parCubes
    rw [Finset.mem_filter]
    refine ⟨hP, fun hsub => ?_⟩
    have hmem : P.2 ∈ cubeP P := mem_cubeP.2 (SameCell.refl _ _)
    exact Set.disjoint_left.1 hdisj (self_mem_Pset P) (Finset.mem_coe.2 (hsub hmem))

/-- The parameter cubes are exactly the image of the labels. -/
theorem coe_parCubes_eq_range_renCube {m₀ : ℕ} {X₁f : Finset (CTorus d L N₁ m₁ K)}
    (hS : PolySetup G m₀ (↑X₁f : Set (CTorus d L N₁ m₁ K))) :
    (↑(parCubes G X₁f) : Set (ℕ × CTorus d L N₁ m₁ K)) =
      Set.range (renCube G (↑X₁f : Set (CTorus d L N₁ m₁ K))) := by
  ext P
  constructor
  · intro hP
    have hP' : P ∈ parCubes G X₁f := hP
    have hc : P ∈ cubeIdx G := (Finset.mem_filter.1 hP').1
    exact ⟨⟨P, hc, (mem_parCubes_iff_disjoint hS hc).1 hP'⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact (mem_parCubes_iff_disjoint hS (renCube_mem G _ i)).2 (renCube_disjoint G _ i)

/-- **One law**: a cube of the cover that is not a parameter cube carries the parameter `1`. -/
theorem renExt_one_of_not_mem_parCubes {X₁f : Finset (CTorus d L N₁ m₁ K)}
    (s : ParIdx G (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) {P : ℕ × CTorus d L N₁ m₁ K}
    (hP : P ∈ cubeIdx G) (hPn : P ∉ parCubes G X₁f) :
    extS G (extParams G (↑X₁f : Set (CTorus d L N₁ m₁ K)) s) P = 1 := by
  unfold extS
  simp only [hP, ↓reduceDIte]
  exact extParams_hs1 s P hP hPn

/-- **Zero law at a cut vector**: if the vector of labels vanishes off the cut family `C`, a
parameter cube that is not in `C` carries the parameter `0`. -/
theorem renExt_extS_zero {m₀ : ℕ} {X₁f : Finset (CTorus d L N₁ m₁ K)}
    (hS : PolySetup G m₀ (↑X₁f : Set (CTorus d L N₁ m₁ K)))
    (t : RenLabel G (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ)
    (C : Finset (RenLabel G (↑X₁f : Set (CTorus d L N₁ m₁ K))))
    (ht : ∀ i, i ∉ C → t i = 0) {P : ℕ × CTorus d L N₁ m₁ K}
    (hP : P ∈ parCubes G X₁f)
    (hPC : P ∉ C.image (renCube G (↑X₁f : Set (CTorus d L N₁ m₁ K)))) :
    extS G (extParams G (↑X₁f : Set (CTorus d L N₁ m₁ K))
      (t ∘ (renLabelEquiv G (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P = 0 := by
  have hc : P ∈ cubeIdx G := (Finset.mem_filter.1 hP).1
  have hd := (mem_parCubes_iff_disjoint hS hc).1 hP
  let i : RenLabel G (↑X₁f : Set (CTorus d L N₁ m₁ K)) := ⟨P, hc, hd⟩
  have hi : i ∉ C := fun h => hPC (Finset.mem_image.2 ⟨i, h, rfl⟩)
  unfold extS
  simp only [hc, ↓reduceDIte]
  have := renExt_label (G := G) (↑X₁f : Set (CTorus d L N₁ m₁ K)) t i
  rw [show (⟨P, hc⟩ : ↥(cubeIdx G)) = ⟨renCube G _ i, renCube_mem G _ i⟩ from rfl, this]
  exact ht i hi

/-- The value at a label cube of the extension is the value of the vector. -/
theorem renExt_extS_label (X₁ : Set (CTorus d L N₁ m₁ K)) (t : RenLabel G X₁ → ℂ)
    (i : RenLabel G X₁) :
    extS G (extParams G X₁ (t ∘ (renLabelEquiv G X₁).symm)) (renCube G X₁ i) = t i := by
  unfold extS
  simp only [renCube_mem G X₁ i, ↓reduceDIte]
  exact renExt_label X₁ t i

end Leaf2

section Instance

/-- **Non-vacuity at the landed pair of levels** (`d = L = 3`, `N₁ = 9`, `K = 2`): `FlCore` holds
and a datum of `XiCOneReal` exists, so the hypotheses of `renXiCOneReal_inUnionC7` are jointly
satisfiable; the datum is in the union domain.  There `X₁` is the whole torus, so `RenLabel` and
`ParIdx` are both empty, `renLabelEquiv` is the empty equivalence and `parCubes` is empty; the
statement records this, together with `PolySetup`, so that the laws of leaf 2 apply. -/
theorem renDomainParams_levelPair (N : ℕ) (hN : 0 < N) :
    ∃ (m₁ : ℕ) (ϱ BG κ eps : ℝ) (D : BgData (LevelPair.Gp m₁ ϱ) N),
      XiCOneReal (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 eps D ∧
      XiCData (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 2 1 eps D ∧
      InUnionDomainC (LevelPair.Gp m₁ ϱ) (bgC0 3 3 N) (c7 3 3 N BG κ) 0 D ∧
      PolySetup (LevelPair.Gp m₁ ϱ) 1
        (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) ∧
      IsEmpty (RenLabel (LevelPair.Gp m₁ ϱ)
        (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))) ∧
      IsEmpty (ParIdx (LevelPair.Gp m₁ ϱ)
        (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))) ∧
      parCubes (LevelPair.Gp m₁ ϱ) (Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) = ∅ := by
  obtain ⟨m₁, ϱ, c, BG, κ, eps, c₂, BG₂, δ₁, κdec, κ₀, hC, -, -, hH, -, -, hS, hX1, -⟩ :=
    LevelPair.interaction_levelPair_witness N
  have hPS : PolySetup (LevelPair.Gp m₁ ϱ) 1
      (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) := by
    rw [hX1]; exact hS.polySetup
  have hε : 0 < eps := hC.eps_pos
  obtain ⟨D, hD⟩ := Balaban.Inhabited.exists_xiCOneReal hH (LevelPair.Gp m₁ ϱ) hN
    (by simp) hε
  have hemp : IsEmpty (RenLabel (LevelPair.Gp m₁ ϱ)
      (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))) := by
    refine ⟨fun q => ?_⟩
    exact Set.disjoint_left.1 q.2.2 (self_mem_Pset q.1) (Finset.mem_coe.2 (Finset.mem_univ _))
  refine ⟨m₁, ϱ, BG, κ, eps, D, hD, xiCData_of_xiCOneReal hD,
    renXiCOneReal_inUnionC7 hC hD, hPS, hemp, ⟨fun p => hemp.false ((renLabelEquiv _ _).symm p)⟩, ?_⟩
  apply Finset.eq_empty_of_forall_notMem
  intro P hP
  have hc : P ∈ cubeIdx (LevelPair.Gp m₁ ϱ) := (Finset.mem_filter.1 hP).1
  have hd := (mem_parCubes_iff_disjoint hPS hc).1 hP
  exact hemp.false ⟨P, hc, hd⟩

end Instance

end Balaban.Localization
