/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainRegroupOut
public import Balaban.LargeField.R.RRemovedChainRegroupVar

/-!
# The regrouping of the window integral exposing the Gaussian node coordinates (W923)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, item (2).  A refinement of `exists_regroup`: the
variables integrated first (`Jv`) are split into the coordinates of the Gaussian nodes (the internal
variables `Nd` of scales above `k₁`, the outputs at a set `G₃` of top blocks outside the window groups,
the inner outputs `ψ_m↾Z₀` at a set `G₀ ⊆ Z₀`) and the remaining coordinates.  The coordinates of every
part are given by explicit formulas, and the internal variables that are not nodes are read from the
window, the core and the rest components alone (`hindep`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section Nodes

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The regrouping `Θ` exposing the Gaussian node coordinates** (a refinement of `exists_regroup`).
Along a quiet window `[k₁, m)` of `Z`, the integration variables `(ψ_m↾Z, x, ψ'_m↾Z₀)` are regrouped,
measure preservingly, into

* the window variables `(ψ_m↾Z₀, tree group `(V₂, P₂)`, coordinates of `x` in `T`)` and the core variables
  (as in `exists_regroup`, with the same coordinate formulas),
* the node variables: the outputs `ψ_m` at the blocks of `G₃` (outside `Z₀` and the tree group), the
  coordinates of `x` in `Nd` (variables of scales above `k₁`), the inner outputs `ψ'_m` at the blocks of
  `G₀ ⊆ Z₀`,
* the remaining coordinates `RO`, `RX`, `RW` of the outputs, of `x` and of the inner outputs.

`hindep`: the coordinates of `x` outside `Nd` are determined by the window, the core and the remaining
`x`-components, so they do not move with the node variables. -/
theorem exists_regroup_nodes {k1 m : ℕ} (h : k1 < m) (hmK : m ≤ K) {Z : H.Comp m}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s m Y Z → ¬ IsKept H s Y)
    (Z0 : Set (BlockAt S n M K m)) (V2 : Set (BlockAt S n M K m)) (P2 : BlockAt S n M K m → Prop)
    (hZ0 : ∀ y ∈ Vblk R (H.localHistory M K m Z) m, y ∈ Z0 → ZBlk (H.localHistory M K m Z) m y)
    (hV2 : ∀ y, y ∈ V2 → P2 y → y ∈ Vblk R (H.localHistory M K m Z) m ∧
      ZBlk (H.localHistory M K m Z) m y ∧ y ∉ Z0)
    (T : Set ↥(locOp geo cs SD KD hH lab m hmK Z).A) [Fintype ↑T]
    (hTo : ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
      (y : OutIdx (K := K) (M := M) R C.2.1)
      (hy : (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (oldVar (by omega) C.1.1 C.2.2 y).1.1,
              (oldVar (by omega) C.1.1 C.2.2 y).1.2.1, (oldVar (by omega) C.1.1 C.2.2 y).1.2.2⟩,
            inclVar_mem hmK (mem_ancFin.mp C.1.2) (oldVar (by omega) C.1.1 C.2.2 y)⟩ :
            InternalVars (H.localHistory M K m Z) m) ∈ (locOp geo cs SD KD hH lab m hmK Z).A),
      (⟨_, hy⟩ : ↥(locOp geo cs SD KD hH lab m hmK Z).A) ∉ T)
    (hTi : ∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
      (q : ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A)
      (hy : (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (ancInc (by omega) C.2.2 q.1).1.1,
              (ancInc (by omega) C.2.2 q.1).1.2.1, (ancInc (by omega) C.2.2 q.1).1.2.2⟩,
            inclVar_mem hmK (mem_ancFin.mp C.1.2) (ancInc (by omega) C.2.2 q.1)⟩ :
            InternalVars (H.localHistory M K m Z) m) ∈ (locOp geo cs SD KD hH lab m hmK Z).A),
      (⟨_, hy⟩ : ↥(locOp geo cs SD KD hH lab m hmK Z).A) ∉ T)
    (Nd : Set ↥(locOp geo cs SD KD hH lab m hmK Z).A) [Fintype ↑Nd]
    (hNj : ∀ p ∈ Nd, k1 < ((p.1.1.1 : Fin m) : ℕ)) (hNT : ∀ p ∈ Nd, p ∉ T)
    (G3 G0 : Set (BlockAt S n M K m))
    (hG3 : ∀ y ∈ G3, y ∈ Vblk R (H.localHistory M K m Z) m ∧ ZBlk (H.localHistory M K m Z) m y ∧
      y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y))
    (hG0 : ∀ y ∈ G0, y ∈ Z0) :
    ∃ (κc : (Σ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
        OutIdx (K := K) (M := M) R C.2.1 ⊕
          ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A) →
        ↥(locOp geo cs SD KD hH lab m hmK Z).A)
      (RO RX RW : Type) (_ : MeasurableSpace RO) (_ : MeasurableSpace RX) (_ : MeasurableSpace RW)
      (μRO : Measure RO) (μRX : Measure RX) (μRW : Measure RW)
      (_ : SFinite μRO) (_ : SFinite μRX) (_ : SFinite μRW)
      (Θ : OutZ N R (H.localHistory M K m Z) m ×
          (SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A ×
            OutZero N R (H.localHistory M K m Z) m Z0) ≃ᵐ
        (OutZero N R (H.localHistory M K m Z) m Z0 × (OutPart N V2 P2 ×
            (∀ t : ↥T, VarVal N t.1.1.isSpin))) ×
          ((∀ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
            OutZ N R (H.localHistory M K k1 C.2.1) k1 ×
              SubCfg N (H.localHistory M K k1 C.2.1) k1
                (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A) ×
            ((OutPart N (Vblk R (H.localHistory M K m Z) m) (· ∈ G3) × RO) ×
              (((∀ t : ↥Nd, VarVal N t.1.1.isSpin) × RX) ×
                (OutPart N (Vblk R (H.localHistory M K m Z) m) (· ∈ G0) × RW))))),
      Function.Injective κc ∧
      (∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
        (y : OutIdx (K := K) (M := M) R C.2.1),
        (κc ⟨C, Sum.inl y⟩).1 =
          (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (oldVar (by omega) C.1.1 C.2.2 y).1.1,
              (oldVar (by omega) C.1.1 C.2.2 y).1.2.1, (oldVar (by omega) C.1.1 C.2.2 y).1.2.2⟩,
            inclVar_mem hmK (mem_ancFin.mp C.1.2) (oldVar (by omega) C.1.1 C.2.2 y)⟩ :
            InternalVars (H.localHistory M K m Z) m)) ∧
      (∀ (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
        (q : ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A),
        (κc ⟨C, Sum.inr q⟩).1 =
          (⟨⟨Fin.castLE (mem_ancFin.mp C.1.2).le (ancInc (by omega) C.2.2 q.1).1.1,
              (ancInc (by omega) C.2.2 q.1).1.2.1, (ancInc (by omega) C.2.2 q.1).1.2.2⟩,
            inclVar_mem hmK (mem_ancFin.mp C.1.2) (ancInc (by omega) C.2.2 q.1)⟩ :
            InternalVars (H.localHistory M K m Z) m)) ∧
      MeasurePreserving Θ
        ((outPartMeasure N (Vblk R (H.localHistory M K m Z) m) (ZBlk (H.localHistory M K m Z) m)).prod
          ((subMeasure N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A).prod
            (outPartMeasure N (Vblk R (H.localHistory M K m Z) m) (· ∈ Z0))))
        (((outPartMeasure N (Vblk R (H.localHistory M K m Z) m) (· ∈ Z0)).prod
          ((outPartMeasure N V2 P2).prod
            (Measure.pi fun t : ↥T => varMeasure N t.1.1.isSpin))).prod
          ((Measure.pi fun C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)) =>
            (outPartMeasure N (Vblk R (H.localHistory M K k1 C.2.1) k1)
              (ZBlk (H.localHistory M K k1 C.2.1) k1)).prod
            (subMeasure N (H.localHistory M K k1 C.2.1) k1
              (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A)).prod
            (((outPartMeasure N (Vblk R (H.localHistory M K m Z) m) (· ∈ G3)).prod μRO).prod
              (((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod μRX).prod
                ((outPartMeasure N (Vblk R (H.localHistory M K m Z) m) (· ∈ G0)).prod μRW))))) ∧
      (∀ ω (y : {y // y ∈ Vblk R (H.localHistory M K m Z) m ∧ y ∈ Z0}),
        (Θ ω).1.1 y = ω.1 ⟨y.1, y.2.1, hZ0 _ y.2.1 y.2.2⟩) ∧
      (∀ ω (y : {y // y ∈ V2 ∧ P2 y}),
        (Θ ω).1.2.1 y = ω.1 ⟨y.1, (hV2 y.1 y.2.1 y.2.2).1, (hV2 y.1 y.2.1 y.2.2).2.1⟩) ∧
      (∀ ω (t : ↥T), (Θ ω).1.2.2 t = ω.2.1 t.1) ∧
      (∀ ω (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
        (y : OutIdx (K := K) (M := M) R C.2.1),
        ((Θ ω).2.1 C).1 y = VarVal.toEuc (ω.2.1 (κc ⟨C, Sum.inl y⟩))) ∧
      (∀ ω (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
        (q : ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A),
        VarVal.toEuc (((Θ ω).2.1 C).2 q) = VarVal.toEuc (ω.2.1 (κc ⟨C, Sum.inr q⟩))) ∧
      (∀ ω (y : {y // y ∈ Vblk R (H.localHistory M K m Z) m ∧ y ∈ G3}),
        (Θ ω).2.2.1.1 y = ω.1 ⟨y.1, y.2.1, (hG3 y.1 y.2.2).2.1⟩) ∧
      (∀ ω (t : ↥Nd), (Θ ω).2.2.2.1.1 t = ω.2.1 t.1) ∧
      (∀ ω (y : {y // y ∈ Vblk R (H.localHistory M K m Z) m ∧ y ∈ G0}),
        (Θ ω).2.2.2.2.1 y = ω.2.2 ⟨y.1, y.2.1, hG0 y.1 y.2.2⟩) ∧
      (∀ ω ω', (Θ ω).1 = (Θ ω').1 → (Θ ω).2.1 = (Θ ω').2.1 →
        (Θ ω).2.2.2.1.2 = (Θ ω').2.2.2.1.2 →
        ∀ p : ↥(locOp geo cs SD KD hH lab m hmK Z).A, p ∉ Nd →
          VarVal.toEuc (ω.2.1 p) = VarVal.toEuc (ω'.2.1 p)) := by
  obtain ⟨RO, _, μRO, _, Ψo, hΨo, co1, co2, co3⟩ := exists_out_nodes (N := N)
    (H.localHistory M K m Z) m Z0 V2 P2 G3 hZ0 hV2 hG3
  obtain ⟨RW, _, μRW, _, Ψw, hΨw, cw⟩ := exists_inner_nodes (N := N)
    (H.localHistory M K m Z) m Z0 G0 hG0
  obtain ⟨κc, RX, _, μRX, _, Ψx, hinj, hκ1, hκ2, hΨx, cT, cN, cK1, cK2, hind⟩ :=
    exists_var_nodes geo cs SD KD h hmK hq T hTo hTi Nd hNj hNT
  obtain ⟨Θ, hΘm, hΘ⟩ := exists_assemble Ψo hΨo Ψx hΨx Ψw hΨw
  refine ⟨κc, RO, RX, RW, _, _, _, μRO, μRX, μRW, inferInstance, inferInstance, inferInstance, Θ,
    hinj, hκ1, hκ2, hΘm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω y
    exact (congrArg (fun p => p.1.1 y) (hΘ ω)).trans (co1 ω.1 y)
  · intro ω y
    exact (congrArg (fun p => p.1.2.1 y) (hΘ ω)).trans (co2 ω.1 y)
  · intro ω t
    exact (congrArg (fun p => p.1.2.2 t) (hΘ ω)).trans (cT ω.2.1 t)
  · intro ω C y
    exact (congrArg (fun p => (p.2.1 C).1 y) (hΘ ω)).trans (cK1 ω.2.1 C y)
  · intro ω C q
    exact (congrArg (fun p => VarVal.toEuc ((p.2.1 C).2 q)) (hΘ ω)).trans (cK2 ω.2.1 C q)
  · intro ω y
    exact (congrArg (fun p => p.2.2.1.1 y) (hΘ ω)).trans (co3 ω.1 y)
  · intro ω t
    exact (congrArg (fun p => p.2.2.2.1.1 t) (hΘ ω)).trans (cN ω.2.1 t)
  · intro ω y
    exact (congrArg (fun p => p.2.2.2.2.1 y) (hΘ ω)).trans (cw ω.2.2 y)
  · intro ω ω' h1 h2 h3 p hp
    refine hind ω.2.1 ω'.2.1 ?_ ?_ ?_ p hp
    · exact (congrArg (fun p => p.2.1) (hΘ ω)).symm.trans
        (h2.trans (congrArg (fun p => p.2.1) (hΘ ω')))
    · exact (congrArg (fun p => p.1.2.2) (hΘ ω)).symm.trans
        ((congrArg (fun p => p.2.2) h1).trans (congrArg (fun p => p.1.2.2) (hΘ ω')))
    · exact (congrArg (fun p => p.2.2.2.1.2) (hΘ ω)).symm.trans
        (h3.trans (congrArg (fun p => p.2.2.2.1.2) (hΘ ω')))

end Nodes

end Balaban.LargeField
