/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidOut
public import Balaban.LargeField.R.RRemovedHidVar

/-!
# The regrouping of the window integral with the node and the shell variables exposed (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstruction (1).  `exists_regroup_shell`: the regrouping
`Θ` of `exists_regroup_nodes` (W923) in which no coordinate is hidden: the window variables
`(ψ_m↾Z₀, tree group, x↾T)`, the core variables, the node variables (outputs at the blocks of `G₃`,
`x↾Nd`, and all the inner outputs `ψ'_m↾Z₀`, which are Gaussian nodes when `Z₀` lies in the Gaussian
blocks) and the shell variables (the remaining outputs `RO`, the remaining coordinates `Sh` of `x`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section Shell

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The regrouping `Θ` with the node and the shell variables exposed** (the explicit form of
`exists_regroup_nodes`).  The integration variables `(ψ_m↾Z, x, ψ'_m↾Z₀)` are regrouped, measure
preservingly, into the window `(ψ_m↾Z₀, tree group, x↾T)`, the core variables, the outputs at `G₃`
and the shell outputs `RO`, the coordinates `x↾Nd` and the shell coordinates `Sh`, and `ψ'_m↾Z₀`; the
coordinates of every part are given by explicit formulas. -/
theorem exists_regroup_shell {k1 m : ℕ} (h : k1 < m) (hmK : m ≤ K) {Z : H.Comp m}
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
    (G3 : Set (BlockAt S n M K m))
    (hG3 : ∀ y ∈ G3, y ∈ Vblk R (H.localHistory M K m Z) m ∧ ZBlk (H.localHistory M K m Z) m y ∧
      y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y)) :
    ∃ (κc : (Σ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
        OutIdx (K := K) (M := M) R C.2.1 ⊕
          ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A) →
        ↥(locOp geo cs SD KD hH lab m hmK Z).A)
      (Θ : OutZ N R (H.localHistory M K m Z) m ×
          (SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A ×
            OutZero N R (H.localHistory M K m Z) m Z0) ≃ᵐ
        (OutZero N R (H.localHistory M K m Z) m Z0 × (OutPart N V2 P2 ×
            (∀ t : ↥T, VarVal N t.1.1.isSpin))) ×
          ((∀ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
            OutZ N R (H.localHistory M K k1 C.2.1) k1 ×
              SubCfg N (H.localHistory M K k1 C.2.1) k1
                (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A) ×
            ((OutPart N (Vblk R (H.localHistory M K m Z) m) (· ∈ G3) ×
              OutPart N (Vblk R (H.localHistory M K m Z) m)
                (fun y => ZBlk (H.localHistory M K m Z) m y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧
                  y ∉ G3)) ×
              (((∀ t : ↥Nd, VarVal N t.1.1.isSpin) ×
                (∀ t : {p : ↥(locOp geo cs SD KD hH lab m hmK Z).A //
                  p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin)) ×
                OutZero N R (H.localHistory M K m Z) m Z0)))),
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
            (((outPartMeasure N (Vblk R (H.localHistory M K m Z) m) (· ∈ G3)).prod
              (outPartMeasure N (Vblk R (H.localHistory M K m Z) m)
                (fun y => ZBlk (H.localHistory M K m Z) m y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧
                  y ∉ G3))).prod
              (((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
                (Measure.pi fun t : {p : ↥(locOp geo cs SD KD hH lab m hmK Z).A //
                  p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => varMeasure N t.1.1.isSpin)).prod
                (outPartMeasure N (Vblk R (H.localHistory M K m Z) m) (· ∈ Z0)))))) ∧
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
      (∀ ω (y : {y // y ∈ Vblk R (H.localHistory M K m Z) m ∧
          (ZBlk (H.localHistory M K m Z) m y ∧ y ∉ Z0 ∧ ¬ (y ∈ V2 ∧ P2 y) ∧ y ∉ G3)}),
        (Θ ω).2.2.1.2 y = ω.1 ⟨y.1, y.2.1, y.2.2.1⟩) ∧
      (∀ ω (t : ↥Nd), (Θ ω).2.2.2.1.1 t = ω.2.1 t.1) ∧
      (∀ ω (t : {p : ↥(locOp geo cs SD KD hH lab m hmK Z).A //
          p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}), (Θ ω).2.2.2.1.2 t = ω.2.1 t.1) ∧
      (∀ ω, (Θ ω).2.2.2.2 = ω.2.2) := by
  obtain ⟨Ψo, hΨo, co1, co2, co3, co4⟩ := exists_out_shell (N := N)
    (H.localHistory M K m Z) m Z0 V2 P2 G3 hZ0 hV2 hG3
  obtain ⟨κc, Ψx, hinj, hκ1, hκ2, hΨx, cT, cN, cS, cK1, cK2⟩ :=
    exists_var_shell geo cs SD KD h hmK hq T hTo hTi Nd hNj hNT
  obtain ⟨Θ, hΘm, hΘ⟩ := exists_assemble Ψo hΨo Ψx hΨx 
    (MeasurableEquiv.refl (OutZero N R (H.localHistory M K m Z) m Z0))
    (MeasurePreserving.id (outPartMeasure N (Vblk R (H.localHistory M K m Z) m) (· ∈ Z0)))
  refine ⟨κc, Θ, hinj, hκ1, hκ2, hΘm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro ω y
    exact (congrArg (fun p => p.2.2.1.2 y) (hΘ ω)).trans (co4 ω.1 y)
  · intro ω t
    exact (congrArg (fun p => p.2.2.2.1.1 t) (hΘ ω)).trans (cN ω.2.1 t)
  · intro ω t
    exact (congrArg (fun p => p.2.2.2.1.2 t) (hΘ ω)).trans (cS ω.2.1 t)
  · intro ω
    exact congrArg (fun p => p.2.2.2.2) (hΘ ω)

end Shell

end Balaban.LargeField
