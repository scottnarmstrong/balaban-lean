/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedRegroupSplit

/-!
# The regrouping `Θ` of the removed-outcome window integral (W912)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, steps (1)-(2): `exists_regroup`, the measure preserving
regrouping of the integration variables into window, core and first-integrated variables.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section Main

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

/-- **The regrouping `Θ` of the integration variables of the removed-outcome window integral**
(Lemma III.8.7, steps (1)-(2)).  Along a quiet window `[k₁, m)` of the component `Z` of scale `m`, the
integration variables of the pre-operator of `Z` (the outputs `ψ_m↾Z`, the internal variables `x` of
its operator, the inner `ψ_m↾Z₀`) are regrouped by a measure preserving equivalence `Θ` into

* the window variables `(ψ_m↾Z₀, tree group `(V₂, P₂)`, the coordinates of `x` in a set `T`)`,
* the core variables of the operators `𝕋_{k₁}(C)` of the ancestors `C` of `Z` at scale `k₁`
  (outputs `ψ_{k₁}↾Z` and internal variables of each `C`, as in `hcore_of_anc`),
* the remaining variables `Jv`, integrated first.

The core variables are the coordinates `κc` of `x` (output `y` of `C` is the variable `oldVar y` of
the ancestor `P` of scale `k₁ + 1`, an internal variable `q` of `C` is `ancInc q`, both included into
the variables of `Z`); `T` is any set of coordinates different from them.  The values of `Θ` on the
window and core variables are the corresponding coordinates (`ψ_m↾Z₀` and the tree group are the
outputs at those blocks), the core internal variables as vectors. -/
theorem exists_regroup {k1 m : ℕ} (h : k1 < m) (hmK : m ≤ K) {Z : H.Comp m}
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
      (⟨_, hy⟩ : ↥(locOp geo cs SD KD hH lab m hmK Z).A) ∉ T) :
    ∃ (κc : (Σ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
        OutIdx (K := K) (M := M) R C.2.1 ⊕
          ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A) →
        ↥(locOp geo cs SD KD hH lab m hmK Z).A)
      (Jv : Type) (_ : MeasurableSpace Jv) (μJ : Measure Jv) (_ : SFinite μJ)
      (Θ : OutZ N R (H.localHistory M K m Z) m ×
          (SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A ×
            OutZero N R (H.localHistory M K m Z) m Z0) ≃ᵐ
        (OutZero N R (H.localHistory M K m Z) m Z0 × (OutPart N V2 P2 ×
            (∀ t : ↥T, VarVal N t.1.1.isSpin))) ×
          ((∀ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
            OutZ N R (H.localHistory M K k1 C.2.1) k1 ×
              SubCfg N (H.localHistory M K k1 C.2.1) k1
                (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A) × Jv)),
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
              (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A)).prod μJ)) ∧
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
        VarVal.toEuc (((Θ ω).2.1 C).2 q) = VarVal.toEuc (ω.2.1 (κc ⟨C, Sum.inr q⟩))) := by
  obtain ⟨κc, hinj, hκ1, hκ2⟩ := exists_coreCoord geo cs SD KD h hmK hq
  obtain ⟨L, hL, μL, hμL, Ψo, hΨo, co1, co2⟩ :=
    exists_outRegroup (N := N) (R := R) (H.localHistory M K m Z) m Z0 V2 P2 hZ0 hV2
  have hT' : ∀ s, κc s ∉ T := by
    rintro ⟨C, y | q⟩ hmem
    · refine hTo C y ((hκ1 C y) ▸ (κc ⟨C, Sum.inl y⟩).2) ?_
      convert hmem using 1
      exact (Subtype.ext (hκ1 C y)).symm
    · refine hTi C q ((hκ2 C q) ▸ (κc ⟨C, Sum.inr q⟩).2) ?_
      convert hmem using 1
      exact (Subtype.ext (hκ2 C q)).symm
  let bf : (Σ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
      OutIdx (K := K) (M := M) R C.2.1 ⊕
        ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A) → Bool :=
    fun s => Sum.elim (fun _ => false) (fun q => q.1.isSpin) s.2
  have hb : ∀ s, (κc s).1.isSpin = bf s := by
    rintro ⟨C, y | q⟩
    · show (κc ⟨C, Sum.inl y⟩).1.isSpin = false
      rw [hκ1 C y]
      exact isSpin_oldVar (by omega) C.1.1 C.2.2 y
    · show (κc ⟨C, Sum.inr q⟩).1.isSpin = q.1.isSpin
      rw [hκ2 C q]
      rfl
  have hE := fun s => exists_varVal_equiv (N := N) _ _ (hb s)
  choose e he hev using hE
  obtain ⟨Lx, hLx, μLx, hμLx, Ψx, hΨx, cx1, cx2⟩ := exists_coreRegroup
    (α := fun p : ↥(locOp geo cs SD KD hH lab m hmK Z).A => VarVal N p.1.isSpin)
    (fun p => varMeasure N p.1.isSpin) κc hinj (β := fun s => VarVal N (bf s))
    (fun s => varMeasure N (bf s)) e he T hT'
  obtain ⟨sh, hsh, csh⟩ := exists_shuffle7_equiv
    (outPartMeasure N (Vblk R (H.localHistory M K m Z) m) (· ∈ Z0)) (outPartMeasure N V2 P2) μL
    (Measure.pi fun j : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)) =>
      (Measure.pi fun a : OutIdx (K := K) (M := M) R j.2.1 =>
        varMeasure N (bf ⟨j, Sum.inl a⟩)).prod
      (Measure.pi fun b : ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) j.2.1).A =>
        varMeasure N (bf ⟨j, Sum.inr b⟩)))
    (Measure.pi fun t : ↥T => varMeasure N t.1.1.isSpin) μLx
    (outPartMeasure N (Vblk R (H.localHistory M K m Z) m) (· ∈ Z0))
  have hΘ : ∀ ω, ((MeasurableEquiv.prodCongr Ψo (MeasurableEquiv.prodCongr Ψx
      (MeasurableEquiv.refl (OutZero N R (H.localHistory M K m Z) m Z0)))).trans sh) ω =
      ((( Ψo ω.1).1, ((Ψo ω.1).2.1, (Ψx ω.2.1).2.1)), ((Ψx ω.2.1).1, ((Ψo ω.1).2.2,
        ((Ψx ω.2.1).2.2, ω.2.2)))) := fun ω => csh _
  refine ⟨κc, L × (Lx × OutZero N R (H.localHistory M K m Z) m Z0), inferInstance,
    μL.prod (μLx.prod (outPartMeasure N (Vblk R (H.localHistory M K m Z) m) (· ∈ Z0))),
    inferInstance, (MeasurableEquiv.prodCongr Ψo (MeasurableEquiv.prodCongr Ψx
      (MeasurableEquiv.refl _))).trans sh, hinj, hκ1, hκ2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hsh.comp (hΨo.prod (hΨx.prod (MeasurePreserving.id _)))
  · intro ω y
    exact (congrArg (fun p => p.1.1 y) (hΘ ω)).trans (co1 ω.1 y)
  · intro ω y
    exact (congrArg (fun p => p.1.2.1 y) (hΘ ω)).trans (co2 ω.1 y)
  · intro ω t
    exact (congrArg (fun p => p.1.2.2 t) (hΘ ω)).trans (cx2 ω.2.1 t)
  · intro ω C y
    refine (congrArg (fun p => p.2.1 C |>.1 y) (hΘ ω)).trans ?_
    show (((Ψx ω.2.1).1 C).1 y) = _
    rw [cx1]
    exact hev ⟨C, Sum.inl y⟩ _
  · intro ω C q
    refine (congrArg (fun p => VarVal.toEuc (p.2.1 C |>.2 q)) (hΘ ω)).trans ?_
    show VarVal.toEuc (((Ψx ω.2.1).1 C).2 q) = _
    rw [cx1]
    exact hev ⟨C, Sum.inr q⟩ _

end Main

end Balaban.LargeField
