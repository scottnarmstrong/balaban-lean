/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainRegroupVar

/-!
# The regrouping of the window integral with the shell variables exposed: the internal variables (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstruction (1).  As `exists_var_nodes` (W923), but the
coordinates of `x` outside the core, `T` and the Gaussian nodes `Nd` are not hidden: they are the explicit
shell variables `Sh`, so that the shell indicators of the new′ variables can be integrated.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban RegionHistory

section Var

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The internal variables regrouped with the node and the shell coordinates exposed.**  The variables `x`
of the operator of `Z` (a quiet window `[k₁, m)`) are regrouped, measure preservingly, into the core
variables (the coordinates `κc`), the coordinates in `T`, those in `Nd` (variables of scales above `k₁`)
and the shell coordinates `Sh`: all the others. -/
theorem exists_var_shell {k1 m : ℕ} (h : k1 < m) (hmK : m ≤ K) {Z : H.Comp m}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s m Y Z → ¬ IsKept H s Y)
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
    (hNj : ∀ p ∈ Nd, k1 < ((p.1.1.1 : Fin m) : ℕ)) (hNT : ∀ p ∈ Nd, p ∉ T) :
    ∃ (κc : (Σ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
        OutIdx (K := K) (M := M) R C.2.1 ⊕
          ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A) →
        ↥(locOp geo cs SD KD hH lab m hmK Z).A)
      (Ψ : SubCfg N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A ≃ᵐ
        (∀ C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)),
          OutZ N R (H.localHistory M K k1 C.2.1) k1 ×
            SubCfg N (H.localHistory M K k1 C.2.1) k1
              (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A) ×
        ((∀ t : ↥T, VarVal N t.1.1.isSpin) × ((∀ t : ↥Nd, VarVal N t.1.1.isSpin) ×
          (∀ t : {p : ↥(locOp geo cs SD KD hH lab m hmK Z).A //
            p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}, VarVal N t.1.1.isSpin)))),
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
      MeasurePreserving Ψ
        (subMeasure N (H.localHistory M K m Z) m (locOp geo cs SD KD hH lab m hmK Z).A)
        ((Measure.pi fun C : (Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1)) =>
            (outPartMeasure N (Vblk R (H.localHistory M K k1 C.2.1) k1)
              (ZBlk (H.localHistory M K k1 C.2.1) k1)).prod
            (subMeasure N (H.localHistory M K k1 C.2.1) k1
              (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A)).prod
          ((Measure.pi fun t : ↥T => varMeasure N t.1.1.isSpin).prod
            ((Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin).prod
              (Measure.pi fun t : {p : ↥(locOp geo cs SD KD hH lab m hmK Z).A //
                p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => varMeasure N t.1.1.isSpin)))) ∧
      (∀ x (t : ↥T), (Ψ x).2.1 t = x t.1) ∧
      (∀ x (t : ↥Nd), (Ψ x).2.2.1 t = x t.1) ∧
      (∀ x (t : {p : ↥(locOp geo cs SD KD hH lab m hmK Z).A //
          p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd}), (Ψ x).2.2.2 t = x t.1) ∧
      (∀ x (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
        (y : OutIdx (K := K) (M := M) R C.2.1),
        ((Ψ x).1 C).1 y = VarVal.toEuc (x (κc ⟨C, Sum.inl y⟩))) ∧
      (∀ x (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
        (q : ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A),
        VarVal.toEuc (((Ψ x).1 C).2 q) = VarVal.toEuc (x (κc ⟨C, Sum.inr q⟩))) := by
  obtain ⟨κc, hinj, hκ1, hκ2⟩ := exists_coreCoord geo cs SD KD h hmK hq
  have hT' : ∀ s, ¬ (κc s ∈ T) := by
    rintro ⟨C, y | q⟩ hmem
    · refine hTo C y ((hκ1 C y) ▸ (κc ⟨C, Sum.inl y⟩).2) ?_
      convert hmem using 1
      exact (Subtype.ext (hκ1 C y)).symm
    · refine hTi C q ((hκ2 C q) ▸ (κc ⟨C, Sum.inr q⟩).2) ?_
      convert hmem using 1
      exact (Subtype.ext (hκ2 C q)).symm
  have hN' : ∀ s, ¬ (κc s ∈ Nd) := by
    rintro ⟨C, y | q⟩ hmem
    · have h1 := hNj _ hmem
      have h2 : ((κc ⟨C, Sum.inl y⟩).1.1.1 : Fin m).val = k1 := by
        rw [hκ1 C y]
        exact oldVar_val (by omega) C.1.1 C.2.2 y
      omega
    · have h1 := hNj _ hmem
      have h2 : ((κc ⟨C, Sum.inr q⟩).1.1.1 : Fin m).val < k1 := by
        rw [hκ2 C q]
        exact q.1.1.1.2
      omega
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
  obtain ⟨Q1, hQ1⟩ : ∃ Q1 : ↥(locOp geo cs SD KD hH lab m hmK Z).A → Prop,
      ∀ p, Q1 p ↔ p ∈ Set.range κc := ⟨_, fun _ => Iff.rfl⟩
  obtain ⟨Ψ, hΨ, cx1, cx2, cx3, cx4⟩ := exists_core_split_two
    (α := fun p : ↥(locOp geo cs SD KD hH lab m hmK Z).A => VarVal N p.1.isSpin)
    (fun p => varMeasure N p.1.isSpin) κc hinj (β := fun s => VarVal N (bf s))
    (fun s => varMeasure N (bf s)) e he Q1 (fun p => p ∈ T) (fun p => p ∈ Nd) hQ1
    hT' hN' (fun p hp hT => hNT p hp hT) (Equiv.refl ↥T) (Equiv.refl ↥Nd)
  let e5 : {p : ↥(locOp geo cs SD KD hH lab m hmK Z).A //
      p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} ≃
      {t : {t : {i : ↥(locOp geo cs SD KD hH lab m hmK Z).A // ¬ Q1 i} // ¬ (fun p => p ∈ T) t.1} //
        ¬ (fun p => p ∈ Nd) t.1.1} :=
    { toFun := fun p => ⟨⟨⟨p.1, fun hh => p.2.1 ((hQ1 p.1).mp hh)⟩, p.2.2.1⟩, p.2.2.2⟩
      invFun := fun t => ⟨t.1.1.1, fun hh => t.1.1.2 ((hQ1 t.1.1.1).mpr hh), t.1.2, t.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  obtain ⟨Ψ5, h5, d5⟩ := exists_reindex_equiv e5
    (β := fun t : {p : ↥(locOp geo cs SD KD hH lab m hmK Z).A //
      p ∉ Set.range κc ∧ p ∉ T ∧ p ∉ Nd} => VarVal N t.1.1.isSpin)
    (γ := fun t : {t : {t : {i : ↥(locOp geo cs SD KD hH lab m hmK Z).A // ¬ Q1 i} //
      ¬ (fun p => p ∈ T) t.1} // ¬ (fun p => p ∈ Nd) t.1.1} => VarVal N t.1.1.1.1.isSpin)
    (fun t => varMeasure N t.1.1.1.1.isSpin) (fun t => varMeasure N t.1.1.isSpin)
    (fun _ => MeasurableEquiv.refl _) (fun _ => MeasurePreserving.id _)
  have hc1 : ∀ x (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
      (y : OutIdx (K := K) (M := M) R C.2.1),
      ((Ψ x).1 C).1 y = e ⟨C, Sum.inl y⟩ (x (κc ⟨C, Sum.inl y⟩)) :=
    fun x C y => congrFun (congrArg Prod.fst (cx1 x C)) y
  have hc2 : ∀ x (C : Σ P : ↥(H.ancFin (k1 + 1) m Z), ↥(H.parts k1 P.1))
      (q : ↥(locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A),
      ((Ψ x).1 C).2 q = e ⟨C, Sum.inr q⟩ (x (κc ⟨C, Sum.inr q⟩)) :=
    fun x C q => congrFun (congrArg Prod.snd (cx1 x C)) q
  refine ⟨κc, Ψ.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl _) Ψ5))), hinj, hκ1, hκ2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h7 := (MeasurePreserving.id (Measure.pi fun C : (Σ P : ↥(H.ancFin (k1 + 1) m Z),
        ↥(H.parts k1 P.1)) => (outPartMeasure N (Vblk R (H.localHistory M K k1 C.2.1) k1)
          (ZBlk (H.localHistory M K k1 C.2.1) k1)).prod
        (subMeasure N (H.localHistory M K k1 C.2.1) k1
          (locOp geo cs SD KD hH lab k1 (h.le.trans hmK) C.2.1).A))).prod
      ((MeasurePreserving.id (Measure.pi fun t : ↥T => varMeasure N t.1.1.isSpin)).prod
        ((MeasurePreserving.id (Measure.pi fun t : ↥Nd => varMeasure N t.1.1.isSpin)).prod h5))
    have h8 := h7.comp (f := Ψ) (by convert hΨ using 3; rfl)
    exact h8
  · exact cx2
  · exact cx3
  · intro x t
    exact (d5 _ t).trans (cx4 x _)
  · intro x C y
    exact (hc1 x C y).trans (hev ⟨C, Sum.inl y⟩ _)
  · intro x C q
    exact (congrArg VarVal.toEuc (hc2 x C q)).trans (hev ⟨C, Sum.inr q⟩ _)

end Var

end Balaban.LargeField
