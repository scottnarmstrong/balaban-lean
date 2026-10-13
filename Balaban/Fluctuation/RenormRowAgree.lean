/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormC1Local

/-!
# Agreement of the row data of the shifted perturbation of the renormalization cut family

Toward the localization principles `locC2` and `locDφ` of `RenormExpInput`.  **`locC2` and `locDφ`
are NOT proved here**; this file proves the agreement bridge `DataAgreeRows` that the landed
locality theorem `i4a_local_rows` asks for.  It uses no zero class and is independent of the choice
of the generating set beyond the hypotheses stated.

**Diagonal shift (`rowSite_shift_iff`).**  The matrix `H_D(α)` depends on the potential `α` only
through its diagonal, and a diagonal entry `(x, x)` with `x ∈ B` is already counted in `RowSite`
by the first clause.  Hence `RowSite G a ν α B = RowSite G a ν α' B` for any two potentials, in
particular for `α' = α + c`.

**The bridge (`renDec_row_agree`).**  For the data `E_ren(D, ξ, s)` of mode P,
`(φ̄_s, α_s + Δν, ζ Ψ, Δν (h - φ_s))` with `Δν = renMassU ν ξ - ν`, `ζ = renZeta εζ ξ`, two data with
equal `ξ` and equal `(Ψ, h)` on the component `compY C` give `DataAgreeRows` on `S_Y`.  As in
`RenormC1Local`, agreement on the component alone suffices (`i4b_local_of_agree_on_component`).  At
the full level `Ω₁` is the whole torus, so the collar is empty and the collar clause is vacuous.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis LocalCover Finset Matrix

section Diagonal

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **Row sites do not depend on the potential.**  The off-diagonal entries of `H_D(α)` do not
involve `α`, and the diagonal entries at `x ∈ B` are covered by the clause `y ∈ B`. -/
theorem rowSite_iff_of_potentials {α α' : G.Ω 1 → ℂ} {B : Finset (CTorus d L N₁ m₁ K)}
    {y : G.Ω 1} : RowSite G a ν α B y ↔ RowSite G a ν α' B y := by
  have key : ∀ {β β' : G.Ω 1 → ℂ}, RowSite G a ν β B y → RowSite G a ν β' B y := by
    intro β β' h
    rcases h with h | ⟨x, hx, hne⟩
    · exact Or.inl h
    · by_cases hxy : x = y
      · subst hxy; exact Or.inl hx
      · refine Or.inr ⟨x, hx, ?_⟩
        intro h0
        apply hne
        unfold dirichletOperator at h0 ⊢
        rw [Matrix.add_apply, Matrix.diagonal_apply_ne _ hxy] at h0 ⊢
        simpa using h0
  exact ⟨key, key⟩

/-- **A diagonal shift of the potential does not change the row sites** (equality, not only an
inclusion `RowSite α' B ⊆ RowSite α B ∪ B`). -/
theorem rowSite_shift_iff (α c : G.Ω 1 → ℂ) (B : Finset (CTorus d L N₁ m₁ K)) (y : G.Ω 1) :
    RowSite G a ν (fun x => α x + c x) B y ↔ RowSite G a ν α B y :=
  rowSite_iff_of_potentials

/-- The shift of the zero potential by a constant `c` (the case `α_s + Δν` over `α = 0`). -/
theorem rowSite_const_iff (α : G.Ω 1 → ℂ) (c : ℂ) (B : Finset (CTorus d L N₁ m₁ K))
    (y : G.Ω 1) :
    RowSite G a ν (fun x => α x + c) B y ↔ RowSite G a ν (0 : G.Ω 1 → ℂ) B y :=
  rowSite_iff_of_potentials

end Diagonal

section Bridge

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **`renDec_row_agree`** (the agreement bridge).  Let `(D, ξ)`, `(D', ξ)` be data of
`XiCOneReal`, with `(Ψ, h)` equal on the component `Y = compY C` (`RenC1Ag`), and let the cut
parameters `s, s'` be equal on the cubes whose patch lies in `Y`, supported in `C`, and of norm
`< e^κ`.  Put `φ_s`, `α_s` for the decoupled background field and multiplier at the cut parameters
`extParams (s ∘ renLabelEquiv.symm)`.  Then the tuples of mode P,
`(φ̄_s, α_s + Δν, ζ Ψ, Δν (h - φ_s))` with `Δν = renMassU ν ξ - ν` and `ζ = renZeta εζ ξ`,
satisfy `DataAgreeRows` on `S_Y`. -/
theorem renDec_row_agree {n : ℕ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    (hG : IsLevel Gp n) {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ K)}
    {X₁f : Finset (CTorus d L N₁ m₁ K)} (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X₁)
    (hPS : PolySetup Gp m₀ X₁) (εζ : ℝ)
    {S : Set (BgData Gp N × (Fin 3 → ℂ))}
    (hS : ∀ u ∈ S, XiCOneReal Gp (compWeight L a₁) ν eps u.1)
    (C : Finset (RenLabel Gp X₁)) {u u' : BgData Gp N × (Fin 3 → ℂ)} (hu : u ∈ S) (hu' : u' ∈ S)
    {s s' : RenLabel Gp X₁ → ℂ} (hs : s ∈ supN C (Real.exp κ)) (hs' : s' ∈ supN C (Real.exp κ))
    (hag : ∀ i ∈ C, Pset m₁ (renCube Gp X₁ i) ⊆ compY (renCube Gp X₁) X₁ C → s i = s' i)
    (hAg : RenC1Ag (renCube Gp X₁) X₁ C u u') :
    DataAgreeRows Gp (compWeight L a₁) ν N
      (SY Gp X₁f (C.image (renCube Gp X₁)) (finOf (compY (renCube Gp X₁) X₁ C)))
      (fun x => decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ)
        (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm)) u.1 x + (renMassU ν u.2 - (ν : ℂ)))
      (fun x => decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ)
        (extParams Gp X₁ (s' ∘ (renLabelEquiv Gp X₁).symm)) u'.1 x + (renMassU ν u'.2 - (ν : ℂ)))
      (barField Gp u.1.Ψ (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ)
        (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm)) u.1))
      (barField Gp u'.1.Ψ (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ)
        (extParams Gp X₁ (s' ∘ (renLabelEquiv Gp X₁).symm)) u'.1))
      (fun x => renZeta εζ u.2 • u.1.Ψ x) (fun x => renZeta εζ u'.2 • u'.1.Ψ x)
      (fun p => (renMassU ν u.2 - (ν : ℂ)) * (u.1.h p.1 p.2 -
        decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ)
          (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm)) u.1 p))
      (fun p => (renMassU ν u'.2 - (ν : ℂ)) * (u'.1.h p.1 p.2 -
        decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ)
          (extParams Gp X₁ (s' ∘ (renLabelEquiv Gp X₁).symm)) u'.1 p)) := by
  classical
  subst hX₁
  obtain ⟨hξ, hdat⟩ := hAg
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hΩ : ∀ x : CTorus d L N₁ m₁ K, x ∈ Gp.Ω 1 := fun x => by
    rw [hG.Ω_one]; exact Finset.mem_univ x
  set cc := renCube Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) with hcc
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))
      (s ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm) P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs.2 _)
  have hsx' : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))
      (s' ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm) P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs'.2 _)
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
  have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
    (bgC1_le_bgC0 d L N hd0))
  have hνε : ν * ((L : ℝ) ^ K) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  have hDom := xiCData_inDomainC hC.HBp hC.small1 (hS u hu).xiCOne
  have hDom' := xiCData_inDomainC hC.HBp hC.small1 (hS u' hu').xiCOne
  obtain ⟨φ, α, hI, huniq, -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hsx P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom
  obtain ⟨φ', α', hI', huniq', -⟩ := i4b_exists_unique hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
    (fun P => (hsx' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom'
  obtain ⟨e1φ, e1α⟩ := decBg_eq hI huniq
  obtain ⟨e2φ, e2α⟩ := decBg_eq hI' huniq'
  rw [e1φ, e1α, e2φ, e2α, ← hξ]
  set Yc : Set (CTorus d L N₁ m₁ K) := compY cc (↑X₁f : Set (CTorus d L N₁ m₁ K)) C with hYc
  set Y : Finset (CTorus d L N₁ m₁ K) := finOf Yc with hY
  set 𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K) := C.image cc with h𝒞
  have hmemY : ∀ x, x ∈ Y ↔ x ∈ Yc := fun x => mem_finOf_set
  have hYsub : Yc ⊆ patchUnion (↑X₁f : Set (CTorus d L N₁ m₁ K)) (fun i => Pset m₁ (cc i)) C :=
    componentOf_subset _ (fun _ h => Or.inl h)
  have hYnn : IsNnComp ((Vset X₁f 𝒞).filter fun x => x ∈ Gp.Ω 1) Y := by
    refine ⟨fun x hx => ?_, fun x hx y hy hadj => ?_⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter]
      exact ⟨(mem_Vset_iff cc C).2 (hYsub hxY), hΩ x⟩
    · have hxY : x ∈ Yc := (hmemY x).1 hx
      rw [Finset.mem_filter] at hy
      exact (hmemY y).2 (compY_closed hxY ((mem_Vset_iff cc C).1 hy.1) hadj)
  have hs1E : ∀ P ∈ cubeIdx Gp, P ∉ parCubes Gp X₁f →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))
        (s ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P = 1 ∧
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))
        (s' ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P = 1 :=
    fun P hP hPn => ⟨renExt_one_of_not_mem_parCubes _ hP hPn, renExt_one_of_not_mem_parCubes _ hP hPn⟩
  have hs0E : ∀ P ∈ parCubes Gp X₁f, P ∉ 𝒞 →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))
        (s ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P = 0 ∧
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))
        (s' ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P = 0 :=
    fun P hP hP𝒞 => ⟨renExt_extS_zero hPS s C (fun i hi => hs.1 i hi) hP hP𝒞,
      renExt_extS_zero hPS s' C (fun i hi => hs'.1 i hi) hP hP𝒞⟩
  have hagE : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))
        (s ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P =
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))
        (s' ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P := by
    intro P hP𝒞 hSub
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    have hsub : Pset m₁ (cc i) ⊆ Yc := fun x hx =>
      (hmemY x).1 (hSub ⟨x, hΩ x⟩ (mem_cubeP.2 hx))
    rw [hcc, renExt_extS_label (↑X₁f : Set (CTorus d L N₁ m₁ K)) s i,
      renExt_extS_label (↑X₁f : Set (CTorus d L N₁ m₁ K)) s' i]
    exact hag i hi hsub
  have hdata : ∀ z ∈ Y, u.1.Ψ z = u'.1.Ψ z ∧ (z ∈ Gp.Ω 1 → u.1.h z = u'.1.h z) :=
    fun z hz => ⟨(hdat z ((hmemY z).1 hz)).1, fun _ => (hdat z ((hmemY z).1 hz)).2⟩
  obtain ⟨hαeq, -, -, hphi⟩ := i4b_local_of_agree_on_component hC.hS hC.Sp hconn hC.HBp
    hC.hκ.le hC.hM (fun P => (hsx P).le) (fun P => (hsx' P).le) hδ0 le_rfl hδ0' hδ1 hνε hDom
    hDom' hG hYnn hs1E hs0E hagE hdata hI hI'
  have hSYY : ∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY Gp X₁f 𝒞 Y →
      (x : CTorus d L N₁ m₁ K) ∈ Yc := fun x hx => (hmemY _).1 (SY_subset hx)
  refine ⟨fun x hx => ?_, fun y hy => ?_, fun x hx => ?_, fun y hy _ => ?_, fun x hx i => ?_⟩
  · simp only [hαeq x hx]
  · have hy0 : RowSite Gp (compWeight L a₁) ν (0 : Gp.Ω 1 → ℂ) (SY Gp X₁f 𝒞 Y) y :=
      rowSite_iff_of_potentials.1 hy
    funext i
    simp only [barField, y.2, ↓reduceDIte]
    exact hphi y hy0 i
  · funext i
    simp only [Pi.smul_apply]
    rw [(hdat x (hSYY x hx)).1]
  · exact absurd (hΩ y) ((mem_collar Gp).1 (by assumption)).1
  · simp only
    rw [(hdat x (hSYY x hx)).2, hphi x (Or.inl hx) i]

end Bridge

section Instance

/-- **Non-vacuity at the landed pair of levels** (`d = L = 3`, `N₁ = 9`, `K = 2`).  The hypotheses
of `renDec_row_agree` hold jointly (`FlCore`, `HatConn`, `IsLevel`, `PolySetup`), the set of data
of `XiCOneReal` is nonempty, and for every pair of data of `XiCOneReal` with equal `ξ` the tuples
satisfy `DataAgreeRows` on `S_Y`.  There `X₁` is the whole torus, so the label type is empty and
the only cut family is `C = ∅`; the statement is the instance of the labelled case at its
degenerate end, not a case with a nonempty set of labels. -/
theorem renDec_row_agree_levelPair (N : ℕ) (hN : 0 < N) :
    ∃ (m₁ : ℕ) (ϱ BG κ eps : ℝ),
      (∃ D : BgData (LevelPair.Gp m₁ ϱ) N,
        XiCOneReal (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 eps D) ∧
      ∀ (εζ : ℝ) (u u' : BgData (LevelPair.Gp m₁ ϱ) N × (Fin 3 → ℂ)),
        XiCOneReal (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 eps u.1 →
        XiCOneReal (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 eps u'.1 →
        ∀ (s s' : RenLabel (LevelPair.Gp m₁ ϱ)
            (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) → ℂ)
          (C : Finset (RenLabel (LevelPair.Gp m₁ ϱ)
            (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)))),
        s ∈ supN C (Real.exp κ) → s' ∈ supN C (Real.exp κ) →
        (∀ i ∈ C, Pset m₁ (renCube (LevelPair.Gp m₁ ϱ)
            (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) i) ⊆
          compY (renCube (LevelPair.Gp m₁ ϱ)
            (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)))
            (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) C →
          s i = s' i) →
        RenC1Ag (renCube (LevelPair.Gp m₁ ϱ)
            (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)))
          (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) C u u' →
        DataAgreeRows (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 N
          (SY (LevelPair.Gp m₁ ϱ) (Finset.univ : Finset (CTorus 3 3 9 m₁ 2))
            (C.image (renCube (LevelPair.Gp m₁ ϱ)
              (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))))
            (finOf (compY (renCube (LevelPair.Gp m₁ ϱ)
              (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)))
              (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) C)))
          (fun x => decBgMult (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 (rho4 3 3 N BG κ)
            (extParams (LevelPair.Gp m₁ ϱ)
              (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))
              (s ∘ (renLabelEquiv (LevelPair.Gp m₁ ϱ)
                (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) :
                  Set (CTorus 3 3 9 m₁ 2))).symm)) u.1 x + (renMassU 0 u.2 - ((0 : ℝ) : ℂ)))
          (fun x => decBgMult (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 (rho4 3 3 N BG κ)
            (extParams (LevelPair.Gp m₁ ϱ)
              (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))
              (s' ∘ (renLabelEquiv (LevelPair.Gp m₁ ϱ)
                (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) :
                  Set (CTorus 3 3 9 m₁ 2))).symm)) u'.1 x + (renMassU 0 u'.2 - ((0 : ℝ) : ℂ)))
          (barField (LevelPair.Gp m₁ ϱ) u.1.Ψ
            (decBgField (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 (rho4 3 3 N BG κ)
              (extParams (LevelPair.Gp m₁ ϱ)
                (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))
                (s ∘ (renLabelEquiv (LevelPair.Gp m₁ ϱ)
                  (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) :
                    Set (CTorus 3 3 9 m₁ 2))).symm)) u.1))
          (barField (LevelPair.Gp m₁ ϱ) u'.1.Ψ
            (decBgField (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 (rho4 3 3 N BG κ)
              (extParams (LevelPair.Gp m₁ ϱ)
                (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))
                (s' ∘ (renLabelEquiv (LevelPair.Gp m₁ ϱ)
                  (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) :
                    Set (CTorus 3 3 9 m₁ 2))).symm)) u'.1))
          (fun x => renZeta εζ u.2 • u.1.Ψ x) (fun x => renZeta εζ u'.2 • u'.1.Ψ x)
          (fun p => (renMassU 0 u.2 - ((0 : ℝ) : ℂ)) * (u.1.h p.1 p.2 -
            decBgField (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 (rho4 3 3 N BG κ)
              (extParams (LevelPair.Gp m₁ ϱ)
                (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))
                (s ∘ (renLabelEquiv (LevelPair.Gp m₁ ϱ)
                  (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) :
                    Set (CTorus 3 3 9 m₁ 2))).symm)) u.1 p))
          (fun p => (renMassU 0 u'.2 - ((0 : ℝ) : ℂ)) * (u'.1.h p.1 p.2 -
            decBgField (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 (rho4 3 3 N BG κ)
              (extParams (LevelPair.Gp m₁ ϱ)
                (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2))
                (s' ∘ (renLabelEquiv (LevelPair.Gp m₁ ϱ)
                  (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) :
                    Set (CTorus 3 3 9 m₁ 2))).symm)) u'.1 p)) := by
  obtain ⟨m₁, ϱ, c, BG, κ, eps, c₂, BG₂, δ₁, κdec, κ₀, hC, -, hGp, hH, hconn, -, hcov, hX1, -, -,
    -, -, -, -, -, -, hmar, -⟩ := LevelPair.interaction_levelPair_witness N
  have hPS : PolySetup (LevelPair.Gp m₁ ϱ) 1
      (↑(Finset.univ : Finset (CTorus 3 3 9 m₁ 2)) : Set (CTorus 3 3 9 m₁ 2)) := by
    rw [hX1]; exact hcov.polySetup
  have hε : 0 < eps := hC.eps_pos
  obtain ⟨D, hD⟩ := Balaban.Inhabited.exists_xiCOneReal hH (LevelPair.Gp m₁ ϱ) hN
    (by simp) hε
  refine ⟨m₁, ϱ, BG, κ, eps, ⟨D, hD⟩, fun εζ u u' hu hu' s s' C hs hs' hag hAg => ?_⟩
  exact renDec_row_agree hC hconn hGp rfl hPS εζ
    (S := {v | XiCOneReal (LevelPair.Gp m₁ ϱ) (compWeight 3 1) 0 eps v.1})
    (fun v hv => hv) C (u := u) (u' := u') hu hu' hs hs' hag hAg

end Instance

end Balaban.Localization
