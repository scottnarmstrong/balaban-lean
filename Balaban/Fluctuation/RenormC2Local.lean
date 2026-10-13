/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.RenormRowAgree
public import Balaban.Fluctuation.RenormDecAnalytic
public import Balaban.Fluctuation.RenormStrictData
public import Balaban.Fluctuation.RenormLocFibre
public import Balaban.Fluctuation.RenormExpBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Locality of the cut functionals of the shifted perturbation: `C₂` and `δφ`

Toward the localization principles `locC2` and `locDφ` of `RenormExpInput`.  **`locC2` and `locDφ`
themselves are NOT proved here**, and neither is the endpoint `s = 1` (the identification of the
family `F` with the cut solution at the all-ones parameter) nor any class bound.  This file proves
the locality inputs of the two cut functionals only.  It uses no zero class and is independent of
the choice of the generating set beyond the hypotheses stated.

**Solutions agree (`renDec_solution_local`).**  Let `F` be a family of solutions of the shifted
perturbation problem, i.e. for each datum and cut parameter `s` the pair `(δφ, δα) = F (rawOf D, ξ) s`
satisfies `δφ = dphi …`, `DecFixed … false …`, `Small … (c6′ …)` for the data `renEdat` of mode P
at the cut parameters `extParams (s ∘ renLabelEquiv.symm)` (this is the first three clauses of the
output of `renDec_sharp`).  For two data with `RenC1Ag` on the component `Y = compY C`, cut
parameters supported in `C` and equal on the cubes whose patch lies in `Y`, the solutions agree:
`δα = δα'` on `S_Y` and `δφ = δφ'` on `Y`.  This is `i4a_local_rows`, with the `DecHyp` pair from
`renEdat_decHyp_of_flCore`, the data agreement from `renDec_row_agree`, and the margins of
`renDec_sharp`.

**Read sets.**  `renC2Site` at `x` reads `ξ 2`, the diagonal entry of the potential at `x`, and
`δφ` at the sites `y` with `H_D(α_u + ν_u) x y ≠ 0`, that is on `RowSite` of the block; the
row sites do not depend on the potential or on the mass (`rowSite_iff_of_mass_potential`), so
`renC2On_congr` asks for agreement of the potential on the block and of `δφ` on `RowSite`.  The
block lies in `S_Y` by the block margin (`blockSites_subset_SY_of_blockMargin`), and the row sites
of `S_Y` lie in `Y` (`rowSite_subset`).  The functional `δφ(p)` reads only the point `p`, which
lies in `X₁ ⊆ Y`.

**The two laws.**  `renC2_local_cut_of`, `renC2_local_cut` and `renDphi_local_cut_of`,
`renDphi_local_cut` are `LocalityAEOn (e^κ)` statements for the agreement `RenC1Ag`, in the form
`renLoc_localization_expansion_fin` takes as `hloc`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Analysis LocalCover Finset Matrix

section Rows

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ}

/-- Off-diagonal entries of the Dirichlet operator depend neither on the mass nor on the
potential. -/
theorem dirichletOperator_apply_ne {ν ν' : ℝ} {α α' : G.Ω 1 → ℂ} {x y : G.Ω 1} (hxy : x ≠ y) :
    dirichletOperator G a ν α x y = dirichletOperator G a ν' α' x y := by
  have hne : (x : CTorus d L N₁ m₁ K) ≠ y := fun h => hxy (Subtype.ext h)
  unfold dirichletOperator
  rw [Matrix.add_apply, Matrix.add_apply, Matrix.diagonal_apply_ne _ hxy,
    Matrix.diagonal_apply_ne _ hxy]
  simp [Green.restrictOp, fullMatrix, latticeLaplacian, Matrix.sub_apply, Matrix.add_apply,
    Matrix.one_apply_ne hne]

/-- **Row sites depend neither on the mass nor on the potential.** -/
theorem rowSite_iff_of_mass_potential {ν ν' : ℝ} {α α' : G.Ω 1 → ℂ}
    {B : Finset (CTorus d L N₁ m₁ K)} {y : G.Ω 1} :
    RowSite G a ν α B y ↔ RowSite G a ν' α' B y := by
  have key : ∀ {ν ν' : ℝ} {α α' : G.Ω 1 → ℂ}, RowSite G a ν α B y → RowSite G a ν' α' B y := by
    intro ν ν' α α' h
    rcases h with h | ⟨x, hx, hne⟩
    · exact Or.inl h
    · by_cases hxy : x = y
      · subst hxy; exact Or.inl hx
      · exact Or.inr ⟨x, hx, fun h0 => hne
          ((dirichletOperator_apply_ne (ν := ν) (ν' := ν') (α := α) (α' := α') hxy).trans h0)⟩
  exact ⟨key, key⟩

/-- The row sites of a smaller set are row sites of a larger one. -/
theorem rowSite_mono {ν : ℝ} {α : G.Ω 1 → ℂ} {B B' : Finset (CTorus d L N₁ m₁ K)} (hB : B ⊆ B')
    {y : G.Ω 1} (h : RowSite G a ν α B y) : RowSite G a ν α B' y := by
  rcases h with h | ⟨x, hx, hne⟩
  · exact Or.inl (hB h)
  · exact Or.inr ⟨x, hB hx, hne⟩

/-- **Congruence of `renC2On`** (the read set).  Two inputs with the same `ξ` and mass, potentials
agreeing on the sites of `B ∩ Ω₁`, and `δφ` agreeing on `RowSite` of `B` give the same value. -/
theorem renC2On_congr {B : Finset (CTorus d L N₁ m₁ K)} {ξ : Fin 3 → ℂ} {νu : ℂ}
    {αu αu' : G.Ω 1 → ℂ} {δφ δφ' : G.Ω 1 × Fin N → ℂ}
    (hα : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ B → αu x = αu' x)
    (hφ : ∀ y : G.Ω 1, RowSite G a 0 αu B y → ∀ i, δφ (y, i) = δφ' (y, i)) :
    renC2On G a B ξ νu αu δφ = renC2On G a B ξ νu αu' δφ' := by
  classical
  unfold renC2On
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxB : (x : CTorus d L N₁ m₁ K) ∈ B := (Finset.mem_filter.1 hx).2
  unfold renC2Site
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∀ (β : G.Ω 1 → ℂ) (δ : G.Ω 1 × Fin N → ℂ),
      (liftOp N (dirichletOperator G a 0 (β + fun _ => νu)) *ᵥ δ) (x, i) =
        ∑ y, dirichletOperator G a 0 (β + fun _ => νu) x y * δ (y, i) := by
    intro β δ; rw [liftOp_mulVec]; rfl
  rw [e, e]
  have hx0 : δφ (x, i) = δφ' (x, i) := hφ x (Or.inl hxB) i
  rw [hx0]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : RowSite G a 0 αu B y
  · have hM : dirichletOperator G a 0 (αu + fun _ => νu) x y =
        dirichletOperator G a 0 (αu' + fun _ => νu) x y := by
      by_cases hxy : x = y
      · subst hxy
        unfold dirichletOperator
        rw [Matrix.add_apply, Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
          Pi.add_apply, Pi.add_apply, hα x hxB]
      · exact dirichletOperator_apply_ne hxy
    rw [hM, hφ y hy i]
  · have h0 : dirichletOperator G a 0 (αu + fun _ => νu) x y = 0 := by
      by_contra hne
      exact hy (rowSite_iff_of_mass_potential.1 (Or.inr ⟨x, hxB, hne⟩))
    have h0' : dirichletOperator G a 0 (αu' + fun _ => νu) x y = 0 := by
      by_cases hxy : x = y
      · exact absurd (hxy ▸ hxB) (fun h => hy (Or.inl h))
      · rw [← dirichletOperator_apply_ne (ν := 0) (α := αu + fun _ => νu) hxy]; exact h0
    rw [h0, h0']
    simp

end Rows

section Geometry

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- **Blocks with the block margin lie in `S_Y`** (the root block is contained in `S_Y`): every
site of `B ∩ Ω₁` has a cube of the cover whose interior box contains it, whose hat box lies in
`X₁ ⊆ Y` and which meets no parameter cube; this cube belongs to `Z_Y`, for every cut family. -/
theorem blockSites_subset_SY_of_blockMargin {X₁f : Finset (CTorus d L N₁ m₁ K)}
    {B : Finset (CTorus d L N₁ m₁ K)} (hmar : BlockMargin Gp X₁f (↑B : Set (CTorus d L N₁ m₁ K)))
    (hΩ : ∀ x : CTorus d L N₁ m₁ K, x ∈ Gp.Ω 1) (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K))
    (Y : Finset (CTorus d L N₁ m₁ K)) (hXY : ∀ y ∈ X₁f, y ∈ Y) :
    ∀ x ∈ B, x ∈ SY Gp X₁f 𝒞 Y := by
  classical
  intro x hx
  obtain ⟨q, hq, hxq, hQ, hsub⟩ := hmar x (Finset.mem_coe.2 hx) (hΩ x)
  refine Finset.mem_biUnion.2 ⟨q, ?_, hxq⟩
  refine Finset.mem_filter.2 ⟨hq, fun P hP hPpar => absurd hPpar (hQ P hP), ?_⟩
  exact fun x' hx' => hXY x' (hsub x' hx')

end Geometry

section Solution

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **T1: locality of the solutions of the shifted perturbation problem.**  Let `F` be a family of
solutions: for each datum `D` of `XiCOneReal`, `‖ξ‖ < r₀` and cut parameter `s` in the polydisc,
`(δφ, δα) = F (rawOf D, ξ) s` satisfies `δφ = dphi …`, `DecFixed … false …` and
`Small … (c6' …)` for the data `renEdat` at the decoupled background of the cut parameters
`extParams (s ∘ renLabelEquiv.symm)` (the first three clauses of the output of `renDec_sharp`).
For two data of `S` with `RenC1Ag` on the component `Y = compY C`, and cut parameters supported in
`C`, of norm `< e^κ`, equal on the cubes whose patch lies in `Y`: `δα = δα'` on `S_Y` and
`δφ = δφ'` on `Y`.  The margins are those of `renDec_sharp`. -/
theorem renDec_solution_local {n : ℕ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    (hG : IsLevel Gp n) {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ K)}
    {X₁f : Finset (CTorus d L N₁ m₁ K)} (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X₁)
    (hPS : PolySetup Gp m₀ X₁) {r₀ : ℝ} (hr₀ : r₀ ≤ 1 / 16)
    (hD₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    (hδ₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {S : Set (BgData Gp N × (Fin 3 → ℂ))}
    (hS : ∀ u ∈ S, XiCOneReal Gp (compWeight L a₁) ν eps u.1)
    (hSξ : ∀ u ∈ S, ‖u.2‖ < r₀)
    {F : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (RenLabel Gp X₁ → ℂ) →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF : ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
      ‖ξ‖ < r₀ → ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
      ∀ (s' : DecParams Gp) (E : Edat Gp N),
        s' = extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) →
        E = renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D)
          (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D) ξ →
        (F (rawOf D, ξ) s).1 = dphi Gp (decG Gp (compWeight L a₁) ν s') E.2.1 E.1
            (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
        DecFixed Gp (compWeight L a₁) ν s' false E.2.1 E.1
            (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
        Small Gp (F (rawOf D, ξ) s).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (C : Finset (RenLabel Gp X₁)) {u u' : BgData Gp N × (Fin 3 → ℂ)} (hu : u ∈ S) (hu' : u' ∈ S)
    {s s' : RenLabel Gp X₁ → ℂ} (hs : s ∈ supN C (Real.exp κ)) (hs' : s' ∈ supN C (Real.exp κ))
    (hag : ∀ i ∈ C, Pset m₁ (renCube Gp X₁ i) ⊆ compY (renCube Gp X₁) X₁ C → s i = s' i)
    (hAg : RenC1Ag (renCube Gp X₁) X₁ C u u') :
    (∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ K) ∈
        SY Gp X₁f (C.image (renCube Gp X₁)) (finOf (compY (renCube Gp X₁) X₁ C)) →
      (F (rawOf u.1, u.2) s).2 x = (F (rawOf u'.1, u'.2) s').2 x) ∧
    (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ compY (renCube Gp X₁) X₁ C → ∀ i : Fin N,
      (F (rawOf u.1, u.2) s).1 (y, i) = (F (rawOf u'.1, u'.2) s').1 (y, i)) := by
  classical
  have hrows := renDec_row_agree hC hconn hG hX₁ hPS eps hS C hu hu' hs hs' hag hAg
  subst hX₁
  obtain ⟨hξ, hdat⟩ := hAg
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hΩ : ∀ x : CTorus d L N₁ m₁ K, x ∈ Gp.Ω 1 := fun x => by
    rw [hG.Ω_one]; exact Finset.mem_univ x
  set cc := renCube Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) with hcc
  have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm) P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs.2 _)
  have hsx' : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s' ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm) P‖ < Real.exp κ :=
    norm_extParams_lt hE1 (fun i => hs'.2 _)
  have hpoly : s ∈ polydisc (0 : RenLabel Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ) := fun i => by
    simpa using hs.2 i
  have hpoly' : s' ∈ polydisc (0 : RenLabel Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) → ℂ) (fun _ => Real.exp κ) := fun i => by
    simpa using hs'.2 i
  -- the component
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
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P = 1 ∧
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s' ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P = 1 :=
    fun P hP hPn => ⟨renExt_one_of_not_mem_parCubes _ hP hPn,
      renExt_one_of_not_mem_parCubes _ hP hPn⟩
  have hs0E : ∀ P ∈ parCubes Gp X₁f, P ∉ 𝒞 →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P = 0 ∧
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s' ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P = 0 :=
    fun P hP hP𝒞 => ⟨renExt_extS_zero hPS s C (fun i hi => hs.1 i hi) hP hP𝒞,
      renExt_extS_zero hPS s' C (fun i hi => hs'.1 i hi) hP hP𝒞⟩
  have hagE : ∀ P ∈ 𝒞, SubI Gp (cubeP P) Y →
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P =
      extS Gp (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) (s' ∘ (renLabelEquiv Gp (↑X₁f : Set (CTorus d L N₁ m₁ K))).symm)) P := by
    intro P hP𝒞 hSub
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hP𝒞
    have hsub : Pset m₁ (cc i) ⊆ Yc := fun x hx =>
      (hmemY x).1 (hSub ⟨x, hΩ x⟩ (mem_cubeP.2 hx))
    rw [hcc, renExt_extS_label (↑X₁f : Set (CTorus d L N₁ m₁ K)) s i, renExt_extS_label (↑X₁f : Set (CTorus d L N₁ m₁ K)) s' i]
    exact hag i hi hsub
  -- the solutions
  have hsol := hF u.1 (hS u hu) u.2 (hSξ u hu) s hpoly _ _ rfl rfl
  have hsol' := hF u'.1 (hS u' hu') u'.2 (hSξ u' hu') s' hpoly' _ _ rfl rfl
  have hH := renEdat_decHyp_of_flCore hC (hS u hu) (fun P => (hsx P).le) hr₀ (hSξ u hu) hD₀
  have hH' := renEdat_decHyp_of_flCore hC (hS u' hu') (fun P => (hsx' P).le) hr₀ (hSξ u' hu') hD₀
  -- equal `ξ`
  rw [← hξ] at hsol' hH' hrows ⊢
  have hε := hC.eps_pos
  have hK4 := (K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0).le
  have hC1pos : 0 < xiC1 d := by unfold xiC1; positivity
  have hK1 := bgK1_pos d L N
  have hcoef : 0 ≤ (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps := by
    positivity
  have hδ₁' : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * ‖u.2‖ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8) :=
    le_trans (mul_le_mul_of_nonneg_left (hSξ u hu).le hcoef) hδ₁
  obtain ⟨hα, hφ⟩ := i4a_local_rows hC.hS.fam hC.Sp hconn hC.hκ.le hC.hM
    (fun P => (hsx P).le) (fun P => (hsx' P).le) hH hH' hδ₀ hδ₁' hYnn hs1E hs0E hagE hrows
    hsol.2.1 hsol.2.2 hsol'.2.1 hsol'.2.2
  refine ⟨fun x hx => hα x hx, fun y hy i => ?_⟩
  exact (congrFun hsol.1 (y, i)).trans
    ((hφ y ((hmemY _).2 hy) i).trans (congrFun hsol'.1 (y, i)).symm)

end Solution

section Local

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **`renC2_local_cut_of`** (T3).  For a set `B` of sites with the block margin against `X₁`, the
cut functional of `C₂(B)`,
`(u, s) ↦ renC2On B ξ ν_u (α_s + δα) δφ` with `(δφ, δα) = F (rawOf D, ξ) s`, `ν_u = renMassU ν ξ`
and `α_s = decBgMult` at the cut parameters, satisfies `LocalityAEOn (e^κ)` for the agreement
`RenC1Ag` on the component. -/
theorem renC2_local_cut_of {n : ℕ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    (hG : IsLevel Gp n) {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ K)}
    {X₁f : Finset (CTorus d L N₁ m₁ K)} (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X₁)
    (hPS : PolySetup Gp m₀ X₁) (B : Finset (CTorus d L N₁ m₁ K))
    (hmar : BlockMargin Gp X₁f (↑B : Set (CTorus d L N₁ m₁ K)))
    {r₀ : ℝ} (hr₀ : r₀ ≤ 1 / 16)
    (hD₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    (hδ₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {S : Set (BgData Gp N × (Fin 3 → ℂ))}
    (hS : ∀ u ∈ S, XiCOneReal Gp (compWeight L a₁) ν eps u.1)
    (hSξ : ∀ u ∈ S, ‖u.2‖ < r₀)
    {F : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (RenLabel Gp X₁ → ℂ) →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF : ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
      ‖ξ‖ < r₀ → ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
      ∀ (s' : DecParams Gp) (E : Edat Gp N),
        s' = extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) →
        E = renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D)
          (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D) ξ →
        (F (rawOf D, ξ) s).1 = dphi Gp (decG Gp (compWeight L a₁) ν s') E.2.1 E.1
            (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
        DecFixed Gp (compWeight L a₁) ν s' false E.2.1 E.1
            (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
        Small Gp (F (rawOf D, ξ) s).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    : LocalityAEOn (Real.exp κ) S (fun i : RenLabel Gp X₁ => Pset m₁ (renCube Gp X₁ i))
      (compY (renCube Gp X₁) X₁) (RenC1Ag (renCube Gp X₁) X₁)
      (fun u s => renC2On Gp (compWeight L a₁) B u.2 (renMassU ν u.2)
        (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ)
          (extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm)) u.1 + (F (rawOf u.1, u.2) s).2)
        (F (rawOf u.1, u.2) s).1) := by
  classical
  intro C u u' hu hu' s s' hs hs' hag hAg
  obtain ⟨hδα, hδφ⟩ := renDec_solution_local hC hconn hG hX₁ hPS hr₀ hD₀ hδ₀ hδ₁ hS hSξ hF C hu hu'
    hs hs' hag hAg
  have hrows := renDec_row_agree hC hconn hG hX₁ hPS eps hS C hu hu' hs hs' hag hAg
  have hξ : u.2 = u'.2 := hAg.1
  have hΩ : ∀ x : CTorus d L N₁ m₁ K, x ∈ Gp.Ω 1 := fun x => by
    rw [hG.Ω_one]; exact Finset.mem_univ x
  have hBSY : ∀ x ∈ B, x ∈ SY Gp X₁f (C.image (renCube Gp X₁))
      (finOf (compY (renCube Gp X₁) X₁ C)) :=
    blockSites_subset_SY_of_blockMargin hmar hΩ _ _ fun y hy =>
      mem_finOf_set.2 (subset_compY (c := renCube Gp X₁) X₁ C (hX₁ ▸ Finset.mem_coe.2 hy))
  show renC2On Gp (compWeight L a₁) B u.2 (renMassU ν u.2) _ _ =
    renC2On Gp (compWeight L a₁) B u'.2 (renMassU ν u'.2) _ _
  rw [← hξ] at hrows hδα hδφ ⊢
  refine renC2On_congr (fun x hx => ?_) (fun y hy i => ?_)
  · have h1 := hrows.alpha x (hBSY x hx)
    simp only [Pi.add_apply]
    rw [add_right_cancel h1, hδα x (hBSY x hx)]
  · have h1 : RowSite Gp (compWeight L a₁) ν (0 : Gp.Ω 1 → ℂ) B y :=
      rowSite_iff_of_mass_potential.1 hy
    have h2 := rowSite_subset hC.Sp (rowSite_mono (fun x hx => hBSY x hx) h1)
    exact hδφ y (mem_finOf_set.1 h2) i

/-- **`renDphi_local_cut_of`** (T3).  For a point `p` with `p.1 ∈ X₁`, the cut functional of the
fluctuation field `δφ(p)`, `(u, s) ↦ (F (rawOf D, ξ) s).1 p`, satisfies `LocalityAEOn (e^κ)`
for the agreement `RenC1Ag` on the component. -/
theorem renDphi_local_cut_of {n : ℕ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hconn : HatConn Gp)
    (hG : IsLevel Gp n) {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ K)}
    {X₁f : Finset (CTorus d L N₁ m₁ K)} (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X₁)
    (hPS : PolySetup Gp m₀ X₁) (p : Gp.Ω 1 × Fin N) (hp : (p.1 : CTorus d L N₁ m₁ K) ∈ X₁f)
    {r₀ : ℝ} (hr₀ : r₀ ≤ 1 / 16)
    (hD₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    (hδ₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {S : Set (BgData Gp N × (Fin 3 → ℂ))}
    (hS : ∀ u ∈ S, XiCOneReal Gp (compWeight L a₁) ν eps u.1)
    (hSξ : ∀ u ∈ S, ‖u.2‖ < r₀)
    {F : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (RenLabel Gp X₁ → ℂ) →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF : ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
      ‖ξ‖ < r₀ → ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
      ∀ (s' : DecParams Gp) (E : Edat Gp N),
        s' = extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) →
        E = renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D)
          (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D) ξ →
        (F (rawOf D, ξ) s).1 = dphi Gp (decG Gp (compWeight L a₁) ν s') E.2.1 E.1
            (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
        DecFixed Gp (compWeight L a₁) ν s' false E.2.1 E.1
            (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
        Small Gp (F (rawOf D, ξ) s).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    : LocalityAEOn (Real.exp κ) S (fun i : RenLabel Gp X₁ => Pset m₁ (renCube Gp X₁ i))
      (compY (renCube Gp X₁) X₁) (RenC1Ag (renCube Gp X₁) X₁)
      (fun u s => (F (rawOf u.1, u.2) s).1 p) := by
  classical
  intro C u u' hu hu' s s' hs hs' hag hAg
  obtain ⟨-, hδφ⟩ := renDec_solution_local hC hconn hG hX₁ hPS hr₀ hD₀ hδ₀ hδ₁ hS hSξ hF C hu hu'
    hs hs' hag hAg
  have hξ : u.2 = u'.2 := hAg.1
  have hpY : (p.1 : CTorus d L N₁ m₁ K) ∈ compY (renCube Gp X₁) X₁ C :=
    subset_compY (c := renCube Gp X₁) X₁ C (hX₁ ▸ Finset.mem_coe.2 hp)
  show (F (rawOf u.1, u.2) s).1 p = (F (rawOf u'.1, u'.2) s').1 p
  exact hδφ p.1 hpY p.2

end Local

section RootLocal

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **`renC2_local_cut`** (T3).  At a block root `z` of the full level `k + 1`, with the root
neighbourhood `X₁ = X1 Gp m₀ k (fam m₀ (blockSite k z))` of `levelLocalCover` and the cover
`renCube`: the cut functional of `C₂(B_{k+1}(z))` satisfies `LocalityAEOn (e^κ)` with the agreement
`RenC1Ag` on the component.  The hypotheses are those of `levelLocalCover`, the margins of
`renDec_sharp`, the typing of the data, and the characterization of `F` by the first three clauses
of `renDec_sharp`. -/
theorem renC2_local_cut (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hG' : IsLevel Gp (k + 1)) {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    {r₀ : ℝ} (hr₀ : r₀ ≤ 1 / 16)
    (hD₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    (hδ₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {S : Set (BgData Gp N × (Fin 3 → ℂ))}
    (hS : ∀ u ∈ S, XiCOneReal Gp (compWeight L a₁) ν eps u.1)
    (hSξ : ∀ u ∈ S, ‖u.2‖ < r₀)
    {F : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) →
      (RenLabel Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) → ℂ) →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF : ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
      ‖ξ‖ < r₀ → ∀ s ∈ polydisc (0 : RenLabel Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) → ℂ)
        (fun _ => Real.exp κ),
      ∀ (s' : DecParams Gp) (E : Edat Gp N),
        s' = extParams Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))
          (s ∘ (renLabelEquiv Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))).symm) →
        E = renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D)
          (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D) ξ →
        (F (rawOf D, ξ) s).1 = dphi Gp (decG Gp (compWeight L a₁) ν s') E.2.1 E.1
            (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
        DecFixed Gp (compWeight L a₁) ν s' false E.2.1 E.1
            (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
        Small Gp (F (rawOf D, ξ) s).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    LocalityAEOn (Real.exp κ) S
      (fun i : RenLabel Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) =>
        Pset m₁ (renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))) i))
      (compY (renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))))
        (X1 Gp m₀ k (fam m₀ (blockSite k z))))
      (RenC1Ag (renCube Gp (X1 Gp m₀ k (fam m₀ (blockSite k z))))
        (X1 Gp m₀ k (fam m₀ (blockSite k z))))
      (fun u s => renC2On Gp (compWeight L a₁) (blockSites d L N₁ m₁ (k + 1) k z) u.2
        (renMassU ν u.2)
        (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ)
          (extParams Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))
            (s ∘ (renLabelEquiv Gp (X1 Gp m₀ k (fam m₀ (blockSite k z)))).symm)) u.1 +
          (F (rawOf u.1, u.2) s).2)
        (F (rawOf u.1, u.2) s).1) := by
  obtain ⟨hV, -⟩ := renLoc_fin_domains (N := N) Hm hC.Sp hG' hm₀ hN
  obtain ⟨hcov, hX₁, -, -, -, hmar, -⟩ := hV z
  exact renC2_local_cut_of hC hconn hG' hX₁ hcov.polySetup _ hmar hr₀ hD₀ hδ₀ hδ₁ hS hSξ hF

/-- **`renDphi_local_cut`** (T3).  At a site root `p` of the full level `k + 1`, with
`X₁ = X1 Gp m₀ k (fam m₀ p.1)`: the cut functional `(u, s) ↦ (F (rawOf D, ξ) s).1 p` of the
fluctuation field `δφ(p)` satisfies `LocalityAEOn (e^κ)` with the agreement `RenC1Ag`. -/
theorem renDphi_local_cut (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hconn : HatConn Gp) (hG' : IsLevel Gp (k + 1)) {m₀ : ℕ} (hm₀ : 1 ≤ m₀) (hN : L ^ m₀ ∣ N₁)
    (p : Gp.Ω 1 × Fin N)
    {r₀ : ℝ} (hr₀ : r₀ ≤ 1 / 16)
    (hD₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    (hδ₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {S : Set (BgData Gp N × (Fin 3 → ℂ))}
    (hS : ∀ u ∈ S, XiCOneReal Gp (compWeight L a₁) ν eps u.1)
    (hSξ : ∀ u ∈ S, ‖u.2‖ < r₀)
    {F : RawData d L (N₁ * L ^ m₁) (k + 1) N × (Fin 3 → ℂ) →
      (RenLabel Gp (X1 Gp m₀ k (fam m₀ (p.1 : CTorus d L N₁ m₁ (k + 1)))) → ℂ) →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF : ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
      ‖ξ‖ < r₀ → ∀ s ∈ polydisc
        (0 : RenLabel Gp (X1 Gp m₀ k (fam m₀ (p.1 : CTorus d L N₁ m₁ (k + 1)))) → ℂ)
        (fun _ => Real.exp κ),
      ∀ (s' : DecParams Gp) (E : Edat Gp N),
        s' = extParams Gp (X1 Gp m₀ k (fam m₀ (p.1 : CTorus d L N₁ m₁ (k + 1))))
          (s ∘ (renLabelEquiv Gp (X1 Gp m₀ k (fam m₀ (p.1 : CTorus d L N₁ m₁ (k + 1))))).symm) →
        E = renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D)
          (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D) ξ →
        (F (rawOf D, ξ) s).1 = dphi Gp (decG Gp (compWeight L a₁) ν s') E.2.1 E.1
            (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
        DecFixed Gp (compWeight L a₁) ν s' false E.2.1 E.1
            (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
        Small Gp (F (rawOf D, ξ) s).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    LocalityAEOn (Real.exp κ) S
      (fun i : RenLabel Gp (X1 Gp m₀ k (fam m₀ (p.1 : CTorus d L N₁ m₁ (k + 1)))) =>
        Pset m₁ (renCube Gp (X1 Gp m₀ k (fam m₀ (p.1 : CTorus d L N₁ m₁ (k + 1)))) i))
      (compY (renCube Gp (X1 Gp m₀ k (fam m₀ (p.1 : CTorus d L N₁ m₁ (k + 1)))))
        (X1 Gp m₀ k (fam m₀ (p.1 : CTorus d L N₁ m₁ (k + 1)))))
      (RenC1Ag (renCube Gp (X1 Gp m₀ k (fam m₀ (p.1 : CTorus d L N₁ m₁ (k + 1)))))
        (X1 Gp m₀ k (fam m₀ (p.1 : CTorus d L N₁ m₁ (k + 1)))))
      (fun u s => (F (rawOf u.1, u.2) s).1 p) := by
  obtain ⟨-, hV⟩ := renLoc_fin_domains (N := N) Hm hC.Sp hG' hm₀ hN
  obtain ⟨hcov, hX₁, -, -, hp, -⟩ := hV (p.1, p.2)
  exact renDphi_local_cut_of hC hconn hG' hX₁ hcov.polySetup p hp hr₀ hD₀ hδ₀ hδ₁ hS hSξ hF

end RootLocal

section Inhabited

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The solution-family hypothesis of the locality laws is inhabited**: under the margins of
`renDec_sharp`, a family `F` with the three characterizing clauses used by `renDec_solution_local`
exists (it is the family of `renDec_sharp`). -/
theorem renDec_solution_family_exists
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) {r₀ : ℝ} (hr₀0 : 0 < r₀)
    (hr₀ : r₀ ≤ 1 / 16) (X₁ : Set (CTorus d L N₁ m₁ K))
    (hD₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤ 1)
    (hδ₀ : 2 * (K4 d L N BG κ * (xiC1 d * eps)) + 3 * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : (3 / 2 + 32 / 15 * (3 + (K4 d L N BG κ + bgK1 d L N) * xiC1 d)) * eps * r₀ ≤
      deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8)) :
    ∃ F : RawData d L (N₁ * L ^ m₁) K N × (Fin 3 → ℂ) → (RenLabel Gp X₁ → ℂ) →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ),
    ∀ D : BgData Gp N, XiCOneReal Gp (compWeight L a₁) ν eps D → ∀ ξ : Fin 3 → ℂ,
      ‖ξ‖ < r₀ → ∀ s ∈ polydisc (0 : RenLabel Gp X₁ → ℂ) (fun _ => Real.exp κ),
      ∀ (s' : DecParams Gp) (E : Edat Gp N),
        s' = extParams Gp X₁ (s ∘ (renLabelEquiv Gp X₁).symm) →
        E = renEdat ν eps D (decBgField Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D)
          (decBgMult Gp (compWeight L a₁) ν (rho4 d L N BG κ) s' D) ξ →
        (F (rawOf D, ξ) s).1 = dphi Gp (decG Gp (compWeight L a₁) ν s') E.2.1 E.1
            (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
        DecFixed Gp (compWeight L a₁) ν s' false E.2.1 E.1
            (pertSource Gp (compWeight L a₁) E.2.2.1 E.2.2.2) (F (rawOf D, ξ) s).2 ∧
        Small Gp (F (rawOf D, ξ) s).2 (c6' d L N (famConst d L BG κ) (gamma1 d / 8)) := by
  obtain ⟨F, -, hF⟩ := renDec_sharp hC hr₀0 hr₀ X₁ hD₀ hδ₀ hδ₁
  refine ⟨F, fun D hD ξ hξ s hs s' E hs' hE => ?_⟩
  obtain ⟨h1, h2, h3, -⟩ := hF D hD ξ hξ s hs s' E hs' hE
  exact ⟨h1, h2, h3⟩

end Inhabited

end Balaban.Localization
