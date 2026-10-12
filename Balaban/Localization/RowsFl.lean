/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5FluctStep
public import Balaban.Fluctuation.Lemma25Xi

/-!
# Locality of the fluctuation field with the data agreeing on the sites that are read (package 3c)

Narrower versions of `local_step_fpS` and `i4a_local_fpS` (`I5FluctStep.lean`).  Write `B_F = S_Y^F`
(`SYF`) and `R(B_F)` (`RowF`) for the set of sites read by a row of the operator `H_D(α)` at a
site of `B_F`: the site itself and the sites `w` with `H_D(0) x w ≠ 0` (nearest neighbours and the
block-diagonal part), `x ∈ B_F`.  The agreement structure `DataAgreeRows B R` asks: the potential
on `B`; the field `φ₀` on `R`; the perturbation `δΨ` and the source `f₁` on `B`.  The collar
condition is a separate hypothesis `δΨ y = δΨ' y` for the collar sites adjacent to `B`; for a
full-level `H` (`Balaban.Fluctuation.IsLevel H k`) the collar is empty and the hypothesis is void.

Main results: `DataAgreeRows.of_dataAgreeS` (the landed agreement implies the narrow one, no extra
hypothesis: `R(S_Y^F) ⊆ Y` holds by definition of `Z_Y^F`), `local_step_fpS_rows`,
`local_step_fpS_rows_level`, `i4a_local_fpS_rows`, `i4a_local_fpS_rows_level`, and the landed
statements re-derived (`local_step_fpS'`, `i4a_local_fpS'`).

## Where `DataAgreeS` is used, and on which set (T5)

| use (`I5FluctStep.lean`) | field | set needed |
|---|---|---|
| `local_step_fpS`, `hAeq` (l. ~87) | `alpha` | `B_F` |
| `hdphi`, source of `dg5'_inner_fp` (l. ~99, `Fsrc` at `b`) | `psi`, `src`, `phi` | `b ∈ B_F` (`dg5'_inner_fp` reads `f` on `S_Y^F` only) |
| `Nexp_congr`, `hφx`, `hFx` at `x` (l. ~110) | `phi`, `psi`, `src` | `x ∈ B_F` |
| `Nexp_congr`, row hypothesis `hy` (l. ~114) | `phi` | `y` with `H x y ≠ 0`: `R(B_F)` |
| `pertSource_congrS` (l. ~38-52) | `psi`, `src`, `psi_collar` | `z ∈ B_F`; collar sites adjacent to `z` |
| `i4a_local_fpS`, final `dg5'_inner_fp` (l. ~180) | `alpha`, `psi`, `src`, `phi` | `B_F` only; the conclusion on all of `Y` comes from `dg5'_inner_fp`, which evaluates at `x ∈ Y` but reads its input on `S_Y^F` |

No use needs `phi`, `psi` or `src` outside `B_F ∪ R(B_F)`: there is no tension with item 6 of the
footprint note.  (b) `collar H = ∅` for `Balaban.Fluctuation.IsLevel H k` (`IsLevel.collar_eq`); `IsLevel` is assumed
for the whole-lattice sets of the fluctuation step (`Lemma25Xi.lean`, `CriticalPoint.lean`).

Not proved here: the fan/engine versions (footprint note, item 7) and the physical-reads lemma
(that the physical comparison data agree on `R(B_F)`).
-/

@[expose] public section

namespace Balaban.Localization.Dec2.RowsFl

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection
  Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}

open Classical in
/-- **The sites read by the rows of the operator at the sites of `B`**: `B` itself and the sites
`w` with `H_D(0) x w ≠ 0` for some operator site `x` of `B`. -/
noncomputable def RowF (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (B : Finset (CTorus d L N₁ m₁ K)) : Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun y => ∃ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ B ∧
    (y = (x : CTorus d L N₁ m₁ K) ∨
      ∃ w : H.Ω 1, dirichletOperator H a ν 0 x w ≠ 0 ∧ y = (w : CTorus d L N₁ m₁ K))

theorem subset_RowF {B : Finset (CTorus d L N₁ m₁ K)} {x : H.Ω 1}
    (hx : (x : CTorus d L N₁ m₁ K) ∈ B) : (x : CTorus d L N₁ m₁ K) ∈ RowF H a ν B := by
  classical
  unfold RowF
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx, Or.inl rfl⟩

/-- A nonzero entry of a row of `H_D(α)` at a site of `B` lies in `RowF B`, for every `α`. -/
theorem row_mem_RowF {B : Finset (CTorus d L N₁ m₁ K)} {x y : H.Ω 1}
    (hx : (x : CTorus d L N₁ m₁ K) ∈ B) (α : H.Ω 1 → ℂ)
    (h : dirichletOperator H a ν α x y ≠ 0) : (y : CTorus d L N₁ m₁ K) ∈ RowF H a ν B := by
  classical
  unfold RowF
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, x, hx, ?_⟩
  by_cases hxy : x = y
  · subst hxy; exact Or.inl rfl
  · refine Or.inr ⟨y, ?_, rfl⟩
    rw [dirichletOperator_eq_add a ν α] at h
    simpa [Matrix.add_apply, Matrix.diagonal_apply, hxy] using h

variable {X₁ Y : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}

/-- `R(S_Y^F) ⊆ Y`: the rows at the sites of `S_Y^F` read only sites of `Y`. -/
theorem RowF_SYF_subset_Y {y : CTorus d L N₁ m₁ K}
    (hy : y ∈ RowF H a ν (SYF C H a ν X₁ 𝒞 Y)) : y ∈ Y := by
  classical
  unfold RowF at hy
  obtain ⟨-, x, hx, hyx⟩ := Finset.mem_filter.1 hy
  obtain ⟨z, hz, hxz⟩ := Finset.mem_biUnion.1 hx
  have hzf := (Finset.mem_filter.1 hz).2.2.2
  rcases hyx with rfl | ⟨w, hw, rfl⟩
  · exact hzf _ (mem_footprint_self hxz)
  · exact hzf _ ⟨x, hxz, Or.inr ⟨w, hw, rfl⟩⟩

/-- **Agreement of two data sets: the potential on `B`, the field on `R`, the perturbation and the
source on `B`.**  (The collar condition is a separate hypothesis of the theorems.) -/
structure DataAgreeRows (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (N : ℕ)
    (B R : Finset (CTorus d L N₁ m₁ K))
    (α₀ α₀' : H.Ω 1 → ℂ) (φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (f₁ f₁' : H.Ω 1 × Fin N → ℂ) : Prop where
  alpha : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ B → α₀ x = α₀' x
  phi : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ R → φ₀ x = φ₀' x
  psi : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ B → δΨ x = δΨ' x
  src : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ B → ∀ i, f₁ (x, i) = f₁' (x, i)

/-- Reflexivity: the structure is inhabited (for every choice of sets and data). -/
theorem DataAgreeRows.refl (B R : Finset (CTorus d L N₁ m₁ K)) (α₀ : H.Ω 1 → ℂ)
    (φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ) (f₁ : H.Ω 1 × Fin N → ℂ) :
    DataAgreeRows H N B R α₀ α₀ φ₀ φ₀ δΨ δΨ f₁ f₁ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem nonempty_dataAgreeRows (B R : Finset (CTorus d L N₁ m₁ K)) :
    Nonempty (DataAgreeRows H N B R (0 : H.Ω 1 → ℂ) 0 (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)) :=
  ⟨DataAgreeRows.refl B R _ _ _ _⟩

/-- The landed agreement on `Y` (potential on `S_Y^F`) implies the narrow agreement on
`(S_Y^F, R(S_Y^F))`; no extra hypothesis, since `R(S_Y^F) ⊆ Y`. -/
theorem DataAgreeRows.of_dataAgreeS {α₀ α₀' : H.Ω 1 → ℂ}
    {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ} {f₁ f₁' : H.Ω 1 × Fin N → ℂ}
    (hD : DataAgreeS H N Y (SYF C H a ν X₁ 𝒞 Y) α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁') :
    DataAgreeRows H N (SYF C H a ν X₁ 𝒞 Y) (RowF H a ν (SYF C H a ν X₁ 𝒞 Y))
      α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁' :=
  ⟨hD.alpha, fun x hx => hD.phi x (RowF_SYF_subset_Y hx),
    fun x hx => hD.psi x (SYF_subset_Y hx), fun x hx => hD.src x (SYF_subset_Y hx)⟩

/-- `pertSource` at a site of `B` reads `δΨ`, `f₁` there and `δΨ` on the collar sites adjacent
to `B`. -/
theorem pertSource_congrRows {B R : Finset (CTorus d L N₁ m₁ K)} {α₀ α₀' : H.Ω 1 → ℂ}
    {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ} {f₁ f₁' : H.Ω 1 × Fin N → ℂ}
    (hD : DataAgreeRows H N B R α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    (hcol : ∀ y ∈ collar H,
      (∃ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ B ∧ Adj (x : CTorus d L N₁ m₁ K) y) →
      δΨ y = δΨ' y)
    {z : H.Ω 1} (hz : (z : CTorus d L N₁ m₁ K) ∈ B) (i : Fin N) :
    pertSource H a δΨ f₁ (z, i) = pertSource H a δΨ' f₁' (z, i) := by
  unfold pertSource qStar boundaryTerm
  simp only [Pi.add_apply]
  rw [hD.psi z hz, hD.src z hz i]
  congr 2
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  · by_cases h : (z : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∈ collar H
    · simp only [h, ↓reduceIte]
      rw [hcol _ h ⟨z, hz, μ, Or.inl rfl⟩]
    · simp only [h, ↓reduceIte]
  · by_cases h : (z : CTorus d L N₁ m₁ K) - Pi.single μ 1 ∈ collar H
    · simp only [h, ↓reduceIte]
      rw [hcol _ h ⟨z, hz, μ, Or.inr (by simp)⟩]
    · simp only [h, ↓reduceIte]

/-- **One step of the comparison, narrow agreement** (general collar form). -/
theorem local_step_fpS_rows {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG) (S : FootLocal C H a ν Kc Cx)
    {κ : ℝ} (hκ : 0 ≤ κ) (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : H.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : H.Ω 1 × Fin N → ℂ} {δ₀ ρ : ℝ} (hα0 : Small H α₀ δ₀) (hα0' : Small H α₀' δ₀)
    (hρ : δ₀ + ρ ≤ gamma1 d / 8)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → extS C s P = 1 ∧ extS C s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → extS C s P = 0 ∧ extS C s' P = 0)
    (hag : ∀ P ∈ 𝒞, P ∈ A → extS C s P = extS C s' P)
    (hD : DataAgreeRows H N (SYF C H a ν X₁ 𝒞 Y) (RowF H a ν (SYF C H a ν X₁ 𝒞 Y))
      α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    (hcol : ∀ y ∈ collar H,
      (∃ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y ∧ Adj (x : CTorus d L N₁ m₁ K) y) →
      δΨ y = δΨ' y)
    {ξ η : H.Ω 1 → ℂ} (hξ : ∀ x, ‖ξ x‖ ≤ ρ) (hη : ∀ x, ‖η x‖ ≤ ρ)
    (hξη : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → ξ x = η x) :
    ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y →
      Smap H (decG C H a ν s) (dirichletOperator H a ν α₀) ιU α₀ φ₀ (pertSource H a δΨ f₁) ξ x =
      Smap H (decG C H a ν s') (dirichletOperator H a ν α₀') ιU α₀' φ₀' (pertSource H a δΨ' f₁') η x := by
  classical
  intro x hxT
  have hxY : (x : CTorus d L N₁ m₁ K) ∈ Y := SYF_subset_Y hxT
  have hd0 : 0 < d := by have := S.hd; omega
  obtain ⟨-, hunit⟩ := hF.2.2 C H S.toCoverBase hκ hM hs N
  obtain ⟨-, hunit'⟩ := hF.2.2 C H S.toCoverBase hκ hM hs' N
  have hδα : Small H (toAlpha H ξ) ρ := small_toAlpha H ξ hξ
  have hδα' : Small H (toAlpha H η) ρ := small_toAlpha H η hη
  have hA : Small H (α₀ + toAlpha H ξ) (gamma1 d / 8) := fun y =>
    ((Small.add hα0 hδα) y).trans hρ
  have hA' : Small H (α₀' + toAlpha H η) (gamma1 d / 8) := fun y =>
    ((Small.add hα0' hδα') y).trans hρ
  have hAeq : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y →
      (α₀ + toAlpha H ξ) y = (α₀' + toAlpha H η) y := by
    intro y hy
    simp only [Pi.add_apply]
    rw [hD.alpha y hy, show toAlpha H ξ y = toAlpha H η y by
      unfold toAlpha; rw [hξη y hy]]
  have hdphi : ∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) (toAlpha H ξ) (y, i) =
      dphi H (decG C H a ν s') α₀' φ₀' (pertSource H a δΨ' f₁') (toAlpha H η) (y, i) := by
    intro y hy i
    unfold dphi
    rw [liftOp_mulVec, liftOp_mulVec]
    refine dg5'_inner_fp S hY (admPot_of_small hd0 hA) (admPot_of_small hd0 hA')
      (hunit (admPot_of_small hd0 hA)) (hunit' (admPot_of_small hd0 hA')) hs1 hs0 hag hAeq
      (f := fun b => Fsrc φ₀ (pertSource H a δΨ f₁) (toAlpha H ξ) (b, i))
      (f' := fun b => Fsrc φ₀' (pertSource H a δΨ' f₁') (toAlpha H η) (b, i)) ?_ y hy
    intro b hb
    simp only [Fsrc]
    rw [pertSource_congrRows hD hcol hb i, hD.phi b (subset_RowF hb)]
    congr 2
    unfold toAlpha; rw [hξη b hb]
  -- the geometry of `x`
  obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hxT
  have hzZ' := Finset.mem_filter.1 hzZ
  unfold Smap
  rw [Nmap_explicit, Nmap_explicit]
  congr 1
  refine Nexp_congr ιU ?_ (fun i => by rw [hD.phi x (subset_RowF hxT)]) (fun i => pertSource_congrRows hD hcol hxT i)
    (fun i => hdphi x hxY i) (fun y hy => ?_)
  · intro y
    rw [dirichletOperator_eq_add a ν α₀, dirichletOperator_eq_add a ν α₀']
    simp only [Matrix.add_apply, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy; simp [hD.alpha x hxT]
    · simp [hxy]
  · have hyR := row_mem_RowF hxT α₀ hy
    have hyY : (y : CTorus d L N₁ m₁ K) ∈ Y := RowF_SYF_subset_Y hyR
    exact ⟨fun i => by rw [hD.phi y hyR], fun i => hdphi y hyY i⟩

/-- **Theorem I-4a (e), narrow agreement** (general collar form). -/
theorem i4a_local_fpS_rows {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG) (S : FootLocal C H a ν Kc Cx)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : H.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : H.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (Hh : DecHyp H a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) (H' : DecHyp H a ν ιU α₀' φ₀' δΨ' f₁' δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → extS C s P = 1 ∧ extS C s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → extS C s P = 0 ∧ extS C s' P = 0)
    (hag : ∀ P ∈ 𝒞, P ∈ A → extS C s P = extS C s' P)
    (hD : DataAgreeRows H N (SYF C H a ν X₁ 𝒞 Y) (RowF H a ν (SYF C H a ν X₁ 𝒞 Y))
      α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    (hcol : ∀ y ∈ collar H,
      (∃ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y ∧ Adj (x : CTorus d L N₁ m₁ K) y) →
      δΨ y = δΨ' y)
    {δα δα' : H.Ω 1 → ℂ}
    (hfix : DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα)
    (hsm : Small H δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed C H a ν s' ιU α₀' φ₀' (pertSource H a δΨ' f₁') δα')
    (hsm' : Small H δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → δα x = δα' x) ∧
    (∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα (y, i) =
      dphi H (decG C H a ν s') α₀' φ₀' (pertSource H a δΨ' f₁') δα' (y, i)) := by
  classical
  have hBG := hF.2.1
  have hd0 : 0 < d := by have := S.hd; omega
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ B := by have := famConst_ge_one (L := L) hBG κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ Hh.δ₀_nn Hh.δ₁_nn hδ₀ hδ₁
  obtain ⟨⟨hfam, -⟩, hunit⟩ := hF.2.2 C H S.toCoverBase hκ hM hs N
  obtain ⟨⟨hfam', -⟩, hunit'⟩ := hF.2.2 C H S.toCoverBase hκ hM hs' N
  obtain ⟨ξ, hξB, hξfix, hξuniq, hit⟩ := smap_fixed_iterates hfam Hh.setup hC
  obtain ⟨ξ', hξB', hξfix', hξuniq', hit'⟩ := smap_fixed_iterates hfam' H'.setup hC
  -- identify `toAlpha ξ` with `δα`
  have hid : ∀ {s₀ : DecParams C} {α₀₀ : H.Ω 1 → ℂ} {φ₀₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}
      {Fs₀ : H.Ω 1 × Fin N → ℂ} {ξ₀ δα₀ : H.Ω 1 → ℂ},
      Smap H (decG C H a ν s₀) (dirichletOperator H a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀ ξ₀ = ξ₀ →
      ξ₀ ∈ Metric.closedBall (0 : H.Ω 1 → ℂ) (c6' d L N B Γ) →
      (∀ ξ' ∈ Metric.closedBall (0 : H.Ω 1 → ℂ) (c6' d L N B Γ),
        Smap H (decG C H a ν s₀) (dirichletOperator H a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀ ξ' = ξ' → ξ' = ξ₀) →
      DecFixed C H a ν s₀ ιU α₀₀ φ₀₀ Fs₀ δα₀ → Small H δα₀ (c6' d L N B Γ) →
      toAlpha H ξ₀ = δα₀ := by
    intro s₀ α₀₀ φ₀₀ Fs₀ ξ₀ δα₀ _ _ huniq hf hsm₀
    have hm : ofAlpha H δα₀ ∈ Metric.closedBall (0 : H.Ω 1 → ℂ) (c6' d L N B Γ) := by
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg (c6'_pos (d := d) (L := L) (N := N) hB0 hΓ).le).2
        fun x => ?_
      rw [norm_ofAlpha]; exact hsm₀ x
    have hf' : Smap H (decG C H a ν s₀) (dirichletOperator H a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀
        (ofAlpha H δα₀) = ofAlpha H δα₀ := by
      funext x
      unfold Smap
      rw [toAlpha_ofAlpha]
      have := congrFun hf x
      unfold DecFixed at hf
      rw [hf]
      rfl
    rw [← huniq _ hm hf', toAlpha_ofAlpha]
  have e1 : toAlpha H ξ = δα := hid hξfix hξB hξuniq hfix hsm
  have e2 : toAlpha H ξ' = δα' := hid hξfix' hξB' hξuniq' hfix' hsm'
  have hpoly : ∀ {α₀₀ : H.Ω 1 → ℂ}, Small H α₀₀ δ₀ → δ₀ + c6' d L N B Γ ≤ Γ := by
    intro _ _; linarith [hC.poly, hC.ρ_nn]
  -- the pair induction
  have hagreeξ : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → ξ x = ξ' x := by
    refine fixed_agree_of_step (T := fun x : H.Ω 1 => (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y)
      (fun u v hu hv huv i hi => ?_) (fun n => ⟨(hit n).1, (hit n).2⟩)
      (fun n => ⟨(hit' n).1, (hit' n).2⟩) hC.ρ_nn
    exact local_step_fpS_rows hF S hκ hM hs hs' Hh.alpha0 H'.alpha0 (hpoly Hh.alpha0)
      hY hs1 hs0 hag hD hcol hu hv huv i hi
  have hδ : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → δα x = δα' x := by
    intro x hx
    rw [← e1, ← e2]
    unfold toAlpha
    rw [hagreeξ x hx]
  refine ⟨hδ, fun y hy i => ?_⟩
  have hA : Small H (α₀ + δα) Γ := fun z => ((Small.add Hh.alpha0 hsm) z).trans (hpoly Hh.alpha0)
  have hA' : Small H (α₀' + δα') Γ := fun z =>
    ((Small.add H'.alpha0 hsm') z).trans (hpoly H'.alpha0)
  unfold dphi
  rw [liftOp_mulVec, liftOp_mulVec]
  refine dg5'_inner_fp S hY (admPot_of_small hd0 hA) (admPot_of_small hd0 hA')
    (hunit (admPot_of_small hd0 hA)) (hunit' (admPot_of_small hd0 hA')) hs1 hs0 hag
    (fun z hz => ?_) (f := fun b => Fsrc φ₀ (pertSource H a δΨ f₁) δα (b, i))
    (f' := fun b => Fsrc φ₀' (pertSource H a δΨ' f₁') δα' (b, i)) (fun b hb => ?_) y hy
  · simp only [Pi.add_apply]
    rw [hD.alpha z hz, hδ z hz]
  · simp only [Fsrc]
    rw [pertSource_congrRows hD hcol hb i, hD.phi b (subset_RowF hb), hδ b hb]

/-! ### Full-level forms: the collar is empty, so the collar hypothesis disappears. -/

/-- **One step, narrow agreement, full-level `H`.** -/
theorem local_step_fpS_rows_level {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG) (S : FootLocal C H a ν Kc Cx)
    {κ : ℝ} (hκ : 0 ≤ κ) (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : H.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : H.Ω 1 × Fin N → ℂ} {δ₀ ρ : ℝ} (hα0 : Small H α₀ δ₀) (hα0' : Small H α₀' δ₀)
    (hρ : δ₀ + ρ ≤ gamma1 d / 8)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → extS C s P = 1 ∧ extS C s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → extS C s P = 0 ∧ extS C s' P = 0)
    (hag : ∀ P ∈ 𝒞, P ∈ A → extS C s P = extS C s' P)
    (hD : DataAgreeRows H N (SYF C H a ν X₁ 𝒞 Y) (RowF H a ν (SYF C H a ν X₁ 𝒞 Y))
      α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {k : ℕ} (hlev : Balaban.Fluctuation.IsLevel H k)
    {ξ η : H.Ω 1 → ℂ} (hξ : ∀ x, ‖ξ x‖ ≤ ρ) (hη : ∀ x, ‖η x‖ ≤ ρ)
    (hξη : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → ξ x = η x) :
    ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y →
      Smap H (decG C H a ν s) (dirichletOperator H a ν α₀) ιU α₀ φ₀ (pertSource H a δΨ f₁) ξ x =
      Smap H (decG C H a ν s') (dirichletOperator H a ν α₀') ιU α₀' φ₀' (pertSource H a δΨ' f₁') η x := 
  local_step_fpS_rows hF S hκ hM hs hs' hα0 hα0' hρ hY hs1 hs0 hag hD
    (fun y hy _ => absurd hy (by simp [(Balaban.Fluctuation.IsLevel.collar_eq hlev)])) hξ hη hξη

/-- **Theorem I-4a (e), narrow agreement, full-level `H`.** -/
theorem i4a_local_fpS_rows_level {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG) (S : FootLocal C H a ν Kc Cx)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : H.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : H.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (Hh : DecHyp H a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) (H' : DecHyp H a ν ιU α₀' φ₀' δΨ' f₁' δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → extS C s P = 1 ∧ extS C s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → extS C s P = 0 ∧ extS C s' P = 0)
    (hag : ∀ P ∈ 𝒞, P ∈ A → extS C s P = extS C s' P)
    (hD : DataAgreeRows H N (SYF C H a ν X₁ 𝒞 Y) (RowF H a ν (SYF C H a ν X₁ 𝒞 Y))
      α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {k : ℕ} (hlev : Balaban.Fluctuation.IsLevel H k)
    {δα δα' : H.Ω 1 → ℂ}
    (hfix : DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα)
    (hsm : Small H δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed C H a ν s' ιU α₀' φ₀' (pertSource H a δΨ' f₁') δα')
    (hsm' : Small H δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → δα x = δα' x) ∧
    (∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα (y, i) =
      dphi H (decG C H a ν s') α₀' φ₀' (pertSource H a δΨ' f₁') δα' (y, i)) := 
  i4a_local_fpS_rows hF S hκ hM hs hs' Hh H' hδ₀ hδ₁ hY hs1 hs0 hag hD
    (fun y hy _ => absurd hy (by simp [(Balaban.Fluctuation.IsLevel.collar_eq hlev)])) hfix hsm hfix' hsm'

/-! ### The landed statements re-derived -/

/-- `local_step_fpS` from the narrow form. -/
theorem local_step_fpS' {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG) (S : FootLocal C H a ν Kc Cx)
    {κ : ℝ} (hκ : 0 ≤ κ) (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : H.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : H.Ω 1 × Fin N → ℂ} {δ₀ ρ : ℝ} (hα0 : Small H α₀ δ₀) (hα0' : Small H α₀' δ₀)
    (hρ : δ₀ + ρ ≤ gamma1 d / 8)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → extS C s P = 1 ∧ extS C s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → extS C s P = 0 ∧ extS C s' P = 0)
    (hag : ∀ P ∈ 𝒞, P ∈ A → extS C s P = extS C s' P)
    (hD : DataAgreeS H N Y (SYF C H a ν X₁ 𝒞 Y) α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {ξ η : H.Ω 1 → ℂ} (hξ : ∀ x, ‖ξ x‖ ≤ ρ) (hη : ∀ x, ‖η x‖ ≤ ρ)
    (hξη : ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → ξ x = η x) :
    ∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y →
      Smap H (decG C H a ν s) (dirichletOperator H a ν α₀) ιU α₀ φ₀ (pertSource H a δΨ f₁) ξ x =
      Smap H (decG C H a ν s') (dirichletOperator H a ν α₀') ιU α₀' φ₀' (pertSource H a δΨ' f₁') η x :=
  local_step_fpS_rows hF S hκ hM hs hs' hα0 hα0' hρ hY hs1 hs0 hag (DataAgreeRows.of_dataAgreeS hD)
    (fun y hy hadj => hD.psi_collar y hy (by
      obtain ⟨x, hx, hxy⟩ := hadj
      exact ⟨x, SYF_subset_Y hx, hxy⟩)) hξ hη hξη

/-- `i4a_local_fpS` from the narrow form. -/
theorem i4a_local_fpS' {cstar BG : ℝ} (hF : FamSpec d L Kc Cx cstar BG) (S : FootLocal C H a ν Kc Cx)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams C} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : H.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : H.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (Hh : DecHyp H a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) (H' : DecHyp H a ν ιU α₀' φ₀' δΨ' f₁' δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    {A : Finset (ℕ × CTorus d L N₁ m₁ K)} (hY : IsIncUnion C H a ν X₁ 𝒞 Y A)
    (hs1 : ∀ P ∈ C.cubeIdx, P ∉ C.parCubes X₁ → extS C s P = 1 ∧ extS C s' P = 1)
    (hs0 : ∀ P ∈ C.parCubes X₁, P ∉ 𝒞 → extS C s P = 0 ∧ extS C s' P = 0)
    (hag : ∀ P ∈ 𝒞, P ∈ A → extS C s P = extS C s' P)
    (hD : DataAgreeS H N Y (SYF C H a ν X₁ 𝒞 Y) α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {δα δα' : H.Ω 1 → ℂ}
    (hfix : DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα)
    (hsm : Small H δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed C H a ν s' ιU α₀' φ₀' (pertSource H a δΨ' f₁') δα')
    (hsm' : Small H δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : H.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SYF C H a ν X₁ 𝒞 Y → δα x = δα' x) ∧
    (∀ y : H.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi H (decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα (y, i) =
      dphi H (decG C H a ν s') α₀' φ₀' (pertSource H a δΨ' f₁') δα' (y, i)) :=
  i4a_local_fpS_rows hF S hκ hM hs hs' Hh H' hδ₀ hδ₁ hY hs1 hs0 hag (DataAgreeRows.of_dataAgreeS hD)
    (fun y hy hadj => hD.psi_collar y hy (by
      obtain ⟨x, hx, hxy⟩ := hadj
      exact ⟨x, SYF_subset_Y hx, hxy⟩)) hfix hsm hfix' hsm'

end Balaban.Localization.Dec2.RowsFl
