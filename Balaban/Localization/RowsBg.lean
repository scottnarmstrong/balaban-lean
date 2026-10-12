/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledBackgroundLocal
import Mathlib.Tactic.Linarith

/-!
# Row-narrowed locality of the decoupled background field (FOOTPRINT package 3a)

Parallel versions of `local_step`, `i4a_local`, `i4b_local` in which agreement of the data on the
whole component `Y₁` is replaced by agreement on the sites the proofs read: the interaction boxes
`B = SY G X₁ 𝒞 Y₁` and the sites `RowSite` read by the rows of the Dirichlet operator at the sites
of `B` (`B` itself, and the `y` with `H_D(α₀) x y ≠ 0` for some `x ∈ B`). The landed theorems are
untouched, and recovered as corollaries (`local_step_of_rows`, `i4a_local_of_rows`,
`i4b_local_of_rows`); no inclusion hypothesis is needed since `row_mem_hatBox` supplies
`RowSite ⊆ Y₁`.

Not proved here: the square-root, fluctuation and fan versions (FOOTPRINT items 4–7) and the
physical-reads lemma.

## Where agreement on `Y₁` is used in the landed proofs, and the set really needed

| landed place | use | set really needed |
| --- | --- | --- |
| `DecoupledFieldLocal` 404–418 (`hdphi`, `dg5'_inner` source) | `α₀` | `B` (`dg5'_inner` hypothesis `hA`) |
| same, `pertSource_congr` (346–364) | `δΨ`, `f₁` and `δΨ` on collar sites adjacent | `B` and collar sites adjacent to `B` |
| same, line 416 | `φ₀` in the source `Fsrc` | `B` |
| 425–431 | `φ₀`, `pertSource`, `α₀` at `x` | `x ∈ B` |
| 433–435 | `φ₀` at row sites `y`; `dφ` at `y` | `φ₀` on row sites; `dφ` on `Y₁`, from `dg5'_inner` |
| `i4a_local` 585–597 | as above | `B` |
| `DecoupledBackgroundLocal` 171–200 (`hdata`, `hphi`, `hDA`) | raw data on `resDep x` | `A` |

No use needs an input outside `B ∪ RowSite` (the comparison of the correction on all of `Y₁`
is a conclusion of `dg5'_inner`, not an input). The collar input of `DataAgree.psi_collar` does
occur in the landed `local_step` (through `pertSource`); it is kept, narrowed to collar sites
adjacent to `B`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Rows

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The sites read by the rows of `H_D(α)` at the sites of `B`: the sites of `B`, and the sites `y`
with `H_D(α) x y ≠ 0` for some `x ∈ B`. -/
def RowSite (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (B : Finset (CTorus d L N₁ m₁ K)) (y : G.Ω 1) : Prop :=
  (y : CTorus d L N₁ m₁ K) ∈ B ∨
    ∃ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ B ∧ dirichletOperator G a ν α x y ≠ 0

/-- **Agreement of two data sets on the sites read.**  `α₀, f₁, δΨ` agree on `B`, `δΨ` also on
the collar sites adjacent to `B`, and `φ₀` on `RowSite`. -/
structure DataAgreeRows (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ) (N : ℕ)
    (B : Finset (CTorus d L N₁ m₁ K))
    (α₀ α₀' : G.Ω 1 → ℂ) (φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (f₁ f₁' : G.Ω 1 × Fin N → ℂ) : Prop where
  alpha : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ B → α₀ x = α₀' x
  phi : ∀ y : G.Ω 1, RowSite G a ν α₀ B y → φ₀ y = φ₀' y
  psi : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ B → δΨ x = δΨ' x
  psi_collar : ∀ y ∈ collar G,
    (∃ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ B ∧ Adj (x : CTorus d L N₁ m₁ K) y) → δΨ y = δΨ' y
  src : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ B → ∀ i, f₁ (x, i) = f₁' (x, i)

/-- Inhabitation: identical data agree on any `B`. -/
theorem dataAgreeRows_refl (B : Finset (CTorus d L N₁ m₁ K)) (α₀ : G.Ω 1 → ℂ)
    (φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ) (f₁ : G.Ω 1 × Fin N → ℂ) :
    DataAgreeRows G a ν N B α₀ α₀ φ₀ φ₀ δΨ δΨ f₁ f₁ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem pertSource_congr_rows {B : Finset (CTorus d L N₁ m₁ K)} {α₀ α₀' : G.Ω 1 → ℂ}
    {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ} {f₁ f₁' : G.Ω 1 × Fin N → ℂ}
    (hD : DataAgreeRows G a ν N B α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁') {z : G.Ω 1}
    (hz : (z : CTorus d L N₁ m₁ K) ∈ B) (i : Fin N) :
    pertSource G a δΨ f₁ (z, i) = pertSource G a δΨ' f₁' (z, i) := by
  unfold pertSource qStar boundaryTerm
  simp only [Pi.add_apply]
  rw [hD.psi z hz, hD.src z hz i]
  congr 2
  refine Finset.sum_congr rfl fun μ _ => ?_
  congr 1
  · by_cases h : (z : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∈ collar G
    · simp only [h, ↓reduceIte]
      rw [hD.psi_collar _ h ⟨z, hz, μ, Or.inl rfl⟩]
    · simp only [h, ↓reduceIte]
  · by_cases h : (z : CTorus d L N₁ m₁ K) - Pi.single μ 1 ∈ collar G
    · simp only [h, ↓reduceIte]
      rw [hD.psi_collar _ h ⟨z, hz, μ, Or.inr (by simp)⟩]
    · simp only [h, ↓reduceIte]

/-- The sites read by the rows at `S_Y` lie in `Y`. -/
theorem rowSite_subset (S : DGSetting G a ν)
    {X₁ Y : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {α₀ : G.Ω 1 → ℂ} {y : G.Ω 1} (hy : RowSite G a ν α₀ (SY G X₁ 𝒞 Y) y) :
    (y : CTorus d L N₁ m₁ K) ∈ Y := by
  classical
  rcases hy with hy | ⟨x, hx, hxy⟩
  · exact SY_subset hy
  · obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hx
    have hzZ' := Finset.mem_filter.1 hzZ
    exact hzZ'.2.2 y (row_mem_hatBox S hzZ'.1 α₀ hxz hxy)

/-- **`local_step` with agreement on the sites read** (T1). -/
theorem local_step_rows {cstar BG : ℝ} (hF : FamSpec d L cstar BG) (S : DGSetting G a ν)
    (hconn : HatConn G)
    {κ : ℝ} (hκ : 0 ≤ κ) (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams G} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : G.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : G.Ω 1 × Fin N → ℂ} {δ₀ ρ : ℝ} (hα0 : Small G α₀ δ₀) (hα0' : Small G α₀' δ₀)
    (hρ : δ₀ + ρ ≤ gamma1 d / 8)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx G, P ∉ parCubes G X₁ → extS G s P = 1 ∧ extS G s' P = 1)
    (hs0 : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → extS G s P = 0 ∧ extS G s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI G (cubeP P) Y → extS G s P = extS G s' P)
    (hD : DataAgreeRows G a ν N (SY G X₁ 𝒞 Y) α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {ξ η : G.Ω 1 → ℂ} (hξ : ∀ x, ‖ξ x‖ ≤ ρ) (hη : ∀ x, ‖η x‖ ≤ ρ)
    (hξη : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → ξ x = η x) :
    ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y →
      Smap G (decG G a ν s) (dirichletOperator G a ν α₀) ιU α₀ φ₀ (pertSource G a δΨ f₁) ξ x =
      Smap G (decG G a ν s') (dirichletOperator G a ν α₀') ιU α₀' φ₀' (pertSource G a δΨ' f₁') η x := by
  classical
  intro x hxT
  have hxY : (x : CTorus d L N₁ m₁ K) ∈ Y := SY_subset hxT
  have hd0 : 0 < d := by have := S.hd; omega
  obtain ⟨-, hunit⟩ := hF.2.2 G S hκ hM hs N
  obtain ⟨-, hunit'⟩ := hF.2.2 G S hκ hM hs' N
  have hδα : Small G (toAlpha G ξ) ρ := small_toAlpha G ξ hξ
  have hδα' : Small G (toAlpha G η) ρ := small_toAlpha G η hη
  have hA : Small G (α₀ + toAlpha G ξ) (gamma1 d / 8) := fun y =>
    ((Small.add hα0 hδα) y).trans hρ
  have hA' : Small G (α₀' + toAlpha G η) (gamma1 d / 8) := fun y =>
    ((Small.add hα0' hδα') y).trans hρ
  have hAeq : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y →
      (α₀ + toAlpha G ξ) y = (α₀' + toAlpha G η) y := by
    intro y hy
    simp only [Pi.add_apply]
    rw [hD.alpha y hy, show toAlpha G ξ y = toAlpha G η y by
      unfold toAlpha; rw [hξη y hy]]
  have hdphi : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) (toAlpha G ξ) (y, i) =
      dphi G (decG G a ν s') α₀' φ₀' (pertSource G a δΨ' f₁') (toAlpha G η) (y, i) := by
    intro y hy i
    unfold dphi
    rw [liftOp_mulVec, liftOp_mulVec]
    refine dg5'_inner S hconn hY (admPot_of_small hd0 hA) (admPot_of_small hd0 hA')
      (hunit (admPot_of_small hd0 hA)) (hunit' (admPot_of_small hd0 hA')) hs1 hs0 hag hAeq
      (f := fun b => Fsrc φ₀ (pertSource G a δΨ f₁) (toAlpha G ξ) (b, i))
      (f' := fun b => Fsrc φ₀' (pertSource G a δΨ' f₁') (toAlpha G η) (b, i)) ?_ y hy
    intro b hb
    simp only [Fsrc]
    rw [pertSource_congr_rows hD hb i, hD.phi b (Or.inl hb)]
    congr 2
    unfold toAlpha; rw [hξη b hb]
  obtain ⟨z, hzZ, hxz⟩ := Finset.mem_biUnion.1 hxT
  have hzZ' := Finset.mem_filter.1 hzZ
  unfold Smap
  rw [Nmap_explicit, Nmap_explicit]
  congr 1
  refine Nexp_congr ιU ?_ (fun i => by rw [hD.phi x (Or.inl hxT)])
    (fun i => pertSource_congr_rows hD hxT i)
    (fun i => hdphi x hxY i) (fun y hy => ?_)
  · intro y
    rw [dirichletOperator_eq_add a ν α₀, dirichletOperator_eq_add a ν α₀']
    simp only [Matrix.add_apply, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · subst hxy; simp [hD.alpha x hxT]
    · simp [hxy]
  · have hrow : RowSite G a ν α₀ (SY G X₁ 𝒞 Y) y := Or.inr ⟨x, hxT, hy⟩
    have hyY : (y : CTorus d L N₁ m₁ K) ∈ Y := rowSite_subset S hrow
    exact ⟨fun i => by rw [hD.phi y hrow], fun i => hdphi y hyY i⟩

/-- The landed `DataAgree` on `Y` implies the narrower agreement. -/
theorem dataAgreeRows_of_dataAgree (S : DGSetting G a ν)
    {X₁ Y : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}
    {α₀ α₀' : G.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : G.Ω 1 × Fin N → ℂ} (hD : DataAgree G N Y α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁') :
    DataAgreeRows G a ν N (SY G X₁ 𝒞 Y) α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁' :=
  ⟨fun x hx => hD.alpha x (SY_subset hx),
    fun y hy => hD.phi y (rowSite_subset S hy),
    fun x hx => hD.psi x (SY_subset hx),
    fun y hy ⟨x, hx, hxy⟩ => hD.psi_collar y hy ⟨x, SY_subset hx, hxy⟩,
    fun x hx => hD.src x (SY_subset hx)⟩

/-- The landed `local_step` from `local_step_rows` (T4). -/
theorem local_step_of_rows {cstar BG : ℝ} (hF : FamSpec d L cstar BG) (S : DGSetting G a ν)
    (hconn : HatConn G)
    {κ : ℝ} (hκ : 0 ≤ κ) (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams G} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : G.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : G.Ω 1 × Fin N → ℂ} {δ₀ ρ : ℝ} (hα0 : Small G α₀ δ₀) (hα0' : Small G α₀' δ₀)
    (hρ : δ₀ + ρ ≤ gamma1 d / 8)
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx G, P ∉ parCubes G X₁ → extS G s P = 1 ∧ extS G s' P = 1)
    (hs0 : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → extS G s P = 0 ∧ extS G s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI G (cubeP P) Y → extS G s P = extS G s' P)
    (hD : DataAgree G N Y α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {ξ η : G.Ω 1 → ℂ} (hξ : ∀ x, ‖ξ x‖ ≤ ρ) (hη : ∀ x, ‖η x‖ ≤ ρ)
    (hξη : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → ξ x = η x) :
    ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y →
      Smap G (decG G a ν s) (dirichletOperator G a ν α₀) ιU α₀ φ₀ (pertSource G a δΨ f₁) ξ x =
      Smap G (decG G a ν s') (dirichletOperator G a ν α₀') ιU α₀' φ₀' (pertSource G a δΨ' f₁') η x :=
  local_step_rows hF S hconn hκ hM hs hs' hα0 hα0' hρ hY hs1 hs0 hag
    (dataAgreeRows_of_dataAgree S hD) hξ hη hξη

/-- **`i4a_local` with agreement on the sites read** (T2): the paired Picard iteration with
`local_step_rows`. -/
theorem i4a_local_rows {cstar BG : ℝ} (hF : FamSpec d L cstar BG) (S : DGSetting G a ν)
    (hconn : HatConn G) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams G} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : G.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (H : DecHyp G a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) (H' : DecHyp G a ν ιU α₀' φ₀' δΨ' f₁' δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx G, P ∉ parCubes G X₁ → extS G s P = 1 ∧ extS G s' P = 1)
    (hs0 : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → extS G s P = 0 ∧ extS G s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI G (cubeP P) Y → extS G s P = extS G s' P)
    (hD : DataAgreeRows G a ν N (SY G X₁ 𝒞 Y) α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {δα δα' : G.Ω 1 → ℂ}
    (hfix : DecFixed G a ν s ιU α₀ φ₀ (pertSource G a δΨ f₁) δα)
    (hsm : Small G δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed G a ν s' ιU α₀' φ₀' (pertSource G a δΨ' f₁') δα')
    (hsm' : Small G δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → δα x = δα' x) ∧
    (∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα (y, i) =
      dphi G (decG G a ν s') α₀' φ₀' (pertSource G a δΨ' f₁') δα' (y, i)) := by
  classical
  have hBG := hF.2.1
  have hd0 : 0 < d := by have := S.hd; omega
  set B : ℝ := famConst d L BG κ with hB
  set Γ : ℝ := gamma1 d / 8 with hΓdef
  have hB0 : 0 ≤ B := by have := famConst_ge_one (L := L) hBG κ hd0; linarith
  have hΓ : 0 < Γ := by have := gamma1_pos hd0; positivity
  have hC := coreHyp'_small (d := d) (L := L) (N := N) hB0 hΓ H.δ₀_nn H.δ₁_nn hδ₀ hδ₁
  obtain ⟨⟨hfam, -⟩, hunit⟩ := hF.2.2 G S hκ hM hs N
  obtain ⟨⟨hfam', -⟩, hunit'⟩ := hF.2.2 G S hκ hM hs' N
  obtain ⟨ξ, hξB, hξfix, hξuniq, hit⟩ := smap_fixed_iterates hfam H.setup hC
  obtain ⟨ξ', hξB', hξfix', hξuniq', hit'⟩ := smap_fixed_iterates hfam' H'.setup hC
  -- identify `toAlpha ξ` with `δα`
  have hid : ∀ {s₀ : DecParams G} {α₀₀ : G.Ω 1 → ℂ} {φ₀₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}
      {Fs₀ : G.Ω 1 × Fin N → ℂ} {ξ₀ δα₀ : G.Ω 1 → ℂ},
      Smap G (decG G a ν s₀) (dirichletOperator G a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀ ξ₀ = ξ₀ →
      ξ₀ ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) (c6' d L N B Γ) →
      (∀ ξ' ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) (c6' d L N B Γ),
        Smap G (decG G a ν s₀) (dirichletOperator G a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀ ξ' = ξ' → ξ' = ξ₀) →
      DecFixed G a ν s₀ ιU α₀₀ φ₀₀ Fs₀ δα₀ → Small G δα₀ (c6' d L N B Γ) →
      toAlpha G ξ₀ = δα₀ := by
    intro s₀ α₀₀ φ₀₀ Fs₀ ξ₀ δα₀ _ _ huniq hf hsm₀
    have hm : ofAlpha G δα₀ ∈ Metric.closedBall (0 : G.Ω 1 → ℂ) (c6' d L N B Γ) := by
      rw [mem_closedBall_zero_iff]
      refine (pi_norm_le_iff_of_nonneg (c6'_pos (d := d) (L := L) (N := N) hB0 hΓ).le).2
        fun x => ?_
      rw [norm_ofAlpha]; exact hsm₀ x
    have hf' : Smap G (decG G a ν s₀) (dirichletOperator G a ν α₀₀) ιU α₀₀ φ₀₀ Fs₀
        (ofAlpha G δα₀) = ofAlpha G δα₀ := by
      funext x
      unfold Smap
      rw [toAlpha_ofAlpha]
      have := congrFun hf x
      unfold DecFixed at hf
      rw [hf]
      rfl
    rw [← huniq _ hm hf', toAlpha_ofAlpha]
  have e1 : toAlpha G ξ = δα := hid hξfix hξB hξuniq hfix hsm
  have e2 : toAlpha G ξ' = δα' := hid hξfix' hξB' hξuniq' hfix' hsm'
  have hpoly : ∀ {α₀₀ : G.Ω 1 → ℂ}, Small G α₀₀ δ₀ → δ₀ + c6' d L N B Γ ≤ Γ := by
    intro _ _; linarith [hC.poly, hC.ρ_nn]
  -- the pair induction
  have hagreeξ : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → ξ x = ξ' x := by
    refine fixed_agree_of_step (T := fun x : G.Ω 1 => (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y)
      (fun u v hu hv huv i hi => ?_) (fun n => ⟨(hit n).1, (hit n).2⟩)
      (fun n => ⟨(hit' n).1, (hit' n).2⟩) hC.ρ_nn
    exact local_step_rows hF S hconn hκ hM hs hs' H.alpha0 H'.alpha0 (hpoly H.alpha0)
      hY hs1 hs0 hag hD hu hv huv i hi
  have hδ : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → δα x = δα' x := by
    intro x hx
    rw [← e1, ← e2]
    unfold toAlpha
    rw [hagreeξ x hx]
  refine ⟨hδ, fun y hy i => ?_⟩
  have hA : Small G (α₀ + δα) Γ := fun z => ((Small.add H.alpha0 hsm) z).trans (hpoly H.alpha0)
  have hA' : Small G (α₀' + δα') Γ := fun z =>
    ((Small.add H'.alpha0 hsm') z).trans (hpoly H'.alpha0)
  unfold dphi
  rw [liftOp_mulVec, liftOp_mulVec]
  refine dg5'_inner S hconn hY (admPot_of_small hd0 hA) (admPot_of_small hd0 hA')
    (hunit (admPot_of_small hd0 hA)) (hunit' (admPot_of_small hd0 hA')) hs1 hs0 hag
    (fun z hz => ?_) (f := fun b => Fsrc φ₀ (pertSource G a δΨ f₁) δα (b, i))
    (f' := fun b => Fsrc φ₀' (pertSource G a δΨ' f₁') δα' (b, i)) (fun b hb => ?_) y hy
  · simp only [Pi.add_apply]
    rw [hD.alpha z hz, hδ z hz]
  · simp only [Fsrc]
    rw [pertSource_congr_rows hD hb i, hD.phi b (Or.inl hb), hδ b hb]

/-- The landed `i4a_local` from `i4a_local_rows` (T4). -/
theorem i4a_local_of_rows {cstar BG : ℝ} (hF : FamSpec d L cstar BG) (S : DGSetting G a ν)
    (hconn : HatConn G) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {s s' : DecParams G} (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
    {ιU : Bool} {α₀ α₀' : G.Ω 1 → ℂ} {φ₀ φ₀' δΨ δΨ' : CTorus d L N₁ m₁ K → Fin N → ℂ}
    {f₁ f₁' : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}
    (H : DecHyp G a ν ιU α₀ φ₀ δΨ f₁ δ₀ δ₁) (H' : DecHyp G a ν ιU α₀' φ₀' δΨ' f₁' δ₀ δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG κ) (gamma1 d / 8))
    {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)} {X₁ Y : Finset (CTorus d L N₁ m₁ K)}
    (hY : IsNnComp ((Vset X₁ 𝒞).filter fun x => x ∈ G.Ω 1) Y)
    (hs1 : ∀ P ∈ cubeIdx G, P ∉ parCubes G X₁ → extS G s P = 1 ∧ extS G s' P = 1)
    (hs0 : ∀ P ∈ parCubes G X₁, P ∉ 𝒞 → extS G s P = 0 ∧ extS G s' P = 0)
    (hag : ∀ P ∈ 𝒞, SubI G (cubeP P) Y → extS G s P = extS G s' P)
    (hD : DataAgree G N Y α₀ α₀' φ₀ φ₀' δΨ δΨ' f₁ f₁')
    {δα δα' : G.Ω 1 → ℂ}
    (hfix : DecFixed G a ν s ιU α₀ φ₀ (pertSource G a δΨ f₁) δα)
    (hsm : Small G δα (c6' d L N (famConst d L BG κ) (gamma1 d / 8)))
    (hfix' : DecFixed G a ν s' ιU α₀' φ₀' (pertSource G a δΨ' f₁') δα')
    (hsm' : Small G δα' (c6' d L N (famConst d L BG κ) (gamma1 d / 8))) :
    (∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ SY G X₁ 𝒞 Y → δα x = δα' x) ∧
    (∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ Y → ∀ i : Fin N,
      dphi G (decG G a ν s) α₀ φ₀ (pertSource G a δΨ f₁) δα (y, i) =
      dphi G (decG G a ν s') α₀' φ₀' (pertSource G a δΨ' f₁') δα' (y, i)) :=
  i4a_local_rows hF S hconn hκ hM hs hs' H H' hδ₀ hδ₁ hY hs1 hs0 hag
    (dataAgreeRows_of_dataAgree S hD) hfix hsm hfix' hsm'

end Rows

end Balaban.Localization
