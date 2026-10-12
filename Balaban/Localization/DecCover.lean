/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled

/-!
# The decoupling cover as data, separated from the operator generating set (VMOD.md §3.2)

The landed decoupled layer builds the cover (`cubeIdx G`, `chi G`, `Qset G`, `sProd G`) and the
operator (`cutOperator G`, `G.Ω 1`, `G.spacing`) from the same generating set `G`.  The
fluctuation part of I-5 needs the cover of `𝔹_{k+1}` with the operator of `𝔹_k`.

`DecCover d L N₁ m₁ K` is the cover as data on the fine torus `CTorus d L N₁ m₁ K`: the index set of
centres `cubeIdx` and the partition functions `chi`.  The interaction, thickened and core boxes
(`intBox`, `hatBox`, `coreBox`) and the cubes `cubeP` are functions of the centre only.  The sets
`Qset`, `sProd` are derived from `cubeIdx`.  The properties of the cover (and of the
pair of the cover with an operator) are the fields of `CoverCompatible`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

open Classical in
/-- `𝒬(z)` computed from an index set of centres: the centres meeting the thickened interaction
cube `□̂_z`. -/
noncomputable def qsetOf (I : Finset (ℕ × CTorus d L N₁ m₁ K)) (q : ℕ × CTorus d L N₁ m₁ K) :
    Finset (ℕ × CTorus d L N₁ m₁ K) :=
  I.filter (fun q' => ∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
    InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y)

theorem mem_qsetOf {I : Finset (ℕ × CTorus d L N₁ m₁ K)} {q q' : ℕ × CTorus d L N₁ m₁ K} :
    q' ∈ qsetOf I q ↔ q' ∈ I ∧ ∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
      InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y := by
  classical
  simp [qsetOf]

variable (d L N₁ m₁ K) in
/-- **The decoupling cover as data.** -/
structure DecCover where
  /-- The centres `z = (j, y₀)` of the cover. -/
  cubeIdx : Finset (ℕ × CTorus d L N₁ m₁ K)
  /-- The partition functions `χ_z`. -/
  chi : ℕ × CTorus d L N₁ m₁ K → CTorus d L N₁ m₁ K → ℝ

namespace DecCover

variable (C : DecCover d L N₁ m₁ K)

/-- `𝒬(z)`. -/
noncomputable def Qset (q : ℕ × CTorus d L N₁ m₁ K) : Finset (ℕ × CTorus d L N₁ m₁ K) :=
  qsetOf C.cubeIdx q

theorem mem_Qset {q q' : ℕ × CTorus d L N₁ m₁ K} :
    q' ∈ C.Qset q ↔ q' ∈ C.cubeIdx ∧ ∃ y, SameCell (L ^ (q'.1 + m₁)) y q'.2 ∧
      InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y := mem_qsetOf

/-- The decoupling factor `s_z = ∏_{P ∈ 𝒬(z)} s_P`. -/
noncomputable def sProd (s : ℕ × CTorus d L N₁ m₁ K → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) : ℂ :=
  ∏ P ∈ C.Qset q, s P

/-- The scalar field `χ_z` as a field of `ℂ ^ 1`. -/
noncomputable def chiField (q : ℕ × CTorus d L N₁ m₁ K) (x : CTorus d L N₁ m₁ K) : Fin 1 → ℂ :=
  fun _ => ((C.chi q x : ℝ) : ℂ)

theorem sProd_one (q : ℕ × CTorus d L N₁ m₁ K) : C.sProd (fun _ => (1 : ℂ)) q = 1 := by
  simp [sProd]

/-- `|s_z| ≤ e^{N₀ κ₁}` if every `|s_P| ≤ e^{κ₁}` and `|𝒬(z)| ≤ N₀`. -/
theorem norm_sProd_le {q : ℕ × CTorus d L N₁ m₁ K} (hcard : (C.Qset q).card ≤ N0 d L)
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {κ : ℝ} (hκ : 0 ≤ κ) (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) :
    ‖C.sProd s q‖ ≤ Real.exp (N0 d L * κ) := by
  unfold sProd
  rw [norm_prod]
  calc ∏ P ∈ C.Qset q, ‖s P‖ ≤ ∏ _P ∈ C.Qset q, Real.exp κ :=
        Finset.prod_le_prod₀ (fun P _ => norm_nonneg _) fun P _ => hs P
    _ = Real.exp κ ^ (C.Qset q).card := Finset.prod_const _
    _ = Real.exp ((C.Qset q).card * κ) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (N0 d L * κ) := by
        apply Real.exp_le_exp.2
        have h2 : ((C.Qset q).card : ℝ) ≤ (N0 d L : ℝ) := by exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right h2 hκ

end DecCover

/-- **The landed cover of a generating set**, the instance `C = H`. -/
noncomputable def coverOf {ϱ : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) : DecCover d L N₁ m₁ K where
  cubeIdx := cubeIdx G
  chi := chi G

end Balaban.Localization
