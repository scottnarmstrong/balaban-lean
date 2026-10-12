/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.GraphGmExponent
public import Balaban.Fluctuation.SizeModCore
public import Balaban.Multiscale.GeneratingSet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The ledger counterexample (VMOD-19 (1.1), VMOD-21 §4 row 4)

P6 p. 34: in the large-field step each new term carries a set `C` of derivative parameters, whose
layer cells `cellOfCube P` form its *ledger*.  `VMOD-18.md` (3.7) proposed to sum
`e^{-η |C|}` over all `C` with the same old source and the same active output support, with a
constant `H e^{q Δ_X}` independent of the ledger.  `VMOD-19.md` (1.1) refutes this.

* `SNAGGridRecord`: the abstract SN-AG-GRID witness record of `VMOD-18.md` §2, each field citing
  the sentence of §2 it transcribes (`SNAGGridRecord_nonempty`: it is inhabited).
* `FiberEstimate`: the proposed fiber bound (3.7) for a given constant `H`.
* `site_record_counterexample`: for `J ≤ K` a family of `J` singleton derivative families with the
  same old source (zero cost), the same active support, pairwise distinct ledgers, and fiber sum
  exactly `J e^{-η}`.
* `no_uniform_fiber_constant`: no constant `H` independent of the horizon bounds the fiber.
* `singleton_fiber_bound`, `singleton_fiber_landed_bound`: for a fixed ledger the fiber is one
  term and the landed `boundary_gm3_fixed_Y_rate` is not contradicted.
* `layer_cube_index_clash`: the actual-cover side remark.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Fluctuation Balaban.Multiscale Finset

section Record

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- Two site sets Moore-touch: some site of one is within sup-distance `1` of a site of the
other (`Near 1 1`; overlapping sets touch). -/
def MooreTouch (S S' : Set (CTorus d L N₁ m₁ K)) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S', Near 1 1 x y

/-- The top `π_K` cell of the parameter `P`: the cell of side `a_K` containing `P`
(`VMOD-18` §2 AG: "each inside its top `π_K` cell"). -/
def topCell (m₀ : ℕ) (P : ℕ × CTorus d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) :=
  box (cbase (cellSide L m₀ m₁ K) P.2) (cellSide L m₀ m₁ K)

/-- The union `B` of the new `π'_K` cubes with bases `ℬ`. -/
def newCubes (m₀ : ℕ) (ℬ : Finset (CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  ⋃ b ∈ ℬ, box b (L * cellSide L m₀ m₁ K)

/-- The central overlapping cube `Q(P) = box (b(P) - a (1,…,1)) (L a)` of `VMOD-18` (2.2). -/
def centralCube (m₀ : ℕ) (P : ℕ × CTorus d L N₁ m₁ K) : Set (CTorus d L N₁ m₁ K) :=
  box (cbase (cellSide L m₀ m₁ K) P.2 -
    fun _ => ((cellSide L m₀ m₁ K : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K))) (L * cellSide L m₀ m₁ K)

/-- The active output support `S_C = (X ∪ B ∪ ⋃_{P∈C} Q(P)) ∩ Ω` of `VMOD-18` (2.3). -/
def activeSupport (m₀ : ℕ) (Ω X : Set (CTorus d L N₁ m₁ K)) (ℬ : Finset (CTorus d L N₁ m₁ K))
    (C : Finset (ℕ × CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K) :=
  (X ∪ newCubes m₀ ℬ ∪ ⋃ P ∈ C, centralCube m₀ P) ∩ Ω

/-- **The SN-AG-GRID witness record** of `VMOD-18.md` §2 (the finite record quantified over by
Theorem 2.1 and by the proposed fiber bound (3.7)), for the old source `X` with the fixed old
minimizing pair `(𝒦, W, E)`, the new cubes `ℬ`, the action anchor `A₀` and the derivative family
`C`. -/
structure SNAGGridRecord (m₀ k : ℕ) (Ω X 𝒦 : Set (CTorus d L N₁ m₁ K))
    (W : Finset (CTorus d L N₁ m₁ K))
    (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K))
    (ℬ : Finset (CTorus d L N₁ m₁ K)) (A₀ : Set (CTorus d L N₁ m₁ K))
    (C : Finset (ℕ × CTorus d L N₁ m₁ K)) : Prop where
  /-- typing: `K = k + 1`. -/
  scale : k + 1 = K
  /-- SN: "`X ∩ Ω ≠ ∅`". -/
  source_meets : (X ∩ Ω).Nonempty
  /-- SN: "fix one minimizing old chosen cover and tree" (the old pair is admissible ...). -/
  old_admissible : ModAdmissible m₀ k Ω X 𝒦 W E
  /-- ... and realizes `Δ_X = d^cov_k (X mod Ω^c)`. -/
  old_minimizing : bondCost (scaleW L m₀ m₁ k) E = dcovMod m₀ k Ω X
  /-- SN: "a finite set `ℬ` of new `π'_K` cubes" (bases aligned to the `π_K` grid). -/
  cubes_aligned : ∀ b ∈ ℬ, Aligned (cellSide L m₀ m₁ K) b
  /-- SN: "with `X ∩ Ω ⊂ B`", `B` the union of `ℬ`. -/
  source_in_union : X ∩ Ω ⊆ newCubes m₀ ℬ
  /-- SN: "every member of `ℬ` meeting `X`". -/
  cube_meets_source : ∀ b ∈ ℬ, (X ∩ box b (L * cellSide L m₀ m₁ K)).Nonempty
  /-- SN: "containing an old chosen cover cube". -/
  cube_contains_old : ∀ b ∈ ℬ, ∃ c ∈ 𝒦,
    box c (L * cellSide L m₀ m₁ k) ⊆ box b (L * cellSide L m₀ m₁ K)
  /-- SN: "being met by the old tree". -/
  cube_met_by_tree : ∀ b ∈ ℬ, ∃ x ∈ W, x ∈ box b (L * cellSide L m₀ m₁ K)
  /-- AG: "a nonempty action anchor `A₀ ⊂ B`". -/
  anchor_nonempty : A₀.Nonempty
  anchor_sub : A₀ ⊆ newCubes m₀ ℬ
  /-- AG: the parameters are aligned derivative indices of layer `≤ K`. -/
  layer_le : ∀ P ∈ C, P.1 ≤ K
  base_aligned : ∀ P ∈ C, CubeBase (K := K) m₁ P.1 P.2
  /-- AG: "aligned parameter patches `Pset(P)`, each inside its top `π_K` cell". -/
  patch_in_top : ∀ P ∈ C, Pset m₁ P ⊆ topCell m₀ P
  /-- AG: "whose Moore-incidence graph is a forest rooted at `A₀`.  A root patch Moore-touches
  `A₀`; a nonroot patch Moore-touches its parent." (parent map with a decreasing rank, so it is
  acyclic). -/
  forest : ∃ (parent : ℕ × CTorus d L N₁ m₁ K → Option (ℕ × CTorus d L N₁ m₁ K))
      (rank : ℕ × CTorus d L N₁ m₁ K → ℕ),
    (∀ P ∈ C, ∀ Q, parent P = some Q → Q ∈ C ∧ rank Q < rank P ∧
      MooreTouch (Pset m₁ Q) (Pset m₁ P)) ∧
    (∀ P ∈ C, parent P = none → MooreTouch A₀ (Pset m₁ P))
  /-- GRID: "`L ≥ 3`". -/
  three_le : 3 ≤ L
  /-- GRID: "aligned top cells exist on the torus, and `Ω` is their union". -/
  grid : ∃ 𝒯 : Set (CTorus d L N₁ m₁ K), 𝒯.Nonempty ∧
    (∀ b ∈ 𝒯, Aligned (cellSide L m₀ m₁ K) b) ∧ Ω = ⋃ b ∈ 𝒯, box b (cellSide L m₀ m₁ K)

/-- The proposed fiber bound `VMOD-18.md` (3.7) with constant `H`: for every record family with
common source and common active support, `∑ e^{-η|C|} ≤ H e^{q Δ_X}`, `Δ_X = dcovMod`. -/
def FiberEstimate (d L N₁ m₁ K : ℕ) [NeZero N₁] [NeZero L] (m₀ k : ℕ) (η q H : ℝ) : Prop :=
  ∀ (Ω X 𝒦 : Set (CTorus d L N₁ m₁ K)) (W : Finset (CTorus d L N₁ m₁ K))
    (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)) (ℬ : Finset (CTorus d L N₁ m₁ K))
    (A₀ : Set (CTorus d L N₁ m₁ K)) (𝔉 : Finset (Finset (ℕ × CTorus d L N₁ m₁ K))),
    (∀ C ∈ 𝔉, SNAGGridRecord m₀ k Ω X 𝒦 W E ℬ A₀ C) →
    (∀ C ∈ 𝔉, ∀ C' ∈ 𝔉, activeSupport m₀ Ω X ℬ C = activeSupport m₀ Ω X ℬ C') →
    ∑ C ∈ 𝔉, Real.exp (-η * C.card) ≤ H * Real.exp (q * dcovMod m₀ k Ω X)

/-! ### The single-cell data -/

/-- The old source: one old `π'_k` cube at the origin. -/
def cellSource (m₀ k : ℕ) : Set (CTorus d L N₁ m₁ K) := box 0 (L * cellSide L m₀ m₁ k)

omit [NeZero N₁] [NeZero L] in
lemma cellSide_succ (m₀ k : ℕ) : cellSide L m₀ m₁ (k + 1) = L * cellSide L m₀ m₁ k := by
  unfold cellSide; ring

lemma cellSide_le_succ (m₀ k : ℕ) : cellSide L m₀ m₁ k ≤ cellSide L m₀ m₁ (k + 1) := by
  rw [cellSide_succ]; exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne L))

lemma mul_cellSide_pos (m₀ k : ℕ) : 0 < L * cellSide L m₀ m₁ k :=
  Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ k)

omit [NeZero N₁] in
lemma cellSource_admissible (m₀ k : ℕ) :
    ModAdmissible m₀ k (Set.univ : Set (CTorus d L N₁ m₁ K)) (cellSource m₀ k)
      {(0 : CTorus d L N₁ m₁ K)} {(0 : CTorus d L N₁ m₁ K)} ∅ := by
  have h0 : (0 : CTorus d L N₁ m₁ K) ∈ cellSource m₀ k :=
    mem_box_self _ (mul_cellSide_pos m₀ k)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact ⟨fun μ => by simp, le_rfl⟩
  · intro x hx
    simp only [Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left]
    exact hx.1
  · refine ⟨by simp, by simp, ?_⟩
    intro x hx y hy
    simp only [Finset.mem_singleton] at hx hy
    subst hx; subst hy
    exact Relation.ReflTransGen.refl
  · intro x hx
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hx
    subst hx; exact h0
  · intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    exact ⟨0, by simp, mem_box_self _ (mul_cellSide_pos m₀ k)⟩

omit [NeZero N₁] in
lemma zero_mem_cellSource (m₀ k : ℕ) : (0 : CTorus d L N₁ m₁ K) ∈ cellSource m₀ k :=
  mem_box_self _ (mul_cellSide_pos m₀ k)

omit [NeZero N₁] in
lemma dcovMod_cellSource (m₀ k : ℕ) :
    dcovMod m₀ k (Set.univ : Set (CTorus d L N₁ m₁ K)) (cellSource m₀ k) = 0 := by
  refine le_antisymm ?_ (dcovMod_nonneg _ _)
  have := dcovMod_le_of_admissible (cellSource_admissible (d := d) (L := L) (N₁ := N₁)
    (m₁ := m₁) (K := K) m₀ k)
  simpa [bondCost] using this

lemma patch_in_top_zero (m₀ : ℕ) {j : ℕ} (hj : j ≤ K) :
    Pset m₁ (j, (0 : CTorus d L N₁ m₁ K)) ⊆ topCell m₀ (j, (0 : CTorus d L N₁ m₁ K)) := by
  intro x hx
  have hdvd : L ^ (j + m₁) ∣ cellSide L m₀ m₁ K := by
    unfold cellSide; exact pow_dvd_pow L (by omega)
  have h := SameCell.mono hdvd hx
  have hb : cbase (cellSide L m₀ m₁ K) x = cbase (cellSide L m₀ m₁ K) 0 := by
    funext μ; simp only [cbase]; rw [h μ]
  unfold topCell
  simp only
  rw [← hb]
  exact mem_box_cbase (cellSide_pos m₀ m₁ K) x

/-- **T1 inhabitation.** The single-cell record of VMOD-19 §1: source `X` one old cube, new cube
`B` at the origin, anchor `{0}`, `C = {(j, 0)}`. -/
theorem singleton_record (m₀ k : ℕ) (hL : 3 ≤ L) (hK : k + 1 = K) {j : ℕ} (hj : j ≤ K) :
    SNAGGridRecord m₀ k (Set.univ : Set (CTorus d L N₁ m₁ K)) (cellSource m₀ k) {0}
      {(0 : CTorus d L N₁ m₁ K)} ∅ {(0 : CTorus d L N₁ m₁ K)} {0}
      {((j, 0) : ℕ × CTorus d L N₁ m₁ K)} := by
  have hKs : cellSide L m₀ m₁ K = L * cellSide L m₀ m₁ k := by
    subst hK; exact cellSide_succ m₀ k
  have hsub : cellSource m₀ k ⊆ newCubes m₀ ({0} : Finset (CTorus d L N₁ m₁ K)) := by
    intro x hx
    simp only [newCubes, Finset.mem_singleton, Set.iUnion_iUnion_eq_left]
    refine box_mono _ ?_ hx
    rw [hKs]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne L)))
  have hbox : box (0 : CTorus d L N₁ m₁ K) (L * cellSide L m₀ m₁ k) ⊆
      box 0 (L * cellSide L m₀ m₁ K) := by
    refine box_mono _ ?_
    rw [hKs]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne L)))
  have hKpos : 0 < L * cellSide L m₀ m₁ K := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ K)
  have h0 : (0 : CTorus d L N₁ m₁ K) ∈ newCubes m₀ ({0} : Finset (CTorus d L N₁ m₁ K)) :=
    hsub (zero_mem_cellSource m₀ k)
  refine ⟨hK, ⟨0, zero_mem_cellSource m₀ k, Set.mem_univ _⟩,
    cellSource_admissible m₀ k, ?_, ?_, (fun x hx => hsub hx.1), ?_, ?_, ?_, ⟨0, rfl⟩, ?_, ?_, ?_, ?_, ?_,
    hL, ?_⟩
  · simp [bondCost, dcovMod_cellSource]
  · intro b hb; simp only [Finset.mem_singleton] at hb; subst hb; exact fun μ => by simp
  · intro b hb
    simp only [Finset.mem_singleton] at hb; subst hb
    exact ⟨0, zero_mem_cellSource m₀ k, mem_box_self _ hKpos⟩
  · intro b hb
    simp only [Finset.mem_singleton] at hb; subst hb
    exact ⟨0, rfl, hbox⟩
  · intro b hb
    simp only [Finset.mem_singleton] at hb; subst hb
    exact ⟨0, by simp, mem_box_self _ hKpos⟩
  · intro x hx; simp only [Set.mem_singleton_iff] at hx; subst hx; exact h0
  · intro P hP; simp only [Finset.mem_singleton] at hP; subst hP; exact hj
  · intro P hP; simp only [Finset.mem_singleton] at hP; subst hP
    exact fun μ => by simp
  · intro P hP; simp only [Finset.mem_singleton] at hP; subst hP
    exact patch_in_top_zero m₀ hj
  · refine ⟨fun _ => none, fun _ => 0, ?_, ?_⟩
    · intro P _ Q hQ; simp at hQ
    · intro P hP _
      simp only [Finset.mem_singleton] at hP; subst hP
      exact ⟨0, rfl, 0, self_mem_Pset _, 0, fun _ => by simp, by funext μ; simp⟩
  · exact ⟨{b | Aligned (cellSide L m₀ m₁ K) b}, ⟨cbase _ 0, aligned_cbase _⟩, fun b hb => hb, by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      exact ⟨cbase _ x, aligned_cbase _, mem_box_cbase (cellSide_pos m₀ m₁ K) x⟩⟩

theorem SNAGGridRecord_nonempty (m₀ k : ℕ) (hL : 3 ≤ L) (hK : k + 1 = K) :
    Nonempty (SNAGGridRecord m₀ k (Set.univ : Set (CTorus d L N₁ m₁ K)) (cellSource m₀ k) {0}
      {(0 : CTorus d L N₁ m₁ K)} ∅ {(0 : CTorus d L N₁ m₁ K)} {0}
      {((1, 0) : ℕ × CTorus d L N₁ m₁ K)}) :=
  ⟨singleton_record m₀ k hL hK (by omega)⟩

/-! ### T2: the counterexample family -/

/-- The family of singleton derivative families `{(j, 0)}`, `1 ≤ j ≤ J`. -/
def ledgerFamily (J : ℕ) : Finset (Finset (ℕ × CTorus d L N₁ m₁ K)) :=
  (Finset.Icc 1 J).image fun j => {((j, 0) : ℕ × CTorus d L N₁ m₁ K)}

omit [NeZero N₁] [NeZero L] in
lemma mem_ledgerFamily {J : ℕ} {C : Finset (ℕ × CTorus d L N₁ m₁ K)} :
    C ∈ ledgerFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) J ↔
      ∃ j, 1 ≤ j ∧ j ≤ J ∧ C = {((j, 0) : ℕ × CTorus d L N₁ m₁ K)} := by
  simp [ledgerFamily, and_assoc, eq_comm]

omit [NeZero N₁] [NeZero L] in
lemma card_ledgerFamily (J : ℕ) :
    (ledgerFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) J).card = J := by
  unfold ledgerFamily
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  simp

omit [NeZero N₁] [NeZero L] in
lemma sum_ledgerFamily (J : ℕ) (η : ℝ) :
    ∑ C ∈ ledgerFamily (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) J,
      Real.exp (-η * C.card) = J * Real.exp (-η) := by
  unfold ledgerFamily
  rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
  simp

omit [NeZero N₁] [NeZero L] in
lemma activeSupport_singleton (m₀ : ℕ) (Ω X : Set (CTorus d L N₁ m₁ K))
    (ℬ : Finset (CTorus d L N₁ m₁ K)) (j j' : ℕ) :
    activeSupport m₀ Ω X ℬ {((j, 0) : ℕ × CTorus d L N₁ m₁ K)} =
      activeSupport m₀ Ω X ℬ {((j', 0) : ℕ × CTorus d L N₁ m₁ K)} := by
  simp [activeSupport, centralCube]

/-- **T2.  The ledger counterexample (VMOD-19 (1.1)).**  For `J ≤ K` (`K = k+1`): one old
source cube `X` with `ModAdmissible m₀ k Ω X {0} {0} ∅`, hence `Δ_X = dcovMod = 0`; a family
`𝔉` of `J` singleton derivative families, each satisfying the record `SNAGGridRecord` for the
same source, the same new cube, the same anchor, with the same active output support, pairwise
distinct ledgers `C.image (cellOfCube m₀ m₁)`, and fiber sum exactly `J e^{-η}`. -/
theorem site_record_counterexample (m₀ k J : ℕ) (hL : 3 ≤ L) (hK : k + 1 = K) (hJ : J ≤ K) :
    ∃ (X : Set (CTorus d L N₁ m₁ K)) (𝒦 : Set (CTorus d L N₁ m₁ K))
      (W : Finset (CTorus d L N₁ m₁ K))
      (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K))
      (ℬ : Finset (CTorus d L N₁ m₁ K)) (A₀ : Set (CTorus d L N₁ m₁ K))
      (𝔉 : Finset (Finset (ℕ × CTorus d L N₁ m₁ K))),
      ModAdmissible m₀ k (Set.univ : Set (CTorus d L N₁ m₁ K)) X {0} {0} ∅ ∧
      dcovMod m₀ k (Set.univ : Set (CTorus d L N₁ m₁ K)) X = 0 ∧
      𝔉.card = J ∧
      (∀ C ∈ 𝔉, (∃ j, C = {((j, 0) : ℕ × CTorus d L N₁ m₁ K)}) ∧
        SNAGGridRecord m₀ k Set.univ X 𝒦 W E ℬ A₀ C) ∧
      (∀ C ∈ 𝔉, ∀ C' ∈ 𝔉,
        activeSupport m₀ Set.univ X ℬ C = activeSupport m₀ Set.univ X ℬ C') ∧
      (∀ C ∈ 𝔉, ∀ C' ∈ 𝔉, C ≠ C' →
        C.image (cellOfCube (L := L) m₀ m₁) ≠ C'.image (cellOfCube (L := L) m₀ m₁)) ∧
      (∀ η : ℝ, ∑ C ∈ 𝔉, Real.exp (-η * C.card) = J * Real.exp (-η)) := by
  refine ⟨cellSource m₀ k, {0}, {0}, ∅, {0}, {0}, ledgerFamily J,
    cellSource_admissible m₀ k, dcovMod_cellSource m₀ k, card_ledgerFamily J, ?_, ?_, ?_,
    fun η => sum_ledgerFamily J η⟩
  · intro C hC
    obtain ⟨j, -, hj, rfl⟩ := mem_ledgerFamily.1 hC
    exact ⟨⟨j, rfl⟩, singleton_record m₀ k hL hK (by omega)⟩
  · intro C hC C' hC'
    obtain ⟨j, -, -, rfl⟩ := mem_ledgerFamily.1 hC
    obtain ⟨j', -, -, rfl⟩ := mem_ledgerFamily.1 hC'
    exact activeSupport_singleton m₀ _ _ _ j j'
  · intro C hC C' hC' hne himg
    obtain ⟨j, -, -, rfl⟩ := mem_ledgerFamily.1 hC
    obtain ⟨j', -, -, rfl⟩ := mem_ledgerFamily.1 hC'
    apply hne
    simp only [Finset.image_singleton, cellOfCube, Finset.singleton_inj, Prod.mk.injEq] at himg
    rw [himg.1]

/-- **The refutation of `VMOD-18.md` (3.7).**  For every `η`, `q`, no constant `H` (independent
of the horizon `K = k+1`) satisfies `FiberEstimate` for all `k`; here `Δ_X = 0` in the witness. -/
theorem no_uniform_fiber_constant (d L N₁ m₁ m₀ : ℕ) [NeZero N₁] [NeZero L] (hL : 3 ≤ L)
    (η q : ℝ) :
    ¬ ∃ H : ℝ, ∀ k : ℕ, FiberEstimate d L N₁ m₁ (k + 1) m₀ k η q H := by
  rintro ⟨H, hH⟩
  obtain ⟨X, 𝒦, W, E, ℬ, A₀, 𝔉, -, hΔ, -, hrec, hsupp, -, hsum⟩ :=
    site_record_counterexample (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := ⌈H * Real.exp η⌉₊ + 1)
      m₀ ⌈H * Real.exp η⌉₊ (⌈H * Real.exp η⌉₊ + 1) hL rfl le_rfl
  have h := hH (⌈H * Real.exp η⌉₊) Set.univ X 𝒦 W E ℬ A₀ 𝔉 (fun C hC => (hrec C hC).2) hsupp
  rw [hsum, hΔ] at h
  simp only [mul_zero, Real.exp_zero, mul_one] at h
  have h2 : ((⌈H * Real.exp η⌉₊ + 1 : ℕ) : ℝ) ≤ H * Real.exp η := by
    calc ((⌈H * Real.exp η⌉₊ + 1 : ℕ) : ℝ)
        = ((⌈H * Real.exp η⌉₊ + 1 : ℕ) : ℝ) * Real.exp (-η) * Real.exp η := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ H * Real.exp η := mul_le_mul_of_nonneg_right h (Real.exp_pos η).le
  have h3 := Nat.le_ceil (H * Real.exp η)
  push_cast at h2
  linarith

/-! ### T3: consistency with the landed fixed-ledger count -/

omit [NeZero N₁] [NeZero L] in
/-- For a fixed ledger the fiber is the single family `{(j,0)}` and the bound by `1` holds. -/
theorem singleton_fiber_bound (j : ℕ) {κ₂ : ℝ} (hκ : 0 ≤ κ₂) :
    ∑ C ∈ ({{((j, 0) : ℕ × CTorus d L N₁ m₁ K)}} : Finset (Finset (ℕ × CTorus d L N₁ m₁ K))),
      Real.exp (-κ₂ * C.card) ≤ 1 := by
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, mul_one]
  exact Real.exp_le_one_iff.2 (by linarith)

/-- The landed `boundary_gm3_fixed_Y_rate` applied to the one-element fiber over the ledger
`{cellOfCube (j,0)}`: the fixed-ledger count is not contradicted by `site_record_counterexample`. -/
theorem singleton_fiber_landed_bound (m₀ : ℕ) (hL1 : 1 ≤ L) (hN : L ^ m₀ ∣ N₁) {j : ℕ}
    (hj : j ≤ K) (κ₁ : ℝ) (h6 : 6 ≤ κ₁)
    (hκ : 4 * d * Real.log (((2 * L + 1 : ℕ) : ℝ) * ((L ^ m₀ : ℕ) : ℝ)) + 2 ≤ κ₁) :
    ∑ C ∈ ({{((j, 0) : ℕ × CTorus d L N₁ m₁ K)}} : Finset (Finset (ℕ × CTorus d L N₁ m₁ K))),
      Real.exp (-(κ₁ / 2 - 1) * C.card) ≤ 1 := by
  refine boundary_gm3_fixed_Y_rate hL1 hN {((j, 0) : ℕ × CTorus d L N₁ m₁ K)} ?_
    (fun P => {cellOfCube (L := L) m₀ m₁ P}) ?_ {cellOfCube (L := L) m₀ m₁ (j, 0)} ∅ _ ?_ κ₁ h6 hκ
  · intro P hP
    simp only [Finset.mem_singleton] at hP; subst hP
    exact ⟨hj, fun μ => by simp⟩
  · intro P
    simpa using Nat.one_le_pow _ _ (by omega : 0 < 2 * L + 1)
  · intro C hC
    simp only [Finset.mem_singleton] at hC; subst hC
    simp

end Record

/-! ### T4: the actual-cover side remark -/

section Cover

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **Same-point indices in different layers cannot lie in one cover's cube index set.**  A
generating set has pairwise disjoint layers (`GeneratingSet.layer_disjoint`).  This says only that
the points `P_j = (j, A₀)` of the abstract family cannot all be cube indices of one actual cover
(`Cover.mem_cubeIdx` requires `P_j` in layer `j`).  It does NOT identify the abstract `𝔉` with
`Cover.cubeIdx G`, and does not decide whether an actual P6 cover admits a fiber counterexample
(open, VMOD-21 row 4). -/
theorem layer_cube_index_clash (G : GeneratingSet d L N₀ k ϱ) {j j' : ℕ}
    (hj : 1 ≤ j) (hjk : j ≤ k) (hj' : 1 ≤ j') (hj'k : j' ≤ k) (hne : j ≠ j')
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer j) (hx' : x ∈ G.layer j') : False :=
  G.layer_disjoint hj hjk hj' hj'k hne hx hx'

end Cover

end Balaban.Localization
