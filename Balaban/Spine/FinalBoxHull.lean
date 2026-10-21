/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalBoxGas
public import Balaban.Spine.FinalRegroup
import Mathlib.Tactic.Linarith

/-!
# The fine sites of a set of cells and its hull in the scale-`(k+1)` cubes

A6-3, gas layer, the regrouping of the cell gas into Root-F's scale-`(k+1)` polymers. On the fine
torus `𝕋_ℓ`, `ℓ = M n_K L^K`, the fine sites of a set `𝒳` of macro cells are the sites of the
`k`-blocks of its cells (`fineCells`), and its hull (`cellHull`) is the union of the cubes of side
`M L^{k+1}` meeting them.

* `preimage_reflTransGen`: if the fibres of a map are connected and adjacency lifts, the preimage of a
  connected set is connected;
* `stepIn_fineCells_cell`: the fine sites of one cell are connected (the cell is a product of
  intervals, `block_connected_of_monotone`);
* `exists_stepIn_of_adj`: adjacent cells contain nearest-neighbour fine sites;
* `isPolymer_cellHull`: the hull of a connected set of cells is a polymer of side `M L^{k+1}`.
-/

@[expose] public section

open Finset Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 Balaban.Green
  Balaban.Polymer Balaban.Multiscale

namespace Balaban.RootFSpine

/-- **The preimage of a connected set is connected** when the fibres are connected and adjacency
lifts. -/
theorem preimage_reflTransGen {V W : Type*} (φ : V → W) (RV : V → V → Prop) (RW : W → W → Prop)
    (A : Set W)
    (hfib : ∀ v v', φ v = φ v' → φ v ∈ A →
      Relation.ReflTransGen (fun a b => φ a ∈ A ∧ φ b ∈ A ∧ RV a b) v v')
    (hlift : ∀ w w', w ∈ A → w' ∈ A → RW w w' →
      ∃ v v', φ v = w ∧ φ v' = w' ∧ RV v v')
    {w w' : W} (hw : Relation.ReflTransGen (fun a b => a ∈ A ∧ b ∈ A ∧ RW a b) w w') :
    ∀ v v', φ v = w → φ v' = w' → w ∈ A →
      Relation.ReflTransGen (fun a b => φ a ∈ A ∧ φ b ∈ A ∧ RV a b) v v' := by
  induction hw with
  | refl => intro v v' hv hv' hw; exact hfib v v' (hv.trans hv'.symm) (hv ▸ hw)
  | @tail b c hab hbc ih =>
    intro v v' hv hv' hw
    obtain ⟨hb, hc, hr⟩ := hbc
    obtain ⟨u, u', hu, hu', hruu⟩ := hlift b c hb hc hr
    refine (ih v u hv hu hw).trans (Relation.ReflTransGen.head
      ⟨hu ▸ hb, hu' ▸ hc, hruu⟩ (hfib u' v' (hu'.trans hv'.symm) (hu' ▸ hc)))

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- The fine torus side is the block side times the side of the torus of the `k`-blocks. -/
theorem fine_eq_blockSide {k : ℕ} (hk : k ≤ K) :
    M * n K * S.L ^ K = S.L ^ k * (M * n K * S.L ^ (K - k)) := by
  have : S.L ^ K = S.L ^ k * S.L ^ (K - k) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

theorem fineBlock_val {k : ℕ} (hk : k ≤ K) (x : Torus S.d (M * n K * S.L ^ K)) (μ : Fin S.d) :
    ((fineBlock (S := S) (n := n) (M := M) (K := K) k x) μ).val = (x μ).val / S.L ^ k := by
  unfold fineBlock jBlock
  rw [blockMap_apply, blockCoord_val (fine_eq_blockSide hk)]

/-- The cell of a fine site. -/
def fineCellOf (k Mc : ℕ) (x : Torus S.d (M * n K * S.L ^ K)) :
    MacIdx S.d (M * n K * S.L ^ (K - k)) Mc :=
  cellOf k Mc (fineBlock k x)

/-- **The fine sites of a set of cells.** -/
def fineCells (k Mc : ℕ) (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc)) :
    Finset (Torus S.d (M * n K * S.L ^ K)) :=
  Finset.univ.filter fun x => fineCellOf (S := S) (n := n) (M := M) (K := K) k Mc x ∈ 𝒳

/-- **The hull of a set of cells** in the cubes of side `M L^{k+1}` (Root-F's scale-`(k+1)` cubes). -/
def cellHull (k Mc : ℕ) (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc)) :
    Finset (Torus S.d (M * n K * S.L ^ K)) :=
  hullT (M * S.L ^ (k + 1)) (fineCells (S := S) (n := n) (M := M) (K := K) k Mc 𝒳)

/-- The coordinate function whose level sets are the fine sites of the cells. -/
def cellCoord (k Mc m : ℕ) (v : ℕ) : ℕ := min (v / S.L ^ k / Mc) (macK m Mc - 1)

omit [NeZero S.L] in
theorem monotone_cellCoord (k Mc m : ℕ) : Monotone (cellCoord (S := S) k Mc m) := fun _ _ h =>
  min_le_min_right _ (Nat.div_le_div_right (Nat.div_le_div_right h))

theorem fineCellOf_val {k : ℕ} (hk : k ≤ K) (Mc : ℕ) (x : Torus S.d (M * n K * S.L ^ K))
    (μ : Fin S.d) :
    ((fineCellOf (S := S) (n := n) (M := M) (K := K) k Mc x) μ : ℕ) =
      cellCoord (S := S) k Mc (M * n K * S.L ^ (K - k)) (x μ).val := by
  unfold fineCellOf cellOf cellCoord macZ macCell
  simp only
  rw [fineBlock_val hk]

theorem fineCellOf_eq_iff {k : ℕ} (hk : k ≤ K) (Mc : ℕ) (x : Torus S.d (M * n K * S.L ^ K))
    (z : MacIdx S.d (M * n K * S.L ^ (K - k)) Mc) :
    fineCellOf (S := S) (n := n) (M := M) (K := K) k Mc x = z ↔
      ∀ μ, cellCoord (S := S) k Mc (M * n K * S.L ^ (K - k)) (x μ).val = (z μ : ℕ) := by
  constructor
  · rintro rfl μ; exact (fineCellOf_val hk Mc x μ).symm
  · intro h; funext μ; exact Fin.ext ((fineCellOf_val hk Mc x μ).trans (h μ))

/-- **The fine sites of one cell are connected** inside the fine sites of every set of cells
containing it. -/
theorem stepIn_fineCells_of_cell {k : ℕ} (hk : k ≤ K) {Mc : ℕ}
    (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc)) {x x' : Torus S.d (M * n K * S.L ^ K)}
    (hxx : fineCellOf (S := S) (n := n) (M := M) (K := K) k Mc x =
      fineCellOf (S := S) (n := n) (M := M) (K := K) k Mc x')
    (hx : fineCellOf (S := S) (n := n) (M := M) (K := K) k Mc x ∈ 𝒳) :
    Relation.ReflTransGen (StepIn (fineCells (S := S) (n := n) (M := M) (K := K) k Mc 𝒳)) x x' := by
  set z := fineCellOf (S := S) (n := n) (M := M) (K := K) k Mc x with hz
  refine block_connected_of_monotone (cellCoord (S := S) k Mc (M * n K * S.L ^ (K - k)))
    (monotone_cellCoord _ _ _) _ (fun μ => (z μ : ℕ)) (fun y hy => ?_) _ x x' rfl
    ((fineCellOf_eq_iff hk Mc x z).1 rfl) ((fineCellOf_eq_iff hk Mc x' z).1 hxx.symm)
  rw [fineCells, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, ((fineCellOf_eq_iff hk Mc y z).2 hy).symm ▸ hx⟩

/-- The fine site with block coordinates `b` and offsets `o` inside the block. -/
def blockSite {k : ℕ} (b : BlockAt S n M K k) (o : Fin S.d → ℕ) : Torus S.d (M * n K * S.L ^ K) :=
  fun ν => (((b ν).val * S.L ^ k + o ν : ℕ) : ZMod (M * n K * S.L ^ K))

theorem fineBlock_blockSite {k : ℕ} (hk : k ≤ K) (b : BlockAt S n M K k) {o : Fin S.d → ℕ}
    (ho : ∀ ν, o ν < S.L ^ k) :
    fineBlock (S := S) (n := n) (M := M) (K := K) k (blockSite b o) = b := by
  have hL : 0 < S.L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) k
  funext ν
  apply ZMod.val_injective
  rw [fineBlock_val hk]
  have hb := ZMod.val_lt (b ν)
  have hlt : (b ν).val * S.L ^ k + o ν < M * n K * S.L ^ K := by
    rw [fine_eq_blockSide hk]
    have := ho ν
    have h2 : (b ν).val + 1 ≤ M * n K * S.L ^ (K - k) := hb
    nlinarith
  unfold blockSite
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.add_comm, Nat.add_mul_div_right _ _ hL,
    Nat.div_eq_of_lt (ho ν), zero_add]

/-- **Adjacent blocks contain nearest-neighbour fine sites** (one orientation). -/
theorem exists_fine_adj_of_add_single {k : ℕ} (hk : k ≤ K) (b : BlockAt S n M K k) (μ : Fin S.d) :
    ∃ x x' : Torus S.d (M * n K * S.L ^ K),
      fineBlock (S := S) (n := n) (M := M) (K := K) k x = b ∧
      fineBlock (S := S) (n := n) (M := M) (K := K) k x' = b + Pi.single μ 1 ∧
      x' = x + Pi.single μ 1 := by
  have hL : 0 < S.L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) k
  set o : Fin S.d → ℕ := fun ν => if ν = μ then S.L ^ k - 1 else 0 with ho
  have ho' : ∀ ν, o ν < S.L ^ k := fun ν => by simp only [ho]; split_ifs <;> omega
  have hoμ : o μ = S.L ^ k - 1 := by simp [ho]
  refine ⟨blockSite b o, blockSite b o + Pi.single μ 1, fineBlock_blockSite hk b ho', ?_, rfl⟩
  funext ν
  by_cases hν : ν = μ
  · subst hν
    unfold fineBlock jBlock
    rw [blockMap_apply]
    unfold blockCoord blockSite
    simp only [Pi.add_apply, Pi.single_eq_same]
    rw [hoμ]
    have e : (((b ν).val * S.L ^ k + (S.L ^ k - 1) : ℕ) : ZMod (M * n K * S.L ^ K)) + 1 =
        ((((b ν).val + 1) * S.L ^ k : ℕ) : ZMod (M * n K * S.L ^ K)) := by
      have : ((S.L ^ k - 1 : ℕ) : ZMod (M * n K * S.L ^ K)) = ((S.L ^ k : ℕ) : ZMod _) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      push_cast
      rw [this]; push_cast; ring
    rw [e, ZMod.val_natCast, fine_eq_blockSide hk, Nat.mul_comm (S.L ^ k)
      (M * n K * S.L ^ (K - k)), Nat.mul_mod_mul_right, Nat.mul_div_cancel _ hL, ZMod.natCast_mod]
    push_cast
    rw [ZMod.natCast_zmod_val]
  · have e1 : (blockSite b o + Pi.single μ 1 : Torus S.d (M * n K * S.L ^ K)) ν =
        blockSite b o ν := by
      simp [Pi.single_eq_of_ne hν]
    have e2 : (b + Pi.single μ 1 : BlockAt S n M K k) ν = b ν := by simp [Pi.single_eq_of_ne hν]
    rw [e2]
    have := congrFun (fineBlock_blockSite (S := S) (n := n) (M := M) (K := K) hk b ho') ν
    unfold fineBlock jBlock at this ⊢
    rw [blockMap_apply] at this ⊢
    rw [e1]
    exact this

/-- **Adjacent blocks contain nearest-neighbour fine sites.** -/
theorem exists_fine_adj_of_adj {k : ℕ} (hk : k ≤ K) {b b' : BlockAt S n M K k}
    (h : (blockGraph S.d (M * n K * S.L ^ (K - k))).Adj b b') :
    ∃ x x' : Torus S.d (M * n K * S.L ^ K),
      fineBlock (S := S) (n := n) (M := M) (K := K) k x = b ∧
      fineBlock (S := S) (n := n) (M := M) (K := K) k x' = b' ∧
      ∃ μ : Fin S.d, x' = x + Pi.single μ 1 ∨ x = x' + Pi.single μ 1 := by
  obtain ⟨-, μ, hμ | hμ⟩ := h
  · obtain ⟨x, x', hx, hx', he⟩ := exists_fine_adj_of_add_single (S := S) (n := n) (M := M)
      (K := K) hk b μ
    exact ⟨x, x', hx, hμ ▸ hx', μ, Or.inl he⟩
  · obtain ⟨x', x, hx', hx, he⟩ := exists_fine_adj_of_add_single (S := S) (n := n) (M := M)
      (K := K) hk b' μ
    exact ⟨x, x', hμ ▸ hx, hx', μ, Or.inr he⟩

/-- **Adjacent cells contain nearest-neighbour fine sites.** -/
theorem exists_fine_adj_of_cell_adj {k : ℕ} (hk : k ≤ K) {Mc : ℕ}
    {z z' : MacIdx S.d (M * n K * S.L ^ (K - k)) Mc} (h : (macCellGraph Mc).Adj z z') :
    ∃ x x' : Torus S.d (M * n K * S.L ^ K),
      fineCellOf (S := S) (n := n) (M := M) (K := K) k Mc x = z ∧
      fineCellOf (S := S) (n := n) (M := M) (K := K) k Mc x' = z' ∧
      ∃ μ : Fin S.d, x' = x + Pi.single μ 1 ∨ x = x' + Pi.single μ 1 := by
  rw [macCellGraph, SimpleGraph.fromRel_adj] at h
  rcases h.2 with ⟨b, b', hbb, hb, hb'⟩ | ⟨b, b', hbb, hb, hb'⟩
  · obtain ⟨x, x', hx, hx', hμ⟩ := exists_fine_adj_of_adj (S := S) (n := n) (M := M) (K := K)
      hk hbb
    exact ⟨x, x', by rw [fineCellOf, hx]; exact hb, by rw [fineCellOf, hx']; exact hb', hμ⟩
  · obtain ⟨x, x', hx, hx', μ, hμ⟩ := exists_fine_adj_of_adj (S := S) (n := n) (M := M) (K := K)
      hk hbb
    exact ⟨x', x, by rw [fineCellOf, hx']; exact hb', by rw [fineCellOf, hx]; exact hb, μ,
      hμ.symm⟩

/-- **The fine sites of a connected set of cells are connected** (a polymer of side `1`). -/
theorem isPolymer_fineCells {k : ℕ} (hk : k ≤ K) {Mc : ℕ}
    {𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc)} (h𝒳 : IsAnimal (macCellGraph Mc) 𝒳) :
    IsPolymer S.d (M * n K * S.L ^ K) 1 (fineCells (S := S) (n := n) (M := M) (K := K) k Mc 𝒳) := by
  rw [isAnimal_iff] at h𝒳
  obtain ⟨⟨z, hz⟩, hconn⟩ := h𝒳
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := macCore_nonempty (d := S.d) (m := M * n K * S.L ^ (K - k)) (M := Mc) z
    have hbz : cellOf (S := S) (n := n) (M := M) (K := K) k Mc b = z :=
      (eq_macZ_of_mem_macCore hb).symm
    have hL : 0 < S.L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) k
    refine ⟨blockSite b (fun _ => 0), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
    rw [fineCellOf, fineBlock_blockSite hk b (fun _ => hL), hbz]
    exact hz
  · intro x hx y hxy
    have : x = y := funext fun μ => ZMod.val_injective _ (by simpa using hxy μ)
    exact this ▸ hx
  · intro x hx y hy
    have hx' := (Finset.mem_filter.1 hx).2
    have hy' := (Finset.mem_filter.1 hy).2
    have := preimage_reflTransGen (fineCellOf (S := S) (n := n) (M := M) (K := K) k Mc)
      (fun a b => ∃ μ : Fin S.d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
      (macCellGraph Mc).Adj (𝒳 : Set _)
      (fun v v' hvv hv => by
        have h1 := stepIn_fineCells_of_cell hk 𝒳 hvv hv
        refine Relation.ReflTransGen.mono (fun a b hab => ?_) _ _ h1
        exact ⟨(Finset.mem_filter.1 hab.1).2, (Finset.mem_filter.1 hab.2.1).2, hab.2.2⟩)
      (fun w w' _ _ hww => exists_fine_adj_of_cell_adj hk hww)
      (hconn _ hx' _ hy') x y rfl rfl hx'
    refine Relation.ReflTransGen.mono (fun a b hab => ?_) _ _ this
    exact ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hab.1⟩,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hab.2.1⟩, hab.2.2⟩

/-- **The hull of a connected set of cells is a polymer of side `M L^{k+1}`.** -/
theorem isPolymer_cellHull {k : ℕ} (hk : k ≤ K) {Mc : ℕ}
    {𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc)} (h𝒳 : IsAnimal (macCellGraph Mc) 𝒳) :
    IsPolymer S.d (M * n K * S.L ^ K) (M * S.L ^ (k + 1))
      (cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳) :=
  hullT_isPolymer (isPolymer_fineCells hk h𝒳)

/-! ### Counting cubes and cells -/

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- The fine torus side is the cube side times the side of the torus of the cubes. -/
theorem fine_eq_cubeSide {k : ℕ} (hk : k + 1 ≤ K) :
    M * n K * S.L ^ K = M * S.L ^ (k + 1) * (n K * S.L ^ (K - (k + 1))) := by
  have : S.L ^ K = S.L ^ (k + 1) * S.L ^ (K - (k + 1)) := by rw [← pow_add]; congr 1; omega
  rw [this]; ring

/-- The scale-`(k+1)` cube of a fine site. -/
def cubeOf (k : ℕ) (x : Torus S.d (M * n K * S.L ^ K)) : Torus S.d (n K * S.L ^ (K - (k + 1))) :=
  blockMap (M * S.L ^ (k + 1)) (n K * S.L ^ (K - (k + 1))) x

/-- The hull has the cubes of the set. -/
theorem image_cubeOf_hullT (k : ℕ) (hk : k + 1 ≤ K) (Y : Finset (Torus S.d (M * n K * S.L ^ K))) :
    (hullT (M * S.L ^ (k + 1)) Y).image (cubeOf (S := S) (n := n) (M := M) (K := K) k) =
      Y.image (cubeOf (S := S) (n := n) (M := M) (K := K) k) := by
  ext c
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := mem_hullT.1 hx
    exact ⟨y, hy, ((cell_eq_iff (fine_eq_cubeSide hk)).2 hxy).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, subset_hullT _ Y hy, rfl⟩

/-- A cell meets at most `3^d` cubes of side `M L^{k+1}` when `M_c ≤ M L`. -/
theorem card_image_cubeOf_cell_le {k : ℕ} (hk : k + 1 ≤ K) {Mc : ℕ} (hMc : 0 < Mc)
    (hMcL : Mc ≤ M * S.L) (z : MacIdx S.d (M * n K * S.L ^ (K - k)) Mc) :
    ((fineCells (S := S) (n := n) (M := M) (K := K) k Mc {z}).image
      (cubeOf (S := S) (n := n) (M := M) (K := K) k)).card ≤ 3 ^ S.d := by
  have hk' : k ≤ K := by omega
  set s' := M * S.L ^ (k + 1) with hs'
  have hLk : 0 < S.L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) k
  have hs'pos : 0 < s' := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne M))
    (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _)
  have hcube : Mc * S.L ^ k ≤ s' := by
    rw [hs', pow_succ]; nlinarith
  set A : Fin S.d → ℕ := fun μ => (z μ : ℕ) * Mc * S.L ^ k / s' with hA
  have hsub : (fineCells (S := S) (n := n) (M := M) (K := K) k Mc {z}).image
      (cubeOf (S := S) (n := n) (M := M) (K := K) k) ⊆
      Fintype.piFinset fun μ => (Finset.range 3).image
        fun t => ((A μ + t : ℕ) : ZMod (n K * S.L ^ (K - (k + 1)))) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    have hxz : fineCellOf (S := S) (n := n) (M := M) (K := K) k Mc x = z := by
      simpa [fineCells] using hx
    rw [Fintype.mem_piFinset]
    intro μ
    rw [Finset.mem_image]
    set v := (x μ).val with hv
    set u := v / S.L ^ k with hu
    have hbounds : (z μ : ℕ) * Mc ≤ u ∧ u < (z μ : ℕ) * Mc + 2 * Mc := by
      have hcell : macCell (M * n K * S.L ^ (K - k)) Mc
          ((fineBlock (S := S) (n := n) (M := M) (K := K) k x) μ) = z μ := by
        rw [← hxz]; rfl
      have hbv : ((fineBlock (S := S) (n := n) (M := M) (K := K) k x) μ).val = u :=
        fineBlock_val hk' x μ
      rcases le_or_gt Mc (M * n K * S.L ^ (K - k)) with hle | hlt
      · have := macCell_val_bounds hMc hle hcell
        rw [hbv] at this; exact this
      · have hK1 : macK (M * n K * S.L ^ (K - k)) Mc = 1 := macK_eq_one_of_lt (by omega)
        have hz0 : (z μ : ℕ) = 0 := by have := (z μ).2; omega
        have := ZMod.val_lt ((fineBlock (S := S) (n := n) (M := M) (K := K) k x) μ)
        rw [hbv] at this
        rw [hz0]; omega
    have hv1 : (z μ : ℕ) * Mc * S.L ^ k ≤ v := by
      have h1 := hbounds.1
      have h2 : u * S.L ^ k ≤ v := Nat.div_mul_le_self v _
      nlinarith
    have hv2 : v < (z μ : ℕ) * Mc * S.L ^ k + 2 * s' := by
      have h1 := hbounds.2
      have h2 : v < (u + 1) * S.L ^ k := by
        rw [hu]; exact Nat.lt_mul_div_succ v hLk |>.trans_le (by rw [Nat.mul_comm])
      nlinarith
    have hq1 : A μ ≤ v / s' := Nat.div_le_div_right hv1
    have hq2 : v / s' ≤ A μ + 2 := by
      have : v / s' ≤ ((z μ : ℕ) * Mc * S.L ^ k + 2 * s') / s' := Nat.div_le_div_right hv2.le
      rwa [Nat.add_mul_div_right _ _ hs'pos] at this
    refine ⟨v / s' - A μ, Finset.mem_range.2 (by omega), ?_⟩
    unfold cubeOf
    rw [blockMap_apply]
    unfold blockCoord
    congr 1
    rw [← hv, ← hs']
    omega
  calc _ ≤ _ := Finset.card_le_card hsub
    _ = ∏ μ, ((Finset.range 3).image
          fun t => ((A μ + t : ℕ) : ZMod (n K * S.L ^ (K - (k + 1))))).card :=
        Fintype.card_piFinset _
    _ ≤ ∏ _μ : Fin S.d, 3 := Finset.prod_le_prod fun μ _ =>
        (Finset.card_image_le).trans (by simp)
    _ = 3 ^ S.d := by simp

/-- **The hull of a set of cells has at most `3^d` cubes per cell.** -/
theorem card_image_cubeOf_cellHull_le {k : ℕ} (hk : k + 1 ≤ K) {Mc : ℕ} (hMc : 0 < Mc)
    (hMcL : Mc ≤ M * S.L) (𝒳 : Finset (MacIdx S.d (M * n K * S.L ^ (K - k)) Mc)) :
    ((cellHull (S := S) (n := n) (M := M) (K := K) k Mc 𝒳).image
      (cubeOf (S := S) (n := n) (M := M) (K := K) k)).card ≤ 3 ^ S.d * 𝒳.card := by
  unfold cellHull
  rw [image_cubeOf_hullT k hk]
  have hsub : (fineCells (S := S) (n := n) (M := M) (K := K) k Mc 𝒳).image
      (cubeOf (S := S) (n := n) (M := M) (K := K) k) ⊆
      𝒳.biUnion fun z => (fineCells (S := S) (n := n) (M := M) (K := K) k Mc {z}).image
        (cubeOf (S := S) (n := n) (M := M) (K := K) k) := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    have hx' := (Finset.mem_filter.1 hx).2
    refine Finset.mem_biUnion.2 ⟨_, hx', Finset.mem_image.2 ⟨x, ?_, rfl⟩⟩
    simp [fineCells]
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ z ∈ 𝒳, ((fineCells (S := S) (n := n) (M := M) (K := K) k Mc {z}).image
          (cubeOf (S := S) (n := n) (M := M) (K := K) k)).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ 𝒳, 3 ^ S.d := Finset.sum_le_sum fun z _ => card_image_cubeOf_cell_le hk hMc hMcL z
    _ = 3 ^ S.d * 𝒳.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **The number of `k`-blocks of a union of scale-`(k+1)` cubes** is `(M L)^d` per cube. -/
theorem card_image_fineBlock_eq {k : ℕ} (hk : k + 1 ≤ K) (X : Finset (Torus S.d (M * n K * S.L ^ K)))
    (hX : ∀ x ∈ X, ∀ z : Torus S.d (M * n K * S.L ^ K),
      (∀ μ, (x μ).val / (M * S.L ^ (k + 1)) = (z μ).val / (M * S.L ^ (k + 1))) → z ∈ X) :
    (X.image (fineBlock (S := S) (n := n) (M := M) (K := K) k)).card =
      (M * S.L) ^ S.d * (X.image (cubeOf (S := S) (n := n) (M := M) (K := K) k)).card := by
  have hk' : k ≤ K := by omega
  have hs : M * S.L ^ (k + 1) = S.L ^ k * (M * S.L) := by rw [pow_succ]; ring
  have hX' : ∀ x ∈ X, ∀ z : Torus S.d (M * n K * S.L ^ K),
      (∀ μ, (x μ).val / S.L ^ k = (z μ).val / S.L ^ k) → z ∈ X := by
    intro x hx z hz
    refine hX x hx z fun μ => ?_
    rw [hs, ← Nat.div_div_eq_div_mul (x μ).val (S.L ^ k), ← Nat.div_div_eq_div_mul (z μ).val (S.L ^ k),
      hz μ]
  have h1 := card_blockClosed (fine_eq_blockSide hk') X hX'
  have h2 := card_blockClosed (fine_eq_cubeSide hk) X hX
  have hpos : 0 < (S.L ^ k) ^ S.d := pow_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) k) _
  have : (S.L ^ k) ^ S.d * (X.image (blockMap (S.L ^ k) (M * n K * S.L ^ (K - k)))).card =
      (S.L ^ k) ^ S.d * ((M * S.L) ^ S.d *
        (X.image (cubeOf (S := S) (n := n) (M := M) (K := K) k)).card) := by
    have hp : (M * S.L ^ (k + 1)) ^ S.d = (S.L ^ k) ^ S.d * (M * S.L) ^ S.d := by rw [hs, mul_pow]
    rw [← h1, h2, hp]; unfold cubeOf; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

end Balaban.RootFSpine
