module

public import Balaban.LargeField.R.WindowGenGlue
public import Balaban.LargeField.R.ChainGraph
public import Balaban.LargeField.LF1.Setup
public import Balaban.LargeField.LF1.BlockArith
public import Balaban.Multiscale.PathMetric
import Mathlib.Tactic.Linarith

/-!
# The collar of the window generating set (COLLAR-FIX §§1-2, geometry)

The physical datum of the window background is the trace of the *parent* multiscale field on the
data sites of `G = 𝔹_{k₁,k}` (`notes/phase1/COLLAR-FIX.md`).  This file collects the geometry.

* `parentBlock B x`: the block of the parent `B = 𝔹_k` read at `x` (COLLAR-FIX (1.1)): the block of
  layer `n_B(x)` containing `x` if `x ∈ Ω₁(B)`, the single site `⟨0, x⟩` otherwise;
* `ParentRefines G B`: `parentBlock B` is constant on every block of every layer of `G`;
* `window_parent_refines`: `ParentRefines` for the window generating set;
* `collarIn`, `collarOut`, `window_collar_partition`: the two faces of the collar;
* `outer_collar_outside_reference` and `outer_collar_parent_layer_top`: the outer face is outside
  `Ω₁(𝔹_k(U_k))` and reads the top layer `k` of the parent;
* `inner_collar_parent_layer`: the inner face has parent layer exactly `k₁`;
* `inner_collar_in_regular_T`: the one-site extension of the regularity path of Lemma III.4.6.

The set-theoretic inclusions of LF-RECONSTRUCTION Lemma III.1.2 (f) and the margins of Lemma
III.4.6 are *not* fields of `WindowPieces.Hyp`; they are the named hypotheses `hOmK1`, `hOmK`,
`hZk1top`, `hsupp`, `hmargin`, `hcore`, `hbdry`, `hexitLayer`, `hcoreTop`, `hreach`, `hcT`, `hwT` of
the theorems below.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}

/-! ### The parent block and parent refinement -/

section Parent

open Classical in
/-- **COLLAR-FIX (1.1)**, the block read at `x` from the parent `B`: the block of layer `n_B(x)` containing `x`
for `x ∈ Ω₁(B)`, and the single site `⟨0, x⟩` (layer `0`) off `Ω₁(B)`. -/
noncomputable def parentBlock (B : GeneratingSet d L N₀ k ϱ) (x : Torus d (N₀ * L ^ k)) :
    BlockV d L N₀ k :=
  if x ∈ B.Ω 1 then blockOf d L N₀ k (B.layerIndex x) x else ⟨0, x⟩

theorem parentBlock_of_mem (B : GeneratingSet d L N₀ k ϱ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ B.Ω 1) : parentBlock B x = blockOf d L N₀ k (B.layerIndex x) x := by
  simp [parentBlock, hx]

theorem parentBlock_of_not_mem (B : GeneratingSet d L N₀ k ϱ) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∉ B.Ω 1) : parentBlock B x = ⟨0, x⟩ := by
  simp [parentBlock, hx]

/-- **Parent refinement**: every block of every layer `1 ≤ n ≤ k` of `G` is read from a single block of
the parent `B` (so that the parent lift is constant on the blocks of `G`, i.e. is a legitimate
datum for `G`). -/
def ParentRefines (G : GeneratingSet d L N₀ k ϱ) (B : GeneratingSet d L N₀ k ϱ') : Prop :=
  ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ G.layer n, ∀ x' ∈ G.blk n x, parentBlock B x' = parentBlock B x

/-- The layer index of a site of `Ω_n(B)` is at least `n`. -/
theorem le_layerIndex_of_mem {B : GeneratingSet d L N₀ k ϱ'} {n : ℕ} (hn1 : 1 ≤ n) (hnk : n ≤ k)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ B.Ω n) : n ≤ B.layerIndex x := by
  have hx1 : x ∈ B.Ω 1 := B.Ω_antitone le_rfl hn1 (by omega) hx
  obtain ⟨h1, hk, hxl⟩ := B.layerIndex_spec hx1
  by_contra hlt
  push Not at hlt
  exact ((B.mem_layer).1 hxl).2 (B.Ω_antitone (by omega) (by omega) (by omega) hx)

/-- If every layer-`n` site of `G` lies in `Ω_n(B)`, the parent refines `G`. -/
theorem parentRefines_of_subset (G : GeneratingSet d L N₀ k ϱ) (B : GeneratingSet d L N₀ k ϱ')
    (hsub : ∀ n, 1 ≤ n → n ≤ k → ∀ x ∈ G.layer n, x ∈ B.Ω n) : ParentRefines G B := by
  intro n hn1 hnk x hx x' hx'
  have hb : jBlock d L N₀ k n x' = jBlock d L N₀ k n x := GeneratingSet.mem_blk.1 hx'
  have hx'l : x' ∈ G.layer n := (G.mem_layer_iff hn1 hnk hb).2 hx
  have hxB := hsub n hn1 hnk x hx
  have hx'B := hsub n hn1 hnk x' hx'l
  have hxB1 : x ∈ B.Ω 1 := B.Ω_antitone le_rfl hn1 (by omega) hxB
  have hx'B1 : x' ∈ B.Ω 1 := B.Ω_antitone le_rfl hn1 (by omega) hx'B
  obtain ⟨hm1, hmk, hxm⟩ := B.layerIndex_spec hxB1
  have hnm := le_layerIndex_of_mem hn1 hnk hxB
  have hbm : jBlock d L N₀ k (B.layerIndex x) x' = jBlock d L N₀ k (B.layerIndex x) x :=
    jBlock_mono hnm hmk hb
  have hx'm : x' ∈ B.layer (B.layerIndex x) := (layer_blockConst B hm1 hmk hbm).2 hxm
  rw [parentBlock_of_mem B hx'B1, parentBlock_of_mem B hxB1,
    B.layerIndex_eq hm1 hmk hx'm]
  simp only [blockOf]
  rw [hbm]

/-- **`window_parent_refines`** (COLLAR-FIX §1): the parent `𝔹_k` refines the window generating set.
Premises (not fields of `WindowPieces.Hyp`): the core sites of `Z_{k₁}` and the boundary-piece sites lie
in the same layers of the parent (`hcore`: the margin of Lemma III.4.6; `hbdry`: the boundary piece
is in the parent's top layer `k`, hence in every layer). -/
theorem window_parent_refines (W : WindowPieces d L N₀ k ϱ) (hWh : W.Hyp)
    (hcore : ∀ n, 1 ≤ n → n ≤ k → W.core.Ω n ∩ W.Zk1 ⊆ W.full.Ω n)
    (hbdry : ∀ n, 1 ≤ n → n ≤ k → W.bdry.Ω n ∩ (W.Unb \ W.Z) ⊆ W.full.Ω n) :
    ParentRefines (W.windowGenSet hWh) W.full := by
  refine parentRefines_of_subset _ _ fun n hn1 hnk x hx => ?_
  have hxΩ := ((GeneratingSet.mem_layer _).1 hx).1
  rw [W.windowGenSet_Ω hWh n] at hxΩ
  rcases Finset.mem_union.1 hxΩ with h | h
  · rcases Finset.mem_union.1 h with h | h
    · exact hcore n hn1 hnk h
    · exact (Finset.mem_inter.1 h).1
  · exact hbdry n hn1 hnk h

end Parent

/-! ### The two faces of the collar -/

section Faces

variable (W : WindowPieces d L N₀ k ϱ) (hWh : W.Hyp)

/-- The inner face `C_in = C_G ∩ Z_{k₁}` of the collar of the window generating set. -/
noncomputable def collarIn : Finset (Torus d (N₀ * L ^ k)) :=
  by classical exact collar (W.windowGenSet hWh) ∩ W.Zk1

/-- The outer face `C_out = C_G ∖ Z_{k₁}` of the collar of the window generating set. -/
noncomputable def collarOut : Finset (Torus d (N₀ * L ^ k)) :=
  by classical exact collar (W.windowGenSet hWh) \ W.Zk1

theorem mem_collarIn {c : Torus d (N₀ * L ^ k)} :
    c ∈ collarIn W hWh ↔ c ∈ collar (W.windowGenSet hWh) ∧ c ∈ W.Zk1 := by
  classical simp [collarIn]

theorem mem_collarOut {c : Torus d (N₀ * L ^ k)} :
    c ∈ collarOut W hWh ↔ c ∈ collar (W.windowGenSet hWh) ∧ c ∉ W.Zk1 := by
  classical simp [collarOut]

/-- **`window_collar_partition`**: the collar of the window generating set is the disjoint union of the
inner and outer faces. -/
theorem window_collar_partition :
    collarIn W hWh ∪ collarOut W hWh = collar (W.windowGenSet hWh) ∧
      Disjoint (collarIn W hWh) (collarOut W hWh) := by
  classical
  refine ⟨?_, ?_⟩
  · ext c
    simp only [Finset.mem_union, mem_collarIn, mem_collarOut]
    by_cases hc : c ∈ W.Zk1 <;> simp [hc]
  · rw [Finset.disjoint_left]
    intro c h1 h2
    exact ((mem_collarOut W hWh).1 h2).2 ((mem_collarIn W hWh).1 h1).2

theorem collarIn_not_mem_Ω1 {c : Torus d (N₀ * L ^ k)} (hc : c ∈ collarIn W hWh) :
    c ∉ (W.windowGenSet hWh).Ω 1 :=
  ((mem_collar _).1 ((mem_collarIn W hWh).1 hc).1).1

theorem collarOut_not_mem_Ω1 {c : Torus d (N₀ * L ^ k)} (hc : c ∈ collarOut W hWh) :
    c ∉ (W.windowGenSet hWh).Ω 1 :=
  ((mem_collar _).1 ((mem_collarOut W hWh).1 hc).1).1

/-- **`outer_collar_outside_reference`** (COLLAR-FIX §2, outer face): a site of the outer collar is
neither in `Z` nor in `Ω₁(𝔹_k(U_k))`, the generating set of the later reference field.  Premises
(Lemma III.1.2 (f) and the support of the boundary piece): `Ω_{k₁}(B)ᶜ ⊆ Z_{k₁}`, i.e. every site off
`Z_{k₁}` is in `Ω₁(B)`, and `Ω₁(𝔹_k(U_k)) ⊆ U^∼_k`. -/
theorem outer_collar_outside_reference
    (hOmK1 : ∀ x, x ∉ W.Zk1 → x ∈ W.full.Ω 1) (hsupp : ∀ x ∈ W.bdry.Ω 1, x ∈ W.Unb)
    {c : Torus d (N₀ * L ^ k)} (hc : c ∈ collarOut W hWh) :
    c ∉ W.Z ∧ c ∉ W.bdry.Ω 1 := by
  have hcG := collarOut_not_mem_Ω1 W hWh hc
  have hcZ1 := ((mem_collarOut W hWh).1 hc).2
  have hcZ : c ∉ W.Z := by
    intro hZ
    refine hcG ?_
    rw [W.windowGenSet_Ω hWh 1]
    simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, hcZ1, hZ, hOmK1 c hcZ1]
  refine ⟨hcZ, fun hb => hcG ?_⟩
  rw [W.windowGenSet_Ω hWh 1]
  simp [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, hcZ, hb, hsupp c hb]

/-- **`outer_collar_parent_layer_top`**: a site of the outer collar lies in the top layer `k` of the
parent (`Ω_k(B)ᶜ ⊆ Z`), so its parent block is the `k`-block `blockOf k c`. -/
theorem outer_collar_parent_layer_top (hk : 1 ≤ k)
    (hOmK1 : ∀ x, x ∉ W.Zk1 → x ∈ W.full.Ω 1) (hsupp : ∀ x ∈ W.bdry.Ω 1, x ∈ W.Unb)
    (hOmK : ∀ x, x ∉ W.Z → x ∈ W.full.Ω k)
    {c : Torus d (N₀ * L ^ k)} (hc : c ∈ collarOut W hWh) :
    c ∈ W.full.layer k ∧ W.full.layerIndex c = k ∧
      parentBlock W.full c = blockOf d L N₀ k k c := by
  have hcZ := (outer_collar_outside_reference W hWh hOmK1 hsupp hc).1
  have hl : c ∈ W.full.layer k := (GeneratingSet.mem_layer _).2 ⟨hOmK c hcZ, by simp [W.full.top]⟩
  have hli := W.full.layerIndex_eq hk le_rfl hl
  have h1 : c ∈ W.full.Ω 1 := W.full.layer_subset hk le_rfl hl
  exact ⟨hl, hli, by rw [parentBlock_of_mem _ h1, hli]⟩

/-- **`inner_collar_parent_layer`** (COLLAR-FIX §2, inner face): a site of the inner collar lies in the
layer exactly `k₁` of the parent.  Premises: the margin of Lemma III.4.6 (a site adjacent to a site of
`Ω₁(G)` and lying in `Z_{k₁}` is in `Ω_{k₁}(B)`: `Ω_{k₁}(B)ᶜ` starts `2[R̂]+6` cubes into `Z_{k₁}`,
the core reaches `2[R̂]+3`) and `Z_{k₁} ∩ Ω_{k₁+1}(B) = ∅` (Lemma III.1.2 (f)). -/
theorem inner_collar_parent_layer {k1 : ℕ} (hk1 : 1 ≤ k1) (hk1k : k1 ≤ k)
    (hmargin : ∀ x ∈ (W.windowGenSet hWh).Ω 1, ∀ c, Adj x c → c ∈ W.Zk1 → c ∈ W.full.Ω k1)
    (hZk1top : ∀ x ∈ W.Zk1, x ∉ W.full.Ω (k1 + 1))
    {c : Torus d (N₀ * L ^ k)} (hc : c ∈ collarIn W hWh) :
    c ∈ W.full.layer k1 ∧ W.full.layerIndex c = k1 ∧
      parentBlock W.full c = blockOf d L N₀ k k1 c := by
  obtain ⟨hcol, hcZ⟩ := (mem_collarIn W hWh).1 hc
  obtain ⟨-, x, hx, hadj⟩ := (mem_collar _).1 hcol
  have hcΩ : c ∈ W.full.Ω k1 := hmargin x hx c hadj hcZ
  have hl : c ∈ W.full.layer k1 := (GeneratingSet.mem_layer _).2 ⟨hcΩ, hZk1top c hcZ⟩
  have hli := W.full.layerIndex_eq hk1 hk1k hl
  have h1 : c ∈ W.full.Ω 1 := W.full.layer_subset hk1 hk1k hl
  exact ⟨hl, hli, by rw [parentBlock_of_mem _ h1, hli]⟩

end Faces

/-! ### The one-site extension of the regularity path -/

section RegularT

/-- Sites at nearest-neighbour distance lie in equal or adjacent `j`-blocks. -/
theorem jBlock_eq_or_adjT {j : ℕ} (hj : j ≤ k) {x c : Torus d (N₀ * L ^ k)} (h : Adj x c) :
    jBlock d L N₀ k j x = jBlock d L N₀ k j c ∨
      AdjT (jBlock d L N₀ k j x) (jBlock d L N₀ k j c) := by
  have hℓ : N₀ * L ^ k = L ^ j * (N₀ * L ^ (k - j)) := side_eq hj
  have hpos : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  by_cases heq : jBlock d L N₀ k j x = jBlock d L N₀ k j c
  · exact Or.inl heq
  · refine Or.inr ⟨heq, ?_⟩
    obtain ⟨μ, hμ | hμ⟩ := h
    · have := blockMap_add_single_cases (N := L ^ j) (m := N₀ * L ^ (k - j)) hℓ x μ
        (t := 1) hpos
      simp only [Nat.cast_one] at this
      rw [← hμ] at this
      rcases this with h1 | h1
      · exact absurd h1.symm heq
      · exact ⟨μ, Or.inl h1⟩
    · have := blockMap_add_single_cases (N := L ^ j) (m := N₀ * L ^ (k - j)) hℓ c μ
        (t := 1) hpos
      simp only [Nat.cast_one] at this
      rw [← hμ] at this
      rcases this with h1 | h1
      · exact absurd h1 heq
      · exact ⟨μ, Or.inr h1⟩

theorem adjT_symm' {m : ℕ} {y y' : Torus d m} (h : AdjT y y') : AdjT y' y := by
  obtain ⟨hne, μ, h | h⟩ := h
  · exact ⟨hne.symm, μ, Or.inr h⟩
  · exact ⟨hne.symm, μ, Or.inl h⟩

/-- A path of at most `m` adjacent `k₁`-blocks from `b`, all in `T`, to the `k₁`-block of a window block
`s ∈ Λ_{k₁}(B)`, `s ∉ Z_{k₁}` (the shape of `hreach` in `deltaPsi_le_pieces'`). -/
def TPathToWindow (B : GeneratingSet d L N₀ k ϱ') (Zc : Finset (Torus d (N₀ * L ^ k))) (k1 : ℕ)
    (T : Set (Torus d (N₀ * L ^ (k - k1)))) (b : Torus d (N₀ * L ^ (k - k1))) (m : ℕ) : Prop :=
  ∃ u : ℕ → Torus d (N₀ * L ^ (k - k1)), u 0 = b ∧ (∀ i ≤ m, u i ∈ T) ∧
    (∀ i < m, AdjT (u i) (u (i + 1))) ∧
    ∃ s ∈ B.layer k1, s ∉ Zc ∧ jBlock d L N₀ k k1 s = u m

/-- Prepending one block (equal or adjacent to the start) lengthens a path by at most one. -/
theorem TPathToWindow.prepend {B : GeneratingSet d L N₀ k ϱ'} {Zc : Finset (Torus d (N₀ * L ^ k))}
    {k1 : ℕ} {T : Set (Torus d (N₀ * L ^ (k - k1)))} {q : Torus d (N₀ * L ^ (k - k1))} {m : ℕ}
    (hq : TPathToWindow B Zc k1 T q m) (p : Torus d (N₀ * L ^ (k - k1))) (hp : p ∈ T)
    (hpq : p = q ∨ AdjT p q) : ∃ m' ≤ m + 1, TPathToWindow B Zc k1 T p m' := by
  obtain ⟨u, hu0, huT, huA, s, hs, hsZ, hsu⟩ := hq
  rcases hpq with rfl | hpq
  · exact ⟨m, by omega, u, hu0, huT, huA, s, hs, hsZ, hsu⟩
  · refine ⟨m + 1, le_rfl, fun i => match i with | 0 => p | i + 1 => u i, rfl, ?_, ?_, s, hs, hsZ, hsu⟩
    · intro i hi
      match i, hi with
      | 0, _ => exact hp
      | i + 1, hi => exact huT i (by omega)
    · intro i hi
      match i, hi with
      | 0, _ => simpa [hu0] using hpq
      | i + 1, hi => exact huA i (by omega)

/-- **`inner_collar_in_regular_T`** (COLLAR-FIX §2, the one-site extension of Lemma III.4.6): every
site `c` of the inner collar has a path of at most `m_W + 1` adjacent `k₁`-blocks in the regularity set `T`
from `b_{k₁}(c)` to a window block.  It follows from the landed core reach `hreach` (the path of
`deltaPsi_le_pieces'` from a core site of `Z_{k₁}`) by prepending the block of `c`.  Premises, all of
the geometry of the window that `WindowPieces.Hyp` does not contain:
* `hZ`: `Z_{k₁} ⊆ Z`; `hcoreTop`, `hreach`: as in `deltaPsi_le_pieces'`;
* `hexitLayer`: a site of `Ω₁(G)` off `Z_{k₁}` adjacent to `Z_{k₁}` lies in `Λ_{k₁}(B)` (the window
  blocks next to the core);
* `hcT`, `hwT`: the cube incidence: the `k₁`-blocks of the inner collar, and of the window sites next to
  it, lie in the regularity set `T` (the supports `χ_{k₁}(Ω^{∼-3}_{k₁} ∩ Z_{k₁})`,
  `χ'_{k₁}(Ω_{k₁} ∩ (Ω^c_{k₁})^{∼3} ∩ Z_{k₁})` of Definition II.5.6 at the preceding step). -/
theorem inner_collar_in_regular_T (W : WindowPieces d L N₀ k ϱ) (hWh : W.Hyp) {k1 : ℕ}
    (hk1k : k1 ≤ k) (T : Set (Torus d (N₀ * L ^ (k - k1)))) (mW : ℕ)
    (hZ : W.Zk1 ⊆ W.Z)
    (hcoreTop : ∀ x ∈ W.Zk1, x ∈ W.core.Ω 1 → x ∈ W.core.layer k1)
    (hreach : ∀ x ∈ W.core.layer k1, x ∈ W.Zk1 → ∃ m ≤ mW, TPathToWindow W.full W.Zk1 k1 T
      (jBlock d L N₀ k k1 x) m)
    (hexitLayer : ∀ x ∈ (W.windowGenSet hWh).Ω 1, x ∉ W.Zk1 → ∀ c, Adj x c → c ∈ W.Zk1 →
      x ∈ W.full.layer k1)
    (hcT : ∀ c ∈ collarIn W hWh, jBlock d L N₀ k k1 c ∈ T)
    (hwT : ∀ x ∈ (W.windowGenSet hWh).Ω 1, x ∉ W.Zk1 → x ∈ W.full.layer k1 →
      jBlock d L N₀ k k1 x ∈ T)
    {c : Torus d (N₀ * L ^ k)} (hc : c ∈ collarIn W hWh) :
    ∃ m ≤ mW + 1, TPathToWindow W.full W.Zk1 k1 T (jBlock d L N₀ k k1 c) m := by
  obtain ⟨hcol, hcZ⟩ := (mem_collarIn W hWh).1 hc
  obtain ⟨-, x, hx, hadj⟩ := (mem_collar _).1 hcol
  have hcb := jBlock_eq_or_adjT hk1k hadj
  by_cases hxZ : x ∈ W.Zk1
  · have hxcore : x ∈ W.core.Ω 1 := by
      have := hx
      rw [W.windowGenSet_Ω hWh 1] at this
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at this
      rcases this with (⟨h1, _⟩ | ⟨_, h2, h3⟩) | ⟨_, _, h3⟩
      · exact h1
      · exact absurd hxZ h3
      · exact absurd (hZ hxZ) h3
    obtain ⟨m, hm, hpath⟩ := hreach x (hcoreTop x hxZ hxcore) hxZ
    obtain ⟨m', hm', hp⟩ := hpath.prepend (jBlock d L N₀ k k1 c) (hcT c hc)
      (by
        rcases hcb with h | h
        · exact Or.inl h.symm
        · exact Or.inr (adjT_symm' h))
    exact ⟨m', by omega, hp⟩
  · have hxl := hexitLayer x hx hxZ c hadj hcZ
    have h0 : TPathToWindow W.full W.Zk1 k1 T (jBlock d L N₀ k k1 x) 0 :=
      ⟨fun _ => jBlock d L N₀ k k1 x, rfl, fun i _ => hwT x hx hxZ hxl, fun i hi => absurd hi (by omega),
        x, hxl, hxZ, rfl⟩
    obtain ⟨m', hm', hp⟩ := h0.prepend (jBlock d L N₀ k k1 c) (hcT c hc)
      (by
        rcases hcb with h | h
        · exact Or.inl h.symm
        · exact Or.inr (adjT_symm' h))
    exact ⟨m', by omega, hp⟩

end RegularT

end Balaban.LargeField
