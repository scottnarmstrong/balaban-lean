/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.LedgerPacking
public import Balaban.Localization.P6PairBoundary
public import Balaban.Localization.P6PairOp
public import Balaban.LargeField.Characteristic.Analytic
import Balaban.LargeField.R.WindowOfHistory
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The active halo and the root incidence count of the P6 auxiliary cover (VMOD-24 §1)

Geometry of the cover only.  Rooting of the actual P6 coefficients at active cells is NOT proved
here (VMOD-25: it is not implied by the landed locality).

Notation: `K = k + 1`, `a_K = L ^ (K + m₀ + m₁)` the side of a top cell, `F♯ = p6FsharpC`.

General form (any generating set `G` of the cover torus; no alignment is needed):
let `U` be a top cell and suppose every top cell equal or Moore-adjacent to `U` lies in `G.Ω K`.
* `touch_layer_eq_top`: an index `P ∈ cubeIdx G` whose parameter patch Moore-touches `U` has layer
  `K` (the patch lies in one top cell, that cell is in `Ω_K`, and the layers are disjoint);
* `root_patch_count`: there are at most `3 ^ d * (L ^ m₀) ^ d` such indices (formula (1.2)),
  when `L ^ m₀ ∣ N₁`.

Why the halo hypothesis cannot be dropped (VMOD-24 §2): the hypothesis only puts the patch's own
top cell in `Ω_K`.  A top cell that is not adjacent to an active cell may lie across the old wall,
outside `Ω_K`; its sites then carry a layer `n < K` of `F♯` (the layers `n ≤ k` of `F♯` are those of
the old set, `p6Fsharp_Ω_of_le`), and the layer-`n` patches inside it are indices of `cubeIdx` that
are not at layer `K`.  Only the active-halo hypothesis forces layer `K`.

P6 instance: `p6_active_top_halo` verifies the hypothesis for `F♯`: a top cell Moore-adjacent to a
top cell over the fine lift of the new active region lies in `F♯.Ω K` (the one-top-cell
neighbourhood of the top closure of `thick Z_kᶜ`, `p6HaloCubes`).  This needs the numerical
premise `L ^ m₀ ∣ c`, so that top cells of side `a_K` do not straddle the cubes of side
`L ^ (K + m₁) c` defining `p6HaloCubes`.  The fine/coarse identification of the two tori is carried
by the explicit cast `torusCast`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Finset

section General

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

omit [NeZero N₁] [NeZero L] in
/-- A parameter patch of layer `n ≤ K` lies in the top cell (of side `a_K`) of its centre. -/
theorem Pset_subset_topCell (m₀ : ℕ) [NeZero N₁] [NeZero L] {P : ℕ × CTorus d L N₁ m₁ K}
    (hP : P.1 ≤ K) : Pset m₁ P ⊆ topCell m₀ (K, P.2) := by
  intro x hx
  have hdvd : L ^ (P.1 + m₁) ∣ cellSide L m₀ m₁ K := by
    unfold cellSide
    exact pow_dvd_pow L (by omega)
  have h := SameCell.mono hdvd hx
  have hb : cbase (cellSide L m₀ m₁ K) x = cbase (cellSide L m₀ m₁ K) P.2 := by
    funext μ; simp only [cbase]; rw [h μ]
  show x ∈ box (cbase (cellSide L m₀ m₁ K) P.2) (cellSide L m₀ m₁ K)
  rw [← hb]
  exact mem_box_cbase (cellSide_pos m₀ m₁ K) x

/-- **Layer of a root-adjacent index.**  Let `U` be the top cell of `u`, and suppose every top cell
Moore-adjacent to (or equal to) `U` lies in `Ω_K`.  An index `P ∈ cubeIdx G` whose parameter patch
Moore-touches `U` has layer `K`. -/
theorem touch_layer_eq_top (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {m₀ : ℕ}
    (u : CTorus d L N₁ m₁ K)
    (hU : ∀ z : CTorus d L N₁ m₁ K, MooreTouch (topCell m₀ (K, u)) (topCell m₀ (K, z)) →
      topCell m₀ (K, z) ⊆ ↑(G.Ω K))
    {P : ℕ × CTorus d L N₁ m₁ K} (hP : P ∈ cubeIdx G)
    (hT : MooreTouch (topCell m₀ (K, u)) (Pset m₁ P)) : P.1 = K := by
  obtain ⟨⟨h1, hK⟩, hl, -⟩ := (mem_cubeIdx G).1 hP
  have hsub := Pset_subset_topCell (m₁ := m₁) (L := L) (N₁ := N₁) m₀ hK
  have hT' : MooreTouch (topCell m₀ (K, u)) (topCell m₀ (K, P.2)) := by
    obtain ⟨x, hx, y, hy, hn⟩ := hT
    exact ⟨x, hx, y, hsub hy, hn⟩
  have hmem : P.2 ∈ topCell m₀ (K, P.2) := mem_box_cbase (cellSide_pos m₀ m₁ K) _
  have hΩ : P.2 ∈ G.Ω K := Finset.mem_coe.1 (hU P.2 hT' hmem)
  have hlay : P.2 ∈ G.layer K := G.mem_layer.2 ⟨hΩ, by rw [G.top]; simp⟩
  by_contra hne
  exact G.layer_disjoint h1 hK (h1.trans hK) le_rfl hne hl hlay

end General

section Offsets

variable {d : ℕ}

/-- Two aligned boxes of side `a` (`a ∣ n`) that Moore-touch have bases differing by `a s` with
`s ∈ {-1, 0, 1}` in each coordinate. -/
theorem aligned_touch_offsets {n : ℕ} [NeZero n] {a : ℕ} (ha0 : 0 < a) (ha : a ∣ n)
    {b b0 : Torus d n} (hb : Aligned a b) (hb0 : Aligned a b0) {x y : Torus d n}
    (hx : x ∈ box b0 a) (hy : y ∈ box b a) (hn : Fluctuation.Near 1 1 x y) :
    ∃ s : Fin d → ℤ, (∀ μ, |s μ| ≤ 1) ∧
      b = b0 + fun μ => (((a : ℤ) * s μ : ℤ) : ZMod n) := by
  obtain ⟨w', hw', rfl⟩ := hx
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨q, hq, hyq⟩ := hn
  have key : ∀ μ, ∃ s : ℤ, |s| ≤ 1 ∧ b μ = b0 μ + (((a : ℤ) * s : ℤ) : ZMod n) := by
    intro μ
    have e := congrFun hyq μ
    simp only [Pi.add_apply, natT] at e
    set t : ℤ := (w' μ : ℤ) + q μ - w μ with ht
    have hbt : b μ = b0 μ + (t : ZMod n) := by
      rw [ht]; push_cast at e ⊢
      linear_combination e
    have hq1 := abs_le.1 (hq μ)
    have hw1 := hw μ
    have hw1' := hw' μ
    have htb : -(a : ℤ) ≤ t ∧ t ≤ a := by
      constructor <;> push_cast at hq1 <;> omega
    have hcast := congrArg (ZMod.castHom ha (ZMod a)) hbt
    rw [map_add, map_intCast] at hcast
    simp only [ZMod.castHom_apply, ZMod.cast_eq_val] at hcast
    have hbz : (((b μ).val : ℕ) : ZMod a) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (Nat.dvd_of_mod_eq_zero (hb μ))
    have hb0z : (((b0 μ).val : ℕ) : ZMod a) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (Nat.dvd_of_mod_eq_zero (hb0 μ))
    rw [hbz, hb0z, zero_add] at hcast
    have hdv : (a : ℤ) ∣ t := (ZMod.intCast_zmod_eq_zero_iff_dvd t a).1 hcast.symm
    obtain ⟨s, hs⟩ := hdv
    have ha1 : (0 : ℤ) < a := by exact_mod_cast ha0
    refine ⟨s, abs_le.2 ⟨?_, ?_⟩, by rw [hbt, hs]⟩
    · by_contra hlt
      replace hlt := not_le.1 hlt
      nlinarith [htb.1]
    · by_contra hlt
      replace hlt := not_le.1 hlt
      nlinarith [htb.2]
  choose s hs1 hs2 using key
  refine ⟨s, hs1, ?_⟩
  funext μ
  simpa using hs2 μ

end Offsets

section Count

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

open Classical in
/-- **Root patch count (VMOD-24 (1.2)), general form.**  Under the hypothesis of
`touch_layer_eq_top` and `L ^ m₀ ∣ N₁`, at most `3 ^ d * (L ^ m₀) ^ d` indices of `cubeIdx G` have
a parameter patch Moore-touching the top cell `U` of `u`. -/
theorem root_patch_count (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {m₀ : ℕ}
    (hN : L ^ m₀ ∣ N₁) (u : CTorus d L N₁ m₁ K)
    (hU : ∀ z : CTorus d L N₁ m₁ K, MooreTouch (topCell m₀ (K, u)) (topCell m₀ (K, z)) →
      topCell m₀ (K, z) ⊆ ↑(G.Ω K)) :
    ((cubeIdx G).filter fun P => MooreTouch (topCell m₀ (K, u)) (Pset m₁ P)).card ≤
      3 ^ d * (L ^ m₀) ^ d := by
  set a := cellSide L m₀ m₁ K with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ K
  have hadvd : a ∣ (N₁ * L ^ m₁) * L ^ K := cellSide_dvd hN le_rfl
  set b0 : CTorus d L N₁ m₁ K := cbase a u with hb0
  let R : Finset (ℕ × CTorus d L N₁ m₁ K) :=
    (Finset.univ : Finset (Fin d → Fin 3)).image fun r =>
      (K, b0 + fun μ => ((((a : ℤ) * (((r μ : ℕ) : ℤ) - 1) : ℤ)) : ZMod ((N₁ * L ^ m₁) * L ^ K)))
  have hR : R.card ≤ 3 ^ d := by
    refine (Finset.card_image_le).trans ?_
    simp
  have hsub : ((cubeIdx G).filter fun P => MooreTouch (topCell m₀ (K, u)) (Pset m₁ P)) ⊆
      idxInCells G m₀ R := by
    intro P hP
    rw [Finset.mem_filter] at hP
    obtain ⟨hPc, hT⟩ := hP
    rw [mem_idxInCells]
    refine ⟨hPc, ?_⟩
    have hP1 := touch_layer_eq_top G u hU hPc hT
    have hK : P.1 ≤ K := ((mem_cubeIdx G).1 hPc).1.2
    obtain ⟨x, hx, y, hy, hn⟩ := hT
    have hy' : y ∈ box (cbase a P.2) a := Pset_subset_topCell (m₁ := m₁) (L := L) (N₁ := N₁) m₀ hK hy
    obtain ⟨s, hs1, hs2⟩ := aligned_touch_offsets ha0 hadvd (aligned_cbase P.2) (aligned_cbase u)
      hx hy' hn
    have hcell : cellOfCube (L := L) m₀ m₁ P = (K, cbase a P.2) := by
      show (P.1, cbase (cellSide L m₀ m₁ P.1) P.2) = _
      rw [hP1]
    rw [hcell]
    refine Finset.mem_image.2 ⟨fun μ => ⟨(s μ + 1).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
    · have := abs_le.1 (hs1 μ); omega
    · rw [hs2]
      congr 2
      funext μ
      have := abs_le.1 (hs1 μ)
      have h2 : (((s μ + 1).toNat : ℕ) : ℤ) = s μ + 1 := Int.toNat_of_nonneg (by omega)
      simp only [h2]
      congr 2; ring
  calc _ ≤ (idxInCells G m₀ R).card := Finset.card_le_card hsub
    _ ≤ (L ^ m₀) ^ d * R.card := card_idx_in_cells_le G hN R
    _ ≤ (L ^ m₀) ^ d * 3 ^ d := Nat.mul_le_mul_left _ hR
    _ = 3 ^ d * (L ^ m₀) ^ d := mul_comm _ _

open Classical in
/-- **Non-vacuity of the general form.**  The generating set with `Ω_j = univ` for `j ≤ K` (and
`Ω_{K+1} = ∅`) satisfies the halo hypothesis at every top cell, so `root_patch_count` applies to it
for every `u`. -/
theorem root_patch_count_instance (ϱ : ℝ) :
    ∃ G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ, ∀ {m₀ : ℕ}, L ^ m₀ ∣ N₁ →
      ∀ u : CTorus d L N₁ m₁ K,
        ((cubeIdx G).filter fun P => MooreTouch (topCell m₀ (K, u)) (Pset m₁ P)).card ≤
          3 ^ d * (L ^ m₀) ^ d := by
  let G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ :=
    { Ω := fun j => if j ≤ K then Finset.univ else ∅
      top := by simp
      subset := fun j _ hjK => by
        intro x _
        simp [show j ≤ K from hjK]
      blockUnion := fun j _ hjK x x' _ => by simp [show j ≤ K from hjK]
      separation := fun j _ hjK x hx => by
        exact absurd (by simp [show j ≤ K from hjK.le]) hx }
  refine ⟨G, fun {m₀} hN u => root_patch_count G hN u fun z _ y _ => ?_⟩
  simp [G]

end Count

end Balaban.Localization

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Multiscale.GeneratingSet

set_option linter.unusedSectionVars false

section P6

variable {d M1 c n1 L k n0 m₁ m₀ : ℕ} [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} (st : RegionStep d L n0 n1 Rprev Rk)

omit [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1] in
/-- The block map does not see the identification of two equal torus sizes. -/
theorem blockMap_torusCast {ℓ ℓ' : ℕ} (h : ℓ = ℓ') (N m : ℕ) (x : Torus d ℓ) :
    blockMap N m (torusCast h x) = blockMap N m x := by
  subst h; rfl

/-- Membership in the top domain of `F♯` on the cover torus: the block of the site (cubes of side
`L ^ (K + m₁) c`) lies in the one-cube neighbourhood of the blocks over `thick Z_kᶜ`. -/
theorem mem_p6FsharpC_Ω_top (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (x : Localization.CTorus d L (c * n1) m₁ (k + 1)) :
    x ∈ (p6FsharpC (k := k) hn hρ hc Z hM1).Ω (k + 1) ↔
      blockMap (L ^ (k + 1) * (c * M1)) n1 x ∈ p6HaloCubes L n1 ρ' Z := by
  unfold p6FsharpC
  rw [castN_mem (p6_side hM1), p6Fsharp_Ω_top, mem_p6Halo, blockMap_torusCast]

omit [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1] in
/-- Sites of one cell of side `a` lie in one block of side `s` when `a ∣ s`. -/
theorem blockMap_eq_of_mem_box {ℓ a s m : ℕ} [NeZero ℓ] (ha0 : 0 < a) (ha : a ∣ ℓ)
    (hs : a ∣ s) {u x : Torus d ℓ} (hx : x ∈ Localization.box (cbase a u) a) :
    blockMap s m x = blockMap s m u := by
  have hc := cbase_eq_of_mem_box ha (aligned_cbase u) hx
  refine blockMap_eq_of_sameCell (fun μ => ?_) hs
  have h1 := congrFun hc μ
  have hlt : ∀ z : Torus d ℓ, a * ((z μ).val / a) < ℓ := fun z =>
    lt_of_le_of_lt (Nat.mul_div_le _ _) (ZMod.val_lt _)
  have h2 := congrArg ZMod.val h1
  simp only [cbase, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt _)] at h2
  exact Nat.eq_of_mul_eq_mul_left ha0 h2

omit [NeZero L] [NeZero M1] [NeZero c] [NeZero n0] [NeZero n1] in
theorem supDist_le_one_of_near {ℓ : ℕ} [NeZero ℓ] {x y : Torus d ℓ}
    (h : Fluctuation.Near 1 1 x y) : supDist y x ≤ 1 := by
  obtain ⟨q, hq, rfl⟩ := h
  refine supDist_le_iff.2 fun i => (cycNorm_le_iff _ _).2 ⟨q i, by simpa using hq i, ?_⟩
  simp

/-- **`p6_active_top_halo`** (VMOD-24 §5 row 1).  Let `u` be a site of the cover torus whose fine
lift lies over the new active region `Ω_{k+1}` of the `RegionStep` (explicit cast `torusCast`), and
let `L ^ m₀ ∣ c`.  Then every top cell equal or Moore-adjacent to the top cell of `u` lies in the top
domain `F♯.Ω (k+1)` of `F♯ = p6FsharpC`.  (The old preimage of an active cell is in `Z_kᶜ`, so the
top cell is within one top cell of the blocks over `thick Z_kᶜ`.) -/
theorem p6_active_top_halo (hM1 : M1 = L ^ m₁) (hmc : L ^ m₀ ∣ c) (hn : n0 = L * n1)
    (hL : 0 < L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hc : 5 ≤ c) (u : Localization.CTorus d L (c * n1) m₁ (k + 1))
    (hu : LargeField.torusCast (by rw [p6_side hM1] : (c * n1) * L ^ m₁ * L ^ (k + 1) =
        M1 * (c * n1) * L ^ (k + 1)) u ∈ fineK1 M1 c n1 L k st.Omega)
    (z : Localization.CTorus d L (c * n1) m₁ (k + 1))
    (hz : MooreTouch (topCell m₀ (k + 1, u)) (topCell m₀ (k + 1, z))) :
    topCell m₀ (k + 1, z) ⊆ ↑((p6FsharpC (k := k) hn hρ hc st.Z hM1).Ω (k + 1)) := by
  have hN : L ^ m₀ ∣ c * n1 := Dvd.dvd.mul_right hmc n1
  have ha0 : 0 < cellSide L m₀ m₁ (k + 1) := cellSide_pos m₀ m₁ _
  have hadvd := cellSide_dvd (L := L) (K := k + 1) (m₁ := m₁) hN le_rfl
  have hs : cellSide L m₀ m₁ (k + 1) ∣ L ^ (k + 1) * (c * M1) := by
    rw [hM1, show L ^ (k + 1) * (c * L ^ m₁) = L ^ (k + 1 + m₁) * c by rw [pow_add]; ring]
    unfold cellSide
    rw [show k + 1 + m₀ + m₁ = (k + 1 + m₁) + m₀ by ring, pow_add]
    exact mul_dvd_mul_left _ hmc
  have hℓ : (c * n1) * L ^ m₁ * L ^ (k + 1) = (L ^ (k + 1) * (c * M1)) * n1 := by
    rw [hM1]; ring
  obtain ⟨x, hx, y0, hy0, hnear⟩ := hz
  -- the block of `u` lies over `Z_kᶜ`
  set u' := LargeField.torusCast (by rw [p6_side hM1] : (c * n1) * L ^ m₁ * L ^ (k + 1) =
        M1 * (c * n1) * L ^ (k + 1)) u with hu'
  have hu1 : blockMap (L ^ (k + 1) * (c * M1)) n1 u' ∈ st.Omega := mem_fineK1.1 hu
  have hkk := blockMap_k_succ (M1 := M1) (c := c) (L := L) (k := k) hn u'
  have hv : blockMap (L ^ k * (c * M1)) n0 u' ∈ (st.Z)ᶜ :=
    st.not_mem_Z_of_mem_Omega hL hn (by rw [hkk]; exact hu1)
  intro y hy
  rw [Finset.mem_coe, mem_p6FsharpC_Ω_top hn hρ hc st.Z hM1]
  have e1 : blockMap (L ^ (k + 1) * (c * M1)) n1 y = blockMap (L ^ (k + 1) * (c * M1)) n1 y0 :=
    (blockMap_eq_of_mem_box ha0 hadvd hs hy).trans (blockMap_eq_of_mem_box ha0 hadvd hs hy0).symm
  have e2 : blockMap (L ^ (k + 1) * (c * M1)) n1 x = blockMap (L ^ (k + 1) * (c * M1)) n1 u :=
    blockMap_eq_of_mem_box ha0 hadvd hs hx
  have hd := supDist_blockMap_le (L := L ^ (k + 1) * (c * M1)) (m := n1) hℓ y0 x
  have hd1 : supDist (blockMap (L ^ (k + 1) * (c * M1)) n1 y0)
      (blockMap (L ^ (k + 1) * (c * M1)) n1 x) ≤ 1 := by
    refine hd.trans ?_
    have h1 := supDist_le_one_of_near hnear
    have hpos : 0 < L ^ (k + 1) * (c * M1) := Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero _ (NeZero.ne L))
      (mul_ne_zero (NeZero.ne c) (NeZero.ne M1)))
    rw [Nat.div_le_iff_le_mul_add_pred hpos]
    omega
  unfold p6HaloCubes
  refine mem_nbhd.2 ⟨blockMap (L ^ (k + 1) * (c * M1)) n1 u,
    ⟨blockMap (L ^ k * (c * M1)) n0 u', subset_nbhd _ _ hv, ?_⟩, ?_⟩
  · rw [hkk, hu', blockMap_torusCast]
  · rw [e1, ← e2]; exact hd1

variable {ρ' : ℕ}

/-- **`p6_touch_active_layer`** (VMOD-24 §5 row 2, layer clause).  Under the hypotheses of
`p6_active_top_halo`, an index of `cubeIdx F♯` whose parameter patch Moore-touches the top cell of
`u` has layer `k + 1`. -/
theorem p6_touch_active_layer (hM1 : M1 = L ^ m₁) (hmc : L ^ m₀ ∣ c) (hn : n0 = L * n1)
    (hL : 0 < L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hc : 5 ≤ c) (u : Localization.CTorus d L (c * n1) m₁ (k + 1))
    (hu : LargeField.torusCast (by rw [p6_side hM1] : (c * n1) * L ^ m₁ * L ^ (k + 1) =
        M1 * (c * n1) * L ^ (k + 1)) u ∈ fineK1 M1 c n1 L k st.Omega)
    {P : ℕ × Localization.CTorus d L (c * n1) m₁ (k + 1)}
    (hP : P ∈ cubeIdx (p6FsharpC (k := k) hn hρ hc st.Z hM1))
    (hT : MooreTouch (topCell m₀ (k + 1, u)) (Pset m₁ P)) : P.1 = k + 1 :=
  touch_layer_eq_top _ u (fun z hz => p6_active_top_halo st hM1 hmc hn hL hρ hc u hu z hz) hP hT

open Classical in
/-- **`p6_root_patch_count`** (VMOD-24 (1.2)).  Under the hypotheses of `p6_active_top_halo`, at
most `3 ^ d * (L ^ m₀) ^ d` indices of `cubeIdx F♯` have a parameter patch Moore-touching the active
top cell of `u`. -/
theorem p6_root_patch_count (hM1 : M1 = L ^ m₁) (hmc : L ^ m₀ ∣ c) (hn : n0 = L * n1)
    (hL : 0 < L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hc : 5 ≤ c) (u : Localization.CTorus d L (c * n1) m₁ (k + 1))
    (hu : LargeField.torusCast (by rw [p6_side hM1] : (c * n1) * L ^ m₁ * L ^ (k + 1) =
        M1 * (c * n1) * L ^ (k + 1)) u ∈ fineK1 M1 c n1 L k st.Omega) :
    ((cubeIdx (p6FsharpC (k := k) hn hρ hc st.Z hM1)).filter
        fun P => MooreTouch (topCell m₀ (k + 1, u)) (Pset m₁ P)).card ≤
      3 ^ d * (L ^ m₀) ^ d :=
  root_patch_count _ (Dvd.dvd.mul_right hmc n1) u
    (fun z hz => p6_active_top_halo st hM1 hmc hn hL hρ hc u hu z hz)

end P6

end Balaban.LargeField
