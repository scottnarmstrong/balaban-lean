/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.GraphGmDefs
public import Balaban.Localization.Vmod7Glue
public import Balaban.Localization.TreeLengthCov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The modular size lemma (GRAPH-GM-2 §3, Theorem 3.1; P3 (4.48) in modular form)

`modular_tree_of_witnesses`: given an old minimizing tree `Γ₀ ⊂ X` of the old-scale modular size
and the witness record of OPEN-P6-WITNESS-GEOMETRY (source nesting, attachment, ownership/cover),
the output `Y(𝒞)` has an admissible new chosen family and a connected structure of new-scale cost
`≤ L⁻¹ Δ + d (2L+1)^d |𝒞|`.

The proof follows GRAPH-GM-2 §3.  The source tree is retained (new-scale cost `L⁻¹` times the old
one: `bondCost_scaleW_succ`).  The generated cells are joined along the face-adjacency graph of
the cells (`zcell_walk`), each root cell to a point of `Γ₀` in the source cube it touches
(`linked_box_pair`), and the pieces are glued by `assemble`; the number of cells is at most
`G |𝒞|` (ownership), the number of roots is at most `|𝒞|`.  Explicit constants (in units of the
cell side `a`): a link between face-adjacent cells costs `≤ (d+1)/2 + 1/(2a)` (3.3); a root costs
`≤ 2dL + 2d + 1/a` (the note has `dL + 1/2`; the cruder constant comes from joining through the
corner of the source cube); the total is `≤ d G |𝒞|` since `G = (2L+1)^d ≥ 4dL + 4d` and `a ≥ 36`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Fluctuation Finset

section Arith

/-- `(2L+1)^d ≥ 4dL + 4d` for `d ≥ 3`, `L ≥ 3`. -/
theorem G_ge (d L : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) : 4 * d * L + 4 * d ≤ (2 * L + 1) ^ d := by
  have ht : 7 ≤ 2 * L + 1 := by omega
  induction d, hd using Nat.le_induction with
  | base =>
    have h2 : 49 ≤ (2 * L + 1) ^ 2 := by nlinarith
    calc 4 * 3 * L + 4 * 3 ≤ 49 * (2 * L + 1) := by nlinarith
      _ ≤ (2 * L + 1) ^ 2 * (2 * L + 1) := Nat.mul_le_mul_right _ h2
      _ = (2 * L + 1) ^ 3 := by ring
  | succ n hn ih =>
    calc 4 * (n + 1) * L + 4 * (n + 1) ≤ 7 * (4 * n * L + 4 * n) := by nlinarith
      _ ≤ (2 * L + 1) * (2 * L + 1) ^ n := Nat.mul_le_mul ht ih
      _ = (2 * L + 1) ^ (n + 1) := by ring

/-- The numerical heart of `modular_tree_of_witnesses`: the root cost plus the link cost per cell
times `G` is at most `d G`. -/
theorem tree_arith (d L a G : ℝ) (c0 : ℝ) (hd : 3 ≤ d) (hL : 3 ≤ L) (hc0 : 0 < c0)
    (ha : c0 ≤ 1 / 36) (hac : a * c0 = 1) (hG : 4 * d * L + 4 * d ≤ G) :
    2 * (d * (L * a) * c0) + c0 + 2 * (d * a * c0) + ((d + 1) / 2 + c0 / 2) * G ≤ d * G := by
  have e1 : 2 * (d * (L * a) * c0) = 2 * d * L := by
    have : d * (L * a) * c0 = d * L * (a * c0) := by ring
    rw [this, hac]; ring
  have e2 : 2 * (d * a * c0) = 2 * d := by
    have : d * a * c0 = d * (a * c0) := by ring
    rw [this, hac]; ring
  rw [e1, e2]
  have hG0 : 0 ≤ G := by nlinarith
  have h1 : c0 * G ≤ G / 36 := by nlinarith
  have h2 : 0 ≤ (d - 3) * G := mul_nonneg (by linarith) hG0
  nlinarith

end Arith

section Lift

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- The layered cells: boxes of side `cellSide n`, `n ≤ K`, with base divisible by the side. -/
def ZCell.Layered (L m₀ m₁ K : ℕ) (c : ZCell d) : Prop :=
  ∃ n ≤ K, c.side = cellSide L m₀ m₁ n ∧ ∀ μ, ((c.side : ℕ) : ℤ) ∣ c.base μ

/-- Layered cells exist (the typing data `Layered` is inhabited). -/
theorem ZCell.layered_exists (L m₀ m₁ K d : ℕ) : ∃ c : ZCell d, c.Layered L m₀ m₁ K :=
  ⟨⟨0, cellSide L m₀ m₁ 0⟩, 0, Nat.zero_le _, rfl, fun _ => dvd_zero _⟩

theorem scaleW_eq_cellSide (L m₀ m₁ j : ℕ) {α : Type*} (x y : α) :
    scaleW L m₀ m₁ j x y = ((cellSide L m₀ m₁ j : ℕ) : ℝ)⁻¹ := by
  unfold scaleW cellSide
  push_cast
  congr 2
  ring

theorem bondCost_scaleW_succ {n : ℕ} (L m₀ m₁ k : ℕ) (E : Finset (Torus d n × Torus d n)) :
    bondCost (scaleW L m₀ m₁ (k + 1)) E = (L : ℝ)⁻¹ * bondCost (scaleW L m₀ m₁ k) E := by
  unfold bondCost
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold scaleW
  rw [show m₀ + m₁ + (k + 1) = (m₀ + m₁ + k) + 1 by ring, pow_succ, mul_inv]
  ring

omit [NeZero N₁] [NeZero L] in
/-- A walk in a union of integer cells gives a linked pair in the torus. -/
theorem zwalk_linked {R : Set (CTorus d L N₁ m₁ K)} {ω : CTorus d L N₁ m₁ K → CTorus d L N₁ m₁ K → ℝ}
    (hω0 : ∀ x y, 0 ≤ ω x y) {c : ℝ} (hωc : ∀ x y, ω x y ≤ c)
    {Rz : Set (Fin d → ℤ)} (hR : ∀ z ∈ Rz, zTorus L N₁ m₁ K z ∈ R) {x y : Fin d → ℤ} {ℓ : ℕ}
    (h : ZWalk Rz x y ℓ) :
    Linked R ω (ℓ * c) (zTorus L N₁ m₁ K x) (zTorus L N₁ m₁ K y) := by
  induction h with
  | refl hx =>
    simpa using Linked.refl (R := R) (ω := ω) (c := ((0 : ℕ) : ℝ) * c) (by simp) (hR _ hx)
  | @step x y z ℓ hx hs w ih =>
    have h1 : Linked R ω c (zTorus L N₁ m₁ K x) (zTorus L N₁ m₁ K y) :=
      Linked.step (nbr_zTorus hs) (hR _ hx) (hR _ w.mem_left) (hωc _ _)
    have := Linked.trans hω0 h1 ih
    refine Covers.mono_c this (le_of_eq ?_)
    push_cast; ring

end Lift

section Main

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- Adjacency in the nerve of the generated cells together with the source tree (`none`): a root
cell is adjacent to the source tree, cells are adjacent when they are face-adjacent. -/
def nerveAdj (roots : Finset (ZCell d)) : Option (ZCell d) → Option (ZCell d) → Prop
  | none, some g => g ∈ roots
  | some g, none => g ∈ roots
  | some g, some g' => ZFaceAdj g g'
  | none, none => False

/-- **The modular size lemma (GRAPH-GM-2 Theorem 3.1, (3.1)), conditional on the witness record
(`modular_tree_of_witnesses`).**  `K = k + 1`.  `(W₀, E₀)` is an admissible old pair for
`(X, Ωk)` at scale `k` (a chosen old family `𝒦X` and a connected structure `Γ₀ ⊂ X` meeting it);
`Q0` are the lifts of the source `π'_{k+1}`-cubes (side `L M L^{k+1}`) and `B = ⋃ Q0`; `C` are the
retained derivative cubes, `D P` the cells generated by the completion of `P` and `home P ∈ D P`
the one containing `P`; `Kgen` is the `π'_{k+1}`-cover of the generated pieces.  The named
geometric assertions (OPEN-P6-WITNESS-GEOMETRY), all hypotheses here:

* source nesting: `hSN` (every source cube contains an old chosen cube, hence is met by `Γ₀`) and
  `hSB` (`X ∩ Ω ⊂ B`, no uncharged collar);
* attachment: `hatt` (every generated cell is reached by a face-adjacent chain of generated cells
  from the cell containing a derivative cube that face-touches a source cube);
* ownership and cover: `hcard` (`|D P| ≤ G = (2L+1)^d`), `hcov` (the generated cells are covered by
  `Kgen`), `hKgen` (every cube of `Kgen` lies in `Y`, is aligned, and is a source cube or contains a
  generated cell).

The rest are typing data: `hQtype` (source cubes are aligned boxes of side `L a`, `a = M L^{k+1}`),
`hlayer` (generated cells are aligned boxes of some layer `n ≤ K`), `hP` (derivative cubes are
non-degenerate), `hhome`.  Conclusion: `Y(𝒞)` has an admissible new chosen family and tree of
new-scale cost `≤ L⁻¹ cost(Γ₀) + d (2L+1)^d |𝒞|`. -/
theorem modular_tree_of_witnesses {m₀ k : ℕ} (hK : k + 1 = K) (hN : L ^ m₀ ∣ N₁)
    (hL : 3 ≤ L) (hd : 3 ≤ d) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (Ω Ωk X 𝒦X : Set (CTorus d L N₁ m₁ K)) (W₀ : Finset (CTorus d L N₁ m₁ K))
    (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K))
    (hΓ : ModAdmissible m₀ k Ωk X 𝒦X W₀ E₀)
    (Q0 : Finset (ZCell d))
    (hQtype : ∀ Q ∈ Q0, Q.side = L * cellSide L m₀ m₁ K ∧
      ∀ μ, ((cellSide L m₀ m₁ K : ℕ) : ℤ) ∣ Q.base μ)
    (hSN : ∀ Q ∈ Q0, ∃ q ∈ 𝒦X, box q (L * cellSide L m₀ m₁ k) ⊆ Q.sites L N₁ m₁ K)
    (hSB : X ∩ Ω ⊆ ⋃ Q ∈ Q0, Q.sites L N₁ m₁ K)
    (C : Finset (ZCell d)) (D : ZCell d → Finset (ZCell d)) (home : ZCell d → ZCell d)
    (hP : ∀ P ∈ C, 0 < P.side)
    (hhome : ∀ P ∈ C, home P ∈ D P ∧ P.pts ⊆ (home P).pts)
    (hlayer : ∀ P ∈ C, ∀ g ∈ D P, g.Layered L m₀ m₁ K)
    (hcard : ∀ P ∈ C, (D P).card ≤ (2 * L + 1) ^ d)
    (hatt : ∀ g ∈ C.biUnion D, ∃ P₀ ∈ C, (∃ Q ∈ Q0, ZFaceAdj Q P₀) ∧
      Relation.ReflTransGen (fun u v => u ∈ C.biUnion D ∧ v ∈ C.biUnion D ∧ ZFaceAdj u v)
        (home P₀) g)
    (Kgen : Finset (CTorus d L N₁ m₁ K))
    (hKgen : ∀ b ∈ Kgen, Aligned (cellSide L m₀ m₁ K) b ∧
      box b (L * cellSide L m₀ m₁ K) ⊆ outputY L N₁ m₁ K Ω X Q0 C D ∧
      (b ∈ Q0.image (fun Q => zTorus L N₁ m₁ K Q.base) ∨
        ∃ g ∈ C.biUnion D, g.sites L N₁ m₁ K ⊆ box b (L * cellSide L m₀ m₁ K)))
    (hcov : ∀ g ∈ C.biUnion D, g.sites L N₁ m₁ K ⊆ ⋃ b ∈ Kgen, box b (L * cellSide L m₀ m₁ K)) :
    ∃ (𝒦 : Set (CTorus d L N₁ m₁ K)) (W : Finset (CTorus d L N₁ m₁ K))
      (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ModAdmissible m₀ K Ω (outputY L N₁ m₁ K Ω X Q0 C D) 𝒦 W E ∧
      bondCost (scaleW L m₀ m₁ K) E ≤
        bondCost (scaleW L m₀ m₁ k) E₀ / L + d * (((2 * L + 1) ^ d : ℕ) : ℝ) * C.card := by
  classical
  subst hK
  have hL0 : 0 < L := by omega
  set a := cellSide L m₀ m₁ (k + 1) with ha
  have ha0 : 0 < a := cellSide_pos m₀ m₁ (k + 1)
  have ha36 : 36 ≤ a := by
    have h1 : L ^ m₁ ≤ a := by
      rw [ha]; unfold cellSide
      exact Nat.pow_le_pow_right hL0 (by omega)
    have h2 : 9 ≤ L ^ 2 := by nlinarith
    omega
  have had : a ∣ (N₁ * L ^ m₁) * L ^ (k + 1) := cellSide_dvd hN le_rfl
  set c0 : ℝ := (a : ℝ)⁻¹ with hc0
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha0
  have hac : (a : ℝ) * c0 = 1 := by rw [hc0]; field_simp
  have hc0pos : 0 < c0 := by rw [hc0]; positivity
  have hc0le : c0 ≤ 1 / 36 := by
    rw [hc0]
    have : (36 : ℝ) ≤ a := by exact_mod_cast ha36
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) this
  set Y := outputY L N₁ m₁ (k + 1) Ω X Q0 C D with hY
  set 𝒢 := C.biUnion D with h𝒢
  set ω : CTorus d L N₁ m₁ (k + 1) → CTorus d L N₁ m₁ (k + 1) → ℝ :=
    scaleW L m₀ m₁ (k + 1) with hω
  have hωc : ∀ x y, ω x y = c0 := fun x y => scaleW_eq_cellSide L m₀ m₁ (k + 1) x y
  have hω0 : ∀ x y, 0 ≤ ω x y := fun x y => by rw [hωc]; exact hc0pos.le
  have hωcc : ∀ x ∈ Y, ∀ y ∈ Y, ω x y ≤ c0 := fun x _ y _ => (hωc x y).le
  -- generated cells
  have hgY : ∀ g ∈ 𝒢, g.sites L N₁ m₁ (k + 1) ⊆ Y := by
    intro g hg
    obtain ⟨P, hP', hgP⟩ := Finset.mem_biUnion.1 hg
    exact cell_subset_outputY Ω X Q0 C D hP' hgP
  have hglay : ∀ g ∈ 𝒢, g.Layered L m₀ m₁ (k + 1) := by
    intro g hg
    obtain ⟨P, hP', hgP⟩ := Finset.mem_biUnion.1 hg
    exact hlayer P hP' g hgP
  have hgpos : ∀ g ∈ 𝒢, 0 < g.side := by
    intro g hg
    obtain ⟨n, -, hn, -⟩ := hglay g hg
    rw [hn]; exact cellSide_pos m₀ m₁ n
  have hgle : ∀ g ∈ 𝒢, g.side ≤ a := by
    intro g hg
    obtain ⟨n, hnK, hn, -⟩ := hglay g hg
    rw [hn, ha]; unfold cellSide
    exact Nat.pow_le_pow_right hL0 (by omega)
  have hgnest : ∀ g ∈ 𝒢, ∀ g' ∈ 𝒢, ((g'.side : ℕ) : ℤ) ∣ (g.side : ℤ) ∨
      ((g.side : ℕ) : ℤ) ∣ (g'.side : ℤ) := by
    intro g hg g' hg'
    obtain ⟨n, -, hn, -⟩ := hglay g hg
    obtain ⟨n', -, hn', -⟩ := hglay g' hg'
    rw [hn, hn']
    unfold cellSide
    rcases le_total n n' with h | h
    · right
      exact_mod_cast pow_dvd_pow L (by omega : n + m₀ + m₁ ≤ n' + m₀ + m₁)
    · left
      exact_mod_cast pow_dvd_pow L (by omega : n' + m₀ + m₁ ≤ n + m₀ + m₁)
  -- source cubes
  have hQY : ∀ Q ∈ Q0, Q.sites L N₁ m₁ (k + 1) ⊆ Y := fun Q hQ =>
    source_subset_outputY Ω X Q0 C D hQ
  have hQbox : ∀ Q ∈ Q0, Q.sites L N₁ m₁ (k + 1) =
      box (zTorus L N₁ m₁ (k + 1) Q.base) (L * a) := fun Q hQ => by
    rw [ZCell.sites_eq_box, (hQtype Q hQ).1]
  -- the tree `Γ₀` meets every source cube
  have hmeetQ : ∀ Q ∈ Q0, ∃ p ∈ W₀, p ∈ Q.sites L N₁ m₁ (k + 1) := by
    intro Q hQ
    obtain ⟨q, hq, hqQ⟩ := hSN Q hQ
    obtain ⟨p, hp, hpq⟩ := hΓ.2.2.2.2 q hq
    exact ⟨p, hp, hqQ hpq⟩
  -- the roots and the cost of attaching a root to `Γ₀`
  set Aatt : ℝ := 2 * ((d : ℝ) * ((L : ℝ) * a) * c0) + c0 + 2 * ((d : ℝ) * a * c0) with hAatt
  set roots : Finset (ZCell d) :=
    (C.filter fun P => ∃ Q ∈ Q0, ZFaceAdj Q P).image home with hroots
  have hroot : ∀ g ∈ roots, g ∈ 𝒢 ∧ ∃ p ∈ W₀, Linked Y ω Aatt p (zTorus L N₁ m₁ (k + 1) g.rep) := by
    intro g hg
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨hP₀C, Q, hQ, hQP⟩ := Finset.mem_filter.1 hP₀
    obtain ⟨hh1, hh2⟩ := hhome P₀ hP₀C
    have hg𝒢 : home P₀ ∈ 𝒢 := Finset.mem_biUnion.2 ⟨P₀, hP₀C, hh1⟩
    refine ⟨hg𝒢, ?_⟩
    obtain ⟨p, hpW, hpQ⟩ := hmeetQ Q hQ
    have hQs : 0 < Q.side := by rw [(hQtype Q hQ).1]; positivity
    obtain ⟨u, hu, v, hv, huv⟩ := hQP.exists_step hQs (hP P₀ hP₀C)
    have hvg : v ∈ (home P₀).pts := hh2 hv
    refine ⟨p, hpW, ?_⟩
    have hbox := hQbox Q hQ
    have hQb : box (zTorus L N₁ m₁ (k + 1) Q.base) (L * a) ⊆ Y := by
      rw [← hbox]; exact hQY Q hQ
    have hpb : p ∈ box (zTorus L N₁ m₁ (k + 1) Q.base) (L * a) := by rw [← hbox]; exact hpQ
    have hub : zTorus L N₁ m₁ (k + 1) u ∈ box (zTorus L N₁ m₁ (k + 1) Q.base) (L * a) := by
      rw [← hbox]; exact ⟨u, hu, rfl⟩
    have l1 := linked_box_pair hω0 (zTorus L N₁ m₁ (k + 1) Q.base) (L * a) hQb hωcc hpb hub
    have huY : zTorus L N₁ m₁ (k + 1) u ∈ Y := hQb hub
    have hvY : zTorus L N₁ m₁ (k + 1) v ∈ Y := hgY _ hg𝒢 ⟨v, hvg, rfl⟩
    have l2 : Linked Y ω c0 (zTorus L N₁ m₁ (k + 1) u) (zTorus L N₁ m₁ (k + 1) v) :=
      Linked.step (nbr_zTorus huv) huY hvY (hωc _ _).le
    have hgs := ZCell.sites_eq_box (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) (home P₀)
    have hgb : box (zTorus L N₁ m₁ (k + 1) (home P₀).base) (home P₀).side ⊆ Y := by
      rw [← hgs]; exact hgY _ hg𝒢
    have hvb : zTorus L N₁ m₁ (k + 1) v ∈ box (zTorus L N₁ m₁ (k + 1) (home P₀).base)
        (home P₀).side := by rw [← hgs]; exact ⟨v, hvg, rfl⟩
    have hrb : zTorus L N₁ m₁ (k + 1) (home P₀).rep ∈
        box (zTorus L N₁ m₁ (k + 1) (home P₀).base) (home P₀).side := by
      rw [← hgs]; exact (home P₀).rep_mem_sites (hgpos _ hg𝒢)
    have l3 := linked_box_pair hω0 (zTorus L N₁ m₁ (k + 1) (home P₀).base) (home P₀).side hgb hωcc
      hvb hrb
    have := Linked.trans hω0 (Linked.trans hω0 l1 l2) l3
    refine Covers.mono_c this ?_
    have hgle' : ((home P₀).side : ℝ) ≤ a := by exact_mod_cast hgle _ hg𝒢
    have hc3 : 2 * ((d : ℝ) * ((home P₀).side : ℕ) * c0) ≤ 2 * ((d : ℝ) * a * c0) := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
      gcongr
    have : 2 * ((d : ℝ) * ((L * a : ℕ) : ℝ) * c0) = 2 * ((d : ℝ) * ((L : ℝ) * a) * c0) := by
      push_cast; ring
    rw [hAatt]
    linarith
  -- the cover of each generated cell (and its attachment to `Γ₀` if it is a root)
  have hnode : ∀ g ∈ 𝒢, ∃ A : Finset (CTorus d L N₁ m₁ (k + 1)),
      zTorus L N₁ m₁ (k + 1) g.rep ∈ A ∧
      Covers Y ω (if g ∈ roots then Aatt else 0) A ∧ (g ∈ roots → ∃ p ∈ W₀, p ∈ A) := by
    intro g hg
    have hrepY : zTorus L N₁ m₁ (k + 1) g.rep ∈ Y := hgY g hg (g.rep_mem_sites (hgpos g hg))
    by_cases hgr : g ∈ roots
    · obtain ⟨-, p, hpW, hlk⟩ := hroot g hgr
      refine ⟨{p, zTorus L N₁ m₁ (k + 1) g.rep}, by simp, ?_, fun _ => ⟨p, hpW, by simp⟩⟩
      simp only [hgr, ↓reduceIte]; exact hlk
    · refine ⟨{zTorus L N₁ m₁ (k + 1) g.rep}, by simp, ?_, fun h => absurd h hgr⟩
      simp only [hgr, ↓reduceIte]
      refine ⟨{zTorus L N₁ m₁ (k + 1) g.rep}, ∅, connStruct_singleton _, ?_, subset_rfl, ?_⟩
      · simpa using hrepY
      · simp [bondCost]
  choose! Anode hAn1 hAn2 hAn3 using hnode
  -- the old tree, rescaled
  set σ₀ : ℝ := (L : ℝ)⁻¹ * bondCost (scaleW L m₀ m₁ k) E₀ with hσ₀
  have hX_Y : X ⊆ Y := X_subset_outputY Ω X Q0 C D
  have cov₀ : Covers Y ω σ₀ W₀ := by
    refine ⟨W₀, E₀, hΓ.2.2.1, fun x hx => hX_Y (hΓ.2.2.2.1 hx), subset_rfl, ?_⟩
    rw [hσ₀, hω, bondCost_scaleW_succ]
  -- the link between face-adjacent cells
  set ρ : ℝ := ((d : ℝ) + 1) / 2 + c0 / 2 with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hlinkcell : ∀ g ∈ 𝒢, ∀ g' ∈ 𝒢, ZFaceAdj g g' →
      Linked Y ω ρ (zTorus L N₁ m₁ (k + 1) g.rep) (zTorus L N₁ m₁ (k + 1) g'.rep) := by
    intro g hg g' hg' hadj
    obtain ⟨ℓ, hℓ, hw⟩ := zcell_walk g g' (hgpos g hg) (hgpos g' hg') (hgnest g hg g' hg')
      (fun μ => (hglay g hg).choose_spec.2.2 μ) (fun μ => (hglay g' hg').choose_spec.2.2 μ) hadj
    have hR : ∀ z ∈ g.pts ∪ g'.pts, zTorus L N₁ m₁ (k + 1) z ∈ Y := by
      rintro z (hz | hz)
      · exact hgY g hg ⟨z, hz, rfl⟩
      · exact hgY g' hg' ⟨z, hz, rfl⟩
    have := zwalk_linked hω0 (fun x y => (hωc x y).le) hR hw
    refine Covers.mono_c this ?_
    have hmax : max g.side g'.side ≤ a := max_le (hgle g hg) (hgle g' hg')
    have h1 : (2 * ℓ : ℝ) ≤ ((d : ℝ) + 1) * a + 1 := by
      have : 2 * ℓ ≤ (d + 1) * a + 1 :=
        hℓ.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hmax) 1)
      exact_mod_cast this
    have h2 : (ℓ : ℝ) * c0 ≤ ρ := by
      rw [hρ]
      have : (2 * ℓ : ℝ) * c0 ≤ (((d : ℝ) + 1) * a + 1) * c0 := by gcongr
      nlinarith
    exact h2
  -- assembly along the nerve
  let σ : Option (ZCell d) → ℝ := fun o => o.elim σ₀ (fun g => if g ∈ roots then Aatt else 0)
  let A' : Option (ZCell d) → Finset (CTorus d L N₁ m₁ (k + 1)) :=
    fun o => o.elim W₀ Anode
  have hreach : ∀ v ∈ Finset.insertNone 𝒢, Relation.ReflTransGen
      (fun u v => nerveAdj roots u v ∧ u ∈ Finset.insertNone 𝒢 ∧ v ∈ Finset.insertNone 𝒢) none v := by
    intro v hv
    cases v with
    | none => exact Relation.ReflTransGen.refl
    | some g =>
      have hg : g ∈ 𝒢 := Finset.some_mem_insertNone.1 hv
      obtain ⟨P₀, hP₀, hQP, hchain⟩ := hatt g hg
      have hroot' : home P₀ ∈ roots :=
        Finset.mem_image.2 ⟨P₀, Finset.mem_filter.2 ⟨hP₀, hQP⟩, rfl⟩
      have hroot𝒢 : home P₀ ∈ 𝒢 := (hroot _ hroot').1
      have h1 : Relation.ReflTransGen
          (fun u v => nerveAdj roots u v ∧ u ∈ Finset.insertNone 𝒢 ∧ v ∈ Finset.insertNone 𝒢)
          (some (home P₀)) (some g) := by
        refine hchain.lift some ?_
        intro x y ⟨hx, hy, hxy⟩
        exact ⟨hxy, Finset.some_mem_insertNone.2 hx, Finset.some_mem_insertNone.2 hy⟩
      refine Relation.ReflTransGen.head ?_ h1
      exact ⟨hroot', Finset.none_mem_insertNone, Finset.some_mem_insertNone.2 hroot𝒢⟩
  have key := assemble (R := Y) (ω := ω) hω0 (Finset.insertNone 𝒢) (nerveAdj roots) none
    Finset.none_mem_insertNone hreach A' σ ?_ ρ ?_
  rotate_left
  · intro o ho
    cases o with
    | none => exact cov₀
    | some g => exact hAn2 g (Finset.some_mem_insertNone.1 ho)
  · intro u hu v hv huv
    cases u with
    | none =>
      cases v with
      | none => exact absurd huv (by simp [nerveAdj])
      | some g =>
        have hgr : g ∈ roots := huv
        obtain ⟨p, hpW, hpA⟩ := hAn3 g (Finset.some_mem_insertNone.1 hv) hgr
        exact ⟨p, hpW, p, hpA, Linked.refl hρ0 (hX_Y (hΓ.2.2.2.1 hpW))⟩
    | some g =>
      cases v with
      | none =>
        have hgr : g ∈ roots := huv
        obtain ⟨p, hpW, hpA⟩ := hAn3 g (Finset.some_mem_insertNone.1 hu) hgr
        exact ⟨p, hpA, p, hpW, Linked.refl hρ0 (hX_Y (hΓ.2.2.2.1 hpW))⟩
      | some g' =>
        have hg := Finset.some_mem_insertNone.1 hu
        have hg' := Finset.some_mem_insertNone.1 hv
        exact ⟨_, hAn1 g hg, _, hAn1 g' hg', hlinkcell g hg g' hg' huv⟩
  obtain ⟨W, E, hconn, hWY, hAW, hcost⟩ := key
  -- the cost
  have hsum : ∑ o ∈ Finset.insertNone 𝒢, σ o =
      σ₀ + ∑ g ∈ 𝒢, (if g ∈ roots then Aatt else 0) := by
    rw [Finset.sum_insertNone]
    rfl
  have hcardS : ((Finset.insertNone 𝒢).card : ℝ) - 1 = 𝒢.card := by
    rw [Finset.card_insertNone]; push_cast; ring
  have hAtt0 : 0 ≤ Aatt := by rw [hAatt]; positivity
  have hrootsC : roots.card ≤ C.card :=
    Finset.card_image_le.trans (Finset.card_filter_le _ _)
  have hsumroot : ∑ g ∈ 𝒢, (if g ∈ roots then Aatt else 0) ≤ Aatt * C.card := by
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
    have h1 : ((𝒢 ∩ roots).card : ℝ) ≤ C.card := by
      exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans hrootsC
    nlinarith
  have h𝒢card : (𝒢.card : ℝ) ≤ (((2 * L + 1) ^ d : ℕ) : ℝ) * C.card := by
    have h1 : 𝒢.card ≤ ∑ P ∈ C, (D P).card := Finset.card_biUnion_le
    have h2 : ∑ P ∈ C, (D P).card ≤ C.card * (2 * L + 1) ^ d := by
      calc ∑ P ∈ C, (D P).card ≤ ∑ _P ∈ C, (2 * L + 1) ^ d :=
            Finset.sum_le_sum fun P hP' => hcard P hP'
        _ = C.card * (2 * L + 1) ^ d := by rw [Finset.sum_const, smul_eq_mul]
    have : (𝒢.card : ℝ) ≤ ((C.card * (2 * L + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast h1.trans h2
    rw [mul_comm]; exact_mod_cast this
  set Gr : ℝ := (((2 * L + 1) ^ d : ℕ) : ℝ) with hGr
  have hGge : 4 * (d : ℝ) * L + 4 * d ≤ Gr := by
    have := G_ge d L hd hL
    rw [hGr]; exact_mod_cast this
  have harith := tree_arith (d : ℝ) (L : ℝ) (a : ℝ) Gr c0 (by exact_mod_cast hd) (by exact_mod_cast hL)
    hc0pos hc0le hac hGge
  have hcostE : bondCost ω E ≤ σ₀ + d * Gr * C.card := by
    rw [hsum, hcardS] at hcost
    have hC0 : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
    have h1 : (𝒢.card : ℝ) * ρ ≤ Gr * C.card * ρ := mul_le_mul_of_nonneg_right h𝒢card hρ0
    have h2 : (Aatt + ρ * Gr) * C.card ≤ d * Gr * C.card :=
      mul_le_mul_of_nonneg_right (by rw [hρ, hAatt]; linarith) hC0
    nlinarith
  -- the admissible pair
  refine ⟨(↑(Q0.image fun Q => zTorus L N₁ m₁ (k + 1) Q.base) : Set _) ∪ ↑Kgen, W, E, ?_, ?_⟩
  · refine ⟨?_, ?_, hconn, hWY, ?_⟩
    · intro b hb
      rcases hb with hb | hb
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
        refine ⟨aligned_zTorus had (hQtype Q hQ).2, ?_⟩
        rw [← hQbox Q hQ]; exact hQY Q hQ
      · exact ⟨(hKgen b hb).1, (hKgen b hb).2.1⟩
    · intro x hx
      obtain ⟨hxY, hxΩ⟩ := hx
      rcases outputY_inter Ω X Q0 C D ⟨hxY, hxΩ⟩ with (hx | hx) | hx
      · obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.1 (hSB ⟨hx, hxΩ⟩)
        refine Set.mem_iUnion₂.2 ⟨zTorus L N₁ m₁ (k + 1) Q.base,
          Or.inl (Finset.mem_coe.2 (Finset.mem_image.2 ⟨Q, hQ, rfl⟩)), ?_⟩
        rw [← hQbox Q hQ]; exact hxQ
      · obtain ⟨Q, hQ, hxQ⟩ := Set.mem_iUnion₂.1 hx
        refine Set.mem_iUnion₂.2 ⟨zTorus L N₁ m₁ (k + 1) Q.base,
          Or.inl (Finset.mem_coe.2 (Finset.mem_image.2 ⟨Q, hQ, rfl⟩)), ?_⟩
        rw [← hQbox Q hQ]; exact hxQ
      · obtain ⟨P, hP', hx'⟩ := Set.mem_iUnion₂.1 hx
        obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 hx'
        obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.1
          (hcov g (Finset.mem_biUnion.2 ⟨P, hP', hg⟩) hxg)
        exact Set.mem_iUnion₂.2 ⟨b, Or.inr (Finset.mem_coe.2 hb), hxb⟩
    · intro b hb
      have hQcase : ∀ Q ∈ Q0, ∃ x ∈ W, x ∈ box (zTorus L N₁ m₁ (k + 1) Q.base) (L * a) := by
        intro Q hQ
        obtain ⟨p, hpW, hpQ⟩ := hmeetQ Q hQ
        refine ⟨p, hAW ?_, ?_⟩
        · exact Finset.mem_biUnion.2 ⟨none, Finset.none_mem_insertNone, hpW⟩
        · rw [← hQbox Q hQ]; exact hpQ
      rcases hb with hb | hb
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
        exact hQcase Q hQ
      · rcases (hKgen b hb).2.2 with hb' | ⟨g, hg, hgb⟩
        · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hb'
          exact hQcase Q hQ
        · refine ⟨zTorus L N₁ m₁ (k + 1) g.rep, hAW ?_, hgb (g.rep_mem_sites (hgpos g hg))⟩
          exact Finset.mem_biUnion.2 ⟨some g, Finset.some_mem_insertNone.2 hg, hAn1 g hg⟩
  · have : bondCost (scaleW L m₀ m₁ (k + 1)) E ≤ σ₀ + d * Gr * C.card := hcostE
    rw [hσ₀] at this
    rw [div_eq_inv_mul]
    exact this

end Main

end Balaban.Localization
