module

public import Balaban.Multiscale.GeneratingSet
public import Balaban.LargeField.Geometry.DomainsMod
public import Balaban.Green.BlockDistance
public import Balaban.Green.MassLipschitz
public import Balaban.LargeField.Region.Overwrite
import Mathlib.Tactic.Linarith

/-!
# The chain graph of a generating set (Part III, Definition III.4.1, Lemma III.4.2)

On the fine torus `T = Torus d (N₀ * L ^ k)` with a generating set `G` (layers
`Λ_i = Ω_i ∖ Ω_{i+1}`), a *block vertex* is a pair `(i, b)` with `b` an `i`-block (a block of side
`L ^ i`, `Multiscale.jBlock`).  Given the fine set `Zc` of the core `Z_{k₁}` and the fine set `Zf`
of the component `Z`:

* the *window blocks* of layer `i`, `k₁ ≤ i < k`, are the `i`-blocks contained in `Λ_i ∖ Zc`;
* the *terminal blocks* are the `k`-blocks contained in `Ω_k ∩ Zf`;
* *intra edges* join two different `i`-blocks containing nearest-neighbour sites;
* a *cross edge* joins an `(i+1)`-block `b₊` and an `i`-block `y'` contained in an `(i+1)`-block `b₋`
  which is nearest-neighbour adjacent to `b₊` and disjoint from `Ω_{i+1}`.

`nn_layers_adj` (Lemma III.4.2 (b)) and `crossPair_window` (Lemma III.4.2 (a)) show that
nearest-neighbour sites lie in layers differing by at most one and give a cross edge when the layers
differ.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Multiscale

/-! ### Distances -/

section Dist

variable {d m : ℕ} [NeZero m]

theorem torusDist_nnAdj_le {x y : Torus d m} (h : NNAdj x y) : Green.torusDist d m x y ≤ 1 := by
  obtain ⟨μ, hμ⟩ := h
  have key : ∀ i : Fin d, ((Green.cycRep (x i - y i)).natAbs : ℝ) ≤ if i = μ then 1 else 0 := by
    intro i
    have hi : ∃ t : ℤ, ((t : ℤ) : ZMod m) = x i - y i ∧ t.natAbs ≤ (if i = μ then 1 else 0) := by
      rcases hμ with hμ | hμ
      · by_cases hiμ : i = μ
        · subst hiμ
          refine ⟨-1, ?_, by simp⟩
          rw [hμ]; simp
        · refine ⟨0, ?_, by simp [hiμ]⟩
          rw [hμ]; simp [hiμ]
      · by_cases hiμ : i = μ
        · subst hiμ
          refine ⟨1, ?_, by simp⟩
          rw [hμ]; simp
        · refine ⟨0, ?_, by simp [hiμ]⟩
          rw [hμ]; simp [hiμ]
    obtain ⟨t, ht, hle⟩ := hi
    have := Green.natAbs_cycRep_le_of_cast (x i - y i) t ht
    have h2 : (Green.cycRep (x i - y i)).natAbs ≤ (if i = μ then 1 else 0) := this.trans hle
    split_ifs at h2 ⊢ <;> exact_mod_cast h2
  unfold Green.torusDist
  calc ∑ i, ((Green.cycRep (x i - y i)).natAbs : ℝ) ≤ ∑ i : Fin d, (if i = μ then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun i _ => key i
    _ = 1 := by simp

end Dist

/-! ### Blocks, window and terminal blocks, the chain graph -/

section Chain

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- A block vertex: a layer `i` and an `i`-block (a block of side `L ^ i` of the fine torus). -/
abbrev BlockV (d L N₀ k : ℕ) : Type := Σ i : ℕ, Torus d (N₀ * L ^ (k - i))

/-- The fine sites of a block. -/
def BlockV.sites (b : BlockV d L N₀ k) : Set (Torus d (N₀ * L ^ k)) :=
  {x | jBlock d L N₀ k b.1 x = b.2}

/-- The block of layer `i` containing the site `x`. -/
def blockOf (d L N₀ k i : ℕ) (x : Torus d (N₀ * L ^ k)) : BlockV d L N₀ k := ⟨i, jBlock d L N₀ k i x⟩

theorem mem_blockOf_sites (i : ℕ) (x : Torus d (N₀ * L ^ k)) : x ∈ (blockOf d L N₀ k i x).sites :=
  rfl

theorem blockOf_sites_iff {i : ℕ} {x y : Torus d (N₀ * L ^ k)} :
    y ∈ (blockOf d L N₀ k i x).sites ↔ jBlock d L N₀ k i y = jBlock d L N₀ k i x := Iff.rfl

variable (G : GeneratingSet d L N₀ k ϱ)

/-- **Definition III.4.1**: the *window blocks* of layer `i` (`k₁ ≤ i < k`): the `i`-blocks contained
in `Λ_i ∖ Z_{k₁}` (`Zc` is the fine set of `Z_{k₁}`). -/
def IsWindowBlock (Zc : Set (Torus d (N₀ * L ^ k))) (k1 : ℕ) (b : BlockV d L N₀ k) : Prop :=
  k1 ≤ b.1 ∧ b.1 < k ∧ ∀ x ∈ b.sites, x ∈ G.layer b.1 ∧ x ∉ Zc

/-- **Definition III.4.1**: the *terminal blocks*: the `k`-blocks contained in `Ω_k ∩ Z`
(`Zf` is the fine set of `Z`). -/
def IsTerminalBlock (Zf : Set (Torus d (N₀ * L ^ k))) (b : BlockV d L N₀ k) : Prop :=
  b.1 = k ∧ ∀ x ∈ b.sites, x ∈ G.Ω k ∧ x ∈ Zf

/-- **Definition III.4.1**: *intra edges*: two different blocks of the same layer containing
nearest-neighbour sites (nearest-neighbour translates `y' = y ± L ^ i e_m`). -/
def IntraAdj (b b' : BlockV d L N₀ k) : Prop :=
  b.1 = b'.1 ∧ b ≠ b' ∧ ∃ x ∈ b.sites, ∃ y ∈ b'.sites, NNAdj x y

/-- **Definition III.4.1**: *cross edges*: an `(i+1)`-block `b₊` and an `i`-block `y'` contained in
an `(i+1)`-block `b₋` that is nearest-neighbour adjacent to `b₊` and disjoint from `Ω_{i+1}`. -/
def CrossAdj (bp y : BlockV d L N₀ k) : Prop :=
  y.1 + 1 = bp.1 ∧ ∃ x ∈ bp.sites, ∃ x'', NNAdj x x'' ∧ x'' ∉ G.Ω bp.1 ∧
    ∃ x' ∈ y.sites, jBlock d L N₀ k bp.1 x' = jBlock d L N₀ k bp.1 x''

/-- The set of window blocks. -/
def windowBlocks (Zc : Set (Torus d (N₀ * L ^ k))) (k1 : ℕ) : Set (BlockV d L N₀ k) :=
  {b | IsWindowBlock G Zc k1 b}

/-- The set of terminal blocks. -/
def terminalBlocks (Zf : Set (Torus d (N₀ * L ^ k))) : Set (BlockV d L N₀ k) :=
  {b | IsTerminalBlock G Zf b}

/-- The chain vertices: window blocks and terminal blocks. -/
def IsChainVertex (Zc Zf : Set (Torus d (N₀ * L ^ k))) (k1 : ℕ) (b : BlockV d L N₀ k) : Prop :=
  IsWindowBlock G Zc k1 b ∨ IsTerminalBlock G Zf b

theorem nnAdj_symm' {m : ℕ} {a b : Torus d m} (h : NNAdj a b) : NNAdj b a := by
  obtain ⟨μ, h | h⟩ := h
  · exact ⟨μ, Or.inr h⟩
  · exact ⟨μ, Or.inl h⟩

theorem IntraAdj.symm {b b' : BlockV d L N₀ k} (h : IntraAdj b b') : IntraAdj b' b := by
  obtain ⟨h1, h2, x, hx, y, hy, hxy⟩ := h
  exact ⟨h1.symm, h2.symm, y, hy, x, hx, nnAdj_symm' hxy⟩

/-- **Definition III.4.1**: the chain graph `𝒢`. -/
def chainGraph (Zc Zf : Set (Torus d (N₀ * L ^ k))) (k1 : ℕ) : SimpleGraph (BlockV d L N₀ k) where
  Adj u v := IsChainVertex G Zc Zf k1 u ∧ IsChainVertex G Zc Zf k1 v ∧
    (IntraAdj u v ∨ CrossAdj G u v ∨ CrossAdj G v u)
  symm := ⟨fun u v ⟨hu, hv, h⟩ => ⟨hv, hu, by
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩⟩
  loopless := ⟨fun u hu => by
    obtain ⟨-, -, h⟩ := hu
    rcases h with h | h | h
    · exact h.2.1 rfl
    · have := h.1; omega
    · have := h.1; omega⟩


/-! ### Blocks and layers -/

theorem jBlock_mono {i j : ℕ} (hij : i ≤ j) (hjk : j ≤ k) {x x' : Torus d (N₀ * L ^ k)}
    (h : jBlock d L N₀ k i x = jBlock d L N₀ k i x') :
    jBlock d L N₀ k j x = jBlock d L N₀ k j x' := by
  unfold Multiscale.jBlock at h ⊢
  rw [blockMap_eq_iff_val (Multiscale.side_eq (hij.trans hjk))] at h
  rw [blockMap_eq_iff_val (Multiscale.side_eq hjk)]
  intro c
  have h1 := h c
  have e : L ^ j = L ^ i * L ^ (j - i) := by rw [← pow_add]; congr 1; omega
  rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h1]

theorem Omega_blockUnion {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ k + 1) :
    IsBlockUnion L N₀ k i (G.Ω j) := by
  rcases Nat.lt_or_ge j (k + 1) with h | h
  · exact isBlockUnion_of_le hij (by omega) (G.blockUnion j (hi.trans hij) (by omega))
  · have : j = k + 1 := by omega
    subst this
    intro x x' _
    simp [G.top]

theorem layer_blockConst {i : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) {x x' : Torus d (N₀ * L ^ k)}
    (h : jBlock d L N₀ k i x = jBlock d L N₀ k i x') : x ∈ G.layer i ↔ x' ∈ G.layer i := by
  rw [GeneratingSet.mem_layer, GeneratingSet.mem_layer, Omega_blockUnion G hi le_rfl (by omega) x x' h,
    Omega_blockUnion G hi (by omega) (by omega) x x' h]

theorem mem_Omega_blockConst {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ k + 1)
    {x x' : Torus d (N₀ * L ^ k)} (h : jBlock d L N₀ k i x = jBlock d L N₀ k i x') :
    x ∈ G.Ω j ↔ x' ∈ G.Ω j := Omega_blockUnion G hi hij hj x x' h

/-- A site of `Λ_i ∖ Z_{k₁}` lies in a window block (`Z_{k₁}` is a union of `k₁`-blocks which does
not meet `Ω_{k₁+1}`). -/
theorem isWindowBlock_blockOf {Zc : Set (Torus d (N₀ * L ^ k))} {k1 i : ℕ}
    (hblk : ∀ x x', jBlock d L N₀ k k1 x = jBlock d L N₀ k k1 x' → (x ∈ Zc ↔ x' ∈ Zc))
    (hΩ : ∀ x ∈ Zc, x ∉ G.Ω (k1 + 1)) (hk1 : 1 ≤ k1) (hki : k1 ≤ i) (hik : i < k)
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.layer i) (hxZ : x ∉ Zc) :
    IsWindowBlock G Zc k1 (blockOf d L N₀ k i x) := by
  refine ⟨hki, hik, fun x' hx' => ?_⟩
  have hx'x : jBlock d L N₀ k i x' = jBlock d L N₀ k i x := hx'
  refine ⟨?_, ?_⟩
  · exact (layer_blockConst G (hk1.trans hki) hik.le hx'x).mpr hx
  · rcases Nat.eq_or_lt_of_le hki with h | h
    · subst h
      intro hz
      exact hxZ ((hblk x' x hx'x).mp hz)
    · intro hz
      have hx'l : x' ∈ G.layer i := (layer_blockConst G (hk1.trans hki) hik.le hx'x).mpr hx
      have : x' ∈ G.Ω (k1 + 1) :=
        G.Ω_antitone (by omega) (by omega) (by omega) (G.mem_layer.1 hx'l).1
      exact hΩ x' hz this

/-- A site of `Ω_k ∩ Z` lies in a terminal block. -/
theorem isTerminalBlock_blockOf {Zf : Set (Torus d (N₀ * L ^ k))} (hk1 : 1 ≤ k)
    (hblk : ∀ x x', jBlock d L N₀ k k x = jBlock d L N₀ k k x' → (x ∈ Zf ↔ x' ∈ Zf))
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω k) (hxZ : x ∈ Zf) :
    IsTerminalBlock G Zf (blockOf d L N₀ k k x) := by
  refine ⟨rfl, fun x' hx' => ?_⟩
  have hx'x : jBlock d L N₀ k k x' = jBlock d L N₀ k k x := hx'
  exact ⟨(mem_Omega_blockConst G hk1 le_rfl (by omega) hx'x).mpr hx, (hblk x' x hx'x).mpr hxZ⟩

/-! ### Lemma III.4.2 -/

/-- **Lemma III.4.2 (b)**: nearest-neighbour sites lie in layers that differ by at most one; if the
layers are `i = i' + 1` the blocks of the two sites form a cross edge. -/
theorem nn_layers_adj (hϱ : 1 ≤ ϱ) {x x' : Torus d (N₀ * L ^ k)} (hnn : NNAdj x x') {i i' : ℕ}
    (hi : 1 ≤ i) (hik : i ≤ k) (hi' : 1 ≤ i') (hi'k : i' ≤ k) (hx : x ∈ G.layer i)
    (hx' : x' ∈ G.layer i') :
    i ≤ i' + 1 ∧ i' ≤ i + 1 ∧
      (i = i' + 1 → CrossAdj G (blockOf d L N₀ k i x) (blockOf d L N₀ k i' x')) := by
  have hd := torusDist_nnAdj_le hnn
  have hLpos : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have key : ∀ {a a' : Torus d (N₀ * L ^ k)} {j j' : ℕ}, NNAdj a a' → 1 ≤ j → j ≤ k → 1 ≤ j' →
      j' ≤ k → a ∈ G.layer j → a' ∈ G.layer j' → j ≤ j' + 1 := by
    intro a a' j j' hnn' hj hjk hj' hj'k ha ha'
    by_contra hlt
    push Not at hlt
    have h1 : a ∈ G.Ω (j' + 2) := G.Ω_antitone (by omega) (by omega) (by omega) (G.mem_layer.1 ha).1
    have h2 : a' ∉ G.Ω (j' + 1) := fun h => (G.mem_layer.1 ha').2 h
    have h3 := G.separation (j' + 1) (by omega) (by omega) a' h2 a h1
    have h4 := torusDist_nnAdj_le (nnAdj_symm' hnn')
    have h5 : (1 : ℝ) ≤ (L : ℝ) ^ (j' + 1) := one_le_pow₀ hLpos
    nlinarith
  refine ⟨key hnn hi hik hi' hi'k hx hx', key (nnAdj_symm' hnn) hi' hi'k hi hik hx' hx, fun h => ?_⟩
  subst h
  refine ⟨rfl, x, rfl, x', hnn, fun hmem => (G.mem_layer.1 hx').2 hmem, x', rfl, rfl⟩

/-- **Lemma III.4.2 (a)**: if `b₊ ⊂ Ω_{i+1}` and `b₋` is a nearest-neighbour adjacent
`(i+1)`-block disjoint from `Ω_{i+1}`, then `b₋ ⊂ Λ_i ∖ Z_{k₁}` (assuming `ϱ ≥ 2dL`, and that the
core `Z_{k₁}` is far from `Ω_{k₁+1}`). -/
theorem crossPair_window (hϱ : (2 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L)
    {Zc : Set (Torus d (N₀ * L ^ k))} {k1 i : ℕ} (hk1 : 1 ≤ k1) (hki : k1 ≤ i) (hik : i + 1 ≤ k)
    (hZfar : ∀ z ∈ Zc, ∀ y ∈ G.Ω (k1 + 1), (2 * d * L ^ (k1 + 1) : ℝ) < Green.torusDist d (N₀ * L ^ k) z y)
    {x x'' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω (i + 1)) (hnn : NNAdj x x'')
    (hx'' : x'' ∉ G.Ω (i + 1)) {z : Torus d (N₀ * L ^ k)}
    (hz : jBlock d L N₀ k (i + 1) z = jBlock d L N₀ k (i + 1) x'') :
    z ∈ G.layer i ∧ z ∉ Zc := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hLN : (L ^ (i + 1) * (N₀ * L ^ (k - (i + 1))) : ℕ) = N₀ * L ^ k := by
    rw [← mul_assoc, mul_comm (L ^ (i + 1)) N₀, mul_assoc, ← pow_add]; congr 2; omega
  -- the distance between `x` and `z`
  have hdist : Green.torusDist d (N₀ * L ^ k) x z ≤ 1 + d * (L : ℝ) ^ (i + 1) := by
    have h1 := Green.torusDist_triangle_gen x x'' z
    have h2 := torusDist_nnAdj_le hnn
    have h3 : Green.torusDist d (N₀ * L ^ k) x'' z ≤ d * (L ^ (i + 1) : ℕ) := by
      refine Green.torusDist_le_of_blockMap_eq (N := L ^ (i + 1)) (m := N₀ * L ^ (k - (i + 1)))
        hLN.symm (by positivity) ?_
      exact hz.symm
    push_cast at h3
    linarith
  have hpow : (1 : ℝ) < d * (L : ℝ) ^ (i + 1) := by
    have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have h2 : (2 : ℝ) ≤ L ^ (i + 1) := by
      calc (2 : ℝ) ≤ L := by exact_mod_cast hL
        _ = L ^ 1 := (pow_one _).symm
        _ ≤ L ^ (i + 1) := pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ L by omega)) (by omega)
    nlinarith
  have hsep : ϱ * (L : ℝ) ^ i ≥ 2 * d * (L : ℝ) ^ (i + 1) := by
    have : (0 : ℝ) < (L : ℝ) ^ i := pow_pos hLpos i
    calc ϱ * (L : ℝ) ^ i ≥ (2 * d * L) * (L : ℝ) ^ i := by nlinarith
      _ = 2 * d * (L : ℝ) ^ (i + 1) := by ring
  have hdist' : Green.torusDist d (N₀ * L ^ k) z x ≤ 1 + d * (L : ℝ) ^ (i + 1) := by
    rw [Green.torusDist_comm_gen]; exact hdist
  have hzi : z ∈ G.Ω i := by
    by_contra hzn
    have := G.separation i (by omega) (by omega) z hzn x hx
    linarith
  have hz1 : z ∉ G.Ω (i + 1) := fun h =>
    hx'' ((mem_Omega_blockConst G (i := i + 1) (by omega) le_rfl (by omega) hz).mp h)
  refine ⟨G.mem_layer.2 ⟨hzi, hz1⟩, fun hzc => ?_⟩
  rcases Nat.eq_or_lt_of_le hki with h | h
  · subst h
    have := hZfar z hzc x hx
    linarith
  · have hzk : z ∈ G.Ω (k1 + 1) := G.Ω_antitone (by omega) (by omega) (by omega) hzi
    have := hZfar z hzc z hzk
    rw [Green.torusDist_self_eq_zero] at this
    have : (0 : ℝ) < 2 * d * (L : ℝ) ^ (k1 + 1) := by positivity
    linarith

end Chain

end Balaban.LargeField
