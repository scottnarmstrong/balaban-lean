module

public import Balaban.LargeField.R.DeltaPsiDef
public import Balaban.LargeField.R.DeltaPsiPath
public import Balaban.LargeField.R.ChiBridge
public import Balaban.LargeField.R.FineBox
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The edge bounds of the chain from the window domain (Part III, §III.4.4, first paragraph)

`WinBond` (the conditions (1.24) of Definition II.3.4 contained in `𝒳_win`) bounds the field difference
across intra edges by `c δ_i`; this file derives the bounds on intra and cross edges that Lemma CH
(`lemmaCH`) takes as input: intra edges cost `≤ c δ_i` (`winBond_intra`), and a cross edge between the
layers `i + 1` and `i` costs `≤ d L c δ_i` (`winBond_cross`): go from the `i`-block `y'` inside the
`(i + 1)`-block `b₋` to the `i`-block of `b₋` adjacent to `b₊` along a monotone lattice path of at most
`d (L - 1)` intra edges (Lemma III.4.2 (a): all `i`-blocks of `b₋` are window blocks), then one step.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale

section Edge

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The `(i + 1)`-block of a site is the image under the block map of its `i`-block. -/
theorem jBlock_succ_eq_blockMap {i : ℕ} (hi : i + 1 ≤ k) (x : Torus d (N₀ * L ^ k)) :
    jBlock d L N₀ k (i + 1) x = blockMap L (N₀ * L ^ (k - (i + 1))) (jBlock d L N₀ k i x) := by
  have hℓ := side_eq (N₀ := N₀) (L := L) (k := k) (j := i) (by omega)
  have hm : N₀ * L ^ (k - i) = L ^ 1 * (N₀ * L ^ (k - (i + 1))) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
    have e1 : i + 1 + t - i = t + 1 := by omega
    have e2 : i + 1 + t - (i + 1) = t := by omega
    rw [e1, e2]
    ring
  have key := blockMap_pow_add (d := d) (L := L) (j := i) (k := 1) (m₂ := N₀ * L ^ (k - (i + 1)))
    hℓ hm x
  simp only [pow_one] at key
  unfold jBlock
  exact key.symm

/-- The `i`-blocks inside a given `(i + 1)`-block `P` form a box of side `L`. -/
theorem blockMap_eq_iff_mem_box {i : ℕ} (hi : i + 1 ≤ k) (P : Torus d (N₀ * L ^ (k - (i + 1))))
    (w : Torus d (N₀ * L ^ (k - i))) :
    blockMap L (N₀ * L ^ (k - (i + 1))) w = P ↔
      w ∈ box (fun c => (((L * (P c).val : ℕ)) : ZMod (N₀ * L ^ (k - i)))) (fun _ => L) := by
  have hℓ : N₀ * L ^ (k - i) = L * (N₀ * L ^ (k - (i + 1))) := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hi
    have e1 : i + 1 + t - i = t + 1 := by omega
    have e2 : i + 1 + t - (i + 1) = t := by omega
    rw [e1, e2]
    ring
  have h := blockMap_mem_box_iff (d := d) (ℓ := N₀ * L ^ (k - i)) (N := L)
    (m := N₀ * L ^ (k - (i + 1))) hℓ P (s := fun _ => 1) w
  have hbox : blockMap L (N₀ * L ^ (k - (i + 1))) w ∈ box P (fun _ => 1) ↔
      blockMap L (N₀ * L ^ (k - (i + 1))) w = P := by
    unfold box
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hh
      funext c
      obtain ⟨jj, hjj, hxj⟩ := hh c
      have : jj = 0 := by omega
      subst this
      simpa using hxj
    · intro hh c
      exact ⟨0, by omega, by simp [hh]⟩
  rw [← hbox, h]
  simp only [mul_one]

/-- Intra edges cost `≤ c δ_i`. -/
theorem winBond_intra {G : GeneratingSet d L N₀ k ϱ} {Zc Zf : Set (Torus d (N₀ * L ^ k))} {k1 : ℕ}
    {c : ℝ} {δ : ℕ → ℝ} {N : ℕ} {ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)}
    (hW : WinBond G Zc Zf k1 c δ ψ) (u v : BlockV d L N₀ k) (hu : IsChainVertex G Zc Zf k1 u)
    (hv : IsChainVertex G Zc Zf k1 v) (h : IntraAdj u v) : dist (ψ u) (ψ v) ≤ c * δ u.1 := by
  obtain ⟨i, u⟩ := u
  obtain ⟨j, v⟩ := v
  obtain ⟨hij, hne, x, hx, y, hy, hnn⟩ := h
  simp only at hij
  subst hij
  have hik : i ≤ k := by
    rcases hu with hu | hu
    · exact hu.2.1.le
    · exact hu.1.le
  have hx' : jBlock d L N₀ k i x = u := hx
  have hy' : jBlock d L N₀ k i y = v := hy
  rcases jBlock_adj_or hik (show Adj x y from hnn) with he | ha
  · have huv : u = v := by rw [← hx', ← hy']; exact he
    exact absurd (by rw [huv]) hne
  · rw [hx', hy'] at ha
    exact (hW.1 i u v hu hv ha).le

/-- A cross edge between the layers `i + 1` and `i` costs `≤ d L c δ_i` (Lemma III.4.2 (a) and the
monotone path inside `b₋`). -/
theorem winBond_cross (hϱ : (2 * d * L : ℝ) ≤ ϱ) (hd : 1 ≤ d) (hL : 2 ≤ L)
    (G : GeneratingSet d L N₀ k ϱ) {Zc Zf : Set (Torus d (N₀ * L ^ k))} {k1 : ℕ} (hk1 : 1 ≤ k1)
    (hZfar : ∀ z ∈ Zc, ∀ y ∈ G.Ω (k1 + 1),
      (2 * d * (L : ℝ) ^ (k1 + 1) : ℝ) < Green.torusDist d (N₀ * L ^ k) z y)
    {c : ℝ} {δ : ℕ → ℝ} {N : ℕ} {ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N)} (hc : 0 < c)
    (hδ : ∀ i, k1 ≤ i → i < k → 0 < δ i) (hW : WinBond G Zc Zf k1 c δ ψ)
    (u v : BlockV d L N₀ k) (hu : IsChainVertex G Zc Zf k1 u) (hv : IsChainVertex G Zc Zf k1 v)
    (h : CrossAdj G u v) : dist (ψ u) (ψ v) ≤ (d : ℝ) * L * c * δ v.1 := by
  obtain ⟨j, u⟩ := u
  obtain ⟨i, v⟩ := v
  obtain ⟨hij, x, hxu, x'', hnn, hx''Ω, x', hx'v, hjb⟩ := h
  simp only at hij
  subst hij
  -- `v` is a window block
  have hvw : IsWindowBlock G Zc k1 ⟨i, v⟩ := by
    rcases hv with hv | hv
    · exact hv
    · exfalso
      have h1 : i = k := hv.1
      rcases hu with hu | hu
      · have := hu.2.1; simp only at this; omega
      · have := hu.1; simp only at this; omega
  obtain ⟨hk1i, hik, -⟩ := hvw
  replace hk1i : k1 ≤ i := hk1i
  replace hik : i < k := hik
  have hxΩ : x ∈ G.Ω (i + 1) := by
    rcases hu with hu | hu
    · exact (G.mem_layer.1 (hu.2.2 x hxu).1).1
    · have hk : i + 1 = k := hu.1
      rw [hk]; exact (hu.2 x hxu).1
  set P := jBlock d L N₀ k (i + 1) x'' with hPdef
  have hP : ∀ z, jBlock d L N₀ k (i + 1) z = P → z ∈ G.layer i ∧ z ∉ Zc := fun z hz =>
    crossPair_window G hϱ hd hL hk1 hk1i (by omega) hZfar hxΩ hnn hx''Ω hz
  have hwin : ∀ w : Torus d (N₀ * L ^ (k - i)), blockMap L (N₀ * L ^ (k - (i + 1))) w = P →
      IsWindowBlock G Zc k1 ⟨i, w⟩ := by
    intro w hw
    refine ⟨hk1i, hik, fun s hs => ?_⟩
    have hs' : jBlock d L N₀ k i s = w := hs
    refine hP s ?_
    rw [jBlock_succ_eq_blockMap (by omega) s, hs']
    exact hw
  set v'' := jBlock d L N₀ k i x'' with hv''
  have hv''P : blockMap L (N₀ * L ^ (k - (i + 1))) v'' = P := by
    rw [← jBlock_succ_eq_blockMap (by omega) x'']
  have hv'P : blockMap L (N₀ * L ^ (k - (i + 1))) v = P := by
    have hx'v' : jBlock d L N₀ k i x' = v := hx'v
    rw [← hx'v', ← jBlock_succ_eq_blockMap (by omega) x']
    exact hjb
  have hbox := fun w => blockMap_eq_iff_mem_box (d := d) (L := L) (N₀ := N₀) (k := k) (i := i)
    (by omega) P w
  have hm : L ≤ N₀ * L ^ (k - i) := by
    have h1 : 1 ≤ N₀ := Nat.pos_of_ne_zero (NeZero.ne N₀)
    have h2 : L ^ 1 ≤ L ^ (k - i) := Nat.pow_le_pow_right (by omega) (by omega)
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ (k - i) := h2
      _ ≤ N₀ * L ^ (k - i) := Nat.le_mul_of_pos_left _ h1
  obtain ⟨n, hn, hr⟩ := box_reach (m := N₀ * L ^ (k - i)) (s := fun _ => L) (fun _ => hm)
    ((hbox v).1 hv'P) ((hbox v'').1 hv''P)
  have hcδ : 0 < c * δ i := mul_pos hc (hδ i hk1i hik)
  have hstep := reach_dist_le (adj := torusAdj) (P := box (fun c => (((L * (P c).val : ℕ)) :
      ZMod (N₀ * L ^ (k - i)))) (fun _ => L)) (fun w => ψ ⟨i, w⟩) (B := c * δ i)
    (fun w hw w' hw' hadj => by
      by_cases he : w = w'
      · subst he; simp [hcδ.le]
      · exact (hW.1 i w w' (Or.inl (hwin w ((hbox w).2 hw))) (Or.inl (hwin w' ((hbox w').2 hw')))
          ⟨he, hadj⟩).le) hr
  have hcross := hW.2 i u v'' hu (Or.inl (hwin v'' hv''P)) ⟨x, hxu, x'', rfl, hnn⟩
  have hn' : (n : ℝ) ≤ d * (L - 1) := by
    have h1 : n ≤ d * (L - 1) := by
      have := hn
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using this
    have h2 : ((d * (L - 1) : ℕ) : ℝ) = d * ((L : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]; simp
    calc (n : ℝ) ≤ ((d * (L - 1) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = d * ((L : ℝ) - 1) := h2
  have htri := dist_triangle (ψ ⟨i + 1, u⟩) (ψ ⟨i, v''⟩) (ψ ⟨i, v⟩)
  have hsymm := dist_comm (ψ ⟨i, v''⟩) (ψ ⟨i, v⟩)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  simp only at hstep hcross ⊢
  have hfin : dist (ψ ⟨i, v⟩) (ψ ⟨i, v''⟩) ≤ d * ((L : ℝ) - 1) * (c * δ i) := by
    calc _ ≤ n * (c * δ i) := hstep
      _ ≤ _ := mul_le_mul_of_nonneg_right hn' hcδ.le
  nlinarith [hcδ]

end Edge

end Balaban.LargeField
