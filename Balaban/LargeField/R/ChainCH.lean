module

public import Balaban.LargeField.R.ChainWalk
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma CH (Part III, Lemma III.4.4)

`lemmaCH`: for a ripe component `Z` of `Z^pre_k` and a window block `y` of layer `j` there is a chain
`y = x₀, …, x_p` in the chain graph `𝒢`, `x_p` a terminal block, all vertices but the last window blocks
of layers `≥ i₀ = max {k₁, j - h_k + 2}`, visiting every vertex at most once; and for every field `ψ`
on the blocks that changes by at most `c δ_i` along intra edges of layer `i` and by at most `d L c δ_i`
along cross edges between layers `i + 1` and `i`, `dist (ψ y) (ψ x_p) < Ŵ_k c δ_j`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Multiscale

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} [NeZero S.L] [NeZero S.M]

/-- The block over a site exists (the fibres of the block map are nonempty). -/
theorem exists_site_of_block {d L N₀ k j : ℕ} [NeZero N₀] [NeZero L] (hjk : j ≤ k)
    (b : Torus d (N₀ * L ^ (k - j))) : ∃ x : Torus d (N₀ * L ^ k), jBlock d L N₀ k j x = b := by
  have hℓ : N₀ * L ^ k = L ^ j * (N₀ * L ^ (k - j)) := Multiscale.side_eq hjk
  have h := card_blockFibre (d := d) (ℓ := N₀ * L ^ k) (N := L ^ j) (m := N₀ * L ^ (k - j)) hℓ b
  have hpos : 0 < (L ^ j) ^ d := by have := NeZero.pos L; positivity
  rw [← h] at hpos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  exact ⟨x, mem_blockFibre.mp hx⟩

/-- **Lemma III.4.4 (Lemma CH)**, combinatorial part: the chain from a window block to a terminal
block. -/
theorem exists_chain_of_window (hkK : k ≤ K) (hL : 2 ≤ S.L)
    (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j) (hW : H.RipeWindow k Z) (hk0 : k ≤ k0)
    (hq1 : 1 ≤ (H.bk k Z).q) (hT : ∀ j, 1 ≤ j → j ≤ k0 → 2 * S.crit j + 5 ≤ n j)
    {j : ℕ} (hjk : j < k) {y : BlockV S.d S.L (S.M * n k) k}
    (hy : IsWindowBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (S.k1 k) y)
    (hyj : y.1 = j) :
    ∃ (len : ℕ) (x : ℕ → BlockV S.d S.L (S.M * n k) k), x 0 = y ∧
      (∀ m < len, IsWindowBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (S.k1 k) (x m) ∧
        S.chainFloor (S.k1 k) k j ≤ (x m).1) ∧
      IsTerminalBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M k) (x len) ∧
      (∀ m < len, (chainGraph (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k))
        (H.locFine Z S.M k) (S.k1 k)).Adj (x m) (x (m + 1))) ∧
      (∀ m ≤ len, ∀ m' ≤ len, x m = x m' → m = m') := by
  classical
  set G := H.locGen Z S.M hkK hL hR with hG
  have hS := H.F.ok
  have hqk1 : S.k1 k = (H.bk k Z).q := hW.core_k1
  have hkk1 : 1 ≤ S.k1 k := by rw [hqk1]; exact hq1
  have hk1j : S.k1 k ≤ j := by
    obtain ⟨hh1, -, -⟩ := hy; rw [hyj] at hh1; exact hh1
  have hkq : S.k1 k < k := by
    rw [hqk1]
    have := hW.core_window.1
    have : 1 ≤ S.nq (H.bk k Z).q := by unfold Setting.nq; omega
    omega
  obtain ⟨j', b⟩ := y
  simp only at hyj
  subst hyj
  obtain ⟨x0, hx0b⟩ := exists_site_of_block (d := S.d) (L := S.L) (N₀ := S.M * n k) hjk.le b
  have hxs : x0 ∈ BlockV.sites (⟨j', b⟩ : BlockV S.d S.L (S.M * n k) k) := hx0b
  obtain ⟨N, p, hN, hp0, hadj, hwin, hpE, hpZ⟩ := path_avoids_obstacles hkK hL hR hW hk0 hq1 hT hjk hy rfl hxs
  -- block constancy of the core and of the component
  have hnn := hnn_k H hkK
  have hblk : ∀ x x' : Torus S.d (S.M * n k * S.L ^ k),
      jBlock S.d S.L (S.M * n k) k (S.k1 k) x = jBlock S.d S.L (S.M * n k) k (S.k1 k) x' →
        (x ∈ H.locFine Z S.M (S.k1 k) ↔ x' ∈ H.locFine Z S.M (S.k1 k)) := by
    intro x x' h
    have h1 := cubeMap_eq_of_jBlock_eq (S := S) (n := n) (M := S.M) (K := k) (j := S.k1 k)
      (k := S.k1 k) le_rfl hkq.le hnn h
    show cubeMap n S.L S.M k (S.k1 k) x ∈ ((H.locRH k Z).step (S.k1 k)).Z ↔
      cubeMap n S.L S.M k (S.k1 k) x' ∈ ((H.locRH k Z).step (S.k1 k)).Z
    rw [h1]
  have hZf : ∀ x x' : Torus S.d (S.M * n k * S.L ^ k),
      jBlock S.d S.L (S.M * n k) k k x = jBlock S.d S.L (S.M * n k) k k x' →
        (x ∈ H.locFine Z S.M k ↔ x' ∈ H.locFine Z S.M k) := by
    intro x x' h
    have h1 := cubeMap_eq_of_jBlock_eq (S := S) (n := n) (M := S.M) (K := k) (j := k)
      (k := k) le_rfl le_rfl hnn h
    show cubeMap n S.L S.M k k x ∈ ((H.locRH k Z).step k).Z ↔
      cubeMap n S.L S.M k k x' ∈ ((H.locRH k Z).step k).Z
    rw [h1]
  have hΩ : ∀ x ∈ H.locFine Z S.M (S.k1 k), x ∉ G.Ω (S.k1 k + 1) := fun x hx =>
    locFine_not_mem_Omega (hkK := hkK) (hL := hL) (hR := hR) hkq hx
  have hϱ : 1 ≤ ((S.L : ℝ) * S.M * S.Rb) := by
    have h1 : (1 : ℝ) ≤ S.L := by exact_mod_cast (by omega : 1 ≤ S.L)
    have h2 : (1 : ℝ) ≤ S.M := by exact_mod_cast hS.one_le_M
    have h3 : (1 : ℝ) ≤ S.Rb := by have := hS.two_le_Rb; linarith
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ S.L * S.M * S.Rb := by gcongr
  obtain ⟨len, x, hx0, hwin', hterm, hadj', hinj⟩ := exists_chain (G := G)
    (Zc := H.locFine Z S.M (S.k1 k)) (Zf := H.locFine Z S.M k) (k1 := S.k1 k)
    (i0 := S.chainFloor (S.k1 k) k j') hϱ hkk1 (Setting.le_chainFloor _ _ _)
    hblk hΩ hZf hN p hadj (fun m hm => hwin m hm) ⟨hpE, hpZ⟩
  refine ⟨len, x, ?_, hwin', hterm, hadj', hinj⟩
  rw [hx0, hp0]
  have hl : x0 ∈ G.layer j' := (hy.2.2 x0 hx0b).1
  rw [layerIndex_eq' (by omega) hjk.le hl]
  simp only [blockOf]
  rw [hx0b]

/-- The window blocks of one layer form a finite set. -/
theorem windowBlocks_finite {G : GeneratingSet S.d S.L (S.M * n k) k ((S.L : ℝ) * S.M * S.Rb)}
    (Zc : Set (Torus S.d (S.M * n k * S.L ^ k))) (k1 i : ℕ) :
    {b : BlockV S.d S.L (S.M * n k) k | IsWindowBlock G Zc k1 b ∧ b.1 = i}.Finite := by
  classical
  refine (Set.finite_range (fun b : Torus S.d (S.M * n k * S.L ^ (k - i)) =>
    (⟨i, b⟩ : BlockV S.d S.L (S.M * n k) k))).subset ?_
  rintro ⟨i', b⟩ ⟨-, h⟩
  simp only at h
  subst h
  exact ⟨b, rfl⟩

/-- **Lemma III.4.4 (Lemma CH)**.  For a ripe component `Z` of `Z^pre_k` and a window block `y` of
layer `j`, there is a chain `y = x₀, …, x_p` in the chain graph `𝒢`, with `x_p` a terminal block, all
other vertices window blocks of layers `≥ i₀ = max {k₁, j - h_k + 2}`, visiting every vertex at most
once; and if a field `ψ` on blocks changes by at most `c δ_i` along intra edges of layer `i` and by at
most `d L c δ_i` along cross edges from layer `i + 1` to layer `i`, where `δ` satisfies the
hypotheses of Lemma III.4.4 (`IsAdmDelta`), then `dist (ψ y) (ψ x_p) < Ŵ_k c δ_j`. -/
theorem lemmaCH (hkK : k ≤ K) (hL : 2 ≤ S.L)
    (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j) (hW : H.RipeWindow k Z) (hk0 : k ≤ k0)
    (hq1 : 1 ≤ (H.bk k Z).q) (hT : ∀ j, 1 ≤ j → j ≤ k0 → 2 * S.crit j + 5 ≤ n j)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ) {c : ℝ} (hc : 0 < c)
    {E : Type*} [PseudoMetricSpace E] (ψ : BlockV S.d S.L (S.M * n k) k → E)
    (hψintra : ∀ u v, IsChainVertex (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k))
        (H.locFine Z S.M k) (S.k1 k) u →
      IsChainVertex (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k)
        (S.k1 k) v → IntraAdj u v → dist (ψ u) (ψ v) ≤ c * δ u.1)
    (hψcross : ∀ u v, IsChainVertex (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k))
        (H.locFine Z S.M k) (S.k1 k) u →
      IsChainVertex (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k)
        (S.k1 k) v → CrossAdj (H.locGen Z S.M hkK hL hR) u v →
        dist (ψ u) (ψ v) ≤ (S.d : ℝ) * S.L * c * δ v.1)
    {j : ℕ} (hjk : j < k) {y : BlockV S.d S.L (S.M * n k) k}
    (hy : IsWindowBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (S.k1 k) y)
    (hyj : y.1 = j) :
    ∃ (len : ℕ) (x : ℕ → BlockV S.d S.L (S.M * n k) k), x 0 = y ∧
      (∀ m < len, IsWindowBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (S.k1 k) (x m) ∧
        S.chainFloor (S.k1 k) k j ≤ (x m).1) ∧
      IsTerminalBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M k) (x len) ∧
      (∀ m < len, (chainGraph (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k))
        (H.locFine Z S.M k) (S.k1 k)).Adj (x m) (x (m + 1))) ∧
      (∀ m ≤ len, ∀ m' ≤ len, x m = x m' → m = m') ∧
      dist (ψ y) (ψ (x len)) < S.hatW ε k * c * δ j := by
  classical
  obtain ⟨len, x, hx0, hwin, hterm, hadj, hinj⟩ :=
    exists_chain_of_window hkK hL hR hW hk0 hq1 hT hjk hy hyj
  refine ⟨len, x, hx0, hwin, hterm, hadj, hinj, ?_⟩
  have hS := H.F.ok
  have hqk1 : S.k1 k = (H.bk k Z).q := hW.core_k1
  have hk1j : S.k1 k ≤ j := by
    obtain ⟨hh1, -, -⟩ := hy; rw [hyj] at hh1; exact hh1
  -- the layers of the chain
  have hlay : ∀ m < len, S.chainFloor (S.k1 k) k j ≤ (x m).1 ∧ (x m).1 < k := fun m hm =>
    ⟨(hwin m hm).2, (hwin m hm).1.2.1⟩
  have hend : k ≤ (x len).1 := hterm.1.ge
  have hedge : ∀ m < len,
      (x (m + 1)).1 = (x m).1 ∨ (x (m + 1)).1 + 1 = (x m).1 ∨ (x m).1 + 1 = (x (m + 1)).1 := by
    intro m hm
    obtain ⟨-, -, h | h | h⟩ := hadj m hm
    · exact Or.inl h.1.symm
    · exact Or.inr (Or.inl h.1)
    · exact Or.inr (Or.inr h.1)
  have hcount : ∀ i, ((((Finset.range len).filter fun m => (x m).1 = i).card : ℕ) : ℝ) ≤
      S.numax k * ((S.L : ℝ) * S.M * S.crit k) ^ S.d := by
    intro i
    by_cases hne : ((Finset.range len).filter fun m => (x m).1 = i).Nonempty
    · obtain ⟨m0, hm0⟩ := hne
      obtain ⟨hm0len, hm0i⟩ := Finset.mem_filter.mp hm0
      have hwin0 := hwin m0 (Finset.mem_range.mp hm0len)
      have hik : i < k := by rw [← hm0i]; exact hwin0.1.2.1
      have hi : S.k1 k ≤ i := by rw [← hm0i]; exact hwin0.1.1
      have hfin := windowBlocks_finite (G := H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k))
        (S.k1 k) i
      have hcard : ((Finset.range len).filter fun m => (x m).1 = i).card ≤
          {b : BlockV S.d S.L (S.M * n k) k |
            IsWindowBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (S.k1 k) b ∧
              b.1 = i}.ncard := by
        rw [← Finset.card_image_of_injOn (f := x)]
        · rw [← Set.ncard_coe_finset]
          refine Set.ncard_le_ncard ?_ hfin
          intro b hb
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
            Finset.mem_range] at hb
          obtain ⟨m, ⟨hm, hmi⟩, rfl⟩ := hb
          exact ⟨(hwin m hm).1, hmi⟩
        · intro m hm m' hm' he
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hm hm'
          exact hinj m hm.1.le m' hm'.1.le he
      have hbound := windowBlocks_ncard_le (M := S.M) (hkK := hkK) (hL := hL) (hR := hR) hW hi hik
      have : ((Finset.range len).filter fun m => (x m).1 = i).card ≤
          S.numax k * ((S.L : ℕ) * S.M * S.crit k) ^ S.d := hcard.trans hbound
      exact_mod_cast this
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have hmain := hS.chain_lt_hatW (ε := ε) hk1j hjk hδ hc ψ (fun b => b.1) x len hlay hend hedge
    (fun m hm he => ?_) (fun m hm he => ?_) (fun m hm he => ?_) hcount
  · rw [hx0] at hmain
    exact hmain
  · obtain ⟨hu, hv, h | h | h⟩ := hadj m hm
    · exact hψintra _ _ hu hv h
    · exfalso; have := h.1; omega
    · exfalso; have := h.1; omega
  · obtain ⟨hu, hv, h | h | h⟩ := hadj m hm
    · exfalso; have := h.1; omega
    · exact hψcross _ _ hu hv h
    · exfalso; have := h.1; omega
  · obtain ⟨hu, hv, h | h | h⟩ := hadj m hm
    · exfalso; have := h.1; omega
    · exfalso; have := h.1; omega
    · rw [dist_comm]; exact hψcross _ _ hv hu h

/-- The large-torus hypothesis (H-T) of the source, `n_j ≥ 4 ν_max(j) (crit_j + ω_j) + 4`, implies the
two forms used above. -/
theorem hT_forms (hS : S.Ok) {j : ℕ}
    (h : 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j) :
    4 * S.rho j + 21 ≤ n j ∧ 2 * S.crit j + 5 ≤ n j := by
  have h1 := hS.hatW_numax_ge_one j
  have h2 := L_add_eleven_le_omega S j
  have hL := hS.two_le_L
  have h3 : 4 * (S.crit j + S.omega j) ≤ 4 * S.numax j * (S.crit j + S.omega j) := by
    nlinarith [Nat.zero_le (S.crit j + S.omega j)]
  have hc : S.crit j = 2 * S.rho j + 10 := rfl
  constructor <;> omega

/-- **Lemma III.4.4 (Lemma CH) for a ripe component**: the same statement with the hypotheses of
Lemma III.1.2 derived from the ripeness of `Z`, under the source hypothesis (H-T). -/
theorem lemmaCH_of_ripe (hG : S.Good) (hkK : k ≤ K) (hL : 2 ≤ S.L)
    (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j) (hk0 : k ≤ k0) (hrip : S.Ripe k (H.bk k Z))
    (hq1 : 1 ≤ (H.bk k Z).q)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.numax j * (S.crit j + S.omega j) + 4 ≤ n j)
    {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S.d S.L ε (S.k1 k) k δ) {c : ℝ} (hc : 0 < c)
    {E : Type*} [PseudoMetricSpace E] (ψ : BlockV S.d S.L (S.M * n k) k → E)
    (hψintra : ∀ u v, IsChainVertex (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k))
        (H.locFine Z S.M k) (S.k1 k) u →
      IsChainVertex (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k)
        (S.k1 k) v → IntraAdj u v → dist (ψ u) (ψ v) ≤ c * δ u.1)
    (hψcross : ∀ u v, IsChainVertex (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k))
        (H.locFine Z S.M k) (S.k1 k) u →
      IsChainVertex (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (H.locFine Z S.M k)
        (S.k1 k) v → CrossAdj (H.locGen Z S.M hkK hL hR) u v →
        dist (ψ u) (ψ v) ≤ (S.d : ℝ) * S.L * c * δ v.1)
    {j : ℕ} (hjk : j < k) {y : BlockV S.d S.L (S.M * n k) k}
    (hy : IsWindowBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (S.k1 k) y)
    (hyj : y.1 = j) :
    ∃ (len : ℕ) (x : ℕ → BlockV S.d S.L (S.M * n k) k), x 0 = y ∧
      (∀ m < len, IsWindowBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k)) (S.k1 k) (x m) ∧
        S.chainFloor (S.k1 k) k j ≤ (x m).1) ∧
      IsTerminalBlock (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M k) (x len) ∧
      (∀ m < len, (chainGraph (H.locGen Z S.M hkK hL hR) (H.locFine Z S.M (S.k1 k))
        (H.locFine Z S.M k) (S.k1 k)).Adj (x m) (x (m + 1))) ∧
      (∀ m ≤ len, ∀ m' ≤ len, x m = x m' → m = m') ∧
      dist (ψ y) (ψ (x len)) < S.hatW ε k * c * δ j := by
  have hS := H.F.ok
  have hW : H.RipeWindow k Z :=
    ripe_window hG (fun j hj1 hj0 => (hT_forms hS (hT j hj1 hj0)).1) hk0 hkK hrip
  exact lemmaCH hkK hL hR hW hk0 hq1 (fun j hj1 hj0 => (hT_forms hS (hT j hj1 hj0)).2) hδ hc ψ
    hψintra hψcross hjk hy hyj

end RegionHistory

end Balaban.LargeField
