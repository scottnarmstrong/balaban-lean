module

public import Balaban.LargeField.R.ChainSetting
public import Balaban.LargeField.Budget.Fine
public import Balaban.LargeField.History.FlowCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Counting window blocks (Part III, Lemma III.1.2 (c))

The number of window blocks of layer `i` is at most `ν_max(k) (L M crit_k)^d`:
the window blocks of layer `i` lie in the fine set of `Z_{i+1}` (`Λ_i ⊆ Ω_{i+1}ᶜ ⊆ Z_{i+1}`), which is
covered by `ν ≤ ν_max(k)` boxes of `≤ crit_{i+1} ≤ crit_k` cubes of side `L^{i+1} M` per direction,
and each `i`-block has `L^{i d}` sites.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Multiscale

section Blocks

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L]

/-- Disjoint `i`-blocks inside a finite set of sites. -/
theorem card_blocks_mul_le {i : ℕ} (hi : i ≤ k) (P : Finset (Torus d (N₀ * L ^ (k - i))))
    (F : Finset (Torus d (N₀ * L ^ k)))
    (hF : ∀ b ∈ P, ∀ x, jBlock d L N₀ k i x = b → x ∈ F) : P.card * (L ^ i) ^ d ≤ F.card := by
  classical
  have hℓ : N₀ * L ^ k = L ^ i * (N₀ * L ^ (k - i)) := Multiscale.side_eq hi
  have hdisj : ∀ b ∈ P, ∀ b' ∈ P, b ≠ b' →
      Disjoint (blockFibre (ℓ := N₀ * L ^ k) (L ^ i) (N₀ * L ^ (k - i)) b)
        (blockFibre (ℓ := N₀ * L ^ k) (L ^ i) (N₀ * L ^ (k - i)) b') := by
    intro b _ b' _ hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [mem_blockFibre] at hx hx'
    exact hne (hx.symm.trans hx')
  have h1 : (P.biUnion fun b => blockFibre (ℓ := N₀ * L ^ k) (L ^ i) (N₀ * L ^ (k - i)) b).card =
      P.card * (L ^ i) ^ d := by
    rw [Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl (fun b _ => card_blockFibre hℓ b)]
    simp
  rw [← h1]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
  exact hF b hb x (mem_blockFibre.mp hxb)

end Blocks

section Boxes

variable {d n : ℕ}

theorem ncard_box_le (a : Torus d n) (s : Fin d → ℕ) : (box a s).ncard ≤ ∏ i, s i := by
  classical
  have hsub : box a s ⊆ ↑((Fintype.piFinset fun i => Finset.range (s i)).image
      fun j : Fin d → ℕ => fun i => a i + (j i : ZMod n)) := by
    intro x hx
    choose j hj hxj using hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Fintype.mem_piFinset,
      Finset.mem_range]
    exact ⟨j, hj, funext fun i => (hxj i).symm⟩
  calc (box a s).ncard ≤ (↑((Fintype.piFinset fun i => Finset.range (s i)).image
        fun j : Fin d → ℕ => fun i => a i + (j i : ZMod n)) : Set (Torus d n)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ (Fintype.piFinset fun i => Finset.range (s i)).card := by
        rw [Set.ncard_coe_finset]; exact Finset.card_image_le
    _ = ∏ i, s i := by simp

end Boxes

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K} {k : ℕ} {Z : H.Comp k} {M : ℕ} [NeZero M] [NeZero S.L]

/-- The number of cubes of a set covered by `ν` boxes of side `≤ crit_j`. -/
theorem card_le_of_coveredBy {j : ℕ} {c : Finset (Torus S.d (n j))} {ν : ℕ}
    (h : CoveredBy S n j c ν) : c.card ≤ ν * S.crit j ^ S.d := by
  classical
  obtain ⟨B, hB, hs, hcov⟩ := h
  have h1 : c.card ≤ ∑ b ∈ B, (box b.1 b.2).ncard := by
    have hsub : c ⊆ B.biUnion fun b => (Set.toFinite (box b.1 b.2)).toFinset := by
      intro x hx
      have := hcov (Finset.mem_coe.mpr hx)
      simp only [Set.mem_iUnion, exists_prop] at this
      obtain ⟨b, hb, hxb⟩ := this
      exact Finset.mem_biUnion.mpr ⟨b, hb, (Set.toFinite _).mem_toFinset.mpr hxb⟩
    calc c.card ≤ (B.biUnion fun b => (Set.toFinite (box b.1 b.2)).toFinset).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ b ∈ B, ((Set.toFinite (box b.1 b.2)).toFinset).card := Finset.card_biUnion_le
      _ = ∑ b ∈ B, (box b.1 b.2).ncard := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  have h2 : ∀ b ∈ B, (box b.1 b.2).ncard ≤ S.crit j ^ S.d := by
    intro b hb
    calc (box b.1 b.2).ncard ≤ ∏ i, b.2 i := ncard_box_le _ _
      _ ≤ ∏ _i : Fin S.d, S.crit j := Finset.prod_le_prod (fun i _ => hs b hb i)
      _ = S.crit j ^ S.d := by simp
  calc c.card ≤ ∑ b ∈ B, (box b.1 b.2).ncard := h1
    _ ≤ ∑ _b ∈ B, S.crit j ^ S.d := Finset.sum_le_sum h2
    _ = B.card * S.crit j ^ S.d := by simp
    _ ≤ ν * S.crit j ^ S.d := Nat.mul_le_mul_right _ hB

variable (hkK : k ≤ K) (hL : 2 ≤ S.L) (hR : ∀ j, 1 ≤ j → j < k → S.Rb ≤ R j)

/-- **Lemma III.1.2 (c)**: the number of window blocks of layer `i` is at most
`ν_max(k) (L M crit_k)^d`. -/
theorem windowBlocks_ncard_le (hW : H.RipeWindow k Z) {i : ℕ} (hi : S.k1 k ≤ i) (hik : i < k) :
    {b : BlockV S.d S.L (M * n k) k |
        IsWindowBlock (H.locGen Z M hkK hL hR) (H.locFine Z M (S.k1 k)) (S.k1 k) b ∧ b.1 = i}.ncard ≤
      S.numax k * ((S.L : ℕ) * M * S.crit k) ^ S.d := by
  classical
  set G := H.locGen Z M hkK hL hR with hGdef
  -- the finite set of window blocks of layer `i`
  set P : Finset (Torus S.d (M * n k * S.L ^ (k - i))) :=
    Finset.univ.filter fun b => IsWindowBlock G (H.locFine Z M (S.k1 k)) (S.k1 k) ⟨i, b⟩ with hP
  have hset : {b : BlockV S.d S.L (M * n k) k |
      IsWindowBlock G (H.locFine Z M (S.k1 k)) (S.k1 k) b ∧ b.1 = i} =
      (fun b => (⟨i, b⟩ : BlockV S.d S.L (M * n k) k)) '' (P : Set _) := by
    ext b
    rcases b with ⟨i', b⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, hP, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, rfl⟩
      exact ⟨b, hw, rfl⟩
    · rintro ⟨b', hw, he⟩
      have h1 : i = i' := (congrArg Sigma.fst he)
      subst h1
      have : b' = b := by simpa using he
      subst this
      exact ⟨hw, rfl⟩
  rw [hset, Set.ncard_image_of_injective _ (fun a b h => by simpa using h), Set.ncard_coe_finset]
  -- count the sites
  have hq : (H.bk k Z).q = S.k1 k := hW.core_k1.symm
  have hcov := hW.cover (i + 1) (by omega) (by omega)
  have hlin : (H.lin (i + 1) k Z).card ≤ S.numax k * S.crit k ^ S.d := by
    calc (H.lin (i + 1) k Z).card ≤ (H.bk k Z).nu * S.crit (i + 1) ^ S.d := card_le_of_coveredBy hcov
      _ ≤ S.numax k * S.crit k ^ S.d := by
          refine Nat.mul_le_mul hW.nu_le ?_
          exact Nat.pow_le_pow_left (H.F.ok.crit_mono (by omega)) _
  have hfine : H.locFine Z M (i + 1) =
      fineSet (S := S) (n := n) M k (i + 1) ((H.lin (i + 1) k Z : Finset _) : Set _) := by
    unfold locFine; rw [locRH_Z Z (by omega) (by omega)]
  set F : Finset (Torus S.d (M * n k * S.L ^ k)) := (Set.toFinite (H.locFine Z M (i + 1))).toFinset
    with hF
  have hFcard : F.card = (S.L ^ (i + 1) * M) ^ S.d * (H.lin (i + 1) k Z).card := by
    rw [hF, ← Set.ncard_eq_toFinset_card _ (Set.toFinite _), hfine]
    exact card_fineSet (hnn_k H hkK) (by omega) _
  have hsites := card_blocks_mul_le (d := S.d) (L := S.L) (N₀ := M * n k) (k := k) (i := i)
    hik.le P F (by
      intro b hb x hx
      have hw := (Finset.mem_filter.mp hb).2
      have hxlay : x ∈ G.layer i := (hw.2.2 x hx).1
      have hx2 : x ∉ G.Ω (i + 1) := (G.mem_layer.1 hxlay).2
      exact (Set.toFinite _).mem_toFinset.mpr
        (compl_Omega_subset (hkK := hkK) (hL := hL) (hR := hR) (by omega) (by omega) hx2))
  have hLpos : 0 < (S.L ^ i) ^ S.d := by
    have := NeZero.pos S.L
    positivity
  have h3 : P.card * (S.L ^ i) ^ S.d ≤ (S.L ^ i) ^ S.d * ((S.L * M) ^ S.d * (S.numax k * S.crit k ^ S.d)) := by
    refine hsites.trans ?_
    rw [hFcard]
    calc (S.L ^ (i + 1) * M) ^ S.d * (H.lin (i + 1) k Z).card
        ≤ (S.L ^ (i + 1) * M) ^ S.d * (S.numax k * S.crit k ^ S.d) :=
          Nat.mul_le_mul_left _ hlin
      _ = (S.L ^ i) ^ S.d * ((S.L * M) ^ S.d * (S.numax k * S.crit k ^ S.d)) := by
          rw [show S.L ^ (i + 1) * M = S.L ^ i * (S.L * M) by ring, mul_pow]; ring
  have h4 : P.card ≤ (S.L * M) ^ S.d * (S.numax k * S.crit k ^ S.d) := by
    rw [mul_comm P.card] at h3
    exact Nat.le_of_mul_le_mul_left h3 hLpos
  calc P.card ≤ (S.L * M) ^ S.d * (S.numax k * S.crit k ^ S.d) := h4
    _ = S.numax k * ((S.L : ℕ) * M * S.crit k) ^ S.d := by rw [mul_pow, mul_pow]; ring

end RegionHistory

end Balaban.LargeField
