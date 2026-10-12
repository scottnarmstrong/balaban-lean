/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroHessTop
public import Balaban.LargeField.R.PsiZeroTube
public import Balaban.LargeField.LF1

/-!
# The top-layer pair sum is the Dirichlet form (PSIZERO-HESS §5, row 5)

`layer_isBlockUnion`: the layers of a generating set are unions of blocks of their own scale.
`pairSum_ge_dirichlet`: on a torus of side `≥ 3` the unordered pair sum `pairSumT` of a function dominates the
Dirichlet sum `∑_x ∑_μ ‖f(x + e_μ) - f(x)‖²` (each bond is counted once, with no factor-of-two loss).
`top_pairSum_dirichlet`: for a perturbation `v` supported in a box `Z` with `OverTop G (Z ∪ shellOut Z)` the pair sum
over the `k`-blocks meeting `Ω_k` of `t ṽ` is at least `t²` times the Dirichlet form of the zero extension `ṽ`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Finset

section Pair

theorem layer_isBlockUnion {d L N₀ q : ℕ} {ϱ : ℝ} [NeZero N₀] [NeZero L] (G : GeneratingSet d L N₀ q ϱ)
    {n : ℕ} (hn1 : 1 ≤ n) (hnq : n ≤ q) : IsBlockUnion L N₀ q n (G.Ω 1 ∩ G.layer n) := by
  intro x x' h
  have h1 : x ∈ G.layer n ↔ x' ∈ G.layer n := by
    have hΩ := G.blockUnion n hn1 hnq x x' h
    rw [G.mem_layer, G.mem_layer]
    refine and_congr hΩ (not_congr ?_)
    by_cases hnq' : n + 1 ≤ q
    · exact G.blockUnion (n + 1) (by omega) hnq' x x' (jBlock_eq_of_le (by omega) hnq' h)
    · have : n = q := by omega
      subst this
      simp [G.top]
  constructor
  · intro hx
    exact Finset.mem_inter.2 ⟨G.layer_subset hn1 hnq (h1.1 (Finset.mem_inter.1 hx).2),
      h1.1 (Finset.mem_inter.1 hx).2⟩
  · intro hx
    exact Finset.mem_inter.2 ⟨G.layer_subset hn1 hnq (h1.2 (Finset.mem_inter.1 hx).2),
      h1.2 (Finset.mem_inter.1 hx).2⟩

section Dirichlet

variable {d ℓ : ℕ} [NeZero ℓ] {E : Type*} [NormedAddCommGroup E]

theorem single_one_ne_zero (hℓ : 2 ≤ ℓ) (μ : Fin d) : (Pi.single μ (1 : ZMod ℓ) : Torus d ℓ) ≠ 0 := by
  intro h
  have hf : Fact (1 < ℓ) := ⟨by omega⟩
  have h1 := congrFun h μ
  simp only [Pi.single_eq_same, Pi.zero_apply] at h1
  exact one_ne_zero h1

theorem add_single_inj (hℓ : 3 ≤ ℓ) (y : Torus d ℓ) (μ ν : Fin d) (s t : Bool)
    (h : y + (if s then Pi.single μ (1 : ZMod ℓ) else -Pi.single μ (1 : ZMod ℓ)) =
      y + (if t then Pi.single ν (1 : ZMod ℓ) else -Pi.single ν (1 : ZMod ℓ))) : μ = ν ∧ s = t := by
  have hf : Fact (1 < ℓ) := ⟨by omega⟩
  have h2 : (2 : ZMod ℓ) ≠ 0 := by
    intro h2
    have h3 : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have h := add_left_cancel h
  by_cases hμν : μ = ν
  · subst hμν
    refine ⟨rfl, ?_⟩
    have hc := congrFun h μ
    cases s <;> cases t
    · rfl
    · simp only [Bool.false_eq_true, ↓reduceIte, Pi.neg_apply, Pi.single_eq_same] at hc
      exact absurd (by linear_combination -hc) h2
    · simp only [Bool.false_eq_true, ↓reduceIte, Pi.neg_apply, Pi.single_eq_same] at hc
      exact absurd (by linear_combination hc) h2
    · rfl
  · exfalso
    have hc := congrFun h μ
    cases s <;> cases t <;> simp [hμν] at hc

open Classical in
/-- **The pair sum dominates the Dirichlet sum** (side `≥ 3`, no factor-of-two loss). -/
theorem pairSumT_ge_dirichlet (hℓ : 3 ≤ ℓ) (T : Finset (Torus d ℓ)) (f : Torus d ℓ → E)
    (hT : ∀ (x : Torus d ℓ) (μ : Fin d), f (x + Pi.single μ 1) ≠ f x →
      x ∈ T ∧ x + Pi.single μ 1 ∈ T) :
    ∑ x, ∑ μ : Fin d, ‖f (x + Pi.single μ 1) - f x‖ ^ 2 ≤ pairSumT T f := by
  have hℓ2 : 2 ≤ ℓ := by omega
  -- terms outside `T × T` vanish
  have hz : ∀ y y' : Torus d ℓ, ¬ (y ∈ T ∧ y' ∈ T) →
      (if AdjT y y' then ‖f y - f y'‖ ^ 2 else 0) = 0 := by
    intro y y' hyy
    by_cases hA : AdjT y y'
    · obtain ⟨-, μ, hμ | hμ⟩ := id hA
      · have hfe : f y' = f y := by
          by_contra hne
          have h1 := hT y μ (by rw [← hμ]; exact hne)
          exact hyy ⟨h1.1, by rw [hμ]; exact h1.2⟩
        simp [hA, hfe]
      · have hfe : f y = f y' := by
          by_contra hne
          have h1 := hT y' μ (by rw [← hμ]; exact hne)
          exact hyy ⟨by rw [hμ]; exact h1.2, h1.1⟩
        simp [hA, hfe]
    · simp [hA]
  have hfull : pairSumT T f = 1 / 2 * ∑ y, ∑ y', (if AdjT y y' then ‖f y - f y'‖ ^ 2 else 0) := by
    unfold pairSumT
    congr 1
    have e1 : ∑ y ∈ T, ∑ y' ∈ T, (if AdjT y y' then ‖f y - f y'‖ ^ 2 else 0) =
        ∑ y ∈ T, ∑ y', (if AdjT y y' then ‖f y - f y'‖ ^ 2 else 0) :=
      Finset.sum_congr rfl fun y hy => Finset.sum_subset (Finset.subset_univ _) fun y' _ hy' =>
        hz y y' fun h => hy' h.2
    rw [e1]
    exact Finset.sum_subset (Finset.subset_univ _) fun y _ hy =>
      Finset.sum_eq_zero fun y' _ => hz y y' fun h => hy h.1
  rw [hfull]
  -- for each `y`, the `2d` neighbours give a lower bound
  have hrow : ∀ y : Torus d ℓ, ∑ μ : Fin d, ‖f y - f (y + Pi.single μ 1)‖ ^ 2 +
      ∑ μ : Fin d, ‖f y - f (y - Pi.single μ 1)‖ ^ 2 ≤
      ∑ y', (if AdjT y y' then ‖f y - f y'‖ ^ 2 else 0) := by
    intro y
    let g : Fin d × Bool → Torus d ℓ := fun p => y + (if p.2 then (Pi.single p.1 1 : Torus d ℓ)
      else -(Pi.single p.1 1 : Torus d ℓ))
    have hginj : Function.Injective g := by
      intro p q hpq
      obtain ⟨h1, h2⟩ := add_single_inj hℓ y p.1 q.1 p.2 q.2 hpq
      exact Prod.ext h1 h2
    have hsum : ∑ p : Fin d × Bool, ‖f y - f (g p)‖ ^ 2 =
        ∑ μ : Fin d, ‖f y - f (y + Pi.single μ 1)‖ ^ 2 +
          ∑ μ : Fin d, ‖f y - f (y - Pi.single μ 1)‖ ^ 2 := by
      rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      simp [g, sub_eq_add_neg]
    rw [← hsum, ← Finset.sum_image (f := fun y' => ‖f y - f y'‖ ^ 2) (s := Finset.univ)
      (g := g) (fun p _ q _ h => hginj h)]
    calc ∑ y' ∈ Finset.univ.image g, ‖f y - f y'‖ ^ 2
        = ∑ y' ∈ Finset.univ.image g, (if AdjT y y' then ‖f y - f y'‖ ^ 2 else 0) := by
          refine Finset.sum_congr rfl fun y' hy' => ?_
          obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy'
          have hA : AdjT y (g p) := by
            refine ⟨?_, p.1, ?_⟩
            · intro h
              have h0 : (if p.2 then (Pi.single p.1 1 : Torus d ℓ) else -(Pi.single p.1 1 : Torus d ℓ)) = 0 := by
                have : y + (if p.2 then (Pi.single p.1 1 : Torus d ℓ) else -(Pi.single p.1 1 : Torus d ℓ)) = y + 0 := by
                  rw [add_zero]; exact h.symm
                exact add_left_cancel this
              cases hb : p.2
              · simp only [hb, Bool.false_eq_true, ↓reduceIte, neg_eq_zero] at h0
                exact single_one_ne_zero hℓ2 p.1 h0
              · simp only [hb, ↓reduceIte] at h0
                exact single_one_ne_zero hℓ2 p.1 h0
            · cases hb : p.2
              · right; simp [g, hb]
              · left; simp [g, hb]
          simp [hA]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by
          split_ifs <;> positivity)
  have hsum1 : ∑ y : Torus d ℓ, ∑ μ : Fin d, ‖f y - f (y + Pi.single μ 1)‖ ^ 2 =
      ∑ x, ∑ μ : Fin d, ‖f (x + Pi.single μ 1) - f x‖ ^ 2 := by
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun μ _ => ?_
    rw [norm_sub_rev]
  have hsum2 : ∑ y : Torus d ℓ, ∑ μ : Fin d, ‖f y - f (y - Pi.single μ 1)‖ ^ 2 =
      ∑ x, ∑ μ : Fin d, ‖f (x + Pi.single μ 1) - f x‖ ^ 2 := by
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← Equiv.sum_comp (Equiv.addRight (Pi.single μ (1 : ZMod ℓ) : Torus d ℓ))]
    exact Finset.sum_congr rfl fun x _ => by simp
  have := Finset.sum_le_sum fun y (_ : y ∈ (Finset.univ : Finset (Torus d ℓ))) => hrow y
  rw [Finset.sum_add_distrib, hsum1, hsum2] at this
  linarith

end Dirichlet

section Top

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ k ϱ}
  {Z : Finset (Torus d (N₀ * L ^ (k - k)))}

/-- The `k`-blocks of `Z ∪ shellOut Z` meet `Ω_k`, hence belong to `T_k(Λ_k ∩ Ω₁)`. -/
theorem mem_tBlocks_top (hk : 1 ≤ k)
    (hΩ : OverTop G ((Z : Set (Torus d (N₀ * L ^ (k - k)))) ∪ shellOut (Z : Set (Torus d (N₀ * L ^ (k - k))))))
    {y : Torus d (N₀ * L ^ (k - k))}
    (hy : y ∈ (Z : Set (Torus d (N₀ * L ^ (k - k)))) ∪ shellOut (Z : Set (Torus d (N₀ * L ^ (k - k))))) :
    y ∈ tBlocks d L N₀ k k (lam G k ∩ G.Ω 1) := by
  have hN : 0 < L ^ k := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) k
  obtain ⟨x, hx⟩ := Balaban.exists_blockMap_eq (fine_eq_block L N₀ k) hN y
  have hxk : x ∈ G.Ω k := hΩ x (by simpa [jBlock] using (hx ▸ hy))
  have h1 : x ∈ G.Ω 1 := G.Ω_antitone le_rfl hk (by omega) hxk
  have hlam : x ∈ lam G k := by
    have : k ≠ 0 := by omega
    simp only [lam, this, ↓reduceIte]
    exact G.mem_layer.2 ⟨hxk, by rw [G.top]; simp⟩
  exact Finset.mem_image.2 ⟨x, Finset.mem_inter.2 ⟨hlam, h1⟩, hx⟩

/-- **Row 5 (`top_pairSum_dirichlet`)**: the pair sum of `t ṽ` over the `k`-blocks meeting `Ω_k` dominates
`t²` times the Dirichlet form of the zero extension `ṽ`. -/
theorem top_pairSum_dirichlet (hk : 1 ≤ k) (hn : 3 ≤ N₀ * L ^ (k - k))
    (hΩ : OverTop G ((Z : Set (Torus d (N₀ * L ^ (k - k)))) ∪ shellOut (Z : Set (Torus d (N₀ * L ^ (k - k))))))
    (v : SuppSpace Z N) (t : ℝ) :
    t ^ 2 * dirichletForm Z v ≤
      pairSumT (tBlocks d L N₀ k k (lam G k ∩ G.Ω 1)) (fun y => t • extSupp Z v y) := by
  have key := pairSumT_ge_dirichlet (d := d) hn (tBlocks d L N₀ k k (lam G k ∩ G.Ω 1))
    (fun y => t • extSupp Z v y) ?_
  · refine le_trans (le_of_eq ?_) key
    unfold dirichletForm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  · intro x μ hne
    have hmem : ∀ y, y ∈ (Z : Set (Torus d (N₀ * L ^ (k - k)))) →
        y ∈ tBlocks d L N₀ k k (lam G k ∩ G.Ω 1) := fun y hy =>
      mem_tBlocks_top hk hΩ (Or.inl hy)
    have hsh : ∀ y, y ∈ (Z : Set (Torus d (N₀ * L ^ (k - k)))) ∪ shellOut (Z : Set (Torus d (N₀ * L ^ (k - k)))) →
        y ∈ tBlocks d L N₀ k k (lam G k ∩ G.Ω 1) := fun y hy => mem_tBlocks_top hk hΩ hy
    by_cases hx : x ∈ (Z : Set (Torus d (N₀ * L ^ (k - k))))
    · refine ⟨hsh x (Or.inl hx), hsh _ ?_⟩
      by_cases hx' : x + Pi.single μ 1 ∈ (Z : Set (Torus d (N₀ * L ^ (k - k))))
      · exact Or.inl hx'
      · exact Or.inr (mem_shellOut_of_adj hx hx' ⟨μ, Or.inl rfl⟩)
    · by_cases hx' : x + Pi.single μ 1 ∈ (Z : Set (Torus d (N₀ * L ^ (k - k))))
      · exact ⟨hsh x (Or.inr (mem_shellOut_of_adj hx' hx ⟨μ, Or.inr rfl⟩)), hsh _ (Or.inl hx')⟩
      · exfalso
        apply hne
        have h1 : extSupp Z v (x + Pi.single μ 1) = 0 := by
          have hx'' : x + Pi.single μ 1 ∉ Z := fun h => hx' (by exact_mod_cast h)
          simp [extSupp, hx'']
        have h2 : extSupp Z v x = 0 := by
          have hx'' : x ∉ Z := fun h => hx (by exact_mod_cast h)
          simp [extSupp, hx'']
        simp [h1, h2]

end Top

end Pair

end Balaban.LargeField
