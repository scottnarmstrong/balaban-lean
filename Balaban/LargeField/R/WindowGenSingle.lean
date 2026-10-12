module

public import Balaban.LargeField.Operators.MainAction
public import Balaban.LargeField.R.WindowGenLeaf

/-!
# The single-scale action and the layer decomposition of the multiscale action

* `singleGen`: the generating set `T^{(q)}_1` of the single-scale action (`Ω_n = T` for `1 ≤ n ≤ q`):
  `actionG singleGen` has only the block term at scale `q`; `actionG_single` computes it;
* `actionG_blocks`: for a set `X ⊂ Ω₁`, with `X ∩ Λ_n` a union of `n`-blocks for every `n`,
  the block part of `actionG G` is the sum over the sites `s` of `X` of the term of the leaf of `s`,
  divided by the number of sites of the leaf.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Finset

section Single

variable (d L N₀ q : ℕ) [NeZero N₀] [NeZero L] (ϱ : ℝ)

open Classical in
/-- The generating set `T^{(q)}_1` of the single-scale action: `Ω_n = T` for `n ≤ q`. -/
noncomputable def singleGen : GeneratingSet d L N₀ q ϱ where
  Ω := fun j => if j ≤ q then Finset.univ else ∅
  top := by simp
  subset := by
    intro j _ _
    by_cases h : j + 1 ≤ q
    · simp [h, show j ≤ q by omega]
    · simp [h]
  blockUnion := by
    intro j hj1 hjq x x' _
    simp [hjq]
  separation := by
    intro j hj1 hjq x hx
    exfalso
    apply hx
    simp [show j ≤ q by omega]

variable {d L N₀ q ϱ}

open Classical in
theorem singleGen_Ω {j : ℕ} (hj : j ≤ q) : (singleGen d L N₀ q ϱ).Ω j = Finset.univ := by
  simp [singleGen, hj]

open Classical in
theorem singleGen_Ω_succ : (singleGen d L N₀ q ϱ).Ω (q + 1) = ∅ := by
  simp [singleGen]

theorem lam_single_self (hq : 1 ≤ q) :
    lam (singleGen d L N₀ q ϱ) q = Finset.univ := by
  unfold lam
  have hq0 : q ≠ 0 := by omega
  simp only [hq0, ↓reduceIte]
  ext x
  simp [GeneratingSet.layer, singleGen_Ω le_rfl, singleGen_Ω_succ]

theorem lam_single_of_lt (hq : 1 ≤ q) {n : ℕ} (hn : n < q) :
    lam (singleGen d L N₀ q ϱ) n = ∅ := by
  unfold lam
  by_cases h0 : n = 0
  · subst h0
    simp [singleGen_Ω (show 1 ≤ q from hq)]
  · simp only [h0, ↓reduceIte]
    ext x
    simp [GeneratingSet.layer, singleGen_Ω hn.le, singleGen_Ω (show n + 1 ≤ q by omega)]

/-- The single-scale action: only the block term at scale `q` survives. -/
theorem actionG_single {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (hq : 1 ≤ q)
    (a : ℕ → ℝ) (μ : ℝ) (h : E) (X : Finset (Site d L N₀ q))
    (ψ : (m : ℕ) → Blk d L N₀ q m → E) (φ : Site d L N₀ q → E) :
    actionG (singleGen d L N₀ q ϱ) a μ h X ψ φ =
      (1 / 2) * ∑ y ∈ tBlocks d L N₀ q q X,
          a q * (L : ℝ) ^ (q * (d - 2)) * ‖ψ q y - bavgL d L N₀ q q φ y‖ ^ 2 +
        (1 / 2) * bondE X φ + μ / 2 * ∑ x ∈ X, ‖φ x - h‖ ^ 2 := by
  unfold actionG
  congr 2
  rw [Finset.sum_eq_single q]
  · rw [lam_single_self hq, Finset.univ_inter]
  · intro n hn hne
    have hn' := Finset.mem_Icc.1 hn
    rw [lam_single_of_lt hq (by omega)]
    simp [tBlocks]
  · intro h
    exfalso; exact h (Finset.mem_Icc.2 ⟨hq, le_rfl⟩)

end Single

section Blocks

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- The field of the leaf of `s`: `ψ_{n_s}` at the `n_s`-block of `s` (the window field `ψ^G`). -/
noncomputable def leafField (G : GeneratingSet d L N₀ q ϱ) (ψ : (m : ℕ) → Blk d L N₀ q m → E)
    (s : Site d L N₀ q) : E :=
  ψ (G.layerIndex s) (blkMap d L N₀ q (G.layerIndex s) s)

/-- The block average of `φ` over the leaf of `s`, `(Q_{n_s} φ)`. -/
noncomputable def leafAvg (G : GeneratingSet d L N₀ q ϱ) (φ : Site d L N₀ q → E)
    (s : Site d L N₀ q) : E :=
  bavgL d L N₀ q (G.layerIndex s) φ (blkMap d L N₀ q (G.layerIndex s) s)

/-- **Layer decomposition of the block part of the multiscale action**: for `X ⊂ Ω₁` with `X ∩ Λ_n`
a union of `n`-blocks, the block part is the sum over the sites `s ∈ X` of
`a_{n_s}(L^{n_s})⁻² ‖ψ^G(s) - (Q_{n_s}φ)(s)‖²`. -/
theorem blockPart_eq (G : GeneratingSet d L N₀ q ϱ) (hd : 2 ≤ d) (a : ℕ → ℝ)
    (X : Finset (Site d L N₀ q))
    (hX : ∀ n, 1 ≤ n → n ≤ q → IsBlockUnion L N₀ q n (X ∩ G.layer n))
    (hXΩ : ∀ s ∈ X, s ∈ G.Ω 1) (ψ : (m : ℕ) → Blk d L N₀ q m → E) (φ : Site d L N₀ q → E) :
    ∑ n ∈ Finset.Icc 1 q, ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
        a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2 =
      ∑ s ∈ X, a (G.layerIndex s) / ((L : ℝ) ^ G.layerIndex s) ^ 2 *
        ‖leafField G ψ s - leafAvg G φ s‖ ^ 2 := by
  classical
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hmaps : ∀ s ∈ X, G.layerIndex s ∈ Finset.Icc 1 q := fun s hs => by
    obtain ⟨h1, h2, -⟩ := G.layerIndex_spec (hXΩ s hs)
    exact Finset.mem_Icc.2 ⟨h1, h2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_Icc.1 hn
  have hfil : X.filter (fun s => G.layerIndex s = n) = lam G n ∩ X := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_inter, mem_lam_iff G hn'.2]
    tauto
  rw [hfil]
  have hU : IsBlockUnion L N₀ q n (lam G n ∩ X) := isBlockUnion_lam G hX hn'.2
  have h1 := sum_blkMap (E := ℝ) hn'.2 hU
    (fun y => a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2)
  have hcard : (((L ^ n : ℕ) : ℝ) ^ d) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast pow_ne_zero n (NeZero.ne L))
  have h2 : ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
      a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2 =
      (((L ^ n : ℕ) : ℝ) ^ d)⁻¹ * ∑ s ∈ lam G n ∩ X,
        a n * (L : ℝ) ^ (n * (d - 2)) *
          ‖ψ n (blkMap d L N₀ q n s) - bavgL d L N₀ q n φ (blkMap d L N₀ q n s)‖ ^ 2 := by
    rw [h1, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsn : G.layerIndex s = n := (mem_lam_iff G hn'.2 s).1 (Finset.mem_inter.1 hs).1
  unfold leafField leafAvg
  rw [hsn]
  have e : (((L ^ n : ℕ) : ℝ) ^ d)⁻¹ * (L : ℝ) ^ (n * (d - 2)) = (((L : ℝ) ^ n) ^ 2)⁻¹ := by
    have : ((L : ℝ) ^ n) ^ d = (L : ℝ) ^ (n * (d - 2)) * ((L : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← mul_add]
      congr 2
      omega
    push_cast
    rw [this]
    have : (L : ℝ) ^ (n * (d - 2)) ≠ 0 := pow_ne_zero _ hLpos.ne'
    have : (L : ℝ) ^ n ≠ 0 := pow_ne_zero _ hLpos.ne'
    field_simp
  rw [← mul_assoc, ← mul_assoc]
  calc _ = (((L ^ n : ℕ) : ℝ) ^ d)⁻¹ * (L : ℝ) ^ (n * (d - 2)) * a n *
        ‖ψ n (blkMap d L N₀ q n s) - bavgL d L N₀ q n φ (blkMap d L N₀ q n s)‖ ^ 2 := by ring
    _ = _ := by rw [e]; ring

end Blocks

end Balaban.LargeField
