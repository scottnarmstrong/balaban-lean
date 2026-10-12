module

public import Balaban.LargeField.R.WindowRegSet
public import Balaban.LargeField.Characteristic.OperatorDomain
public import Balaban.LargeField.R.ChainSeq
public import Balaban.LargeField.LF1.BlockArith
import Mathlib.Tactic.Linarith

/-!
# The bond bound on the regularity set from the retained domain condition (COLLAR-FIX §2)

The retained restriction (1.24) of Definition II.3.4 at `j = q - 1` is the first clause of the landed
`ChiDomProp`: for every `π_q`-cube `□ ⊂ Z_q ∩ Ω^∼_q` the multiscale field lies in `Ψ̃(𝔹_k ∩ □^∼; 3dLδ_{q-1})`.
It tests adjacent blocks of the *same* layer in `𝔹_k ∩ □^∼` at `3dLδ_{q-1}` (not `3δ_q`), so the
tolerance obtained is `3dLδ_{q-1}`, and with Lemma III.4.5 (`δ_{q-1} ≤ e^ε L^{(d-2)/2} δ_q`) the constant is
`C_reg = 3dL e^ε L^{(d-2)/2}` of COLLAR-FIX §2.

* `exists_adjSites_of_adjT`: adjacent blocks contain nearest-neighbour sites;
* `bond_lt_of_chiDomProp`: the bond bound `‖ψ_q(b) - ψ_q(b')‖ < 3dLδ_{q-1}` for adjacent `q`-blocks `b, b'`
  of layer `q` of `B` lying in the one-neighbourhood of a cube `□` of the support;
* `bond_le_Creg_of_chiDomProp`: the bound `C_reg δ_q`, `C_reg = 3dL e^ε L^{(d-2)/2}`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

section Lift

variable {d ℓ N m : ℕ}

/-- Adjacent blocks `y' = y + e_μ` contain nearest-neighbour sites `x ∈ y`, `x + e_μ ∈ y'`. -/
theorem exists_adjSites_of_adjT [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m) {y y' : Torus d m}
    (μ : Fin d) (h : y' = y + Pi.single μ 1) :
    ∃ x : Torus d ℓ, blockMap N m x = y ∧ blockMap N m (x + Pi.single μ 1) = y' := by
  have hN : 1 ≤ N := pos_left_of_eq hℓ
  have h1 : N - 1 + 1 = N := Nat.sub_add_cancel hN
  refine ⟨fun i => ((N * (y i).val + (if i = μ then N - 1 else 0) : ℕ) : ZMod ℓ), ?_, ?_⟩
  · funext i
    have := blockCoord_natCast hℓ (y i).val (if i = μ then N - 1 else 0)
      (by split_ifs <;> omega)
    simp only [blockMap]
    rw [this, ZMod.natCast_zmod_val]
  · funext i
    by_cases hi : i = μ
    · subst hi
      have e : ((N * (y i).val + (N - 1) : ℕ) : ZMod ℓ) + 1 =
          ((N * ((y i).val + 1) + 0 : ℕ) : ZMod ℓ) := by
        have : N * (y i).val + (N - 1) + 1 = N * ((y i).val + 1) + 0 := by
          rw [add_assoc, h1]; ring
        rw [← this]; exact (Nat.cast_succ _).symm
      have := blockCoord_natCast hℓ ((y i).val + 1) 0 (by omega)
      simp only [blockMap, Pi.add_apply, Pi.single_eq_same, h, ite_true]
      rw [e, this]; push_cast; rw [ZMod.natCast_zmod_val]
    · have := blockCoord_natCast hℓ (y i).val 0 (by omega)
      simp only [blockMap, Pi.add_apply, Pi.single_eq_of_ne hi, add_zero, h, hi, ite_false]
      simpa [ZMod.natCast_zmod_val] using this

end Lift

section Bond

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M] [NeZero S.L]
  {ϱ : ℝ} {N : ℕ}

/-- Adjacent blocks of one layer `q ≤ K` (`AdjT`) are `BlockAdj`-adjacent. -/
theorem blockAdj_of_adjT {q : ℕ} (hqK : q ≤ K) {b b' : BlockAt S n M K q} (h : AdjT b b') :
    BlockAdj (S := S) (n := n) (M := M) (K := K) ⟨q, b⟩ ⟨q, b'⟩ := by
  obtain ⟨-, μ, h | h⟩ := h
  · obtain ⟨x, hx, hx'⟩ := exists_adjSites_of_adjT (side_eq (N₀ := M * n K) (L := S.L) hqK) μ h
    exact ⟨x, x + Pi.single μ 1, hx, hx', ⟨μ, Or.inl rfl⟩⟩
  · obtain ⟨x, hx, hx'⟩ := exists_adjSites_of_adjT (side_eq (N₀ := M * n K) (L := S.L) hqK) μ h
    exact ⟨x + Pi.single μ 1, x, hx', hx, ⟨μ, Or.inr rfl⟩⟩

variable (a : LocalHistory S n M K) (k : ℕ) (B : GeneratingSet S.d S.L (M * n K) K ϱ)
  (Zc : Set (Torus S.d (M * n K * S.L ^ K))) (δ p0 : ℕ → ℝ) (Cpsi : ℝ)
  (ψ ψ' : MultiField S n M K N)

/-- **The bond bound from the retained (1.24)** (Definition II.3.4, first clause of `ChiDomProp` at
`j = q - 1`): if the configuration `(ψ, ψ')` lies in the support of the domain indicator, then for a
`π_q`-cube `□ = y` with `□ ⊂ Z_q` and `□ ⊂ Ω^∼_q`, adjacent `q`-blocks `b, b'` of layer `q` of `𝔹_k`
whose sites meet `□^∼` satisfy `‖ψ_q(b) - ψ_q(b')‖ < 3dLδ_{q-1}`.  Applies to the interior blocks
`b ∈ regSetT` (taking `y` the cube of `b`) and to the first exterior window block `b'` adjacent to
it (layer `q`, in `□^∼`). -/
theorem bond_lt_of_chiDomProp (hdom : ChiDomProp a k B Zc δ p0 Cpsi ψ ψ') {j : ℕ} (hj : j < k)
    {y : Torus S.d (n (j + 1))} (hy : CubeSub (S := S) (n := n) M K (j + 1) y (a.Z (j + 1)))
    (hyO : y ∈ lhOmegaSim a k (j + 1)) (hjK : j + 1 ≤ K) {b b' : BlockAt S n M K (j + 1)}
    (hb : ∃ x ∈ B.layer (j + 1), jBlock S.d S.L (M * n K) K (j + 1) x = b ∧
      cubeMap n S.L M K (j + 1) x ∈ nbhd 1 {y})
    (hb' : ∃ x ∈ B.layer (j + 1), jBlock S.d S.L (M * n K) K (j + 1) x = b' ∧
      cubeMap n S.L M K (j + 1) x ∈ nbhd 1 {y})
    (hadj : AdjT b b') :
    ‖ψ (j + 1) b - ψ (j + 1) b'‖ < 3 * S.d * S.L * δ j := by
  have h1 := (hdom.1 j hj y hy hyO).1
  exact h1 ⟨j + 1, b⟩ ⟨Nat.succ_pos j, hjK, hb⟩ ⟨j + 1, b'⟩ ⟨Nat.succ_pos j, hjK, hb'⟩ (Or.inl rfl)
    (blockAdj_of_adjT hjK hadj)

/-- **The bond bound with the constant `C_reg`** of COLLAR-FIX §2: with Lemma III.4.5 for the sequence
(`δ_j ≤ e^ε L^{(d-2)/2} δ_{j+1}`; `hδ : IsAdmDelta d L ε j (j+1) δ`), `‖ψ_q(b) - ψ_q(b')‖ ≤ C_reg δ_q`,
`q = j + 1`, `C_reg = 3dL e^ε L^{(d-2)/2}`. -/
theorem bond_le_Creg_of_chiDomProp (hdom : ChiDomProp a k B Zc δ p0 Cpsi ψ ψ') {j : ℕ} (hj : j < k)
    {y : Torus S.d (n (j + 1))} (hy : CubeSub (S := S) (n := n) M K (j + 1) y (a.Z (j + 1)))
    (hyO : y ∈ lhOmegaSim a k (j + 1)) (hjK : j + 1 ≤ K) {b b' : BlockAt S n M K (j + 1)}
    (hb : ∃ x ∈ B.layer (j + 1), jBlock S.d S.L (M * n K) K (j + 1) x = b ∧
      cubeMap n S.L M K (j + 1) x ∈ nbhd 1 {y})
    (hb' : ∃ x ∈ B.layer (j + 1), jBlock S.d S.L (M * n K) K (j + 1) x = b' ∧
      cubeMap n S.L M K (j + 1) x ∈ nbhd 1 {y})
    (hadj : AdjT b b') {ε : ℝ} (hδ : IsAdmDelta S.d S.L ε j (j + 1) δ) :
    ‖ψ (j + 1) b - ψ (j + 1) b'‖ ≤
      (3 * S.d * S.L * Real.exp ε * (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2)) * δ (j + 1) := by
  have h := bond_lt_of_chiDomProp a k B Zc δ p0 Cpsi ψ ψ' hdom hj hy hyO hjK hb hb' hadj
  have hg := hδ.growth j (j + 1) le_rfl (Nat.le_succ j) le_rfl
  have e : (((j + 1 : ℕ) : ℝ) - (j : ℝ)) = 1 := by push_cast; ring
  rw [e, mul_one] at hg
  have h0 : (0 : ℝ) ≤ 3 * S.d * S.L := by positivity
  calc ‖ψ (j + 1) b - ψ (j + 1) b'‖ ≤ 3 * S.d * S.L * δ j := h.le
    _ ≤ 3 * S.d * S.L * (Real.exp ε * (S.L : ℝ) ^ (((S.d : ℝ) - 2) / 2) * δ (j + 1)) :=
        mul_le_mul_of_nonneg_left hg h0
    _ = _ := by ring

end Bond

end Balaban.LargeField
