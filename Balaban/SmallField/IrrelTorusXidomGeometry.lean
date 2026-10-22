/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomData
public import Balaban.SmallField.XiFour
public import Balaban.SmallField.GsSpecCounter

/-!
# Neighboring level blocks are source interface pairs
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField.Def6
  Balaban.SmallField.GsSpec

variable {d L N₁ m₁ k j : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **Two distinct `j` blocks separated by one block side, both in the layer `j` of a generating
set, form an interface pair** of it. -/
theorem interface_shift_of_layer (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (y : CTorus d L N₁ m₁ k) (μ : Fin d) (hy : y ∈ G.layer j)
    (hy' : y + Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k)) ∈ G.layer j)
    (hdiff : jBlock d L (N₁ * L ^ m₁) k j
      (y + Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k))) ≠
      jBlock d L (N₁ * L ^ m₁) k j y) :
    IsInterfacePair G (y + Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k))) y := by
  have h1 : y ∈ G.Ω 1 := G.layer_subset hj1 hjk hy
  have h1' := G.layer_subset hj1 hjk hy'
  have hl : G.layerIndex y = j := G.layerIndex_eq hj1 hjk hy
  have hl' := G.layerIndex_eq hj1 hjk hy'
  obtain ⟨v, w, hv, hw, hadj⟩ := exists_adjacent_blocks (N₀ := N₁ * L ^ m₁) hjk μ y
  rcases hadj with hadj | heq
  · refine ⟨(mem_dataSites G).2 (Or.inl h1'), (mem_dataSites G).2 (Or.inl h1),
        Or.inl (by rw [hl, hl']), ?_⟩
    refine ⟨w, ?_, v, ?_, Adj.symm ⟨μ, Or.inl hadj⟩⟩
    · rw [blockSet_of_mem G h1', hl']
      exact G.mem_blk.2 hw
    · rw [blockSet_of_mem G h1, hl]
      exact G.mem_blk.2 hv
  · subst w
    exact False.elim (hdiff (hw.symm.trans hv))

/-- Two distinct `j` blocks separated by one block side form an interface pair of the
whole-level generating set (the instance of `interface_shift_of_layer`). -/
theorem levelGS_interface_shift (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (y : CTorus d L N₁ m₁ k) (μ : Fin d)
    (hdiff : jBlock d L (N₁ * L ^ m₁) k j
      (y + Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k))) ≠
      jBlock d L (N₁ * L ^ m₁) k j y) :
    IsInterfacePair
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk)
      (y + Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k))) y :=
  interface_shift_of_layer _ hj1 hjk y μ
    ((GeneratingSet.mem_layer _).2 ⟨by simp [levelGS_Ω], by simp [levelGS_Ω]⟩)
    ((GeneratingSet.mem_layer _).2 ⟨by simp [levelGS_Ω], by simp [levelGS_Ω]⟩) hdiff

/-- **At a positive scale gap, the `j` block translated by one block side is another block**
(`j < k`, `L ≥ 2`). -/
theorem jBlock_add_single_ne (hL : 2 ≤ L) (hjk : j < k) (y : CTorus d L N₁ m₁ k) (μ : Fin d) :
    jBlock d L (N₁ * L ^ m₁) k j
      (y + Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k))) ≠
      jBlock d L (N₁ * L ^ m₁) k j y := by
  have hpow : 2 ≤ L ^ (k - j) := by
    have he : k - j = (k - j - 1) + 1 := by omega
    rw [he, pow_succ]
    exact hL.trans (Nat.le_mul_of_pos_left L (pow_pos (by omega : 0 < L) _))
  have hfactor : 0 < N₁ * L ^ m₁ :=
    Nat.mul_pos (NeZero.pos N₁) (pow_pos (NeZero.pos L) _)
  have hside : 2 ≤ N₁ * L ^ m₁ * L ^ (k - j) :=
    hpow.trans (Nat.le_mul_of_pos_left _ hfactor)
  have hone : (1 : ZMod (N₁ * L ^ m₁ * L ^ (k - j))) ≠ 0 := by
    intro he
    have := (ZMod.one_eq_zero_iff).1 he
    omega
  intro he
  rw [jBlock_add_shift hjk.le] at he
  have hs : (Pi.single μ (1 : ZMod (N₁ * L ^ m₁ * L ^ (k - j))) :
      Torus d (N₁ * L ^ m₁ * L ^ (k - j))) = 0 := by
    apply add_left_cancel (a := jBlock d L (N₁ * L ^ m₁) k j y)
    simpa using he
  have hμ := congrFun hs μ
  have hμ' : (1 : ZMod (N₁ * L ^ m₁ * L ^ (k - j))) = 0 := by
    simpa only [Pi.single_eq_same, Pi.zero_apply] using hμ
  exact hone hμ'

/-- **At a positive scale gap, two cells of the layer `j` of a generating set one block side apart
form an interface pair** (`interface_shift_of_layer`, `jBlock_add_single_ne`). -/
theorem interface_shift_of_layer_of_gap (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (hL : 2 ≤ L)
    (hj1 : 1 ≤ j) (hjk : j < k) (y : CTorus d L N₁ m₁ k) (μ : Fin d) (hy : y ∈ G.layer j)
    (hy' : y + Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k)) ∈ G.layer j) :
    IsInterfacePair G (y + Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k))) y :=
  interface_shift_of_layer G hj1 hjk.le y μ hy hy' (jBlock_add_single_ne hL hjk y μ)

/-- At a positive scale gap, translated level blocks are distinct, so the interface pair
condition is automatic. -/
theorem levelGS_interface_shift_of_gap (hL : 2 ≤ L) (hj1 : 1 ≤ j) (hjk : j < k)
    (y : CTorus d L N₁ m₁ k) (μ : Fin d) :
    IsInterfacePair
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk.le)
      (y + Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k))) y :=
  levelGS_interface_shift hj1 hjk.le y μ (jBlock_add_single_ne hL hjk y μ)

omit [NeZero N₁] [NeZero L] in
/-- The pullback of a unit lattice step is one level-block step on the fine torus. -/
theorem ibase_add_single (x : Site d) (μ : Fin d) :
    ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1) =
      ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x +
        Pi.single μ ((L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ k)) := by
  funext i
  by_cases hi : i = μ
  · subst i
    simp [ibase, Pi.add_apply, Pi.single_eq_same]
    ring
  · simp [ibase, Pi.add_apply, Pi.single_eq_of_ne hi]

end Balaban.SmallField

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField.Def6
  Balaban.SmallField.GsSpec

variable {d L N₁ m₁ k N j : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {ν τ ζ σ ε K₂ : ℝ}
  {p : CTorus d L N₁ m₁ k → Fin N → ℝ} {h : Fin N → ℝ}
  {z h' : CTorus d L N₁ m₁ k → Fin N → ℂ}

/-- On the whole-level generating set, the geometric pullback conditions of
`dataHypAniso_of_pullback` follow from a positive scale gap. -/
theorem ScaledPsiC.dataHypAniso_of_levelGS
    (hL : 2 ≤ L) (hj1 : 1 ≤ j) (hjk : j < k)
    (H : ScaledPsiC
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk.le)
      ν τ ζ j p h z h')
    (y : CTorus d L N₁ m₁ k) (f : Site d → CTorus d L N₁ m₁ k)
    (hf : f = fun x => y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)
    (ψ : Site d → Spin N) (b : Spin N)
    (hψ : ∀ x i, ψ x i = (p (f x) i : ℂ) + z (f x) i)
    (hb : b = (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • fun i => (h i : ℂ) + h' (f 0) i))
    (hsharp : ∀ x, ‖∑ i, ((p (f x) i : ℂ) + z (f x) i) *
          ((p (f x) i : ℂ) + z (f x) i) -
        ∑ i, (p (f x) i : ℂ) * (p (f x) i : ℂ)‖ < τ ^ 2 * ζ)
    (hν : 0 < ν * ((L : ℝ) ^ j) ^ 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hντ : ν * ((L : ℝ) ^ j) ^ 2 ≤ τ ^ 2)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1 / 200)
    (hsqNum : 2 * τ ^ 2 * ζ ≤ σ ^ 2 * ε)
    (hadjNum : 2 * τ * ζ ≤ σ * ε)
    (hcloseNum : 10 * τ ^ 2 * ζ ≤ σ ^ 2 * ε)
    (hlongNum : 98 * τ ^ 2 * ζ ^ 2 ≤ σ ^ 2 * ε ^ 2)
    {Dom : Set ((Site d → Spin N) × Spin N)}
    (hchart : (ψ, b) ∈ Dom ∧ ((fun _ => ψ 0), b) ∈ Dom)
    (hK₂ : 0 ≤ K₂)
    (hsec : ∀ x μ μ', ‖ψ (x + Pi.single μ 1 + Pi.single μ' 1) -
      ψ (x + Pi.single μ 1) - ψ (x + Pi.single μ' 1) + ψ x‖ ≤ K₂) :
    DataHypAniso Dom (ν * ((L : ℝ) ^ j) ^ 2) σ ε K₂ ψ b := by
  subst f
  apply ScaledPsiC.dataHypAniso_of_pullback H
    (fun x => y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)
    ψ b hψ hb
  · intro x
    constructor
    · simp [levelGS_Ω, hj1]
    · exact levelGS_layerIndex hj1 hjk.le _
  · intro x μ
    simpa only [ibase_add_single, add_assoc] using
      levelGS_interface_shift_of_gap hL hj1 hjk
        (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x) μ
  · exact hsharp
  · exact hν
  · exact hτ
  · exact hτ1
  · exact hντ
  · exact hζ
  · exact hζ1
  · exact hsqNum
  · exact hadjNum
  · exact hcloseNum
  · exact hlongNum
  · exact hchart
  · exact hK₂
  · exact hsec

end Balaban.SmallField
