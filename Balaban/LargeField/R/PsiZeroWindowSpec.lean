/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroSolve
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `PsiZeroSpec` from the cited expansion estimate, with the block tube on `U^∼_k ∖ Z₀`

`psiZeroSpec_of_input` (`PsiZeroSolve`) takes the premise `OverTop G X` (every site in a `k`-block of `X` lies in
`Ω_k(G)`).  Together with `hdata` (the blocks of the data sites `Ω₁ ∪ C(Ω₁)` lie in `X`) it says that
`Ω₁ ∪ C(Ω₁) ⊆ Ω_k`, i.e. that `G` has a single layer; for the actual `𝔹_k(U_k)` (several layers, nonempty collar)
the two premises contradict each other.  `PsiZeroSpec` asks for the tube conditions (R1), (R2) on *all* adjacent
blocks of `Ut ⊇ dataSites`, which the `G`-interface tube `TubeOn G` does not provide over lower layers.

Here the source premise is the tube of the block field on all adjacent blocks of `U^∼_k ∖ Z₀` (`BlockTube`), and
only the blocks of `Z₀ ∪ shellOut Z₀` are required to lie over `Ω_k(G)` (`OverTop`).

* `BlockTube`, `tubeOn_of_blockTube`: `Ψ̃(X; δ)` for the block field on all adjacent blocks implies the `G`-tube;
* `psiZeroSpec_of_input_blockTube`: `PsiZeroSpec` for the solution of (2.34), whose only non-source premise is
  `PsiZeroInput`; it also records `ψ⁰_k = ψ_k` off `Z₀`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

section BlockTube

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L]

/-- **The tube `Ψ̃(X; δ)` of a block field on all adjacent blocks of `X`**: (R1) for adjacent blocks of `X` and
(R2) for the blocks of `X`. -/
def BlockTube (X : Set (Torus d (N₀ * L ^ (k - k)))) (δ : ℝ) (ψ : BlockField d L N₀ k N) : Prop :=
  (∀ y ∈ X, ∀ y' ∈ X, torusAdj y y' → ‖eu (ψ y) - eu (ψ y')‖ < δ) ∧
    ∀ y ∈ X, |∑ i, ψ y i ^ 2 - 1| < δ

theorem BlockTube.mono_set {X Y : Set (Torus d (N₀ * L ^ (k - k)))} (h : X ⊆ Y) {δ : ℝ}
    {ψ : BlockField d L N₀ k N} (ht : BlockTube Y δ ψ) : BlockTube X δ ψ :=
  ⟨fun y hy y' hy' hadj => ht.1 y (h hy) y' (h hy') hadj, fun y hy => ht.2 y (h hy)⟩

theorem BlockTube.mono {X : Set (Torus d (N₀ * L ^ (k - k)))} {δ δ' : ℝ} (h : δ ≤ δ')
    {ψ : BlockField d L N₀ k N} (ht : BlockTube X δ ψ) : BlockTube X δ' ψ :=
  ⟨fun y hy y' hy' hadj => lt_of_lt_of_le (ht.1 y hy y' hy' hadj) h,
    fun y hy => lt_of_lt_of_le (ht.2 y hy) h⟩

/-- The `G`-interface tube follows from the tube on all adjacent blocks. -/
theorem tubeOn_of_blockTube {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
    {X : Set (Torus d (N₀ * L ^ (k - k)))} {δ : ℝ} (hδ : 0 < δ) {ψ : BlockField d L N₀ k N}
    (ht : BlockTube X δ ψ) : TubeOn G X δ ψ := by
  refine ⟨fun x x' hp hx hx' => ?_, fun x _ hx => ?_⟩
  · rcases blocks_of_interface G hp with h | h
    · have : (fun i => liftR ψ x i - liftR ψ x' i) = fun _ => 0 := by
        funext i; simp [liftR, h]
      rw [this]; simpa [rn] using hδ
    · have e : rn (fun i => liftR ψ x i - liftR ψ x' i) =
          ‖eu (ψ (jBlock d L N₀ k k x)) - eu (ψ (jBlock d L N₀ k k x'))‖ := by
        rw [eu_sub, norm_eu]; rfl
      rw [e]; exact ht.1 _ hx _ hx' h
  · exact ht.2 _ hx

theorem abs_norm_sub_one_lt_of_sq {v : EuclideanSpace ℝ (Fin N)} {δ : ℝ}
    (h : |∑ i, v i ^ 2 - 1| < δ) : |‖v‖ - 1| < δ := by
  have e : ∑ i, v i ^ 2 = ‖v‖ ^ 2 := by
    simp [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (v i))]
  rw [e] at h
  have hn : 0 ≤ ‖v‖ := norm_nonneg _
  have : |‖v‖ - 1| ≤ |‖v‖ ^ 2 - 1| := by
    have : ‖v‖ ^ 2 - 1 = (‖v‖ - 1) * (‖v‖ + 1) := by ring
    rw [this, abs_mul, abs_of_pos (by linarith : 0 < ‖v‖ + 1)]
    nlinarith [abs_nonneg (‖v‖ - 1)]
  linarith

/-- **The premises `OverTop G X` and `hdata` of `psiZeroSpec_of_input` are contradictory unless the collar is empty**:
together they put every data site, in particular every site of the collar `C(Ω₁)`, into `Ω_k ⊆ Ω₁`. -/
theorem collar_eq_empty_of_overTop {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (hk : 1 ≤ k)
    {X : Set (Torus d (N₀ * L ^ (k - k)))} (hΩX : OverTop G X)
    (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) : collar G = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have h1 := hΩX x (hdata x ((mem_dataSites G).2 (Or.inr hx)))
  exact ((mem_collar G).1 hx).1 (G.Ω_antitone le_rfl hk (by omega) h1)

end BlockTube

section Spec

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
  [NeZero N] {X : Set (Torus d (N₀ * L ^ (k - k)))}

/-- **`PsiZeroSpec` from the cited expansion estimate**, with the tube of `ψ_k` on all adjacent blocks of
`U^∼_k ∖ Z₀`.  Premises beyond `PsiZeroInput`: the blocks of `Z₀ ∪ shellOut Z₀` lie over `Ω_k(G)`, `Z ⊆ U^∼_k`, the
data blocks lie in `U^∼_k`, the terminal blocks lie off `Z₀`.  Conclusion: `ψ⁰_k` lies in `Ψ̃(U^∼_k; K₆ δ)`
(`PsiZeroSpec`) and equals `ψ_k` off `Z₀`. -/
theorem psiZeroSpec_of_input_blockTube {D : ℕ} (Gk : GeneratingSet d L N₀ k ϱ') (hd : 2 ≤ d) (hk : 1 ≤ k)
    (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ) (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D)
    (hm : D + 2 ≤ N₀ * L ^ (k - k)) (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
    (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
    (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X)
    (Zf : Set (Torus d (N₀ * L ^ k))) (hZX : ∀ x ∈ Zf, jBlock d L N₀ k k x ∈ X)
    (hterm : ∀ z, IsTerminalBlock Gk Zf (⟨k, z⟩ : BlockV d L N₀ k) → z ∉ box b0 w)
    (H : BgHyp d L k ϱ a 0) (inp : PsiZeroInput (N := N) G a b0 w X) :
    ∃ K c11 : ℝ, 0 < K ∧ 0 < c11 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ c11 →
      ∀ ψ : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N),
        BlockTube (X \ box b0 w) δ (fun z i => ψ ⟨k, z⟩ i) →
        ∃ ψ0 : BlockV d L N₀ k → EuclideanSpace ℝ (Fin N), PsiZeroSpec Gk G Zf (K * δ) ψ ψ0 ∧
          ∀ z, z ∉ box b0 w → ψ0 ⟨k, z⟩ = ψ ⟨k, z⟩ := by
  have hΩ' : ∀ y y', y ∈ box b0 w ∪ shellOut (box b0 w) → y' ∈ box b0 w ∪ shellOut (box b0 w) →
      OverTop G {y, y'} := fun y y' hy hy' x hx => by
    rcases Set.mem_insert_iff.1 hx with h | h
    · exact hΩ x (h ▸ hy)
    · exact hΩ x (by rw [Set.mem_singleton_iff.1 h]; exact hy')
  have hΩ1 : ∀ y, y ∈ box b0 w ∪ shellOut (box b0 w) → OverTop G {y} := fun y hy x hx =>
    hΩ x (by rw [Set.mem_singleton_iff.1 hx]; exact hy)
  obtain ⟨K, c11, hK, hc11, hmain⟩ := psiZero_exists_unique_of_input G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H inp
  refine ⟨K + 1, c11, by linarith, hc11, fun δ hδ hδc ψ hψ => ?_⟩
  have hψ' : TubeOn G (X \ box b0 w) δ (fun z i => ψ ⟨k, z⟩ i) := tubeOn_of_blockTube G hδ hψ
  have h := hmain δ hδ hδc _ hψ'
  have hs1 := psiZeroOf_tube G a h
  set sol := psiZeroOf G a h with hsol
  have hoff : ∀ z, z ∉ box b0 w → sol z = ψ ⟨k, z⟩ := by
    intro z hz
    exact psiZeroOf_eq_off G a h hz
  have hKδ : K * δ ≤ (K + 1) * δ := by nlinarith
  have hδK : δ ≤ (K + 1) * δ := by nlinarith
  refine ⟨solveBlockV ψ sol, ⟨X, hZX, hdata, ⟨?_, ?_⟩, fun b hb => ?_⟩, fun z hz => ?_⟩
  · intro y hy y' hy' hadj
    beta_reduce
    rw [solveBlockV_k, solveBlockV_k]
    have hadj' : torusAdj y y' := hadj.2
    by_cases hyb : y ∈ box b0 w
    · have hy'sh : y' ∈ box b0 w ∪ shellOut (box b0 w) := by
        by_cases hy'b : y' ∈ box b0 w
        · exact Or.inl hy'b
        · exact Or.inr (mem_shellOut_of_adj hyb hy'b hadj')
      have := tube_R1 hs1 hk hy hy' hadj' (hΩ' y y' (Or.inl hyb) hy'sh)
      exact lt_of_lt_of_le this hKδ
    · by_cases hy'b : y' ∈ box b0 w
      · have hysh : y ∈ box b0 w ∪ shellOut (box b0 w) :=
          Or.inr (mem_shellOut_of_adj hy'b hyb ⟨(hadj'.choose), by
            rcases hadj'.choose_spec with h | h
            · exact Or.inr h
            · exact Or.inl h⟩)
        have := tube_R1 hs1 hk hy hy' hadj' (hΩ' y y' hysh (Or.inl hy'b))
        exact lt_of_lt_of_le this hKδ
      · have := hψ.1 y ⟨hy, hyb⟩ y' ⟨hy', hy'b⟩ hadj'
        have e1 := hoff y hyb
        have e2 := hoff y' hy'b
        change ‖eu (sol y) - eu (sol y')‖ < (K + 1) * δ
        rw [e1, e2]
        exact lt_of_lt_of_le this hδK
  · intro y hy
    beta_reduce
    rw [solveBlockV_k]
    by_cases hyb : y ∈ box b0 w
    · exact lt_of_lt_of_le (tube_R2 hs1 hy (hΩ1 y (Or.inl hyb)) hk) hKδ
    · have := abs_norm_sub_one_lt_of_sq (hψ.2 y ⟨hy, hyb⟩)
      change |‖eu (sol y)‖ - 1| < (K + 1) * δ
      rw [hoff y hyb]
      exact lt_of_lt_of_le this hδK
  · obtain ⟨i, u⟩ := b
    have hi : i = k := hb.1
    subst hi
    rw [solveBlockV_k]
    have hu : u ∉ box b0 w := hterm u hb
    ext j
    have := congrFun (hoff u hu) j
    simpa using this
  · rw [solveBlockV_k]
    ext j
    have := congrFun (hoff z hz) j
    simpa using this

end Spec

end Balaban.LargeField
