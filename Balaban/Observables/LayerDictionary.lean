/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerDef

/-!
# Lemma 2.2: the dictionary with the first-order class (H.7) (OBSERVABLES.md §2.3)

The vectors `𝓜^{(j)}(x; ψ_j, h) = β_{j-1}^{-1/2} (M^{(j)}(x; ψ_j, h) - μ_j(x) φ_j(x; ψ_j, h))`
(`Mscript`), with `φ_j(x; ψ_k^{(j)}, h)` the level-`j` background of the composed datum
(`phiLevel`), and the identity

  `M_k = φ_k + ∑_{j ≤ k} 𝓜^{(j)}(ψ_k^{(j)}, h)`  (`Mk_eq_dictionary`),

which uses the composition identity of the backgrounds `φ_j(ψ_k^{(j)}) = φ_k` (BACKGROUND §6,
Theorem 7.3) as the hypothesis `hcomp`.  Consequently the identification (2.4) holds iff the
first-order part of (H.7), `φ_k + ∑_j ℳ^{(j)}(ψ_k^{(j)}, h, 0)` (with `Mloc` of Def-6), equals
`φ_k + ∑_j 𝓜^{(j)}` (`first_order_iff`).
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
open Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **`φ_j(x; ψ_k^{(j)}, h)`**: the background field of level `j` of the composed datum
(`0` for `j > k`). -/
noncomputable def phiLevel (a : ℕ → ℝ) (ν : ℝ) (j : ℕ) (D : BgData (topGS d L N₁ m₁ k ϱ) N)
    (x : CTorus d L N₁ m₁ k) (i : Fin N) : ℂ :=
  if hj : j ≤ k then
    svec (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hj)
      (bgField (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hj) a ν
        (composedData (ϱ := ϱ) (m₁ := m₁) a ν hj D)) x i
  else 0

/-- **`𝓜^{(j)}(x; ψ_k^{(j)}, h) = β_{j-1}^{-1/2} (M^{(j)}(x; ψ_k^{(j)}, h) - μ_j(x) φ_j(x))`**
(Lemma 2.2). -/
noncomputable def Mscript (P : Consts) (β ν a : ℕ → ℝ) (Ot : ObsTerms d L N₁ m₁ k N)
    (D : BgData (topGS d L N₁ m₁ k ϱ) N) (j : ℕ) (x : CTorus d L N₁ m₁ k) : Fin N → ℂ :=
  fun i => ((Real.sqrt (β (j - 1)))⁻¹ : ℂ) *
    (Mobs P.m₀ Ot j x (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
        (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2 i -
      (Ot.μ j x : ℂ) * phiLevel (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D x i)

/-- **Lemma 2.2, the dictionary**: with the composition identity `φ_j(ψ_k^{(j)}) = φ_k`
(`hcomp`, BACKGROUND Theorem 7.3), `M_k = φ_k + ∑_{j ≤ k} 𝓜^{(j)}(ψ_k^{(j)}, h)`. -/
theorem Mk_eq_dictionary (P : Consts) (β ν a : ℕ → ℝ) (Ot : ObsTerms d L N₁ m₁ k N)
    (D : BgData (topGS d L N₁ m₁ k ϱ) N)
    (hcomp : ∀ j, 1 ≤ j → j ≤ k → ∀ (x : CTorus d L N₁ m₁ k) (i : Fin N),
      phiLevel (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D x i =
        svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
          (bgMass L k (β k) (ν k)) D) x i)
    (x : CTorus d L N₁ m₁ k) (i : Fin N) :
    Mk P β ν a Ot D x i =
      svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
        (bgMass L k (β k) (ν k)) D) x i + ∑ j ∈ Finset.Icc 1 k, Mscript P β ν a Ot D j x i := by
  set φk := svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
    (bgMass L k (β k) (ν k)) D) x i with hφk
  have h1 : ∀ j ∈ Finset.Icc 1 k, Mscript P β ν a Ot D j x i =
      ((Real.sqrt (β (j - 1)))⁻¹ : ℂ) *
        Mobs P.m₀ Ot j x (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
          (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2 i -
      ((Real.sqrt (β (j - 1)))⁻¹ : ℂ) * (Ot.μ j x : ℂ) * φk := by
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    simp only [Mscript]
    rw [hcomp j hj'.1 hj'.2 x i]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [Mk, mFactor]
  push_cast
  rw [sub_mul, one_mul]
  ring

/-- **Lemma 2.2, the equivalence**: (2.4) holds, i.e. `M_k` of the layer equals the first-order
part `φ_k + ∑_j ℳ^{(j)}(ψ_k^{(j)}, h, 0)` of (H.7) (`Mloc` of Def-6), iff
`∑_j 𝓜^{(j)} = ∑_j ℳ^{(j)}(·, 0)` (given the composition identity). -/
theorem first_order_iff (P : Consts) (β ν a : ℕ → ℝ) (Tm : Terms d L N₁ m₁ k N ϱ)
    (Ot : ObsTerms d L N₁ m₁ k N) (D : BgData (topGS d L N₁ m₁ k ϱ) N)
    (hcomp : ∀ j, 1 ≤ j → j ≤ k → ∀ (x : CTorus d L N₁ m₁ k) (i : Fin N),
      phiLevel (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D x i =
        svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
          (bgMass L k (β k) (ν k)) D) x i)
    (x : CTorus d L N₁ m₁ k) (i : Fin N) :
    Mk P β ν a Ot D x i =
        svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
          (bgMass L k (β k) (ν k)) D) x i +
          ∑ j ∈ Finset.Icc 1 k, Mloc P.m₀ Tm j x
            (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
            (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2 0 i ↔
      ∑ j ∈ Finset.Icc 1 k, Mscript P β ν a Ot D j x i =
        ∑ j ∈ Finset.Icc 1 k, Mloc P.m₀ Tm j x
          (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
          (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2 0 i := by
  rw [Mk_eq_dictionary P β ν a Ot D hcomp x i]
  exact add_right_inj _

end Balaban.Observables
