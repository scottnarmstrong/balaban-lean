/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedKernel
public import Balaban.LargeField.R.RopConcreteLocal
public import Balaban.LargeField.R.ChiBridgeHist
public import Balaban.LargeField.Operators.PiTools
import Mathlib

/-!
# Transport between the global block fields and the outputs of a localized history

The landed operation `R` (`famDecomp`) acts on `BlockField d L N₀ k N`, the fields on all
`k`-blocks of the level-`k` torus; the operators and the removed kernel act on
`OutT N R a k`, the fields on the `k`-blocks of `V = (Z^≈)^∼` of a localized history `a`.  The two
block tori are `Torus d (N₀ L^(k-k))` and `Torus d (M n_K L^(K-k))`; they are identified by
`torusCast hN` along `hN : N₀ L^(k-k) = M n_K L^(K-k)`.

The restriction of a block field `ψ` is the term
`fun y : Vblk R a k => WithLp.toLp 2 (fun i => ψ (torusCast hN.symm y.1) i)`; it is not measure
preserving onto `outMeasure` (the Lebesgue measure of the block field is the product over all
blocks, including those off `V`).  What is true, and what `R` uses (it integrates only over the
blocks of `Z₀`, the others are parameters), is proved here:

* `res_ext`, `ext_res`: restriction and extension (zero off `V`) are mutually inverse on `V`;
* `tubeOn_iff_of_res`: the tube condition `TubeOn G X δ ψ` reads `ψ` only on `X`, so for `X` in the
  image of `V` it is a condition on the output `o = res ψ`;
* `measurePreserving_suppReindex`, `measurePreserving_suppToOutPart`: the variables of `Z₀`,
  `SuppSpace Zf N`, are identified with `OutPart N V P` measure preservingly;
* `res_mergeField`: the restriction of the field merged with `u` on `Z₀` is `remZeroMerge` of the
  image of `u` and the restriction of `ψ` to `V ∖ Z₀`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

theorem measurePreserving_suppReindex {ι κ : Type} [Fintype ι] [Fintype κ] (N : ℕ) (e : κ ≃ ι) :
    MeasurePreserving (fun (u : EuclideanSpace ℝ (ι × Fin N)) (y : κ) =>
      (WithLp.toLp 2 (fun i => u (e y, i)) : EuclideanSpace ℝ (Fin N)))
      volume (Measure.pi fun _ : κ => (volume : Measure (EuclideanSpace ℝ (Fin N)))) := by
  have h0 : MeasurePreserving (fun u : EuclideanSpace ℝ (ι × Fin N) => (u : ι × Fin N → ℝ))
      volume volume := PiLp.volume_preserving_ofLp _
  have h1 := PiTools.measurePreserving_reindex (Equiv.sigmaEquivProd ι (Fin N))
    (fun _ : ι × Fin N => (volume : Measure ℝ)) (fun _ : (Σ _ : ι, Fin N) => (volume : Measure ℝ))
    (fun _ v => v) (fun _ => MeasurePreserving.id _)
  have h2 := PiTools.measurePreserving_piCurry (fun (_ : ι) (_ : Fin N) => ℝ)
    (fun _ _ => (volume : Measure ℝ))
  have h3 := PiTools.measurePreserving_reindex e
    (fun _ : ι => (volume : Measure (Fin N → ℝ)))
    (fun _ : κ => (volume : Measure (EuclideanSpace ℝ (Fin N))))
    (fun _ v => (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin N)))
    (fun _ => PiLp.volume_preserving_toLp _)
  exact h3.comp ((h2.comp h1).comp h0)

section Transport

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k N₀ : ℕ} [NeZero N₀] (a : LocalHistory S n M K)
  (hN : N₀ * S.L ^ (k - k) = M * n K * S.L ^ (K - k))

/-- Restriction then extension: if the block field `ψ` is the extension (zero off `V`) of the
output `o`, then the restriction of `ψ` is `o`. -/
theorem res_ext (o : OutT N R a k) (ψ : BlockField S.d S.L N₀ k N)
    (hψ : ∀ z i, ψ z i = outField N o (torusCast hN z) i) :
    (fun y : Vblk R a k =>
      (WithLp.toLp 2 (fun i => ψ (torusCast hN.symm y.1) i) : EuclideanSpace ℝ (Fin N))) = o := by
  funext y
  ext i
  simp only [hψ, torusCast_cast_symm]
  simp [outField, y.2]

/-- Extension after restriction: on the blocks of `V` the extension of the restriction of `ψ`
is `ψ`. -/
theorem ext_res (o : OutT N R a k) (ψ : BlockField S.d S.L N₀ k N)
    (ho : o = fun y : Vblk R a k =>
      (WithLp.toLp 2 (fun i => ψ (torusCast hN.symm y.1) i) : EuclideanSpace ℝ (Fin N)))
    {z : Torus S.d (N₀ * S.L ^ (k - k))} (hz : torusCast hN z ∈ Vblk R a k) (i : Fin N) :
    outField N o (torusCast hN z) i = ψ z i := by
  subst ho
  simp [outField, hz, torusCast_symm_cast]

/-- **The tube condition on the outputs**: `TubeOn G X δ ψ` reads `ψ` only on `X`; if `X` lies in
the image of `V` and `ψ'` is the extension of the restriction `o = res ψ`, then
`TubeOn G X δ ψ ↔ TubeOn G X δ ψ'`. -/
theorem tubeOn_iff_of_res {ϱ : ℝ} (G : GeneratingSet S.d S.L N₀ k ϱ)
    (X : Set (Torus S.d (N₀ * S.L ^ (k - k)))) (δ : ℝ) (hXV : ∀ z ∈ X, torusCast hN z ∈ Vblk R a k)
    (ψ ψ' : BlockField S.d S.L N₀ k N) (o : OutT N R a k)
    (ho : o = fun y : Vblk R a k =>
      (WithLp.toLp 2 (fun i => ψ (torusCast hN.symm y.1) i) : EuclideanSpace ℝ (Fin N)))
    (hψ' : ∀ z i, ψ' z i = outField N o (torusCast hN z) i) :
    TubeOn G X δ ψ ↔ TubeOn G X δ ψ' := by
  refine tubeOn_congr G (fun z hz => ?_)
  funext i
  rw [hψ', ext_res a hN o ψ ho (hXV z hz) i]

/-- **The variables of `Z₀` as outputs, measure preserving.**  If the blocks of `V` satisfying `P`
are exactly the blocks mapped into the finite set `Zf` of blocks of the level-`k` torus, the map
`u ↦ (y ↦ (u (cast y, i))_i)` from `SuppSpace Zf N` (Lebesgue measure) to `OutPart N V P` takes
Lebesgue measure to `outPartMeasure`. -/
theorem measurePreserving_suppToOutPart (Zf : Finset (Torus S.d (N₀ * S.L ^ (k - k))))
    (V : Set (BlockAt S n M K k)) (P : BlockAt S n M K k → Prop)
    (hZ : ∀ y : BlockAt S n M K k, (y ∈ V ∧ P y) ↔ torusCast hN.symm y ∈ Zf) :
    MeasurePreserving (fun (u : SuppSpace Zf N) (y : {y : BlockAt S n M K k // y ∈ V ∧ P y}) =>
      (WithLp.toLp 2 (fun i => u (⟨torusCast hN.symm y.1, (hZ y.1).1 y.2⟩, i)) :
        EuclideanSpace ℝ (Fin N)))
      volume (outPartMeasure N V P) := by
  let e : {y : BlockAt S n M K k // y ∈ V ∧ P y} ≃ ↥Zf :=
    { toFun := fun y => ⟨torusCast hN.symm y.1, (hZ y.1).1 y.2⟩
      invFun := fun z => ⟨torusCast hN z.1, by
        refine (hZ _).2 ?_
        rw [torusCast_symm_cast]; exact z.2⟩
      left_inv := fun y => Subtype.ext (torusCast_cast_symm hN y.1)
      right_inv := fun z => Subtype.ext (torusCast_symm_cast hN z.1) }
  exact measurePreserving_suppReindex N e

/-- **The restriction of a merged field**: with `Zf` the image of the blocks of `V` in `Z0`,
the restriction of `mergeField Zf ψ u` is `remZeroMerge` of the image of `u` in `OutZero` and the
restriction of `ψ` to `V ∖ Z₀`. -/
theorem res_mergeField (Z0 : Set (BlockAt S n M K k)) (Zf : Finset (Torus S.d (N₀ * S.L ^ (k - k))))
    (hZ : ∀ y : BlockAt S n M K k, (y ∈ Vblk R a k ∧ y ∈ Z0) ↔ torusCast hN.symm y ∈ Zf)
    (ψ : BlockField S.d S.L N₀ k N) (u : SuppSpace Zf N) :
    (fun y : Vblk R a k =>
      (WithLp.toLp 2 (fun i => mergeField Zf ψ u (torusCast hN.symm y.1) i) :
        EuclideanSpace ℝ (Fin N))) =
      remZeroMerge a k Z0
        ((fun y : {y : BlockAt S n M K k // y ∈ Vblk R a k ∧ y ∈ Z0} =>
          (WithLp.toLp 2 (fun i => u (⟨torusCast hN.symm y.1, (hZ y.1).1 y.2⟩, i)) :
            EuclideanSpace ℝ (Fin N))),
         restrictOutPart (fun y : Vblk R a k =>
          (WithLp.toLp 2 (fun i => ψ (torusCast hN.symm y.1) i) : EuclideanSpace ℝ (Fin N)))
          (· ∉ Z0)) := by
  classical
  funext y
  by_cases h : y.1 ∈ Z0
  · have hm : torusCast hN.symm y.1 ∈ Zf := (hZ y.1).1 ⟨y.2, h⟩
    ext i
    simp [remZeroMerge, h, mergeField, hm]
  · have hm : torusCast hN.symm y.1 ∉ Zf := fun hh => h ((hZ y.1).2 hh).2
    ext i
    simp [remZeroMerge, h, mergeField, hm, restrictOutPart]

end Transport

end Balaban.LargeField
