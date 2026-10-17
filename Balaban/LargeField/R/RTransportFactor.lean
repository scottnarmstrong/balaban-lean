/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RTransport
public import Balaban.LargeField.R.RopConcrete
public import Balaban.LargeField.R.RRemovedKernel
import Mathlib

/-!
# Factorization of the global `R` over separated components

`notes/phase1/LF4R-PLAN.md` §6.5 (P7 §3).  The operation `R` of the family `famDecomp` acts on the
global block field; `remDecomp` is the operation of one component on the outputs of its localized
history.  For `ρ = ∏_c ρ_c ∘ res_c` and components whose volumes `V_c` do not meet the boxes
`Z₀(c')` of the other components, `R[ρ] = ∏_c R_c[ρ_c] ∘ res_c` (Fubini for the product measure,
`integral_fintype_prod_eq_prod`, and the change of variables `measurePreserving_suppToOutPart`).

* `integral_comp_suppToOutPart`: the integral over `SuppSpace Zf N` of a function of its image in
  `OutPart` is the integral over `OutPart N V P` (the image map is a measurable equivalence);
* `RopProd_factor_famEquiv`: the factorization for any family of densities `rfam` that are the
  transports of the `r_c` (`hrfam`);
* `Rop_famDecomp_factor`: the same for the landed `famDecomp` (densities `famRho`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

section Equiv

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k N₀ : ℕ} [NeZero N₀]
  (hN : N₀ * S.L ^ (k - k) = M * n K * S.L ^ (K - k))

/-- The integral over the variables `SuppSpace Zf N` of `Z₀` of a function of their image in
`OutPart N V P` is the integral over `OutPart N V P` (`measurePreserving_suppToOutPart`; the image map
is a measurable equivalence). -/
theorem integral_comp_suppToOutPart (Zf : Finset (Torus S.d (N₀ * S.L ^ (k - k))))
    (V : Set (BlockAt S n M K k)) (P : BlockAt S n M K k → Prop)
    (hZ : ∀ y : BlockAt S n M K k, (y ∈ V ∧ P y) ↔ torusCast hN.symm y ∈ Zf)
    (g : OutPart N V P → ℝ) :
    ∫ u : SuppSpace Zf N, g (fun y : {y : BlockAt S n M K k // y ∈ V ∧ P y} =>
        (WithLp.toLp 2 (fun i => u (⟨torusCast hN.symm y.1, (hZ y.1).1 y.2⟩, i)) :
          EuclideanSpace ℝ (Fin N))) = ∫ wv, g wv ∂(outPartMeasure N V P) := by
  have hf := measurePreserving_suppToOutPart (S := S) (n := n) (M := M) (K := K) (N := N) (k := k)
    hN Zf V P hZ
  let inv : OutPart N V P → SuppSpace Zf N := fun wv =>
    WithLp.toLp 2 (fun p : ↥Zf × Fin N =>
      wv ⟨torusCast hN p.1.1, (hZ _).2 (by rw [torusCast_symm_cast]; exact p.1.2)⟩ p.2)
  have hinv : Measurable inv := by
    refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.mpr fun p => ?_)
    exact (EuclideanSpace.proj p.2).continuous.measurable.comp (measurable_pi_apply _)
  let e : SuppSpace Zf N ≃ᵐ OutPart N V P :=
    { toFun := fun u y => (WithLp.toLp 2 (fun i => u (⟨torusCast hN.symm y.1, (hZ y.1).1 y.2⟩, i)) :
        EuclideanSpace ℝ (Fin N))
      invFun := inv
      left_inv := fun u => by
        ext ⟨⟨z, hz⟩, i⟩
        have h : ∀ (z' : Torus S.d (N₀ * S.L ^ (k - k))) (hz' : z' = z) (hh : z' ∈ Zf),
            u (⟨z', hh⟩, i) = u (⟨z, hz⟩, i) := by
          rintro z' rfl hh; rfl
        exact h _ (torusCast_symm_cast hN z) _
      right_inv := fun wv => by
        funext y
        ext i
        have h : ∀ (z : BlockAt S n M K k) (hz : z = y.1) (hz' : z ∈ V ∧ P z),
            wv ⟨z, hz'⟩ = wv y := by
          rintro z rfl hz'; rfl
        exact congrArg (fun v => v i) (h _ (torusCast_cast_symm hN y.1) _)
      measurable_toFun := hf.measurable
      measurable_invFun := hinv }
  exact MeasurePreserving.integral_comp' (f := e) hf g

end Equiv

section Factor

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] (N : ℕ) {k N₀ : ℕ} [NeZero N₀] [NeZero N]
  (hN : N₀ * S.L ^ (k - k) = M * n K * S.L ^ (K - k)) {ι : Type} [Fintype ι]
  (a : ι → LocalHistory S n M K) (b0 : ι → Torus S.d (N₀ * S.L ^ (k - k))) (w : ι → Fin S.d → ℕ)
  (X : ι → Set (Torus S.d (N₀ * S.L ^ (k - k))))
  (hXreg : ∀ c, box (b0 c) (w c) ∪ shellOut (box (b0 c) (w c)) ⊆ X c)
  (hsep : ∀ c c', c ≠ c' → Disjoint (X c) (box (b0 c') (w c')))
  (σ : Finset ι) (Z0 : ι → Set (BlockAt S n M K k))
  (hZ0 : ∀ (c : ι) (y : BlockAt S n M K k), (y ∈ Vblk R (a c) k ∧ y ∈ Z0 c) ↔
    torusCast hN.symm y ∈ zb b0 w c)
  (hsepV : ∀ c c' : σ, c ≠ c' → ∀ y ∈ Vblk R (a c.1) k, torusCast hN.symm y ∉ zb b0 w c'.1)

set_option hygiene false in
/-- The restriction of a block field to the blocks of `V_c`. -/
local notation "rs[" c "," ψ "]" =>
  (fun ybk : Vblk R (a c) k =>
    (WithLp.toLp 2 (fun ii => ψ (torusCast hN.symm ybk.1) ii) : EuclideanSpace ℝ (Fin N)))

set_option hygiene false in
/-- The variable of `Z₀(c)` carrying the image of `u ∈ SuppSpace (zb c)` in `OutZero`. -/
local notation "fo[" c "," u "]" =>
  (fun ybk : {y : BlockAt S n M K k // y ∈ Vblk R (a c) k ∧ y ∈ Z0 c} =>
    (WithLp.toLp 2 (fun ii => u (⟨torusCast hN.symm ybk.1, (hZ0 c ybk.1).1 ybk.2⟩, ii)) :
      EuclideanSpace ℝ (Fin N)))

include hZ0 hsepV in
/-- The outside variables of component `c` read off the field with the outside data `y` of the
family agree with those read off any field `ψ` with `(famEquiv ψ).2 = y`. -/
theorem restrict_famOut_eq (c : σ) (ψ : BlockField S.d S.L N₀ k N) :
    restrictOutPart rs[c.1, famOut N b0 w X hXreg hsep σ (famEquiv N b0 w X hXreg hsep σ ψ).2]
        (· ∉ Z0 c.1) =
      restrictOutPart rs[c.1, ψ] (· ∉ Z0 c.1) := by
  funext yb
  ext i
  have hz : ∀ c' : σ, torusCast hN.symm yb.1 ∉ zb b0 w c'.1 := by
    intro c' hc'
    by_cases hc : c' = c
    · subst hc
      exact yb.2.2 ((hZ0 c'.1 yb.1).2 hc').2
    · exact hsepV c c' (Ne.symm hc) yb.1 yb.2.1 hc'
  exact congrArg (fun v => v i) (famOut_eq N b0 w X hXreg hsep σ ψ _ hz)

include hsepV in
/-- The restriction to `V_c` of the field of the family with the variables `x` on the boxes and the
outside data `y` is the merge of the image of `x c` and the outside variables read off
`famOut y`. -/
theorem res_famEquiv_symm (c : σ) (x : (c : σ) → SuppSpace (zb b0 w c.1) N)
    (y : ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ) :
    rs[c.1, (famEquiv N b0 w X hXreg hsep σ).symm (x, y)] =
      remZeroMerge (a c.1) k (Z0 c.1)
        (fo[c.1, x c], restrictOutPart rs[c.1, famOut N b0 w X hXreg hsep σ y] (· ∉ Z0 c.1)) := by
  classical
  set Ψ := (famEquiv N b0 w X hXreg hsep σ).symm (x, y) with hΨ
  have hE : famEquiv N b0 w X hXreg hsep σ Ψ = (x, y) :=
    (famEquiv N b0 w X hXreg hsep σ).apply_symm_apply (x, y)
  have P1 : ∀ (c' : σ) (z : Torus S.d (N₀ * S.L ^ (k - k))) (hz : z ∈ zb b0 w c'.1) (i : Fin N),
      Ψ z i = x c' (⟨z, hz⟩, i) := by
    intro c' z hz i
    have h1 := famEquiv_fst N b0 w X hXreg hsep σ Ψ c'
    rw [hE] at h1
    exact (congrArg (fun v => v (⟨z, hz⟩, i)) h1).symm
  have P2 : ∀ (z : Torus S.d (N₀ * S.L ^ (k - k))) (hz : ∀ c' : σ, z ∉ zb b0 w c'.1) (i : Fin N),
      Ψ z i = famOut N b0 w X hXreg hsep σ y z i := by
    intro z hz i
    have h1 := famEquiv_snd N b0 w X hXreg hsep σ Ψ ⟨⟨z, i⟩, hz⟩
    rw [hE] at h1
    rw [← h1]
    exact (famOut_apply N b0 w X hXreg hsep σ y ⟨⟨z, i⟩, hz⟩).symm
  funext yb
  by_cases hZ : yb.1 ∈ Z0 c.1
  · have hzc : torusCast hN.symm yb.1 ∈ zb b0 w c.1 := (hZ0 c.1 yb.1).1 ⟨yb.2, hZ⟩
    ext i
    simp only [remZeroMerge, hZ, ↓reduceDIte]
    exact P1 c _ hzc i
  · have hz : ∀ c' : σ, torusCast hN.symm yb.1 ∉ zb b0 w c'.1 := by
      intro c' hc'
      by_cases hc : c' = c
      · subst hc
        exact hZ ((hZ0 c'.1 yb.1).2 hc').2
      · exact hsepV c c' (Ne.symm hc) yb.1 yb.2 hc'
    ext i
    simp only [remZeroMerge, hZ, ↓reduceDIte, restrictOutPart]
    exact P2 _ hz i

include hZ0 hsepV in
/-- **Factorization of `R` over separated components** (P7 §3, `LF4R-PLAN` §6.5), in the product
form: if `ρ = ∏_c ρ_c ∘ res_c` and the densities `rfam c` are the transports of the densities `r_c`
of the one-component decompositions (`hrfam`), then at every block field `ψ`,
`R[ρ](ψ) = ∏_c R_c[ρ_c](res_c ψ)`.  The separation `hsepV` is `V_c ∩ Z₀(c') = ∅` for `c ≠ c'`
(as sets of blocks of the level-`k` torus). -/
theorem RopProd_factor_famEquiv
    (r : ∀ c : ι, OutZero N R (a c) k (Z0 c) → OutRest N R (a c) k (Z0 c) → ℝ)
    (ρc : ∀ c : ι, OutT N R (a c) k → ℝ) (ρ : BlockField S.d S.L N₀ k N → ℝ)
    (hρ : ∀ ψ, ρ ψ = ∏ c : σ, ρc c.1 rs[c.1, ψ])
    (rfam : ∀ c : σ, SuppSpace (zb b0 w c.1) N →
      (ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ) → ℝ)
    (hrfam : ∀ (c : σ) (y : ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ)
      (u : SuppSpace (zb b0 w c.1) N),
      rfam c u y = r c.1 fo[c.1, u]
        (restrictOutPart rs[c.1, famOut N b0 w X hXreg hsep σ y] (· ∉ Z0 c.1)))
    (ψ : BlockField S.d S.L N₀ k N) :
    RopProd (fun c : σ => (volume : Measure (SuppSpace (zb b0 w c.1) N))) rfam
        (fun p => ρ ((famEquiv N b0 w X hXreg hsep σ).symm p)) (famEquiv N b0 w X hXreg hsep σ ψ) =
      ∏ c : σ, Rop (remDecomp (a c.1) k (Z0 c.1) (r c.1)) (ρc c.1) rs[c.1, ψ] := by
  classical
  set y := (famEquiv N b0 w X hXreg hsep σ ψ).2 with hy
  have hyc : ∀ c : σ, restrictOutPart rs[c.1, famOut N b0 w X hXreg hsep σ y] (· ∉ Z0 c.1) =
      (remZeroSplit (a c.1) k (Z0 c.1) rs[c.1, ψ]).2 := fun c =>
    restrict_famOut_eq N hN a b0 w X hXreg hsep σ Z0 hZ0 hsepV c ψ
  have hden : ∀ c : σ, ∫ u, rfam c u y = remDen (a c.1) k (Z0 c.1) (r c.1) rs[c.1, ψ] := by
    intro c
    simp only [hrfam, hyc]
    exact integral_comp_suppToOutPart hN _ (Vblk R (a c.1) k) (· ∈ Z0 c.1) (hZ0 c.1)
      (fun wv => r c.1 wv (remZeroSplit (a c.1) k (Z0 c.1) rs[c.1, ψ]).2)
  have hnum : ∫ x, ρ ((famEquiv N b0 w X hXreg hsep σ).symm (x, y))
        ∂(Measure.pi fun c : σ => (volume : Measure (SuppSpace (zb b0 w c.1) N))) =
      ∏ c : σ, ∫ wv, ρc c.1 (remZeroMerge (a c.1) k (Z0 c.1)
        (wv, (remZeroSplit (a c.1) k (Z0 c.1) rs[c.1, ψ]).2))
          ∂(outPartMeasure N (Vblk R (a c.1) k) (· ∈ Z0 c.1)) := by
    have h1 : ∀ x : (c : σ) → SuppSpace (zb b0 w c.1) N,
        ρ ((famEquiv N b0 w X hXreg hsep σ).symm (x, y)) =
          ∏ c : σ, ρc c.1 (remZeroMerge (a c.1) k (Z0 c.1)
            (fo[c.1, x c], (remZeroSplit (a c.1) k (Z0 c.1) rs[c.1, ψ]).2)) := by
      intro x
      rw [hρ]
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [res_famEquiv_symm N hN a b0 w X hXreg hsep σ Z0 hZ0 hsepV c x y, hyc]
    simp_rw [h1]
    rw [integral_fintype_prod_eq_prod (f := fun (c : σ) (u : SuppSpace (zb b0 w c.1) N) =>
      ρc c.1 (remZeroMerge (a c.1) k (Z0 c.1)
        (fo[c.1, u], (remZeroSplit (a c.1) k (Z0 c.1) rs[c.1, ψ]).2)))]
    refine Finset.prod_congr rfl fun c _ => ?_
    exact integral_comp_suppToOutPart hN _ (Vblk R (a c.1) k) (· ∈ Z0 c.1) (hZ0 c.1)
      (fun wv => ρc c.1 (remZeroMerge (a c.1) k (Z0 c.1)
        (wv, (remZeroSplit (a c.1) k (Z0 c.1) rs[c.1, ψ]).2)))
  have hfst : ∀ c : σ, rfam c ((famEquiv N b0 w X hXreg hsep σ ψ).1 c) y =
      r c.1 (remZeroSplit (a c.1) k (Z0 c.1) rs[c.1, ψ]).1
        (remZeroSplit (a c.1) k (Z0 c.1) rs[c.1, ψ]).2 := by
    intro c
    rw [hrfam, hyc]
    rfl
  unfold RopProd
  simp only [Rop_remDecomp_apply]
  rw [Finset.prod_congr rfl fun c _ => hfst c, hnum, Finset.prod_congr rfl fun c _ => hden c,
    Finset.prod_mul_distrib, Finset.prod_div_distrib]

section FamDecomp

variable {ϱ : ℝ} (G : ι → GeneratingSet S.d S.L N₀ k ϱ) (aw : ℕ → ℝ) {D : ℕ} (hd : 2 ≤ S.d)
  (hk : 1 ≤ k) (hw1 : ∀ c i, 1 ≤ w c i) (hwD : ∀ c i, w c i ≤ D)
  (hm : D + 2 ≤ N₀ * S.L ^ (k - k))
  (hΩ : ∀ c, OverTop (G c) (box (b0 c) (w c) ∪ shellOut (box (b0 c) (w c))))
  (hdata : ∀ c, ∀ x ∈ dataSites (G c), jBlock S.d S.L N₀ k k x ∈ X c)
  (H : BgHyp S.d S.L k ϱ aw 0) (δ : ι → ℝ) (hδ : ∀ c, 0 < δ c)
  (hδc : ∀ c, δ c ≤ psiZeroC11 N (G c) aw hd hk (b0 c) (w c) (hw1 c) (hwD c) hm (hXreg c) (hΩ c)
    (hdata c) H)

include hZ0 hsepV in
/-- **Factorization of the landed `R` (`famDecomp`) over separated components** (P7 §3,
`LF4R-PLAN` §6.5): for `ρ = ∏_c ρ_c ∘ res_c`, components with `V_c ∩ Z₀(c') = ∅` for `c ≠ c'`, and
one-component densities `r_c` that transport the densities `famRho` of the family (`hrfam`),
`R[ρ](ψ) = ∏_c R_c[ρ_c](res_c ψ)` at every block field `ψ`.  Here `R` is
`Rop (famDecomp …)` and `R_c` is `Rop (remDecomp (a c) k (Z₀ c) (r c))`. -/
theorem Rop_famDecomp_factor (β p0 : ℝ)
    (r : ∀ c : ι, OutZero N R (a c) k (Z0 c) → OutRest N R (a c) k (Z0 c) → ℝ)
    (ρc : ∀ c : ι, OutT N R (a c) k → ℝ) (ρ : BlockField S.d S.L N₀ k N → ℝ)
    (hρ : ∀ ψ, ρ ψ = ∏ c : σ, ρc c.1 rs[c.1, ψ])
    (hrfam : ∀ (c : σ) (y : ZeroOutIdx (fun c : σ => zb b0 w c.1) N → ℝ)
      (u : SuppSpace (zb b0 w c.1) N),
      famRho N G aw hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c.1 y u =
        r c.1 fo[c.1, u]
          (restrictOutPart rs[c.1, famOut N b0 w X hXreg hsep σ y] (· ∉ Z0 c.1)))
    (ψ : BlockField S.d S.L N₀ k N) :
    Rop (famDecomp N G aw hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0) ρ ψ =
      ∏ c : σ, Rop (remDecomp (a c.1) k (Z0 c.1) (r c.1)) (ρc c.1) rs[c.1, ψ] :=
  RopProd_factor_famEquiv N hN a b0 w X hXreg hsep σ Z0 hZ0 hsepV r ρc ρ hρ
    (fun c u y => famRho N G aw hd hk b0 w hw1 hwD hm X hXreg hsep hΩ hdata H δ hδ hδc σ β p0 c.1 y u)
    hrfam ψ

end FamDecomp

end Factor

end Balaban.LargeField
