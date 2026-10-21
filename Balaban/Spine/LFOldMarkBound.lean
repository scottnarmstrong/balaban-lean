/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldH7Loc

/-!
# The bound of the interpolated old term of the local pair (P6 (4.34), one parameter)

At every parameter `s` of the polydisc, the interpolated old term of the local pair (reading HS-1′)
is the record's term `ℬ^{(k)}(X, 𝔸)` at the composed multiscale field of the local composite; by
OPEN-H7-MIXED for the local pair (`h7Domain_composedMulti_loc`, from the named input
`H7MixedInnerLoc`) that field lies in the source H7 domain at `X`, where the record's (D7) bound
applies:

* `truncK`, `extK_truncK_apply`, `extK_truncK_composedMulti`: a multiscale field of scale `≤ K` as a
  field at the scales `≤ K`, and the composed multiscale field is the extension of its truncation;
* `norm_oldInterp_loc_lt`: **`|F_X(s)| < fac · e^{-rate · d^cov(X)}`** for the record's constant and
  rate (`D7BdryPost.bound`), at every parameter `|s_P| < R` and every fluctuation field `|ψ̂| < r_ψ`,
  for a target field of the H7 domain of scale `k + 1` at a set containing `X` and the data sites of
  the local pair.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background

namespace Balaban.RootFSpine

section Trunc

variable {S : Setting} {n : ℕ → ℕ} {M K N : ℕ}

/-- **A multiscale field as a field at the scales `≤ K`.** -/
def truncK (ψ : MultiFieldC S n M K N) : FinFieldC S n M K N := fun j y => ψ j y

theorem extK_truncK_apply (ψ : MultiFieldC S n M K N) {j : ℕ} (hj : j ≤ K)
    (y : Torus S.d (M * n K * S.L ^ (K - j))) : extK (truncK ψ) j y = ψ j y := by
  simp [extK, truncK, hj]

/-- The truncation of an extension is the field. -/
theorem truncK_extK (ψ : FinFieldC S n M K N) : truncK (extK ψ) = ψ := by
  funext j y
  simp [extK, truncK, Nat.lt_succ_iff.1 j.2]

end Trunc

section Bound

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

omit [NeZero M] in
/-- **The composed multiscale field is the extension of its truncation** (it vanishes above the
scale `k < K`). -/
theorem extK_truncK_composedMulti {k : ℕ} (hk : k + 1 ≤ K) {ϱ' : ℝ}
    (G' : GeneratingSet S.d S.L ((g.c * n (k + 1)) * S.L ^ m₁) (k + 1) ϱ')
    (ψ : MultiFieldC S n M K N) (comp : unitPts G' → Fin N → ℂ) :
    extK (truncK (composedMulti g hnn hM1 hk G' ψ comp)) = composedMulti g hnn hM1 hk G' ψ comp := by
  funext j y
  by_cases hj : j ≤ K
  · exact extK_truncK_apply _ hj y
  · simp only [extK, hj, ↓reduceDIte]
    exact (composedMulti_of_gt hk G' ψ comp (by omega) y).symm

/-- **The bound of the interpolated old term of a local step at one parameter, from the source H7
domain** (the core of `norm_oldInterp_loc_lt` for the readings `glob` of the datum): if the composed
multiscale field of the local step `holeStepLocAt glob … V` at the parameter `s` and the fluctuation
field `ψ̂` lies in the H7 domain of scale `k` at the old label `X`, the interpolated old term is below
the record's `fac · e^{-rate · d^cov(X)}` (`D7BdryPost.bound`). -/
theorem norm_oldInterp_locAt_lt (glob : Bool) {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ}
    (hk : k + 1 ≤ K)
    {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {rep : Rep S n R k0 K M N geo cs P k}
    {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))} {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
    {hv : EuclideanSpace ℝ (Fin N)}
    (hrec : D7BdryPost Fr hnn (Nat.le_of_succ_le hk) rep Zof aw μs ε ε1 νs fac rate hv)
    (hgeo : geo = g)
    {A : LabHist S n R k0 K} (hA : A ∈ rep.hist) {X : Finset (Torus S.d (n k))}
    (hX : X ∈ bdryDomsPost Fr A k (Zof A)) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ ρc : ℝ) (ρ r : ℕ)
    (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) {ψ : MultiFieldC S n M K N}
    {q' : FinFieldC S n M K N} {gx : GIdx S n M K N → ℂ}
    {ψhat : (holeStepLocAt g hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).U → Fin N → ℂ}
    {s : Dec2.DecParams (coverOf (holeStepLocAt g hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
      V).G')}
    (hdom : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) k (Nat.le_of_succ_le hk)
      (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs (hC hv)
      (composedMulti g hnn hM1 hk (holeStepLocAt g hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ
          V).G' ψ
        ((holeStepLocAt g hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).composed
          (coverOf (holeStepLocAt g hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G') ρc
          ((holeStepLocAt g hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).slocOf
            (coverOf (holeStepLocAt g hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')
            (locDomsLF g hM1 (holeStepLocAt g hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V) ρ)
            (HoleStep.coreExt
              (coverOf (holeStepLocAt g hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')
              (collarCoreC (c := g.c) (A.H.step k) hM1 r X) s)) ψhat))
      (extK q') (fun x i => gx (x, i))) :
    ‖(holeStepLocAt g hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).oldInterp
        (coverOf (holeStepLocAt g hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G') ρc
        (locDomsLF g hM1 (holeStepLocAt g hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V) ρ)
        (collarCoreC (c := g.c) (A.H.step k) hM1 r X) ∅ ψhat
        (oldTermLF g hnn hM1 rep A X hk
          (holeStepLocAt g hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' ψ (extK q') hv gx)
        (fun b => absurd b.2 (Finset.notMem_empty _)) s‖ <
      fac * Real.exp (-rate * d7Size Fr A k X) := by
  subst hgeo
  have hfill : (holeStepLocAt geo hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).fill ∅
      (fun b => absurd b.2 (Finset.notMem_empty _)) ψhat = ψhat := by
    funext b i
    simp [HoleStep.fill]
  unfold HoleStep.oldInterp oldTermLF
  rw [hfill]
  have hb := hrec.bound A hA X hX (hC hv) rfl
    (truncK (composedMulti geo hnn hM1 hk
      (holeStepLocAt geo hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G'
      ψ ((holeStepLocAt geo hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).composed
        (coverOf (holeStepLocAt geo hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G') ρc
        ((holeStepLocAt geo hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).slocOf
          (coverOf (holeStepLocAt geo hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')
          (locDomsLF geo hM1 (holeStepLocAt geo hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V) ρ)
          (HoleStep.coreExt
            (coverOf (holeStepLocAt geo hnn hM1 glob A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')
            (collarCoreC (c := geo.c) (A.H.step k) hM1 r X) s)) ψhat)), q', gx)
    (by
      simp only
      rw [extK_truncK_composedMulti]
      exact hdom)
  simp only at hb
  rwa [extK_truncK_composedMulti] at hb

/-- **The bound of the interpolated old term of the local pair at one parameter** (P6 (4.34) before
the Cauchy estimate): for an old label `X` of the record (a boundary domain of the post-`R` class of
the history `A`, with (D7) `hrec`), a target field `(ψ, ψ', g)` of the H7 domain of scale `k + 1`
(at the physical field `h`) at a set `Y_f` containing `X` and the data sites of the local pair, a
fluctuation field `|ψ̂| < r_ψ` and a parameter `|s_P| < R`, the interpolated old term of the local
pair is bounded by the record's `fac · e^{-rate · d^cov(X)}`; conditional on the named input
`H7MixedInnerLoc` (OPEN-H7-MIXED, the remaining part). -/
theorem norm_oldInterp_loc_lt {m₀ : ℕ} {Fr : FineSizeFrame S n M K m₀ m₁} {k : ℕ} (hk : k + 1 ≤ K)
    {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {rep : Rep S n R k0 K M N geo cs P k}
    {Zof : LabHist S n R k0 K → Set (Torus S.d (n k))} {aw μs ε ε1 νs : ℕ → ℝ} {fac rate : ℝ}
    {hv : EuclideanSpace ℝ (Fin N)}
    (hrec : D7BdryPost Fr hnn (Nat.le_of_succ_le hk) rep Zof aw μs ε ε1 νs fac rate hv)
    (hgeo : geo = g)
    {A : LabHist S n R k0 K} (hA : A ∈ rep.hist) {X : Finset (Torus S.d (n k))}
    (hX : X ∈ bdryDomsPost Fr A k (Zof A)) (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ)
    (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ ρc : ℝ) (ρ r : ℕ) {Rp rψ : ℝ} (hL : 2 ≤ S.L)
    (hIn : H7MixedInnerLoc g hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ ρc ρ r aw μs ε ε1 νs (hC hv)
      Rp rψ)
    (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {ψ : MultiFieldC S n M K N}
    {q' : FinFieldC S n M K N} {gx : GIdx S n M K N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH A.H M) (k + 1) hk Yf aw μs ε ε1 νs (hC hv) ψ
      (extK q') (fun x i => gx (x, i)))
    (hXY : fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ⊆ Yf)
    (hV : ∀ x ∈ dataSites (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G',
      fineOfC g hnn hM1 hk x ∈ Yf)
    {ψhat : (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).U → Fin N → ℂ}
    (hψhat : ∀ b, vn (ψhat b) < rψ)
    {s : Dec2.DecParams (coverOf (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')}
    (hs : ∀ P, ‖s P‖ < Rp) :
    ‖(holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).oldInterp
        (coverOf (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G') ρc
        (locDomsLF g hM1 (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V) ρ)
        (collarCoreC (c := g.c) (A.H.step k) hM1 r X) ∅ ψhat
        (oldTermLF g hnn hM1 rep A X hk (holeStepLoc g hnn hM1 A.H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G'
          ψ (extK q') hv gx)
        (fun b => absurd b.2 (Finset.notMem_empty _)) s‖ <
      fac * Real.exp (-rate * d7Size Fr A k X) := by
  subst hgeo
  exact norm_oldInterp_locAt_lt (glob := false) geo hnn hM1 hk hrec rfl hA hX hk1 hρ z h₀ a₁ ν β p₁ δ
    ρc ρ r V (h7Domain_composedMulti_loc geo hnn hM1 A.H hk hk1 hρ z h₀ a₁ ν β p₁ δ ρc ρ r aw μs ε
      ε1 νs (hC hv) hL hIn V X htgt hXY hV hψhat hs)

end Bound

end Balaban.RootFSpine
