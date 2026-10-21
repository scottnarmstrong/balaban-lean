/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.LFOldLocCoef

/-!
# OPEN-H7-MIXED for the local pair (reading HS-1′): the named inputs and the transfer

The image lemma OPEN-H7-MIXED (`notes/phase1/PLAN-B.md`) for the composite of the local pair
`(coverOf G′_V, G′_V)` (reading HS-1′), split into the part proved by transfer
(`h7Domain_composedMulti_of_inner`) and two named inputs, both open:

* `H7MixedInnerLoc` (**open**; P5 (2.39)–(2.43), the inclusion of the composed field in the domain
  of the characteristic functions of scale `k`): at the cubes `□ ⊂ X` of `𝕋_k` near `Ω_{k+1}`, the
  composed field of the local pair lies in `Δ^c_k(□; 1, ε_k)`, for every field of the H7 domain of
  scale `k + 1` at a set `Y_f` containing `X` and the data sites of `G′_V`, every fluctuation field
  `|ψ̂| < r_ψ` and every parameter `|s_P| < R`;
* `H7MixedDatumLoc` (**open**; the background part): under the same hypotheses on the field, the
  datum of the local pair lies in `Ψ̃^c(G′_V; δ_b, δ_b)` (the domain of Theorem I-4b).

Proved here:

* `coverSide`, `fineOfC`: the cover torus of the step is the fine torus of the history;
* `h7Domain_composedMulti_loc`: from `H7MixedInnerLoc`, the composed multiscale field of the local
  pair, with the fluctuation field and `g` of the target, lies in the H7 domain of scale `k` at `X`
  (`h7Domain_composedMulti_of_inner` with `cubeOfC_mem_of_unitPts_loc`).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.Multiscale
  Balaban.Localization Balaban.Fluctuation Balaban.LargeField.RegionHistory Balaban.Background

namespace Balaban.RootFSpine

section Inputs

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ : ℕ}
  (g : Geo S n R M) (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) (hM1 : g.M1 = S.L ^ m₁)

omit [NeZero M] in
include hnn hM1 in
/-- The cover torus of the step is the fine torus of the history. -/
theorem coverSide {k : ℕ} (hk : k + 1 ≤ K) :
    (g.c * n (k + 1)) * S.L ^ m₁ * S.L ^ (k + 1) = M * n K * S.L ^ K := by
  simpa using coverScale_eq g hnn hM1 (Nat.zero_le (k + 1)) hk

/-- **The site of the history torus of a site of the cover torus.** -/
def fineOfC {k : ℕ} (hk : k + 1 ≤ K) (x : CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)) :
    Torus S.d (M * n K * S.L ^ K) :=
  LargeField.torusCast (coverSide g hnn hM1 hk) x

/-- **OPEN-H7-MIXED, the remaining part, for the local pair** (reading HS-1′; **open**; P5
(2.39)–(2.43); P6 p. 34): for every multiscale field `(ψ, ψ', g)` in the H7 domain of scale `k + 1`
at a fine set `Y_f` containing the fine set of the old label `X` and the data sites of the local set
`G′_V` of (2.17), every fluctuation field `ψ̂` on the unit points of `G′_V` with `|ψ̂| < r_ψ` and
every parameter `s` with `|s_P| < R`: at every cube `□ ⊂ X` of `𝕋_k` outside `(Ω^c_k)^{∼3}` with a
cube of `𝕋_{k+1}` in `Ω^{∼3}_{k+1}`, the composed multiscale field of the local composite (P5 (2.39)
at the localization vectors of the core `X₁`) lies in `Δ^c_k(□; 1, ε_k)`. -/
def H7MixedInnerLoc (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ ρc : ℝ) (ρ r : ℕ)
    (aw μs ε ε1 νs : ℕ → ℝ) (h : Fin N → ℂ) (Rp rψ : ℝ) : Prop :=
  ∀ (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) (X : Finset (Torus S.d (n k)))
    (Yf : Set (Torus S.d (M * n K * S.L ^ K))) (ψ ψ' : MultiFieldC S n M K N)
    (gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ),
    H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ ψ' gf →
    fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ⊆ Yf →
    (∀ x ∈ dataSites (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G',
      fineOfC g hnn hM1 hk x ∈ Yf) →
    ∀ ψhat : (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).U → Fin N → ℂ,
    (∀ b, vn (ψhat b) < rψ) →
    ∀ s : Dec2.DecParams (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G'),
    (∀ P, ‖s P‖ < Rp) →
    ∀ y : Torus S.d (n k),
      CubeSub (S := S) (n := n) M K k y (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) →
      y ∉ omegaCNb (globalLH H M) 3 k →
      (¬ ∀ x, LargeField.cubeMap n S.L M K k x = y →
        LargeField.cubeMap n S.L M K (k + 1) x ∉ omegaNb (globalLH H M) (k + 1) 3 (k + 1)) →
      (fun z' => composedMulti g hnn hM1 hk (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G'
          ψ ((holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).composed
            (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G') ρc
            ((holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).slocOf
              (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')
              (locDomsLF g hM1 (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V) ρ)
              (HoleStep.coreExt
                (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')
                (collarCoreC (c := g.c) (H.step k) hM1 r X) s)) ψhat) k
          (LargeField.torusCast (histScale_eq g.hM hnn le_rfl (Nat.le_of_succ_le hk)) z')) ∈
        DeltaC (M1 := g.M1) (N₁ := g.c * n k) (L := S.L) (q := k) aw (μs k) (ε k) h g.c (n k) y

/-- **OPEN-H7-MIXED, the background part, for the local pair** (reading HS-1′; **open**): for every
multiscale field in the H7 domain of scale `k + 1` at a fine set `Y_f` containing the data sites of
the local set `G′_V`, the datum of the local pair (the mixed lift of `ψ_k` and `θ = z ψ_{k+1}`) lies
in `Ψ̃^c(G′_V; δ_b, δ_b)`, the domain of Theorem I-4b. -/
def H7MixedDatumLoc (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K) (hk1 : 1 ≤ k)
    (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ : ℝ)
    (aw μs ε ε1 νs : ℕ → ℝ) (h : Fin N → ℂ) (νb δb : ℝ) : Prop :=
  ∀ (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1)))
    (Yf : Set (Torus S.d (M * n K * S.L ^ K))) (ψ ψ' : MultiFieldC S n M K N)
    (gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ),
    H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ ψ' gf →
    (∀ x ∈ dataSites (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G',
      fineOfC g hnn hM1 hk x ∈ Yf) →
    InDomainC (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' νb δb δb
      (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).D'

/-- **The composite of the local pair lies in the source H7 domain** (OPEN-H7-MIXED for the local pair,
from the transfer `h7Domain_composedMulti_of_inner` and the remaining part `H7MixedInnerLoc`): for a
field of the H7 domain of scale `k + 1` at `Y_f ⊇ X ∪ dataSites(G′_V)`, a fluctuation field
`|ψ̂| < r_ψ` and a parameter `|s_P| < R`, the composed multiscale field of the local composite, with
the fluctuation field and `g` of the target, lies in the H7 domain of scale `k` at `X`. -/
theorem h7Domain_composedMulti_loc (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (hk1 : 1 ≤ k) (hρ : 3 * S.L ≤ ⌊R (k - 1)⌋₊) (z : ℝ) (h₀ : Fin N → ℝ) (a₁ ν β p₁ δ ρc : ℝ)
    (ρ r : ℕ) (aw μs ε ε1 νs : ℕ → ℝ) (h : Fin N → ℂ) {Rp rψ : ℝ} (hL : 2 ≤ S.L)
    (hIn : H7MixedInnerLoc g hnn hM1 H hk hk1 hρ z h₀ a₁ ν β p₁ δ ρc ρ r aw μs ε ε1 νs h Rp rψ)
    (V : Set (CTorus S.d S.L (g.c * n (k + 1)) m₁ (k + 1))) (X : Finset (Torus S.d (n k)))
    {Yf : Set (Torus S.d (M * n K * S.L ^ K))} {ψ ψ' : MultiFieldC S n M K N}
    {gf : Torus S.d (M * n K * S.L ^ K) → Fin N → ℂ}
    (htgt : H7Domain g.M1 g.c g.hM hnn (globalLH H M) (k + 1) hk Yf aw μs ε ε1 νs h ψ ψ' gf)
    (hXY : fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k))) ⊆ Yf)
    (hV : ∀ x ∈ dataSites (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G',
      fineOfC g hnn hM1 hk x ∈ Yf)
    {ψhat : (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).U → Fin N → ℂ}
    (hψhat : ∀ b, vn (ψhat b) < rψ)
    {s : Dec2.DecParams (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')}
    (hs : ∀ P, ‖s P‖ < Rp) :
    H7Domain g.M1 g.c g.hM hnn (globalLH H M) k (Nat.le_of_succ_le hk)
      (fineSet (S := S) (n := n) M K k (X : Set (Torus S.d (n k)))) aw μs ε ε1 νs h
      (composedMulti g hnn hM1 hk (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G' ψ
        ((holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).composed
          (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G') ρc
          ((holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).slocOf
            (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')
            (locDomsLF g hM1 (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V) ρ)
            (HoleStep.coreExt
              (coverOf (holeStepLoc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V).G')
              (collarCoreC (c := g.c) (H.step k) hM1 r X) s)) ψhat))
      ψ' gf :=
  h7Domain_composedMulti_of_inner g hnn hM1 H hk (by omega) hL
    (cubeOfC_mem_of_unitPts_loc g hnn hM1 H hk hk1 hρ ψ z h₀ a₁ ν β p₁ δ V) ψ _ hXY aw μs ε ε1 νs
    h ψ' gf htgt fun y hyX hyC hnear =>
      hIn V X Yf ψ ψ' gf htgt hXY hV ψhat hψhat s hs y hyX hyC hnear

end Inputs

end Balaban.RootFSpine
