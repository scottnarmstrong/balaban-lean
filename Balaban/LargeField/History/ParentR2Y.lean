/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.ParentDomain
public import Balaban.LargeField.History.BondLiftY

/-!
# The assembly of the parent domain with the `Y`-clauses discharged (`ParentR2Y`)

`notes/phase1/Q13-YDOMAIN.md` §1.  There is no separate sphere test in the small-field
characteristic function (P5 (1.19), P1 (2.30)); the sphere condition of the real domain
(P1 (3.18)) comes from averaging.  The averaging bound `sphere_sq_over_Y` and the pair bound
`pair_bound_over_Y_either` (file `BondLiftY`) are bridged here to the shapes `hR2Y` (sum of
squares of `parentPsi`) and `hR1Y` (`rn` of the difference) of `inPsiTilde_genW_of_factors`.

## What is proved

* `parentPsi_sphere_over_Y`: for a datum site over a cube of `Y` with `χ_Y ≠ 0` and the cube
  `BgHyp`, `|Σ_i Ψ(s)_i² - 1| < (d+1)δ_k (2 + (d+1)δ_k)`.
* `parentPsi_pair_over_Y`: for an interface pair with a site over `Y`, `rn(Ψ(s) - Ψ(s')) < 3δ_k`.
* `inPsiTilde_genW_of_chiY`: the assembly with `hR2Y` and `hR1Y` discharged, for
  `η_Y = 4 (d+1) δ_k` (needs `0 < δ_k`, `(d+1) δ_k ≤ 1`).

## Case split

`interface_pair_cases` uses `siteCube_dichotomy`, which uses `exists_retained_of_mem_Z` (every
cube of `Z_k` lies in a retained component): every site is over `Y` or over a retained
component, so no third class exists.

## Still open

`hAct` (activity factor over retained components) and `hmass`; the cube `BgHyp` is an explicit
typing hypothesis (`SFCtx` does not carry it).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.Def7

section Bridge

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (H : RegionHistory S n R k0 K)
  (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- **R2Y.**  For a datum site `s` over a cube of `Y`, with `χ_Y ≠ 0` and the cube `BgHyp`,
`|Σ_i Ψ(s)_i² - 1| < (d+1)δ_k (2 + (d+1)δ_k)`. -/
theorem parentPsi_sphere_over_Y (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    {s : BgT Cx.geo (j + 1)} (hY : parentSiteCube Cx s ∈ Y) :
    |∑ i, parentPsi Cx ψk s i ^ 2 - 1| <
      ((S.d + 1) * Cx.cs.delta (j + 1)) * (2 + (S.d + 1) * Cx.cs.delta (j + 1)) := by
  have hs : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s =
      parentSiteCube Cx s := (cubeMap_bgToFine Cx s).symm
  have := sphere_sq_over_Y Cx Y ψk hv h HB hY hs
  rw [← parent_sum_sq_eq_norm_sq] at this
  exact this

/-- **R1Y (either site over `Y`).**  `rn (Ψ(s) - Ψ(s')) < 3 δ_k` for an interface pair of `G_k`
with a site over a cube of `Y`, from `χ_Y ≠ 0` alone. -/
theorem parentPsi_pair_over_Y (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (h : Cx.chiY Y ψk hv ≠ 0) {s s' : BgT Cx.geo (j + 1)}
    (hp : IsInterfacePair (Cx.genW Y) s s')
    (hY : parentSiteCube Cx s ∈ Y ∨ parentSiteCube Cx s' ∈ Y) :
    rn (fun i => parentPsi Cx ψk s i - parentPsi Cx ψk s' i) < 3 * Cx.cs.delta (j + 1) := by
  have e1 := fun i => liftSingle_Ψ_eq_parentPsi Cx Y ψk hv hp.1 i
  have e2 := fun i => liftSingle_Ψ_eq_parentPsi Cx Y ψk hv hp.2.1 i
  rcases hY with hy | hy
  · have := pair_bound_over_Y_either Cx Y ψk hv h hy
      (Or.inl (cubeMap_bgToFine Cx s ▸ rfl)) hp
    simp_rw [e1, e2] at this
    rwa [show (fun i => ((parentPsi Cx ψk s i : ℝ) : ℂ) - ((parentPsi Cx ψk s' i : ℝ) : ℂ)) =
      fun i => (((parentPsi Cx ψk s i - parentPsi Cx ψk s' i : ℝ)) : ℂ) by
        funext i; push_cast; rfl, vn_ofReal] at this
  · have := pair_bound_over_Y_either Cx Y ψk hv h hy
      (Or.inr (cubeMap_bgToFine Cx s' ▸ rfl)) hp
    simp_rw [e1, e2] at this
    rwa [show (fun i => ((parentPsi Cx ψk s i : ℝ) : ℂ) - ((parentPsi Cx ψk s' i : ℝ) : ℂ)) =
      fun i => (((parentPsi Cx ψk s i - parentPsi Cx ψk s' i : ℝ)) : ℂ) by
        funext i; push_cast; rfl, vn_ofReal] at this

/-- **The assembly with the `Y`-clauses discharged.**  `inPsiTilde_genW_of_factors` with
`hR2Y` and `hR1Y` replaced by `χ_Y ≠ 0` (for `Y = Z_kᶜ`) and the cube `BgHyp`, at
`η_Y = 4 (d+1) δ_k`, under `0 < δ_k` and `(d+1) δ_k ≤ 1`.  Open: `hAct`, `hmass`. -/
theorem inPsiTilde_genW_of_chiY (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))
    (hv : EuclideanSpace ℝ (Fin N)) (ν : ℝ) (hν : 0 ≤ ν) (hunit : ‖hv‖ = 1)
    (hδ : 0 < Cx.cs.delta (j + 1)) (hδ1 : (S.d + 1) * Cx.cs.delta (j + 1) ≤ 1)
    (hχ : Cx.chiY ((H.step (j + 1)).Z)ᶜ ψk hv ≠ 0)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (hmass : 2 * ν * ((S.L : ℝ) ^ (j + 1)) ^ 2 <
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1))) ^ 2)
    (hAct : ∀ C : H.Comp (j + 1), C.1 ∉ H.rem (j + 1) →
      (∃ t ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ), parentSiteCube Cx t ∈ C.1) →
      ∃ (A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1)))
        (o : OutT N R (H.localHistory M K (j + 1) C) (j + 1))
        (x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A),
        ChiDomAt Cx.geo Cx.cs H (j + 1) C o x ∧ outField N o = ψk) :
    InPsiTilde (Cx.genW ((H.step (j + 1)).Z)ᶜ) ν
      (max (3 * S.d * S.L * Cx.cs.delta j) (4 * (S.d + 1) * Cx.cs.delta (j + 1)))
      (parentPsi Cx ψk) (fun i => hv i) := by
  have hd : (0 : ℝ) ≤ S.d := Nat.cast_nonneg _
  have hε : 0 < (S.d + 1) * Cx.cs.delta (j + 1) := by positivity
  refine inPsiTilde_genW_of_factors H Cx ψk hv ν (4 * (S.d + 1) * Cx.cs.delta (j + 1)) hν hunit
    (by positivity) hmass hAct ?_ ?_
  · intro s _ hY
    refine (parentPsi_sphere_over_Y Cx _ ψk hv hχ HB hY).trans_le ?_
    nlinarith
  · intro s s' hp hY _
    refine (parentPsi_pair_over_Y Cx _ ψk hv hχ hp (Or.inl hY)).trans_le ?_
    nlinarith

end Bridge

end Balaban.LargeField
