module

public import Balaban.LargeField.R.PieceChain
public import Balaban.LargeField.R.WindowConvPhysSwitch

/-!
# The two local backgrounds at the physical mass switch

P6 p. 14 (2.31) changes the Euler–Lagrange mass convention at `q = k₀ + 1`.
For the actual local datum of a history piece, Theorem 7.2 supplies the two
Euler–Lagrange equations and their bounds when both domain hypotheses are
available.  The spacing, cube cover, field-to-`h` and common-collar inputs of
`massChange_region_bound_cubes` remain separate.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.ActionConv

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}
  {k0 M K N : ℕ} [NeZero M] [NeZero S.L]
  (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (j : ℕ)
  (Zc : Finset (Torus S.d (n (j + 1))))
  (hZc : Zc ∈ comps (S.omega (j + 1)) (Hl.F.Zp (j + 1)))
  (hk : j + 1 ≤ K) (cs : OpConsts)
  (o : OutT N R (locHist Hl M K (j + 1) Zc) (j + 1))
  (x : NewCfg N (locHist Hl M K (j + 1) Zc) j)
  (hv : EuclideanSpace ℝ (Fin N))

/-- At the actual switch mass `cs.muAct (k₀ + 1)`, both backgrounds of the
same local datum satisfy EL and the Theorem 7.2 bounds, provided the two
declared background domains and their common radius are valid. -/
theorem locData_switch_el_bounds (δ ε : ℝ)
    (H0 : BgHyp S.d S.L (j + 1) (minSep S.L g.M1) cs.aw 0)
    (Hm : BgHyp S.d S.L (j + 1) (minSep S.L g.M1) cs.aw (cs.muAct (k0 + 1)))
    (hD0 : InUnionDomainC (locGen g Hl j Zc hZc hk) (bgC0 S.d S.L N)
      (bgC1 S.d S.L N) 0 (locData g Hl j Zc hZc hk o x hv))
    (hDm : InUnionDomainC (locGen g Hl j Zc hZc hk) (bgC0 S.d S.L N)
      (bgC1 S.d S.L N) (cs.muAct (k0 + 1)) (locData g Hl j Zc hZc hk o x hv))
    (hδ : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 S.d S.L N)
    (hδc : δ ≤ bgC1 S.d S.L N)
    (hsmall : cs.muAct (k0 + 1) * ((S.L : ℝ) ^ (j + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (hDC0 : InDomainC (locGen g Hl j Zc hZc hk) 0 δ ε
      (locData g Hl j Zc hZc hk o x hv))
    (hDCm : InDomainC (locGen g Hl j Zc hZc hk) (cs.muAct (k0 + 1)) δ ε
      (locData g Hl j Zc hZc hk o x hv)) :
    let G := locGen g Hl j Zc hZc hk
    let D := locData g Hl j Zc hZc hk o x hv
    let φ0 := bgFieldC G cs.aw 0 (bgC0 S.d S.L N) D
    let α0 := bgMultC G cs.aw 0 (bgC0 S.d S.L N) D
    let φm := bgFieldC G cs.aw (cs.muAct (k0 + 1)) (bgC0 S.d S.L N) D
    let αm := bgMultC G cs.aw (cs.muAct (k0 + 1)) (bgC0 S.d S.L N) D
    IsEL G cs.aw 0 D φ0 α0 ∧
    IsEL G cs.aw (cs.muAct (k0 + 1)) D φm αm ∧
    BgBounds G D φ0 α0 (bgK1 S.d S.L N * δ) ∧
    BgBounds G D φm αm (bgK1 S.d S.L N * δ) ∧
    GreenSetting G cs.aw 0 ∧ 0 ≤ cs.muAct (k0 + 1) := by
  have h0 := theorem72 H0 hD0
  have hm := theorem72 Hm hDm
  refine ⟨h0.2.1.1, hm.2.1.1, ?_, ?_, H0.green, Hm.mass⟩
  · exact h0.2.2 δ ε hδ hδε hε hδc (by simpa using sq_nonneg δ) hDC0
  · exact hm.2.2 δ ε hδ hδε hε hδc hsmall hDCm

/-- For an older piece, `massChange_region_bound_cubes` cannot use its switch
scale `k₀` on the original local generating set: every local spacing is at
most `L^(j+1)`, whereas the theorem asks for spacing at least `L^k₀`.
A comparison on a coarser common cover is required. -/
theorem locGen_switch_spacing_impossible (hj : j + 1 < k0)
    (X : Region (locGen g Hl j Zc hZc hk)) (hX : X.sites.Nonempty) :
    ¬ ∀ y ∈ X.sites, (S.L : ℝ) ^ k0 ≤ (locGen g Hl j Zc hZc hk).spacing y := by
  apply ActionConv.no_later_scale_spacing (locGen g Hl j Zc hZc hk) (by
    have hL := Hl.F.ok.two_le_L
    omega) hj X hX

end Balaban.LargeField
