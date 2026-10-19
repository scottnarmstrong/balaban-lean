/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowShellY
public import Balaban.LargeField.Operators.MainAction

/-!
# The output side of the piece datum over the small-field region (blocker 4)

The datum `locData` of a piece (the lifted pair `(ψ_k, ψ_{k+1})`, Definition II.2.7) is the output
field `ψ_{k+1} = outField o` on the `(k+1)`-blocks over `Ω_{k+1}` and the new variable `ψ_k` off it.
At a data site over a cube `y₁` of `Y = Z_{k+1}ᶜ` (outside the component, hence over `Ω_{k+1}`)
the datum is therefore the field `ψ_{k+1}` of a global post-weight configuration `ψ` that agrees
with `o` on the block, and the sphere and pair bounds of the small-field region (`parentPsi`) apply:

* `locData_Ψ_of_omega`: the value of the datum at a site over `Ω_{k+1}`;
* `mem_omega_of_not_mem_Zp`: a cube outside `Z^pre_{k+1}` lies in `Ω_{k+1}`;
* `interfacePair_top_adj`: an interface pair of any generating set has adjacent top blocks over
  cubes within one cube of each other;
* `locData_sphere_over_Y`: `|Σ_i Ψ(s)_i² - 1| < (d+1)δ_{k+1}(2 + (d+1)δ_{k+1})` at a site over `Y`;
* `locData_pair_over_Y`: `rn (Ψ(s) - Ψ(s')) < 3 δ_{k+1}` for an interface pair with `s` over `Y`
  and `s'` over `Ω_{k+1}`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.Def7

section ThetaY

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 M K : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)
  (Hl : RegionHistory S n R k0 K)
  (Zc : Finset (Torus S.d (n (j + 1)))) (hZc : Zc ∈ comps (S.omega (j + 1)) (Hl.F.Zp (j + 1)))
  (hk : j + 1 ≤ K)

/-- The datum at a data site over `Ω_{k+1}` is the output field `ψ_{k+1}` at the top block of the site. -/
theorem locData_Ψ_of_omega (o : OutT N R (locHist Hl M K (j + 1) Zc) (j + 1))
    (x : NewCfg N (locHist Hl M K (j + 1) Zc) j) (hv : EuclideanSpace ℝ (Fin N))
    {s : BgT Cx.geo (j + 1)}
    (hs : s ∈ dataSites (locGen Cx.geo Hl j Zc hZc hk))
    (hO : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s ∈ (Hl.step j).Omega) :
    (locData Cx.geo Hl j Zc hZc hk o x hv).Ψ s =
      fun i => ((outField N o (blkToBlock Cx.geo Hl.F.hnn hk
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)) i : ℝ) : ℂ) := by
  unfold locData
  rw [liftMixed_Ψ _ _ _ _ _ _ hs]
  unfold mixedLift
  have hm := (mem_fineK1).2 hO
  simp only [hm, ↓reduceIte]
  rfl

/-- A cube outside `Z^pre_{k+1}` lies in `Ω_{k+1}`. -/
theorem mem_omega_of_not_mem_Zp {y : Torus S.d (n (j + 1))}
    (hy : y ∉ Hl.F.Zp (j + 1)) : y ∈ (Hl.step j).Omega := by
  by_contra h
  exact hy (mem_finOf.2 (Omega_compl_subset_Zpre' j (Hl.step j) _ _ h))

/-- **The sphere bound for the datum at a site over `Y`** (R2): `|Σ_i Ψ(s)_i² - 1| < (d+1)δ_{k+1}(2 + (d+1)δ_{k+1})`
when `χ_{k+1}(Y) ≠ 0` for a global field `ψ` that agrees with the output `o` on the top block of `s`. -/
theorem locData_sphere_over_Y (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (hχ : Cx.chiY Y ψk hv ≠ 0)
    (HB : BgHyp S.d S.L (j + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (j + 1)))
    (hYZ : ∀ y ∈ Y, y ∉ Hl.F.Zp (j + 1))
    (o : OutT N R (locHist Hl M K (j + 1) Zc) (j + 1))
    (x : NewCfg N (locHist Hl M K (j + 1) Zc) j)
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ dataSites (locGen Cx.geo Hl j Zc hZc hk))
    (hy : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s ∈ Y)
    (hψ : ψk (blkToBlock Cx.geo Hl.F.hnn hk
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)) =
      outField N o (blkToBlock Cx.geo Hl.F.hnn hk
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s))) :
    |∑ i, ((locData Cx.geo Hl j Zc hZc hk o x hv).Ψ s i).re ^ 2 - 1| <
      ((S.d + 1) * Cx.cs.delta (j + 1)) * (2 + (S.d + 1) * Cx.cs.delta (j + 1)) := by
  have hO := mem_omega_of_not_mem_Zp Hl (hYZ _ hy)
  have h := parentPsi_sphere_over_Y Cx Y ψk hv hχ HB (s := s) (by unfold parentSiteCube; rw [cubeMap_bgToFine]; exact hy)
  have e : ∀ i, ((locData Cx.geo Hl j Zc hZc hk o x hv).Ψ s i).re = parentPsi Cx ψk s i := by
    intro i
    rw [locData_Ψ_of_omega Cx Hl Zc hZc hk o x hv hs hO]
    simp only [Complex.ofReal_re, parentPsi]
    rw [← hψ]
  simp_rw [e]
  exact h

/-- An interface pair of any generating set lies over cubes within one cube of each other, and
its top blocks contain adjacent sites. -/
theorem interfacePair_top_adj {d M1 N₁ L q c n : ℕ} [NeZero L] [NeZero M1] [NeZero N₁] [NeZero n]
    {ϱ : ℝ} (hm : N₁ * L ^ (q - q) = c * n) (hc : 0 < c * M1)
    {G : GeneratingSet d L (M1 * N₁) q ϱ} {s s' : Torus d (M1 * N₁ * L ^ q)}
    (hp : IsInterfacePair G s s') :
    supDist (blockMap (L ^ q * (c * M1)) n s) (blockMap (L ^ q * (c * M1)) n s') ≤ 1 ∧
    ∃ y y' : Torus d (M1 * N₁ * L ^ q), jBlock d L (M1 * N₁) q q y = jBlock d L (M1 * N₁) q q s ∧
      jBlock d L (M1 * N₁) q q y' = jBlock d L (M1 * N₁) q q s' ∧ Adj y y' := by
  obtain ⟨-, -, -, y, hy, y', hy', hadj⟩ := hp
  have e1 := jBlock_top_eq_of_mem_blockSet G hy
  have e2 := jBlock_top_eq_of_mem_blockSet G hy'
  refine ⟨?_, y, y', e1, e2, hadj⟩
  have := cube_adj_near hm hc hadj
  rwa [cube_eq_of_jBlock_eq hm e1, cube_eq_of_jBlock_eq hm e2] at this

/-- **The pair bound for the datum at an interface pair with `s` over `Y`** (R1): `rn (Ψ(s) - Ψ(s')) < 3 δ_{k+1}`
when `χ_{k+1}(Y) ≠ 0` and `s'` lies over `Ω_{k+1}`, for a global field `ψ` that agrees with the output `o` on the
top blocks of `s` and `s'`. -/
theorem locData_pair_over_Y (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    (hχ : Cx.chiY Y ψk hv ≠ 0)
    (hYZ : ∀ y ∈ Y, y ∉ Hl.F.Zp (j + 1))
    (o : OutT N R (locHist Hl M K (j + 1) Zc) (j + 1))
    (x : NewCfg N (locHist Hl M K (j + 1) Zc) j)
    {s s' : BgT Cx.geo (j + 1)} (hs : s ∈ dataSites (locGen Cx.geo Hl j Zc hZc hk))
    (hs' : s' ∈ dataSites (locGen Cx.geo Hl j Zc hZc hk))
    (hp : IsInterfacePair (locGen Cx.geo Hl j Zc hZc hk) s s')
    (hy : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s ∈ Y)
    (hO' : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) s' ∈ (Hl.step j).Omega)
    (hψ : ψk (blkToBlock Cx.geo Hl.F.hnn hk
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)) =
      outField N o (blkToBlock Cx.geo Hl.F.hnn hk
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)))
    (hψ' : ψk (blkToBlock Cx.geo Hl.F.hnn hk
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s')) =
      outField N o (blkToBlock Cx.geo Hl.F.hnn hk
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s'))) :
    rn (fun i => ((locData Cx.geo Hl j Zc hZc hk o x hv).Ψ s i).re -
      ((locData Cx.geo Hl j Zc hZc hk o x hv).Ψ s' i).re) < 3 * Cx.cs.delta (j + 1) := by
  have hO := mem_omega_of_not_mem_Zp Hl (hYZ _ hy)
  have hm : Cx.geo.c * n (j + 1) * S.L ^ (j + 1 - (j + 1)) = Cx.geo.c * n (j + 1) := by simp
  have hc : 0 < Cx.geo.c * Cx.geo.M1 := by
    have := Cx.geo.hc
    have h1 : 0 < Cx.geo.M1 := Nat.pos_of_ne_zero (NeZero.ne _)
    exact Nat.mul_pos (by omega) h1
  obtain ⟨hnear, y, y', e1, e2, hadj⟩ := interfacePair_top_adj (M1 := Cx.geo.M1) hm hc hp
  have hpair := parentPsi_pair_of_adj_over_Y Cx Y ψk hv hχ hy rfl
    (mem_nbhd.2 ⟨_, rfl, by rw [supDist_comm]; exact hnear⟩) ⟨y, y', e1, e2, hadj⟩
  have e : ∀ (t : BgT Cx.geo (j + 1)) (h : t ∈ dataSites (locGen Cx.geo Hl j Zc hZc hk))
      (hOt : blockMap (S.L ^ (j + 1) * (Cx.geo.c * Cx.geo.M1)) (n (j + 1)) t ∈ (Hl.step j).Omega)
      (hψt : ψk (blkToBlock Cx.geo Hl.F.hnn hk
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) t)) =
      outField N o (blkToBlock Cx.geo Hl.F.hnn hk
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) t))) i,
      ((locData Cx.geo Hl j Zc hZc hk o x hv).Ψ t i).re = parentPsi Cx ψk t i := by
    intro t h hOt hψt i
    rw [locData_Ψ_of_omega Cx Hl Zc hZc hk o x hv h hOt]
    simp only [Complex.ofReal_re, parentPsi]
    rw [← hψt]
  simp_rw [e s hs hO hψ, e s' hs' hO' hψ']
  exact hpair

end ThetaY

end Balaban.LargeField
