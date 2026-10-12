module

public import Balaban.LargeField.Operators.Setup
public import Balaban.LargeField.LF1
public import Balaban.LargeField.Background.StepBackgrounds
public import Balaban.LargeField.Analytic.Constants

/-!
# The main action of the new large-field region (Part II, Definition II.5.4, block J3)

For a component `Z'` of `Z^pre_{k+1}` of a region history `H` without removals (the lineage
localization `locRH` of the component), `X_{Z'} = Z^c_k ∩ Z'` (fine sites of the level-`(k+1)`
torus), `𝔹_{k+1}` the generating set of the history (`histGen`, transported to the level-`(k+1)`
torus), `φ = φ^loc_{k+1}` the local background of Definition II.2.7 (iv) (`bgLocPiece`, extended to
the sites by the data), and `ψ` the multiscale field:
```
𝒜_{k+1}(Z'; ψ) = β^{(k+1)}_0 ( A_{𝔹_{k+1}}(X_{Z'}; ψ, φ) + ¼ ∑_{b ∈ st(X_{Z'})} |∂φ(b)|² ),
```
with `A_G` the action of §II.4 (`actionG`; mass `ν_{k+1} L^{-2(k+1)}`, present for every `k`) and
`st(X)` the bonds with exactly one end point in `X` (the boundary half-bonds of P5 (1.5)).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory

/-- `∑_{b ∈ st(X)} |∂φ(b)|²`: the bonds with exactly one end point in `X`. -/
noncomputable def starBondE {E : Type*} [NormedAddCommGroup E] {d ℓ : ℕ} [NeZero ℓ]
    (X : Finset (Torus d ℓ)) (φ : Torus d ℓ → E) : ℝ := by
  classical
  exact ∑ μ : Fin d, ∑ x, if (x ∈ X) ≠ (x + Pi.single μ 1 ∈ X) then bondTerm φ μ x else 0

theorem starBondE_nonneg {E : Type*} [NormedAddCommGroup E] {d ℓ : ℕ} [NeZero ℓ]
    (X : Finset (Torus d ℓ)) (φ : Torus d ℓ → E) : 0 ≤ starBondE X φ := by
  classical
  unfold starBondE
  exact Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact bondTerm_nonneg φ μ x
    · exact le_rfl

theorem actionG_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {d L N₀ q : ℕ}
    [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ q ϱ) {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) {μ : ℝ} (hμ : 0 ≤ μ) (h : E) (X : Finset (Site d L N₀ q))
    (ψ : (m : ℕ) → Blk d L N₀ q m → E) (φ : Site d L N₀ q → E) :
    0 ≤ actionG G a μ h X ψ φ := by
  unfold actionG
  have h1 : 0 ≤ ∑ n ∈ Finset.Icc 1 q, ∑ y ∈ tBlocks d L N₀ q n (lam G n ∩ X),
      a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun y _ => by
      have := ha n
      positivity
  have h2 := bondE_nonneg X φ
  have h3 : 0 ≤ ∑ x ∈ X, ‖φ x - h‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  positivity

section Step

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} (g : Geo S n R M) (Hl : RegionHistory S n R k0) (k : ℕ)
  (Zc : Finset (Torus S.d (n (k + 1)))) (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1)))

include g in
theorem Geo.three_L_le_floor (Hl : RegionHistory S n R k0) (j : ℕ) : 3 * S.L ≤ ⌊R j⌋₊ := by
  apply Nat.le_floor
  have h1 := Hl.F.RH.base
  have h2 := g.hRlow j
  have h3 : (0 : ℝ) ≤ S.L := Nat.cast_nonneg _
  push_cast
  linarith

theorem Omega_compl_subset_Zpre' (st : RegionStep S.d S.L (n k) (n (k + 1)) (R (k - 1)) (R k))
    (ω : ℕ) (c : Option ℕ) : st.Omegaᶜ ⊆ st.Zpre ω c := by
  intro x hx
  by_contra hxn
  exact hx (st.OmegaDD_subset_Omega (st.Zpre_compl_subset_OmegaDD ω c hxn))

/-- The generating set `G^{Z'}_{k+1}` of the local background (Definition II.2.4 (v)). -/
noncomputable abbrev locGen :
    GeneratingSet S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) (minSep S.L g.M1) :=
  genBoundaryLocal g.M1 g.c (n (k + 1)) S.L k (Hl.step k) g.hc (Hl.F.hnn k) Hl.F.ok.two_le_L
    (g.three_L_le_floor Hl (k - 1)) (Hl.F.stepGeom k).rad.omega_rho
    (Omega_compl_subset_Zpre' k (Hl.step k) _ _) hZc

variable (cs : OpConsts) (hk : k + 1 ≤ K)

/-- The lifted data `ψ_k` of the local background: the large-field variable of scale `k`. -/
noncomputable def locLiftPsi (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) :
    BlockCfg S.d (g.M1 * (g.c * n (k + 1))) S.L (k + 1) k N :=
  blockCfgOf g Hl.F.hnn (Nat.le_succ k) hk (subVarField N x k)

/-- The lifted data `ψ_{k+1}` of the local background: the output variable. -/
noncomputable def locLiftTheta (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1)) :
    BlockCfg S.d (g.M1 * (g.c * n (k + 1))) S.L (k + 1) (k + 1) N :=
  blockCfgOf g Hl.F.hnn le_rfl hk (outField N o)

/-- The local background `φ^loc_{k+1}` on the piece of `Z'` (Definition II.2.7 (iv)) at the
configuration `(ψ_k, ψ_{k+1})` and the external direction `h`. -/
noncomputable def locBg (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    (locGen g Hl k Zc hZc).Ω 1 × Fin N → ℂ :=
  bgLocPiece (k := k) (Hl.step k) g.hc (Hl.F.hnn k) Hl.F.ok.two_le_L
    (g.three_L_le_floor Hl (k - 1)) (Hl.F.stepGeom k).rad.omega_rho
    (Omega_compl_subset_Zpre' k (Hl.step k) _ _) cs.aw (cs.mu (k + 1)) (bgC0 S.d S.L N) hZc
    (locLiftPsi g Hl k Zc hk x).toC (locLiftTheta g Hl k Zc hk o).toC (fun i => (hv i : ℂ))

/-- The data `lift_{k,k+1}(ψ_k, ψ_{k+1})` of the local background. -/
noncomputable def locData (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    BgData (locGen g Hl k Zc hZc) N :=
  liftMixed (locGen g Hl k Zc hZc)
    ((isCubeUnion_fineK1 (Hl.step k).Omega).isBlockUnion (le_refl _))
    (genBoundaryLocal_top_subset (Hl.step k) g.hc (Hl.F.hnn k) Hl.F.ok.two_le_L
      (g.three_L_le_floor Hl (k - 1)) (Hl.F.stepGeom k).rad.omega_rho
      (Omega_compl_subset_Zpre' k (Hl.step k) _ _) hZc)
    (locLiftPsi g Hl k Zc hk x).toC (locLiftTheta g Hl k Zc hk o).toC (fun i => (hv i : ℂ))

/-- The real field `φ̄` on the sites of the level-`(k+1)` torus: the real part of the local
background, extended by the data outside `Ω_1(G^{Z'})`. -/
noncomputable def locPhi (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    Site S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) → EuclideanSpace ℝ (Fin N) :=
  fun z => WithLp.toLp 2 fun i =>
    (barField (locGen g Hl k Zc hZc) (locData g Hl k Zc hZc hk o x hv).Ψ (locBg g Hl k Zc hZc cs hk o x hv)
      z i).re

/-- The fine sites of `X_{Z'} = Z^c_k ∩ Z'` in the level-`(k+1)` torus. -/
noncomputable def Xfine :
    Finset (Site S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1)) := by
  classical
  exact (fineK1 g.M1 g.c (n (k + 1)) S.L k (Zc : Set (Torus S.d (n (k + 1))))) \
    (fineK g.M1 g.c (n (k + 1)) S.L k (n k) (Hl.step k).Z)

/-- The multiscale field on the blocks of the level-`(k+1)` torus: `ψ_m` on the `m`-blocks,
`m ≤ k + 1`. -/
noncomputable def psiLevel (ψ : MultiField S n M K N) :
    (m : ℕ) → Blk S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) m → EuclideanSpace ℝ (Fin N) :=
  fun m y => if hm : m ≤ k + 1 then ψ m (torusCast (histScale_eq g.hM Hl.F.hnn hm hk) y) else 0

variable (hrem : ∀ j, Hl.rem j = ∅)

/-- The history's generating set `𝔹_{k+1}` on the level-`(k+1)` torus. -/
noncomputable def histGenLevel :
    GeneratingSet S.d S.L (g.M1 * (g.c * n (k + 1))) (k + 1) ((S.L : ℝ) * M * S.Rb) :=
  castGen ((congrArg (· * n (k + 1)) g.hM).trans (by ring))
    (Hl.histGen (M := M) hrem Hl.F.ok.two_le_L (k + 1) (fun j _ _ => g.hRlow j))

/-- **Definition II.5.4 (main action of the new large-field region)** at the configuration
`(o, x) = (ψ_{k+1}|_V, I^new_k)` (the variables the action reads) and the external direction `h`:
`𝒜_{k+1}(Z'; ψ) = β^{(k+1)}_0 (A_{𝔹_{k+1}}(X_{Z'}; ψ, φ) + ¼ ∑_{b ∈ st(X_{Z'})} |∂φ(b)|²)`. -/
noncomputable def mainActionLoc (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) : ℝ :=
  betaCanon S.d S.L (cs.beta (k + 1)) (k + 1) 0 *
    (actionG (histGenLevel g Hl k hrem) cs.aw (cs.muAct (k + 1)) hv (Xfine g Hl k Zc)
        (psiLevel g Hl k hk
          (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
            (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) x o))
        (locPhi g Hl k Zc hZc cs hk o x hv) +
      1 / 4 * starBondE (Xfine g Hl k Zc) (locPhi g Hl k Zc hZc cs hk o x hv))

theorem mainActionLoc_nonneg (hb : 0 ≤ cs.beta (k + 1)) (ha : ∀ n, 0 ≤ cs.aw n)
    (hμ : 0 ≤ cs.muAct (k + 1)) (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    0 ≤ mainActionLoc g Hl k Zc hZc cs hk hrem o x hv := by
  unfold mainActionLoc betaCanon
  have h1 := actionG_nonneg (histGenLevel g Hl k hrem) ha hμ hv (Xfine g Hl k Zc)
    (psiLevel g Hl k hk
      (subMultiscaleField N (locHist Hl M K (k + 1) Zc) (k + 1)
        (Vblk R (locHist Hl M K (k + 1) Zc) (k + 1)) x o))
    (locPhi g Hl k Zc hZc cs hk o x hv)
  have h2 := starBondE_nonneg (Xfine g Hl k Zc) (locPhi g Hl k Zc hZc cs hk o x hv)
  have h3 : 0 ≤ cs.beta (k + 1) / (S.L : ℝ) ^ ((k + 1 - 0) * (S.d - 2)) := by positivity
  positivity

end Step

end Balaban.LargeField
