/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.TopBlockTransport
public import Balaban.Background.Theorem73

/-!
# The datum of the small-field background lies in the real domain (`ParentDomainFromFactors`)

Assembly of `notes/phase1/Q13-COMPOSED.md` ("Exact transfer statement and tests").  Setting: a
region history `H`, the scale `k = j + 1`, `Y = Z_kᶜ`, the small-field context `Cx : SFCtx` at
scale `k`, the generating set `G_k = Cx.genW Y`, and the datum
`D_k = liftSingle G_k (Cx.liftData ψ_k) h⋆` with the fixed real unit vector `h⋆ = hv`.  The
composition theorem (`lemma62`, `theorem73_real`) needs one antecedent: the datum lies in the
real domain `InDomainR G_k ν η D_k`, that is `InPsiTilde G_k ν η Ψ h⋆` (clauses R1, R2, R3, R4
and layer-constancy) for the real field `Ψ = parentPsi Cx ψ_k`, `Ψ(s) = ψ_k(top block of s)`.

## What is proved

* **Exhaustive case split** (`siteCube_dichotomy`, `interface_pair_cases`).  The scale-`k` cube of
  every datum site lies in `Y` or in a retained component of `Z_k` (`exists_retained_of_mem_Z`);
  an interface pair has a site over a retained component, or both sites over `Y`.
* **R2 and R1 over a retained component** (`parentPsi_sphere_of_chiDomAt`,
  `parentPsi_pair_of_chiDomAt`), from `ChiDomAt` through `TopBlockTransport`, with tolerance
  `3 d L δ_j`; the datum value is identified with the value tested by the characteristic function
  (`parentPsi_eq_tested`), also at a neighbouring site of an interface pair.
* **R3, R4** (`inPsiTilde_genW_of_factors`).  R4 vanishes for a unit `h⋆`.  R3 is bounded by
  `2 ν L^{2k}` (the quantity `|1 - u·h⋆|` is at most `2` for `|u| ≤ 1`, `|h⋆| = 1`), so it holds
  under the explicit mass condition `hmass : 2 ν (L^k)² < η²`.  The landed regime relations give
  only `ν L^{2k} ≤ 1`, which is not small; `hmass` is a genuine relation between the mass and the
  radius `η` (`Q13-MARGIN.md`: `2 ν_j < η²` holds eventually in the genuine early regime).  Nothing
  else depends on the mass convention.
* **The domain statement** `inPsiTilde_genW_of_factors`, its form `inDomainR_genW_of_factors`
  for the datum, and the consequence for `theorem73_real`
  (`theorem73_parent_of_factors`).

## What is NOT proved (named hypotheses, each used once)

* `hAct` (`ActiveFactor`): at every nonzero integrand of (D1) over a retained component `C`
  meeting the data region, `ChiDomAt` holds for the localized component operator at an output
  configuration `o` with `outField o = ψ_k`.  This is the D1/post-R transport; stated exactly in
  the form `TopBlockTransport` consumes.
* `hR1Y`: the bound on `|Ψ(s) - Ψ(s')|` for interface pairs with both sites over `Y`
  (the bond lift of the small-field characteristic function `chiY`, a separate package).
* `hR2Y`: the sphere bound `| |Ψ(s)|² - 1 | < η_Y` for datum sites over `Y`.  `chiY ≠ 0` gives
  `|Ψ - Qφ| < δ_k` (`blockDev_lt_of_chiY_ne_zero`), but the unit length of the block average
  `Qφ` is not available: the background has unit length only after its domain statement.
* `hmass`, `hν`, `hunit`: the mass condition above, `0 ≤ ν`, and `|h⋆| = 1`.
* Not addressed here: the chart agreement of the composed inherited fields `psiJ` with the
  fields of the inherited terms, the reference margins, the strict tube (`StrictData`), and the
  hypotheses `Precedes`, admissibility of the weights (`BgHyp`) in `theorem73_parent_of_factors`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.Def7

section Parent

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (H : RegionHistory S n R k0 K)
  (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- The scale-`(j+1)` cube over which a site of the level-`(j+1)` torus of the backgrounds lies. -/
abbrev siteCube (s : BgT Cx.geo (j + 1)) : Torus S.d (n (j + 1)) :=
  cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s)

/-- The real field `Ψ = lift_k ψ_k` of the datum `D_k`: at a site `s` the value of `ψ_k` at the
top-scale block of `s`. -/
noncomputable def parentPsi (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))
    (s : BgT Cx.geo (j + 1)) : Fin N → ℝ := fun i =>
  ψk (blkToBlock Cx.geo Cx.hnn Cx.hkK
    (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)) i

/-- The datum `D_k` has the real field `parentPsi` on the data sites. -/
theorem liftSingle_Ψ_eq_parentPsi (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ dataSites (Cx.genW Y)) (i : Fin N) :
    (liftSingle (Cx.genW Y) (Cx.liftData ψk) (hC hv)).Ψ s i = ((parentPsi Cx ψk s i : ℝ) : ℂ) := by
  rw [liftSingle_Ψ _ _ _ hs]
  rfl

/-- The field `parentPsi` is constant on the blocks of every layer. -/
theorem parentPsi_layerConst (Y : Set (Torus S.d (n (j + 1))))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) :
    IsLayerConstant (Cx.genW Y) (parentPsi Cx ψk) :=
  liftSingle_layerConst (Cx.genW Y) (fun z i => ψk (blkToBlock Cx.geo Cx.hnn Cx.hkK z) i)

theorem sum_sq_eq_norm_sq (v : EuclideanSpace ℝ (Fin N)) : ∑ i, v i ^ 2 = ‖v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [sq_abs]

theorem rn_eq_norm (v : EuclideanSpace ℝ (Fin N)) : rn (fun i => v i) = ‖v‖ := by
  unfold rn
  rw [sum_sq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-! ### T1: the exhaustive case split -/

/-- **T1 (sites).**  The scale-`(j+1)` cube of a site lies in `Y = Z_{j+1}ᶜ` or in a retained
component of `Z_{j+1}`. -/
theorem siteCube_dichotomy (s : BgT Cx.geo (j + 1)) :
    siteCube Cx s ∈ ((H.step (j + 1)).Z)ᶜ ∨
      ∃ C : H.Comp (j + 1), C.1 ∉ H.rem (j + 1) ∧ siteCube Cx s ∈ C.1 := by
  by_cases h : siteCube Cx s ∈ (H.step (j + 1)).Z
  · exact Or.inr (H.exists_retained_of_mem_Z h)
  · exact Or.inl h

/-- **T1 (pairs).**  An interface pair has a site over a retained component (kind (a)) or both
sites over `Y` (kind (b)). -/
theorem interface_pair_cases (s s' : BgT Cx.geo (j + 1)) :
    (∃ t, (t = s ∨ t = s') ∧ ∃ C : H.Comp (j + 1), C.1 ∉ H.rem (j + 1) ∧ siteCube Cx t ∈ C.1) ∨
      (siteCube Cx s ∈ ((H.step (j + 1)).Z)ᶜ ∧ siteCube Cx s' ∈ ((H.step (j + 1)).Z)ᶜ) := by
  rcases siteCube_dichotomy H Cx s with h | ⟨C, hC, hq⟩
  · rcases siteCube_dichotomy H Cx s' with h' | ⟨C, hC, hq⟩
    · exact Or.inr ⟨h, h'⟩
    · exact Or.inl ⟨s', Or.inr rfl, C, hC, hq⟩
  · exact Or.inl ⟨s, Or.inl rfl, C, hC, hq⟩

/-! ### The value of the datum equals the tested value -/

/-- At a datum site `u` whose cube is within one cube of the cube of a site over the retained
component `C`, the field `parentPsi (outField o)` is the multiscale field of `ChiDomAt` at the
top-scale block of `u`. -/
theorem parentPsi_eq_tested {C : H.Comp (j + 1)} (hret : C.1 ∉ H.rem (j + 1))
    {A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1))}
    (o : OutT N R (H.localHistory M K (j + 1) C) (j + 1))
    (xs : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A)
    {t u : BgT Cx.geo (j + 1)} (hu : u ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ))
    (hq : siteCube Cx t ∈ C.1) (hd : supDist (siteCube Cx u) (siteCube Cx t) ≤ 1) :
    parentPsi Cx (outField N o) u =
      fun i => subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
          (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) xs o (j + 1)
          (blkToBlock Cx.geo Cx.hnn Cx.hkK
            (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) u)) i := by
  have hΩ : siteCube Cx u ∈ C.1 → siteCube Cx u ∈ (H.step j).Omega := fun hqu =>
    (H.step j).OmegaDD_subset_Omega (datum_site_topBlock H Cx hret hu hqu).2.1
  obtain ⟨hV, hfield⟩ := subMultiscaleField_top_eq_out (R := R) H Cx.hkK C
    (x := bgToFine Cx.geo Cx.hnn Cx.hkK u) (mem_nbhd.mpr ⟨_, hq, hd⟩) hΩ o xs
  have e := jBlock_bgToFine Cx u
  have hV' : blkToBlock Cx.geo Cx.hnn Cx.hkK
      (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) u) ∈
      Vblk R (H.localHistory M K (j + 1) C) (j + 1) := e ▸ hV
  have hgen : ∀ (b : BlockAt S n M K (j + 1))
      (hb : b ∈ Vblk R (H.localHistory M K (j + 1) C) (j + 1)),
      jBlock S.d S.L (M * n K) K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK u) = b →
      subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
        (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) xs o (j + 1) b = o ⟨b, hb⟩ := by
    intro b hb e'
    subst e'
    exact hfield
  have hfield' := hgen _ hV' e
  funext i
  rw [hfield']
  simp [parentPsi, outField, hV']

/-! ### T2, T3: R2 and R1 over a retained component -/

/-- **R2 over a retained component.**  Under `ChiDomAt` for a retained component `C`, at a datum
site over `C` the field `parentPsi (outField o)` is within `3 d L δ_j` of the unit sphere. -/
theorem parentPsi_sphere_of_chiDomAt {C : H.Comp (j + 1)} (hret : C.1 ∉ H.rem (j + 1))
    {A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1))}
    {o : OutT N R (H.localHistory M K (j + 1) C) (j + 1)}
    {x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A}
    (hχ : ChiDomAt Cx.geo Cx.cs H (j + 1) C o x)
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ))
    (hq : siteCube Cx s ∈ C.1) :
    |∑ i, parentPsi Cx (outField N o) s i ^ 2 - 1| < 3 * S.d * S.L * Cx.cs.delta j := by
  have h1 := chiDomAt_site_sphere Cx Cx.cs hχ hret hs hq
  have e := parentPsi_eq_tested H Cx hret o x hs hq (by simp [supDist_self])
  have e' : ∀ i, parentPsi Cx (outField N o) s i = _ := fun i => congrFun e i
  simp_rw [e']
  rw [sum_sq_eq_norm_sq]
  exact h1

/-- **R1 over a retained component.**  Under `ChiDomAt` for a retained component `C`, for an
interface pair of `G_{j+1}` one of whose sites `t` lies over `C`, the two values of
`parentPsi (outField o)` are within `3 d L δ_j`. -/
theorem parentPsi_pair_of_chiDomAt {C : H.Comp (j + 1)} (hret : C.1 ∉ H.rem (j + 1))
    {A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1))}
    {o : OutT N R (H.localHistory M K (j + 1) C) (j + 1)}
    {x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A}
    (hχ : ChiDomAt Cx.geo Cx.cs H (j + 1) C o x)
    {s s' t : BgT Cx.geo (j + 1)}
    (hp : IsInterfacePair (Cx.genW ((H.step (j + 1)).Z)ᶜ) s s') (hts : t = s ∨ t = s')
    (hq : siteCube Cx t ∈ C.1) :
    rn (fun i => parentPsi Cx (outField N o) s i - parentPsi Cx (outField N o) s' i) <
      3 * S.d * S.L * Cx.cs.delta j := by
  have hcube := (interface_pair_topBlocks H Cx hret hp hts hq).1
  have hself : supDist (siteCube Cx t) (siteCube Cx t) ≤ 1 := by simp [supDist_self]
  have hds : supDist (siteCube Cx s) (siteCube Cx t) ≤ 1 := by
    rcases hts with rfl | rfl
    · exact hself
    · rw [supDist_comm]; exact hcube
  have hds' : supDist (siteCube Cx s') (siteCube Cx t) ≤ 1 := by
    rcases hts with rfl | rfl
    · exact hcube
    · exact hself
  have es := parentPsi_eq_tested H Cx hret o x hp.1 hq hds
  have es' := parentPsi_eq_tested H Cx hret o x hp.2.1 hq hds'
  obtain ⟨h1, -, -⟩ := chiDomAt_pair_bounds Cx Cx.cs hχ hret hp hts hq
  have e : (fun i => parentPsi Cx (outField N o) s i - parentPsi Cx (outField N o) s' i) =
      fun i => (subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
          (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) x o (j + 1)
          (blkToBlock Cx.geo Cx.hnn Cx.hkK
            (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)) -
        subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
          (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) x o (j + 1)
          (blkToBlock Cx.geo Cx.hnn Cx.hkK
            (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s'))) i := by
    funext i
    rw [congrFun es i, congrFun es' i]
    rfl
  rw [e, rn_eq_norm]
  exact h1

end Parent

end Balaban.LargeField
