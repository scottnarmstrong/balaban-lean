/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.ParentDomain
public import Balaban.LargeField.Def7Hist

/-!
# Local output equality and the parent domain without a field equality (`LocalOutputTransport`)

`notes/phase1/Q13-ACTIVE.md` §2.  The output configuration of a localized operator is the
restriction of the block field `ψ_k` to the set `V` of blocks of the component
(`Def7.outOf R a k ψ_k = fun y => ψ_k y`).  Its extension by zero (`outField`) agrees with `ψ_k`
on `V` only, not on the whole torus.  The assembly `inPsiTilde_genW_of_factors` of `ParentDomain`
asks for `outField o = ψ_k` everywhere, which is stronger than what the operator support gives.

## What is proved

* `outField_outOf_of_mem`, `outField_outOf_of_notMem`: `outField (outOf ψ_k)` is `ψ_k` on
  `Vblk` and `0` off it.
* `datum_value_eq_tested_local`, `parentPsi_eq_tested_local`: the value of the datum, resp. of
  `parentPsi ψ_k`, at a site near a retained component equals the value of the multiscale field
  tested by the characteristic function, with the output configuration `outOf ψ_k`.
* `parentPsi_sphere_of_chiDomAt_local`, `parentPsi_pair_of_chiDomAt_local`: R2 and R1 over a
  retained component from `ChiDomAt` at `outOf ψ_k`, tolerance `3 d L δ_j`.  The neighbouring
  site of an interface pair is covered (both of its top blocks lie in `Vblk`).
* `inPsiTilde_genW_of_factors_local`: the assembly of `ParentDomain` with `hAct` replaced by
  `hActLoc` (`ChiDomAt` at the configuration `outOf ψ_k`, for some internal configuration); there
  is no field equality in the hypotheses.

The landed theorems with the full equality stay; they are the special case of the present ones.
The statements are for the scale `k = j + 1` and say nothing about the composed inherited fields.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.LargeField.Def7

section Out

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- On the blocks of the output set the extension by zero of `outOf ψ_k` is `ψ_k`. -/
theorem outField_outOf_of_mem (a : LocalHistory S n M K) (k : ℕ)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) {b : BlockAt S n M K k}
    (hb : b ∈ Vblk R a k) : outField N (outOf R a k ψk) b = ψk b := by
  simp [outField, outOf, hb]

omit [∀ k, NeZero (n k)] [NeZero M] [NeZero S.L] in
/-- Off the output set the extension by zero of `outOf ψ_k` vanishes. -/
theorem outField_outOf_of_notMem (a : LocalHistory S n M K) (k : ℕ)
    (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) {b : BlockAt S n M K k}
    (hb : b ∉ Vblk R a k) : outField N (outOf R a k ψk) b = 0 := by
  simp [outField, hb]

end Out

section Parent

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N m₁ j : ℕ} {ϱ : ℝ} (H : RegionHistory S n R k0 K)
  (Cx : SFCtx S n R M K N (j + 1) m₁ ϱ)

/-- At a datum site over a retained component the datum of `ψ_k` has the value of the multiscale
field tested by the characteristic function, with the output configuration `outOf ψ_k`. -/
theorem datum_value_eq_tested_local {C : H.Comp (j + 1)} (hret : C.1 ∉ H.rem (j + 1))
    {A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1))}
    (xs : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A)
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ))
    (hq : cubeMap n S.L M K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s) ∈ C.1) :
    (liftSingle (Cx.genW ((H.step (j + 1)).Z)ᶜ) (Cx.liftData ψk) (hC hv)).Ψ s =
      fun i => ((subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
          (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) xs
          (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) (j + 1)
          (blkToBlock Cx.geo Cx.hnn Cx.hkK
            (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)) i : ℝ) : ℂ) := by
  have hnb := dataSite_cube_mem_nbhd Cx H.F.ok.two_le_L _ hs
  have hΩ := (H.step j).OmegaDD_subset_Omega (H.retained_shell_subset_OmegaDD j hret hq hnb)
  obtain ⟨hV, hfield⟩ := subMultiscaleField_top_eq_out (R := R) H Cx.hkK C
    (x := bgToFine Cx.geo Cx.hnn Cx.hkK s) (mem_nbhd.mpr ⟨_, hq, by simp [supDist_self]⟩)
    (fun _ => hΩ) (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) xs
  have e := jBlock_bgToFine Cx s
  have hV' : blkToBlock Cx.geo Cx.hnn Cx.hkK
      (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s) ∈
      Vblk R (H.localHistory M K (j + 1) C) (j + 1) := e ▸ hV
  have hgen : ∀ (b : BlockAt S n M K (j + 1))
      (hb : b ∈ Vblk R (H.localHistory M K (j + 1) C) (j + 1)),
      jBlock S.d S.L (M * n K) K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK s) = b →
      subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
        (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) xs
        (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) (j + 1) b = ψk b := by
    intro b hb e'
    subst e'
    exact hfield
  have hfield' := hgen _ hV' e
  rw [liftSingle_genW_Ψ_top Cx _ ψk hv hs, hfield']

/-- At a datum site `u` within one cube of a site over the retained component `C`, `parentPsi ψ_k`
is the multiscale field of `ChiDomAt` at the top-scale block of `u`, with the output
configuration `outOf ψ_k`. -/
theorem parentPsi_eq_tested_local {C : H.Comp (j + 1)} (hret : C.1 ∉ H.rem (j + 1))
    {A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1))}
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))
    (xs : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A)
    {t u : BgT Cx.geo (j + 1)} (hu : u ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ))
    (hq : parentSiteCube Cx t ∈ C.1) (hd : supDist (parentSiteCube Cx u) (parentSiteCube Cx t) ≤ 1) :
    parentPsi Cx ψk u =
      fun i => subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
          (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) xs
          (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) (j + 1)
          (blkToBlock Cx.geo Cx.hnn Cx.hkK
            (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) u)) i := by
  have hΩ : parentSiteCube Cx u ∈ C.1 → parentSiteCube Cx u ∈ (H.step j).Omega := fun hqu =>
    (H.step j).OmegaDD_subset_Omega (datum_site_topBlock H Cx hret hu hqu).2.1
  obtain ⟨hV, hfield⟩ := subMultiscaleField_top_eq_out (R := R) H Cx.hkK C
    (x := bgToFine Cx.geo Cx.hnn Cx.hkK u) (mem_nbhd.mpr ⟨_, hq, hd⟩) hΩ
    (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) xs
  have e := jBlock_bgToFine Cx u
  have hV' : blkToBlock Cx.geo Cx.hnn Cx.hkK
      (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) u) ∈
      Vblk R (H.localHistory M K (j + 1) C) (j + 1) := e ▸ hV
  have hgen : ∀ (b : BlockAt S n M K (j + 1))
      (hb : b ∈ Vblk R (H.localHistory M K (j + 1) C) (j + 1)),
      jBlock S.d S.L (M * n K) K (j + 1) (bgToFine Cx.geo Cx.hnn Cx.hkK u) = b →
      subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
        (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) xs
        (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) (j + 1) b = ψk b := by
    intro b hb e'
    subst e'
    exact hfield
  have hfield' := hgen _ hV' e
  funext i
  rw [hfield']
  rfl

/-- **R2 over a retained component, local form.**  From `ChiDomAt` at `outOf ψ_k`, at a datum site
over `C` the field `parentPsi ψ_k` is within `3 d L δ_j` of the unit sphere. -/
theorem parentPsi_sphere_of_chiDomAt_local {C : H.Comp (j + 1)} (hret : C.1 ∉ H.rem (j + 1))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))
    {A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1))}
    {x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A}
    (hχ : ChiDomAt Cx.geo Cx.cs H (j + 1) C
      (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) x)
    {s : BgT Cx.geo (j + 1)} (hs : s ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ))
    (hq : parentSiteCube Cx s ∈ C.1) :
    |∑ i, parentPsi Cx ψk s i ^ 2 - 1| < 3 * S.d * S.L * Cx.cs.delta j := by
  have h1 := chiDomAt_site_sphere Cx Cx.cs hχ hret hs hq
  have e := parentPsi_eq_tested_local H Cx hret ψk x hs hq (by simp [supDist_self])
  have e' : ∀ i, parentPsi Cx ψk s i = _ := fun i => congrFun e i
  simp_rw [e']
  rw [parent_sum_sq_eq_norm_sq]
  exact h1

/-- **R1 over a retained component, local form.**  For an interface pair of `G_{j+1}` one of whose
sites `t` lies over `C`, the two values of `parentPsi ψ_k` are within `3 d L δ_j`, from
`ChiDomAt` at `outOf ψ_k`.  The site of the pair that is not over `C` is covered (it lies within
one cube of `t`, so its top block is tested too). -/
theorem parentPsi_pair_of_chiDomAt_local {C : H.Comp (j + 1)} (hret : C.1 ∉ H.rem (j + 1))
    (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N))
    {A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1))}
    {x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A}
    (hχ : ChiDomAt Cx.geo Cx.cs H (j + 1) C
      (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) x)
    {s s' t : BgT Cx.geo (j + 1)}
    (hp : IsInterfacePair (Cx.genW ((H.step (j + 1)).Z)ᶜ) s s') (hts : t = s ∨ t = s')
    (hq : parentSiteCube Cx t ∈ C.1) :
    rn (fun i => parentPsi Cx ψk s i - parentPsi Cx ψk s' i) <
      3 * S.d * S.L * Cx.cs.delta j := by
  have hcube := (interface_pair_topBlocks H Cx hret hp hts hq).1
  have hself : supDist (parentSiteCube Cx t) (parentSiteCube Cx t) ≤ 1 := by simp [supDist_self]
  have hds : supDist (parentSiteCube Cx s) (parentSiteCube Cx t) ≤ 1 := by
    rcases hts with rfl | rfl
    · exact hself
    · rw [supDist_comm]; exact hcube
  have hds' : supDist (parentSiteCube Cx s') (parentSiteCube Cx t) ≤ 1 := by
    rcases hts with rfl | rfl
    · exact hcube
    · exact hself
  have es := parentPsi_eq_tested_local H Cx hret ψk x hp.1 hq hds
  have es' := parentPsi_eq_tested_local H Cx hret ψk x hp.2.1 hq hds'
  obtain ⟨h1, -, -⟩ := chiDomAt_pair_bounds Cx Cx.cs hχ hret hp hts hq
  have e : (fun i => parentPsi Cx ψk s i - parentPsi Cx ψk s' i) =
      fun i => (subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
          (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) x
          (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) (j + 1)
          (blkToBlock Cx.geo Cx.hnn Cx.hkK
            (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s)) -
        subMultiscaleField N (H.localHistory M K (j + 1) C) (j + 1)
          (Vblk R (H.localHistory M K (j + 1) C) (j + 1)) x
          (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) (j + 1)
          (blkToBlock Cx.geo Cx.hnn Cx.hkK
            (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (j + 1))) (j + 1) (j + 1) s'))) i := by
    funext i
    rw [congrFun es i, congrFun es' i]
    rfl
  rw [e, rn_fun_eq_norm]
  exact h1

section Assembly

variable (ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))
  (ν ηY : ℝ)

/-- **The domain statement with the local active factor.**  `inPsiTilde_genW_of_factors` with
`hAct` replaced by `hActLoc`: for every retained component `C` over which a datum site lies,
`ChiDomAt` holds at the output configuration `outOf ψ_k` (the restriction of `ψ_k`) and some
internal configuration.  There is no field equality.  The other hypotheses are those of the
landed theorem (`hmass`, `hR2Y`, `hR1Y` named inputs; `hν`, `hunit`, `hηY` typing). -/
theorem inPsiTilde_genW_of_factors_local (hν : 0 ≤ ν) (hunit : ‖hv‖ = 1) (hηY : 0 < ηY)
    (hmass : 2 * ν * ((S.L : ℝ) ^ (j + 1)) ^ 2 < (max (3 * S.d * S.L * Cx.cs.delta j) ηY) ^ 2)
    (hActLoc : ∀ C : H.Comp (j + 1), C.1 ∉ H.rem (j + 1) →
      (∃ t ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ), parentSiteCube Cx t ∈ C.1) →
      ∃ (A : Set (InternalVars (H.localHistory M K (j + 1) C) (j + 1)))
        (x : SubCfg N (H.localHistory M K (j + 1) C) (j + 1) A),
        ChiDomAt Cx.geo Cx.cs H (j + 1) C
          (outOf R (H.localHistory M K (j + 1) C) (j + 1) ψk) x)
    (hR2Y : ∀ s ∈ dataSites (Cx.genW ((H.step (j + 1)).Z)ᶜ),
      parentSiteCube Cx s ∈ ((H.step (j + 1)).Z)ᶜ → |∑ i, parentPsi Cx ψk s i ^ 2 - 1| < ηY)
    (hR1Y : ∀ s s', IsInterfacePair (Cx.genW ((H.step (j + 1)).Z)ᶜ) s s' →
      parentSiteCube Cx s ∈ ((H.step (j + 1)).Z)ᶜ → parentSiteCube Cx s' ∈ ((H.step (j + 1)).Z)ᶜ →
      rn (fun i => parentPsi Cx ψk s i - parentPsi Cx ψk s' i) < ηY) :
    InPsiTilde (Cx.genW ((H.step (j + 1)).Z)ᶜ) ν (max (3 * S.d * S.L * Cx.cs.delta j) ηY)
      (parentPsi Cx ψk) (fun i => hv i) := by
  have hηC : 3 * S.d * S.L * Cx.cs.delta j ≤ max (3 * S.d * S.L * Cx.cs.delta j) ηY :=
    le_max_left _ _
  have hηYle : ηY ≤ max (3 * S.d * S.L * Cx.cs.delta j) ηY := le_max_right _ _
  have hη0 : 0 < max (3 * S.d * S.L * Cx.cs.delta j) ηY := lt_of_lt_of_le hηY hηYle
  have hsum : ∑ i, hv i ^ 2 = 1 := by rw [parent_sum_sq_eq_norm_sq, hunit]; norm_num
  refine ⟨parentPsi_layerConst Cx _ ψk, ?_, ?_, ?_, ?_⟩
  · intro x x' hp
    rcases interface_pair_cases H Cx x x' with ⟨t, hts, C, hC, hq⟩ | ⟨h1, h2⟩
    · obtain ⟨A, xs, hχ⟩ := hActLoc C hC
        ⟨t, by rcases hts with rfl | rfl; exacts [hp.1, hp.2.1], hq⟩
      exact (parentPsi_pair_of_chiDomAt_local H Cx hC ψk hχ hp hts hq).trans_le hηC
    · exact (hR1Y x x' hp h1 h2).trans_le hηYle
  · intro x hx
    rcases siteCube_dichotomy H Cx x with hY | ⟨C, hC, hq⟩
    · exact (hR2Y x hx hY).trans_le hηYle
    · obtain ⟨A, xs, hχ⟩ := hActLoc C hC ⟨x, hx, hq⟩
      exact (parentPsi_sphere_of_chiDomAt_local H Cx hC ψk hχ hx hq).trans_le hηC
  · intro x hx
    have hCS : (∑ i, parentPsi Cx ψk x i * hv i) ^ 2 ≤ ∑ i, parentPsi Cx ψk x i ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => parentPsi Cx ψk x i)
        (fun i => hv i)
      rwa [hsum, mul_one] at this
    have habs : |∑ i, parentPsi Cx ψk x i * hv i| ≤ rn (parentPsi Cx ψk x) :=
      Real.abs_le_sqrt hCS
    have hq : |(∑ i, parentPsi Cx ψk x i * hv i) / rn (parentPsi Cx ψk x)| ≤ 1 := by
      rcases (rn_nonneg (parentPsi Cx ψk x)).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · rw [abs_div, abs_of_pos hpos, div_le_one hpos]; exact habs
    have h2 : |1 - (∑ i, parentPsi Cx ψk x i * hv i) / rn (parentPsi Cx ψk x)| ≤ 2 := by
      obtain ⟨hq1, hq2⟩ := abs_le.1 hq
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hℓ : ((S.L : ℝ) ^ (Cx.genW ((H.step (j + 1)).Z)ᶜ).layerIndex x) ^ 2 ≤
        ((S.L : ℝ) ^ (j + 1)) ^ 2 := by
      have hL1 : (1 : ℝ) ≤ S.L := by
        have := NeZero.pos S.L
        exact_mod_cast this
      have := pow_le_pow_right₀ hL1 (layerIndex_le_k (Cx.genW ((H.step (j + 1)).Z)ᶜ) x)
      exact pow_le_pow_left₀ (by positivity) this 2
    have hnn : 0 ≤ ν * ((S.L : ℝ) ^ (Cx.genW ((H.step (j + 1)).Z)ᶜ).layerIndex x) ^ 2 := by
      positivity
    calc ν * ((S.L : ℝ) ^ (Cx.genW ((H.step (j + 1)).Z)ᶜ).layerIndex x) ^ 2 *
          |1 - (∑ i, parentPsi Cx ψk x i * hv i) / rn (parentPsi Cx ψk x)|
        ≤ ν * ((S.L : ℝ) ^ (Cx.genW ((H.step (j + 1)).Z)ᶜ).layerIndex x) ^ 2 * 2 :=
          mul_le_mul_of_nonneg_left h2 hnn
      _ ≤ ν * ((S.L : ℝ) ^ (j + 1)) ^ 2 * 2 := by
          have := mul_le_mul_of_nonneg_left hℓ hν
          linarith
      _ < _ := by linarith
  · simp only [hsum, sub_self, abs_zero, mul_zero]
    positivity

end Assembly

end Parent

end Balaban.LargeField
