/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeRRoots
public import Balaban.Localization.I5Inhabited

/-!
# `ℬ′` of the step `R`: the aggregate identity of the residual

The residual of the exponents of the old (`Y₁`) and the new (`Y₂`) small-field region at the
background fields of `𝔹_k(Y₁^{≈2})`, `𝔹_k(Y₂^{≈2})` (P7 (3.22)–(3.25)) is, up to the terms of the top
level `k` (which read only the data), the vacuum terms and `ℛ^{(k)}`, the sum over the final domains `Y`
of `ℬ′_Y = rBPrime` (the P3 coefficients `r4Fresh` of the decoupled extensions of the pair functionals
of the roots); `ℬ′_Y` depends on the data only through their agreement on `Y`, is bounded by
`Σ_r Eb_r e^{-κ₀ d^cov(X_r) - 2κ d̃^cov(Y)}` and is analytic on the data domain.

The connectedness of the thickened cubes at the admissible centres of `𝔹_k(W)` with holes is carried as
the single named open input `GenHatConnAdm` (see its docstring).

* `GenHatConnAdm`, `genHatConnAdm_of_hatConn`, `genHatConnAdm_nonempty`;
* `SFCtx.rootEb`, `SFCtx.rDataSet`, `SFCtx.rBPrime`;
* `SFCtx.rBPrime_aggregate`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.GsSpec Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

section Conn

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **OPEN geometric input: the thickened cubes are connected at the admissible centres, for every
region `X₁` and every family of marked cubes** (`HatConnAdm H X₁ 𝒞`), the hypothesis of the (AE2)
locality of the decoupled background fields (`decBgField_lab_local_adm`, through
`hdich_aux_adm`).  It is open for the transported small-field sets `genWC Y = castG 𝔹_k(Y^{≈2})`:
it fails for `k = 1` at a diagonal corner of `W = Y^{≈2}` (two cubes of `W` touching only at a
corner make `□̂_z ∩ Ω₁` nearest-neighbour disconnected at the level-1 centres there), while the
locality itself holds there (the local solver does not couple the nearest-neighbour components of
`□̂_z ∩ Ω₁`).  To be removed by the component-wise dichotomy (core of `hdich_aux_adm`). -/
def GenHatConnAdm (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) : Prop :=
  ∀ (X₁ : Finset (Localization.CTorus d L N₁ m₁ K)) (𝒞 : Finset (ℕ × Localization.CTorus d L N₁ m₁ K)), HatConnAdm H X₁ 𝒞

theorem genHatConnAdm_of_hatConn {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (h : HatConn H) :
    GenHatConnAdm H :=
  fun X₁ 𝒞 => h.hatConnAdm X₁ 𝒞

/-- `GenHatConnAdm` is inhabited (rule 10): the witness generating set of I-5. -/
theorem genHatConnAdm_nonempty (m₁ : ℕ) (ϱ : ℝ) : GenHatConnAdm (I5Inhabited.GP m₁ ϱ) :=
  genHatConnAdm_of_hatConn I5Inhabited.GP_hatConn

end Conn

namespace Def7.SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (Y₁ Y₂ : Set (Torus S.d (n k))) (hv : EuclideanSpace ℝ (Fin N))
  (vc : Def7v2.CorrCoef S.d) (g : GIdx S n M K N → ℂ)

/-- **The bound of the pair functional of a root**: the two cube bounds at `B` for a cube, the
polymer bound for a polymer. -/
noncomputable def rootEb (P : Def6.Consts) (B : ℝ) : C.RRoot → ℝ
  | Sum.inl c => C.cubeBound Y₁ hv vc g c B + C.cubeBound Y₂ hv vc g c B
  | Sum.inr ⟨j, X⟩ => 2 * ((C.alignedCount j X : ℝ) * P.E₀ +
      P.c₉ * ((S.L : ℝ) ^ j)⁻¹ ^ (((S.d : ℝ) - 2) / 2 + P.γ - P.α₁))

/-- The data domain of the residual: data near real data of both regions. -/
def rDataSet (ν δ τ : ℝ) : Set (BlockAt S n M K k → Fin N → ℂ) :=
  {u | C.RDataNear hv Y₁ ν δ τ u ∧ C.RDataNear hv Y₂ ν δ τ u}

theorem isOpen_rDataSet (ν δ τ : ℝ) : IsOpen (C.rDataSet Y₁ Y₂ hv ν δ τ) :=
  (C.isOpen_rDataNear hv Y₁ ν δ τ).inter (C.isOpen_rDataNear hv Y₂ ν δ τ)

/-- **`ℬ′_Y` of the step `R`**: the sum over the roots of the residual of the P3 coefficients of the
decoupled extensions of their pair functionals (`bPrime` at the whole-lattice set of the top level,
the labels `rootLabs`, the label map `topLab`, the self covers of the two transported sets). -/
noncomputable def rBPrime {Zt : Type*} (a₁ ν rho : ℝ) (Sz : Finset Zt)
    (Y : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) (u : BlockAt S n M K k → Fin N → ℂ) : ℂ := by
  classical
  exact bPrime C.rLevelGS C.m₀ C.rRoots (ι := C.rootIdx) (fun _ i => i.1) C.rootX₁
    (fun r (_ : Finset Zt) => pairExt (coverOf (C.genWC Y₁)) (coverOf (C.genWC Y₂)) (C.genWC Y₁)
      (C.genWC Y₂) (compWeight S.L a₁) ν rho topLab topLab (fun i => i.1) (C.dataWC Y₁ hv)
      (C.dataWC Y₂ hv) (C.rootPair Y₁ Y₂ hv vc g r)) Sz Y u

/-- **The pair functionals vanish at equal regions and equal fields.** -/
theorem rootPair_self (Y : Set (Torus S.d (n k))) (r : C.RRoot)
    (u : BlockAt S n M K k → Fin N → ℂ) (φ : (C.genWC Y).Ω 1 × Fin N → ℂ) :
    C.rootPair Y Y hv vc g r u φ φ = 0 := by
  rcases r with c | ⟨j, X⟩
  · exact sub_self _
  · exact sub_self _

/-- **`ℬ′` vanishes for no removed member** (the hypothesis `hfresh` of `gasR4Decor_eq`): when the
old and the new small-field regions coincide, the two decoupled fields coincide and every pair
functional vanishes. -/
theorem rBPrime_self {Zt : Type*} (Y : Set (Torus S.d (n k))) (a₁ ν rho : ℝ) (Sz : Finset Zt)
    (Y' : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) (u : BlockAt S n M K k → Fin N → ℂ) :
    C.rBPrime Y Y hv vc g a₁ ν rho Sz Y' u = 0 := by
  classical
  unfold rBPrime bPrime
  refine Finset.sum_eq_zero fun r _ => ?_
  refine r4Fresh_eq_zero_of_zero (G := C.rLevelGS) (m₀ := C.m₀) _ _ _ Sz Y' u fun w => ?_
  unfold pairExt
  exact C.rootPair_self hv vc g Y r u _

open Classical in
/-- The final domains of `ℬ′` of the step `R`. -/
noncomputable def rDomains : Finset (Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) :=
  bPrimeDomains C.rLevelGS C.m₀ C.rRoots (ι := C.rootIdx) (fun _ i => i.1) C.rootX₁

theorem cubeBound_nonneg {B : ℝ} (hB : 0 ≤ B) (c : Torus S.d (n k)) (Y : Set (Torus S.d (n k))) :
    0 ≤ C.cubeBound Y hv vc g c B := by
  unfold cubeBound
  refine add_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) (by positivity))
    (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun s _ => ?_))
    (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) hB)
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (sq_nonneg _))
    (mul_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _)
      (mul_nonneg (vn_nonneg _) (mul_nonneg (by norm_num) hB))))

theorem rootEb_nonneg (P : Def6.Consts) (hE₀ : 0 ≤ P.E₀) (hc₉ : 0 ≤ P.c₉) {B : ℝ} (hB : 0 ≤ B)
    (r : C.RRoot) : 0 ≤ C.rootEb Y₁ Y₂ hv vc g P B r := by
  rcases r with c | ⟨j, X⟩
  · exact add_nonneg (C.cubeBound_nonneg hv vc g hB c Y₁) (C.cubeBound_nonneg hv vc g hB c Y₂)
  · have h : 0 ≤ ((S.L : ℝ) ^ j)⁻¹ ^ (((S.d : ℝ) - 2) / 2 + P.γ - P.α₁) :=
      Real.rpow_nonneg (by positivity) _
    show 0 ≤ 2 * ((C.alignedCount j X : ℝ) * P.E₀ +
      P.c₉ * ((S.L : ℝ) ^ j)⁻¹ ^ (((S.d : ℝ) - 2) / 2 + P.γ - P.α₁))
    have : 0 ≤ (C.alignedCount j X : ℝ) * P.E₀ := mul_nonneg (Nat.cast_nonneg _) hE₀
    have : 0 ≤ P.c₉ * ((S.L : ℝ) ^ j)⁻¹ ^ (((S.d : ℝ) - 2) / 2 + P.γ - P.α₁) := mul_nonneg hc₉ h
    linarith

/-- **The aggregate identity of the residual of `R` (P7 (3.22)–(3.25), row (c))**: for data in the
data domain `Su` (near real data of `Ψ̃(genWC Yᵢ; δ)`, `h = hv`) and the background fields of
`𝔹_k(Yᵢ^{≈2})`,
1. the residual `sfExp2At(Y₁) - sfExp2At(Y₂)` is the sum over the final domains `Y` of
   `ℬ′_Y = rBPrime`, plus the terms of the top level `k` (which read only the data), minus the
   difference of the vacuum terms, plus the difference of `ℛ^{(k)}`;
2. `ℬ′_Y` depends on the data only through their agreement on `Y` (`pairAgree … dataAgree`);
3. `‖ℬ′_Y‖ ≤ Σ_r Eb_r e^{-κ₀ d^cov(X_r) - 2κ d̃^cov(Y)}`;
4. `ℬ′_Y` is analytic on `Su`.
The hypotheses are the step's typing ties, the class `IsSF2` strong clauses with its birth domain,
the settings of the two transported sets, the P3 constants, the source `‖g‖₁ < 1`, and the single
open geometric input `GenHatConnAdm` of the two transported sets. -/
theorem rBPrime_aggregate {Zt : Type*} (Sz : Finset Zt) (hk1 : 1 ≤ k) (hd : 3 ≤ S.d)
    (hL : 3 ≤ S.L) (hN : S.L ^ C.m₀ ∣ C.N₁) (hlt : hatScale S.L m₁ ϱ < C.m₀)
    (hsep : ϱ ≤ minSep S.L (S.L ^ (m₁ + hatScale S.L m₁ ϱ)))
    (hMm : C.geo.c * C.geo.M1 = S.L ^ (C.m₀ + m₁)) (hm : m₁ + hatScale S.L m₁ ϱ + 3 ≤ C.m₀ + m₁)
    {P : Def6.Consts} {Rg : Regime S.L} {a : ℕ → ℝ}
    (hT : GsSpec.SFTermClausesStrong P (birthXiDom P Rg a C.N₁) (C.sf.Tm C.N₁))
    (hm0 : P.m₀ = C.m₀) (hE₀ : 0 ≤ P.E₀) (hc₉ : 0 ≤ P.c₉)
    (hg : l1 (sfG C.geo C.hnn C.hkK C.hT g) < 1)
    {a₁ ν c₀ BG κ κ₀ κ₁ : ℝ} (hS : Dec2.DecSpecs S.d S.L (Dec2.selfKc S.d S.L) (Cchi S.d S.L) c₀ BG)
    (S₁ : DGSetting (C.genWC Y₁) (compWeight S.L a₁) ν)
    (S₂ : DGSetting (C.genWC Y₂) (compWeight S.L a₁) ν)
    (HB : BgHyp S.d S.L k (minSep S.L C.geo.M1) (compWeight S.L a₁) ν)
    (HBG : BgHyp S.d S.L k ϱ (compWeight S.L a₁) ν) (ha₁ : 0 < a₁)
    (hw : C.weights = compWeight S.L a₁) (hA : aIdeal S.L k (a k) = compWeight S.L a₁)
    (hμ : ∀ j, 1 ≤ j → j < k → physMass S.L j (Rg.ν j) = ν)
    (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκκ₁ : 4 * S.d * (((2 * S.L + 1) ^ S.d : ℕ) : ℝ) * κ ≤ κ₁) (h1 : 1 ≤ (κ₁ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * S.L + 1) ^ S.d : ℕ) : ℝ) *
      (((S.L ^ C.m₀) ^ S.d : ℕ) : ℝ)) ≤ (κ₁ / 2 - 1) / 2) (hκ₁ : 0 < κ₁)
    (hM : c₀ * Real.exp (N0 S.d S.L * κ₁) ≤ (S.L : ℝ) ^ m₁) (hκP : κ ≤ P.κ + 1)
    {δ τ : ℝ} (hδ0 : 0 < δ) (hτ0 : 0 ≤ τ) (hδ73 : δ ≤ thm73C1 S.d S.L N)
    (hδc : δ + 5 * τ ≤ c7 S.d S.L N BG κ₁)
    (hrad : decDomRad S.d S.L N BG κ₁ δ τ ≤ bgC1 S.d S.L N)
    (hε : ∀ j, 1 ≤ j → j < k →
      (2 * bgK1 S.d S.L N + 2) * decDomRad S.d S.L N BG κ₁ δ τ ≤ P.eps S.d S.L j)
    (hconn₁ : GenHatConnAdm (C.genWC Y₁)) (hconn₂ : GenHatConnAdm (C.genWC Y₂)) :
    (∀ u ∈ C.rDataSet Y₁ Y₂ hv ν δ τ,
      Def7v2.sfExp2At C vc Y₁ u hv g (castΩField C.coarseSide_eq (C.genW Y₁)
          (bgFieldC (C.genWC Y₁) (compWeight S.L a₁) ν (bgC0 S.d S.L N) (C.dataWC Y₁ hv u))) -
        Def7v2.sfExp2At C vc Y₂ u hv g (castΩField C.coarseSide_eq (C.genW Y₂)
          (bgFieldC (C.genWC Y₂) (compWeight S.L a₁) ν (bgC0 S.d S.L N) (C.dataWC Y₂ hv u))) =
      ∑ Y ∈ C.rDomains, C.rBPrime Y₁ Y₂ hv vc g a₁ ν (rho4 S.d S.L N BG κ₁) Sz Y u +
        ∑ X ∈ Def7v2.polyIdx C k, C.polyPair Y₁ Y₂ hv g k X u
          (bgFieldC (C.genWC Y₁) (compWeight S.L a₁) ν (bgC0 S.d S.L N) (C.dataWC Y₁ hv u))
          (bgFieldC (C.genWC Y₂) (compWeight S.L a₁) ν (bgC0 S.d S.L N) (C.dataWC Y₂ hv u)) -
        (((C.sf.E C.N₁ * volK M Y₁ : ℝ) : ℂ) - ((C.sf.E C.N₁ * volK M Y₂ : ℝ) : ℂ)) +
        (C.RresC Y₁ u hv g - C.RresC Y₂ u hv g)) ∧
    (∀ Y, ∀ u ∈ C.rDataSet Y₁ Y₂ hv ν δ τ, ∀ u' ∈ C.rDataSet Y₁ Y₂ hv ν δ τ,
      pairAgree (C.genWC Y₁) (C.genWC Y₂) (C.dataWC Y₁ hv) (C.dataWC Y₂ hv) C.dataAgree Y u u' →
      C.rBPrime Y₁ Y₂ hv vc g a₁ ν (rho4 S.d S.L N BG κ₁) Sz Y u =
        C.rBPrime Y₁ Y₂ hv vc g a₁ ν (rho4 S.d S.L N BG κ₁) Sz Y u') ∧
    (∀ Y, ∀ u ∈ C.rDataSet Y₁ Y₂ hv ν δ τ,
      ‖C.rBPrime Y₁ Y₂ hv vc g a₁ ν (rho4 S.d S.L N BG κ₁) Sz Y u‖ ≤
        ∑ r ∈ C.rRoots, C.rootEb Y₁ Y₂ hv vc g P (2 + nearCb S.d S.L N BG κ₁ δ τ + τ) r *
          Real.exp (-κ₀ * treeLenCovOne C.m₀ (C.rootLevel r) (C.rootX r) -
            2 * κ * treeLenCov C.rLevelGS C.m₀ Y)) ∧
    (∀ Y, AnalyticOnNhd ℂ (C.rBPrime Y₁ Y₂ hv vc g a₁ ν (rho4 S.d S.L N BG κ₁) Sz Y)
      (C.rDataSet Y₁ Y₂ hv ν δ τ)) := by
  classical
  have hd0 : 0 < S.d := by omega
  have hL2 : 2 ≤ S.L := by omega
  have hBG : 0 ≤ BG := hS.fam.2.1
  have hδc0 : 0 < δ + 5 * τ := by positivity
  have hsmall := small_of_c7 (L := S.L) (N := N) hd0 hBG hδ0 hτ0 hδc
  have hδ14 : δ ≤ 1 / 4 := by linarith
  have hτ1 : τ ≤ 1 := by linarith
  have hδc0' : δ + 5 * τ ≤ bgC0 S.d S.L N :=
    (c7_facts (L := S.L) (N := N) hd0 hBG hδc0.le hδc).1.trans (bgC1_le_bgC0 S.d S.L N hd0)
  have hνε : ν * ((S.L : ℝ) ^ k) ^ 2 * (δ + 5 * τ) ^ 2 ≤ (δ + 5 * τ) ^ 2 := by
    have := HB.massLe; nlinarith [sq_nonneg (δ + 5 * τ)]
  have hB0 : 0 ≤ 2 + nearCb S.d S.L N BG κ₁ δ τ + τ := by
    have := nearCb_nonneg (L := S.L) (N := N) hd0 hBG κ₁ hδ0.le hτ0; linarith
  have hG := C.isLevel_rLevelGS hk1
  -- the data of the two pairs on the data domain
  have hD₁ : ∀ u ∈ C.rDataSet Y₁ Y₂ hv ν δ τ,
      InDomainC (C.genWC Y₁) ν (δ + 5 * τ) (δ + 5 * τ) (C.dataWC Y₁ hv u) := fun u hu =>
    C.inDomainC_of_rDataNear hv Y₁ hδ0 hδ14 hτ0 hτ1 hu.1
  have hD₂ : ∀ u ∈ C.rDataSet Y₁ Y₂ hv ν δ τ,
      InDomainC (C.genWC Y₂) ν (δ + 5 * τ) (δ + 5 * τ) (C.dataWC Y₂ hv u) := fun u hu =>
    C.inDomainC_of_rDataNear hv Y₂ hδ0 hδ14 hτ0 hτ1 hu.2
  -- the polymer roots read the class terms in their domains
  have hdom : ∀ (Y : Set (Torus S.d (n k))) (SY : DGSetting (C.genWC Y) (compWeight S.L a₁) ν)
      {u : BlockAt S n M K k → Fin N → ℂ}, C.RDataNear hv Y ν δ τ u →
      ∀ {φ : (C.genWC Y).Ω 1 × Fin N → ℂ},
      NearApprox (C.genWC Y) (compWeight S.L a₁) ν (C.dataWC Y hv u)
        (cK2' S.d S.L N (famConst S.d S.L BG κ₁) * (lemma53Const S.d S.L * (δ + 5 * τ))) φ →
      ∀ {j : ℕ} {X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)}, 1 ≤ j → j ≤ k - 1 →
      IsPolyDom C.m₀ j X → X ⊆ C.sset (thickY R Y) →
      (birthXiDom P Rg a C.N₁).dom j ((C.sf.Tm C.N₁).gs j X)
        (C.psiJAt Y u hv (castΩField C.coarseSide_eq (C.genW Y) φ) j) (constFld (hC hv)) := by
    intro Y SY u hu φ hφ j X hj1 hj hpoly hX
    obtain ⟨Ψ₀, hP, hDu⟩ := hu
    have hpoly' : IsPolyDom P.m₀ j X := hm0 ▸ hpoly
    have hjk : j < k := by omega
    exact C.dom_psiJAt_of_near Y hv hj1 hjk hL hX hpoly hN
      (hT.gs_spec j hj1 hjk.le X hpoly').2 (hm0 ▸ hT.hat j hj1 hjk.le X hpoly') hlt hsep hMm hm hS SY
      HB HBG ha₁ hκ₁.le hM hδ0 hτ0 hδ73 hδc hrad hw hA (hμ j hj1 hjk) (hε j hj1 hjk) hP u
      (fun x hx => (hDu x hx).le) hφ
  -- the analyticity of the pair functionals
  have hΦan : ∀ r ∈ C.rRoots, ∀ u ∈ C.rDataSet Y₁ Y₂ hv ν δ τ, ∀ φ₁ φ₂,
      NearApprox (C.genWC Y₁) (compWeight S.L a₁) ν (C.dataWC Y₁ hv u)
        (cK2' S.d S.L N (famConst S.d S.L BG κ₁) * (lemma53Const S.d S.L * (δ + 5 * τ))) φ₁ →
      NearApprox (C.genWC Y₂) (compWeight S.L a₁) ν (C.dataWC Y₂ hv u)
        (cK2' S.d S.L N (famConst S.d S.L BG κ₁) * (lemma53Const S.d S.L * (δ + 5 * τ))) φ₂ →
      AnalyticAt ℂ (fun q : (BlockAt S n M K k → Fin N → ℂ) × ((C.genWC Y₁).Ω 1 × Fin N → ℂ) ×
        ((C.genWC Y₂).Ω 1 × Fin N → ℂ) => C.rootPair Y₁ Y₂ hv vc g r q.1 q.2.1 q.2.2)
        (u, φ₁, φ₂) := by
    intro r hr u hu φ₁ φ₂ hφ₁ hφ₂
    rcases r with c | ⟨j, X⟩
    · exact C.analyticAt_cubePair hv Y₁ Y₂ vc g c u φ₁ φ₂
        (C.cubeRoot_region Y₁ hv hk1 vc g c hT hm0 hL hN hlt hsep hMm hm hS S₁ HB HBG ha₁ hκ₁.le hM
          hδ0 hτ0 hδ73 hδc hrad hw hu.1 hφ₁).1
        (C.cubeRoot_region Y₂ hv hk1 vc g c hT hm0 hL hN hlt hsep hMm hm hS S₂ HB HBG ha₁ hκ₁.le hM
          hδ0 hτ0 hδ73 hδc hrad hw hu.2 hφ₂).1
    · obtain ⟨hj1, hj, hpoly⟩ := C.rRoots_inr hr
      exact C.analyticAt_polyPair Y₁ Y₂ hv g hT.toSFTermClauses hm0 hj1 (by omega) hpoly hg u φ₁ φ₂
        (hdom Y₁ S₁ hu.1 hφ₁ hj1 hj hpoly) (hdom Y₂ S₂ hu.2 hφ₂ hj1 hj hpoly)
  -- the bound of the pair functionals
  have hΦbd : ∀ r ∈ C.rRoots, ∀ u ∈ C.rDataSet Y₁ Y₂ hv ν δ τ, ∀ φ₁ φ₂,
      NearApprox (C.genWC Y₁) (compWeight S.L a₁) ν (C.dataWC Y₁ hv u)
        (cK2' S.d S.L N (famConst S.d S.L BG κ₁) * (lemma53Const S.d S.L * (δ + 5 * τ))) φ₁ →
      NearApprox (C.genWC Y₂) (compWeight S.L a₁) ν (C.dataWC Y₂ hv u)
        (cK2' S.d S.L N (famConst S.d S.L BG κ₁) * (lemma53Const S.d S.L * (δ + 5 * τ))) φ₂ →
      ‖C.rootPair Y₁ Y₂ hv vc g r u φ₁ φ₂‖ ≤
        C.rootEb Y₁ Y₂ hv vc g P (2 + nearCb S.d S.L N BG κ₁ δ τ + τ) r *
          Real.exp (-(κ - 1) * treeLenCovOne C.m₀ (C.rootLevel r) (C.rootX r)) := by
    intro r hr u hu φ₁ φ₂ hφ₁ hφ₂
    rcases r with c | ⟨j, X⟩
    · rw [C.treeLen_root_inl c, mul_zero, Real.exp_zero, mul_one]
      have b1 := (C.cubeRoot_region Y₁ hv hk1 vc g c hT hm0 hL hN hlt hsep hMm hm hS S₁ HB HBG ha₁
        hκ₁.le hM hδ0 hτ0 hδ73 hδc hrad hw hu.1 hφ₁).2
      have b2 := (C.cubeRoot_region Y₂ hv hk1 vc g c hT hm0 hL hN hlt hsep hMm hm hS S₂ HB HBG ha₁
        hκ₁.le hM hδ0 hτ0 hδ73 hδc hrad hw hu.2 hφ₂).2
      exact (norm_sub_le _ _).trans (add_le_add b1 b2)
    · obtain ⟨hj1, hj, hpoly⟩ := C.rRoots_inr hr
      have b := C.norm_polyPair_le Y₁ Y₂ hv g hT.toSFTermClauses hm0 hE₀ hc₉ hj1 (by omega) hpoly hg
        u φ₁ φ₂ (hdom Y₁ S₁ hu.1 hφ₁ hj1 hj hpoly) (hdom Y₂ S₂ hu.2 hφ₂ hj1 hj hpoly)
      refine b.trans (mul_le_mul_of_nonneg_left ?_
        (C.rootEb_nonneg Y₁ Y₂ hv vc g P hE₀ hc₉ hB0 (Sum.inr ⟨j, X⟩)))
      refine Real.exp_le_exp.2 ?_
      have ht : 0 ≤ treeLenCovOne C.m₀ j X := treeLenCovOne_nonneg _ _ _
      show -P.κ * sizeJ C.m₀ j X ≤ -(κ - 1) * treeLenCovOne C.m₀ j X
      unfold sizeJ
      nlinarith
  -- the locality of the pair functionals
  have hΦloc : ∀ r ∈ C.rRoots, ∀ u u' φ₁ φ₁' φ₂ φ₂',
      (∀ y : (C.genWC Y₁).Ω 1, (y : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ C.rootX₁f r →
        ∀ i, φ₁ (y, i) = φ₁' (y, i)) →
      (∀ y : (C.genWC Y₂).Ω 1, (y : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ C.rootX₁f r →
        ∀ i, φ₂ (y, i) = φ₂' (y, i)) →
      C.dataAgree ↑(C.rootX₁f r) u u' →
      C.rootPair Y₁ Y₂ hv vc g r u φ₁ φ₂ = C.rootPair Y₁ Y₂ hv vc g r u' φ₁' φ₂' := by
    intro r hr u u' φ₁ φ₁' φ₂ φ₂' h₁ h₂ hu
    rcases r with c | ⟨j, X⟩
    · exact C.cubePair_loc hv Y₁ Y₂ vc g c (C.cube_mem_rootX₁f hk1 hN hL2 hMm c)
        (C.cube_nbr_mem_rootX₁f hk1 hN hL2 hMm c) u u' φ₁ φ₁' φ₂ φ₂' h₁ h₂ hu
    · obtain ⟨hj1, hj, hpoly⟩ := C.rRoots_inr hr
      have hcov := C.covSetup_root hk1 hN hL2 hr
      have hXX : X ⊆ ↑(C.rootX₁f (Sum.inr ⟨j, X⟩)) := by
        rw [C.coe_rootX₁f]; exact hcov.X_sub
      exact C.polyPair_loc Y₁ Y₂ hv g hT.toSFTermClauses (j := j) (by omega) hXX
        (fun x hx y hy => by
          rw [← Finset.mem_coe, C.coe_rootX₁f] at hx ⊢
          exact C.mem_rootX₁_of_sameCell hN _ hx hy)
        u u' φ₁ φ₁' φ₂ φ₂' h₁ h₂ (C.liftAgree_of_dataAgree hv Y₁ Y₂ hu)
  -- the aggregate identity of the pairs
  obtain ⟨hsum, hloc, hbd, han⟩ := bPrime_pairs_aggregate_adm (G := C.rLevelGS) (m₀ := C.m₀)
    (Zt := Zt) hd hL hκ₀ hκ hκκ₁ h1 hlog hS S₁ S₂ HB HB hκ₁ hM (π₁ := topLab) (π₂ := topLab)
    (fun P hP x hx => mem_Pset_topLab ((mem_cubeIdx _).1 hP).1.2 hx)
    (fun P hP x hx => mem_Pset_topLab ((mem_cubeIdx _).1 hP).1.2 hx)
    (roots := C.rRoots) (ι := C.rootIdx) (lab := fun _ i => i.1) (j := C.rootLevel)
    (X := C.rootX) (𝒦X := C.rootFam) (X₁f := C.rootX₁f)
    (fun r hr => C.covSetup_root hk1 hN hL2 hr) (fun r hr => C.hopt_root hr)
    (fun r _ => C.coe_rootX₁f r) (fun r _ i => rootLabs_mem i)
    (fun r _ => Subtype.val_injective) (fun r _ i => rootLabs_disj i)
    (fun r _ => rootLabs_par hG hN (C.coe_rootX₁f r) (C.genWC Y₁))
    (fun r _ => rootLabs_par hG hN (C.coe_rootX₁f r) (C.genWC Y₂))
    (fun r _ Cf => hconn₁ _ _) (fun r _ Cf => hconn₂ _ _)
    (C.isOpen_rDataSet Y₁ Y₂ hv ν δ τ) (fun u _ => C.analyticAt_dataWC hv Y₁ u)
    (fun u _ => C.analyticAt_dataWC hv Y₂ u) hδc0 le_rfl hδc0' hδc hνε hD₁ hD₂
    (Φ := C.rootPair Y₁ Y₂ hv vc g)
    (Eb := C.rootEb Y₁ Y₂ hv vc g P (2 + nearCb S.d S.L N BG κ₁ δ τ + τ))
    (fun r _ => C.rootEb_nonneg Y₁ Y₂ hv vc g P hE₀ hc₉ hB0 r)
    hΦan hΦbd (AgΦ := C.dataAgree) (fun A u => C.dataAgree_refl A u)
    (fun A A' u u' hA' h => C.dataAgree_mono hA' h) hΦloc Sz
  refine ⟨fun u hu => ?_, fun Y u hu u' hu' h => hloc Y u hu u' hu' h, fun Y u hu => hbd Y u hu,
    fun Y => han Y⟩
  rw [C.sfExp2At_sub_eq_rootPair Y₁ Y₂ hv vc g hk1 u, hsum u hu]
  rfl

end Def7.SFCtx

end Balaban.LargeField
