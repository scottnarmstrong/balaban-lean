/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfConst
public import Balaban.Spine.FinalValue
public import Balaban.Fluctuation.CubeActionReal
public import Balaban.Fluctuation.Theorem42WireData

/-!
# The single-scale action on the whole torus is the Background-theory action

A6-3 (a), step (P1c). For the cut `Y = univ` the generating set `𝔹_k(W_k)` has the single layer
`Ω_1 = … = Ω_k = univ`, so the multiscale action `actionG` of `actStar2` (with the level generating
set) is the Background-theory action `actionC` of the lifted datum at the real background field:
`actStar2_univ_eq_actionC`.
-/

@[expose] public section

open Matrix Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2

namespace Balaban.RootFSpine

section Generic

variable {d L N₀ q : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- `actionG` depends on the generating set only through the sets `lam G n`, `1 ≤ n ≤ q`. -/
theorem actionG_congr_lam {G₁ : GeneratingSet d L N₀ q ϱ} {G₂ : GeneratingSet d L N₀ q ϱ'}
    (h : ∀ n, 1 ≤ n → n ≤ q → lam G₁ n = lam G₂ n) (a : ℕ → ℝ) (μ : ℝ) (v : E)
    (X : Finset (Site d L N₀ q)) (ψ : (m : ℕ) → Blk d L N₀ q m → E) (φ : Site d L N₀ q → E) :
    actionG G₁ a μ v X ψ φ = actionG G₂ a μ v X ψ φ := by
  unfold actionG
  have e : ∀ n ∈ Finset.Icc 1 q,
      ∑ y ∈ tBlocks d L N₀ q n (lam G₁ n ∩ X),
        a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2 =
      ∑ y ∈ tBlocks d L N₀ q n (lam G₂ n ∩ X),
        a n * (L : ℝ) ^ (n * (d - 2)) * ‖ψ n y - bavgL d L N₀ q n φ y‖ ^ 2 := fun n hn => by
    obtain ⟨hn1, hnq⟩ := Finset.mem_Icc.1 hn
    rw [h n hn1 hnq]
  rw [Finset.sum_congr rfl e]

/-- A generating set with `Ω_n = univ` for `1 ≤ n ≤ q` has the single layer `q`. -/
theorem lam_of_Ω_univ {G : GeneratingSet d L N₀ q ϱ} (hΩ : ∀ n, 1 ≤ n → n ≤ q → G.Ω n = Finset.univ)
    {n : ℕ} (hn1 : 1 ≤ n) (hnq : n ≤ q) :
    lam G n = if n = q then Finset.univ else ∅ := by
  unfold lam
  simp only [show n ≠ 0 from by omega, ↓reduceIte]
  ext x
  by_cases hnq' : n = q
  · subst hnq'
    simp [GeneratingSet.layer, hΩ n hn1 le_rfl, G.top]
  · have : n + 1 ≤ q := by omega
    simp [GeneratingSet.layer, hΩ n hn1 hnq, hΩ (n + 1) (by omega) this, hnq']

end Generic

section SecondVar

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The second variation** of the variational function at the constant configuration `e`, in the
direction `E`, for the action mass `ν'` and the background mass `ν`:
`A(E, 0) − ½ ⟨φ̇, Ṡ⟩ + ½ (ν' − ν) ⟨φ̇, φ̇⟩`, `Ṡ = source E`, `φ̇ = (H⁻¹ − Π) Ṡ`
(`value_quadratic_limit_mass`). -/
noncomputable def secondVariation (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν ν' : ℝ)
    (e : Fin N → ℝ) (E : BgData G N) : ℂ :=
  actionC G a ν ((bgZero G N).lineAt E 1) 0 -
    (1 / 2) * pair G ((liftOp N (dirichletOperator G a ν 0)⁻¹ -
      constrainedOp (dirichletOperator G a ν 0)⁻¹ (constVec G e)) *ᵥ source G a ν E)
      (source G a ν E) +
    (((ν' - ν : ℝ) : ℂ) / 2) * pair G ((liftOp N (dirichletOperator G a ν 0)⁻¹ -
      constrainedOp (dirichletOperator G a ν 0)⁻¹ (constVec G e)) *ᵥ source G a ν E)
      ((liftOp N (dirichletOperator G a ν 0)⁻¹ -
      constrainedOp (dirichletOperator G a ν 0)⁻¹ (constVec G e)) *ᵥ source G a ν E)

end SecondVar

section Ctx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)
  (ψk : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (hv : EuclideanSpace ℝ (Fin N))

/-- **`A*_k` on the whole torus is the Background-theory action** (`k ≥ 1`, `d ≥ 2`): the value
`actStar2 C univ` is the real action of the lifted datum at the real background `φ̄_k`. -/
theorem actStar2_univ_eq_actionC (hk : 1 ≤ k) (hd2 : 2 ≤ S.d) :
    ((actStar2 C Set.univ ψk hv : ℝ) : ℂ) =
      actionC (C.genW Set.univ) C.weights (sfActMass2 C.cs k)
        (liftSingle (C.genW Set.univ) (C.liftData ψk) (hC hv))
        (Fluctuation.toFieldC (C.genW Set.univ) (C.phiBar Set.univ ψk hv)) := by
  classical
  have hb : C.bgSet (Set.univ : Set (Torus S.d (n k))) = Finset.univ := by
    ext x; simp [SFCtx.bgSet]
  have hΩ : ∀ m, 1 ≤ m → m ≤ k → (C.genW (Set.univ : Set (Torus S.d (n k)))).Ω m = Finset.univ :=
    fun m _ hmk => genW_Ω_univ_of_le C hmk
  have hlam : ∀ m, 1 ≤ m → m ≤ k → lam (C.genW (Set.univ : Set (Torus S.d (n k)))) m =
      lam (levelGen (d := S.d) (L := S.L) (N₀ := C.geo.M1 * (C.geo.c * n k)) (ϱ := (1 : ℝ)) k) m := by
    intro m hm1 hmk
    rw [lam_of_Ω_univ hΩ hm1 hmk]
    unfold lam
    simp only [show m ≠ 0 from by omega, ↓reduceIte]
    ext x
    by_cases h : m = k
    · subst h; simp [GeneratingSet.layer, levelGen]
    · have : m + 1 ≤ k := by omega
      simp [GeneratingSet.layer, levelGen, hmk, this, h]
  rw [← Fluctuation.cubeActionStar_univ]
  have hmem : ∀ x : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ k),
      x ∈ (C.genW (Set.univ : Set (Torus S.d (n k)))).Ω 1 := fun x => by
    rw [genW_Ω_univ C hk]; exact Finset.mem_univ x
  rw [Fluctuation.cubeActionStar_eq_actionG (G := C.genW Set.univ) hd2 Finset.univ
    (fun x _ => hmem x) (fun _ _ _ x _ _ y _ => Finset.mem_univ y) _ _ _ (C.psiLevelK ψk) hv
    (fun x hx => absurd (hmem x) hx) ?_ ?_]
  · unfold actStar2
    rw [hb]
    have e := actionG_congr_lam (G₁ := levelGen (d := S.d) (L := S.L)
      (N₀ := C.geo.M1 * (C.geo.c * n k)) (ϱ := (1 : ℝ)) k) (G₂ := C.genW Set.univ)
      (fun m h1 h2 => (hlam m h1 h2).symm) C.weights (sfActMass2 C.cs k) hv Finset.univ
      (C.psiLevelK ψk) (C.phiBar Set.univ ψk hv)
    rw [e]
  · intro m hm1 hmk x hx i
    have hxd : x ∈ dataSites (C.genW (Set.univ : Set (Torus S.d (n k)))) :=
      (mem_dataSites _).2 (Or.inl (hmem x))
    have hmk' : m = k := by
      by_contra hne
      have h1 : x ∈ (C.genW (Set.univ : Set (Torus S.d (n k)))).Ω m := ((C.genW (Set.univ : Set (Torus S.d (n k)))).mem_layer.1 hx).1
      have h2 := ((C.genW (Set.univ : Set (Torus S.d (n k)))).mem_layer.1 hx).2
      rw [hΩ (m + 1) (by omega) (by omega)] at h2
      exact h2 (Finset.mem_univ x)
    subst hmk'
    rw [liftSingle_Ψ _ _ _ hxd]
    simp [SFCtx.liftData, SFCtx.psiLevelK, singleScale, BlockCfg.toC, blockCfgOf, blkMap, jBlock]
  · intro x _ i
    rw [liftSingle_h _ _ _ (hmem x)]
    rfl

/-- The tangent datum of a block field `u`: the lift of `u` with `h̃ = 0`. -/
noncomputable def tangentDatum
    (u : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) : BgData (C.genW Set.univ) N :=
  liftSingle (C.genW Set.univ) (blockCfgOf C.geo C.hnn le_rfl C.hkK u).toC 0

/-- **The lifted datum of `ψ_k = h + t u` is the line from the constant datum** (`Y = univ`). -/
theorem liftSingle_line (hk : 1 ≤ k) (u : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) (t : ℝ) :
    liftSingle (C.genW Set.univ) (C.liftData (fun z => hv + t • u z)) (hC hv) =
      (constUnitBg (C.genW Set.univ) (fun i => hv i)).lineAt (tangentDatum C u) (t : ℂ) := by
  have hmem : ∀ x : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ k),
      x ∈ (C.genW (Set.univ : Set (Torus S.d (n k)))).Ω 1 := fun x => by
    rw [genW_Ω_univ C hk]; exact Finset.mem_univ x
  have hd : ∀ x : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ k),
      x ∈ dataSites (C.genW (Set.univ : Set (Torus S.d (n k)))) := fun x =>
    (mem_dataSites _).2 (Or.inl (hmem x))
  refine bgData_ext ?_ ?_
  · funext x i
    simp [BgData.lineAt, tangentDatum, liftSingle_Ψ _ _ _ (hd x), constUnitBg_Ψ (hd x),
      SFCtx.liftData, BlockCfg.toC, blockCfgOf]
  · funext x i
    simp [BgData.lineAt, tangentDatum, liftSingle_h _ _ _ (hmem x), constUnitBg_h (hmem x), hC]

theorem tangentDatum_isReal (u : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    (tangentDatum C u).IsReal := by
  intro x i
  by_cases hx : x ∈ dataSites (C.genW (Set.univ : Set (Torus S.d (n k))))
  · by_cases hx' : x ∈ (C.genW (Set.univ : Set (Torus S.d (n k)))).Ω 1
    · simp [tangentDatum, liftSingle, BgData.clip, hx, blockLift, BlockCfg.toC]
    · simp [tangentDatum, liftSingle, BgData.clip, hx, blockLift, BlockCfg.toC]
  · have : x ∉ (C.genW (Set.univ : Set (Torus S.d (n k)))).Ω 1 := fun h =>
      hx ((mem_dataSites _).2 (Or.inl h))
    simp [tangentDatum, liftSingle, BgData.clip, hx]

/-- **`φ̄_k` is the real background field**: on the whole torus, when the complex background of the
lifted datum is real. -/
theorem toFieldC_phiBar_eq
    (hreal : ∀ p, (bgFieldC (C.genW (Set.univ : Set (Torus S.d (n k)))) C.weights (C.cs.muBg k)
      (bgC0 S.d S.L N) (liftSingle (C.genW Set.univ) (C.liftData ψk) (hC hv)) p).im = 0) :
    Fluctuation.toFieldC (C.genW Set.univ) (C.phiBar Set.univ ψk hv) =
      bgFieldC (C.genW (Set.univ : Set (Torus S.d (n k)))) C.weights (C.cs.muBg k)
        (bgC0 S.d S.L N) (liftSingle (C.genW Set.univ) (C.liftData ψk) (hC hv)) := by
  funext ⟨x, i⟩
  have hx : (x : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ k)) ∈
      (C.genW (Set.univ : Set (Torus S.d (n k)))).Ω 1 := x.2
  have h := hreal (x, i)
  apply Complex.ext
  · simp [Fluctuation.toFieldC, SFCtx.phiBar, SFCtx.phiK, bgSF, barField, hx]
  · simpa [Fluctuation.toFieldC] using h.symm

/-- **The second variation of `A*_k(univ; ·)` at the constant configuration** (A6-3 (a), P1c):
along `ψ_k = h + t u` with `|h| = 1`, `actStar2 C univ ψ_t h / t²` tends to the real part of
`secondVariation`. -/
theorem actStar2_univ_second_variation
    (H : BgHyp S.d S.L k (minSep S.L C.geo.M1) C.weights (C.cs.muBg k))
    (he : ∑ i, hv i ^ 2 = 1) (hk : 1 ≤ k) (hd2 : 2 ≤ S.d)
    (u : BlockAt S n M K k → EuclideanSpace ℝ (Fin N)) :
    Filter.Tendsto (fun t : ℝ => actStar2 C Set.univ (fun z => hv + t • u z) hv / t ^ 2)
      (nhdsWithin 0 {0}ᶜ)
      (nhds (secondVariation (C.genW Set.univ) C.weights (C.cs.muBg k) (sfActMass2 C.cs k)
        (fun i => hv i) (tangentDatum C u)).re) := by
  classical
  set G := C.genW (Set.univ : Set (Torus S.d (n k))) with hG
  have hmem : ∀ x : Torus S.d (C.geo.M1 * (C.geo.c * n k) * S.L ^ k), x ∈ G.Ω 1 := fun x => by
    rw [hG, genW_Ω_univ C hk]; exact Finset.mem_univ x
  have hE : ∀ x, x ∉ G.Ω 1 → (tangentDatum C u).Ψ x = 0 := fun x hx => absurd (hmem x) hx
  have hEh : ∀ x, (tangentDatum C u).h x = 0 := fun x => by
    simp [tangentDatum, liftSingle, BgData.clip]
  have hlimC := value_quadratic_limit_mass (tangentDatum C u) hE hEh H
    (e := fun i => hv i) he (sfActMass2 C.cs k)
  have hof : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) :=
    tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto' 0 0 Complex.ofReal_zero).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun t ht => Complex.ofReal_ne_zero.2 ht⟩
  have hre := (Complex.continuous_re.tendsto _).comp (hlimC.comp hof)
  refine hre.congr' ?_
  -- the data lie in the domain for small real `t`
  have hD0 := constUnitBg_inUnionDomainC (G := G) (a := C.weights) (ν := C.cs.muBg k) H
    (e := fun i => hv i) he
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hD0
  have hevC := eventually_inDomainC_lineAt hDC (tangentDatum C u)
  have hevR : ∀ᶠ t : ℝ in nhdsWithin 0 {0}ᶜ, InDomainC G (C.cs.muBg k) δ ε
      ((constUnitBg G (fun i => hv i)).lineAt (tangentDatum C u) (t : ℂ)) :=
    (hof.mono_right nhdsWithin_le_nhds).eventually hevC
  filter_upwards [hevR, self_mem_nhdsWithin] with t ht ht0
  have ht0' : t ≠ 0 := ht0
  have hD1 : InUnionDomainC G (bgC0 S.d S.L N) (bgC1 S.d S.L N) (C.cs.muBg k)
      ((constUnitBg G (fun i => hv i)).lineAt (tangentDatum C u) (t : ℂ)) :=
    ⟨δ, ε, hδ0, hδε, hε, hδc.trans (bgC2_le_bgC1 S.d S.L N), hνε, ht⟩
  have hreal : ((constUnitBg G (fun i => hv i)).lineAt (tangentDatum C u) (t : ℂ)).IsReal :=
    isReal_lineAt (constUnitBg_isReal _) (tangentDatum_isReal C u) t
  have him := Fluctuation.bgFieldC_im_zero H hD1 hreal
  rw [← liftSingle_line C hv hk u t] at him
  have hbr := actStar2_univ_eq_actionC C (fun z => hv + t • u z) hv hk hd2
  rw [toFieldC_phiBar_eq C _ hv him, liftSingle_line C hv hk u t] at hbr
  simp only [Function.comp]
  rw [← hbr, ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]

end Ctx

end Balaban.RootFSpine
