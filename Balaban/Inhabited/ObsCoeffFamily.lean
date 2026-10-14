/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.ObsCoeffAnalytic
public import Balaban.Inhabited.Thm31bPolymerSupport
public import Balaban.Fluctuation.GsumActiveParam
public import Balaban.Fluctuation.ObsRowCoeff
public import Balaban.Fluctuation.ObsRowLabels
public import Balaban.Fluctuation.RootActiveSize
public import Balaban.Fluctuation.Thm31bFirst
public import Balaban.Polymer.MarkedCubesVanish

/-!
# The coefficient family of the observable at the tower

* `obsCoeffParam_support_of_Ev`: the coefficient `obsCoeffParam` of the observable vanishes unless
  the finite set of cubes contains the root cube of the observable site and its sites form a
  polymer domain.
* `obsCoeffParam_bound_of_Ev`: the sum bound `(B₁ + B₂) e^{-λ dExt T'}` on the parameter set.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer MeasureTheory Metric Balaban.Multiscale
  Balaban.Background Balaban.SmallField Balaban.SmallField.Def6

section Generic

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

local notation "𝔅" => CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ

/-- A first-order term vanishes on a set of cubes with `dOmega = ⊤`. -/
theorem markIntTerm_eq_zero_of_dOmega_top {Lb : Type*} [Fintype Lb] {Ωb : 𝔅 → Type*}
    [∀ b, MeasurableSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (hN : L ^ m₀ ∣ N₁) {Lab : CubeLabels m₀ K Set.univ Lb} {εH κH κ0 Kc : ℝ}
    (A : ℂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : Lb) (G : (∀ b, Ωb b) → ℂ) (S : Finset 𝔅)
    (hS : dOmega m₀ K Set.univ (sitesOf S) = ⊤) : markIntTerm μ A y0 G S = 0 := by
  unfold markIntTerm
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (0 : ℂ)) (fun s _ =>
    Gst_eq_zero_of_dOmega_top μ hN le_rfl isPiUnion_univ_K Lab (A (s : ℂ) 1).H y0 G S hS)]
  simp

/-- If every nonzero `h i T` contains the cube `bx`, so does the support of the resummed sum. -/
theorem mem_of_kernelMarkSum_ne_zero {ι : Type*} [Fintype ι] (h E : ι → Finset 𝔅 → ℂ) (bx : 𝔅)
    (hh : ∀ i T, h i T ≠ 0 → bx ∈ T) {W : Finset 𝔅} (hW : kernelMarkSum h E W ≠ 0) : bx ∈ W := by
  classical
  unfold kernelMarkSum at hW
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hW
  obtain ⟨T, -, hT⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  obtain ⟨S, -, hS⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
  split_ifs at hS with hTS
  · rw [← hTS]
    exact Finset.mem_union_left _ (hh i T (left_ne_zero_of_mul hS))
  · exact absurd rfl hS

/-- The label of a domain of `𝒟_K` has `dOmega ≠ ⊤`. -/
theorem dOmega_ne_top_obsRowLabel (hN : L ^ m₀ ∣ N₁) {Y : Set (CTorus d L N₁ m₁ K)}
    (hY : IsDj m₀ K Y) : dOmega m₀ K Set.univ (sitesOf (obsRowLabel m₀ K Y)) ≠ ⊤ := by
  have hs := sitesOf_obsRowLabel hN hY
  have hle : dOmega m₀ K Set.univ (sitesOf (obsRowLabel m₀ K Y)) ≤
      ENNReal.ofReal (treeLenCovOne m₀ K Y) := by
    rw [hs]
    simpa using G4_dOmega_le (Ω := Set.univ) hY (by simpa using hY.1)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

end Generic

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

section TowerG

variable {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
  (ν β p₁ : ℝ) (Dsc : StepScaleDataG T k hk N₁ ν β p₁)
  {ϱ : ℝ} (S : StepSetting d L N₁ T.m₁ k N ϱ) (hS : S = hatStepKG T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
  (hp : 0 < S.p₁) (y : CTorus d L N₁ T.m₁ (k + 1)) (h3N : L ^ T.m₀ ∣ N₁)
  {Lb : Type} [Fintype Lb]
  (Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
    Set.univ Lb) {εH : ℝ} (hεH : 0 < εH) {Kc : ℝ}
  (Aact : physParam N S → ℂ → LabelAct Lab (S.blockSplit T.m₀ hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc)
  (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y), IsDj T.m₀ (k + 1) Y)
  {Kobs : ℝ} (hK : Kc + Kc + K0 d L T.κ0 + K0 d L T.κ0 ≤ Kobs) (Rg : ℝ) (hR : 0 ≤ Rg)

include Dsc hS in
/-- General tower `T : StepTowerG d L N κmin` (block scale `T.m₀`, `b = β L^{k (d-2)}`); the landed theorem `obsCoeffParam_support_of_Ev` is its `ρ = 1` corollary.  **Support of the coefficient of the observable.**  For `θ` in the parameter set, if
`obsCoeffParam … θ T' ≠ 0` then the root cube of the observable site lies in `T'` and the sites of
`T'` form a polymer domain.  The kernel at `θ` is the kernel of the row coefficients at a datum
`D` with `rawOf D = θ.1`; its nonzero values sit on labels of domains of `𝒟_{k+1}`, which are
polymer site sets, and contain the root cube; the first-order terms vanish unless their cube lies in
the set and `dOmega` is finite; the remainder vanishes off polymer sets and contains the root cube
in every label. -/
theorem obsCoeffParam_support_of_EvG_rho {ρ q : ℝ} (hRg : 1 < Rg) (hKc : K0 d L T.κ0 + 1 ≤ Kc)
    (hε : Rg * max (εH + εH) εH ≤ stepTheta d L Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
        RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))}))
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y))
    (hD : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S T.m₀ hp Ev D (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))))
          (2 * T.κdec) (rootCube (m₀ := T.m₀) (blockIndex y)))
    (θ : physParam N S) (hθ : θ ∈ physVqRho S S.a₁ S.ν T.t ρ q)
    (T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
      Set.univ)) :
    obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T' ≠ 0 →
    rootCube (m₀ := T.m₀) (blockIndex y) ∈ T' ∧ IsPolyDom T.m₀ (k + 1) (sitesOf T') := by
  subst hS
  intro hne
  have hcψ := Dsc.cψ_pos
  have hC0 := cK2'_famConst_mul_t_posG T
  have hq : p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) ≤ 1 / 4 := by
    rw [div_le_iff₀ hcψ]
    have : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁ * p₁ := mul_pos Dsc.r_pos hp
    nlinarith [Dsc.ray_margin]
  have hN3 : L ^ T.m₀ ∣ N₁ := by simpa using h3N
  have hK0 := T.marks_K0_pos
  have hKobs : K0 d L T.κ0 + 1 ≤ Kobs := by linarith
  have hεpos : 0 < Rg * max (εH + εH) εH :=
    mul_pos (by linarith) (lt_of_lt_of_le (by linarith) (le_max_left _ _))
  have hε' : Rg * max (εH + εH) εH ≤ 1 / (8 * Kobs ^ 3 * c1 d L *
      Real.exp ((2 * T.κdec - 1 - 2 * T.κ0) * cG d L + c1 d L + T.κ' * cG d L)) := by
    unfold stepTheta at hε; exact hε
  have hdl0 : ∀ m : ObsMarkIdx (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ),
      (obsLab (Lab.sum Lab) hdj).dl (obsY1 T.m₀ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (Lb ⊕ Lb)
        (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
        = 0 := fun m => obsCubeLab_dl T.m₀ _
  have hcell : ∀ m : ObsMarkIdx (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ),
      obsMarkCube (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ m ∈ blocksOf (d := d) (L := L) (N₁ := N₁)
        (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1) Set.univ ((obsLab (Lab.sum Lab) hdj).ysite
          (obsY1 T.m₀ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (Lb ⊕ Lb) (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
            (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)) :=
    fun m => obsCubeLab_mem T.m₀ (obsMarkCube (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ m)
  obtain ⟨D, hDx, hDr⟩ := hθ.1.1
  have hDr' : (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N) = rawOf D := hDr
  have hker : ∀ (m : ObsMarkIdx (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) T'',
      obsHker (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
          (LocalCover.fam T.m₀ y)) (fun Y => hatCoeff (Ev Y)
            (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
            (obsUnitVec (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) m)) T.m₀ T'' =
        obsHker (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
          (LocalCover.fam T.m₀ y)) (obsRowCoeff (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) Ev D m) T.m₀ T'' := by
    intro m T''
    rw [hDr']; rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, hsp, hroot, hrem⟩ := hD D hDx
  have hlab := hrem.2.2.2.2.2.1
  -- the kernel
  have hkerN : ∀ m (T'' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁)
      (K := k + 1) T.m₀ (k + 1) Set.univ)),
      obsHker (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
          (LocalCover.fam T.m₀ y)) (fun Y => hatCoeff (Ev Y)
            (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
            (obsUnitVec (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) m)) T.m₀ T'' ≠ 0 →
        rootCube (m₀ := T.m₀) (blockIndex y) ∈ T'' ∧ obsMarkCube (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ m ∈ T'' ∧
        dOmega T.m₀ (k + 1) Set.univ (sitesOf T'') ≠ ⊤ := by
    intro m T'' h
    rw [hker m T''] at h
    refine ⟨by_contra fun hb => h (hroot m T'' hb), by_contra fun hb => h (hsp m T'' hb), ?_⟩
    obtain ⟨Y, hY, hYl, -⟩ := exists_of_obsHker_ne_zero h
    rw [← hYl]
    exact dOmega_ne_top_obsRowLabel hN3 (hdj Y hY)
  -- the first-order terms
  have hE : ∀ (m : ObsMarkIdx (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) (S' : Finset (CubeB (d := d) (L := L)
      (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1) Set.univ)),
      markIntTerm ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit T.m₀ hp).μ
        (fun t σ => tiltActObs Aact hN3 T.κ0_ent hεH.le hdj hK Rg hR
          (ball (0 : ℂ) (3 / 2)) θ t σ)
        (obsY1 T.m₀ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (Lb ⊕ Lb) (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
          (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
        (blockMarkC (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp m.1 m.2) S' ≠ 0 →
      obsMarkCube (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ m ∈ S' ∧ dOmega T.m₀ (k + 1) Set.univ (sitesOf S') ≠ ⊤ := by
    intro m S' h
    refine ⟨?_, fun ht => h (markIntTerm_eq_zero_of_dOmega_top _ hN3 _ _ _ S' ht)⟩
    by_contra hb
    exact h (markIntTerm_support
      ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit T.m₀ hp).μ hN3 (le_refl (k + 1)) isPiUnion_univ_K
      (fun t σ => tiltActObs Aact hN3 T.κ0_ent hεH.le hdj hK Rg hR
        (ball (0 : ℂ) (3 / 2)) θ t σ)
      (obsY1 T.m₀ (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (Lb ⊕ Lb) (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
        (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y)) m)
      (blockMarkC (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp m.1 m.2)
      (measurable_blockMarkC m.1 m.2) (depOn_blockMarkC m.1 m.2 (hcell m))
      (fun Φ => by rw [hdl0 m]; simpa using norm_blockMarkC_le m.1 m.2 Φ)
      T.marks_hκ0 (by linarith) hεpos hp T.marks_hκ' T.marks_hκG T.marks_hκ hε' S'
      (fun hsub => hb (hsub (hcell m))))
  -- the remainder
  have hgs := fun {W : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1) Set.univ)} (h : gsumCoeff ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit T.m₀ hp).μ
        (obsLab (Lab.sum Lab) hdj)
        (fun t => tiltActObs Aact hN3 T.κ0_ent hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) θ t 1)
        (obsRemLab (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
            (LocalCover.fam T.m₀ y)) (fun Y => Sum.inl (Sum.inr Y))
          (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) (LocalCover.nbhdF T.m₀ y) T.m₀ k
            (LocalCover.fam T.m₀ y)) (rootCube (m₀ := T.m₀) (blockIndex y))))
        (obsGrFam (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp Ev (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
          (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (XiCRaw (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' (compWeight L 1) ν (k + 1) 1 T.t) θ) W ≠ 0) =>
    mem_of_gsumCoeff_ne_zero_of_labels hN3
      ((hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).blockSplit T.m₀ hp).μ
      (Lab := obsLab (Lab.sum Lab) hdj) (κG := 2 * T.κdec - 1) (κ' := T.κ')
      (F0 := fun _ => 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
        (p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2)
      (fun t => tiltActObs Aact hN3 T.κ0_ent hεH.le hdj hK Rg hR (ball (0 : ℂ) (3 / 2)) θ t 1)
      _ (obsGrFam (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ hp Ev (obsDomains (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)
          (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (XiCRaw (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ).G' (compWeight L 1) ν (k + 1) 1 T.t) θ)
      (fun i u => measurable_obsGrFam hcψ hq (fun Y _ => ha Y) θ i u)
      (fun i u => depOn_obsGrFam_all (hp := hp) hN3 hcψ hq hdj (fun Y _ => hd Y) _
        (fun Y => Sum.inl (Sum.inr Y)) _ (fun Y => rfl) θ i u)
      (fun i u Φ => norm_obsGrFam_le hcψ hq (fun Y _ => ha Y) hC0 (fun Y _ => hb Y) _
        (fun Y => Sum.inl (Sum.inr Y)) _ (fun Y => rfl) T.marks_κG_le θ i u Φ)
      T.marks_hκ0 (by linarith) hεpos (fun _ => by positivity) T.marks_hκ' T.marks_hκG
      T.marks_hκ hε' hlab h
  unfold obsCoeffParam at hne
  have hpoly : IsPolyDom T.m₀ (k + 1) (sitesOf T') := by
    by_contra hP
    have htop := dOmega_top_of_not_isPolyDom hP
    apply hne
    rw [kernelMarkSum_eq_zero_of_dOmega_top _ _
      (fun m => obsMarkCube (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) T.m₀ m)
      (fun m T'' h => ⟨(hkerN m T'' h).2.1, (hkerN m T'' h).2.2⟩)
      (fun m S' h => hE m S' h) T' htop,
      gsumCoeff_eq_zero_of_dOmega_top hN3 _ _ _ _ _ htop, add_zero]
  refine ⟨?_, hpoly⟩
  by_contra hroot
  apply hne
  refine (congrArg₂ (· + ·) (not_not.1 fun h => hroot ?_) (not_not.1 fun h => hroot ?_)).trans
    (add_zero 0)
  · exact mem_of_kernelMarkSum_ne_zero _ _ _ (fun i T h => (hkerN i T h).1) h
  · exact hgs h


include Dsc hS in
/-- General tower `T : StepTowerG d L N κmin` (block scale `T.m₀`, `b = β L^{k (d-2)}`); the fixed theorem `obsCoeffParam_support_of_Ev` is its corollary.  **Support of the coefficient of the observable.**  For `θ` in the parameter set, if
`obsCoeffParam … θ T' ≠ 0` then the root cube of the observable site lies in `T'` and the sites of
`T'` form a polymer domain.  The kernel at `θ` is the kernel of the row coefficients at a datum
`D` with `rawOf D = θ.1`; its nonzero values sit on labels of domains of `𝒟_{k+1}`, which are
polymer site sets, and contain the root cube; the first-order terms vanish unless their cube lies in
the set and `dOmega` is finite; the remainder vanishes off polymer sets and contains the root cube
in every label. -/
theorem obsCoeffParam_support_of_EvG {q : ℝ} (hRg : 1 < Rg) (hKc : K0 d L T.κ0 + 1 ≤ Kc)
    (hε : Rg * max (εH + εH) εH ≤ stepTheta d L Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
        RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))}))
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y))
    (hD : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S T.m₀ hp Ev D (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))))
          (2 * T.κdec) (rootCube (m₀ := T.m₀) (blockIndex y)))
    (θ : physParam N S) (hθ : θ ∈ physVq S S.a₁ S.ν T.t q)
    (T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
      Set.univ)) :
    obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T' ≠ 0 →
    rootCube (m₀ := T.m₀) (blockIndex y) ∈ T' ∧ IsPolyDom T.m₀ (k + 1) (sitesOf T') :=
  obsCoeffParam_support_of_EvG_rho (ρ := 1) T k hk N₁ ν β p₁ Dsc S hS hp y h3N Lab hεH Aact hdj hK Rg hR hRg hKc hε Ev ha hd hb hD θ hθ T'

include Dsc hS in
/-- General tower `T : StepTowerG d L N κmin` (block scale `T.m₀`, `b = β L^{k (d-2)}`); the landed theorem `obsCoeffParam_bound_of_Ev` is its `ρ = 1` corollary.  **The sum bound of the coefficient of the observable.**  On the parameter set, with
`C₀ = Q t`, `c_ψ = lvCpsi`, `κ' = T.κ'`, `n_* = 2 · 3^{3(1+m₁+1)}`,
`B₁ = (C₀/c_ψ) (C_PE p₁/R_g) (n_* c₁) K_obs² e^{(min(2κ_dec, κ') - κ₀) c_G}` (the kernel sum),
`B₂ = C_PE ∑_r 8 C₀ (p₁/c_ψ)² e^{-κ₀ 𝗱(y_r)}` (the remainder coefficient) and the rate
`λ = min (min(2κ_dec, κ') - κ₀ - 1) κ'`:
`‖obsCoeffParam … θ T'‖ ≤ (B₁ + B₂) e^{-λ dExt T'}`. -/
theorem obsCoeffParam_bound_of_EvG_rho {ρ q : ℝ} (hRg : 1 < Rg) (hKc : K0 d L T.κ0 + 1 ≤ Kc)
    (hσ : ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ t ∈ ball (0 : ℂ) (3 / 2), ∀ y' Φ, DifferentiableOn ℂ
      (fun σ => (tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg
        hR (ball (0 : ℂ) (3 / 2)) e t σ).H y' Φ) (ball (0 : ℂ) Rg))
    (hzero : ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ t y' Φ,
      (tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
        (ball (0 : ℂ) (3 / 2)) e t 0).H y' Φ = 0)
    (hε : Rg * max (εH + εH) εH ≤ stepTheta d L Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
        RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))}))
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y))
    (hD : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S T.m₀ hp Ev D (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))))
          (2 * T.κdec) (rootCube (m₀ := T.m₀) (blockIndex y)))
    (θ : physParam N S) (hθ : θ ∈ physVqRho S S.a₁ S.ν T.t ρ q)
    (T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
      Set.univ)) :
    ‖obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T'‖ ≤
      ((cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
          (CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / Rg) *
          (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) * Kobs ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
        CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
            (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
              (LocalCover.fam T.m₀ y)) (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
                (LocalCover.fam T.m₀ y)) (rootCube (m₀ := T.m₀) (blockIndex y))) r)))) *
        Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T') := by
  obtain ⟨-, hrem, hkern⟩ := obsCoeffParam_norm_le_of_EvG_rho T k hk N₁ ν β p₁ Dsc S hS hp y h3N Lab
    hεH Aact hdj hK Rg hR hRg hKc hσ hzero hε Ev ha hd hb hD T'
  have hr := hrem θ hθ
  have hk' := hkern θ hθ
  have hcψ := Dsc.cψ_pos
  have hC0 := cK2'_famConst_mul_t_posG T
  have hCPE := CPE_nonneg' (d := d) (L := L) Kobs (2 * T.κdec - 1) T.κ0 T.κ'
  have hc1 : 0 < c1 d L := by linarith [one_le_c1 d L]
  have hdn := dExt_nonneg T'
  have hB1 : 0 ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
          (CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / Rg) *
          (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) * Kobs ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hC0.le hcψ.le)
      (div_nonneg (mul_nonneg hCPE hp.le) (by linarith)))
      (mul_nonneg (Nat.cast_nonneg _) hc1.le)) (sq_nonneg _)) (Real.exp_pos _).le
  have hB2 : 0 ≤ CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
            (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
              (LocalCover.fam T.m₀ y)) (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
                (LocalCover.fam T.m₀ y)) (rootCube (m₀ := T.m₀) (blockIndex y))) r))) :=
    mul_nonneg hCPE (Finset.sum_nonneg fun r _ => mul_nonneg (mul_nonneg (mul_nonneg
      (by norm_num) hC0.le) (sq_nonneg _)) (Real.exp_pos _).le)
  have e1 : Real.exp (-(min (2 * T.κdec) T.κ' - T.κ0 - 1) * dExt T') ≤
      Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T') :=
    Real.exp_le_exp.2 (by
      nlinarith [mul_le_mul_of_nonneg_right (min_le_left (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') hdn])
  have e2 : Real.exp (-T.κ' * dExt T') ≤
      Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T') :=
    Real.exp_le_exp.2 (by
      nlinarith [mul_le_mul_of_nonneg_right (min_le_right (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') hdn])
  unfold obsCoeffParam
  refine (norm_add_le _ _).trans ?_
  rw [add_mul]
  exact add_le_add (hk'.trans (mul_le_mul_of_nonneg_left e1 hB1))
    (hr.trans (mul_le_mul_of_nonneg_left e2 hB2))


include Dsc hS in
/-- General tower `T : StepTowerG d L N κmin` (block scale `T.m₀`, `b = β L^{k (d-2)}`); the fixed theorem `obsCoeffParam_bound_of_Ev` is its corollary.  **The sum bound of the coefficient of the observable.**  On the parameter set, with
`C₀ = Q t`, `c_ψ = lvCpsi`, `κ' = T.κ'`, `n_* = 2 · 3^{3(1+m₁+1)}`,
`B₁ = (C₀/c_ψ) (C_PE p₁/R_g) (n_* c₁) K_obs² e^{(min(2κ_dec, κ') - κ₀) c_G}` (the kernel sum),
`B₂ = C_PE ∑_r 8 C₀ (p₁/c_ψ)² e^{-κ₀ 𝗱(y_r)}` (the remainder coefficient) and the rate
`λ = min (min(2κ_dec, κ') - κ₀ - 1) κ'`:
`‖obsCoeffParam … θ T'‖ ≤ (B₁ + B₂) e^{-λ dExt T'}`. -/
theorem obsCoeffParam_bound_of_EvG {q : ℝ} (hRg : 1 < Rg) (hKc : K0 d L T.κ0 + 1 ≤ Kc)
    (hσ : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ t ∈ ball (0 : ℂ) (3 / 2), ∀ y' Φ, DifferentiableOn ℂ
      (fun σ => (tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg
        hR (ball (0 : ℂ) (3 / 2)) e t σ).H y' Φ) (ball (0 : ℂ) Rg))
    (hzero : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ t y' Φ,
      (tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
        (ball (0 : ℂ) (3 / 2)) e t 0).H y' Φ = 0)
    (hε : Rg * max (εH + εH) εH ≤ stepTheta d L Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (Ev : Set (CTorus d L N₁ T.m₁ (k + 1)) →
        RawData d L (N₁ * L ^ T.m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))}))
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ∀ u' ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))},
        ‖Ev Y u‖ ≤ (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne T.m₀ (k + 1) Y))
    (hD : ∀ D : BgData S.G' N, XiCData S.G' (compWeight L 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S T.m₀ hp Ev D (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / (lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))))
          (2 * T.κdec) (rootCube (m₀ := T.m₀) (blockIndex y)))
    (θ : physParam N S) (hθ : θ ∈ physVq S S.a₁ S.ν T.t q)
    (T' : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) T.m₀ (k + 1)
      Set.univ)) :
    ‖obsCoeffParam (S.blockSplit T.m₀ hp).μ
      (fun θ t σ => tiltActObs Aact (show L ^ T.m₀ ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 T.m₀ S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) m) (fun m => blockMarkC S T.m₀ hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData d L (N₁ * L ^ T.m₁) (k + 1) N)
          (obsUnitVec S m)) T.m₀ T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k (LocalCover.fam T.m₀ y))
          (rootCube (m₀ := T.m₀) (blockIndex y))))
      (fun θ => obsGrFam S T.m₀ hp Ev (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
        (LocalCover.fam T.m₀ y)) (XiCRaw S.G' (compWeight L 1) ν (k + 1) 1 T.t) θ) θ T'‖ ≤
      ((cK2' d L N (famConst d L T.BG₂ T.κ) * T.t / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) *
          (CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / Rg) *
          (((N * L ^ (d * (T.m₀ + T.m₁ + 1)) : ℕ) : ℝ) * c1 d L) * Kobs ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG d L) +
        CPE d L Kobs (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' d L N (famConst d L T.BG₂ T.κ) * T.t) *
            (S.p₁ / lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
              (LocalCover.fam T.m₀ y)) (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 T.m₀ (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF T.m₀ y) T.m₀ k
                (LocalCover.fam T.m₀ y)) (rootCube (m₀ := T.m₀) (blockIndex y))) r)))) *
        Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T') :=
  obsCoeffParam_bound_of_EvG_rho (ρ := 1) T k hk N₁ ν β p₁ Dsc S hS hp y h3N Lab hεH Aact hdj hK Rg hR hRg hKc hσ hzero hε Ev ha hd hb hD θ hθ T'

end TowerG

section Tower

variable {κmin : ℝ} (T : StepTower κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
  (ν β p₁ : ℝ) (Dsc : StepScaleData T k hk N₁ ν β p₁)
  (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
  (hp : 0 < S.p₁) (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (h3N : 3 ∣ N₁)
  {Lb : Type} [Fintype Lb]
  (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
    Set.univ Lb) {εH : ℝ} (hεH : 0 < εH) {Kc : ℝ}
  (Aact : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0 Kc)
  (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y), IsDj 1 (k + 1) Y)
  {Kobs : ℝ} (hK : Kc + Kc + K0 3 3 T.κ0 + K0 3 3 T.κ0 ≤ Kobs) (Rg : ℝ) (hR : 0 ≤ Rg)

include Dsc hS in
/-- **Support of the coefficient of the observable.**  For `θ` in the parameter set, if
`obsCoeffParam … θ T' ≠ 0` then the root cube of the observable site lies in `T'` and the sites of
`T'` form a polymer domain.  The kernel at `θ` is the kernel of the row coefficients at a datum
`D` with `rawOf D = θ.1`; its nonzero values sit on labels of domains of `𝒟_{k+1}`, which are
polymer site sets, and contain the root cube; the first-order terms vanish unless their cube lies in
the set and `dOmega` is finite; the remainder vanishes off polymer sets and contains the root cube
in every label. -/
theorem obsCoeffParam_support_of_Ev_rho {ρ q : ℝ} (hRg : 1 < Rg) (hKc : K0 3 3 T.κ0 + 1 ≤ Kc)
    (hε : Rg * max (εH + εH) εH ≤ stepTheta 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)}))
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y))
    (hD : ∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S 1 hp Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsi T.κ T.t (β * 3 ^ k))
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k)))
          (2 * T.κdec) (rootCube (m₀ := 1) (blockIndex y)))
    (θ : physParam 2 S) (hθ : θ ∈ physVqRho S S.a₁ S.ν T.t ρ q)
    (T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ)) :
    obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' ≠ 0 →
    rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T') := by
  have hb' : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  exact obsCoeffParam_support_of_EvG_rho T.toG k hk N₁ ν β p₁ (T.scaleDataG_of_fixed Dsc) S hS hp y h3N
    Lab hεH Aact hdj hK Rg hR hRg hKc hε Ev (by rw [hb']; exact ha) (by rw [hb']; exact hd)
    (by rw [hb']; exact hb) (by rw [hb']; exact hD) θ hθ T'


include Dsc hS in
/-- **Support of the coefficient of the observable.**  For `θ` in the parameter set, if
`obsCoeffParam … θ T' ≠ 0` then the root cube of the observable site lies in `T'` and the sites of
`T'` form a polymer domain.  The kernel at `θ` is the kernel of the row coefficients at a datum
`D` with `rawOf D = θ.1`; its nonzero values sit on labels of domains of `𝒟_{k+1}`, which are
polymer site sets, and contain the root cube; the first-order terms vanish unless their cube lies in
the set and `dOmega` is finite; the remainder vanishes off polymer sets and contains the root cube
in every label. -/
theorem obsCoeffParam_support_of_Ev {q : ℝ} (hRg : 1 < Rg) (hKc : K0 3 3 T.κ0 + 1 ≤ Kc)
    (hε : Rg * max (εH + εH) εH ≤ stepTheta 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)}))
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y))
    (hD : ∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S 1 hp Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsi T.κ T.t (β * 3 ^ k))
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k)))
          (2 * T.κdec) (rootCube (m₀ := 1) (blockIndex y)))
    (θ : physParam 2 S) (hθ : θ ∈ physVq S S.a₁ S.ν T.t q)
    (T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ)) :
    obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T' ≠ 0 →
    rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T') := by
  have hb' : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  exact obsCoeffParam_support_of_EvG T.toG k hk N₁ ν β p₁ (T.scaleDataG_of_fixed Dsc) S hS hp y h3N
    Lab hεH Aact hdj hK Rg hR hRg hKc hε Ev (by rw [hb']; exact ha) (by rw [hb']; exact hd)
    (by rw [hb']; exact hb) (by rw [hb']; exact hD) θ hθ T'

include Dsc hS in
/-- **The sum bound of the coefficient of the observable.**  On the parameter set, with
`C₀ = Q t`, `c_ψ = lvCpsi`, `κ' = T.κ'`, `n_* = 2 · 3^{3(1+m₁+1)}`,
`B₁ = (C₀/c_ψ) (C_PE p₁/R_g) (n_* c₁) K_obs² e^{(min(2κ_dec, κ') - κ₀) c_G}` (the kernel sum),
`B₂ = C_PE ∑_r 8 C₀ (p₁/c_ψ)² e^{-κ₀ 𝗱(y_r)}` (the remainder coefficient) and the rate
`λ = min (min(2κ_dec, κ') - κ₀ - 1) κ'`:
`‖obsCoeffParam … θ T'‖ ≤ (B₁ + B₂) e^{-λ dExt T'}`. -/
theorem obsCoeffParam_bound_of_Ev_rho {ρ q : ℝ} (hRg : 1 < Rg) (hKc : K0 3 3 T.κ0 + 1 ≤ Kc)
    (hσ : ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ t ∈ ball (0 : ℂ) (3 / 2), ∀ y' Φ, DifferentiableOn ℂ
      (fun σ => (tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg
        hR (ball (0 : ℂ) (3 / 2)) e t σ).H y' Φ) (ball (0 : ℂ) Rg))
    (hzero : ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ t y' Φ,
      (tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
        (ball (0 : ℂ) (3 / 2)) e t 0).H y' Φ = 0)
    (hε : Rg * max (εH + εH) εH ≤ stepTheta 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)}))
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y))
    (hD : ∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S 1 hp Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsi T.κ T.t (β * 3 ^ k))
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k)))
          (2 * T.κdec) (rootCube (m₀ := 1) (blockIndex y)))
    (θ : physParam 2 S) (hθ : θ ∈ physVqRho S S.a₁ S.ν T.t ρ q)
    (T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ)) :
    ‖obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T'‖ ≤
      ((cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
          (CPE 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / Rg) *
          (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) * Kobs ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
        CPE 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
            (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k
              (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
                (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))) r)))) *
        Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T') := by
  have hb' : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have h := obsCoeffParam_bound_of_EvG_rho T.toG k hk N₁ ν β p₁ (T.scaleDataG_of_fixed Dsc) S hS hp y
    h3N Lab hεH Aact hdj hK Rg hR hRg hKc hσ hzero hε Ev (by rw [hb']; exact ha)
    (by rw [hb']; exact hd) (by rw [hb']; exact hb) (by rw [hb']; exact hD) θ hθ T'
  rw [hb'] at h
  exact h


include Dsc hS in
/-- **The sum bound of the coefficient of the observable.**  On the parameter set, with
`C₀ = Q t`, `c_ψ = lvCpsi`, `κ' = T.κ'`, `n_* = 2 · 3^{3(1+m₁+1)}`,
`B₁ = (C₀/c_ψ) (C_PE p₁/R_g) (n_* c₁) K_obs² e^{(min(2κ_dec, κ') - κ₀) c_G}` (the kernel sum),
`B₂ = C_PE ∑_r 8 C₀ (p₁/c_ψ)² e^{-κ₀ 𝗱(y_r)}` (the remainder coefficient) and the rate
`λ = min (min(2κ_dec, κ') - κ₀ - 1) κ'`:
`‖obsCoeffParam … θ T'‖ ≤ (B₁ + B₂) e^{-λ dExt T'}`. -/
theorem obsCoeffParam_bound_of_Ev {q : ℝ} (hRg : 1 < Rg) (hKc : K0 3 3 T.κ0 + 1 ≤ Kc)
    (hσ : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ t ∈ ball (0 : ℂ) (3 / 2), ∀ y' Φ, DifferentiableOn ℂ
      (fun σ => (tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg
        hR (ball (0 : ℂ) (3 / 2)) e t σ).H y' Φ) (ball (0 : ℂ) Rg))
    (hzero : ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ t y' Φ,
      (tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK Rg hR
        (ball (0 : ℂ) (3 / 2)) e t 0).H y' Φ = 0)
    (hε : Rg * max (εH + εH) εH ≤ stepTheta 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ')
    (Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
        RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ)
    (ha : ∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)}))
    (hd : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ∀ u' ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        AgHatDir S.hG' Y u u' → Ev Y u = Ev Y u')
    (hb : ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t ×ˢ
          {ψh : unitPts S.G' × Fin 2 → ℂ | ∀ p, ‖ψh p‖ ≤ lvCpsi T.κ T.t (β * 3 ^ k)},
        ‖Ev Y u‖ ≤ (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
          Real.exp (-(2 * T.κdec) * treeLenCovOne 1 (k + 1) Y))
    (hD : ∀ D : BgData S.G' 2, XiCData S.G' (compWeight 3 1) ν (k + 1) 1 T.t D →
        ObsMarkHalf S 1 hp Ev D (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (obsLab (Lab.sum Lab) hdj) (lvCpsi T.κ T.t (β * 3 ^ k))
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) (2 * T.κdec - 1) T.κ0
          (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / (lvCpsi T.κ T.t (β * 3 ^ k)))
          (2 * T.κdec) (rootCube (m₀ := 1) (blockIndex y)))
    (θ : physParam 2 S) (hθ : θ ∈ physVq S S.a₁ S.ν T.t q)
    (T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
      Set.univ)) :
    ‖obsCoeffParam (S.blockSplit 1 hp).μ
      (fun θ t σ => tiltActObs Aact (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj hK
        Rg hR (ball (0 : ℂ) (3 / 2)) θ t σ)
      (fun m => obsY1 1 S (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) m) (fun m => blockMarkC S 1 hp m.1 m.2)
      (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
          (obsUnitVec S m)) 1 T'')
      (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
        (fun Y => Sum.inl (Sum.inr Y))
        (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
          (rootCube (m₀ := 1) (blockIndex y))))
      (fun θ => obsGrFam S 1 hp Ev (obsDomains S (LocalCover.nbhdF 1 y) 1 k
        (LocalCover.fam 1 y)) (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T'‖ ≤
      ((cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
          (CPE 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / Rg) *
          (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) * Kobs ^ 2 *
          Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
        CPE 3 3 Kobs (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
            (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp (-T.κ0 *
            (obsLab (Lab.sum Lab) hdj).dl (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k
              (LocalCover.fam 1 y)) (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k
                (LocalCover.fam 1 y)) (rootCube (m₀ := 1) (blockIndex y))) r)))) *
        Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T') := by
  have hb' : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have h := obsCoeffParam_bound_of_EvG T.toG k hk N₁ ν β p₁ (T.scaleDataG_of_fixed Dsc) S hS hp y
    h3N Lab hεH Aact hdj hK Rg hR hRg hKc hσ hzero hε Ev (by rw [hb']; exact ha)
    (by rw [hb']; exact hd) (by rw [hb']; exact hb) (by rw [hb']; exact hD) θ hθ T'
  rw [hb'] at h
  exact h

end Tower

end Balaban.Inhabited
