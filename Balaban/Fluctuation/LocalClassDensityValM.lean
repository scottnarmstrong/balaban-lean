/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityValClass
public import Balaban.Inhabited.OffFibreM0Family

/-!
# The source density of the new level as a sum of coefficients on the class domain (blocker 6, M)

* `JointRep.eq_sum_clipRaw_of_value`: a function `F` of the raw datum whose value at the raw datum of
  every datum of the chart is the sum of a family `e` over cube sets has, at the cut-off `q̄` of every
  pair `q` of the class domain `Ξ^c_{k+1}(𝔹; 1, ε)`, `ε ≤ eps`, the value `∑_T e(q̄) T`.
* `JointRep.densM0_eq_sum_of_value`: for any class, the source density
  `densM0 x ((Ψ, h), g)_i = ℳ₀^{(k+1)}(x; g)_i` at the cut-off is the sum of a family `e(·, g)`
  whenever `M0J` is at every chart datum and every source of a set `Gs`;
  `JointRep.densM0_eq_sum_of_avgJ`: the same with the value identity written as
  `β_k^{1/2} avgJ (W₁, W₂, ℳ_k) = β_k^{1/2} ∑ e`, the form of the landed value clause.
* `densM0_zeroClass_fromTower_rho` (the input `hDM` for the zero class, on the whole class domain):
  at the tower, beyond a threshold `β₀`, for every site `y`, component `i` and source radius `q ≤ ρ`,
  the coefficient family `e = obsCoeffParam …` of `obsM0Family_full_fromTower_rho` is analytic on
  `physVqRho`, bounded, rooted at `y` and local on `sitesOf T`, and for every pair `q` of the class
  domain and every source `g` of the `ℓ¹` ball of radius `q`,
  `densM0 y ((Ψ, h), g)_i = β_k^{1/2} ∑_T e(q̄, g) T`.

The general class analogue of the last item needs the general class analogue of the observable
coefficient family (tilted activity and marks of the class exponent `W₁^C + W₂^C`), which is not
constructed; the generic lemmas apply to it once constructed.
-/

@[expose] public section

namespace Balaban.Fluctuation.StepSetting.JointRep

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Polymer

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ eps pp : ℝ}
  {S : StepSetting d L N₁ m₁ k N ϱ} (Jr : S.JointRep eps pp) (C : StepClass d L N₁ m₁ k N ϱ)

open Classical in
/-- **The value at the cut-off of a pair of the class domain** of a function `F` of the raw datum
whose value at the raw datum of every chart datum is the sum of a family over cube sets. -/
theorem eq_sum_clipRaw_of_value {m₀ : ℕ} (F : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    (e : rawSub N S.G' →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ)
    (hval : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D →
      F (rawOf D) = ∑ T, e ⟨rawOf D, rawOf_mem_rawSub _⟩ T)
    {ε : ℝ} (hε : ε ≤ eps) {q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hq : XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2) :
    F (clipRaw S.G' q) = ∑ T,
      (if h : clipRaw S.G' q ∈ rawSub N S.G' then e ⟨clipRaw S.G' q, h⟩ T else 0) := by
  obtain ⟨D, hD, hcl⟩ := clipRaw_mem_xiCRaw_of_xiDom hε hq
  have hmem : clipRaw S.G' q ∈ rawSub N S.G' := hcl ▸ rawOf_mem_rawSub D
  have hsub : (⟨clipRaw S.G' q, hmem⟩ : rawSub N S.G') = ⟨rawOf D, rawOf_mem_rawSub D⟩ :=
    Subtype.ext hcl
  simp only [hmem, ↓reduceDIte, hsub]
  rw [hcl]
  exact hval D hD

open Classical in
/-- **The source density on the class domain from the value of `M0J` at every chart datum.** -/
theorem densM0_eq_sum_of_value {m₀ : ℕ} (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (Gs : Set (Fld d L N₁ m₁ (k + 1) N))
    (e : physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ)
    (hval : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ g ∈ Gs,
      Jr.M0J C g x i (rawOf D) = ∑ T, e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T)
    {ε : ℝ} (hε : ε ≤ eps) {q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hq : XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2) {g : Fld d L N₁ m₁ (k + 1) N} (hg : g ∈ Gs) :
    Jr.densM0 C x (q, g) i = ∑ T,
      (if h : clipRaw S.G' q ∈ rawSub N S.G' then
        e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), g) T else 0) :=
  eq_sum_clipRaw_of_value (Jr.M0J C g x i) (fun r T => e (r, g) T)
    (fun D hD => hval D hD g hg) hε hq

open Classical in
/-- **The source density on the class domain from the value identity in the form
`β_k^{1/2} avgJ (W₁, W₂, ℳ_k) = β_k^{1/2} ∑ e`** at every chart datum and every source of `Gs`. -/
theorem densM0_eq_sum_of_avgJ {m₀ : ℕ} (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (Gs : Set (Fld d L N₁ m₁ (k + 1) N))
    (e : physParam N S →
      Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ)
    (hval : ∀ D : BgData S.G' N, XiCData S.G' S.a S.ν (k + 1) 1 eps D → ∀ g ∈ Gs,
      ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          S.avgJ (Jr.W1 C) (Jr.W2 C g) (Jr.McJ C g x i) (rawOf D) =
        ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          ∑ T, e ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) T)
    {ε : ℝ} (hε : ε ≤ eps) {q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hq : XiDom S.G' S.a S.ν (k + 1) ε q.1 q.2) {g : Fld d L N₁ m₁ (k + 1) N} (hg : g ∈ Gs) :
    Jr.densM0 C x (q, g) i = ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T,
      (if h : clipRaw S.G' q ∈ rawSub N S.G' then
        e ((⟨clipRaw S.G' q, h⟩ : rawSub N S.G'), g) T else 0) := by
  have h := Jr.densM0_eq_sum_of_value C x i Gs
    (fun θ T => ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * e θ T)
    (fun D hD g hg => (hval D hD g hg).trans (Finset.mul_sum _ _ _)) hε hq hg
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hm : clipRaw S.G' q ∈ rawSub N S.G'
  · simp only [hm, ↓reduceDIte]
  · simp only [hm, ↓reduceDIte, mul_zero]

end Balaban.Fluctuation.StepSetting.JointRep

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep MeasureTheory Metric

open Classical in
/-- **The input `hDM` of the zero class on the whole class domain.**  At the tower, beyond a
threshold `β₀`, at every scale datum and every source radius `q ≤ ρ`, there are the labels and the
activity of `obsM0Family_full_fromTower_rho` such that for every site `y` and component `i` the
coefficient family `e = obsCoeffParam …` (the family of `obsM0Family_full_fromTower_rho`) is analytic
on `physVqRho`, bounded, non-zero only on polymer sets containing the root cube of `y`, local on
`sitesOf T` (raw datum and source), and for one joint representative `Jr`, every pair `q` of the
class domain `Ξ^c_{k+1}(𝔹; 1, ε)`, `ε ≤ t`, and every source `g` of the `ℓ¹` ball of radius `q`,
`densM0 y (q, g)_i = β_k^{1/2} ∑_T e(q̄, g) T` (`q̄` the cut-off of `q`). -/
theorem densM0_zeroClass_fromTower_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁)
    (p : ℕ) {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) (ρ : ℝ) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ ρ →
      ∀ (_ : StepScaleData T k hk N₁ ν β p₁)
        (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Lb : Type) (_ : Fintype Lb)
        (Lab : CubeLabels (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
          Set.univ Lb) (εH : ℝ) (hεH : 0 < εH)
        (A : physParam 2 S → ℂ → LabelAct Lab (S.blockSplit 1 hp).Ωb εH (2 * T.κdec - 1) T.κ0
          (K0 3 3 T.κ0 + 1)),
        ∀ (y : CTorus 3 3 N₁ T.m₁ (k + 1)) (i : Fin 2)
          (hdj : ∀ Y ∈ obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y),
            IsDj 1 (k + 1) Y),
        ∃ (hR : 0 ≤ obsRg CR s (p : ℝ) (β * 3 ^ k))
          (Ev : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) →
            RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (unitPts S.G' × Fin 2 → ℂ) → ℂ)
          (e : physParam 2 S → Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁)
            (K := k + 1) 1 (k + 1) Set.univ) → ℂ)
          (Jr : S.JointRep T.t (2 * p₁)),
          (∀ θ T', e θ T' = obsCoeffParam (S.blockSplit 1 hp).μ
            (fun θ t σ => tiltActObs A (show 3 ^ 1 ∣ N₁ by simpa using h3N) T.κ0_ent hεH.le hdj
              (le_refl _) (obsRg CR s (p : ℝ) (β * 3 ^ k)) hR (ball (0 : ℂ) (3 / 2)) θ t σ)
            (fun m => obsY1 1 S (Lb ⊕ Lb)
              (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y)) m)
            (fun m => blockMarkC S 1 hp m.1 m.2)
            (fun θ m T'' => obsHker (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
              (fun Y => hatCoeff (Ev Y) (θ.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2)
                (obsUnitVec S m)) 1 T'')
            (obsRemLab (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
              (fun Y => Sum.inl (Sum.inr Y))
              (obsY0 1 (Lb ⊕ Lb) (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                (rootCube (m₀ := 1) (blockIndex y))))
            (fun θ => obsGrFam S 1 hp Ev
              (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
              (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 T.t) θ) θ T') ∧
          (∀ T' : Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ),
            AnalyticOnNhd ℂ (fun θ => e θ T') (physVqRho S S.a₁ S.ν T.t ρ q) ∧
            (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ‖e θ T'‖ ≤
              ((cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t / lvCpsi T.κ T.t (β * 3 ^ k)) *
                  (CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
                    (2 * T.κdec - 1) T.κ0 T.κ' * S.p₁ / (obsRg CR s (p : ℝ) (β * 3 ^ k))) *
                  (((2 * 3 ^ (3 * (1 + T.m₁ + 1)) : ℕ) : ℝ) * c1 3 3) *
                  ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0) ^ 2 *
                  Real.exp ((min (2 * T.κdec) T.κ' - T.κ0) * cG 3 3) +
                CPE 3 3 ((K0 3 3 T.κ0 + 1) + (K0 3 3 T.κ0 + 1) + K0 3 3 T.κ0 + K0 3 3 T.κ0)
                    (2 * T.κdec - 1) T.κ0 T.κ' *
                  (∑ r, 8 * (cK2' 3 3 2 (famConst 3 3 T.BG₂ T.κ) * T.t) *
                    (S.p₁ / lvCpsi T.κ T.t (β * 3 ^ k)) ^ 2 * Real.exp (-T.κ0 *
                    (obsLab (Lab.sum Lab) hdj).dl (obsRemLab
                      (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                      (fun Y => Sum.inl (Sum.inr Y))
                      (obsY0 1 (Lb ⊕ Lb)
                        (obsDomains S (LocalCover.nbhdF 1 y) 1 k (LocalCover.fam 1 y))
                        (rootCube (m₀ := 1) (blockIndex y))) r)))) *
                Real.exp (-(min (min (2 * T.κdec) T.κ' - T.κ0 - 1) T.κ') * dExt T')) ∧
            (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, e θ T' ≠ 0 →
              rootCube (m₀ := 1) (blockIndex y) ∈ T' ∧ IsPolyDom 1 (k + 1) (sitesOf T')) ∧
            (∀ θ ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ θ' ∈ physVqRho S S.a₁ S.ν T.t ρ q,
              physRestrict (N := 2) (sitesOf T') (physIncl 2 S θ) =
                physRestrict (sitesOf T') (physIncl 2 S θ') → e θ T' = e θ' T')) ∧
          ∀ ε : ℝ, ε ≤ T.t →
          ∀ qq : Fld 3 3 N₁ T.m₁ (k + 1) 2 × Fld 3 3 N₁ T.m₁ (k + 1) 2,
            XiDom S.G' S.a S.ν (k + 1) ε qq.1 qq.2 →
          ∀ g ∈ l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 q,
            Jr.densM0 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) y (qq, g) i =
              ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T',
                (if h : clipRaw S.G' qq ∈ rawSub 2 S.G' then
                  e ((⟨clipRaw S.G' qq, h⟩ : rawSub 2 S.G'), g) T' else 0) := by
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ := obsM0Family_full_fromTower_rho T hA p hCR hs0 hs ρ
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp₀ hp₁ q hq0 hq Dsc S hS hp
  obtain ⟨Lb, hLb, Lab, εH, hεH, A, -, hy⟩ :=
    H k hk N₁ h3N hN ν hν0 hν β hβ p₁ hp₀ hp₁ q hq0 hq Dsc S hS hp
  refine ⟨Lb, hLb, Lab, εH, hεH, A, fun y i hdj => ?_⟩
  obtain ⟨hR, -, -, Ev, -, -, -, -, -, hT', -, Jr, -, hval⟩ := hy y i hdj
  refine ⟨hR, Ev, _, Jr, fun θ T' => rfl, fun T' => ?_, fun ε hε qq hqq g hg => ?_⟩
  · obtain ⟨-, -, -, han, hbd, hsupp, -, hloc⟩ := hT' T'
    exact ⟨han, hbd, hsupp, hloc⟩
  · exact Jr.densM0_eq_sum_of_avgJ (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) y i
      (l1BallRho 3 3 N₁ T.m₁ (k + 1) 2 q) _ hval hε hqq hg

end Balaban.Inhabited
