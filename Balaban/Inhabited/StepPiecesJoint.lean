/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepPiecesRenSol
public import Balaban.Inhabited.SourceWitnessJoint
public import Balaban.Inhabited.RenormDetFibreTower
public import Balaban.Inhabited.StepTowerTheta

/-!
# The step pieces, the source witness and the determinant fibre at one tower

`stepPieces_joint`: for `Tw : StepTowerTheta κmin` with `renDetFibreMin ≤ κmin` (hence
`stepHullMin ≤ κmin`) there is ONE threshold `β₀` such that, at every admissible scale, for every
scale datum `D` of the tower, the following hold together:

* the conclusions of `stepPieces_fromTowerRenSol` at `Tw.toStepTowerRenSol`, except its first
  conjunct (the source activity records `BR`, `BC`), which is replaced by
* the conclusion of `sourceWitness_fromTower` at `Tw.T` (its own amplitude constants `CE₂`, `CF₂`);
* the conclusion of `renDetFibre_tower` at `Tw.T`.

Every conjunct is copied from the landed theorem with the tower replaced by `Tw.T`.  The witnesses
chosen by the three theorems are separate existentials: the source witness `val, 𝒴, Tt` of the
second part is not identified with the `𝒴` of `stepPieces_fromTowerRenSol` (parts (iii), (v), the
source family), the determinant family `E` of the package in part (i) and that of (vi) is not
identified with the fibre family `E` of the last part, and the field `F` of the renormalization
lane is the one of `renLoc_fields_scale_of_tower`; the second expansion (`C₂`) carries its own `F`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover
  Filter Topology Matrix Metric Set Balaban.Localization.DecEquiv MeasureTheory

section Joint

variable {κmin : ℝ}

open Classical in
/-- **The step pieces, the source witness and the determinant fibre at one tower.**  See the
module doc-string. -/
theorem stepPieces_joint (Tw : StepTowerTheta κmin) (hT : renDetFibreMin ≤ κmin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
                3 / 2 * Tw.T.κdec ≤ hullRate 3 3
          ((Tw.T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 : ℝ) + 1)) / 18) ∧
        (∃ C : StepOutputConsts 3 3, C.k0 = Tw.T.κ0 ∧ C.kdec = Tw.T.κdec ∧ C.k' = Tw.T.κ' ∧
          C.kout = 3 / 2 * Tw.T.κdec ∧ C.kH = 2 * Tw.T.κdec - 1 ∧ C.kapp = Tw.T.κ ∧
          C.kdet = (Tw.T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 : ℝ) + 1)) / 18 ∧
          C.Bhull = collarB 3 3 ∧ C.lhull = hullRate 3 3 C.kdet ∧
          C.Kc = 2 * (K0 3 3 Tw.T.κ0 + 1) ∧
          C.Kall = max (2 * K0 3 3 Tw.T.κ0) (rootUnionK 3 3 1 Tw.T.m₁ Tw.T.κ0) ∧ C.Ktot = C.Kc + C.Kall) ∧
    ∃ β₀ CE CF CE' CF' CE₂ CF₂ : ℝ, 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧ 0 < CE' ∧ 0 < CF' ∧
      0 < CE₂ ∧ 0 < CF₂ ∧
    ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
    ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
    ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp0 : 0 < p₁),
    p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      Nonempty (StepScaleData Tw.T k hk N₁ ν β p₁) ∧
      ∀ D : StepScaleData Tw.T k hk N₁ ν β p₁,
      (
      (
              (
              ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ Tw.T.m₁ * 3 ^ (k + 1 - (k + 1))),
                  DetExpansionLocC (Tw.T.step k hk N₁ ν β p₁) 1 z Tw.T.t (towerDetRate Tw.T.κ)
                    (towerDetConst Tw.T.κ),
                (∀ z D T', (E z).term D T' = ∑ y ∈ (Tw.T.step k hk N₁ ν β p₁).blockU z,
                  detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 Tw.T.BG Tw.T.κ) D y T') ∧
                (∀ z (D : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2),
                  XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D →
                  ∑ X ∈ (Finset.univ : Finset (Finset (CubeB (d := 3) (L := 3) (N₁ := N₁) (m₁ := Tw.T.m₁)
                      (K := k + 1) 1 (k + 1) Set.univ))).image detCollarHull, (E z).detGrouped D X =
                    rootTrace (Tw.T.step k hk N₁ ν β p₁).G' (Tw.T.step k hk N₁ ν β p₁).a 1 ν
                      (unitQ (Tw.T.step k hk N₁ ν β p₁).G') (unitP (Tw.T.step k hk N₁ ν β p₁).G')
                      ((Tw.T.step k hk N₁ ν β p₁).blockU z) (fun _ => 1)
                      (svec (Tw.T.step k hk N₁ ν β p₁).G' (bgFieldC (Tw.T.step k hk N₁ ν β p₁).G'
                        (Tw.T.step k hk N₁ ν β p₁).a ν (bgC0 3 3 2) D))
                      (bgMultC (Tw.T.step k hk N₁ ν β p₁).G' (Tw.T.step k hk N₁ ν β p₁).a ν (bgC0 3 3 2) D)) ∧
                (∀ z (D : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2),
                  XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D →
                  ∀ X : Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1)),
                    ‖(E z).detGrouped D X‖ ≤ hullConst 3 3 (towerDetRate Tw.T.κ) (towerDetConst Tw.T.κ) *
                      Real.exp (-hullRate 3 3 (towerDetRate Tw.T.κ) * sizeJ 1 (k + 1) X)) ∧
                (∀ z (D : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2),
                  XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D →
                  ∀ X : Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1)), (E z).detGrouped D X ≠ 0 →
                    IsPolyDom 1 (k + 1) X ∧
                      box (rootCube (m₀ := 1) (K := k + 1) z).1 (cellSide 3 1 Tw.T.m₁ (k + 1)) ⊆ X) ∧
                (∀ z (D D₂ : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2),
                  XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D →
                  XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D₂ →
                  ∀ X : Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1)),
                    (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
                    (E z).detGrouped D X = (E z).detGrouped D₂ X) ∧
                (∀ {σ : Equiv.Perm (CTorus 3 3 N₁ Tw.T.m₁ (k + 1))},
                  GenSymm 3 N₁ Tw.T.m₁ (k + 1) (k + 1) 1 σ →
                  ∃ Sy : LatSymm (Tw.T.step k hk N₁ ν β p₁).G' (Tw.T.step k hk N₁ ν β p₁).G' σ,
                    (∀ D : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2,
                      XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D →
                      XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t (Sy.sym D)) ∧
                    ∀ z, (∀ (D : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2) T',
                        (E (rootAct σ z)).term (Sy.sym D) (cubeAct σ T') = (E z).term D T') ∧
                      ∀ (D : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2)
                        (X : Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1))),
                        (E (rootAct σ z)).detGrouped (Sy.sym D) (σ '' X) = (E z).detGrouped D X) ∧
                (∀ z (D : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2),
                  XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D →
                  ∀ {Rm : Matrix (Fin 2) (Fin 2) ℂ}, Rmᵀ * Rm = 1 →
                    (∀ T', (E z).term (D.rot Rm) T' = (E z).term D T') ∧
                    ∀ X : Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1)),
                      (E z).detGrouped (D.rot Rm) X = (E z).detGrouped D X) ∧
                (∀ (D : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2),
                  XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D →
                  ∀ {Q : Matrix (Fin 2) (Fin 2) ℝ}, Qᵀ * Q = 1 →
                    XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t
                      (D.rot (cmat Q)))) ∧
              (
              ∃ Jr : (Tw.T.step k hk N₁ ν β p₁).JointRep Tw.T.t (2 * p₁),
              ∃ val : ((((Tw.T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) ×
                    ((Tw.T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ))) →
                  (((Tw.T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ) × ((Tw.T.step k hk N₁ ν β p₁).U × Fin 2 → ℂ)) →
                    ℂ → (RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2 ×
                      (CTorus 3 3 N₁ Tw.T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ,
                (∀ x w σ Θ, val x w σ Θ =
                  (-((Tw.T.step k hk N₁ ν β p₁).β : ℂ)) * raySrc3
                    (hatFun (Tw.T.step k hk N₁ ν β p₁).G' (Tw.T.step k hk N₁ ν β p₁).a₁
                      (Tw.T.step k hk N₁ ν β p₁).ν Tw.T.t (Tw.T.step k hk N₁ ν β p₁).hG'
                      (((Tw.T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                      (interactionOne (Tw.T.step k hk N₁ ν β p₁).hG (Tw.T.step k hk N₁ ν β p₁).hG'
                        (le_refl (k + 1)) (Tw.T.step k hk N₁ ν β p₁).a₁ (Tw.T.step k hk N₁ ν β p₁).ν Tw.T.t))
                    taylorWeight x.1 w.1 σ Θ.1 +
                  ((Tw.T.step k hk N₁ ν β p₁).β : ℂ) * (∑ s : CTorus 3 3 N₁ Tw.T.m₁ (k + 1) × Fin 2,
                    Θ.2 s.1 s.2 *
                    dirTermSrc (hatFun (Tw.T.step k hk N₁ ν β p₁).G' (Tw.T.step k hk N₁ ν β p₁).a₁
                      (Tw.T.step k hk N₁ ν β p₁).ν Tw.T.t (Tw.T.step k hk N₁ ν β p₁).hG'
                      (((Tw.T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                      (onXi (Tw.T.step k hk N₁ ν β p₁).G' (Tw.T.step k hk N₁ ν β p₁).a₁
                        (Tw.T.step k hk N₁ ν β p₁).ν Tw.T.t
                        (fun D' ψ' => svec (stepG 3 3 N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁))
                          (flFieldOne (Tw.T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁))
                            Tw.T.BG₂ Tw.T.κ (Tw.T.step k hk N₁ ν β p₁).a₁ (Tw.T.step k hk N₁ ν β p₁).ν D' ψ')
                          s.1 s.2)))
                      (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
                ∀ (g : Fld 3 3 N₁ Tw.T.m₁ (k + 1) 2) (x : (Tw.T.step k hk N₁ ν β p₁).EC),
                  (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ q, ‖((r : ℂ) • x) q‖ ≤ 2 * p₁) →
                  ∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 →
                    Jr.W2 (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁)) g
                        (rawOf (Tw.T.step k hk N₁ ν β p₁).D', (τ : ℂ) • x) =
                      val (x, x) (x, x) (τ : ℂ)
                          (rawOf (Tw.T.step k hk N₁ ν β p₁).D',
                            fun y i => g y i / ((Tw.T.step k hk N₁ ν β p₁).β : ℂ)) -
                        val (x, x) (x, x) (τ : ℂ) (rawOf (Tw.T.step k hk N₁ ν β p₁).D', 0)) ∧
              (∀ q : ℝ, 0 < q → q ≤ 1 →
                ∀ S : StepSetting 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁), S = Tw.T.step k hk N₁ ν β p₁ →
                ∀ hp : 0 < S.p₁,
                ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
                      ℂ → (RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ Tw.T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
                    (𝒴 : Finset (Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1))))
                    (Tt : Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
                      ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
                      (RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ Tw.T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
                    (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                          (S.β * prop33EpsEtaScaled 3 3 2 Tw.T.m₁ k 1 S.a₁ Tw.T.BG Tw.T.BG₂ Tw.T.κ Tw.T.t
                            (lvR Tw.T.κ Tw.T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * Tw.T.κdec - 1)
                          (rawOf S.D', (0 : CTorus 3 3 N₁ Tw.T.m₁ (k + 1) → Fin 2 → ℂ))
                          (physSΛEta S S.a₁ S.ν Tw.T.t (q / S.β))
                          (physXW S (lvCpsi Tw.T.κ Tw.T.t (β * 3 ^ k)) 2 2 (lvR Tw.T.κ Tw.T.t (β * 3 ^ k) p₁)) val (physAgΘ S)
                          (AgFDirPair S)),
                    I.𝒴 = 𝒴 ∧ I.T = Tt ∧
                    ∃ hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
                        (physVq S 1 ν Tw.T.t q),
                      (∀ g : Fld 3 3 N₁ Tw.T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < q →
                        ∃ hg : (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) ∈ physVq S 1 ν Tw.T.t q,
                          physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) =
                            (rawOf S.D', fun y i => g y i / (S.β : ℂ)) ∧
                          (I.atThetaOn S 1 _ hF hg).𝒴 = 𝒴 ∧ (I.atThetaOn S 1 _ hF hg).T = Tt) ∧
                      ∃ hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 Tw.T.m₁ k 1 S.a₁ Tw.T.BG Tw.T.BG₂ Tw.T.κ Tw.T.t
                            (lvR Tw.T.κ Tw.T.t (β * 3 ^ k) p₁) 0 0 (q / S.β),
                        4 * (S.β * prop33EpsEtaScaled 3 3 2 Tw.T.m₁ k 1 S.a₁ Tw.T.BG Tw.T.BG₂ Tw.T.κ Tw.T.t
                            (lvR Tw.T.κ Tw.T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) ≤
                          CE' * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
                            q * CF' * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
                        ∀ {Kc : ℝ} (hKc : K0 3 3 Tw.T.κ0 ≤ Kc),
                        (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                          AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                            (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                              (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                              Tw.T.κ0_ent hKc r.1 r.2).H y Φ)
                            (physVq S 1 ν Tw.T.t q ×ˢ ball (0 : ℂ) 2)) ∧
                        (∀ e (he : e ∈ physVq S 1 ν Tw.T.t q) (u : ℂ),
                          labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                              (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                              Tw.T.κ0_ent hKc e u =
                            dtAct S 1 (I.atThetaOn S 1 _ hF he)
                              (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                              Tw.T.κ0_ent hKc u) ∧
                        (∀ e ∈ physVq S 1 ν Tw.T.t q, ∀ u : ℂ, ‖u‖ < 2 →
                          ∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                          (labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                              (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU
                              Tw.T.κ0_ent hKc e u).H y Φ =
                            I.T y.1 (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                              (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                              (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)))) ∧
      -- (ii)
      (∀ ε : ℝ, ε ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
          CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) →
        ε ≤ (stepOutputPhysical Tw.T (stepHullMin_le_renDetFibreMin.trans hT)).theta ∧
        ε ≤ stepTheta 3 3 Tw.T.marksKc' (2 * Tw.T.κdec - 1) Tw.T.κ0 Tw.T.κ') ∧
      -- (iii)
      (
            ∃ (𝒴 : Torus 3 (N₁ * 3 ^ Tw.T.m₁ * 3 ^ (k + 1 - (k + 1))) →
              Finset (Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1))))
            (Ev : Torus 3 (N₁ * 3 ^ Tw.T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1)) →
              RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ Tw.T.m₁ (k + 1) → Fin 2 → ℂ) → ℂ),
            (∀ zb Y, AnalyticOnNhd ℂ (Ev zb Y)
              (XiCRaw (Tw.T.step k hk N₁ ν β p₁).G' (Tw.T.step k hk N₁ ν β p₁).a (Tw.T.step k hk N₁ ν β p₁).ν (k + 1) 1 Tw.T.t ×ˢ FlBall (stepG 3 3 N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) Tw.T.t)) ∧
            (∀ zb, ∀ Θ ∈ XiCRaw (Tw.T.step k hk N₁ ν β p₁).G' (Tw.T.step k hk N₁ ν β p₁).a (Tw.T.step k hk N₁ ν β p₁).ν (k + 1) 1 Tw.T.t,
              ∀ ψ' ∈ FlBall (stepG 3 3 N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) Tw.T.t,
              blockEnergyOne (Tw.T.step k hk N₁ ν β p₁).G' (stepG 3 3 N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) (Tw.T.step k hk N₁ ν β p₁).a₁ (Tw.T.step k hk N₁ ν β p₁).ν Tw.T.BG₂ Tw.T.κ Tw.T.t k zb
                (Θ, ψ') = ∑ Y ∈ 𝒴 zb, Ev zb Y (Θ, ψ')) ∧
            (∀ zb Y, ∀ u ∈ XiCRaw (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 (Tw.T.step k hk N₁ ν β p₁).a₁) (Tw.T.step k hk N₁ ν β p₁).ν (k + 1) 1 Tw.T.t ×ˢ
                FlBall (stepG 3 3 N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) Tw.T.t,
              ∀ u' ∈ XiCRaw (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 (Tw.T.step k hk N₁ ν β p₁).a₁) (Tw.T.step k hk N₁ ν β p₁).ν (k + 1) 1 Tw.T.t ×ˢ
                FlBall (stepG 3 3 N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) Tw.T.t,
              agreeOn (thickSet (Tw.T.step k hk N₁ ν β p₁).G' Y) u.1 u'.1 →
                (∀ y ∈ psiThick Y, u.2 y = u'.2 y) → Ev zb Y u = Ev zb Y u') ∧
            (∀ zb Y, ∀ u ∈ XiCRaw (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 (Tw.T.step k hk N₁ ν β p₁).a₁) (Tw.T.step k hk N₁ ν β p₁).ν (k + 1) 1 Tw.T.t ×ˢ
                FlBall (stepG 3 3 N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) Tw.T.t,
              ‖Ev zb Y u‖ ≤ energyBdScaled 3 3 2 (compWeight 3 (Tw.T.step k hk N₁ ν β p₁).a₁) k
                (cK2' 3 3 2 (famConst 3 3 Tw.T.BG₂ Tw.T.κ) * Tw.T.t) Tw.T.t (rho4 3 3 2 Tw.T.BG Tw.T.κ) *
                Real.exp (-2 * Tw.T.κdec * treeLenCov (Tw.T.step k hk N₁ ν β p₁).G' 1 Y)) ∧
            (∀ x : (Tw.T.step k hk N₁ ν β p₁).E, ‖x‖ ≤ p₁ →
              ∃ Q : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2 → (Tw.T.step k hk N₁ ν β p₁).EC,
                AnalyticOnNhd ℂ Q (XiCRaw (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 (Tw.T.step k hk N₁ ν β p₁).a₁) (Tw.T.step k hk N₁ ν β p₁).ν (k + 1) 1 Tw.T.t) ∧
                (∀ (D : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2) (hDh : ∀ y i, D.h y i = ((Tw.T.step k hk N₁ ν β p₁).h₀ i : ℂ)),
                  XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 (Tw.T.step k hk N₁ ν β p₁).a₁) (Tw.T.step k hk N₁ ν β p₁).ν (k + 1) 1 Tw.T.t D →
                  Q (rawOf D) = ((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x) ∧
                (∀ Θ ∈ XiCRaw (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 (Tw.T.step k hk N₁ ν β p₁).a₁) (Tw.T.step k hk N₁ ν β p₁).ν (k + 1) 1 Tw.T.t, ∀ b : (Tw.T.step k hk N₁ ν β p₁).U,
                  vn (fun i => Q Θ (b, i)) ≤
                    markedRad 3 3 2 k (Tw.T.step k hk N₁ ν β p₁).a₁ Tw.T.κ p₁ ((((Tw.T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) ∧
                ∀ (z : Torus 3 (N₁ * 3 ^ Tw.T.m₁ * 3 ^ (k + 1 - (k + 1))))
                  (zb : Torus 3 (N₁ * 3 ^ Tw.T.m₁ * 3 ^ (k + 1 - (k + 1)))) (Y : Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1))),
                AnalyticOnNhd ℂ (fun w : (physParam 2 (Tw.T.step k hk N₁ ν β p₁) × ℂ) × ℂ =>
                    markedBlockTerm (Ev zb Y) taylorWeight
                      (liftC (Tw.T.step k hk N₁ ν β p₁).hG' (w.1.2 • Q (w.1.1.1 : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2)))
                      (liftC (Tw.T.step k hk N₁ ν β p₁).hG' ((Tw.T.step k hk N₁ ν β p₁).maskUC z (Q (w.1.1.1 : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2))))
                      (w.1.1.1 : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2) w.2)
                  ((physV (Tw.T.step k hk N₁ ν β p₁) (Tw.T.step k hk N₁ ν β p₁).a₁ (Tw.T.step k hk N₁ ν β p₁).ν Tw.T.t ×ˢ Metric.ball (0 : ℂ) (17 / 16)) ×ˢ Metric.ball (0 : ℂ) (1 / 16)) ∧
                AnalyticOnNhd ℂ (fun w : physParam 2 (Tw.T.step k hk N₁ ν β p₁) × ℂ => deriv (markedBlockTerm (Ev zb Y) taylorWeight
                    (liftC (Tw.T.step k hk N₁ ν β p₁).hG' (w.2 • Q (w.1.1 : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2)))
                    (liftC (Tw.T.step k hk N₁ ν β p₁).hG' ((Tw.T.step k hk N₁ ν β p₁).maskUC z (Q (w.1.1 : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2))))
                    (w.1.1 : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2)) 0)
                  (physV (Tw.T.step k hk N₁ ν β p₁) (Tw.T.step k hk N₁ ν β p₁).a₁ (Tw.T.step k hk N₁ ν β p₁).ν Tw.T.t ×ˢ Metric.ball (0 : ℂ) (17 / 16)) ∧
                ∀ {t₀ : ℝ}, 0 < t₀ → t₀ < 1 / 16 → ∀ e ∈ physV (Tw.T.step k hk N₁ ν β p₁) (Tw.T.step k hk N₁ ν β p₁).a₁ (Tw.T.step k hk N₁ ν β p₁).ν Tw.T.t, ∀ u : ℂ,
                  ‖u‖ < 17 / 16 →
                  ‖deriv (markedBlockTerm (Ev zb Y) taylorWeight
                    (liftC (Tw.T.step k hk N₁ ν β p₁).hG' (u • Q (e.1 : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2)))
                    (liftC (Tw.T.step k hk N₁ ν β p₁).hG' ((Tw.T.step k hk N₁ ν β p₁).maskUC z (Q (e.1 : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2))))
                    (e.1 : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2)) 0‖ ≤
                    3 * (energyBdScaled 3 3 2 (compWeight 3 (Tw.T.step k hk N₁ ν β p₁).a₁) k
                      (cK2' 3 3 2 (famConst 3 3 Tw.T.BG₂ Tw.T.κ) * Tw.T.t) Tw.T.t (rho4 3 3 2 Tw.T.BG Tw.T.κ) *
                      Real.exp (-2 * Tw.T.κdec * treeLenCov (Tw.T.step k hk N₁ ν β p₁).G' 1 Y)) /
                      ((lvR Tw.T.κ Tw.T.t (β * 3 ^ k) p₁ / 4) ^ 3 * t₀)) ∧
            ∀ (D : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2)
            (hDh : ∀ y i, D.h y i = ((Tw.T.step k hk N₁ ν β p₁).h₀ i : ℂ))
            (_hD : XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D)
            {x : ((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).E} (_hx : ‖x‖ ≤ p₁)
            (z : Torus 3 (N₁ * 3 ^ Tw.T.m₁ * 3 ^ (k + 1 - (k + 1)))) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1),
            HasDerivAt (fun t : ℂ => ((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
                (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁))
                (((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).markedTangentC z (s : ℂ) t x))
              (-(((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
                deriv (markedBlockTerm (Ev zb Y) taylorWeight
                  (liftC ((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
                    ((s : ℂ) • ((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
                  (liftC ((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
                    (((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
                      (((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)))
                  (rawOf ((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).D')) 0) 0 ∧
            (fderiv ℂ (((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).Phi1C
                (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁)))
                ((s : ℂ) • ((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)
              (((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
                (((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)) =
              -(((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).β : ℂ) * ∑ zb, ∑ Y ∈ 𝒴 zb,
                deriv (markedBlockTerm (Ev zb Y) taylorWeight
                  (liftC ((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
                    ((s : ℂ) • ((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x))
                  (liftC ((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).hG'
                    (((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).maskUC z
                      (((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).shiftUC x)))
                  (rawOf ((Tw.T.step k hk N₁ ν β p₁).withDatum D hDh).D')) 0)) ∧
      -- (iv)
      (∀ S : StepSetting 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁), S = Tw.T.step k hk N₁ ν β p₁ →
      ∃ (Ev : Torus 3 (N₁ * 3 ^ Tw.T.m₁ * 3 ^ (k + 1 - (k + 1))) → Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1)) →
          RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ Tw.T.m₁ (k + 1) → Fin 2 → ℂ) → ℂ)
        (M : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2 → Matrix (S.U × Fin 2) (S.U × Fin 2) ℂ),
        (∀ p q, AnalyticOnNhd ℂ (fun Θ => M Θ p q)
          (XiCRaw S.G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t)) ∧
        (∀ (D' : BgData S.G' 2) (hD' : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
          XiCData S.G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D' → ∀ x : S.E,
          (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M (rawOf D') *ᵥ yhat x) =
            (S.withDatum D' hD').shiftUC x) ∧
        ∀ (z : Torus 3 (N₁ * 3 ^ Tw.T.m₁ * 3 ^ (k + 1 - (k + 1)))) (x : S.E), ‖x‖ ≤ p₁ →
          (∀ (D' : BgData S.G' 2) (hD' : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
            XiCData S.G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D' →
            (S.withDatum D' hD').MarkRealAt Tw.T.t 2 x) ∧
          S.MarkedRootFamily z 1
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) Ev 1 ν Tw.T.t (17 / 16)
            (fun Θ => (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
            (3 * ‖energyBdScaled 3 3 2 (compWeight 3 1) k
                (cK2' 3 3 2 (famConst 3 3 Tw.T.BG₂ Tw.T.κ) * Tw.T.t) Tw.T.t (rho4 3 3 2 Tw.T.BG Tw.T.κ)‖ /
                ((lvR Tw.T.κ Tw.T.t (β * 3 ^ k) p₁ / 4) ^ 3 * (1 / 32)) *
              (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + Tw.T.m₁)) ^ 3) *
              ((nFibre 3 3 : ℝ) * Real.exp ((2 * Tw.T.κdec - 1) * cBr 3 3))) (2 * Tw.T.κdec - 1) ∧
          S.MarkedRootAssembly z 1
            (fun b => polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
              (LocalCover.fam 1 (LocalCover.blockSite k b))) Ev Tw.T.t (17 / 16)
            (fun Θ => (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (M Θ *ᵥ yhat x))
            (|β| * (3 * ‖energyBdScaled 3 3 2 (compWeight 3 1) k
                (cK2' 3 3 2 (famConst 3 3 Tw.T.BG₂ Tw.T.κ) * Tw.T.t) Tw.T.t (rho4 3 3 2 Tw.T.BG Tw.T.κ)‖ /
                ((lvR Tw.T.κ Tw.T.t (β * 3 ^ k) p₁ / 4) ^ 3 * (1 / 32)) *
              (c1 3 3 * (((3 : ℕ) : ℝ) ^ (1 + Tw.T.m₁)) ^ 3) *
              ((nFibre 3 3 : ℝ) * Real.exp ((2 * Tw.T.κdec - 1) * cBr 3 3)))) (2 * Tw.T.κdec - 1)) ∧
      -- (v)
      (∀ S : StepSetting 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁), S = Tw.T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Jr : S.JointRep Tw.T.t (2 * p₁)) (𝒴 : Finset (Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1))))
        (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y) (εU : ℝ),
        εU = β * prop33EpsEtaScaled 3 3 2 Tw.T.m₁ k 1 1 Tw.T.BG Tw.T.BG₂ Tw.T.κ Tw.T.t
          (lvR Tw.T.κ Tw.T.t (β * 3 ^ k) p₁) 0 0 (1 / β) ∧ 0 ≤ εU ∧
        ∃ Aseg : ∀ e : physParam 2 S, e ∈ physFibre S S.a₁ S.ν Tw.T.t → ℝ × ℝ →
            LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit 1 hp).Ωb
              (4 * εU) (2 * Tw.T.κdec - 1) Tw.T.κ0 (2 * (K0 3 3 Tw.T.κ0 + 1)),
          (∀ (e : physParam 2 S) (he : e ∈ physFibre S S.a₁ S.ν Tw.T.t), ∀ p ∈ stepSegments,
            ∀ᵐ x ∂S.nuFl,
              Jr.W1 (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁))
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
                Jr.W2 (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁)) e.2
                  ((e.1 : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
              ∑ y, (Aseg e he p).H y ((S.blockSplit 1 hp).restr x)) ∧
          (∀ g : Fld 3 3 N₁ Tw.T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
            ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
                physFibre S S.a₁ S.ν Tw.T.t,
              ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
                S.WoneC (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁)) p.1 x +
                  S.WtwoC (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁)) g p.2 x =
                ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                  ((S.blockSplit 1 hp).restr x))) ∧
      -- (vi)
      (
            ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ Tw.T.m₁ * 3 ^ (k + 1 - (k + 1))),
                DetExpansionLocC (Tw.T.step k hk N₁ ν β p₁) 1 z Tw.T.t (towerDetRate Tw.T.κ)
                  (towerDetConst Tw.T.κ),
              (∀ z D T', (E z).term D T' = ∑ y ∈ (Tw.T.step k hk N₁ ν β p₁).blockU z,
                detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 Tw.T.BG Tw.T.κ) D y T') ∧
              ∀ z (X : Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1))),
                AnalyticOnNhd ℂ (fun e : rawSub 2 (Tw.T.step k hk N₁ ν β p₁).G' =>
                    (E z).detGrouped (bgOfRaw e.1 e.2) X)
                  (((↑) : rawSub 2 (Tw.T.step k hk N₁ ν β p₁).G' →
                      RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2) ⁻¹'
                    XiCRaw (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t) ∧
                AnalyticOnNhd ℂ (fun e : physParam 2 (Tw.T.step k hk N₁ ν β p₁) =>
                    (E z).detGrouped (bgOfRaw e.1.1 e.1.2) X)
                  (physV (Tw.T.step k hk N₁ ν β p₁) 1 ν Tw.T.t) ∧
                (∀ D : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2,
                  XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D →
                  ‖(E z).detGrouped D X‖ ≤ hullConst 3 3 (towerDetRate Tw.T.κ) (towerDetConst Tw.T.κ) *
                    Real.exp (-hullRate 3 3 (towerDetRate Tw.T.κ) * sizeJ 1 (k + 1) X)) ∧
                (∀ D D₂ : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2,
                  XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D →
                  XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D₂ →
                  (∀ v ∈ X, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
                    (E z).detGrouped D X = (E z).detGrouped D₂ X)) ∧
      -- (vii) renormalization lane
      (∃ F : RawData 3 3 (N₁ * 3 ^ Tw.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
          ((lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)).Ω 1 → ℂ),
        IsRenSol (N := 2) (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1) ν Tw.t Tw.t Tw.r₀
          (8 * Tw.t) F ∧
        (∀ z : Torus 3 (N₁ * 3 ^ Tw.m₁ * 3 ^ (k + 1 - (k + 1))),
          HasLocPrinciple (N := 2) (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁))
            (XiCOneReal (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1) ν Tw.t) Tw.r₀
            (renYs (renCube (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁))
                (X1 (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1 k (fam 1 (blockSite k z))))
              (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1
              (X1 (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1 k (fam 1 (blockSite k z))))
            (renDY (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1) (3 / 2 * Tw.κdec) 1
            (fun D _ => bgClass (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) ν
              (renCK 3 3 2 Tw.BG Tw.κ * Tw.t) D)
            (fun D φ ξ => renC1On (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1) ν Tw.t
              (blockSites 3 3 N₁ Tw.m₁ (k + 1) k z) D.Ψ D.h φ ξ)
            (fun D _ => bgFieldC (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1) ν
              (bgC0 3 3 2) D)) ∧
        (∀ z : Torus 3 (N₁ * 3 ^ Tw.m₁ * 3 ^ (k + 1 - (k + 1))),
          HasLocPrinciple (N := 2) (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁))
            (XiCOneReal (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1) ν Tw.t) Tw.r₀
            (renYs (renCube (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁))
                (X1 (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1 k (fam 1 (blockSite k z))))
              (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1
              (X1 (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1 k (fam 1 (blockSite k z))))
            (renDY (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1) (3 / 2 * Tw.κdec) 1
            (fun _ ξ => pertClass (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁))
              (renCK 3 3 2 Tw.BG Tw.κ * (cK2 3 3 2 * (8 * Tw.t * ‖ξ‖)))
              (bgK1 3 3 2 * (xiC1 3 * Tw.t) + renCK 3 3 2 Tw.BG Tw.κ * cK2 3 3 2 * (8 * Tw.t) * Tw.r₀
                + 2) (renMassU ν ξ))
            (fun _ v ξ => renC2On (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1)
              (blockSites 3 3 N₁ Tw.m₁ (k + 1) k z) ξ (renMassU ν ξ) v.2 v.1)
            (fun D ξ => ((F ((D.Ψ, D.h), ξ)).1,
              bgMultC (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
                (F ((D.Ψ, D.h), ξ)).2))) ∧
        (∀ p : (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)).Ω 1 × Fin 2,
          HasLocPrinciple (N := 2) (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁))
            (XiCOneReal (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1) ν Tw.t) Tw.r₀
            (renYs (renCube (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁))
                (X1 (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1 k
                  (fam 1 (p.1 : CTorus 3 3 N₁ Tw.m₁ (k + 1)))))
              (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1
              (X1 (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1 k
                (fam 1 (p.1 : CTorus 3 3 N₁ Tw.m₁ (k + 1)))))
            (renDY (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1) (3 / 2 * Tw.κdec) 1
            (fun _ ξ => {v | SupBounds (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) v
              (renCK 3 3 2 Tw.BG Tw.κ * (cK2 3 3 2 * (8 * Tw.t * ‖ξ‖)))})
            (fun _ v _ => v p) (fun D ξ => (F ((D.Ψ, D.h), ξ)).1))) ∧
      (∀ {εR : ℝ}, εR ≤ Tw.r₀ → ∀ z : Torus 3 (N₁ * 3 ^ Tw.m₁ * 3 ^ (k + 1 - (k + 1))),
      ∃ term, IsLocExp (N := 2) (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁))
        (XiCOneReal (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1) ν Tw.t) εR
        (renYs (renCube (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁))
            (X1 (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1 k (fam 1 (blockSite k z))))
          (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1
          (X1 (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1 k (fam 1 (blockSite k z))))
        (renDY (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1) (3 / 2 * Tw.κdec)
        (1 * ((3 + 6) * (renCK 3 3 2 Tw.BG Tw.κ * Tw.t) ^ 2 *
          blockWeight (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (blockSites 3 3 N₁ Tw.m₁ (k + 1) k z)) *
          εR ^ 1)
        (fun D ξ => renC1On (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1) ν Tw.t
          (blockSites 3 3 N₁ Tw.m₁ (k + 1) k z) D.Ψ D.h
          (bgFieldC (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D) ξ) term) ∧
      (∀ {εR : ℝ}, 0 ≤ εR → εR ≤ Tw.r₀ → ∀ z : Torus 3 (N₁ * 3 ^ Tw.m₁ * 3 ^ (k + 1 - (k + 1))),
      ∃ F : RawData 3 3 (N₁ * 3 ^ Tw.m₁) (k + 1) 2 × (Fin 3 → ℂ) →
          ((lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)).Ω 1 × Fin 2 → ℂ) ×
            ((lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)).Ω 1 → ℂ),
        IsRenSol (N := 2) (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1) ν Tw.t Tw.t Tw.r₀
          (8 * Tw.t) F ∧
        ∃ term, IsLocExp (N := 2) (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁))
        (XiCOneReal (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1) ν Tw.t) εR
        (renYs (renCube (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁))
            (X1 (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1 k (fam 1 (blockSite k z))))
          (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1
          (X1 (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1 k (fam 1 (blockSite k z))))
        (renDY (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) 1) (3 / 2 * Tw.κdec)
        (1 * (17 / 32 * ((2 : ℕ) * ((3 + (bgK1 3 3 2 * (xiC1 3 * Tw.t) +
          renCK 3 3 2 Tw.BG Tw.κ * cK2 3 3 2 * (8 * Tw.t) * Tw.r₀ + 2)) *
          (renCK 3 3 2 Tw.BG Tw.κ * cK2 3 3 2 * (8 * Tw.t)) ^ 2)) *
          blockWeight (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (blockSites 3 3 N₁ Tw.m₁ (k + 1) k z)) *
          εR ^ 2)
        (fun D ξ => renC2On (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1)
          (blockSites 3 3 N₁ Tw.m₁ (k + 1) k z) ξ (renMassU ν ξ)
          (bgMultC (lvTop N₁ Tw.m₁ k (rhoSep Tw.m₁)) (compWeight 3 1) ν (bgC0 3 3 2) D +
            (F ((D.Ψ, D.h), ξ)).2) (F ((D.Ψ, D.h), ξ)).1) term)
      ) ∧
      (
    ∀ (S : StepSetting 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁)), S = Tw.T.step k hk N₁ ν β p₁ →
    ∀ (hp : 0 < S.p₁),
    ∃ (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
        ℂ → (RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ Tw.T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (𝒴 : Finset (Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1))))
      (Tt : Set (CTorus 3 3 N₁ Tw.T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
        ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
        (RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ Tw.T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
      (hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y),
      (∀ x w σ Θ, val x w σ Θ =
        (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν Tw.T.t S.hG'
          ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν Tw.T.t)) taylorWeight x.1 w.1 σ Θ.1 +
        (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ Tw.T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
          dirTermSrc (hatFun S.G' S.a₁ S.ν Tw.T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
            (onXi S.G' S.a₁ S.ν Tw.T.t
              (fun D ψ' => svec (stepG 3 3 N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁))
                (flFieldOne S.G' (stepG 3 3 N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) Tw.T.BG₂ Tw.T.κ S.a₁ S.ν D ψ')
                  s.1 s.2)))
            (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
      ∃ εU : ℝ,
      εU = β * prop33EpsEtaScaled 3 3 2 Tw.T.m₁ k 1 1 Tw.T.BG Tw.T.BG₂ Tw.T.κ Tw.T.t
        (lvR Tw.T.κ Tw.T.t (β * 3 ^ k) p₁) 0 0 (1 / β) ∧ 0 < εU ∧
      4 * εU ≤ CE₂ * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
        CF₂ * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
      (∀ g : Fld 3 3 N₁ Tw.T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ Tw.T.m₁ (k + 1) 2 →
        ∃ BR : StepActivityBound S (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁)) g,
        ∃ BC : StepActivityBoundC S (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁)) g,
          BR.m₀ = 1 ∧ BC.m₀ = 1 ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
          HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
          HEq BR.BS (S.blockSplit 1 hp) ∧ HEq BC.BS BR.BS ∧
          BR.κ0 = Tw.T.κ0 ∧ BC.κ0 = Tw.T.κ0 ∧ BR.κ' = Tw.T.κ' ∧ BC.κ' = Tw.T.κ' ∧
          BR.κH = 2 * Tw.T.κdec - 1 ∧ BC.κH = BR.κH ∧
          BR.Kc = 2 * (K0 3 3 Tw.T.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧ BR.εH = 4 * εU) ∧
      (∃ Jr : S.JointRep Tw.T.t (2 * p₁),
        ∃ Aseg : ∀ e : physParam 2 S, e ∈ physFibre S S.a₁ S.ν Tw.T.t → ℝ × ℝ →
          LabelAct ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) (S.blockSplit 1 hp).Ωb
            (4 * εU) (2 * Tw.T.κdec - 1) Tw.T.κ0 (2 * (K0 3 3 Tw.T.κ0 + 1)),
        (∀ (e : physParam 2 S) (he : e ∈ physFibre S S.a₁ S.ν Tw.T.t), ∀ p ∈ stepSegments,
          ∀ᵐ x ∂S.nuFl,
            Jr.W1 (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁))
                ((e.1 : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
              Jr.W2 (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁)) e.2
                ((e.1 : RawData 3 3 (N₁ * 3 ^ Tw.T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
            ∑ y, (Aseg e he p).H y ((S.blockSplit 1 hp).restr x)) ∧
        (∀ g : Fld 3 3 N₁ Tw.T.m₁ (k + 1) 2, ∑ x, ∑ i, ‖g x i‖ < 1 →
          ∃ he : ((⟨rawOf S.D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) ∈
              physFibre S S.a₁ S.ν Tw.T.t,
            ∀ p ∈ stepSegments, ∀ᵐ x ∂S.nuFl,
              S.WoneC (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁)) p.1 x +
                S.WtwoC (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁)) g p.2 x =
              ∑ y, (Aseg (⟨rawOf S.D', rawOf_mem_rawSub _⟩, g) he p).H y
                ((S.blockSplit 1 hp).restr x))) ∧
      (0 < εU ∧ ∃ A₀ : ℂ → LabelAct (thickLabels 𝒴 hdom) (S.blockSplit 1 hp).Ωb
          εU (2 * Tw.T.κdec - 1) Tw.T.κ0 (K0 3 3 Tw.T.κ0 + 1),
        (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (A₀ z).H y Φ =
          Tt y.1 (z • S.hatOf 1 p₁ hp Φ, z • S.hatOf 1 p₁ hp Φ)
            (z • S.hatOf 1 p₁ hp Φ, z • S.hatOf 1 p₁ hp Φ) 1
            (rawOf S.D', (0 : CTorus 3 3 N₁ Tw.T.m₁ (k + 1) → Fin 2 → ℂ))) ∧
        (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (A₀ z).H y Φ = 0) ∧
        ∀ g : Fld 3 3 N₁ Tw.T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ Tw.T.m₁ (k + 1) 2 →
        ∃ Ag : ℂ → LabelAct (thickLabels 𝒴 hdom) (S.blockSplit 1 hp).Ωb
            εU (2 * Tw.T.κdec - 1) Tw.T.κ0 (K0 3 3 Tw.T.κ0 + 1),
          (∀ z : ℂ, ‖z‖ < 3 / 2 → ∀ y Φ, (Ag z).H y Φ =
            Tt y.1 (z • S.hatOf 1 p₁ hp Φ, z • S.hatOf 1 p₁ hp Φ)
              (z • S.hatOf 1 p₁ hp Φ, z • S.hatOf 1 p₁ hp Φ) 1
              (rawOf S.D', fun y i => g y i / (S.β : ℂ))) ∧
          (∀ z : ℂ, 3 / 2 ≤ ‖z‖ → ∀ y Φ, (Ag z).H y Φ = 0) ∧
          ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
            ∑ y, (((A₀ 1).sub (A₀ (t : ℂ))).sum (Ag (t : ℂ))).H y
                (((S.blockSplit 1 hp).restr x)) =
              S.WoneC (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁)) 1 x +
              S.WtwoC (zeroClass 3 3 N₁ Tw.T.m₁ k 2 (rhoSep Tw.T.m₁)) g t x)
      ) ∧
      (
    ∃ E : ∀ z : Torus 3 (N₁ * 3 ^ Tw.T.m₁ * 3 ^ (k + 1 - (k + 1))),
        DetExpansionLocC (Tw.T.step k hk N₁ ν β p₁) 1 z Tw.T.t (towerDetRate Tw.T.κ)
          (towerDetConst Tw.T.κ),
      (∀ z D T', (E z).term D T' = ∑ y ∈ (Tw.T.step k hk N₁ ν β p₁).blockU z,
        detActivityBg 1 (compWeight 3 1) 1 ν (rho4 3 3 2 Tw.T.BG Tw.T.κ) D y T') ∧
      (∀ z (D : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2),
        XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D →
        ∑ Y ∈ renYs (renCube (lvTop N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁))
              (X1 (lvTop N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) 1 k (fam 1 (blockSite k z))))
            (lvTop N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) 1
            (X1 (lvTop N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) 1 k (fam 1 (blockSite k z))),
          renFibreTerm (lvTop N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) 1
            (X1 (lvTop N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) 1 k (fam 1 (blockSite k z)))
            ((E z).detGrouped D) Y =
          rootTrace (Tw.T.step k hk N₁ ν β p₁).G' (Tw.T.step k hk N₁ ν β p₁).a 1 ν
            (unitQ (Tw.T.step k hk N₁ ν β p₁).G') (unitP (Tw.T.step k hk N₁ ν β p₁).G')
            ((Tw.T.step k hk N₁ ν β p₁).blockU z) (fun _ => 1)
            (svec (Tw.T.step k hk N₁ ν β p₁).G' (bgFieldC (Tw.T.step k hk N₁ ν β p₁).G'
              (Tw.T.step k hk N₁ ν β p₁).a ν (bgC0 3 3 2) D))
            (bgMultC (Tw.T.step k hk N₁ ν β p₁).G' (Tw.T.step k hk N₁ ν β p₁).a ν (bgC0 3 3 2) D)) ∧
      (∀ z (D : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2),
        XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D →
        ∀ Y : Finset (CTorus 3 3 N₁ Tw.T.m₁ (k + 1)),
          ‖renFibreTerm (lvTop N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) 1
              (X1 (lvTop N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) 1 k (fam 1 (blockSite k z)))
              ((E z).detGrouped D) Y‖ ≤
            hullConst 3 3 (towerDetRate Tw.T.κ) (towerDetConst Tw.T.κ) *
              Real.exp (c1 3 3 * Real.log 2) * Real.exp (hullRate 3 3 (towerDetRate Tw.T.κ)) *
              Real.exp (-(3 / 2 * Tw.T.κdec) *
                renDY (lvTop N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) 1 Y)) ∧
      (∀ z (D D₂ : BgData (Tw.T.step k hk N₁ ν β p₁).G' 2),
        XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D →
        XiCData (Tw.T.step k hk N₁ ν β p₁).G' (compWeight 3 1) ν (k + 1) 1 Tw.T.t D₂ →
        ∀ Y : Finset (CTorus 3 3 N₁ Tw.T.m₁ (k + 1)),
          (∀ v ∈ Y, D.Ψ v = D₂.Ψ v ∧ D.h v = D₂.h v) →
          renFibreTerm (lvTop N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) 1
              (X1 (lvTop N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) 1 k (fam 1 (blockSite k z)))
              ((E z).detGrouped D) Y =
            renFibreTerm (lvTop N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) 1
              (X1 (lvTop N₁ Tw.T.m₁ k (rhoSep Tw.T.m₁)) 1 k (fam 1 (blockSite k z)))
              ((E z).detGrouped D₂) Y)
      )
  := by
  classical
  have hT' : stepHullMin ≤ κmin := stepHullMin_le_renDetFibreMin.trans hT
  obtain ⟨hull, hC, β₁, CE, CF, CE', CF', h3, hCE, hCF, hCE', hCF', H⟩ :=
    stepPieces_fromTowerRenSol Tw.toStepTowerRenSol hT' hA p
  obtain ⟨β₂, CE₂, CF₂, h2, hCE₂, hCF₂, H2⟩ := sourceWitness_fromTower Tw.T hA p
  refine ⟨hull, hC, max β₁ β₂, CE, CF, CE', CF', CE₂, CF₂, le_trans h3 (le_max_left _ _),
    hCE, hCF, hCE', hCF', hCE₂, hCF₂, ?_⟩
  intro k hk N₁ _ h3N hN ν hν0 hν β hβ p₁ hp0 hp₁
  have hβ1 : β₁ ≤ β := le_trans (le_max_left _ _) hβ
  have hβ2 : β₂ ≤ β := le_trans (le_max_right _ _) hβ
  obtain ⟨hne, hall⟩ := H k hk N₁ h3N hN ν hν0 hν β hβ1 p₁ hp0 hp₁
  refine ⟨hne, fun D => ?_⟩
  obtain ⟨hi, hrest⟩ := hall D
  exact ⟨⟨hi.2, hrest⟩, H2 k hk N₁ h3N hN ν hν0 hν β hβ2 p₁ hp0 hp₁ D,
    renDetFibre_tower Tw.T hT k hk N₁ h3N hN hν0.le hν β p₁⟩

end Joint

end Balaban.Inhabited
