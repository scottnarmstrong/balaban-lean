/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerDataOrigin
public import Balaban.Fluctuation.RootPavingMap

/-!
# The gap-scale clause at the tower, root and site at an arbitrary cell (blocker 7)

`towerGapScale_resum_fromTowerG_cell`: `towerGapScale_resum_fromTowerG` for the root of the cell `a`
and the site `a * aK` of every torus of the family, where `a ∈ ℤ^d` lies in the quarter box
`4 |a_μ| < K ℓ` of every torus (the hypothesis of Root-F's two-torus clause).  The root is the point
`a L^{1+m₁}` of the coarse torus and the site is the corner `a aK` of the cell; their cells are
`a`, and the box maps of the root and the site tori carry them to the corresponding root and
site of the canonical torus (`root_cell_eq`, `root_box_eq`, `site_cell_eq`, `site_box_eq`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField Balaban.SmallField.Def6
  Balaban.Background Balaban.Analysis Balaban.Polymer Balaban.Multiscale MeasureTheory Metric
  Balaban.Localization.DecEquiv Balaban.Inhabited Balaban.Inhabited.LevelStep

section Cell

/-- The cell index of the point `w D` of the torus `ℤ/(D K)` is `w` modulo `K`. -/
theorem cellIndex_intCast_mul {n D K : ℕ} [NeZero n] (hD : 0 < D) (h : n = D * K) (w : ℤ) :
    ((((w * (D : ℤ) : ℤ) : ZMod n).val / D : ℕ) : ZMod K) = (w : ZMod K) := by
  subst h
  have hK : 0 < K := Nat.pos_of_ne_zero fun h0 => by simp [h0] at *
  have h2 : 0 ≤ w % (K : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hK.ne')
  have h1 : (w * (D : ℤ)) % ((D * K : ℕ) : ℤ) = (D : ℤ) * (w % (K : ℤ)) := by
    push_cast
    rw [mul_comm w, Int.mul_emod_mul_of_pos _ _ (by exact_mod_cast hD)]
  have hv : ((((w * (D : ℤ) : ℤ) : ZMod (D * K)).val : ℕ) : ℤ) =
      (D : ℤ) * (w % (K : ℤ)) := by
    rw [ZMod.val_intCast, h1]
  have hv' : (((w * (D : ℤ) : ℤ) : ZMod (D * K)).val) = D * (w % (K : ℤ)).toNat := by
    have : (((w % (K : ℤ)).toNat : ℕ) : ℤ) = w % (K : ℤ) := Int.toNat_of_nonneg h2
    have h5 : ((((w * (D : ℤ) : ℤ) : ZMod (D * K)).val : ℕ) : ℤ) =
        ((D * (w % (K : ℤ)).toNat : ℕ) : ℤ) := by
      rw [hv]; push_cast; rw [this]
    exact_mod_cast h5
  rw [hv', Nat.mul_div_cancel_left _ hD]
  have : (((w % (K : ℤ)).toNat : ℕ) : ℤ) = w % (K : ℤ) := Int.toNat_of_nonneg h2
  have h4 : ((((w % (K : ℤ)).toNat : ℕ) : ZMod K)) = (((w % (K : ℤ) : ℤ)) : ZMod K) := by
    rw [← this]; simp
  rw [h4, ZMod.intCast_mod]

/-- Centred representatives of a point in the quarter box survive the box maps. -/
theorem valMinAbs_mul_cell {n D K : ℕ} [NeZero n] (hD : 0 < D) (h : n = D * K) (hK : 2 ≤ K)
    {a : ℤ} (ha : 4 * |a| < (K : ℤ)) :
    (((a * (D : ℤ) : ℤ) : ZMod n)).valMinAbs = a * (D : ℤ) := by
  subst h
  have hn : 4 * a.natAbs < K := by
    rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  refine valMinAbs_intCast_of_abs_le (r := (a.natAbs * D)) ?_ ?_
  · have h1 : 2 * a.natAbs + 2 ≤ K := by omega
    have : D * (2 * a.natAbs + 2) ≤ D * K := Nat.mul_le_mul_left D h1
    nlinarith
  · rw [abs_mul, Int.abs_eq_natAbs, Nat.abs_cast]
    push_cast
    exact le_refl _

set_option hygiene false in
local notation "zrP[" a "," n "," m "," k "]" =>
  (fun μ => ((a μ * ((L ^ (1 + m) : ℕ) : ℤ) : ℤ) : ZMod (n * L ^ m * L ^ (k + 1 - (k + 1)))) :
    RootIdx d L n m (k + 1))
set_option hygiene false in
local notation "xsP[" a "," n "," m "," k "]" =>
  (fun μ => ((a μ * ((cellSide L 1 m (k + 1) : ℕ) : ℤ) : ℤ) : ZMod ((n * L ^ m) * L ^ (k + 1))) :
    CTorus d L n m (k + 1))

section Points

variable {d L : ℕ} [NeZero L]

theorem rootIdx_cell_val {n m k : ℕ} [NeZero n] (z : RootIdx d L n m (k + 1)) (μ : Fin d) :
    (((rootCube (m₀ := 1) z).1 μ).val / cellSide L 1 m (k + 1)) = (z μ).val / L ^ (1 + m) := by
  have hc : cellSide L 1 m (k + 1) = L ^ (k + 1) * L ^ (1 + m) := by
    unfold cellSide; rw [← pow_add]; congr 1; omega
  have h0 : 0 < L ^ (k + 1) := Nat.pos_of_ne_zero (NeZero.ne _)
  rw [rootCube, cbase_val, rootSite_val, hc, Nat.mul_div_mul_left _ _ h0]
  exact Nat.mul_div_cancel_left _ (Nat.mul_pos h0 (Nat.pos_of_ne_zero (NeZero.ne _)))

theorem root_side_eq {n m k K : ℕ}
    (hside : (n * L ^ m) * L ^ (k + 1) = cellSide L 1 m (k + 1) * K) :
    n * L ^ m * L ^ (k + 1 - (k + 1)) = L ^ (1 + m) * K := by
  have hc : cellSide L 1 m (k + 1) = L ^ (k + 1) * L ^ (1 + m) := by
    unfold cellSide; rw [← pow_add]; congr 1; omega
  have h0 : 0 < L ^ (k + 1) := Nat.pos_of_ne_zero (NeZero.ne _)
  rw [hc] at hside
  rw [Nat.sub_self, pow_zero, mul_one]
  have : L ^ (k + 1) * (n * L ^ m) = L ^ (k + 1) * (L ^ (1 + m) * K) := by
    rw [mul_comm (L ^ (k + 1)), hside]; ring
  exact Nat.eq_of_mul_eq_mul_left h0 this

/-- The root of the cell `a` lies in the cell `a`. -/
theorem root_cell_eq {n m k K : ℕ} [NeZero n] [NeZero K]
    (hside : (n * L ^ m) * L ^ (k + 1) = cellSide L 1 m (k + 1) * K) (hK : 2 ≤ K)
    {a : Fin d → ℤ} (ha : ∀ μ, 4 * |a μ| < (K : ℤ)) :
    (fun μ => ((((rootCube (m₀ := 1) (zrP[a, n, m, k])).1 μ).val / cellSide L 1 m (k + 1) : ℕ) :
      ZMod K).valMinAbs) = a := by
  funext μ
  have hD : 0 < L ^ (1 + m) := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn := root_side_eq hside
  rw [rootIdx_cell_val]
  have := cellIndex_intCast_mul hD hn (a μ)
  rw [this]
  exact valMinAbs_intCast_of_abs_le (r := (a μ).natAbs) (by
    have : 4 * (a μ).natAbs < K := by
      have := ha μ
      rcases abs_cases (a μ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    omega) (by rw [Int.abs_eq_natAbs])

/-- The roots of two tori correspond under the box maps. -/
theorem root_box_eq {n n' m k K : ℕ} [NeZero n] [NeZero K]
    (hside : (n * L ^ m) * L ^ (k + 1) = cellSide L 1 m (k + 1) * K) (hK : 2 ≤ K)
    {a : Fin d → ℤ}
    (ha : ∀ μ, 4 * |a μ| < (K : ℤ)) :
    (zrP[a, n', m, k]) = boxMap (n * L ^ m * L ^ (k + 1 - (k + 1)))
      (n' * L ^ m * L ^ (k + 1 - (k + 1))) (zrP[a, n, m, k]) := by
  funext μ
  have hD : 0 < L ^ (1 + m) := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn := root_side_eq hside
  have := valMinAbs_mul_cell hD hn hK (ha μ)
  simp only [boxMap]
  rw [this]

/-- The site `a aK` lies in the cell `a`. -/
theorem site_cell_eq {n m k K : ℕ} [NeZero n] [NeZero K]
    (hside : (n * L ^ m) * L ^ (k + 1) = cellSide L 1 m (k + 1) * K) (hK : 2 ≤ K)
    {a : Fin d → ℤ} (ha : ∀ μ, 4 * |a μ| < (K : ℤ)) :
    (fun μ => (((((xsP[a, n, m, k]) μ).val / cellSide L 1 m (k + 1) : ℕ) : ZMod K).valMinAbs)) =
      a := by
  funext μ
  have hD : 0 < cellSide L 1 m (k + 1) := cellSide_pos _ _ _
  have := cellIndex_intCast_mul hD hside (a μ)
  dsimp only
  rw [this]
  exact valMinAbs_intCast_of_abs_le (r := (a μ).natAbs) (by
    have : 4 * (a μ).natAbs < K := by
      have := ha μ
      rcases abs_cases (a μ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    omega) (by rw [Int.abs_eq_natAbs])

/-- The sites of two tori correspond under the box maps. -/
theorem site_box_eq {n n' m k K : ℕ} [NeZero n] [NeZero K]
    (hside : (n * L ^ m) * L ^ (k + 1) = cellSide L 1 m (k + 1) * K) (hK : 2 ≤ K)
    {a : Fin d → ℤ}
    (ha : ∀ μ, 4 * |a μ| < (K : ℤ)) :
    (xsP[a, n', m, k]) = boxMap ((n * L ^ m) * L ^ (k + 1)) ((n' * L ^ m) * L ^ (k + 1))
      (xsP[a, n, m, k]) := by
  funext μ
  have hD : 0 < cellSide L 1 m (k + 1) := cellSide_pos _ _ _
  have := valMinAbs_mul_cell hD hside hK (ha μ)
  simp only [boxMap]
  rw [this]

end Points

section Tower

set_option hygiene false in
local notation "ST[" n "]" => StepTowerG.step T k hk n ν β p₁
set_option hygiene false in
local notation "SA[" ℓ "]" => StepTowerG.step T k hk (N₁ ℓ) ν β p₁
set_option hygiene false in
local notation "bm[" ℓ "," ℓ' "]" =>
  boxMap ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)) ((N₁ ℓ' * L ^ T.m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "aK" => cellSide L 1 T.m₁ (k + 1)
set_option hygiene false in
local notation "zrA[" ℓ "]" => zrP[a, N₁ ℓ, T.m₁, k]
set_option hygiene false in
local notation "xsA[" ℓ "]" => xsP[a, N₁ ℓ, T.m₁, k]
set_option hygiene false in
local notation "cellsOf[" ℓ "," X "]" => {x : CTorus d L (N₁ ℓ) T.m₁ (k + 1) |
  (fun μ => (((((x μ).val / cellSide L 1 T.m₁ (k + 1) : ℕ)) : ZMod (K ℓ))).valMinAbs) ∈
    (↑X : Set (Fin d → ℤ))}

open Classical in
/-- **The gap-scale clause at the tower for the root and the site at the cell `a`.**
`towerGapScale_resum_fromTowerG` with the root of the cell `a` and the site `a * aK` (the corner of
the cell `a`) of every torus, for `a` in the quarter box of every torus of the family: the root cube
and the site lie in the cell `a`, and both are carried to the corresponding root and site of the
canonical torus by the box maps. -/
theorem towerGapScale_resum_fromTowerG_cell {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1)
    (hhull : 2 * d * L * (1 + collarB d L) * (3 / 2 * T.κdec + c1 d L * Real.log 2) +
      Real.log 2 + 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ) ≤ T.κ) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {CR s : ℝ} (hCR : 0 < CR) (hs0 : 0 < s) (hs : s < 1 / 2) :
    ∃ (β₀ CE CF : ℝ), 3 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (ν : ℝ) (_ : 0 < ν) (_ : ν * (L : ℝ) ^ (2 * (k + 1)) ≤ 1) (β : ℝ)
        (_ : β₀ ≤ β) (p₁ : ℝ) (_ : 0 < p₁) (_ : p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))))
        (q : ℝ) (_ : 0 < q) (_ : q ≤ 1),
      ∃ (e0 dz c : ∀ (n : ℕ) [NeZero n], L ^ T.m₀ ∣ n → 5 < n → StepScaleDataG T k hk n ν β p₁ →
            RootIdx d L n T.m₁ (k + 1) → physParam N (ST[n]) →
            Finset (CubeB (d := d) (L := L) (N₁ := n) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ)
        (mObs : ∀ (n : ℕ) [NeZero n], L ^ T.m₀ ∣ n → 5 < n → StepScaleDataG T k hk n ν β p₁ →
            CTorus d L n T.m₁ (k + 1) → Fin N → physParam N (ST[n]) →
            Finset (CubeB (d := d) (L := L) (N₁ := n) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ) → ℂ) (B : ℝ),
        0 ≤ B ∧
        (∀ (n : ℕ) [NeZero n] (h3 : L ^ T.m₀ ∣ n) (h5' : 5 < n) (Dn : StepScaleDataG T k hk n ν β p₁),
          (∀ (D' : BgData (ST[n]).G' N) (hDh : ∀ y i, D'.h y i = ((ST[n]).h₀ i : ℂ)),
            XiCData (ST[n]).G' (ST[n]).a (ST[n]).ν (k + 1) 1 T.t D' →
            ∀ g : Fld d L n T.m₁ (k + 1) N, ∑ x, ∑ i, ‖g x i‖ < q →
              ((ST[n]).withDatum D' hDh).TstepC (zeroClass d L n T.m₁ k N (rhoSepG d L T.m₁)) g =
                Complex.exp (-((ST[n]).β : ℂ) * ((ST[n]).withDatum D' hDh).AnewC -
                  (((ST[n]).withDatum D' hDh).Eppp
                      (zeroClass d L n T.m₁ k N (rhoSepG d L T.m₁)) : ℂ) *
                    (((ST[n]).withDatum D' hDh).nU : ℂ) +
                  FcompAtC (zeroClass d L n T.m₁ k N (rhoSepG d L T.m₁)).m₀
                    (zeroClass d L n T.m₁ k N (rhoSepG d L T.m₁)).Tm (ST[n]).a (ST[n]).ν
                    (Nat.le_succ k) ((ST[n]).withDatum D' hDh).psiKdC g +
                  ∑ z : RootIdx d L n T.m₁ (k + 1), ∑ C,
                    e0 n h3 h5' Dn z ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N (ST[n]).G'),
                      (0 : CTorus d L n T.m₁ (k + 1) → Fin N → ℂ)) C +
                  ∑ y : CTorus d L n T.m₁ (k + 1), ∑ i : Fin N, g y i *
                    ∑ T', mObs n h3 h5' Dn y i
                      ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub N (ST[n]).G'), g) T')) ∧
          ∀ z θ C, e0 n h3 h5' Dn z θ C = dz n h3 h5' Dn z θ C + c n h3 h5' Dn z θ C) ∧
        ∀ {ι G : Type*} (N₁ : ι → ℕ) [∀ ℓ, NeZero (N₁ ℓ)] (h3N : ∀ ℓ, L ^ T.m₀ ∣ N₁ ℓ)
          (h5 : ∀ ℓ, 5 < N₁ ℓ) (D : ∀ ℓ, StepScaleDataG T k hk (N₁ ℓ) ν β p₁)
          (K : ι → ℕ) [∀ ℓ, NeZero (K ℓ)] (_ : ∀ ℓ, 2 ≤ K ℓ)
          (_ : ∀ ℓ, (N₁ ℓ * L ^ T.m₁) * L ^ (k + 1) = aK * K ℓ)
          (a : Fin d → ℤ) (_ : ∀ ℓ μ, 4 * |a μ| < (K ℓ : ℤ))
          (P : ι → Finset (Finset (Fin d → ℤ))) (Q : ι → Finset (Fin d → ℤ) → Prop)
          (can : Finset (Fin d → ℤ) → ι) (τ : ι → Finset (Fin d → ℤ) → ℕ)
          (_ : ∀ ℓ X, X ∈ P ℓ ↔ ∃ Y, IsAnimal (blockGraph d (K ℓ)) Y ∧
            X = Y.image (fun b μ => (b μ).valMinAbs))
          (_ : ∀ ℓ X, Q ℓ X ↔ ∀ x ∈ X, ∀ μ, (x μ).natAbs ≤ K ℓ / 4)
          (_ : ∀ ℓ X, τ ℓ X = K ℓ / 4 - X.sup (fun x => Finset.univ.sup fun μ => (x μ).natAbs))
          (_ : ∀ ℓ X, X ∈ P ℓ → Q ℓ X → K ℓ ≤ K (can X))
          (Ycub : ∀ ℓ, Finset (Fin d → ℤ) →
            Finset (CubeB (d := d) (L := L) (N₁ := N₁ ℓ) (m₁ := T.m₁) (K := k + 1) 1 (k + 1)
              Set.univ))
          (_ : ∀ ℓ X, sitesOf (Ycub ℓ X) = cellsOf[ℓ, X])
          (iy : Fin N)
          {Dset : Set G} (θ : ∀ ℓ, G → physParam N (SA[ℓ]))
          (_ : ∀ ℓ, ∀ g ∈ Dset, θ ℓ g ∈ physVq (SA[ℓ]) (SA[ℓ]).a₁ (SA[ℓ]).ν T.t q)
          (Dat : ∀ ℓ, G → BgData (SA[ℓ]).G' N)
          (_ : ∀ ℓ, ∀ g ∈ Dset, XiCData (SA[ℓ]).G' (compWeight L 1) ν (k + 1) 1 T.t (Dat ℓ g))
          (_ : ∀ ℓ, ∀ g ∈ Dset,
            ((θ ℓ g).1 : RawData d L (N₁ ℓ * L ^ T.m₁) (k + 1) N) = rawOf (Dat ℓ g))
          (_ : ∀ ℓ X g, 300 * L + 100 ≤ K ℓ → X ∈ P ℓ → Q ℓ X →
            (∀ c ∈ X, ∀ c' ∈ X, ∀ μ, |c μ - c' μ| ≤ (((K ℓ - 36) / 25 - L : ℕ) : ℤ)) →
            L ≤ τ ℓ X → a ∈ X → g ∈ Dset →
            ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
            ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
            (∀ x ∈ LocalCover.nbhd 1 xsA[ℓ] ∪ sitesOf (Ycub ℓ X), ∀ μ,
              |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
            RawBoxAgree {w | InBox d (Ds + (Ds + 1) / 4 + 3 * L ^ (k + 1))
                ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)) w}
              (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)))))
                ((θ ℓ g).1 : RawData d L (N₁ ℓ * L ^ T.m₁) (k + 1) N))
              (symRaw (Equiv.addRight
                (fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ T.m₁) * L ^ (k + 1)))))
                ((θ (can X) g).1 : RawData d L (N₁ (can X) * L ^ T.m₁) (k + 1) N)))
          (_ : ∀ ℓ X g, 300 * L + 100 ≤ K ℓ → X ∈ P ℓ → Q ℓ X →
            (∀ c ∈ X, ∀ c' ∈ X, ∀ μ, |c μ - c' μ| ≤ (((K ℓ - 36) / 25 - L : ℕ) : ℤ)) →
            L ≤ τ ℓ X → a ∈ X → g ∈ Dset →
            ∀ Ds : ℕ, Ds = aK * ((K ℓ - 26) / 25 + 1) - 1 →
            ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
            (∀ x ∈ LocalCover.nbhd 1 xsA[ℓ] ∪ sitesOf (Ycub ℓ X), ∀ μ,
              |(x μ).valMinAbs + z μ| ≤ ((Ds + (Ds + 1) / 4 : ℕ) : ℤ)) →
            ∀ x, InBox d (Ds + (Ds + 1) / 4) ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1))
              (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)))) →
            ∀ i, (θ (can X) g).2 (bm[ℓ, can X] (x + fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ T.m₁) *
              L ^ (k + 1)))) - fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ T.m₁) * L ^ (k + 1))))
              i = (θ ℓ g).2 x i)
          (_ : ∀ ℓ X g, 300 * L + 100 ≤ K ℓ → X ∈ P ℓ → Q ℓ X →
            (∀ c ∈ X, ∀ c' ∈ X, ∀ μ, |c μ - c' μ| ≤ (((K ℓ - 36) / 25 - L : ℕ) : ℤ)) →
            L ≤ τ ℓ X → a ∈ X → g ∈ Dset →
            ∀ z : Fin d → ℤ, (∀ μ, ((aK : ℕ) : ℤ) ∣ z μ) →
            (∀ x ∈ box (rootCube (m₀ := 1) zrA[ℓ]).1 (L * aK) ∪ sitesOf (Ycub ℓ X), ∀ μ,
              |(x μ).valMinAbs + z μ| ≤
                (((aK * ((K ℓ - 36) / 25 + 1) - 1) + ((aK * ((K ℓ - 36) / 25 + 1) - 1) + 1) / 4 :
                  ℕ) : ℤ)) →
            RawBoxAgree {w | InBox d ((aK * ((K ℓ - 36) / 25 + 1) - 1) +
                ((aK * ((K ℓ - 36) / 25 + 1) - 1) + 1) / 4 + 2 * L ^ (k + 1) + 3 * L ^ (k + 1))
                ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)) w}
              (symRaw (Equiv.addRight (fun μ => ((z μ : ℤ) : ZMod ((N₁ ℓ * L ^ T.m₁) * L ^ (k + 1)))))
                (rawOf (Dat ℓ g)))
              (symRaw (Equiv.addRight
                (fun μ => ((z μ : ℤ) : ZMod ((N₁ (can X) * L ^ T.m₁) * L ^ (k + 1)))))
                (rawOf (Dat (can X) g))))
          (Ag : Finset (Fin d → ℤ) → G → G → Prop)
          (_ : ∀ X Z, X ⊆ Z → ∀ g g', Ag Z g g' → Ag X g g')
          (_ : ∀ ℓ X g g', X ∈ P ℓ → Ag X g g' → θ ℓ g = θ ℓ g' ∨
            (θ ℓ g ∈ physVq (SA[ℓ]) (SA[ℓ]).a₁ (SA[ℓ]).ν T.t q ∧
              θ ℓ g' ∈ physVq (SA[ℓ]) (SA[ℓ]).a₁ (SA[ℓ]).ν T.t q ∧
              physRestrict (N := N) (thickSet (SA[ℓ]).G' (Yhat Set.univ (sitesOf (Ycub ℓ X))))
                  (physIncl N (SA[ℓ]) (θ ℓ g)) =
                physRestrict (thickSet (SA[ℓ]).G' (Yhat Set.univ (sitesOf (Ycub ℓ X))))
                  (physIncl N (SA[ℓ]) (θ ℓ g'))))
          (W : Submodule ℂ (G → ℂ))
          (_ : ∀ ℓ (f : physParam N (SA[ℓ]) → ℂ),
            AnalyticOnNhd ℂ f (physVq (SA[ℓ]) (SA[ℓ]).a₁ (SA[ℓ]).ν T.t q) →
              (fun g => f (θ ℓ g)) ∈ W)
          {κ κ₂ lam : ℝ} (_ : 0 ≤ κ) (_ : κ + Real.log 2 ≤ κ₂) (_ : κ₂ ≤ lam)
          (_ : 7 * lam + κ₂ ≤ 3 / 2 * T.κdec / c1 d L),
        ∃ Tt : ι → G → Finset (Fin d → ℤ) → ℂ,
          (∀ ℓ g X, Tt ℓ g X = c (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) zrA[ℓ] (θ ℓ g) (Ycub ℓ X) +
            dz (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) zrA[ℓ] (θ ℓ g) (Ycub ℓ X) +
            mObs (N₁ ℓ) (h3N ℓ) (h5 ℓ) (D ℓ) xsA[ℓ] iy (θ ℓ g) (Ycub ℓ X)) ∧
        ∃ Φ : ι → Finset (Fin d → ℤ) → Finset (Fin d → ℤ),
        ∃ Tn : ι → G → Finset (Fin d → ℤ) → ℂ,
          (∀ ℓ X, X ∈ P ℓ → Q ℓ X → X ⊆ Φ ℓ X) ∧
          (∀ ℓ g X, Tn ℓ g X = if Q ℓ X then Tt (can X) g X else
            Tt ℓ g X + ∑ X₀ ∈ ((P ℓ).filter (Q ℓ)).filter (fun X₀ => Φ ℓ X₀ = X),
              (Tt ℓ g X₀ - Tt (can X₀) g X₀)) ∧
          (∀ ℓ g, ∑ X ∈ P ℓ, Tn ℓ g X = ∑ X ∈ P ℓ, Tt ℓ g X) ∧
          (∀ ℓ ℓ' g X, Q ℓ X → Q ℓ' X → Tn ℓ g X = Tn ℓ' g X) ∧
          (∀ ℓ X, X ∈ P ℓ → ∀ g ∈ Dset, ‖Tn ℓ g X‖ ≤
            (3 * B * Real.exp (3 / 2 * T.κdec) +
              (2 * (3 * B * Real.exp (3 / 2 * T.κdec)) *
                  Real.exp ((((300 * L + 100) / 4 : ℕ) : ℝ) * lam) +
                2 * (3 * B * Real.exp (3 / 2 * T.κdec))) * Real.exp κ₂ +
              2 * (3 * B * Real.exp (3 / 2 * T.κdec)) * Real.exp (κ₂ * (L : ℝ))) *
              Real.exp (-κ * (X.card : ℝ))) ∧
          (∀ ℓ X, X ∈ P ℓ → ∀ g g', Ag X g g' → Tn ℓ g X = Tn ℓ g' X) ∧
          (∀ ℓ X, X ∈ P ℓ → (fun g => Tn ℓ g X) ∈ W) := by
  classical
  obtain ⟨β₀, CE, CF, h3, hCE, hCF, H⟩ :=
    towerGapScale_resum_fromTowerG T hm₀ hhull hA p hCR hs0 hs
  refine ⟨β₀, CE, CF, h3, hCE, hCF, ?_⟩
  intro k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  obtain ⟨e0, dz, c, mObs, B, hB, hT, hF⟩ := H k hk ν hν0 hν β hβ p₁ hp0 hp₁ q hq0 hq1
  refine ⟨e0, dz, c, mObs, B, hB, hT, ?_⟩
  intro ι G N₁ _ h3N h5 D K _ hK2 hside a ha P Q can τ hP hQ hτ hcanK Ycub hYs iy Dset θ hθV Dat hDat
    hθD hrawO hsrcO hrawR Ag hAg hAgθ W hWan κ κ₂ lam hκ hκ₂ hlam hrate
  refine hF N₁ h3N h5 D K hK2 hside P Q can τ hP hQ hτ hcanK Ycub hYs
    (fun ℓ => zrA[ℓ]) a (fun ℓ => root_cell_eq (hside ℓ) (hK2 ℓ) (ha ℓ))
    (fun ℓ X _ _ _ => root_box_eq (hside ℓ) (hK2 ℓ) (ha ℓ))
    (fun ℓ => xsA[ℓ]) iy a (fun ℓ => site_cell_eq (hside ℓ) (hK2 ℓ) (ha ℓ))
    (fun ℓ X _ _ _ => site_box_eq (hside ℓ) (hK2 ℓ) (ha ℓ))
    θ hθV Dat hDat hθD hrawO hsrcO hrawR Ag hAg hAgθ
    W hWan hκ hκ₂ hlam hrate

end Tower

end Cell

end Balaban.Polymer.TwoTorusStep
