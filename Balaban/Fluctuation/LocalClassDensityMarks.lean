/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalPairReplacementHat
public import Balaban.Fluctuation.LocalClassChart
public import Balaban.Fluctuation.MarkedDecBall
public import Balaban.Fluctuation.MarkedEvParam

/-!
# The replacement identity at the local generating set as an identity of functions of the datum

P3 pp. 78-79 recomputes every term of (4.45) on `𝔹_{k+1}(Y)` and uses that the recomputed term
equals the term of the whole-level expansion.  `coef_eTermFun_replacement_localB_hat` gives this
equality of the Lemma AE coefficients for one datum `D` of the chart, with the local term evaluated
at the restricted datum `localBRestrict D`.  Here it is restated as an identity of functions of the
raw datum on the whole chart and on the class domain:

* `rawOf_localBRestrict`: the raw datum of the restricted datum is the cut-off `clipRaw 𝔹_j(X)` of
  the raw datum;
* `clipRaw_levelGS`, `clipRaw_localB_clipRaw_levelGS`: the cut-off of a whole-level set is the
  identity on pairs of fields, and the cut-off of `𝔹_j(X)` absorbs it;
* `coef_eTermFun_replacement_localB_hat_raw`: for every raw datum `Θ` of the chart
  `Ξ^c(𝔹_{k+1}; 1, ε)` and every hat variable `ψ̂` of the box `|ψ̂| ≤ c_ψ`, the coefficient of the
  term of the whole level at `(Θ, ψ̂)` equals the coefficient of the term recomputed on
  `(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` at the cut-off `clipRaw 𝔹_{k+1}(Y⁺) Θ` and the restriction of `ψ̂`;
* `evTerm_eTermFun_replacement_localB_hat`: the same for the term `𝓔(X, Y)` of the polymer `Y`, the
  sum of the coefficients over the connected families `𝒞` with `Y[𝒞] = Y`, as functions of
  `(Θ, ψ̂)` on the chart times the box (the read region of every such `𝒞` lies in `Y`);
* `evTerm_eTermFun_replacement_localB_hat_xiDom`: on the class domain `Ξ^c_{k+1}(𝔹_{k+1}; 1, ε)`
  the term of the whole level read at a pair of fields `q` equals the term recomputed on
  `𝔹_{k+1}(Y⁺)` read at the cut-off `clipRaw 𝔹_{k+1}(Y⁺) q`, the reading of the local terms of
  `localB_eTermHat_evTerm_xiFieldDom`;
* `coef_eTermFun_replacement_localB_marked`, `coef_eTermFun_replacement_localB_marked_raw`: the same
  along the masked tangent `um ψ' + tm M_Z ψ'` of the marks (the term of the whole level at
  `markedHatPsiF … Zm um tm`, the recomputed term at the site-wise multiple
  `(um + tm 1[unitPt · ∈ Zm])` of the local hat lift), under the radius condition of the marks;
  `coef_eTermFun_replacement_localB_marked_of_lift` is the assembly step for an abstract local lift;
* `evTerm_FFmarked_replacement_localB`: the marked term `evTerm … (FFmarked … Φ Zm um tm) Y` of an
  inherited label (the family `Ev Y um tm` of `classOldMarksY_expansion`, `Φ = eTermFun`) equals the
  marked term recomputed on `𝔹_{k+1}(Y⁺)`, as functions of `(Θ, ψ̂)` on the chart times the box: the
  marks `∂_t` of the localized old terms may be computed on `𝔹_{k+1}(Y⁺)`.

The old term enters only through the functional `E` (and its generating sets `𝔹_k(X)`, `𝔹_j(X)`,
the set `X₁` of the expansion); every statement holds for each label `(j, y, X)` of the class.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Finset
  Balaban.LargeField Balaban.SmallField.GsSpec Balaban.SmallField.Def6 Balaban.Fluctuation Matrix

section Restrict

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  {j : ℕ} {hj : j ≤ K} {X : Set (CTorus d L N₁ m₁ K)} {hsep : ϱ ≤ minSep L (L ^ m₁)}

/-- **The raw datum of the restricted datum is the cut-off of the raw datum** to the data sites of
`𝔹_j(X) = localB j … X` (resp. to `Ω₁(𝔹_j(X))` for the external field). -/
theorem rawOf_localBRestrict (hj1 : 1 ≤ j)
    (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ') j hj) N) :
    rawOf (localBRestrict (X := X) (hsep := hsep) hj1 D) =
      clipRaw (localB j hj X hsep) (rawOf D) := by
  classical
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · by_cases hx : x ∈ dataSites (localB j hj X hsep) <;>
      simp [clipRaw, rawOf, localBRestrict, BgData.clip, hx]
  · by_cases hx : x ∈ (localB j hj X hsep).Ω 1 <;>
      simp [clipRaw, rawOf, localBRestrict, BgData.clip, hx]

/-- **The cut-off of a whole-level set is the identity**: every site lies in `Ω₁(𝔹_j)`, `j ≥ 1`. -/
theorem clipRaw_levelGS (hj1 : 1 ≤ j) (q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) :
    clipRaw (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ') j hj) q =
      q := by
  classical
  have hΩ : ∀ x, x ∈ (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ')
      j hj).Ω 1 := fun x => by simp [Def6.levelGS, hj1]
  refine Prod.ext (funext fun x => funext fun i => ?_) (funext fun x => funext fun i => ?_)
  · have hx : x ∈ dataSites (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
        (ϱ := ϱ') j hj) := (mem_dataSites _).2 (Or.inl (hΩ x))
    simp [clipRaw, hx]
  · simp [clipRaw, hΩ x]

/-- **The cut-off of `𝔹_j(X)` absorbs the cut-off of the whole level `𝔹_j`.** -/
theorem clipRaw_localB_clipRaw_levelGS (hj1 : 1 ≤ j)
    (q : Fld d L N₁ m₁ K N × Fld d L N₁ m₁ K N) :
    clipRaw (localB j hj X hsep)
        (clipRaw (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ') j hj)
          q) =
      clipRaw (localB j hj X hsep) q := by
  rw [clipRaw_levelGS hj1]

end Restrict

section Ball

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱm : ℝ}

/-- **A pointwise multiple of a field of the ball.**  If `c • f` lies in the ball `FlBall Hm δ` and
at every site `g = m • f` with `‖m‖ ≤ c`, then `g` lies in the ball. -/
theorem mem_flBall_of_pointwise_mul {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm} {δ c : ℝ}
    {f g : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hf : (fun y i => (c : ℂ) * f y i) ∈ FlBall Hm δ)
    (hg : ∀ y, ∃ m : ℂ, ‖m‖ ≤ c ∧ ∀ i, g y i = m * f y i) : g ∈ FlBall Hm δ := by
  intro x hx
  obtain ⟨m, hm, hgm⟩ := hg x
  have hc : 0 ≤ c := (norm_nonneg m).trans hm
  have e1 : g x = m • f x := funext fun i => by rw [hgm i]; rfl
  have e2 : (fun i => (c : ℂ) * f x i) = (c : ℂ) • f x := funext fun i => rfl
  have hv : 0 ≤ vn (f x) := norm_nonneg _
  have h := hf x hx
  simp only at h
  rw [e2, vn_smul', Complex.norm_real, Real.norm_of_nonneg hc] at h
  rw [e1, vn_smul']
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hm hv) h

/-- The multiplier `u + t 1[·]` of the marked tangent has norm at most `‖u‖ + ‖t‖`. -/
theorem norm_add_ite_le (u t : ℂ) (p : Prop) [Decidable p] :
    ‖u + if p then t else 0‖ ≤ ‖u‖ + ‖t‖ := by
  refine (norm_add_le _ _).trans ?_
  split_ifs
  · exact le_rfl
  · simp

end Ball

section MaskedLift

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}

/-- **The masked local hat lift lies in the ball** if the local hat lift with the amplitude
`(‖um‖ + ‖tm‖) cc` does: the masked lift is the site-wise multiple of the local hat lift by
`um + tm 1[p x]`, of norm at most `‖um‖ + ‖tm‖`. -/
theorem maskedLocalLift_mem_flBall {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {δ : ℝ}
    (M : Matrix (unitPts G × Fin N) (unitPts G × Fin N) ℂ) (ψ : unitPts G × Fin N → ℂ)
    (cc um tm : ℂ) (p : CTorus d L N₁ m₁ (k + 1) → Prop) [DecidablePred p]
    (h : (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) => if h : unitBlock x ∈ unitPts G then
        ((((‖um‖ + ‖tm‖ : ℝ) : ℂ) * cc) • (M *ᵥ ψ)) (⟨unitBlock x, h⟩, i) else 0) ∈
      FlBall Hm δ) :
    (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) => (um + if p x then tm else 0) *
      (if h : unitBlock x ∈ unitPts G then (cc • (M *ᵥ ψ)) (⟨unitBlock x, h⟩, i) else 0)) ∈
      FlBall Hm δ := by
  refine mem_flBall_of_pointwise_mul (c := ‖um‖ + ‖tm‖) ?_ fun y =>
    ⟨_, norm_add_ite_le um tm _, fun i => rfl⟩
  convert h using 1
  funext x i
  split_ifs <;> simp [mul_assoc]

/-- **The masked tangent of the whole level lies in the ball** if the hat lift with the amplitude
`(‖um‖ + ‖tm‖) cc` does (`markedHatPsiF_apply`). -/
theorem markedHatPsiF_mem_flBall_of {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a₁ ν δ : ℝ} (hG' : IsLevel Gp (k + 1))
    (cc : ℂ) (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Zm : Finset (unitPts Gp)) (um tm : ℂ) (s : DecParams Gp)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (ψh : unitPts Gp × Fin N → ℂ)
    (h : hatPsiF Gp a₁ ν hG' (((‖um‖ + ‖tm‖ : ℝ) : ℂ) * cc) F₁ s Θ ψh ∈ FlBall Hm δ) :
    markedHatPsiF a₁ ν hG' cc F₁ Zm um tm s Θ ψh ∈ FlBall Hm δ := by
  refine mem_flBall_of_pointwise_mul (c := ‖um‖ + ‖tm‖)
    (f := hatPsiF Gp a₁ ν hG' cc F₁ s Θ ψh) ?_ fun y =>
    ⟨_, norm_add_ite_le um tm _, fun i => markedHatPsiF_apply hG' cc F₁ Zm um tm s Θ ψh y i⟩
  convert h using 1
  funext y i
  simp only [hatPsiF, liftC_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

end MaskedLift

section Assembly

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm ϱ₁ ϱ₂ : ℝ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {ν : ℝ}

/-- **The replacement identity as an identity of functions of the raw datum** (P3 pp. 78-79,
(4.46)).  The hypotheses of `coef_eTermFun_replacement_localB_hat` with the datum `D` replaced by a
raw datum `Θ` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)`: the coefficient `coef (·) 𝒞` of Lemma AE of the
term of the whole level at `(Θ, ψ̂)` equals that of the term recomputed on
`(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` at the cut-off `clipRaw 𝔹_{k+1}(Y⁺) Θ` (the raw datum of the restricted
datum, `rawOf_localBRestrict`) and the restriction of `ψ̂` to the unit lattice of `𝔹_{k+1}(Y⁺)`. -/
theorem coef_eTermFun_replacement_localB_hat_raw (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 ×
        Fin N → ℂ) × ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1
        × Fin N → ℂ)
        (α : (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁))
      {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεb : xiC1 d * eps + (2 * bgK1 d L N + 1) * (xiC1 d * eps) ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (hΘ : Θ ∈ XiCRaw
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
      (compWeight L a₁) ν (k + 1) 1 eps)
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (ψh : unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) hk) × Fin N → ℂ) (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk), ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hRk : ∀ x ∈ dataSites Gk, x ∈ R)
    (hRY : ∀ x ∈ R, x ∈ Y) :
    coef (fun w => eTermFun (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) Gk Gj Hm ac Fk E (F₁ (extParams
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
      Θ))
        (Sol (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
          flEdat (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk) Hm (F₁ (extParams
            (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
            X₁ w, Θ)) Θ.1
            (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
              (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) (Θ) ψh))).1
        (Θ, (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
                (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) (Θ) ψh))) C =
      coef (fun w => eTermFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ))
            (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ).1
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then ψh (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0))).1
        (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ,
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then ψh (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0))) C := by
  obtain ⟨D, hD, rfl⟩ := hΘ
  rw [← rawOf_localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
    (Nat.le_add_left 1 k) D]
  exact coef_eTermFun_replacement_localB_hat hG hk1 hk Y Yp hYp hN hm₁ hM hag hagm hagl hS HB
    HB' ha₁ ha₂ hκ hMc hMX hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E C hR' hRκ heps hsmall
    hc7 hphi hεb hsmall' hc7' hphi' hδ₀e hD hmarD' hαD' hsm cc hcψ hδ₁c ψh hψh hRC hRX hRk hRY

/-- **The term `𝓔(X, Y)` of the polymer `Y`, recomputed on `𝔹_{k+1}(Y⁺)`, as a function of the
datum** (P3 pp. 78-79).  For the connected families `𝒞` of the expansion of the whole level with
`Y[𝒞] = Y` the read region of `coef_eTermFun_replacement_localB_hat` may be taken to be `Y` itself
(the cubes of `𝒞` lie in `Y[𝒞]`, `Pset_subset_Dsites`; the cubes meeting `X₁` and the data sites of
`𝔹_k(X)` lie in `Y` by hypothesis).  Hence the term of the whole level, `∑_{Y[𝒞] = Y} coef (·) 𝒞`
at `(Θ, ψ̂)`, equals the term recomputed on `(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` at the cut-off
`clipRaw 𝔹_{k+1}(Y⁺) Θ` and `ψ̂`, at every point of the chart times the box. -/
theorem evTerm_eTermFun_replacement_localB_hat (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 ×
        Fin N → ℂ) × ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1
        × Fin N → ℂ)
        (α : (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεb : xiC1 d * eps + (2 * bgK1 d L N + 1) * (xiC1 d * eps) ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {m₀ : ℕ} (hU : LayerUnion (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
      (ϱ := ϱ) (k + 1) hk) m₀) (hNm : L ^ m₀ ∣ N₁)
    (hXY : ∀ P ∈ cubeIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk), ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ Y)
    (hkY : ∀ x ∈ dataSites Gk, x ∈ Y) :
    ∀ u ∈ XiCRaw (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
      (compWeight L a₁) ν (k + 1) 1 eps ×ˢ {ψh : unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ |
        ∀ p, ‖ψh p‖ ≤ cψ},
    evTerm (fun i : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ => i.1.1)
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) m₀ X₁
      (fun (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ))
        (w : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ → ℂ) =>
      eTermFun (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) Gk Gj Hm ac Fk E (F₁ (extParams
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
      u.1))
        (Sol (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
          flEdat (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk) Hm (F₁ (extParams
            (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
            X₁ w, u.1)) u.1.1
            (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
              (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) u.1 u.2))).1
        (u.1, (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
                (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) u.1 u.2))) Y u =
    evTerm (fun i : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ => i.1.1)
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) m₀ X₁
      (fun (v : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ))
        (w : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ → ℂ) =>
      eTermFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1))
            (v.1).1
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (v.1).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then v.2 (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0))).1
        (v.1,
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (v.1).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then v.2 (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0)))
      Y (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) u.1, u.2) := by
  classical
  rintro ⟨Θ, ψh⟩ ⟨hΘ, hψh⟩
  unfold evTerm
  refine Finset.sum_congr rfl fun C hC => ?_
  have hY := ((mem_connFams _).1 hC).2
  exact coef_eTermFun_replacement_localB_hat_raw hG hk1 hk Y Yp hYp hN hm₁ hM hag hagm hagl hS HB
    HB' ha₁ ha₂ hκ hMc hMX hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E C hR' hRκ heps hsmall
    hc7 hphi hεb hsmall' hc7' hphi' hδ₀e Θ hΘ hmarD' hαD' hsm cc hcψ hδ₁c ψh hψh
    (R := Finset.univ.filter (· ∈ Y))
    (fun i hi y hy => by
      rw [Finset.mem_filter, ← hY]
      exact ⟨Finset.mem_univ _,
        Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, Pset_subset_Dsites hU hNm i.1.2 hy⟩)⟩)
    (fun P hP hdis y hy => Finset.mem_filter.2 ⟨Finset.mem_univ _, hXY P hP hdis y hy⟩)
    (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, hkY x hx⟩)
    (fun x hx => (Finset.mem_filter.1 hx).2)

/-- **The replacement identity on the class domain** (the per-label input of `hrepl`).  At a pair
of fields `q` of the class domain `Ξ^c_{k+1}(𝔹_{k+1}; 1, ε)`, `ε ≤ eps`, the term of the polymer `Y`
of the whole level read at `q` (the cut-off of the whole level is the identity, `clipRaw_levelGS`)
equals the term recomputed on `(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` read at the cut-off
`clipRaw 𝔹_{k+1}(Y⁺) q`, for every hat variable of the box. -/
theorem evTerm_eTermFun_replacement_localB_hat_xiDom (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 ×
        Fin N → ℂ) × ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1
        × Fin N → ℂ)
        (α : (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεb : xiC1 d * eps + (2 * bgK1 d L N + 1) * (xiC1 d * eps) ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {m₀ : ℕ} (hU : LayerUnion (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
      (ϱ := ϱ) (k + 1) hk) m₀) (hNm : L ^ m₀ ∣ N₁)
    (hXY : ∀ P ∈ cubeIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk), ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ Y)
    (hkY : ∀ x ∈ dataSites Gk, x ∈ Y)
    {ε : ℝ} (hε : ε ≤ eps) (q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hq : XiDom (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
      (compWeight L a₁) ν (k + 1) ε q.1 q.2)
    (ψh : unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ) (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    evTerm (fun i : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ => i.1.1)
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) m₀ X₁
      (fun (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ))
        (w : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ → ℂ) =>
      eTermFun (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) Gk Gj Hm ac Fk E (F₁ (extParams
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
      u.1))
        (Sol (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
          flEdat (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk) Hm (F₁ (extParams
            (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
            X₁ w, u.1)) u.1.1
            (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
              (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) u.1 u.2))).1
        (u.1, (hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc
              F₁
                (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) u.1 u.2))) Y (q, ψh) =
    evTerm (fun i : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ => i.1.1)
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) m₀ X₁
      (fun (v : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ))
        (w : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ → ℂ) =>
      eTermFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1))
            (v.1).1
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (v.1).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then v.2 (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0))).1
        (v.1,
            (fun x i => if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (v.1).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), v.1)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then v.2 (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0)))
      Y (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) q, ψh) := by
  have hq' := clipRaw_mem_xiCRaw_of_xiDom
    (G := Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
    hε hq
  rw [clipRaw_levelGS (Nat.le_add_left 1 k)] at hq'
  exact evTerm_eTermFun_replacement_localB_hat hG hk1 hk Y Yp hYp hN hm₁ hM hag hagm hagl hS HB
    HB' ha₁ ha₂ hκ hMc hMX hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E hR' hRκ heps hsmall
    hc7 hphi hεb hsmall' hc7' hphi' hδ₀e hmarD' hαD' hsm cc hcψ hδ₁c hU hNm hXY hkY (q, ψh)
    ⟨hq', hψh⟩

/-- **The replacement identity along the masked tangent, for an abstract local lift, core.**  The
statement of `coef_eTermFun_replacement_localB_marked_of_lift` for a level set `𝔹_{k+1}`, arbitrary
generating sets `Gl`, `Gd` with the hypotheses of `coef_eTermFun_replacement_gen`, a datum `D'` of
the chart of `Gl` agreeing with `D` on the top layer of `Gl`, and the margin of the read region in
the top layer of `Gl` (in place of the collar).  The landed `localB` statement is its instance. -/
theorem coef_eTermFun_replacement_marked_of_lift_gen
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG' : IsLevel Gp (k + 1))
    (hG : IsLevel Hm k) (hk1 : 1 ≤ k) {ϱl ϱl' : ℝ} {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
    {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}
    (hA : CubeAligned Gl m₁) (hSS : SupSep Gl m₁) (hPd : Precedes Gd Gl)
    (hdk : Gd.Ω k = Gl.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl - 1))
    (hagd : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl' - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) ϱl (compWeight L a₁) ν)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 ×
        Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf Gl) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) ×
        (Gl.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData
      Gp N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        Gp.Ω 1
        × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          Gp)
          Gp
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf Gl))
      (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gl)
          Gl (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf Gl) ×
        Edat Gd N →
      (Gd.Ω 1 × Fin N → ℂ) ×
        (Gd.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          Gp)
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf Gl) ×
        Edat Gd N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi Gd
          (Dec2.decG (coverOf Gl)
            Gd (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource Gd (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf Gl)
          Gd (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource Gd (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small Gd (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ,
          Small Gd δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl)
            Gd (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource Gd (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx
      Gp X₁))
      {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hle : eps ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {D' : BgData Gl N} (hD'x : XiCData Gl (compWeight L a₁) ν (k + 1) 1 eps' D')
    (hD' : ∀ x ∈ Gl.Ω (k + 1), D'.Ψ x = D.Ψ x ∧ D'.h x = D.h x)
    (cc : ℂ) (Zm : Finset (unitPts Gp))
    (um tm : ℂ) (ψh : unitPts Gp × Fin N → ℂ)
    (M : (ParIdx Gp X₁ → ℂ) →
      Matrix (unitPts Gl × Fin N)
        (unitPts Gl × Fin N) ℂ)
    (ψl : unitPts Gl × Fin N → ℂ)
    (hℓ : ∀ w ∈ supN C R', (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts Gl then
        ((((‖um‖ + ‖tm‖ : ℝ) : ℂ) * cc) • (M w *ᵥ ψl)) (⟨unitBlock x, h⟩, i) else 0) ∈ FlBall Hm δ₁)
    (hamb : ∀ w ∈ supN C R', hatPsiF Gp a₁ ν
      hG' (((‖um‖ + ‖tm‖ : ℝ) : ℂ) * cc) F₁
      (extParams Gp X₁ w) (rawOf D) ψh ∈ FlBall Hm δ₁)

    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hRk : ∀ x ∈ dataSites Gk, x ∈ R)
    (hℓeq : ∀ w ∈ supN C R', ∀ x ∈ R, ∀ y : CTorus d L N₁ m₁ (k + 1), supDist x y ≤ L ^ (k + 1) →
      ∀ i, (if h : unitBlock y ∈ unitPts Gl then
        (cc • (M w *ᵥ ψl)) (⟨unitBlock y, h⟩, i) else 0) =
      hatPsiF Gp a₁ ν hG' cc F₁
        (extParams Gp X₁ w) (rawOf D) ψh y i)
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1)) :
    coef (fun w => eTermFun Gp Gk Gj Hm ac Fk E (F₁ (extParams
      Gp X₁ w,
      rawOf D))
        (Sol (extParams Gp X₁ w,
          flEdat Gp Hm (F₁ (extParams
            Gp
            X₁ w, rawOf D)) D.Ψ (markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
          (extParams Gp X₁ w) (rawOf D) ψh))).1 (rawOf D, (markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
          (extParams Gp X₁ w) (rawOf D) ψh))) C =
      coef (fun w => eTermFun Gl Gk Gj
        Gd
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams
              Gp X₁ w) P.1 else 0), rawOf
              D'))
        (Sol' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams
              Gp X₁ w) P.1 else 0),
          flEdat Gl
            Gd
            (F₁' ((fun P => if P.1.2 ∈ Gl.Ω
                (k + 1) then Dec2.extS (coverOf
                  Gp) (extParams
                  Gp X₁ w) P.1 else 0), rawOf
                  D'))
            D'.Ψ (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
          (um + if unitPt hG' x ∈ Zm then tm else 0) *
          (if h : unitBlock x ∈ unitPts Gl then
            (cc • (M w *ᵥ ψl)) (⟨unitBlock x, h⟩, i) else 0)))).1 (rawOf
              D', (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
          (um + if unitPt hG' x ∈ Zm then tm else 0) *
          (if h : unitBlock x ∈ unitPts Gl then
            (cc • (M w *ᵥ ψl)) (⟨unitBlock x, h⟩, i) else 0)))) C  := by
  classical
  obtain ⟨Sb, -, Sf, -⟩ := replacement_coverBases hG' Hm hA hSS hPd hN hm₁ hM HB hag hagm hagl hagd
  have hd0 : 0 < d := by have := HB.hd; omega
  have hxi := one_le_xiC1 d
  have hK4 : 0 ≤ K4 d L N BG κ := (K4_pos hS.fam.2.1 hd0).le
  have hδ₀a : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤ δ₀ := by
    have : K4 d L N BG κ * (xiC1 d * eps) ≤ K4 d L N BG κ * (xiC1 d * eps') :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by linarith)) hK4
    linarith
  have hsσ : ∀ w ∈ supN C R', ∀ P, ‖extParams _ X₁ w P‖ < Real.exp κ := fun w hw P =>
    (norm_extParams_lt hR' hw.2 P).trans_le hRκ
  have hψl := fun w (hw : w ∈ supN C R') =>
    maskedLocalLift_mem_flBall (M w) ψl cc um tm (fun x => unitPt hG' x ∈ Zm) (hℓ w hw)
  refine (coef_congr_near hR' fun w hw => ?_).trans
    (coef_eTermFun_replacement_restrict_gen hG' hG hk1 hA hSS hPd hdk hdtop hN hm₁ hM hag hagm
      hagl hagd hS HB HB' hκ hMc hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E C hR' hRκ heps
      hsmall hc7 hphi hle hsmall' hc7' hphi' hδ₀e hD hD'x hD' _ hψl hRC hRX hRk hmar)
  exact eTermFun_level_hat_congr hG' hm₁ hF₂ Sf hκ.le hM₂ h0 h1.le hδ₀ hδ₁ hSol ac Fk E hRC hRX
    hRk hw.1 (hsσ w hw) _ (rawOf D)
    (strictDataM_flEdat_cover hS Sb HB hκ hMc heps hsmall hc7 hphi h1 hδ₀a
      (isLevel_top_precedes hG' Hm) hF₁ hSol (hsσ w hw) hD
      (markedHatPsiF_mem_flBall_of hG' cc F₁ Zm um tm _ _ ψh (hamb w hw)))
    (strictDataM_flEdat_cover hS Sb HB hκ hMc heps hsmall hc7 hphi h1 hδ₀a
      (isLevel_top_precedes hG' Hm) hF₁ hSol (hsσ w hw) hD (hψl w hw))
    (fun x hx y hy => funext fun i =>
      (markedHatPsiF_apply hG' cc F₁ Zm um tm _ _ ψh y i).trans
        (congrArg _ (hℓeq w hw x hx y hy i).symm))


/-- **The replacement identity along the masked tangent, for an abstract local lift.**  The
assembly step of `coef_eTermFun_replacement_localB_marked`: if the local lift
`x ↦ cc (M w ψ̂_l)(unitBlock x)` (extended by zero off the unit points of `𝔹_{k+1}(Y⁺)`, `M w` any
matrix) and the hat lift of the whole level lie, with the amplitude `(‖um‖ + ‖tm‖) cc`, in the ball
of fluctuations of `𝔹_k`, and the two lifts agree within `L^{k+1}` of the read region (`hℓeq`), then
the coefficient of the term of the whole level along the masked tangent equals that of the term
recomputed on `(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` along the same site-wise multiple of the local lift. -/
theorem coef_eTermFun_replacement_localB_marked_of_lift (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 ×
        Fin N → ℂ) × ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1
        × Fin N → ℂ)
        (α : (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁))
      {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεb : xiC1 d * eps + (2 * bgK1 d L N + 1) * (xiC1 d * eps) ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    {D : BgData (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) N} (hD : XiCData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
      (compWeight L a₁) ν (k + 1) 1 eps D)
    (cc : ℂ) (Zm : Finset (unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)))
    (um tm : ℂ) (ψh : unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ)
    (M : (ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ → ℂ) →
      Matrix (unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N)
        (unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N) ℂ)
    (ψl : unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℂ)
    (hℓ : ∀ w ∈ supN C R', (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
      if h : unitBlock x ∈ unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
        ((((‖um‖ + ‖tm‖ : ℝ) : ℂ) * cc) • (M w *ᵥ ψl)) (⟨unitBlock x, h⟩, i) else 0) ∈ FlBall Hm δ₁)
    (hamb : ∀ w ∈ supN C R', hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν
      (isLevel_levelGS (Nat.le_add_left 1 k) hk) (((‖um‖ + ‖tm‖ : ℝ) : ℂ) * cc) F₁
      (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) (rawOf D) ψh ∈ FlBall Hm δ₁)

    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk), ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hRk : ∀ x ∈ dataSites Gk, x ∈ R)
    (hℓeq : ∀ w ∈ supN C R', ∀ x ∈ R, ∀ y : CTorus d L N₁ m₁ (k + 1), supDist x y ≤ L ^ (k + 1) →
      ∀ i, (if h : unitBlock y ∈ unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
        (cc • (M w *ᵥ ψl)) (⟨unitBlock y, h⟩, i) else 0) =
      hatPsiF (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc F₁
        (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) (rawOf D) ψh y i)
    (hRY : ∀ x ∈ R, x ∈ Y) :
    coef (fun w => eTermFun (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) Gk Gj Hm ac Fk E (F₁ (extParams
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
      rawOf D))
        (Sol (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
          flEdat (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk) Hm (F₁ (extParams
            (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
            X₁ w, rawOf D)) D.Ψ (markedHatPsiF a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc F₁ Zm um tm
          (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) (rawOf D) ψh))).1 (rawOf D, (markedHatPsiF a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc F₁ Zm um tm
          (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) (rawOf D) ψh))) C =
      coef (fun w => eTermFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
              (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D)))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D)))
            (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D).Ψ (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
          (um + if unitPt (isLevel_levelGS (Nat.le_add_left 1 k) hk) x ∈ Zm then tm else 0) *
          (if h : unitBlock x ∈ unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
            (cc • (M w *ᵥ ψl)) (⟨unitBlock x, h⟩, i) else 0)))).1 (rawOf
              (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D), (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
          (um + if unitPt (isLevel_levelGS (Nat.le_add_left 1 k) hk) x ∈ Zm then tm else 0) *
          (if h : unitBlock x ∈ unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
            (cc • (M w *ᵥ ψl)) (⟨unitBlock x, h⟩, i) else 0)))) C  := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hxi := one_le_xiC1 d
  have hK1 : 0 < bgK1 d L N := bgK1_pos d L N
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hle : eps ≤ eps' := by nlinarith
  have hc1 : xiC1 d * eps ≤ bgC1 d L N := hc7.trans (c7_le_bgC1 d L N BG κ)
  have hc0 : xiC1 d * eps ≤ bgC0 d L N := hc1.trans (bgC1_le_bgC0 d L N hd0)
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := HB.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  exact coef_eTermFun_replacement_marked_of_lift_gen (isLevel_levelGS (Nat.le_add_left 1 k) hk) hG
    hk1 (localB_cubeAligned hk Yp _ hm₁) (localB_supSep hk Yp _)
    (localB_drop_precedes hk (Nat.le_succ k) Yp _ _)
    (localB_drop_Ω hk (Nat.le_succ k) Yp _ _ (le_refl k)) (localB_drop_top hk (Nat.le_succ k) Yp _ _)
    hN hm₁ hM hag hagm hagl hagl hS HB HB' hκ hMc hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E C
    hR' hRκ heps hsmall hc7 hphi hle hsmall' hc7' hphi' hδ₀e hD
    (localB_xiCData_restrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
      (Nat.le_add_left 1 k) HB' HB.mass hδ0 le_rfl hc0 hc1 hνε hεb D (xiCData_inDomainC HB hsmall hD))
    (fun x hx => localBRestrict_eq_of_mem_top (Nat.le_add_left 1 k) D hx) cc Zm um tm ψh M ψl hℓ hamb
    hRC hRX hRk hℓeq (localB_collar_margin hk (le_refl (minSep L (L ^ m₁))) hYp hRY)

/-- **The replacement identity along the masked tangent, core** (P3 pp. 78-79, (4.46), with the
masked tangent `u ψ' + t M_Z ψ'`).  The statement of `coef_eTermFun_replacement_localB_marked` for a
level set `𝔹_{k+1}`, arbitrary generating sets `Gl`, `Gd` with the hypotheses of
`coef_eTermFun_replacement_gen` (cube alignment and sup-separation of `Gl`, `Gd ≺ Gl` with the layer
`k` of `Gl` and no layer `k + 1`), a datum `D'` of the chart `Ξ^c_{k+1}(Gl; 1, ε')` agreeing with `D`
on the top layer of `Gl` (`ε ≤ ε'`), and the margin of the read region in the top layer of `Gl`.
The landed `localB` statement is its instance; the cast local generating sets of the new level are
another. -/
theorem coef_eTermFun_replacement_marked_gen
    {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (hG' : IsLevel Gp (k + 1))
    (hG : IsLevel Hm k) (hk1 : 1 ≤ k) {ϱl ϱl' : ℝ} {Gl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl}
    {Gd : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl'}
    (hA : CubeAligned Gl m₁) (hSS : SupSep Gl m₁) (hPd : Precedes Gd Gl)
    (hdk : Gd.Ω k = Gl.Ω k) (hdtop : Gd.Ω (k + 1) = ∅)
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl - 1))
    (hagd : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱl' - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) ϱl (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 ×
        Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf Gl) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gl.Ω 1 × Fin N → ℂ) ×
        (Gl.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData
      Gp N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        Gp.Ω 1
        × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          Gp)
          Gp
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf Gl))
      (D : BgData Gl N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gl (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : Gl.Ω 1 × Fin N → ℂ)
        (α : Gl.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gl)
          Gl (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf Gl) ×
        Edat Gd N →
      (Gd.Ω 1 × Fin N → ℂ) ×
        (Gd.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          Gp)
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf Gl) ×
        Edat Gd N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Gd N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi Gd
          (Dec2.decG (coverOf Gl)
            Gd (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource Gd (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf Gl)
          Gd (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource Gd (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small Gd (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Gd (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Gd (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Gd.Ω 1 → ℂ,
          Small Gd δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gl)
            Gd (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource Gd (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx
      Gp X₁))
      {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hle : eps ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {D' : BgData Gl N} (hD'x : XiCData Gl (compWeight L a₁) ν (k + 1) 1 eps' D')
    (hD' : ∀ x ∈ Gl.Ω (k + 1), D'.Ψ x = D.Ψ x ∧ D'.h x = D.h x)
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (Zm : Finset (unitPts Gp)) (um tm : ℂ)
    (hδ₁m : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    (ψh : unitPts Gp × Fin N → ℂ) (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx Gp, ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hRk : ∀ x ∈ dataSites Gk, x ∈ R)
    (hmar : ∀ x ∈ R, ∀ y, supDist x y ≤ 2 * L ^ (k + 1 + m₁) → y ∈ Gl.Ω (k + 1)) :
    coef (fun w => eTermFun Gp Gk Gj Hm ac Fk E (F₁ (extParams
      Gp X₁ w,
      rawOf D))
        (Sol (extParams Gp X₁ w,
          flEdat Gp Hm (F₁ (extParams
            Gp
            X₁ w, rawOf D)) D.Ψ
            (markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
              (extParams Gp X₁ w) (rawOf D) ψh))).1
        (rawOf D, (markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
              (extParams Gp X₁ w) (rawOf D) ψh))) C =
      coef (fun w => eTermFun Gl Gk Gj
        Gd
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams
              Gp X₁ w) P.1 else 0), rawOf
              D'))
        (Sol' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1)
            then Dec2.extS (coverOf Gp) (extParams
              Gp X₁ w) P.1 else 0),
          flEdat Gl
            Gd
            (F₁' ((fun P => if P.1.2 ∈ Gl.Ω
                (k + 1) then Dec2.extS (coverOf
                  Gp) (extParams
                  Gp X₁ w) P.1 else 0), rawOf
                  D'))
            D'.Ψ
            (fun x i => (um + if unitPt hG' x ∈ Zm
                then tm else 0) * (if h : unitBlock x ∈
                unitPts Gl then
              (cc • (decCovSqrt Gl
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ Gl.Ω
                  (k + 1) then Dec2.extS (coverOf
                    Gp) (extParams
                    Gp X₁ w) P.1 else 0), rawOf
                  D')).2
                (Dec2.extS (coverOf Gl)
                  (fun P => if P.1.2 ∈ Gl.Ω
                  (k + 1) then Dec2.extS (coverOf
                    Gp) (extParams
                    Gp X₁ w) P.1 else 0))
                (barField Gl
                  D'.Ψ
                  (F₁' ((fun P => if P.1.2 ∈ Gl.Ω
                  (k + 1) then Dec2.extS (coverOf
                    Gp) (extParams
                    Gp X₁ w) P.1 else 0), rawOf
                  D')).1)
                (unitQ Gl)
                (unitP Gl) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0)))).1
        (rawOf D',
            (fun x i => (um + if unitPt hG' x ∈ Zm
                then tm else 0) * (if h : unitBlock x ∈
                unitPts Gl then
              (cc • (decCovSqrt Gl
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ Gl.Ω
                  (k + 1) then Dec2.extS (coverOf
                    Gp) (extParams
                    Gp X₁ w) P.1 else 0), rawOf
                  D')).2
                (Dec2.extS (coverOf Gl)
                  (fun P => if P.1.2 ∈ Gl.Ω
                  (k + 1) then Dec2.extS (coverOf
                    Gp) (extParams
                    Gp X₁ w) P.1 else 0))
                (barField Gl
                  D'.Ψ
                  (F₁' ((fun P => if P.1.2 ∈ Gl.Ω
                  (k + 1) then Dec2.extS (coverOf
                    Gp) (extParams
                    Gp X₁ w) P.1 else 0), rawOf
                  D')).1)
                (unitQ Gl)
                (unitP Gl) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0)))) C := by
  classical
  obtain ⟨Sb, Sb', -, -⟩ := replacement_coverBases hG' Hm hA hSS hPd hN hm₁ hM HB hag hagm hagl hagd
  have hd0 : 0 < d := by have := HB.hd; omega
  have hxi := one_le_xiC1 d
  have heps' : 0 < eps' := lt_of_lt_of_le heps hle
  have hK4 : 0 ≤ K4 d L N BG κ := (K4_pos hS.fam.2.1 hd0).le
  have hxle : xiC1 d * eps ≤ xiC1 d * eps' := mul_le_mul_of_nonneg_left hle (by linarith)
  have hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hxle hK4) hαD'
  have hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc := by
    refine lt_of_le_of_lt ?_ hmarD'
    unfold decDomMargin
    gcongr
  have hsσ : ∀ w ∈ supN C R', ∀ P, ‖extParams _ X₁ w P‖ < Real.exp κ := fun w hw P =>
    (norm_extParams_lt hR' hw.2 P).trans_le hRκ
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hHm : Hm.Ω (k + 1) = ∅ :=
    Finset.eq_empty_of_forall_notMem fun x => isLevel_not_mem_Ω hG le_rfl (by omega) x
  have hψh' : ∀ p : unitPts Gl × Fin N,
      ‖(fun p : unitPts Gl × Fin N =>
        if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0) p‖ ≤ cψ := by
    intro p
    dsimp only
    split_ifs
    · exact hψh _
    · simpa using hcψ
  have hcm : 0 ≤ ‖um‖ + ‖tm‖ := by positivity
  have hδ₁cm : Real.sqrt N * (‖((‖um‖ + ‖tm‖ : ℝ) : ℂ) * cc‖ *
      (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcm]
    calc Real.sqrt N * ((‖um‖ + ‖tm‖) * ‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))
        = (‖um‖ + ‖tm‖) *
          (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) := by ring
      _ < δ₁ := hδ₁m
  exact coef_eTermFun_replacement_marked_of_lift_gen hG' hG hk1 hA hSS hPd hdk hdtop hN hm₁ hM hag
    hagm hagl hagd hS HB HB' hκ hMc hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E C hR' hRκ
    heps hsmall hc7 hphi hle hsmall' hc7' hphi' hδ₀e hD hD'x hD' cc Zm um tm ψh
    (fun w => decCovSqrt Gl (compWeight L a₁) a₁ ν
      (F₁' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1) then
        Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D')).2
      (Dec2.extS (coverOf Gl) (fun P => if P.1.2 ∈ Gl.Ω (k + 1) then
        Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0))
      (barField Gl D'.Ψ (F₁' ((fun P => if P.1.2 ∈ Gl.Ω (k + 1) then
        Dec2.extS (coverOf Gp) (extParams Gp X₁ w) P.1 else 0), rawOf D')).1)
      (unitQ Gl) (unitP Gl))
    (fun p => if hp : p.1.1 ∈ unitPts Gp then ψh (⟨p.1.1, hp⟩, p.2) else 0)
    (fun w hw => (localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS Sb' HB' hκ.le hMc hMX
      (Cchi_nonneg d L) hF₁' heps' hsmall' hc7' hphi' hmarD' hαD' hsm
      (tau_norm_lt (Gl := Gl) (hsσ w hw) hE1) hD'x _ hcψ h1 hδ₁cm hψh').1)
    (fun w hw => by
      rw [hatPsiF_eq_dite (a₁ := a₁) (ν := ν) hG' (((‖um‖ + ‖tm‖ : ℝ) : ℂ) * cc) F₁
        (extParams _ X₁ w) (rawOf D) ψh]
      exact (localHatLift_mem_flBallLC_of_spec hHm hk1 ha₁ ha₂ hS Sb HB hκ.le hMc hMX
        (Cchi_nonneg d L) hF₁ heps hsmall hc7 hphi hmarD hαD hsm (hsσ w hw) hD _ hcψ h1 hδ₁cm
        hψh).1)
    hRC hRX hRk
    (fun w hw x hx y hy i => localHatLift_eq_hatPsiF hSS hA hG' hk1 hN hm₁ hM hag hagl hS HB HB'
      ha₁ ha₂ hκ hMc hMX hF₁ hF₁' heps hsmall hc7 hphi heps' hsmall' hc7' hphi' hmarD hαD
      hmarD' hαD' hsm hD hD'x hD' hRC hRX hmar hw.1 (hsσ w hw) cc ψh ⟨x, hx, hy⟩ i)
    hmar


/-- **The replacement identity along the masked tangent** (the marked form of
`coef_eTermFun_replacement_localB_hat`, for the marks of the inherited energy: P3 pp. 78-79 with the
masked tangent `u ψ' + t M_Z ψ'`).  The term of the whole level is evaluated at the masked decoupled
tangent `markedHatPsiF … Zm um tm (σ w) (rawOf D) ψ̂` (the site-wise multiple
`(um + tm 1[unitPt y ∈ Zm]) · hatPsiF`, `markedHatPsiF_apply`); the term recomputed on
`(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` at the restricted datum `localBRestrict D` is evaluated at the same site-wise
multiple of the local hat lift.  The radius condition is that of the marks,
`(‖um‖ + ‖tm‖) √N ‖cc‖ K c_ψ < δ₁`.  Proof: the term of the whole level reads its fluctuation
variable only within `L^{k+1}` of the read region (`eTermFun_level_hat_congr`), where the two hat
lifts agree (`localHatLift_eq_hatPsiF_localB`), hence so do their site-wise multiples; then
`coef_eTermFun_replacement_localB_collar` with the masked local lift as `ψ'(w)`. -/
theorem coef_eTermFun_replacement_localB_marked (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 ×
        Fin N → ℂ) × ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1
        × Fin N → ℂ)
        (α : (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁))
      {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεb : xiC1 d * eps + (2 * bgK1 d L N + 1) * (xiC1 d * eps) ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    {D : BgData (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) N} (hD : XiCData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
      (compWeight L a₁) ν (k + 1) 1 eps D)
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (Zm : Finset (unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (um tm : ℂ)
    (hδ₁m : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    (ψh : unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) hk) × Fin N → ℂ) (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk), ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hRk : ∀ x ∈ dataSites Gk, x ∈ R)
    (hRY : ∀ x ∈ R, x ∈ Y) :
    coef (fun w => eTermFun (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) Gk Gj Hm ac Fk E (F₁ (extParams
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
      rawOf D))
        (Sol (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
          flEdat (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk) Hm (F₁ (extParams
            (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
            X₁ w, rawOf D)) D.Ψ
            (markedHatPsiF a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc F₁ Zm um tm
              (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) (rawOf D) ψh))).1
        (rawOf D, (markedHatPsiF a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc F₁ Zm um tm
              (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) (rawOf D) ψh))) C =
      coef (fun w => eTermFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
              (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D)))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D)))
            (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D).Ψ
            (fun x i => (um + if unitPt (isLevel_levelGS (Nat.le_add_left 1 k) hk) x ∈ Zm
                then tm else 0) * (if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D))).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D).Ψ
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D))).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then ψh (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0)))).1
        (rawOf (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
              (Nat.le_add_left 1 k) D),
            (fun x i => (um + if unitPt (isLevel_levelGS (Nat.le_add_left 1 k) hk) x ∈ Zm
                then tm else 0) * (if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D))).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D).Ψ
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), rawOf
                  (localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
                  (Nat.le_add_left 1 k) D))).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then ψh (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0)))) C := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hxi := one_le_xiC1 d
  have hK1 : 0 < bgK1 d L N := bgK1_pos d L N
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hle : eps ≤ eps' := by nlinarith
  have hc1 : xiC1 d * eps ≤ bgC1 d L N := hc7.trans (c7_le_bgC1 d L N BG κ)
  have hc0 : xiC1 d * eps ≤ bgC0 d L N := hc1.trans (bgC1_le_bgC0 d L N hd0)
  have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
    have := HB.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
  exact coef_eTermFun_replacement_marked_gen (isLevel_levelGS (Nat.le_add_left 1 k) hk) hG hk1
    (localB_cubeAligned hk Yp _ hm₁) (localB_supSep hk Yp _)
    (localB_drop_precedes hk (Nat.le_succ k) Yp _ _)
    (localB_drop_Ω hk (Nat.le_succ k) Yp _ _ (le_refl k)) (localB_drop_top hk (Nat.le_succ k) Yp _ _)
    hN hm₁ hM hag hagm hagl hagl hS HB HB' ha₁ ha₂ hκ hMc hMX hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol
    hSol' ac Fk E C hR' hRκ heps hsmall hc7 hphi hle hsmall' hc7' hphi' hδ₀e hD
    (localB_xiCData_restrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
      (Nat.le_add_left 1 k) HB' HB.mass hδ0 le_rfl hc0 hc1 hνε hεb D (xiCData_inDomainC HB hsmall hD))
    (fun x hx => localBRestrict_eq_of_mem_top (Nat.le_add_left 1 k) D hx) hmarD' hαD' hsm cc hcψ Zm
    um tm hδ₁m ψh hψh hRC hRX hRk (localB_collar_margin hk (le_refl (minSep L (L ^ m₁))) hYp hRY)

/-- **The replacement identity along the masked tangent as an identity of functions of the raw
datum**: `coef_eTermFun_replacement_localB_marked` with the datum replaced by a raw datum `Θ` of the
chart and the restricted datum by the cut-off `clipRaw 𝔹_{k+1}(Y⁺) Θ` (`rawOf_localBRestrict`). -/
theorem coef_eTermFun_replacement_localB_marked_raw (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 ×
        Fin N → ℂ) × ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1
        × Fin N → ℂ)
        (α : (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (C : Finset (ParIdx
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁))
      {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεb : xiC1 d * eps + (2 * bgK1 d L N + 1) * (xiC1 d * eps) ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (hΘ : Θ ∈ XiCRaw
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
      (compWeight L a₁) ν (k + 1) 1 eps)
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (Zm : Finset (unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (um tm : ℂ)
    (hδ₁m : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    (ψh : unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
      (k + 1) hk) × Fin N → ℂ) (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    {R : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hRC : ∀ i ∈ C, ∀ y ∈ Pset m₁ i.1.1, y ∈ R)
    (hRX : ∀ P ∈ cubeIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk), ¬ Disjoint (Pset m₁ P) X₁ → ∀ y ∈ Pset m₁ P, y ∈ R)
    (hRk : ∀ x ∈ dataSites Gk, x ∈ R)
    (hRY : ∀ x ∈ R, x ∈ Y) :
    coef (fun w => eTermFun (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk) Gk Gj Hm ac Fk E (F₁ (extParams
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
      Θ))
        (Sol (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w,
          flEdat (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk) Hm (F₁ (extParams
            (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
            X₁ w, Θ)) Θ.1
            (markedHatPsiF a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc F₁ Zm um tm
              (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) Θ ψh))).1
        (Θ, (markedHatPsiF a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc F₁ Zm um tm
              (extParams (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) Θ ψh))) C =
      coef (fun w => eTermFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0),
          flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ))
            (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ).1
            (fun x i => (um + if unitPt (isLevel_levelGS (Nat.le_add_left 1 k) hk) x ∈ Zm
                then tm else 0) * (if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then ψh (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0)))).1
        (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ,
            (fun x i => (um + if unitPt (isLevel_levelGS (Nat.le_add_left 1 k) hk) x ∈ Zm
                then tm else 0) * (if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) X₁ w) P.1 else 0), clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then ψh (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0)))) C := by
  obtain ⟨D, hD, rfl⟩ := hΘ
  rw [← rawOf_localBRestrict (X := Yp) (hsep := le_refl (minSep L (L ^ m₁)))
    (Nat.le_add_left 1 k) D]
  exact coef_eTermFun_replacement_localB_marked hG hk1 hk Y Yp hYp hN hm₁ hM hag hagm hagl hS HB
    HB' ha₁ ha₂ hκ hMc hMX hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E C hR' hRκ heps hsmall
    hc7 hphi hεb hsmall' hc7' hphi' hδ₀e hD hmarD' hαD' hsm cc hcψ Zm um tm hδ₁m ψh hψh hRC hRX
    hRk hRY

/-- **The marked Y-term of an inherited label recomputed on `𝔹_{k+1}(Y⁺)`, as a function of the
datum.**  The term `evTerm … (FFmarked … Φ Zm um tm) Y` of the expansion along the masked tangent
(the family `Ev Y um tm` of `classOldMarksY_expansion`, with `Φ = eTermFun` of the label) equals,
at every point `(Θ, ψ̂)` of the chart times the box, the sum over the same connected families
`𝒞` (`Y[𝒞] = Y`) of the coefficients of the term recomputed on `(𝔹_{k+1}(Y⁺), 𝔹_k(Y⁺))` along the
site-wise multiple `(um + tm 1[·])` of the local hat lift, at the cut-off `clipRaw 𝔹_{k+1}(Y⁺) Θ`
and `ψ̂` (`coef_eTermFun_replacement_localB_marked_raw` with the read region `Y`). -/
theorem evTerm_FFmarked_replacement_localB (hG : IsLevel Hm k) (hk1 : 1 ≤ k)
    (hk : k + 1 ≤ k + 1) (Y Yp : Set (CTorus d L N₁ m₁ (k + 1)))
    (hYp : ∀ z, z ∈ Yp ↔ ∃ x ∈ Y, ∃ y : CTorus d L N₁ m₁ (k + 1),
      fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast y : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) =
        fineCubeIdx (L ^ m₁) N₁ L (k + 1) (k + 1)
          (torusCast z : Torus d (L ^ m₁ * N₁ * L ^ (k + 1))) ∧
      supDist x y ≤ 2 * L ^ (k + 1 + m₁))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1))
    (hagm : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1))
    (hagl : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {c BG a₁ : ℝ} (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (HB : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) (HB' : BgHyp d L (k + 1) (minSep L (L ^ m₁))
      (compWeight L a₁) ν)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {κ : ℝ} (hκ : 0 < κ) (hMc : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {F₁ : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 ×
        Fin N → ℂ) × ((Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ)}
    {F₁' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (D : BgData
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k + 1) (ϱ := ϱ) (k + 1) hk) (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ :
        (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1
        × Fin N → ℂ)
        (α : (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk).Ω 1 → ℂ), Dec2.IsDecBg (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
          (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
    (hF₁' : ∀ (s : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N),
      (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D →
      ∀ (φ : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ)
        (α : (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
          F₁' (s, rawOf D) = (φ, α))
    {c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₀ δ₁ : ℝ} (h0 : 0 ≤ δ₀) (h1 : 0 < δ₁)
    (hδ₀ : δ₀ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    {Sol' : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N →
      ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk)) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false δ₀ δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf
          (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk))
          Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
          (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k + 1) (ϱ := ϱ) (k + 1) hk)) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    (hSol' : ∀ p : Dec2.DecParams (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
        Edat (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N,
      (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) N false δ₀ δ₁ p.2 →
        (Sol' p).1 = dphi (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
          (Dec2.decG (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1)
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν p.1
                false
          p.2.2.1 p.2.1
          (pertSource (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                p.2.2.2.1
            p.2.2.2.2) (Sol' p).2 ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).2
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (Sol' p).1
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ,
          Small (localB k (Nat.le_succ k)
            (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
              Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) δα'
            (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
                  p.1 false
            p.2.2.1 p.2.1
            (pertSource (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁)
                  p.2.2.2.1
              p.2.2.2.2) δα' → δα' = (Sol' p).2))
    (ac : ℕ → ℝ)
    (Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ))
    (E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ)
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {R' : ℝ} (hR' : 1 < R')
    (hRκ : R' ≤ Real.exp κ)
    {eps eps' : ℝ} (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    (hεb : xiC1 d * eps + (2 * bgK1 d L N + 1) * (xiC1 d * eps) ≤ eps')
    (hsmall' : (4 * d + 6) * ((2 * d + 1) * eps') ≤ 1) (hc7' : xiC1 d * eps' ≤ c7 d L N BG κ)
    (hphi' : (3 + K4 d L N BG κ) * (xiC1 d * eps') < 1 / 2)
    (hδ₀e : 2 * (K4 d L N BG κ * (xiC1 d * eps')) ≤ δ₀)
    {δc : ℝ} (hmarD' : decDomMargin d L N BG κ (xiC1 d * eps') < δc)
    (hαD' : K4 d L N BG κ * (xiC1 d * eps') < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (Zm : Finset (unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk))) (um tm : ℂ)
    (hδ₁m : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁)
    {m₀ : ℕ} (hU : LayerUnion (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
      (ϱ := ϱ) (k + 1) hk) m₀) (hNm : L ^ m₀ ∣ N₁)
    (hXY : ∀ P ∈ cubeIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k + 1) (ϱ := ϱ) (k + 1) hk), ¬ Disjoint (Pset m₁ P) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ∀ y ∈ Pset m₁ P, y ∈ Y)
    (hkY : ∀ x ∈ dataSites Gk, x ∈ Y) :
    ∀ u ∈ XiCRaw (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk)
      (compWeight L a₁) ν (k + 1) 1 eps ×ˢ {ψh : unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ |
        ∀ p, ‖ψh p‖ ≤ cψ},
    evTerm (fun i : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) m₀ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))
      (FFmarked X₁f a₁ ν (isLevel_levelGS (Nat.le_add_left 1 k) hk) cc F₁ Sol
        (eTermFun (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) Gk Gj Hm ac Fk E) Zm um tm) Y u =
    evTerm (fun i : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) m₀ (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))
      (fun (v : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) × Fin N → ℂ))
        (w : ParIdx (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) =>
      eTermFun (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj
        (localB k (Nat.le_succ k)
          (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
            Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
        ac Fk E
        (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0), v.1))
        (Sol' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1)
            then Dec2.extS (coverOf (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
              (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
              (k := k + 1) (ϱ := ϱ) (k + 1) hk) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0),
          flEdat (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
            (localB k (Nat.le_succ k)
              (↑((localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω k) :
                Set (CTorus d L N₁ m₁ (k + 1))) (le_refl (minSep L (L ^ m₁))))
            (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                (k + 1) then Dec2.extS (coverOf
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                  (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                  (k := k + 1) (ϱ := ϱ) (k + 1) hk) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0), v.1))
            (v.1).1
            (fun x i => (um + if unitPt (isLevel_levelGS (Nat.le_add_left 1 k) hk) x ∈ Zm
                then tm else 0) * (if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0), v.1)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (v.1).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0), v.1)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then v.2 (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0)))).1
        (v.1,
            (fun x i => (um + if unitPt (isLevel_levelGS (Nat.le_add_left 1 k) hk) x ∈ Zm
                then tm else 0) * (if h : unitBlock x ∈
                unitPts (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
              (cc • (decCovSqrt (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0), v.1)).2
                (Dec2.extS (coverOf (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                  (fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0))
                (barField (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))
                  (v.1).1
                  (F₁' ((fun P => if P.1.2 ∈ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω
                  (k + 1) then Dec2.extS (coverOf
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk)) (extParams
                    (Def6.levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
                    (k := k + 1) (ϱ := ϱ) (k + 1) hk) (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) w) P.1 else 0), v.1)).1)
                (unitQ (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
                (unitP (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ
                (fun p => if hp : p.1.1 ∈ unitPts (Def6.levelGS (d := d) (L := L) (N₁ := N₁)
                  (m₁ := m₁) (k := k + 1) (ϱ := ϱ) (k + 1) hk) then v.2 (⟨p.1.1, hp⟩, p.2)
                  else 0))) (⟨unitBlock x, h⟩, i)
              else 0))))
      Y (clipRaw (localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) u.1, u.2) := by
  classical
  rintro ⟨Θ, ψh⟩ ⟨hΘ, hψh⟩
  unfold evTerm FFmarked
  refine Finset.sum_congr rfl fun C hC => ?_
  have hY := ((mem_connFams _).1 hC).2
  exact coef_eTermFun_replacement_localB_marked_raw hG hk1 hk Y Yp hYp hN hm₁ hM hag hagm hagl hS
    HB HB' ha₁ ha₂ hκ hMc hMX hF₁ hF₁' hF₂ hM₂ h0 h1 hδ₀ hδ₁ hSol hSol' ac Fk E C hR' hRκ heps
    hsmall hc7 hphi hεb hsmall' hc7' hphi' hδ₀e Θ hΘ hmarD' hαD' hsm cc hcψ Zm um tm hδ₁m ψh hψh
    (R := Finset.univ.filter (· ∈ Y))
    (fun i hi y hy => by
      rw [Finset.mem_filter, ← hY]
      exact ⟨Finset.mem_univ _,
        Or.inr (Set.mem_iUnion₂.2 ⟨i, hi, Pset_subset_Dsites hU hNm i.1.2 hy⟩)⟩)
    (fun P hP hdis y hy => Finset.mem_filter.2 ⟨Finset.mem_univ _, hXY P hP hdis y hy⟩)
    (fun x hx => Finset.mem_filter.2 ⟨Finset.mem_univ _, hkY x hx⟩)
    (fun x hx => (Finset.mem_filter.1 hx).2)

end Assembly

end Balaban.Localization
