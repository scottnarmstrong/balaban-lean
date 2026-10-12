/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerV2RenormCompare
public import Balaban.Observables.LayerV2RenormFirst
public import Balaban.Observables.LayerConst
public import Balaban.Observables.ImprovedFirst
public import Balaban.Observables.ImprovedBound
public import Balaban.SmallField.GsSpecStrong
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The observable layer of the second version: (P9 (4.10)) and Lemma 3.4

The ports to `IsObs2` / `IsSFObs2` of the landed `Mk_const` (`LayerConst`),
`improved_first_of_slice`, `improved_first_of_const`, `improved_second_bound`.  All four are
**direct ports**: the proofs use the clauses `boundM`, `analyticM`, `localM`, `normM` of the layer
and the geometry of the domains (`xiDom_orig`, `xiDom_const`, `xiDom_slice`, stated for an arbitrary
mass with `BgHyp`); the background mass enters only through the domain, which is the field domain
`Dom` of the class (the wide domain at the complete mass `Rg.sfBgMass k` for the main instance).
The conclusions are stated for the objects of the second version (`Mk2`, `Dom.dom`) and have the
constants of the landed statements.

* `IsObs2.Mk_const`: `M_k(x; h, h) = m_k(x) h` at the mass `Rg.sfBgMass k`;
* `IsObs2.improved_first_of_slice`, `IsObs2.improved_first_of_slice_xi`;
* `IsSFObs2.improved_first_of_const` (premise `hlayer` of the landed statement),
  `IsSFObs2.improved_first_of_const_strong` (`hlayer` derived from `GsSpecStrong`, as the landed
  `improved_first_of_const_strong`: the clause `gsStrong` of `SFTermClausesStrong`);
* `IsObs2.improved_second_bound`, `IsSFObs2.improved_second_bound`.

The comparisons with the landed statements in the complete regime `1 < β_k ν_k` are the
`…_of_v2` theorems.
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
open Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Metric Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

section Mk

variable {P : Consts} {Q : ObsConsts} {Rg : Regime L} {β a : ℕ → ℝ}
  {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ} {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}

/-- **`M_k(x; h, h) = m_k(x) h`** at the constant physical unit configuration (P9 (4.10)), second
version, at the background mass `Rg.sfBgMass k`.  The unit vector is a physical field of the
domain (`v ∈ Dom.phys`; `Set.univ` for `xiFieldDom`). -/
theorem IsObs2.Mk_const (hO : IsObs2 P Q Rg β a Dom Tm Ot Gker) {v : Fin N → ℝ}
    (hvD : v ∈ Dom.phys) (hv : v ⬝ᵥ v = 1) (D : BgData (topGS d L N₁ m₁ k ϱ) N)
    (hφ : ∀ (x : CTorus d L N₁ m₁ k) (i : Fin N),
      svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
        (Rg.sfBgMass k) D) x i = (v i : ℂ))
    (hψ : ∀ j, 1 ≤ j → j ≤ k →
      composedPair (aIdeal L k (a k)) (Rg.sfBgMass k) j D =
        (constFld (fun i => (v i : ℂ)), constFld (fun i => (v i : ℂ))))
    (x : CTorus d L N₁ m₁ k) (i : Fin N) :
    Mk2 P β a (Rg.sfBgMass k) Ot D x i = (mFactor β Ot x : ℂ) * (v i : ℂ) := by
  have hsum : ∀ j ∈ Finset.Icc 1 k, (((Real.sqrt (β (j - 1)))⁻¹ : ℝ) : ℂ) *
      Mobs P.m₀ Ot j x (composedPair (aIdeal L k (a k)) (Rg.sfBgMass k) j D).1
        (composedPair (aIdeal L k (a k)) (Rg.sfBgMass k) j D).2 i = 0 := by
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    rw [hψ j hj'.1 hj'.2]
    have := hO.Mobs_const_zero hj'.1 hj'.2 x hvD hv
    simp only [this, Pi.zero_apply, mul_zero]
  simp only [Mk2]
  rw [Finset.sum_eq_zero hsum, add_zero, hφ]

end Mk

section Slice

variable {P : Consts} {Q : ObsConsts} {Rg : Regime L} {β a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ} {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
  {j : ℕ}

/-- **The first bound of Lemma 3.4 (2.21), corrected form, from the slice and the constant part,
second version** (port of `improved_first_of_slice`; any field domain `Dom` of the layer). -/
theorem IsObs2.improved_first_of_slice {Dom : FieldDom d L N₁ m₁ k N ϱ}
    (hO : IsObs2 P Q Rg β a Dom Tm Ot Gker) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    (Ψ h : Fld d L N₁ m₁ k N) (c : Fin N → ℂ) (v : Fin N → ℝ) (hβ0 : 0 < β 0)
    {s c₁ Rad c' bc : ℝ} (hs : 0 < s) (hc₁ : 0 < c₁) (hRad : 0 < Rad) (hc' : 0 < c')
    (hL : (1 : ℝ) / 2 ≤ L) (hD : 0 ≤ sizeJ P.m₀ j X)
    (hΨ : Dom.dom j (Tm.gs j X) Ψ h)
    (hc0 : Dom.dom j (Tm.gs j X) (constFld c) h)
    (hslice : sizeJ P.m₀ j X ≤ c' / s → ∀ t : ℂ,
      ‖t‖ < Rad / (c₁ * (1 + sizeJ P.m₀ j X / (2 * (L : ℝ))) * s) →
      Dom.dom j (Tm.gs j X) (constFld c + t • (Ψ - constFld c)) h)
    (hconst : vn (Ot.M j x X (constFld c) h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
      (constFld (fun i => (v i : ℂ)))) ≤ bc) :
    vn (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst c₁ Rad c' * ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
        s * Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) + bc := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set A : ℝ := (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  -- the slice function and its values at `0` and `1`
  set Gs : ℂ → Fin N → ℂ := fun t => Ot.M j x X (constFld c + t • (Ψ - constFld c)) h with hGs
  have e1 : constFld c + (1 : ℂ) • (Ψ - constFld c) = Ψ := by
    funext z i; simp [constFld]
  have e0 : constFld c + (0 : ℂ) • (Ψ - constFld c) = constFld c := by simp
  have hG1 : Gs 1 = Ot.M j x X Ψ h := by simp only [hGs, e1]
  have hG0 : Gs 0 = Ot.M j x X (constFld c) h := by simp only [hGs, e0]
  set G' : ℂ → EuclideanSpace ℂ (Fin N) := fun t => WithLp.toLp 2 (Gs t) with hG'
  have hnorm : ∀ t, ‖G' t‖ = vn (Gs t) := fun t => rfl
  have hBv : vn (Ot.M j x X Ψ h) ≤ A * Real.exp (-P.κ * sizeJ P.m₀ j X) :=
    hO.boundM j hj1 hjk x X hX hx Ψ h hΨ
  have hBc : vn (Ot.M j x X (constFld c) h) ≤ A * Real.exp (-P.κ * sizeJ P.m₀ j X) :=
    hO.boundM j hj1 hjk x X hX hx _ h hc0
  have hdelta := improved_delta_bound (G := G') (A := A) (κ := P.κ) (D := sizeJ P.m₀ j X) (s := s)
    (L := (L : ℝ)) (c := c₁) (Rad := Rad) (c' := c') hA0 hD hs hL hc₁ hRad hc'
    (by rw [hnorm, hG1]; exact hBv) (by rw [hnorm, hG0]; exact hBc)
    (by
      intro hsm
      set r : ℝ := Rad / (c₁ * (1 + sizeJ P.m₀ j X / (2 * (L : ℝ))) * s) with hr
      have hmem := hslice hsm
      refine ⟨?_, ?_⟩
      · have hd : DifferentiableOn ℂ Gs (ball 0 r) := by
          intro t ht
          have h1 := hO.analyticM j hj1 hjk x X hX hx
            (constFld c + t • (Ψ - constFld c), h) (hmem t (mem_ball_zero_iff.1 ht))
          have h2 : AnalyticAt ℂ (fun u : ℂ => ((constFld c + u • (Ψ - constFld c) :
              Fld d L N₁ m₁ k N), (h : Fld d L N₁ m₁ k N))) t :=
            (analyticAt_const.add (analyticAt_id.smul analyticAt_const)).prod analyticAt_const
          exact (AnalyticAt.comp (g := fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
            Ot.M j x X p.1 p.2) (f := fun u : ℂ => ((constFld c + u • (Ψ - constFld c) :
              Fld d L N₁ m₁ k N), (h : Fld d L N₁ m₁ k N))) h1 h2).differentiableAt.differentiableWithinAt
        exact (EuclideanSpace.equiv (Fin N) ℂ).symm.differentiable.comp_differentiableOn hd
      · intro t ht
        rw [hnorm]
        exact hO.boundM j hj1 hjk x X hX hx _ h (hmem t ht))
  have hd2 : vn (Gs 1 - Gs 0) ≤ improvedConst c₁ Rad c' * (A * s * Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) := by
    have e : G' 1 - G' 0 = WithLp.toLp 2 (Gs 1 - Gs 0) := rfl
    rw [e] at hdelta
    exact hdelta
  rw [hG1, hG0] at hd2
  have htri : vn (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) ≤
      vn (Ot.M j x X Ψ h - Ot.M j x X (constFld c) h) +
      vn (Ot.M j x X (constFld c) h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) := by
    have e : Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ))) =
        (Ot.M j x X Ψ h - Ot.M j x X (constFld c) h) +
        (Ot.M j x X (constFld c) h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
          (constFld (fun i => (v i : ℂ)))) := by abel
    rw [e]
    exact vn_add' _ _
  linarith

/-- **`improved_first_of_slice` for the main instance (Scheme A)**: the domain is `Ξ^c_j` at the
complete mass `Rg.sfBgMass k`, as `XiDom` in the landed statement. -/
theorem IsObs2.improved_first_of_slice_xi
    (hO : IsObs2 P Q Rg β a (xiFieldDom (aIdeal L k (a k)) (Rg.sfBgMass k) (P.eps d L)) Tm Ot Gker)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    (Ψ h : Fld d L N₁ m₁ k N) (c : Fin N → ℂ) (v : Fin N → ℝ) (hβ0 : 0 < β 0)
    {s c₁ Rad c' bc : ℝ} (hs : 0 < s) (hc₁ : 0 < c₁) (hRad : 0 < Rad) (hc' : 0 < c')
    (hL : (1 : ℝ) / 2 ≤ L) (hD : 0 ≤ sizeJ P.m₀ j X)
    (hΨ : XiDom (Tm.gs j X) (aIdeal L k (a k)) (Rg.sfBgMass k) j (P.eps d L j) Ψ h)
    (hc0 : XiDom (Tm.gs j X) (aIdeal L k (a k)) (Rg.sfBgMass k) j (P.eps d L j) (constFld c) h)
    (hslice : sizeJ P.m₀ j X ≤ c' / s → ∀ t : ℂ,
      ‖t‖ < Rad / (c₁ * (1 + sizeJ P.m₀ j X / (2 * (L : ℝ))) * s) →
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (Rg.sfBgMass k) j (P.eps d L j)
        (constFld c + t • (Ψ - constFld c)) h)
    (hconst : vn (Ot.M j x X (constFld c) h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
      (constFld (fun i => (v i : ℂ)))) ≤ bc) :
    vn (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst c₁ Rad c' * ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
        s * Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) + bc :=
  hO.improved_first_of_slice hj1 hjk hX hx Ψ h c v hβ0 hs hc₁ hRad hc' hL hD hΨ hc0 hslice hconst

end Slice

section Const

variable {P : Consts} {Q : ObsConsts} {Rg : Regime L} {β a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ} {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ}

/-- **The first bound of Lemma 3.4 (2.21), corrected form, from the constant part, second
version** (port of `improved_first_of_const`): the small-field representation with its observable
layer on the wide domain at the complete mass `Rg.sfBgMass k`, at every scale `1 ≤ j ≤ k` (also
below the switch of the landed class).  The constants are those of the landed statement; the
datum `(Ψ₀ + Ψ'', h₀ + h')` lies in `Ψ̃^c(𝔹_j(X); δ, ε)` at the mass `Rg.sfBgMass k`. -/
theorem IsSFObs2.improved_first_of_const
    (hS : IsSFObs2 P Q Rg β a (completeXiDom P Rg a N₁) Tm ρd Ek Ot Gker)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (Rg.sfBgMass k))
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    {y : CTorus d L N₁ m₁ k} (hy : y ∈ X)
    (hlayer : ∀ z ∈ X, (Tm.gs j X).layerIndex z = j)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ} {h' : Fin N → ℂ} {δ ε δ₀ : ℝ}
    (hP : InPsiTildeC (Tm.gs j X) (Rg.sfBgMass k) δ ε Ψ₀ h₀ Ψ'' (fun _ => h'))
    (hβ0 : 0 < β 0) (hδ : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ δ₀) (hc0 : δ₀ ≤ bgC0 d L N)
    (hc1 : δ₀ ≤ bgC1 d L N)
    (hεj : δ₀ + (2 * bgK1 d L N + 1) * δ₀ ≤ P.eps d L j)
    (hsmall : 128 * (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) * δ ≤ δ₀)
    {v : Fin N → ℝ} {bc : ℝ}
    (hconst : vn (Ot.M j x X (constFld (fun i => (Ψ₀ y i : ℂ) + Ψ'' y i))
        (constFld (fun i => (h₀ i : ℂ) + h' i)) -
      Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤ bc) :
    vn (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) (constFld (fun i => (h₀ i : ℂ) + h' i)) -
        Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst
          (max (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) (2 * L * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁))))
          (δ₀ / 128) (δ₀ / (128 * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁)))) *
        ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * δ *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) + bc := by
  classical
  obtain ⟨hXΩ, hΩ⟩ := hS.sf.terms.gs_spec j hj1 hjk X hX
  have hLp : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  set M : ℝ := (L : ℝ) ^ (P.m₀ + m₁) with hM
  have hM1 : 1 ≤ M := one_le_pow₀ hL1
  have h3d : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  set K₀ : ℝ := 3 ^ d * (M * (4 * d * L) + 1) with hK₀
  have hK₀1 : 1 ≤ K₀ := by
    have : 0 ≤ M * (4 * d * L) := by positivity
    rw [hK₀]; nlinarith
  set E : ℝ := 3 ^ d * M with hE
  have hE0 : 0 < E := by positivity
  set c₁ : ℝ := max K₀ (2 * L * E) with hc₁
  have hc₁0 : 0 < c₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  set D : ℝ := sizeJ P.m₀ j X with hD
  have hD0 : 0 ≤ D := treeLenCovOne_nonneg _ _ _
  set A : ℝ := (β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hδ₀ : 0 < δ₀ := by linarith
  have h4δ : 4 * δ ≤ δ₀ := by nlinarith
  have hblock : ∀ z z', jBlock d L (N₁ * L ^ m₁) k j z = jBlock d L (N₁ * L ^ m₁) k j z' →
      z ∈ X → z' ∈ X := fun z z' h hz => IsPolyDom.block_closed hjk hN hX hz h
  have hδ₀1 : δ₀ ≤ 1 / 16 := hc0.trans (bgC0_le d L N)
  set hfld : Fld d L N₁ m₁ k N := constFld (fun i => (h₀ i : ℂ) + h' i) with hhf
  set c : Fin N → ℂ := fun i => (Ψ₀ y i : ℂ) + Ψ'' y i with hc
  set Sf : ℂ → Fld d L N₁ m₁ k N := fun t z i =>
    (sliceBase X Ψ₀ y z i : ℂ) + slicePert X Ψ₀ Ψ'' y t z i with hSf
  -- the endpoints
  have e1 : ∀ z ∈ X, Sf 1 z = fun i => (Ψ₀ z i : ℂ) + Ψ'' z i := by
    intro z hz; funext i
    simp only [hSf, sliceBase, slicePert, hz, ↓reduceIte]; ring
  have e0 : Sf 0 = constFld c := by
    funext z i
    by_cases hz : z ∈ X
    · simp only [hSf, sliceBase, slicePert, hz, ↓reduceIte, constFld, hc]; push_cast; ring
    · simp only [hSf, sliceBase, slicePert, hz, ↓reduceIte, constFld, hc]
  set Gs : ℂ → Fin N → ℂ := fun t => Ot.M j x X (Sf t) hfld with hGs
  have hG1 : Gs 1 = Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) hfld :=
    hS.obs.localM j x X (Sf 1) _ hfld hfld (fun z hz => ⟨e1 z hz, rfl⟩)
  have hG0 : Gs 0 = Ot.M j x X (constFld c) hfld := by simp only [hGs, e0]
  -- domain facts
  have hdomΨ := xiDom_orig (G := Tm.gs j X) (a := aIdeal L k (a k)) hBg hjk hP hδ hδε hε hc0 hc1 hεj
  have hdom0 := xiDom_const (G := Tm.gs j X) (a := aIdeal L k (a k)) hBg hjk hΩ hP (hXΩ hy)
    (hlayer y hy) hδ hδε hε hc0 hc1 hεj
  have hBΨ : vn (Gs 1) ≤ A * Real.exp (-P.κ * D) := by
    rw [hG1]; exact hS.obs.boundM j hj1 hjk x X hX hx _ hfld hdomΨ
  have hB0 : vn (Gs 0) ≤ A * Real.exp (-P.κ * D) := by
    rw [hG0]; exact hS.obs.boundM j hj1 hjk x X hX hx _ hfld hdom0
  set G' : ℂ → EuclideanSpace ℂ (Fin N) := fun t => WithLp.toLp 2 (Gs t) with hG'
  have hnorm : ∀ t, ‖G' t‖ = vn (Gs t) := fun t => rfl
  have hdelta := improved_delta_bound (G := G') (A := A) (κ := P.κ) (D := D) (s := δ)
    (L := (L : ℝ)) (c := c₁) (Rad := δ₀ / 128) (c' := δ₀ / (128 * E)) hA0 hD0 hδ (by linarith)
    hc₁0 (by positivity) (by positivity) (by rw [hnorm]; exact hBΨ) (by rw [hnorm]; exact hB0)
    (by
      intro hsm
      set r : ℝ := (δ₀ / 128) / (c₁ * (1 + D / (2 * (L : ℝ))) * δ) with hr
      have hmem : ∀ t : ℂ, ‖t‖ < r →
          XiDom (Tm.gs j X) (aIdeal L k (a k)) (Rg.sfBgMass k) j (P.eps d L j)
            (Sf t) hfld := by
        intro t ht
        -- the path bounds
        have hpb := fun z (hz : z ∈ X) =>
          psi_path_bounds (m₀ := P.m₀) hjk hN hP hX hXΩ hlayer hδ hy hz
        have hQeq : δ * (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L + sizeJ P.m₀ j X) + 1)) =
            δ * (K₀ + E * D) := by rw [hK₀, hE, hM, hD]; ring
        have hpb' : ∀ z ∈ X, rn (fun i => Ψ₀ z i - Ψ₀ y i) ≤ δ * (K₀ + E * D) ∧
            vn (fun i => Ψ'' z i - Ψ'' y i) ≤ δ * (K₀ + E * D) := fun z hz => by
          rw [← hQeq]; exact hpb z hz
        obtain ⟨hT, hδQ, -⟩ := slice_arith hδ hE0 hK₀1 (le_max_left _ _) (le_max_right _ _) hLp hD0
          hsmall hsm (norm_nonneg t) ht
        exact xiDom_slice (G := Tm.gs j X) (a := aIdeal L k (a k)) hBg hjk hΩ hP hXΩ hlayer hblock hy
          (fun z hz => (hpb' z hz).1) (fun z hz => (hpb' z hz).2) hδ hδε hε hδQ hδ₀1 h4δ hc0 hc1 hεj t hT
      have hd : DifferentiableOn ℂ Gs (ball 0 r) := by
        intro t ht
        have h1 := hS.obs.analyticM j hj1 hjk x X hX hx (Sf t, hfld) (hmem t (mem_ball_zero_iff.1 ht))
        have h2 : AnalyticAt ℂ (fun u : ℂ => (Sf u, hfld)) t :=
          (analyticAt_sliceField X Ψ₀ Ψ'' y t).prod analyticAt_const
        exact (AnalyticAt.comp (g := fun p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
          Ot.M j x X p.1 p.2) (f := fun u : ℂ => (Sf u, hfld)) h1 h2).differentiableAt.differentiableWithinAt
      refine ⟨?_, ?_⟩
      · exact (EuclideanSpace.equiv (Fin N) ℂ).symm.differentiable.comp_differentiableOn hd
      · intro t ht
        rw [hnorm]
        exact hS.obs.boundM j hj1 hjk x X hX hx _ hfld (hmem t ht))
  have hd2 : vn (Gs 1 - Gs 0) ≤ improvedConst c₁ (δ₀ / 128) (δ₀ / (128 * E)) *
      (A * δ * Real.exp (-(P.κ - 1) * D)) := by
    have e : G' 1 - G' 0 = WithLp.toLp 2 (Gs 1 - Gs 0) := rfl
    rw [e] at hdelta
    exact hdelta
  rw [hG1, hG0] at hd2
  have htri : vn (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) hfld -
        Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤
      vn (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) hfld - Ot.M j x X (constFld c) hfld) +
      vn (Ot.M j x X (constFld c) hfld - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) := by
    have e : Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) hfld -
        Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ))) =
        (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) hfld - Ot.M j x X (constFld c) hfld) +
        (Ot.M j x X (constFld c) hfld - Ot.M j x X (constFld (fun i => (v i : ℂ)))
          (constFld (fun i => (v i : ℂ)))) := by abel
    rw [e]
    exact vn_add' _ _
  linarith

/-- **`improved_first_of_const` with `hlayer` derived from the strong specification** of the local
sets (second version; the port of `improved_first_of_const_strong`): the premise `hS'` is the clause
`gsStrong` of `SFTermClausesStrong`, and the typing premise "`X` lies in the top layer `j` of
`𝔹_j(X)`" is no longer a hypothesis. -/
theorem IsSFObs2.improved_first_of_const_strong
    (hS : IsSFObs2 P Q Rg β a (completeXiDom P Rg a N₁) Tm ρd Ek Ot Gker)
    (hS' : ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∀ X, IsPolyDom P.m₀ j X →
      GsSpecStrong j hjk X (Tm.gs j X))
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (Rg.sfBgMass k))
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    {y : CTorus d L N₁ m₁ k} (hy : y ∈ X)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ} {h' : Fin N → ℂ} {δ ε δ₀ : ℝ}
    (hP : InPsiTildeC (Tm.gs j X) (Rg.sfBgMass k) δ ε Ψ₀ h₀ Ψ'' (fun _ => h'))
    (hβ0 : 0 < β 0) (hδ : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ δ₀) (hc0 : δ₀ ≤ bgC0 d L N)
    (hc1 : δ₀ ≤ bgC1 d L N)
    (hεj : δ₀ + (2 * bgK1 d L N + 1) * δ₀ ≤ P.eps d L j)
    (hsmall : 128 * (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) * δ ≤ δ₀)
    {v : Fin N → ℝ} {bc : ℝ}
    (hconst : vn (Ot.M j x X (constFld (fun i => (Ψ₀ y i : ℂ) + Ψ'' y i))
        (constFld (fun i => (h₀ i : ℂ) + h' i)) -
      Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤ bc) :
    vn (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) (constFld (fun i => (h₀ i : ℂ) + h' i)) -
        Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst
          (max (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) (2 * L * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁))))
          (δ₀ / 128) (δ₀ / (128 * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁)))) *
        ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * δ *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) + bc :=
  hS.improved_first_of_const hBg hj1 hjk hN hX hx hy
    (fun _ hz => (hS' j hj1 hjk X hX).toGsSpecCore.layerIndex_eq hj1 hjk hz) hP hβ0 hδ hδε hε hc0
    hc1 hεj hsmall hconst

/-- **`improved_first_of_const`, class form**: the strong specification of the local sets is the
clause `gsStrong` of `IsSF2`, so the premise `hS'` of `improved_first_of_const_strong` is
discharged from `hS`. -/
theorem IsSFObs2.improved_first_of_const'
    (hS : IsSFObs2 P Q Rg β a (completeXiDom P Rg a N₁) Tm ρd Ek Ot Gker)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (Rg.sfBgMass k))
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    {y : CTorus d L N₁ m₁ k} (hy : y ∈ X)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ} {h' : Fin N → ℂ} {δ ε δ₀ : ℝ}
    (hP : InPsiTildeC (Tm.gs j X) (Rg.sfBgMass k) δ ε Ψ₀ h₀ Ψ'' (fun _ => h'))
    (hβ0 : 0 < β 0) (hδ : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ δ₀) (hc0 : δ₀ ≤ bgC0 d L N)
    (hc1 : δ₀ ≤ bgC1 d L N)
    (hεj : δ₀ + (2 * bgK1 d L N + 1) * δ₀ ≤ P.eps d L j)
    (hsmall : 128 * (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) * δ ≤ δ₀)
    {v : Fin N → ℝ} {bc : ℝ}
    (hconst : vn (Ot.M j x X (constFld (fun i => (Ψ₀ y i : ℂ) + Ψ'' y i))
        (constFld (fun i => (h₀ i : ℂ) + h' i)) -
      Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤ bc) :
    vn (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) (constFld (fun i => (h₀ i : ℂ) + h' i)) -
        Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst
          (max (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) (2 * L * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁))))
          (δ₀ / 128) (δ₀ / (128 * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁)))) *
        ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * δ *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) + bc :=
  hS.improved_first_of_const_strong (fun j hj1 hjk X hX => hS.sf.gsStrong j hj1 hjk X hX) hBg hj1
    hjk hN hX hx hy hP hβ0 hδ hδε hε hc0 hc1 hεj hsmall hconst

end Const

section Second

variable {P : Consts} {Q : ObsConsts} {Rg : Regime L} {β a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ} {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ}

/-- **(2.22) with the entropy bound, second version** (port of `improved_second_bound`): if each
term obeys the improved bound `C A s e^{-(κ-1) d_j(X)}` and
`∑_{X ∋ x} e^{-(κ-1) d_j(X)} ≤ K₀`, then `|M^{(j)}(x; ψ, h)| ≤ C K₀ A s`.  The unit vector is a
physical field of the domain (`v ∈ Dom.phys`). -/
theorem IsObs2.improved_second_bound {Dom : FieldDom d L N₁ m₁ k N ϱ}
    (hO : IsObs2 P Q Rg β a Dom Tm Ot Gker) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (x : CTorus d L N₁ m₁ k) (Ψ h : Fld d L N₁ m₁ k N) {v : Fin N → ℝ}
    (hvD : v ∈ Dom.phys) (hv : v ⬝ᵥ v = 1) {C A s K₀ : ℝ} (hC : 0 ≤ C)
    (hfirst : ∀ X ∈ polysAt P.m₀ j x,
      vn (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) ≤
        C * (A * s * Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)))
    (hK : ∑ᶠ X ∈ polysAt P.m₀ j x, Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) ≤ K₀) (hAs : 0 ≤ A * s) :
    vn (Mobs P.m₀ Ot j x Ψ h) ≤ C * K₀ * (A * s) := by
  have hS : (polysAt P.m₀ j x).Finite := Set.toFinite _
  refine (hO.improved_second_of_first hj1 hjk x Ψ h hvD hv _ hfirst).trans ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ hS]
  rw [finsum_mem_eq_finite_toFinset_sum _ hS] at hK
  calc ∑ X ∈ hS.toFinset, C * (A * s * Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X))
      = C * (A * s) * ∑ X ∈ hS.toFinset, Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun X _ => by ring
    _ ≤ C * (A * s) * K₀ := mul_le_mul_of_nonneg_left hK (by positivity)
    _ = C * K₀ * (A * s) := by ring

/-- **`improved_second_bound` for the main instance (Scheme A)**: the observable layer on the wide
domain at the complete mass; every real unit vector is a physical field (`phys = univ`), as in the
landed statement. -/
theorem IsSFObs2.improved_second_bound
    (hS : IsSFObs2 P Q Rg β a (completeXiDom P Rg a N₁) Tm ρd Ek Ot Gker) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (x : CTorus d L N₁ m₁ k) (Ψ h : Fld d L N₁ m₁ k N) {v : Fin N → ℝ}
    (hv : v ⬝ᵥ v = 1) {C A s K₀ : ℝ} (hC : 0 ≤ C)
    (hfirst : ∀ X ∈ polysAt P.m₀ j x,
      vn (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) ≤
        C * (A * s * Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)))
    (hK : ∑ᶠ X ∈ polysAt P.m₀ j x, Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) ≤ K₀) (hAs : 0 ≤ A * s) :
    vn (Mobs P.m₀ Ot j x Ψ h) ≤ C * K₀ * (A * s) :=
  hS.obs.improved_second_bound hj1 hjk x Ψ h (Set.mem_univ v) hv hC hfirst hK hAs

end Second

/-! ### Comparison with the landed statements (complete regime `1 < β_k ν_k`) -/

section Compare

variable {P : Consts} {Q : ObsConsts} {β ν a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ} {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ}

/-- **Comparison for `Mk_const`**: in the complete regime of the landed class the landed
`Mk_const` is `IsObs2.Mk_const` for the landed layer (`IsObs.toObs2`, `Mk2_bgMass`). -/
theorem Mk_const_of_v2 (hβν : 1 < β k * ν k) (k₀ : ℕ) (hO : IsObs P Q β ν a Tm Ot Gker)
    {v : Fin N → ℝ} (hv : v ⬝ᵥ v = 1) (D : BgData (topGS d L N₁ m₁ k ϱ) N)
    (hφ : ∀ (x : CTorus d L N₁ m₁ k) (i : Fin N),
      svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
        (bgMass L k (β k) (ν k)) D) x i = (v i : ℂ))
    (hψ : ∀ j, 1 ≤ j → j ≤ k →
      composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D =
        (constFld (fun i => (v i : ℂ)), constFld (fun i => (v i : ℂ))))
    (x : CTorus d L N₁ m₁ k) (i : Fin N) :
    Mk P β ν a Ot D x i = (mFactor β Ot x : ℂ) * (v i : ℂ) := by
  have hμ : physMass L k (ν k) = bgMass L k (β k) (ν k) := physMass_eq_bgMass_of_lt hβν
  have h := (hO.toObs2 k₀ hμ).Mk_const (Set.mem_univ v) hv D
    (by rw [show (⟨k₀, ν⟩ : Regime L).sfBgMass k = bgMass L k (β k) (ν k) from hμ]; exact hφ)
    (by rw [show (⟨k₀, ν⟩ : Regime L).sfBgMass k = bgMass L k (β k) (ν k) from hμ]; exact hψ) x i
  rw [show (⟨k₀, ν⟩ : Regime L).sfBgMass k = bgMass L k (β k) (ν k) from hμ, Mk2_bgMass] at h
  exact h

/-- **Comparison for `improved_first_of_slice`**. -/
theorem improved_first_of_slice_of_v2 (hβν : 1 < β k * ν k) (k₀ : ℕ)
    (hO : IsObs P Q β ν a Tm Ot Gker) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    (Ψ h : Fld d L N₁ m₁ k N) (c : Fin N → ℂ) (v : Fin N → ℝ) (hβ0 : 0 < β 0)
    {s c₁ Rad c' bc : ℝ} (hs : 0 < s) (hc₁ : 0 < c₁) (hRad : 0 < Rad) (hc' : 0 < c')
    (hL : (1 : ℝ) / 2 ≤ L) (hD : 0 ≤ sizeJ P.m₀ j X)
    (hΨ : XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j) Ψ h)
    (hc0 : XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
      (constFld c) h)
    (hslice : sizeJ P.m₀ j X ≤ c' / s → ∀ t : ℂ,
      ‖t‖ < Rad / (c₁ * (1 + sizeJ P.m₀ j X / (2 * (L : ℝ))) * s) →
      XiDom (Tm.gs j X) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
        (constFld c + t • (Ψ - constFld c)) h)
    (hconst : vn (Ot.M j x X (constFld c) h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
      (constFld (fun i => (v i : ℂ)))) ≤ bc) :
    vn (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst c₁ Rad c' * ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) *
        s * Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) + bc := by
  have hμ : physMass L k (ν k) = bgMass L k (β k) (ν k) := physMass_eq_bgMass_of_lt hβν
  refine (hO.toObs2 k₀ hμ).improved_first_of_slice_xi hj1 hjk hX hx Ψ h c v hβ0 hs hc₁ hRad hc'
    hL hD ?_ ?_ ?_ hconst
  · rw [show (⟨k₀, ν⟩ : Regime L).sfBgMass k = bgMass L k (β k) (ν k) from hμ]; exact hΨ
  · rw [show (⟨k₀, ν⟩ : Regime L).sfBgMass k = bgMass L k (β k) (ν k) from hμ]; exact hc0
  · rw [show (⟨k₀, ν⟩ : Regime L).sfBgMass k = bgMass L k (β k) (ν k) from hμ]; exact hslice

/-- **Comparison for `improved_first_of_const`**: for a member of the landed class in its complete
regime, with its observable layer, the landed statement is `IsSFObs2.improved_first_of_const`
(`IsSF.toV2`, `IsObs.toObs2`). -/
theorem improved_first_of_const_of_v2 (hβν : 1 < β k * ν k) (k₀ : ℕ)
    (hO : IsObs P Q β ν a Tm Ot Gker) (hsf : IsSF P β ν a Tm ρd Ek)
    (hGS : ∀ j, 1 ≤ j → ∀ hjk : j ≤ k, ∀ X, IsPolyDom P.m₀ j X →
      GsSpecStrong j hjk X (Tm.gs j X))
    (hbg : BgHyp d L k ϱ (aIdeal L k (a k)) (bgMass L k (β k) (ν k)))
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ j X) {x : CTorus d L N₁ m₁ k} (hx : x ∈ X)
    {y : CTorus d L N₁ m₁ k} (hy : y ∈ X)
    (hlayer : ∀ z ∈ X, (Tm.gs j X).layerIndex z = j)
    {Ψ₀ : CTorus d L N₁ m₁ k → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' : CTorus d L N₁ m₁ k → Fin N → ℂ} {h' : Fin N → ℂ} {δ ε δ₀ : ℝ}
    (hP : InPsiTildeC (Tm.gs j X) (bgMass L k (β k) (ν k)) δ ε Ψ₀ h₀ Ψ'' (fun _ => h'))
    (hβ0 : 0 < β 0) (hδ : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ δ₀) (hc0 : δ₀ ≤ bgC0 d L N)
    (hc1 : δ₀ ≤ bgC1 d L N)
    (hεj : δ₀ + (2 * bgK1 d L N + 1) * δ₀ ≤ P.eps d L j)
    (hsmall : 128 * (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) * δ ≤ δ₀)
    {v : Fin N → ℝ} {bc : ℝ}
    (hconst : vn (Ot.M j x X (constFld (fun i => (Ψ₀ y i : ℂ) + Ψ'' y i))
        (constFld (fun i => (h₀ i : ℂ) + h' i)) -
      Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤ bc) :
    vn (Ot.M j x X (fun z i => (Ψ₀ z i : ℂ) + Ψ'' z i) (constFld (fun i => (h₀ i : ℂ) + h' i)) -
        Ot.M j x X (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) ≤
      improvedConst
          (max (3 ^ d * ((L : ℝ) ^ (P.m₀ + m₁) * (4 * d * L) + 1)) (2 * L * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁))))
          (δ₀ / 128) (δ₀ / (128 * (3 ^ d * (L : ℝ) ^ (P.m₀ + m₁)))) *
        ((β 0) ^ (-(1 / 2 : ℝ) + Q.ρ₁) * (L : ℝ) ^ (-((j : ℝ) * Q.ρ₀)) * δ *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)) + bc := by
  have hμ : physMass L k (ν k) = bgMass L k (β k) (ν k) := physMass_eq_bgMass_of_lt hβν
  have hs : (⟨k₀, ν⟩ : Regime L).sfBgMass k = bgMass L k (β k) (ν k) := hμ
  have hS : IsSFObs2 P Q ⟨k₀, ν⟩ β a (completeXiDom P ⟨k₀, ν⟩ a N₁) Tm
      (rhoV2 (ϱ := ϱ) ⟨k₀, ν⟩ β a ρd) Ek Ot Gker :=
    ⟨hsf.toV2 (k₀ := k₀) hGS hμ (Dom := completeXiDom P ⟨k₀, ν⟩ a N₁)
      (fun j G Ψ h' hp => by
        have hp' : XiDom G (aIdeal L k (a k)) (physMass L k (ν k)) j (P.eps d L j) Ψ h' := hp
        rw [← hμ]; exact hp'), hO.toObs2 k₀ hμ⟩
  refine IsSFObs2.improved_first_of_const hS (by rw [hs]; exact hbg) hj1 hjk hN hX hx hy hlayer
    (by rw [hs]; exact hP) hβ0 hδ hδε hε hc0 hc1 hεj hsmall hconst

/-- **Comparison for `improved_second_bound`**. -/
theorem improved_second_bound_of_v2 (hβν : 1 < β k * ν k) (k₀ : ℕ)
    (hO : IsObs P Q β ν a Tm Ot Gker) (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (x : CTorus d L N₁ m₁ k) (Ψ h : Fld d L N₁ m₁ k N) {v : Fin N → ℝ}
    (hv : v ⬝ᵥ v = 1) {C A s K₀ : ℝ} (hC : 0 ≤ C)
    (hfirst : ∀ X ∈ polysAt P.m₀ j x,
      vn (Ot.M j x X Ψ h - Ot.M j x X (constFld (fun i => (v i : ℂ)))
        (constFld (fun i => (v i : ℂ)))) ≤
        C * (A * s * Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X)))
    (hK : ∑ᶠ X ∈ polysAt P.m₀ j x, Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) ≤ K₀) (hAs : 0 ≤ A * s) :
    vn (Mobs P.m₀ Ot j x Ψ h) ≤ C * K₀ * (A * s) :=
  (hO.toObs2 k₀ (physMass_eq_bgMass_of_lt hβν)).improved_second_bound hj1 hjk x Ψ h
    (Set.mem_univ v) hv hC hfirst hK hAs

end Compare

end Balaban.Observables
