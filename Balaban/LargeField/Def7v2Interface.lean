/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Def7v2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Def-7 v2, part 3: the SF-to-LF interface of Scheme A (W2-RESOLVE §3) -- DRAFT

**Draft, pending Roland's answer to Q13.**  `notes/phase1/W2-RESOLVE.md` §§3-4 (Scheme A, the
author's decision): the small-field class uses complete backgrounds at every scale (solver mass
`Rg.sfBgMass k = ν_k L^{-2k}`), the large-field operators keep field-free backgrounds below `k₀`
(solver mass `Rg.lfBgMass k`), and the exact difference of the two main actions goes into the
large-field kernel.

Whole-lattice form, on a Def-6 torus, for a datum `D` (same generating set, physical action, data
for the two backgrounds `φ^m = bgField(…, sfBgMass, D)`, `φ^0 = bgField(…, lfBgMass, D)`):

* `expoAt`: the exponent of the density with given action mass and solver mass
  (`expo2_eq_expoAt`: the exponent of `Def6v2.IsSF2` is `expoAt` at the physical and the complete
  mass);
* `chordD`, `deltaE`, `deltaF` (W2-RESOLVE (3.2)): the chord
  `D = β_k [A^phys(D, φ^0) - A^phys(D, φ^m)]` (fine-unit coefficient `β_k L^{-k(d-2)}`), the
  differences `ΔE`, `ΔF` of the inherited terms at the two composed fields;
* `sfToLF_identity` (**W2-RESOLVE (3.1), the exact density identity**):
  `expo(φ^m) = expo(φ^0) + D + ΔE + ΔF(g)`;
* `chordD_of_lt`, `deltaE_of_lt`, `deltaF_of_lt`: above the switch the two backgrounds coincide and
  the three corrections vanish;
* `SFtoLFData`, `IfConsts`, `Overlap`, `SFtoLFInterface`: **the interface clause**: localized
  kernel data `D_Y` (real), `ΔE_Y`, `ΔF_Y(g)` (analytic in `g` on `‖g‖₁ < 1`) summing to `chordD`,
  `deltaE`, `deltaF` on the overlap of the two real background domains at real fields
  `|h| ≤ B_h`, with the **open estimates** `chord_bound` (W2-RESOLVE (3.5)), `dE_bound`, `dF_bound`
  ((3.6)) and the budget `budget` ((3.7)) as named clauses.  They are hypotheses to be proved, not
  facts; `D` and `ΔE` belong to the real-`h` kernel, `ΔF` to its `g`-analytic exponent;
* `sfToLFInterface_complete`, `sfToLFInterface_witness`: the clause is inhabited in the complete
  regime `k > k₀` (zero data);
* `IsRepA`: the landed `IsRep` with (D1-corr) and the interface clause on every Def-6 torus.

**Not proved / recorded.**  (i) For `k ≤ k₀` the interface is not inhabited here: already for zero
terms the chord is the positive difference of the physical action at the free and at the complete
background, and its bound (3.5) is the open estimate; `IsRepA` (which has `k ≤ k₀` through (D9))
therefore has no witness, is not used as a hypothesis, and needs an exemption from hard rule 10 or
the estimate.  (ii) W2-RESOLVE (3.6) bounds `ΔF` by `C_F E₀ m_j/ε_j`; the Lean `ℱ_k = Fcomp`
contains the leading term `⟨g, φ_k⟩`, whose difference `⟨g, φ^m - φ^0⟩` is not an inherited term
and is `O(m_j)` (Q13-ANSWER (3.4)), so `dF_bound` has the form `C_F (m_k + E₀ m_k/ε_k)`.  (iii) The
clause is the whole-lattice form; its restriction to the LF region and collar (the common-collar
identity of COLLAR-RULING, the gluing at the collar, the support of the kernel) is not formalized.
-/

@[expose] public section

namespace Balaban.LargeField.Def7v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.LargeField.Def7

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-! ### The exact density identity (W2-RESOLVE (3.1)-(3.2)) -/

/-- The exponent of the density (H.1) with the action mass `mA` and the solver mass `μ` given
separately. -/
noncomputable def expoAt (P : Def6.Consts) (β a : ℕ → ℝ) (Tm : Terms d L N₁ m₁ k N ϱ)
    (Ek mA μ : ℝ) (D : BgData (topGS d L N₁ m₁ k ϱ) N) (g : Fld d L N₁ m₁ k N) : ℂ :=
  -((betaFine d L k (β k) : ℝ) : ℂ) *
      ((action (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) mA D
        (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) μ D) : ℝ) : ℂ) +
    Ecomp P.m₀ Tm (aIdeal L k (a k)) μ D -
    (Ek : ℂ) * (((N₁ * L ^ m₁) ^ d : ℕ) : ℂ) +
    Fcomp P.m₀ Tm (aIdeal L k (a k)) μ D g

/-- The exponent of the small-field class of the second version is `expoAt` at the physical action
mass and the complete solver mass. -/
theorem expo2_eq_expoAt (P : Def6.Consts) (Rg : Regime L) (β a : ℕ → ℝ)
    (Tm : Terms d L N₁ m₁ k N ϱ) (Ek : ℝ) (D : BgData (topGS d L N₁ m₁ k ϱ) N)
    (g : Fld d L N₁ m₁ k N) :
    expo2 P Rg β a Tm Ek D g = expoAt P β a Tm Ek (Rg.physMass k) (Rg.sfBgMass k) D g := rfl

/-- **The chord `D_{k,D}`** (W2-RESOLVE (3.2)): `β_k [A^phys(D, φ^0) - A^phys(D, φ^m)]`, the
physical action at the field-free (LF) background minus the physical action at the complete
background, with the fine-unit coefficient. -/
noncomputable def chordD (Rg : Regime L) (β a : ℕ → ℝ) (D : BgData (topGS d L N₁ m₁ k ϱ) N) :
    ℝ :=
  betaFine d L k (β k) *
    (action (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.physMass k) D
        (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.lfBgMass k) D) -
      action (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.physMass k) D
        (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k)) (Rg.sfBgMass k) D))

/-- **`ΔE_{k,D}`** (W2-RESOLVE (3.2)): the inherited energy terms at the complete composed fields
minus the same at the field-free composed fields. -/
noncomputable def deltaE (P : Def6.Consts) (Rg : Regime L) (a : ℕ → ℝ)
    (Tm : Terms d L N₁ m₁ k N ϱ) (D : BgData (topGS d L N₁ m₁ k ϱ) N) : ℂ :=
  Ecomp P.m₀ Tm (aIdeal L k (a k)) (Rg.sfBgMass k) D -
    Ecomp P.m₀ Tm (aIdeal L k (a k)) (Rg.lfBgMass k) D

/-- **`ΔF_{k,D}(g)`** (W2-RESOLVE (3.2)): the generating functional `ℱ_k` at the complete
backgrounds minus the same at the field-free backgrounds. -/
noncomputable def deltaF (P : Def6.Consts) (Rg : Regime L) (a : ℕ → ℝ)
    (Tm : Terms d L N₁ m₁ k N ϱ) (D : BgData (topGS d L N₁ m₁ k ϱ) N) (g : Fld d L N₁ m₁ k N) : ℂ :=
  Fcomp P.m₀ Tm (aIdeal L k (a k)) (Rg.sfBgMass k) D g -
    Fcomp P.m₀ Tm (aIdeal L k (a k)) (Rg.lfBgMass k) D g

/-- **The exact density identity** (W2-RESOLVE (3.1)): the complete-reference exponent is the
field-free-reference exponent plus the chord, `ΔE` and `ΔF(g)`. -/
theorem sfToLF_identity (P : Def6.Consts) (Rg : Regime L) (β a : ℕ → ℝ)
    (Tm : Terms d L N₁ m₁ k N ϱ) (Ek : ℝ) (D : BgData (topGS d L N₁ m₁ k ϱ) N)
    (g : Fld d L N₁ m₁ k N) :
    expoAt P β a Tm Ek (Rg.physMass k) (Rg.sfBgMass k) D g =
      expoAt P β a Tm Ek (Rg.physMass k) (Rg.lfBgMass k) D g + ((chordD Rg β a D : ℝ) : ℂ) +
        deltaE P Rg a Tm D + deltaF P Rg a Tm D g := by
  unfold expoAt chordD deltaE deltaF
  push_cast
  ring

theorem chordD_of_lt {Rg : Regime L} (h : Rg.kZero < k) (β a : ℕ → ℝ)
    (D : BgData (topGS d L N₁ m₁ k ϱ) N) : chordD Rg β a D = 0 := by
  unfold chordD
  rw [Rg.lfBgMass_eq_sfBgMass_of_lt h, sub_self, mul_zero]

theorem deltaE_of_lt {Rg : Regime L} (h : Rg.kZero < k) (P : Def6.Consts) (a : ℕ → ℝ)
    (Tm : Terms d L N₁ m₁ k N ϱ) (D : BgData (topGS d L N₁ m₁ k ϱ) N) :
    deltaE P Rg a Tm D = 0 := by
  unfold deltaE
  rw [Rg.lfBgMass_eq_sfBgMass_of_lt h, sub_self]

theorem deltaF_of_lt {Rg : Regime L} (h : Rg.kZero < k) (P : Def6.Consts) (a : ℕ → ℝ)
    (Tm : Terms d L N₁ m₁ k N ϱ) (D : BgData (topGS d L N₁ m₁ k ϱ) N) (g : Fld d L N₁ m₁ k N) :
    deltaF P Rg a Tm D g = 0 := by
  unfold deltaF
  rw [Rg.lfBgMass_eq_sfBgMass_of_lt h, sub_self]

/-! ### The interface clause (W2-RESOLVE (3.5)-(3.7)) -/

/-- **The localized kernel data of the interface**: `D_{k,Y}` (real), `ΔE_{k,Y}`, `ΔF_{k,Y}(g)`
for the polymers `Y ∈ 𝒟_k` and a datum `D`. -/
structure SFtoLFData (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ) where
  /-- `D_{k,Y}`, in the real-`h` kernel -/
  Dloc : Set (Localization.CTorus d L N₁ m₁ k) → BgData (topGS d L N₁ m₁ k ϱ) N → ℝ
  /-- `ΔE_{k,Y}`, in the real-`h` kernel -/
  Eloc : Set (Localization.CTorus d L N₁ m₁ k) → BgData (topGS d L N₁ m₁ k ϱ) N → ℂ
  /-- `ΔF_{k,Y}(g)`, in the `g`-analytic kernel exponent -/
  Floc : Set (Localization.CTorus d L N₁ m₁ k) → BgData (topGS d L N₁ m₁ k ϱ) N →
    Fld d L N₁ m₁ k N → ℂ

/-- The constants of the interface (W2-RESOLVE (3.5)-(3.7)): the field bound `B_h`, the constants
and rates of the three estimates, the regime constant `C₀` (`β_k m_k ≤ C₀`), `C_int` and the
large-field reserve `η_LF`. -/
structure IfConsts where
  Bh : ℝ
  CD : ℝ
  κD : ℝ
  CE : ℝ
  κE : ℝ
  CF : ℝ
  κF : ℝ
  C0 : ℝ
  Cint : ℝ
  η : ℝ

/-- **The overlap** on which the conversion is made (W2-RESOLVE §3: "identity (3.1) applies only on
the overlap where both background maps and their inherited terms are defined"): real data with
`|h₀| ≤ B_h` in the real background domain of BG Theorem 7.1 at both solver masses. -/
def Overlap (Rg : Regime L) (Bh : ℝ) (D : BgData (topGS d L N₁ m₁ k ϱ) N) : Prop :=
  ∃ (Ψ₀ : Localization.CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ),
    Realizes D Ψ₀ h₀ ∧ rn h₀ ≤ Bh ∧
      InUnionDomainR (topGS d L N₁ m₁ k ϱ) (bgC1 d L N) (Rg.sfBgMass k) D ∧
      InUnionDomainR (topGS d L N₁ m₁ k ϱ) (bgC1 d L N) (Rg.lfBgMass k) D

/-- **The SF-to-LF interface clause** (W2-RESOLVE §3, (3.1)-(3.7); Scheme A), whole-lattice form on
one Def-6 torus, for the regime `Rg`, the terms `Tm`, the localized kernel data `X` and the
constants `c`.
* `sum_D`, `sum_E`, `sum_F`: the localized data sum to the chord, `ΔE`, `ΔF` of the exact identity
  (3.1)-(3.2) on the overlap;
* `F_analytic`: `ΔF_Y` is analytic in the observable source `g` on `‖g‖₁ < 1`;
* `chord_bound` — **OPEN, W2-RESOLVE (3.5)**: `|D_{k,Y}| ≤ C_D β_k m_k² e^{-κ_D d_k(Y)}` (a real
  estimate, `|h| ≤ B_h`);
* `dE_bound`, `dF_bound` — **OPEN, W2-RESOLVE (3.6)**: `|ΔE_{k,Y}| ≤ C_E E₀ (m_k/ε_k) e^{-κ_E d_k(Y)}`,
  `|ΔF_{k,Y}(g)| ≤ C_F (m_k + E₀ m_k/ε_k) e^{-κ_F d_k(Y)}` for `‖g‖₁ < 1` (see the module docstring
  for the term `m_k`);
* `mass_le`, `budget` — W2-RESOLVE (3.7), at the pre-`k₀` scales: `β_k m_k ≤ C₀` and
  `C_int [C₀²/β_k + C₀ E₀/(β_k ε_k)] < η_LF`.
The estimates are clauses to be proved for the members constructed by the flow; they are not
established by P5-P7 or by the landed files.  Draft pending Roland's answer to Q13. -/
structure SFtoLFInterface (P : Def6.Consts) (Rg : Regime L) (β a : ℕ → ℝ)
    (Tm : Terms d L N₁ m₁ k N ϱ) (X : SFtoLFData d L N₁ m₁ k N ϱ) (c : IfConsts) : Prop where
  sum_D : ∀ D, Overlap Rg c.Bh D →
    ∑ᶠ Y ∈ {Y : Set (Localization.CTorus d L N₁ m₁ k) | IsPolyDom P.m₀ k Y}, X.Dloc Y D =
      chordD Rg β a D
  sum_E : ∀ D, Overlap Rg c.Bh D →
    ∑ᶠ Y ∈ {Y : Set (Localization.CTorus d L N₁ m₁ k) | IsPolyDom P.m₀ k Y}, X.Eloc Y D =
      deltaE P Rg a Tm D
  sum_F : ∀ D, Overlap Rg c.Bh D → ∀ g, Def6.l1 g < 1 →
    ∑ᶠ Y ∈ {Y : Set (Localization.CTorus d L N₁ m₁ k) | IsPolyDom P.m₀ k Y}, X.Floc Y D g =
      deltaF P Rg a Tm D g
  F_analytic : ∀ Y D, IsPolyDom P.m₀ k Y → Overlap Rg c.Bh D →
    AnalyticOnNhd ℂ (X.Floc Y D) {g | Def6.l1 g < 1}
  /-- OPEN estimate, W2-RESOLVE (3.5) -/
  chord_bound : ∀ Y D, IsPolyDom P.m₀ k Y → Overlap Rg c.Bh D →
    |X.Dloc Y D| ≤ c.CD * (β k * Rg.ν k ^ 2) * Real.exp (-c.κD * sizeJ P.m₀ k Y)
  /-- OPEN estimate, W2-RESOLVE (3.6) -/
  dE_bound : ∀ Y D, IsPolyDom P.m₀ k Y → Overlap Rg c.Bh D →
    ‖X.Eloc Y D‖ ≤ c.CE * P.E₀ * (Rg.ν k / P.eps d L k) * Real.exp (-c.κE * sizeJ P.m₀ k Y)
  /-- OPEN estimate, W2-RESOLVE (3.6) (with the leading term, Q13-ANSWER (3.4)) -/
  dF_bound : ∀ Y D, IsPolyDom P.m₀ k Y → Overlap Rg c.Bh D → ∀ g, Def6.l1 g < 1 →
    ‖X.Floc Y D g‖ ≤
      c.CF * (Rg.ν k + P.E₀ * (Rg.ν k / P.eps d L k)) * Real.exp (-c.κF * sizeJ P.m₀ k Y)
  /-- the regime bound `β_k m_k ≤ C₀` at the pre-`k₀` scales -/
  mass_le : k ≤ Rg.kZero → β k * Rg.ν k ≤ c.C0
  /-- the budget (3.7) at the pre-`k₀` scales -/
  budget : k ≤ Rg.kZero →
    c.Cint * (c.C0 ^ 2 / β k + c.C0 * P.E₀ / (β k * P.eps d L k)) < c.η

/-- **In the complete regime the interface is trivial**: for `k > k₀` the two backgrounds
coincide, the chord, `ΔE` and `ΔF` vanish, and the zero kernel data satisfy the clause, for every
choice of terms and nonnegative constants. -/
theorem sfToLFInterface_complete {P : Def6.Consts} {Rg : Regime L} {β a : ℕ → ℝ}
    (Tm : Terms d L N₁ m₁ k N ϱ) {c : IfConsts} (h : Rg.kZero < k) (hCD : 0 ≤ c.CD)
    (hCE : 0 ≤ c.CE) (hCF : 0 ≤ c.CF) (hβ : 0 ≤ β k) (hν : 0 ≤ Rg.ν k) (hE : 0 ≤ P.E₀)
    (hε : 0 ≤ P.eps d L k) :
    SFtoLFInterface P Rg β a Tm ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0⟩ c where
  sum_D := fun D _ => by rw [chordD_of_lt h]; simp
  sum_E := fun D _ => by rw [deltaE_of_lt h]; simp
  sum_F := fun D _ g _ => by rw [deltaF_of_lt h]; simp
  F_analytic := fun _ _ _ _ => analyticOnNhd_const
  chord_bound := fun Y D _ _ => by
    simp only [abs_zero]
    exact mul_nonneg (mul_nonneg hCD (mul_nonneg hβ (sq_nonneg _))) (Real.exp_pos _).le
  dE_bound := fun Y D _ _ => by
    simp only [norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCE hE) (div_nonneg hν hε)) (Real.exp_pos _).le
  dF_bound := fun Y D _ _ g _ => by
    simp only [norm_zero]
    exact mul_nonneg (mul_nonneg hCF (add_nonneg hν (mul_nonneg hE (div_nonneg hν hε))))
      (Real.exp_pos _).le
  mass_le := fun h' => absurd h' (not_le.2 h)
  budget := fun h' => absurd h' (not_le.2 h)

/-- **The interface clause is inhabited** (complete regime: `d = L = 3`, `N = 2`, `k = 1`,
`k₀ = 0`, the constants and coefficients of the landed witness, zero terms, all constants `1`). -/
theorem sfToLFInterface_witness (m₁ N₁ : ℕ) [NeZero N₁] (ϱ : ℝ) :
    SFtoLFInterface (d := 3) (L := 3) (N₁ := N₁) (m₁ := m₁) (k := 1) (N := 2) (ϱ := ϱ)
      (witnessConsts 1) ⟨0, witnessν 1⟩ witnessβ witnessa (zeroTerms 3 3 N₁ m₁ 1 2 ϱ)
      ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0⟩ ⟨1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩ :=
  sfToLFInterface_complete _ (by norm_num) zero_le_one zero_le_one zero_le_one
    (by simp [witnessβ]) (by simp only [witnessν]; positivity) le_rfl
    (eps_pos (d := 3) (L := 3) (P := witnessConsts 1) one_pos 1).le

/-! ### `IsRep` with the correction clause and the interface clause -/

section Rep

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {P6 : Def6.Consts} {C7 : Consts7} {k : ℕ} {ϱ : ℝ}

/-- **`IsRep_k` for Scheme A (draft)**: the landed `IsRep` with the clause (D1-corr) of P5 (1.8)
(`IsRepCorr`) and, on every Def-6 torus, the SF-to-LF interface clause for the regime `(k₀, ν)` of
the small-field data and some localized kernel data.  **No witness**: `IsRep` has `k ≤ k₀` (D9),
where the interface needs the open estimate W2-RESOLVE (3.5) (module docstring); this predicate is
not used as a hypothesis in any landed theorem. -/
def IsRepA (S : Setting) (R : ℕ → ℝ) (k0 K M : ℕ) [NeZero M] [NeZero S.L] (N : ℕ)
    (geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M) (cs : OpConsts)
    (P : BudgetConsts) (P6 : Def6.Consts) (C7 : Consts7) (β ν : ℝ)
    (hv : EuclideanSpace ℝ (Fin N)) (k : ℕ) {ϱ : ℝ} (hM6 : M = S.L ^ (P6.m₀ + C7.m₁))
    (hkK : k ≤ K) (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ)
    (ρ : ∀ (nK : ℕ) [NeZero nK], (BlockAt S (sides S.L K nK) M K k → EuclideanSpace ℝ (Fin N)) →
      (GIdx S (sides S.L K nK) M K N → ℂ) → ℂ)
    (St : ∀ (N₁ : ℕ) [NeZero N₁], SourceTerms S.d S.L N₁ C7.m₁ k N) (vc : CorrCoef S.d)
    (c : IfConsts) : Prop :=
  IsRepCorr S R k0 K M N geo cs P P6 C7 β ν hv k hM6 hkK F ρ St vc ∧
    ∀ (N₁ : ℕ) [NeZero N₁], ∃ X : SFtoLFData S.d S.L N₁ C7.m₁ k N ϱ,
      SFtoLFInterface P6 ⟨k0, F.sf.ν⟩ F.sf.β F.sf.a (F.sf.Tm N₁) X c

end Rep

end Balaban.LargeField.Def7v2
