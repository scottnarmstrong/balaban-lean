/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledSqrt
public import Balaban.Localization.Decoupled2Geometry
public import Balaban.Localization.PairedLocalAgree
public import Balaban.Localization.DecoupledCovPrincipal
public import Balaban.Inhabited.LocalizationSettings

/-!
# The decoupled logarithm at zero cuts (the `J = ∅` term)

`notes/phase1/ROOTDET.md` §2 and §4 (package 2). The normalization of the fluctuation step is
`-(1/2)` times the trace of `decLog` at `s ≡ 1`; its cut expansion starts at the fully cut point.
Here `s₀ = extS G 0` is zero on the parameter cubes `cubeIdx G` and one outside.

Proved, with no hypotheses beyond typing data:

* the coefficient `sProd s₀ q` vanishes whenever `Qset G q` is non-empty, in particular for every
  `q ∈ cubeIdx G` (a centre lies in its own `Qset`); the only centres with coefficient `1` are
  those with empty `Qset` (`sProd_extS_zero_eq_one_iff`);
* every term of `Gstarx`, `Kcalx` carries such a coefficient (the sums run over `cubeIdx G`), so
  `Gsx G a aT x ν α s₀ = 0` and `decPi G a aT x ν α s₀ φ = 0`;
* `decCov … s₀ … = covA …` for every `x` (the integrand of `decLog` vanishes identically, not only
  after integration), hence `decLog … s₀ … = log a_k • (1 - P) + log (a_k + aT/L²) • P`
  (lifted to `N` components). This does not involve `φ`, `α`, `Q`, and no standing hypothesis.

Partial cuts (landed pieces only): `Zs_zeroCuts`, `Yreg_zeroCuts`, `Core_zeroCuts` (all empty at `s₀`),
`Qset_subset_of_mem_Zs` (if `s` vanishes on parameter cubes outside `J`, an active centre has its
footprint `Qset z` inside `J`). The landed locality theorems are used as they stand and are not
restated: `Dec2.dg5_support` (`G_s f` vanishes outside `Core s`, hypothesis `CoverLocalGeom`),
`Dec2.dg5_local` (`G_s f` agrees with `G_s α' f'` on a nearest-neighbour component `Y'` of
`Yreg s` when `α, α'` and `f, f'` agree on `Y'`; hypotheses `CoverBase`, `HatConn`, `AdmPot`, and
invertibility of `1 - Kcal`), `i4b_local` (background agreement) and `extS_relParams_zero`.

**DET-CUT-FACTOR (not proved).** For a cut configuration `s` (zero off a set `J`) and every `s'`
in a neighbourhood of `s`: with `Y_1, Y_2, …` the nearest-neighbour components of `Yreg s`, the
matrix `decLog G a aT ν α s' φ Q P` (resolvent integral `∫ (decCov - covA) dx`, the constrained
correction `liftOp (Gsx) - decPi` with its inverse `decM⁻¹`, and the baseline blocks of `P` and of
`liftRect Q`) has no matrix element between sites attached to two different components, and the
rooted diagonal trace depends only on the component of the root. Missing for it: the identification
of the `Gsx` of `DecoupledX` with `Dec2.Gs` on a self-cover (partly `Decoupled2Self`), locality of
`decM⁻¹`, `decN`, of the resolvent integral in `x`, and that the blocks of `P` fit inside single
components. The cheaper step `decCov` has no matrix elements between components is also not
proved; only the Green part is landed.

Not proved: this is only the `J = ∅` term of the cut expansion. The statement DET-CUT-FACTOR
(see the end of this file), the forest bound and the hull count are not proved. Nothing here
depends on a choice of generating set for the class terms.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix Set MeasureTheory Real

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}

/-- The fully cut parameters: zero on the parameter cubes, one outside (`extS G 0`). -/
noncomputable abbrev zeroCuts (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) :
    ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ := extS G 0

theorem zeroCuts_of_mem {P : ℕ × CTorus d L N₁ m₁ (k + 1)} (hP : P ∈ cubeIdx G) :
    zeroCuts G P = 0 := by
  simp [zeroCuts, extS, hP]

theorem zeroCuts_of_not_mem {P : ℕ × CTorus d L N₁ m₁ (k + 1)} (hP : P ∉ cubeIdx G) :
    zeroCuts G P = 1 := by
  simp [zeroCuts, extS, hP]

/-! ### T1: the coefficients -/

/-- Every centre of `cubeIdx G` lies in its own `Qset`. -/
theorem self_mem_Qset_zeroCuts {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G) :
    q ∈ Qset G q := by
  refine mem_Qset.2 ⟨hq, q.2, SameCell.refl _ _, fun μ => ⟨0, ?_⟩⟩
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := one_le_pow₀ hL
  have h2 : (0 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 := by positivity
  simp only [Int.cast_zero, zero_mul, add_zero]
  rw [show ((q.2 μ).val : ℝ) - (((q.2 μ).val : ℝ) + ((L : ℝ) ^ (q.1 + m₁) - 1) / 2)
      = -(((L : ℝ) ^ (q.1 + m₁) - 1) / 2) by ring, abs_neg,
    abs_of_nonneg (by linarith)]
  unfold hatRad
  linarith

/-- **T1.** At zero cuts the coefficient `s_q` vanishes whenever `Qset G q` is non-empty
(`Qset G q ⊆ cubeIdx G`, so non-empty means meeting `cubeIdx G`). -/
theorem sProd_zeroCuts_eq_zero {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (h : (Qset G q).Nonempty) :
    sProd G (zeroCuts G) q = 0 := by
  obtain ⟨P, hP⟩ := h
  exact Finset.prod_eq_zero hP (zeroCuts_of_mem (Qset_subset_cubeIdx q hP))

/-- Every `q ∈ cubeIdx G` has vanishing coefficient at zero cuts. -/
theorem sProd_zeroCuts_of_mem {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : q ∈ cubeIdx G) :
    sProd G (zeroCuts G) q = 0 :=
  sProd_zeroCuts_eq_zero ⟨q, self_mem_Qset_zeroCuts hq⟩

/-- Exactly which centres keep the coefficient `1` at zero cuts: those with empty `Qset`
(the empty product). Such a centre is not in `cubeIdx G`. -/
theorem sProd_zeroCuts_eq_one_iff {q : ℕ × CTorus d L N₁ m₁ (k + 1)} :
    sProd G (zeroCuts G) q = 1 ↔ Qset G q = ∅ := by
  constructor
  · intro h
    by_contra hne
    have := sProd_zeroCuts_eq_zero (Finset.nonempty_iff_ne_empty.2 hne)
    rw [h] at this
    exact one_ne_zero this
  · intro h
    simp [sProd, h]

theorem not_mem_cubeIdx_of_Qset_eq_empty {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (h : Qset G q = ∅) : q ∉ cubeIdx G := fun hq => by
  have := self_mem_Qset_zeroCuts hq
  simp [h] at this

/-! ### T2: the Green operator and covariance at zero cuts -/

section Zero

variable {α : G.Ω 1 → ℂ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι]
  {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}

theorem Gstarx_zeroCuts : Gstarx G a aT x ν α (zeroCuts G) = 0 := by
  unfold Gstarx
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [sProd_zeroCuts_of_mem hq, zero_smul]

theorem Kcalx_zeroCuts : Kcalx G a aT x ν α (zeroCuts G) = 0 := by
  unfold Kcalx
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [sProd_zeroCuts_of_mem hq, zero_smul]

/-- **T2.** The decoupled Green operator vanishes at zero cuts. -/
theorem Gsx_zeroCuts : Gsx G a aT x ν α (zeroCuts G) = 0 := by
  unfold Gsx
  rw [Gstarx_zeroCuts, zero_mul]

omit [Fintype κι] [DecidableEq κι] in
theorem liftOp_zero' : liftOp N (0 : Matrix κι κι ℂ) = 0 := by
  ext p q; simp [liftOp]

/-- The constrained projection `Π_{x,s}` vanishes at zero cuts. -/
theorem decPi_zeroCuts : decPi G a aT x ν α (zeroCuts G) φ = (0 : Matrix _ _ ℂ) := by
  unfold decPi
  rw [Gsx_zeroCuts, liftOp_zero']
  simp

/-- **T2.** At zero cuts the decoupled covariance is the baseline `covA`, for every `x`
(the correction vanishes identically). No standing hypothesis is used. -/
theorem decCov_zeroCuts :
    decCov G a aT x ν α (zeroCuts G) φ Q P =
      covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) := by
  unfold decCov
  rw [Gsx_zeroCuts, decPi_zeroCuts, liftOp_zero', sub_zero]
  simp

/-! ### T3: the logarithm at zero cuts -/

/-- **T3.** `decLog` at zero cuts is the explicit block-diagonal matrix
`log a_k (1 - P) + log (a_k + aT/L²) P` (acting on `N`-vector fields). -/
theorem decLog_zeroCuts :
    decLog G a aT ν α (zeroCuts G) φ Q P =
      ((Real.log (a k) : ℝ) : ℂ) • (1 - liftOp N P) +
        ((Real.log (a k + aT / (L : ℝ) ^ 2) : ℝ) : ℂ) • liftOp N P := by
  unfold decLog
  have : (fun x : ℝ => decCov G a aT x ν α (zeroCuts G) φ Q P -
      covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) = fun _ => 0 := by
    funext x; rw [decCov_zeroCuts, sub_self]
  rw [this]
  have h0 : intMat (volume.restrict (Ioi (0 : ℝ))) (fun _ => (0 : Matrix (κι × Fin N) (κι × Fin N) ℂ))
      = 0 := by
    ext p q; simp [intMat]
  rw [h0, sub_zero]

/-- The entries of `decLog` at zero cuts do not depend on `(φ, α)` (nor on `Q`). -/
theorem decLog_zeroCuts_indep (α' : G.Ω 1 → ℂ) (φ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)
    (Q' : Matrix κι (G.Ω 1) ℂ) :
    decLog G a aT ν α (zeroCuts G) φ Q P = decLog G a aT ν α' (zeroCuts G) φ' Q' P := by
  rw [decLog_zeroCuts, decLog_zeroCuts]

/-- **T3, rooted trace.** For a set `B` of sites, the rooted trace of `decLog` at zero cuts is
`-(1/2) ∑_{y ∈ B} N (log a_k (1 - P_{yy}) + log (a_k + aT/L²) P_{yy})`; it depends only on the
diagonal of `P` on `B`. -/
theorem rootedTrace_decLog_zeroCuts (B : Finset κι) :
    -(1 / 2 : ℂ) * ∑ y ∈ B, ∑ i : Fin N,
        decLog G a aT ν α (zeroCuts G) φ Q P (y, i) (y, i) =
      -(1 / 2 : ℂ) * ∑ y ∈ B, (N : ℂ) *
        (((Real.log (a k) : ℝ) : ℂ) * (1 - P y y) +
          ((Real.log (a k + aT / (L : ℝ) ^ 2) : ℝ) : ℂ) * P y y) := by
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [decLog_zeroCuts, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply_eq, liftOp, ite_true, smul_eq_mul]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Zero

/-! ### T4: partial cuts, the landed footprint statements -/

section Partial



/-- At zero cuts no centre is active: `Zs = ∅` for the self-cover (`Zs` is the set of centres
with `s_z ≠ 0`). Hence `Yreg` and `Core` are empty, consistent with `Gsx = 0`. -/
theorem Zs_zeroCuts : Dec2.Zs (coverOf G) (zeroCuts G) = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨hzc, hne⟩ := Finset.mem_filter.1 hz
  exact hne (sProd_zeroCuts_of_mem hzc)

theorem Yreg_zeroCuts (H : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) :
    Dec2.Yreg (coverOf G) H (zeroCuts G) = ∅ := by
  classical
  simp [Dec2.Yreg, Zs_zeroCuts]

theorem Core_zeroCuts : Dec2.Core (coverOf G) (zeroCuts G) = ∅ := by
  classical
  simp [Dec2.Core, Zs_zeroCuts]

/-- **Partial cuts.** If `s` vanishes on every parameter cube outside `J`, an active centre
(`s_z ≠ 0`) has its whole footprint `Qset z` inside `J`. So the Green operator `G_s` is supported
in `Core` of the active centres (`dg5_support`), and is local on a nearest-neighbour component of
`Yreg s` (`dg5_local`; both need `CoverLocalGeom`/`CoverBase`, `HatConn`, admissible potentials and
invertibility, see the module doc). -/
theorem Qset_subset_of_mem_Zs {J : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (hs : ∀ P ∈ cubeIdx G, P ∉ J → s P = 0)
    {z : ℕ × CTorus d L N₁ m₁ (k + 1)} (hz : z ∈ Dec2.Zs (coverOf G) s) : Qset G z ⊆ J := by
  classical
  obtain ⟨-, hne⟩ := Finset.mem_filter.1 hz
  intro P hP
  by_contra hPJ
  apply hne
  exact Finset.prod_eq_zero hP (hs P (Qset_subset_cubeIdx z hP) hPJ)

end Partial

/-! ### T5: non-vacuity -/

/-- The zero-cut parameters lie in the polydisc of `DecDom` for every `κ`: `‖s₀ P‖ = 0 < e^κ`
on the parameter cubes. -/
theorem norm_zeroCuts_lt (κ : ℝ) (P : cubeIdx G) : ‖zeroCuts G P‖ < Real.exp κ := by
  rw [zeroCuts_of_mem P.2, norm_zero]; exact Real.exp_pos κ

/-- **T5, an instance.** For the landed positive-scale setting (`d = L = 3`, `k = 1`, `a_k = 1`
since `compWeight 3 1 1 = 1`, `a_T = 1`, `ν = 0`), at zero cuts the diagonal entry of `decLog`
for `P = 0` on one site is `log 1 = 0`, for every potential and field. -/
theorem decLog_zeroCuts_instance :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (G : GeneratingSet 3 3 (6 * 3 ^ m₁) (1 + 1) ϱ),
      XSetting G (compWeight 3 1) 1 0 ∧ ∀ (α : G.Ω 1 → ℂ)
        (φ : CTorus 3 3 6 m₁ (1 + 1) → Fin 3 → ℂ) (Q : Matrix Unit (G.Ω 1) ℂ),
        decLog G (compWeight 3 1) 1 0 α (zeroCuts G) φ Q (0 : Matrix Unit Unit ℂ)
          ((), 0) ((), 0) = ((Real.log (compWeight 3 1 1) : ℝ) : ℂ) := by
  obtain ⟨m₁, ϱ, G, hX⟩ := Balaban.Inhabited.xSetting_nonempty
  refine ⟨m₁, ϱ, G, hX, fun α φ Q => ?_⟩
  rw [decLog_zeroCuts]
  simp [liftOp]

end Balaban.Localization
