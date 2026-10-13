/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCauchyBgSupport
public import Balaban.Fluctuation.DetCauchyAssembly
public import Balaban.Fluctuation.StepComplexCov
public import Balaban.Fluctuation.StepComplexThm31
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The polymer activity of the rooted determinant term with cut-dependent backgrounds

For a datum `D` of the chart `Ξ^c(𝔹_{k+1}; 1, ε)` let `F_B(s) = rootTraceBg B D s` be the rooted
trace of the set `B` of unit blocks at the decoupled background `(φ_s, α_s)` of `D`
(`DetCauchyChart`).  Its mixed differences have root-chain support (`DetCauchyBgSupport`) and obey
`‖Δ_J F_B‖ ≤ M_B (2 / e^κ)^{|J|}`, `M_B = ½ N |B| covBLog d L a_k (a₁/L²) κ`
(`rootTraceBg_cut_expansion`; the polydisc radius is the same `e^κ` as for fixed fields, and `κ` is
the parameter of `FlCore`).  The assembly of `DetCauchyAssembly` gives:

## Count and sums

* `card_supportBg_le`: at most `Δ^{2n}` cut sets of size `n` have `Δ_J F_B ≠ 0`,
  `Δ = max (detDeg d L + 1) |B|`.
* `sum_norm_mixDiff_rootTraceBg_le`, `norm_rootTraceBg_one_le`, `tail_norm_mixDiff_rootTraceBg_le`.

## Activity

* `detActivityBg m₀ a aT ν ρ D y Y`: the sum of `Δ_J F_{{y}}` over the cut sets `J` whose hull is
  the polymer `Y` (the only new definition; a finite sum).
* `sum_detActivityBg_eq`, `sum_detActivityBg_eq_rootTrace`: the activities of all polymers add up
  to the rooted trace at `s = 1`, which is the rooted trace at the uncut background
  `(bgFieldC, bgMultC)`.
* `detActivityBg_ne_zero_imp`: a non-zero activity lives on a polymer containing the root cube.
* `norm_detActivityBg_le`: with `z = (detDeg d L + 1)² · 2 / e^κ < 1` and
  `λ = κ - log 2 - 2 log (detDeg d L + 1)`:
  `‖detActivityBg y Y‖ ≤ ½ N covBLog / (1 - z) · exp(-(λ / (2 d L)) dExt Y)`.
* `sum_norm_detActivityBg_le`: the summed form, for `0 ≤ κ'' < λ / (2 d L)`.

## Locality in the datum

* `rootTraceBg_eq_of_agree_on_Yreg`: at fixed `s`, `rootTraceBg B D s` depends on `D` only through
  its restriction to the sets `resDep x`, `x ∈ Yreg s`.
* `mixDiff_rootTraceBg_eq_of_agree`: `Δ_J F_B` depends on `D` only through `resDep x` for the
  sites `x` of the parameter cubes of `J`.
* `detActivityBg_eq_of_agree`: `detActivityBg D y Y` depends on `D` only through `resDep x` for the
  sites `x ∈ Ω₁` of the polymer `Y` (the patches of `J` lie in the hull of `J`).

## The step

* `sum_detActivityBg_eq_halfLogDetCC`, `det_covSqrtC_eq_exp_sum_detActivityBg`: for the datum of a
  step on the chart, the activities of all blocks and polymers add up to `halfLogDetCC`, and
  `det C^{(k)1/2} = exp(∑_y ∑_Y detActivityBg y Y)`.
* `card_blockU_le`, `exists_detExpansionC_of_chart`: the landed structure `DetExpansionC` of the
  step has an element whose terms are the sums over the unit blocks `y ∈ B(z)` of the activities,
  with decay rate `λ / (2 d L)` and constant `L^d · ½ N covBLog / (1 - z)`.

## What is not proved here

That the constant is absorbed by the energy constant `E₀` of the class (the prefactor
`½ N covBLog d L a_k (a₁/L²) κ / (1 - z)` is not small); that the dependency set `⋃_{x ∈ Y ∩ Ω₁} resDep x` lies in the thickening of `Y` allowed by the energy class;
analyticity of the activity on an open set of data (only the pointwise analyticity of
`analyticOnNhd_rootTraceBg_raw` at chart points is available); the symmetry (paving covariance) of
the activities; and the use of these terms in the step identity.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.SmallField.Def6 Finset Matrix

/-! ### The activity -/

section Def

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

open Classical in
/-- **The activity of the polymer `Y` for the root block `y`, with cut-dependent background**: the
sum of the mixed differences `Δ_J` of `s ↦ rootTraceBg {y} D s` (the rooted trace of `{y}` at the
decoupled background of the datum `D` at `s`) over the sets `J` of parameter cubes whose hull
(assigned to the root index of `y` and the patches of `J`) is `Y`. -/
noncomputable def detActivityBg (m₀ : ℕ) (a : ℕ → ℝ) (aT ν ρ : ℝ) (D : BgData G N)
    (y : unitPts G)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) : ℂ :=
  ∑ J ∈ (Finset.univ : Finset (cubeIdx G)).powerset.filter
      (fun J => hullOf m₀ (rootIdxOf y) (patches J) = Y),
    mixDiff J (rootTraceBg G a aT ν ρ (unitQ G) (unitP G) {y} D)

variable {m₀ : ℕ}

/-- The activity is the activity (`cutActivity`) of the function `s ↦ rootTraceBg {y} D s`. -/
theorem detActivityBg_eq_cutActivity (a : ℕ → ℝ) (aT ν ρ : ℝ) (D : BgData G N) (y : unitPts G)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    detActivityBg m₀ a aT ν ρ D y Y =
      cutActivity m₀ (rootTraceBg G a aT ν ρ (unitQ G) (unitP G) {y} D) y Y := rfl

open Classical in
/-- **Resummation.**  The rooted trace of `{y}` with its background at `s = 1` is the sum over all
polymers of the activities. -/
theorem sum_detActivityBg_eq (a : ℕ → ℝ) (aT ν ρ : ℝ) (D : BgData G N) (y : unitPts G) :
    rootTraceBg G a aT ν ρ (unitQ G) (unitP G) {y} D (fun _ => 1) =
      ∑ Y, detActivityBg m₀ a aT ν ρ D y Y :=
  sum_cutActivity_eq (m₀ := m₀) (rootTraceBg G a aT ν ρ (unitQ G) (unitP G) {y} D) y

end Def

/-! ### Count, sums and decay on the chart -/

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ} {m₀ : ℕ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
  (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2) (hconn : HatConn Gp)
  {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)

include hC hD in
open Classical in
/-- **Resummation to the uncut background.**  The rooted trace of `{y}` at `s = 1` and at the
uncut background `(bgFieldC, bgMultC)` of the datum is the sum over all polymers of the
activities. -/
theorem sum_detActivityBg_eq_rootTrace (y : unitPts Gp) :
    rootTrace Gp (compWeight L a₁) a₁ ν (unitQ Gp) (unitP Gp) {y} (fun _ => 1)
        (svec Gp (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
        (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) =
      ∑ Y, detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y := by
  rw [← rootTraceBg_one_eq_of_flCore hC hD]
  exact sum_detActivityBg_eq (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y

include hC hk hδc hcap hsm hmar hα hconn hD

/-- **The two properties used by the assembly**, for the rooted trace of a set `B` of blocks with
its cut-dependent background: root-chain support, and the bound
`‖Δ_J‖ ≤ ½ N |B| covBLog · (2 / e^κ)^{|J|}`. -/
theorem rootTraceBg_cutSupport_and_bound (B : Finset (unitPts Gp)) :
    (∀ J : Finset (cubeIdx Gp),
      mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp)
        B D) ≠ 0 → ∃ y ∈ B, ∀ p ∈ J, ∃ q, RootChain Gp J y q ∧ p ∈ QsetP Gp q) ∧
    ∀ J : Finset (cubeIdx Gp),
      ‖mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp)
        B D)‖ ≤ (1 / 2 : ℝ) * N * B.card *
          covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ * (2 / Real.exp κ) ^ J.card :=
  ⟨fun _ hne => exists_rootChain_of_mixDiff_rootTraceBg_ne_zero hC hk hδc hcap hsm hmar hα hconn
      hD B hne,
    (rootTraceBg_cut_expansion hC hk hδc hcap hsm hmar hα
      (isUnitLatticeB_unit (G := Gp)).toIsUnitLattice B hD).2⟩

/-- The same for one block `y`: every parameter cube of `J` is joined to `y`, and
`‖Δ_J‖ ≤ ½ N covBLog · (2 / e^κ)^{|J|}`. -/
theorem rootTraceBg_single_cutSupport_and_bound (y : unitPts Gp) :
    (∀ J : Finset (cubeIdx Gp),
      mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp)
        {y} D) ≠ 0 → ∀ p ∈ J, ∃ q, RootChain Gp J y q ∧ p ∈ QsetP Gp q) ∧
    ∀ J : Finset (cubeIdx Gp),
      ‖mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp)
        {y} D)‖ ≤ (1 / 2 : ℝ) * N *
          covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ * (2 / Real.exp κ) ^ J.card := by
  obtain ⟨h1, h2⟩ := rootTraceBg_cutSupport_and_bound hC hk hδc hcap hsm hmar hα hconn hD {y}
  constructor
  · intro J hne
    obtain ⟨y', hy', hJ⟩ := h1 J hne
    rw [Finset.mem_singleton] at hy'
    subst hy'
    exact hJ
  · intro J
    have := h2 J
    simpa only [Finset.card_singleton, Nat.cast_one, mul_one] using this

/-- **A cut set with non-zero mixed difference is rooted in the parameter graph** (cut-dependent
background). -/
theorem rooted_of_mixDiff_rootTraceBg_ne_zero (B : Finset (unitPts Gp))
    {J : Finset (cubeIdx Gp)}
    (hne : mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp)
      (unitP Gp) B D) ≠ 0) :
    Polymer.Rooted (paramGraph Gp)
      ((B.biUnion (rootParam Gp) : Finset (cubeIdx Gp)) : Set (cubeIdx Gp)) J :=
  rooted_of_cutSupport hC.Sp
    (rootTraceBg_cutSupport_and_bound hC hk hδc hcap hsm hmar hα hconn hD B).1 hne

open Classical in
/-- **The count of cut sets** (cut-dependent background).  At most `Δ^(2n)` cut sets `J` with
`|J| = n` have non-zero `Δ_J` of `rootTraceBg B D`, `Δ = max (detDeg d L + 1) |B|`. -/
theorem card_supportBg_le (B : Finset (unitPts Gp)) (n : ℕ) :
    (((Finset.univ : Finset (cubeIdx Gp)).powerset.filter fun J =>
        J.card = n ∧ mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ)
          (unitQ Gp) (unitP Gp) B D) ≠ 0)).card
      ≤ (max (detDeg d L + 1) B.card) ^ (2 * n) :=
  card_cutSupport_le hC.Sp
    (rootTraceBg_cutSupport_and_bound hC hk hδc hcap hsm hmar hα hconn hD B).1 n

open Classical in
/-- **Volume-independent bound for the whole expansion** (cut-dependent background).  With
`M = ½ N |B| covBLog` and `Δ = detDeg d L + 1`, if `Δ² · 2 / e^κ < 1` then
`∑_J ‖Δ_J‖ ≤ M (1 - Δ² · 2 / e^κ)^{-|B|}`. -/
theorem sum_norm_mixDiff_rootTraceBg_le (B : Finset (unitPts Gp))
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1) :
    ∑ J ∈ (Finset.univ : Finset (cubeIdx Gp)).powerset,
        ‖mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp)
          (unitP Gp) B D)‖ ≤
      (1 / 2 : ℝ) * N * B.card * covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ *
        (1 / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))) ^ B.card := by
  obtain ⟨h1, h2⟩ := rootTraceBg_cutSupport_and_bound hC hk hδc hcap hsm hmar hα hconn hD B
  exact sum_norm_mixDiff_le_of_cutSupport hC.Sp h1 (by positivity) h2 hz

open Classical in
/-- **The value at `s = 1`** (the sum of all mixed differences) obeys the same bound. -/
theorem norm_rootTraceBg_one_le (B : Finset (unitPts Gp))
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1) :
    ‖rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp) B D
        (fun _ => 1)‖ ≤
      (1 / 2 : ℝ) * N * B.card * covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ *
        (1 / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))) ^ B.card := by
  rw [sum_mixDiff (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp)
    (unitP Gp) B D)]
  exact (norm_sum_le _ _).trans
    (sum_norm_mixDiff_rootTraceBg_le hC hk hδc hcap hsm hmar hα hconn hD B hz)

open Classical in
/-- **The tail of the expansion** (cut-dependent background).  With
`Δ = max (detDeg d L + 1) |B|` and `z = Δ² · 2 / e^κ < 1`:
`∑_{|J| ≥ n} ‖Δ_J‖ ≤ M z^n / (1 - z)`. -/
theorem tail_norm_mixDiff_rootTraceBg_le (B : Finset (unitPts Gp)) (n : ℕ)
    (hz : ((max (detDeg d L + 1) B.card : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1) :
    ∑ J ∈ (Finset.univ : Finset (cubeIdx Gp)).powerset.filter (fun J => n ≤ J.card),
        ‖mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp)
          (unitP Gp) B D)‖ ≤
      (1 / 2 : ℝ) * N * B.card * covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ *
        ((((max (detDeg d L + 1) B.card : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) ^ n /
          (1 - ((max (detDeg d L + 1) B.card : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ))) := by
  obtain ⟨h1, h2⟩ := rootTraceBg_cutSupport_and_bound hC hk hδc hcap hsm hmar hα hconn hD B
  exact tail_norm_mixDiff_le_of_cutSupport hC.Sp h1 (by positivity) h2 n hz

open Classical in
/-- **Support.**  A non-zero activity is supported on a polymer containing the root cube. -/
theorem detActivityBg_ne_zero_imp (hN : L ^ m₀ ∣ N₁) {y : unitPts Gp}
    {Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (h : detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y ≠ 0) :
    rootCube (m₀ := m₀) (rootIdxOf y) ∈ Y ∧ IsPolyDom m₀ (k + 1) (sitesOf Y) :=
  cutActivity_ne_zero_imp hC.Sp hconn hN
    (rootTraceBg_single_cutSupport_and_bound hC hk hδc hcap hsm hmar hα hconn hD y).1 h

open Classical in
/-- **Exponential decay of the activity in the size of the polymer** (cut-dependent background).
With `Δ = detDeg d L + 1`, `z = Δ² · 2 / e^κ < 1` (that is, `e^κ > 2 Δ²`) and the rate
`λ = κ - log 2 - 2 log Δ = -log z`:
`‖detActivityBg y Y‖ ≤ M / (1 - z) · exp(-(λ / (2 d L)) dExt Y)`, `M = ½ N covBLog`. -/
theorem norm_detActivityBg_le (hN : L ^ m₀ ∣ N₁) (y : unitPts Gp)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)) :
    ‖detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y‖ ≤
      (1 / 2 : ℝ) * N * covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
      Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
        (2 * d * L)) * dExt Y) := by
  obtain ⟨hsupp, hbd⟩ :=
    rootTraceBg_single_cutSupport_and_bound hC hk hδc hcap hsm hmar hα hconn hD y
  have hΔ0 : (0 : ℝ) < ((detDeg d L + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos _
  have h := norm_cutActivity_le (m₀ := m₀) hC.Sp hconn hN hsupp (by positivity) hbd hz Y
  rw [log_cutRate hΔ0 κ] at h
  have e : -(κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L) =
      -((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) := by ring
  rw [e] at h
  exact h

open Classical in
/-- **Summed form** (cut-dependent background).  For `0 ≤ κ''` with
`κ'' · 2 d L < λ = κ - log 2 - 2 log Δ`, the sum over all polymers of
`‖detActivityBg y Y‖ · exp(κ'' dExt Y)` is at most `M / (1 - Δ² · (2 / e^κ) · e^{2 d L κ''})`,
`M = ½ N covBLog`. -/
theorem sum_norm_detActivityBg_le (hN : L ^ m₀ ∣ N₁) (y : unitPts Gp) {κ'' : ℝ} (hκ0 : 0 ≤ κ'')
    (hκ'' : κ'' * (2 * d * L) < κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) :
    ∑ Y, ‖detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y‖ *
        Real.exp (κ'' * dExt Y) ≤
      (1 / 2 : ℝ) * N * covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ * Real.exp (κ'' * (2 * d * L)))) := by
  obtain ⟨hsupp, hbd⟩ :=
    rootTraceBg_single_cutSupport_and_bound hC hk hδc hcap hsm hmar hα hconn hD y
  have hΔ0 : (0 : ℝ) < ((detDeg d L + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos _
  exact sum_norm_cutActivity_le (m₀ := m₀) hC.Sp hconn hN hsupp (by positivity) hbd hκ0
    (cutRate_mul_exp_lt_one hΔ0 hκ'')

end Chart

/-! ### Locality in the datum -/

section DatumLocal

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ} {m₀ : ℕ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
  (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2) (hconn : HatConn Gp)
  {D D₂ : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
  (hD₂ : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D₂)

include hC hk hδc hcap hsm hmar hα hconn hD hD₂

/-- **Locality in the datum at fixed cut parameters.**  For `s` in the polydisc and two data of the
chart whose raw data agree on the sets `resDep x`, `x ∈ Yreg s`, the rooted traces (each at its own
decoupled background) of every set `B` of blocks are equal. -/
theorem rootTraceBg_eq_of_agree_on_Yreg {s : DecParams Gp} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    (hdata : ∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ Yreg Gp (extS Gp s) →
      ∀ y ∈ resDep Gp (x : CTorus d L N₁ m₁ (k + 1)),
        D.Ψ y = D₂.Ψ y ∧ (y ∈ Gp.Ω 1 → D.h y = D₂.h y))
    (B : Finset (unitPts Gp)) :
    rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp) B D s =
      rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp) B D₂ s := by
  classical
  rw [rootTraceBg_eq_sum_single _ _ _ _ B D s, rootTraceBg_eq_sum_single _ _ _ _ B D₂ s]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hYr : IsNnComp (Yreg Gp (extS Gp s)) (Yreg Gp (extS Gp s)) :=
    ⟨subset_rfl, fun _ _ y' hy' _ => hy'⟩
  by_cases hl : unitLabel Gp (Yreg Gp (extS Gp s)) y
  · exact rootTraceBg_eq_of_comp hC hk hδc hcap hsm hmar hα hconn hs hs hD hD₂ hYr hYr
      (fun _ _ _ => rfl) hdata {y} (fun y' hy' => by rw [Finset.mem_singleton.1 hy']; exact hl)
  · have hnl : ∀ y' ∈ ({y} : Finset (unitPts Gp)),
        ¬ unitLabel Gp (Yreg Gp (extS Gp s)) y' := fun y' hy' => by
      rw [Finset.mem_singleton.1 hy']; exact hl
    rw [rootTraceBg_eq_baseline_of_not_label hC hk hδc hcap hsm hmar hα hconn hs hD {y} hnl,
      rootTraceBg_eq_baseline_of_not_label hC hk hδc hcap hsm hmar hα hconn hs hD₂ {y} hnl]

/-- **Locality of a mixed difference in the datum.**  If the raw data of two data of the chart
agree on `resDep x` for every site `x ∈ Ω₁` of the parameter cubes of `J`, then `Δ_J` of the
rooted trace with its background is the same for the two data. -/
theorem mixDiff_rootTraceBg_eq_of_agree (J : Finset (cubeIdx Gp))
    (hdata : ∀ P ∈ J, ∀ x : Gp.Ω 1,
      (x : CTorus d L N₁ m₁ (k + 1)) ∈ cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) →
      ∀ y ∈ resDep Gp (x : CTorus d L N₁ m₁ (k + 1)),
        D.Ψ y = D₂.Ψ y ∧ (y ∈ Gp.Ω 1 → D.h y = D₂.h y))
    (B : Finset (unitPts Gp)) :
    mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp)
        B D) =
      mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp) (unitP Gp)
        B D₂) := by
  unfold mixDiff
  refine Finset.sum_congr rfl fun I hI => ?_
  have hIJ := Finset.mem_powerset.1 hI
  refine congrArg (fun w : ℂ => (-1 : ℂ) ^ (J.card - I.card) * w) ?_
  refine rootTraceBg_eq_of_agree_on_Yreg hC hk hδc hcap hsm hmar hα hconn hD hD₂
    (norm_cutPt_lt_exp hC.hκ I) (fun x hx => ?_) B
  obtain ⟨hxΩ, z, -, hzI, hxz⟩ := mem_Yreg_cutPt_iff.1 hx
  obtain ⟨P, hP, hxP⟩ := exists_cube_of_mem_Omega hC.Sp.aligned hxΩ
  have hPz : (⟨P, hP⟩ : cubeIdx Gp) ∈ QsetP Gp z :=
    mem_QsetP.2 (mem_Qset_of_mem_hat_cube hP hxz hxP)
  exact hdata ⟨P, hP⟩ (hIJ (hzI hPz)) x hxP

open Classical in
/-- **Locality of the activity in the datum.**  If the raw data of two data `D`, `D₂` of the chart
agree on the dependency sets `resDep x` of the sites `x ∈ Ω₁` of the polymer `Y`, then the
activities of `Y` are equal.  (The patches of a cut set lie in its hull, and the rooted trace at
the cut point `1_I`, `I ⊆ J`, reads the datum only through `resDep` of the patches of `I`.) -/
theorem detActivityBg_eq_of_agree (hN : L ^ m₀ ∣ N₁) (y : unitPts Gp)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hdata : ∀ x : Gp.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ sitesOf Y →
      ∀ z ∈ resDep Gp (x : CTorus d L N₁ m₁ (k + 1)),
        D.Ψ z = D₂.Ψ z ∧ (z ∈ Gp.Ω 1 → D.h z = D₂.h z)) :
    detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y =
      detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D₂ y Y := by
  unfold detActivityBg
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hY := (Finset.mem_filter.1 hJ).2
  refine mixDiff_rootTraceBg_eq_of_agree hC hk hδc hcap hsm hmar hα hconn hD hD₂ J
    (fun P hP x hxP => hdata x ?_) {y}
  rw [← hY]
  exact subset_sitesOf_piHull hN (hullSet m₀ (rootIdxOf y) (patches J))
    (Or.inr (Set.mem_iUnion₂.2 ⟨P.1, mem_patches.2 ⟨P.2, hP⟩, mem_Pset_iff.2 hxP⟩))

end DatumLocal

/-! ### The determinant of the step -/

section Step

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ} {m₀ : ℕ}
variable (S : StepSetting d L N₁ m₁ k N ϱ)
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}

open Classical in
/-- **The activities add up to `½ log det C^{(k)}`.**  For the block datum `S.D'` of a step on the
chart, the sum over all unit blocks `y` and all polymers `Y` of the activities is `halfLogDetCC`,
the analytic `-½ ∑_y tr 𝕃(y, y)`. -/
theorem sum_detActivityBg_eq_halfLogDetCC
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    ∑ y : S.U, ∑ Y, detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) S.D' y Y =
      S.halfLogDetCC := by
  have h1 : ∀ y : S.U, ∑ Y, detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) S.D' y Y =
      rootTraceBg S.G' S.a S.a₁ S.ν (rho4 d L N BG κ) (unitQ S.G') (unitP S.G') {y} S.D'
        (fun _ => 1) :=
    fun y => (sum_detActivityBg_eq S.a S.a₁ S.ν (rho4 d L N BG κ) S.D' y).symm
  rw [Finset.sum_congr rfl fun y _ => h1 y,
    ← rootTraceBg_eq_sum_single S.a S.a₁ S.ν (rho4 d L N BG κ) Finset.univ S.D' (fun _ => 1),
    rootTraceBg_one_eq_of_flCore hC hD]
  unfold rootTrace StepSetting.halfLogDetCC StepSetting.logAC
  rw [Balaban.Localization.extS_one]

open Classical in
/-- **The Jacobian of the step is the exponential of the sum of the activities.**  On the chart
(`FlCore`, the cap and the margins of the covariance chart),
`det C^{(k)1/2} = exp(∑_y ∑_Y detActivityBg y Y)`. -/
theorem det_covSqrtC_eq_exp_sum_detActivityBg
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') :
    S.covSqrtC.det = Complex.exp
      (∑ y : S.U, ∑ Y, detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) S.D' y Y) := by
  rw [S.det_covSqrtC_of_chart hC hMX hdm hα hsm hD, sum_detActivityBg_eq_halfLogDetCC S hC hD]

/-- The block `B_{k+1}(z)` of the unit lattice has at most `L^d` points. -/
theorem card_blockU_le (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    (S.blockU z).card ≤ L ^ d := by
  classical
  have hcard := card_blockFibre (d := d)
    (unitBlock1_side (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)) z
  have h1 : (L ^ 1) ^ d = L ^ d := by rw [pow_one]
  rw [← h1, ← hcard]
  refine Finset.card_le_card_of_injOn Subtype.val (fun b hb => ?_)
    (fun _ _ _ _ h => Subtype.ext h)
  rw [Finset.mem_coe, mem_blockFibre]
  exact (Finset.mem_filter.1 hb).2

open Classical in
/-- **The determinant expansion of the step from the activities.**  For the block datum of a step
on the chart, with `HatConn`, `L^{m₀} ∣ N₁` and the rate condition `e^κ > 2 (detDeg d L + 1)²`,
the structure `DetExpansionC` of the block `B(z)` has an element whose term at the polymer `T` is
the sum over the unit blocks `y ∈ B(z)` of the activities `detActivityBg y T`; its decay rate is
`(κ - log 2 - 2 log (detDeg d L + 1)) / (2 d L)` and its constant is
`L^d · ½ N covBLog d L a_k (a₁/L²) κ / (1 - (detDeg d L + 1)² · 2 / e^κ)`, which involves neither
the torus nor `z`. -/
theorem exists_detExpansionC_of_chart
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hδc : 0 ≤ δc)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (hconn : HatConn S.G')
    (hD : XiCData S.G' S.a S.ν (k + 1) 1 eps S.D') (hN : L ^ m₀ ∣ N₁)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    ∃ E : DetExpansionC S m₀ z
        ((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L))
        ((L : ℝ) ^ d * ((1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
          (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)))),
      ∀ T, E.term T =
        ∑ y ∈ S.blockU z, detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) S.D' y T := by
  have hc : 0 ≤ covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ := by
    unfold covBLog
    have := covB4_nonneg d L (S.a k) κ
    have := (xSetting_of_flCore hC S.hk1).hak_pos
    positivity
  have hC0 : 0 ≤ (1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
      (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) :=
    div_nonneg (by positivity) (by linarith)
  refine ⟨⟨fun T => ∑ y ∈ S.blockU z,
    detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) S.D' y T, ?_, fun T => ?_⟩, fun _ => rfl⟩
  · rw [← rootTrace_one_eq_logAC S z, ← rootTraceBg_one_eq_of_flCore hC hD,
      rootTraceBg_eq_sum_single S.a S.a₁ S.ν (rho4 d L N BG κ) (S.blockU z) S.D' (fun _ => 1),
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ =>
      sum_detActivityBg_eq S.a S.a₁ S.ν (rho4 d L N BG κ) S.D' y
  · refine (norm_sum_le _ _).trans ?_
    have hb : ∀ y ∈ S.blockU z,
        ‖detActivityBg m₀ S.a S.a₁ S.ν (rho4 d L N BG κ) S.D' y T‖ ≤
          (1 / 2 : ℝ) * N * covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
            (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
          Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
            (2 * d * L)) * dExt T) := fun y _ =>
      norm_detActivityBg_le hC S.hk1 hδc hMX hsm hdm hα hconn hD hN y hz T
    refine (Finset.sum_le_sum hb).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((S.blockU z).card : ℝ) ≤ (L : ℝ) ^ d := by
      exact_mod_cast card_blockU_le S z
    have he : 0 ≤ Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
        (2 * d * L)) * dExt T) := (Real.exp_pos _).le
    calc ((S.blockU z).card : ℝ) * ((1 / 2 : ℝ) * N *
            covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
              (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
            Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
              (2 * d * L)) * dExt T))
        ≤ (L : ℝ) ^ d * ((1 / 2 : ℝ) * N *
            covBLog d L (S.a k) (S.a₁ / (L : ℝ) ^ 2) κ /
              (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
            Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
              (2 * d * L)) * dExt T)) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hC0 he)
      _ = _ := by ring

end Step

end Balaban.Fluctuation
