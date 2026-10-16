/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionHatV
public import Balaban.Fluctuation.SharpChartTestSup
public import Balaban.Localization.P6PairBaseHat
public import Balaban.Localization.P6PairBase
import Mathlib.Tactic.Linarith

/-!
# The local fluctuation generator `𝔹_k(Y)` (WIDEGEN T2, two-generator form)

In P3 (4.16)-(4.18), (4.32) the fluctuation field `δψ(𝔹_k(X), 𝔹_k; ψ', s)` lives on the generating
set `𝔹_k = {Ω₁, …, Ω_k}`, that is `𝔹_{k+1}` with its top layer `Ω_{k+1}` dropped.  When P3 pp. 78-79
replaces `𝔹_{k+1}` by the local generator `𝔹_{k+1}(Y)` in the terms of (4.45), the background field
`φ(𝔹_{k+1}(Y); θ, s)` is defined on `Ω₁(𝔹_{k+1}(Y))` only, so the fluctuation generator must precede
`𝔹_{k+1}(Y)`; the generator agreeing with `𝔹_k` on `Y` is `𝔹_k(Y) = 𝔹_{k+1}(Y)` with its top layer
dropped.  For the literal local generator `𝔹_{j+1}(Y) = localB (j + 1) … Y` this is again a local
generator of the landed form, `localB j … Ω_j(𝔹_{j+1}(Y))` (only the set changes; no new
definition):

* `GsSpec.localB_drop_Ω`: `Ω_n(localB j (Ω_j(localB (j+1) Y))) = Ω_n(localB (j+1) Y)` for `n ≤ j`;
* `GsSpec.localB_drop_precedes`, `GsSpec.localB_drop_top`: it precedes `𝔹_{j+1}(Y)` and has no
  layer above `j`;
* `GsSpec.precedes_localB_drop`: a generating set `𝔹_k(X) ≺ 𝔹_{k+1}(Y)` without layer `k + 1`
  precedes `𝔹_k(Y)` (the order `𝔹_k(X) ≺ H⁻` of `FlSetting`);
* `isLayerConstant_liftC_of_top_empty`, `liftC_mem_flBallLC_of_top_empty`: the lift of a unit-lattice
  field is layer constant for every generating set without layer `k + 1` (no `IsLevel` of `H⁻`);
* `hatLift_mem_flBallLC_of_top_empty`: the fluctuation `ψ' = liftC (cc • C^{1/2}(1) ψ̂)` of the
  ambient level pair lies in the ball of block fluctuations of every such generating set, in
  particular of `𝔹_k(Y)` (P3 (4.46) takes `ψ'` itself as the variable of the local term);
* `localB_footLocal_of_precedes`, `localB_rowInHat_of_precedes`: `FootLocal` and `RowInHat` of the
  pair `(coverOf 𝔹_{k+1}(Y), H⁻)` for every `H⁻ ≺ 𝔹_{k+1}(Y)` (the P6 pair geometry);
* `localB_drop_pair`: the instance `H⁻ = 𝔹_k(Y)`: the order, `FootLocal`, `RowInHat`.
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField Finset

section Drop

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}

/-- **The layers of `𝔹_j(Ω_j(𝔹_{j+1}(Y)))` are those of `𝔹_{j+1}(Y)` up to `j`** (P3 (4.5)-(4.6):
both are the `5 L`-thickenings of the same top set `Ω_j(𝔹_{j+1}(Y))`, a union of `𝒞_j`-cubes). -/
theorem localB_drop_Ω {j : ℕ} (hA : j + 1 ≤ K) (hB : j ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) (hsep' : ϱ' ≤ minSep L (L ^ m₁)) {n : ℕ} (hn : n ≤ j) :
    (localB j hB (↑((localB (j + 1) hA Y hsep).Ω j) : Set (CTorus d L N₁ m₁ K)) hsep').Ω n =
      (localB (j + 1) hA Y hsep).Ω n := by
  have htop : (localB j hB (↑((localB (j + 1) hA Y hsep).Ω j) : Set (CTorus d L N₁ m₁ K))
      hsep').Ω j = (localB (j + 1) hA Y hsep).Ω j := by
    ext x
    rw [mem_localB_Ω_top]
    constructor
    · intro h
      exact Finset.mem_coe.1 (h x rfl)
    · intro hx y hy
      rw [Finset.mem_coe, mem_localB_Ω_succ (Nat.lt_succ_self j)]
      rw [mem_localB_Ω_succ (Nat.lt_succ_self j)] at hx
      obtain ⟨z, hz, hd⟩ := hx
      exact ⟨z, hz, by rw [hy]; exact hd⟩
  suffices h : ∀ t n, n + t = j →
      (localB j hB (↑((localB (j + 1) hA Y hsep).Ω j) : Set (CTorus d L N₁ m₁ K)) hsep').Ω n =
        (localB (j + 1) hA Y hsep).Ω n from h (j - n) n (by omega)
  intro t
  induction t with
  | zero =>
    intro n hn
    obtain rfl : n = j := by omega
    exact htop
  | succ t ih =>
    intro n hn
    ext x
    rw [mem_localB_Ω_succ (by omega : n < j), mem_localB_Ω_succ (by omega : n < j + 1),
      ih (n + 1) (by omega)]

/-- `𝔹_j(Ω_j(𝔹_{j+1}(Y)))` has no layer above `j`. -/
theorem localB_drop_top {j : ℕ} (hA : j + 1 ≤ K) (hB : j ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) (hsep' : ϱ' ≤ minSep L (L ^ m₁)) :
    (localB j hB (↑((localB (j + 1) hA Y hsep).Ω j) : Set (CTorus d L N₁ m₁ K)) hsep').Ω
      (j + 1) = ∅ :=
  localB_Ω_of_gt (Nat.lt_succ_self j)

/-- **`𝔹_j(Y) ≺ 𝔹_{j+1}(Y)`**: the generator with the top layer dropped precedes the local
generator. -/
theorem localB_drop_precedes {j : ℕ} (hA : j + 1 ≤ K) (hB : j ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) (hsep' : ϱ' ≤ minSep L (L ^ m₁)) :
    Precedes (localB j hB (↑((localB (j + 1) hA Y hsep).Ω j) : Set (CTorus d L N₁ m₁ K)) hsep')
      (localB (j + 1) hA Y hsep) := by
  intro i _ _
  by_cases hij : i ≤ j
  · rw [localB_drop_Ω hA hB Y hsep hsep' hij]
  · rw [localB_Ω_of_gt (by omega : j < i)]
    exact Finset.empty_subset _

/-- **`𝔹_j(X) ≺ 𝔹_j(Y)`**: a generating set preceding `𝔹_{j+1}(Y)` and without layer `j + 1`
precedes the generator `𝔹_j(Y)` with the top layer dropped. -/
theorem precedes_localB_drop {j : ℕ} (hA : j + 1 ≤ K) (hB : j ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) (hsep' : ϱ' ≤ minSep L (L ^ m₁)) {ϱk : ℝ}
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱk} (hP : Precedes Gk (localB (j + 1) hA Y hsep))
    (htop : Gk.Ω (j + 1) = ∅) :
    Precedes Gk
      (localB j hB (↑((localB (j + 1) hA Y hsep).Ω j) : Set (CTorus d L N₁ m₁ K)) hsep') := by
  intro i hi1 hiK x hx
  by_cases hij : i ≤ j
  · rw [localB_drop_Ω hA hB Y hsep hsep' hij]
    exact hP i hi1 hiK hx
  · have hx' : x ∈ Gk.Ω (j + 1) := Gk.Ω_antitone (by omega) (by omega) (by omega) hx
    rw [htop] at hx'
    exact absurd hx' (Finset.notMem_empty _)

end Drop

end Balaban.SmallField.GsSpec

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Finset

section Lift

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱ' : ℝ}
  {G' : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}

/-- **The lift is layer constant for every generating set without layer `k + 1`**: the blocks of
the layers `n ≤ k` lie in the unit blocks (`isLayerConstant_liftC` without `IsLevel Hm k`). -/
theorem isLayerConstant_liftC_of_top_empty {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hHm : Hm.Ω (k + 1) = ∅) (hG' : IsLevel G' (k + 1)) (v : unitPts G' × Fin N → ℂ) :
    IsLayerConstant Hm (liftC hG' v) := by
  intro n hn1 hnk x hx x' hx'
  have hn : n ≤ k := by
    by_contra h
    obtain rfl : n = k + 1 := by omega
    rw [GeneratingSet.mem_layer, hHm] at hx
    exact Finset.notMem_empty _ hx.1
  have hb : jBlock d L (N₁ * L ^ m₁) (k + 1) k x' = jBlock d L (N₁ * L ^ m₁) (k + 1) k x :=
    jBlock_eq_of_le hn (by omega) (GeneratingSet.mem_blk.1 hx')
  have hu : unitPt hG' x' = unitPt hG' x := Subtype.ext hb
  funext i
  simp only [liftC_apply, hu]

/-- **Sup bound in, ball membership out**, for every generating set without layer `k + 1`
(`liftC_mem_flBallLC` without `IsLevel Hm k`). -/
theorem liftC_mem_flBallLC_of_top_empty {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
    (hHm : Hm.Ω (k + 1) = ∅) (hG' : IsLevel G' (k + 1)) {δ₁ : ℝ}
    {v : unitPts G' × Fin N → ℂ} (hv : ∀ b : unitPts G', vn (fun i => v (b, i)) < δ₁) :
    liftC hG' v ∈ FlBallLC Hm δ₁ :=
  ⟨fun x _ => hv (unitPt hG' x), isLayerConstant_liftC_of_top_empty hHm hG' v⟩

end Lift

end Balaban.Fluctuation

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.LargeField Finset

section HatLocal

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm ϱl : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **The fluctuation of a bounded hat variable is a block fluctuation of the local generator**:
for the ambient pair of consecutive levels (`FlCore`, `IsLevel H⁻ k`, `IsLevel 𝔹_{k+1} (k + 1)`) the
fluctuation `ψ' = liftC (cc • C^{1/2}(1) ψ̂)` of a hat variable with `|ψ̂| ≤ c_ψ` lies in the ball
`FlBallLC H δ₁` of every generating set `H` without layer `k + 1`, in particular of the local
fluctuation generator `𝔹_k(Y)` (`GsSpec.localB_drop_top`). -/
theorem hatLift_mem_flBallLC_of_top_empty (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    {Hl : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱl} (hHl : Hl.Ω (k + 1) = ∅) :
    hatLift Gp a₁ ν hG' cc D ψh ∈ FlBallLC Hl δ₁ := by
  have h := hatLift_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hδ₁ hD hψh
  exact ⟨fun x _ => h.1 x ((mem_dataSites Hm).2 (Or.inl (hG x).1)),
    isLayerConstant_liftC_of_top_empty hHl hG' _⟩

end HatLocal

section Pair

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}

/-- **`FootLocal` of the pair `(coverOf 𝔹_{t}(Y), H⁻)`** for every generating set `H⁻ ≺ 𝔹_t(Y)` of
the literal local generator (`p6_coverGeom_of_pair`, the mixed-wall cut-operator estimate
`Dec2.coverBase_mixed`), with the constants `mixedKc d L`, `Cchi d L`.  The cover geometry needs
`N₁ > 5`, `M₁ = L^{m₁} ≥ 4 L²`, `m₁ ≥ 2` and the Agmon condition for the separation of `H⁻`. -/
theorem localB_footLocal_of_precedes {t : ℕ} (ht : t ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
    (hP : Precedes Hm (GsSpec.localB t ht Y hsep)) (hN : 5 < N₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1) (ha : IsAdmissibleWeights K a)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱm - 1)) :
    Dec2.FootLocal (coverOf (GsSpec.localB t ht Y hsep)) Hm a ν (Dec2.mixedKc d L) (Cchi d L) :=
  { toCoverBase := Dec2.coverBase_mixed hN (GsSpec.localB t ht Y hsep)
      (p6_coverGeom_of_pair (localB_cubeAligned ht Y hsep hm₁) (localB_supSep ht Y hsep) hP hM
        hd hL hν hνL ha hag) hνL (fun _ hq => hq)
    chi_core := (Dec2.footLocalGeom_coverOf _).chi_core }

/-- **`RowInHat` of the pair `(coverOf 𝔹_t(Y), H⁻)`** for every `H⁻ ≺ 𝔹_t(Y)`
(`p6_rowInHat_of_pair`): the rows of `H⁻_D(α)` at the sites of a cover cube `□_z` stay in `□̂_z`. -/
theorem localB_rowInHat_of_precedes {t : ℕ} (ht : t ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (hsep : ϱ ≤ minSep L (L ^ m₁)) {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
    (hP : Precedes Hm (GsSpec.localB t ht Y hsep)) (hL : 3 ≤ L) (a : ℕ → ℝ) (ν : ℝ) :
    RowInHat (coverOf (GsSpec.localB t ht Y hsep)) Hm a ν :=
  p6_rowInHat_of_pair (localB_supSep ht Y hsep) hP hL

/-- **The local fluctuation pair** `(𝔹_{k+1}(Y), 𝔹_k(Y))`, `𝔹_{k+1}(Y) = localB (k + 1) … Y` and
`𝔹_k(Y) = localB k … Ω_k(𝔹_{k+1}(Y))` (the top layer dropped): `𝔹_k(Y) ≺ 𝔹_{k+1}(Y)`, no layer
`k + 1` in `𝔹_k(Y)`, and `FootLocal`, `RowInHat` of `(coverOf 𝔹_{k+1}(Y), 𝔹_k(Y))`.  These are the
fields `hPmp`, `SM` of `FlSetting` and the stencil hypothesis of the hat engine at the local pair;
by `hatLift_mem_flBallLC_of_top_empty` the ambient hat fluctuations are block fluctuations of
`𝔹_k(Y)`. -/
theorem localB_drop_pair {k : ℕ} (hk : k + 1 ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁) {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d)
    (hL : 3 ≤ L) (hν : 0 ≤ ν) (hνL : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1) (ha : IsAdmissibleWeights K a)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) :
    Precedes (GsSpec.localB k (by omega)
        (↑((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
          Set (CTorus d L N₁ m₁ K)) (le_refl (minSep L (L ^ m₁))))
      (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) ∧
    (GsSpec.localB k (by omega)
        (↑((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
          Set (CTorus d L N₁ m₁ K)) (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) = ∅ ∧
    Dec2.FootLocal (coverOf (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
      (GsSpec.localB k (by omega)
        (↑((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
          Set (CTorus d L N₁ m₁ K)) (le_refl (minSep L (L ^ m₁))))
      a ν (Dec2.mixedKc d L) (Cchi d L) ∧
    RowInHat (coverOf (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
      (GsSpec.localB k (by omega)
        (↑((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
          Set (CTorus d L N₁ m₁ K)) (le_refl (minSep L (L ^ m₁)))) a ν := by
  have hP := GsSpec.localB_drop_precedes hk (by omega) Y (le_refl (minSep L (L ^ m₁)))
    (le_refl (minSep L (L ^ m₁)))
  exact ⟨hP, GsSpec.localB_drop_top hk (by omega) Y le_rfl le_rfl,
    localB_footLocal_of_precedes hk Y le_rfl hP hN hm₁ hM hd hL hν hνL ha hag,
    localB_rowInHat_of_precedes hk Y le_rfl hP hL a ν⟩

end Pair

end Balaban.Localization
