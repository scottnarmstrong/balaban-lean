/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCauchyBgActivity
public import Balaban.Localization.SharpX0Distance
public import Balaban.SmallField.LocalGeneratorSource
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The determinant on a generating set without `HatConn` (local generating sets)

The support, bound and locality theory of the activities `detActivityBg` of the determinant
(`DetCauchyBgSupport`, `DetCauchyAssembly`, `DetCauchyBgActivity`) was stated under `HatConn G`:
every thickened cube `□̂_q ∩ Ω₁` is nearest-neighbour connected.  This fails for the local
generating sets `𝔹_{k+1}(Y)` (two `𝒞₁`-cubes of `Ω₁` meeting only at an edge, `WIDEGEN.md`, W776).
The proofs use `HatConn` only through the dichotomy "the thickened cube of a centre with non-zero
cut factor lies in the component `Y'` or misses it" (`hatDich_of_isNnComp`), and only for the
centres that are active at the cut points `1_I`, `I ⊆ J`, of the cut set `J` at hand (the centres
with footprint in `J`, `ActIn`); the locality in the datum needs nothing (the component is all of
`Yreg`).  The cores `…_of_hatDich`, `…_of_conn`, `…_core` of those files state this.

**The weaker condition, and why every generating set of the localization setting meets it.**  For
a generating set with `DGSetting` (the separation `4 d L M₁ ≤ ϱ` and the cube alignment) the
thickened cube of a centre of scale `q.1 ≥ 2` lies in `Ω_{q.1 - 1} ⊆ Ω₁`
(`hatBox_subset_Ω_one_of_two_le`), so `□̂_q ∩ Ω₁ = □̂_q` is a box and is connected
(`connIn_hatI_of_two_le`).  Hence for a cut set `J` of parameter cubes of scale `≥ 2` every centre
with footprint in `J` has a connected thickened cube (`connIn_hatI_of_actIn_of_two_le`).  Only the
centres of scale `1` can have a disconnected thickened cube.

**Instance: the local generating sets.**  `dgSetting_castG_localB`: the generating set
`castG hc (localB (k + 1) … X hsep)` of the new level (read on the torus `(N₁', m₁')`,
`m₁ ≤ m₁'`) has `DGSetting` whenever the step's level set has it (only the cube alignment depends
on the generating set; it is inherited from `localB_cubeAligned` at the coarser cubes).

**Results (no `HatConn`).** For a datum of the chart of any generating set with `FlCore`:

* `exists_rootChain_of_mixDiff_rootTraceBg_ne_zero_of_two_le`: the support theorem for cut sets of
  parameter cubes of scale `≥ 2`;
* `detActivityBg_ne_zero_imp_of_avoid`, `norm_detActivityBg_le_of_avoid`: support and exponential
  decay of the activity of a polymer `Y` none of whose sites lies in the layer `1` (the cut sets
  with hull `Y` then avoid the scale-`1` cubes; the bound is the landed one).  The proof applies
  the general assembly to the function `F'(s) = F(s')`, `s'_P = s_P` for the cubes `P` of scale
  `≥ 2` and `0` otherwise, whose mixed differences are those of `F` on the cut sets of scale `≥ 2`
  and vanish on the others.

The locality in the datum, `detActivityBg_eq_of_agree_core`, and the analyticity,
`exists_analytic_detActivityBg_raw`, need no connectivity at all.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Analysis
  Balaban.SmallField Balaban.SmallField.Def6 Finset Matrix

/-! ### Connectivity of the thickened cubes of scale `≥ 2` -/

section Conn

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **The thickened cube of a centre of scale `≥ 2` lies in `Ω₁`** (`DGSetting`): it lies within
`4 d M₁ L^{q.1}` of the base of the centre, a site of `Ω_{q.1}`, hence in `Ω_{q.1 - 1}`. -/
theorem hatBox_subset_Ω_one_of_two_le (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) (h2 : 2 ≤ q.1) {y : CTorus d L N₁ m₁ K} (hy : y ∈ hatBox q) :
    y ∈ G.Ω 1 := by
  obtain ⟨⟨hm1, hmK⟩, hl, -⟩ := (mem_cubeIdx G).1 hq
  have hqΩ : q.2 ∈ G.Ω q.1 := (G.mem_layer.1 hl).1
  have hdist := torusDist_hatBox_le S hy
  rw [Green.torusDist_comm_gen] at hdist
  have hpred := mem_pred_cube m₁ G S.cover_sep h2 hmK hqΩ hdist
  exact G.Ω_antitone le_rfl (by omega) (by omega) hpred

/-- For a centre of scale `≥ 2` the thickened cube `□̂_q ∩ Ω₁` is the whole box `□̂_q`. -/
theorem hatI_eq_hatBox_of_two_le (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) (h2 : 2 ≤ q.1) : hatI G q = hatBox q := by
  classical
  unfold hatI
  exact Finset.filter_true_of_mem fun y hy => hatBox_subset_Ω_one_of_two_le S hq h2 hy

/-- **The thickened cube of a centre of scale `≥ 2` is nearest-neighbour connected** (`DGSetting`;
the condition `HatConn` holds at every centre of scale `≥ 2`). -/
theorem connIn_hatI_of_two_le (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K}
    (hq : q ∈ cubeIdx G) (h2 : 2 ≤ q.1) : ConnIn (hatI G q) := by
  rw [hatI_eq_hatBox_of_two_le S hq h2]
  unfold hatBox
  refine boxSet_connected q.2 ?_
  unfold hatRad
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := one_le_pow₀ hL
  have h3 : (0 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 := by positivity
  linarith

end Conn

section ConnJ

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **The weaker condition holds for cut sets of scale `≥ 2`.**  If every parameter cube of `J` has
scale `≥ 2`, every centre with footprint in `J` (`ActIn G J q`) has a connected thickened cube
(the centre lies in its own footprint). -/
theorem connIn_hatI_of_actIn_of_two_le (S : DGSetting G a ν) {J : Finset (cubeIdx G)}
    (hJ : ∀ P ∈ J, 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1)
    {q : ℕ × CTorus d L N₁ m₁ (k + 1)} (hq : ActIn G J q) : ConnIn (hatI G q) := by
  have hself : (⟨q, hq.1⟩ : cubeIdx G) ∈ QsetP G q :=
    mem_QsetP.2 (self_mem_Qset_zeroCuts hq.1)
  exact connIn_hatI_of_two_le S hq.1 (hJ _ (hq.2 hself))

end ConnJ

/-! ### The local generating sets satisfy `DGSetting` -/

section Cast

/-- The cube alignment passes to a finer cube size dividing the period. -/
theorem cubeAligned_of_le {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    {G : GeneratingSet d L N₀ K ϱ} {m m' : ℕ} (h : CubeAligned G m') (hm : 2 ≤ m) (hmm : m ≤ m')
    (hdvd : L ^ m ∣ N₀) : CubeAligned G m :=
  ⟨hm, hdvd, fun j hj1 hjk x x' hx => h.union j hj1 hjk x x' (hx.mono (pow_dvd_pow L (by omega)))⟩

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- `DGSetting` depends on the generating set only through the cube alignment. -/
theorem dgSetting_of_cubeAligned {G G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ}
    {ν : ℝ} (S : DGSetting G a ν) (hA : CubeAligned G' m₁) : DGSetting G' a ν :=
  { S with aligned := hA }

/-- **The local generating sets of the new level satisfy `DGSetting`.**  For the generating set
`castG hc (localB j hj X hsep)` read on the torus `(N₁', m₁')` with `N₁' L^{m₁'} = N₁ L^{m₁}` and
`m₁ ≤ m₁'`, the standing hypotheses of the localization setting hold as soon as they hold for one
generating set of the same index `ϱ` (e.g. the level set of the step). -/
theorem dgSetting_castG_localB {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
    (S : DGSetting G a ν) {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    (hm : m₁ ≤ m₁') {j : ℕ} (hj : j ≤ K) (X : Set (CTorus d L N₁' m₁' K))
    (hsep : ϱ ≤ LargeField.minSep L (L ^ m₁')) :
    DGSetting (GsSpec.castG hc (GsSpec.localB j hj X hsep)) a ν := by
  have h2 : 2 ≤ m₁ := S.aligned.two_le
  have hA' := cubeAligned_castG hc (localB_cubeAligned hj X hsep (by omega))
  exact dgSetting_of_cubeAligned S (cubeAligned_of_le hA' h2 hm (dvd_mul_left _ _))

end Cast

/-! ### The determinant without `HatConn` -/

section Det

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ} {m₀ : ℕ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- The restriction of the cut parameters to the cubes of scale `≥ 2` fixes the cut points of the
cut sets of scale `≥ 2`. -/
theorem cutPt_restrict_two_le {I : Finset (cubeIdx Gp)}
    (hI : ∀ P ∈ I, 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1) :
    (fun P : cubeIdx Gp => if 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1 then cutPt I P else 0) =
      cutPt I := by
  funext P
  by_cases h : 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1
  · simp [h]
  · have hPI : P ∉ I := fun hP => h (hI P hP)
    simp [h, cutPt, hPI]

/-- **The mixed differences of the restricted function.**  On a cut set of scale `≥ 2` they are
those of `F`. -/
theorem mixDiff_restrict_two_le (F : DecParams Gp → ℂ) {J : Finset (cubeIdx Gp)}
    (hJ : ∀ P ∈ J, 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1) :
    mixDiff J (fun s => F fun P => if 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1 then s P else 0) =
      mixDiff J F := by
  unfold mixDiff
  refine Finset.sum_congr rfl fun I hI => ?_
  have hIJ := Finset.mem_powerset.1 hI
  exact congrArg _ (congrArg F (cutPt_restrict_two_le fun P hP => hJ P (hIJ hP)))

/-- **The mixed differences of the restricted function vanish on the cut sets containing a cube of
scale `< 2`** (the restricted function does not depend on that parameter). -/
theorem mixDiff_restrict_two_le_eq_zero (F : DecParams Gp → ℂ) {J : Finset (cubeIdx Gp)}
    {p : cubeIdx Gp} (hp : p ∈ J) (hp2 : ¬ 2 ≤ (p : ℕ × CTorus d L N₁ m₁ (k + 1)).1) :
    mixDiff J (fun s => F fun P => if 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1 then s P else 0) =
      0 := by
  refine mixDiff_eq_zero_of_insert_eq hp _ fun I _ => ?_
  congr 1
  funext P
  by_cases h : 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1
  · have hPp : P ≠ p := fun e => hp2 (e ▸ h)
    simp [h, cutPt, Finset.mem_insert, hPp]
  · simp [h]

variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k) {δc : ℝ}
  (hδc : 0 ≤ δc) (hcap : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hmar : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  {D : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)

include hC hk hδc hcap hsm hmar hα hD

/-- **Support of the mixed differences for cut sets of scale `≥ 2`, without `HatConn`.**  For a
datum of the chart of any generating set with `FlCore` (for instance a local generating set,
`dgSetting_castG_localB`) and a cut set `J` of parameter cubes of scale `≥ 2`: if `Δ_J` of the
rooted trace of `B` with its background is non-zero, every parameter cube of `J` lies in the
footprint of a centre joined to a block of `B` by a chain in `J`. -/
theorem exists_rootChain_of_mixDiff_rootTraceBg_ne_zero_of_two_le (B : Finset (unitPts Gp))
    {J : Finset (cubeIdx Gp)} (hJ : ∀ P ∈ J, 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1)
    (hne : mixDiff J (rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp)
      (unitP Gp) B D) ≠ 0) :
    ∃ y ∈ B, ∀ p ∈ J, ∃ q, RootChain Gp J y q ∧ p ∈ QsetP Gp q :=
  exists_rootChain_of_mixDiff_rootTraceBg_ne_zero_of_conn hC hk hδc hcap hsm hmar hα hD B
    (fun _ hq => connIn_hatI_of_actIn_of_two_le hC.Sp hJ hq) hne

omit hC hk hδc hcap hsm hmar hα hD in
/-- A cut set with hull `Y`, `Y` avoiding the layer `1`, consists of cubes of scale `≥ 2` (the
cubes of a cut set lie in the sites of its hull). -/
theorem two_le_of_hull_avoid (hN : L ^ m₀ ∣ N₁) (y : unitPts Gp)
    {Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hYav : ∀ x ∈ sitesOf Y, x ∉ Gp.layer 1) {J : Finset (cubeIdx Gp)}
    (hJY : hullOf m₀ (rootIdxOf y) (patches J) = Y) :
    ∀ P ∈ J, 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1 := by
  intro P hP
  obtain ⟨⟨hm1, -⟩, hl, -⟩ := (mem_cubeIdx Gp).1 P.2
  by_contra h2
  have h1 : (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1 = 1 := by omega
  have hbase : (P : ℕ × CTorus d L N₁ m₁ (k + 1)).2 ∈ cubeP (P : ℕ × CTorus d L N₁ m₁ (k + 1)) :=
    mem_cubeP.2 (SameCell.refl _ _)
  have hsite : (P : ℕ × CTorus d L N₁ m₁ (k + 1)).2 ∈ sitesOf Y := by
    rw [← hJY]
    exact subset_sitesOf_piHull hN (hullSet m₀ (rootIdxOf y) (patches J))
      (Or.inr (Set.mem_iUnion₂.2 ⟨P.1, mem_patches.2 ⟨P.2, hP⟩, mem_Pset_iff.2 hbase⟩))
  rw [h1] at hl
  exact hYav _ hsite hl

/-- **The support of the restricted rooted trace.**  For `F'(s) = F(s')`, `F` the rooted trace of
`B` with its background and `s'` the restriction of `s` to the cubes of scale `≥ 2`, every cut set
with non-zero mixed difference is joined to a block of `B` (no `HatConn`). -/
theorem restrict_cutSupport (B : Finset (unitPts Gp)) (J : Finset (cubeIdx Gp))
    (hne : mixDiff J (fun s => rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp)
      (unitP Gp) B D fun P => if 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1 then s P else 0) ≠ 0) :
    (∀ P ∈ J, 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1) ∧
      ∃ y ∈ B, ∀ p ∈ J, ∃ q, RootChain Gp J y q ∧ p ∈ QsetP Gp q := by
  by_cases hJ : ∀ P ∈ J, 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1
  · rw [mixDiff_restrict_two_le _ hJ] at hne
    exact ⟨hJ, exists_rootChain_of_mixDiff_rootTraceBg_ne_zero_of_two_le hC hk hδc hcap hsm hmar
      hα hD B hJ hne⟩
  · push Not at hJ
    obtain ⟨p, hp, hp2⟩ := hJ
    exact absurd (mixDiff_restrict_two_le_eq_zero _ hp (by omega)) hne

omit hC hk hδc hcap hsm hmar hα hD in
/-- The cut sets with hull `Y`, `Y` avoiding the layer `1`, see the same mixed differences of the
rooted trace and of its restriction to the cubes of scale `≥ 2`. -/
theorem cutActivity_restrict_eq_of_avoid (hN : L ^ m₀ ∣ N₁) (y : unitPts Gp)
    {Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hYav : ∀ x ∈ sitesOf Y, x ∉ Gp.layer 1) :
    cutActivity m₀ (fun s => rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp)
      (unitP Gp) {y} D fun P => if 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1 then s P else 0)
        y Y =
      detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y := by
  classical
  rw [detActivityBg_eq_cutActivity]
  unfold cutActivity
  refine Finset.sum_congr rfl fun J hJ => ?_
  exact mixDiff_restrict_two_le _ (two_le_of_hull_avoid hN y hYav (Finset.mem_filter.1 hJ).2)

open Classical in
/-- **Support of the activity of a polymer avoiding the layer `1`, without `HatConn`.**  A
non-zero activity `detActivityBg y Y` of a polymer `Y` none of whose sites lies in the layer `1`
lives on a polymer containing the root cube. -/
theorem detActivityBg_ne_zero_imp_of_avoid (hN : L ^ m₀ ∣ N₁) {y : unitPts Gp}
    {Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ)}
    (hYav : ∀ x ∈ sitesOf Y, x ∉ Gp.layer 1)
    (h : detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y ≠ 0) :
    rootCube (m₀ := m₀) (rootIdxOf y) ∈ Y ∧ IsPolyDom m₀ (k + 1) (sitesOf Y) := by
  rw [← cutActivity_restrict_eq_of_avoid hN y hYav] at h
  refine cutActivity_ne_zero_imp_of_conn hC.Sp hN (fun J hne => ?_) (fun J hne _ hq => ?_) h
  · obtain ⟨-, y', hy', hJ⟩ := restrict_cutSupport hC hk hδc hcap hsm hmar hα hD {y} J hne
    rw [Finset.mem_singleton] at hy'
    exact hy' ▸ hJ
  · exact connIn_hatI_of_actIn_of_two_le hC.Sp
      (restrict_cutSupport hC hk hδc hcap hsm hmar hα hD {y} J hne).1 hq

open Classical in
/-- **Exponential decay of the activity of a polymer avoiding the layer `1`, without `HatConn`.**
With `Δ = detDeg d L + 1`, `z = Δ² · 2 / e^κ < 1` and `λ = κ - log 2 - 2 log Δ`: for a polymer
`Y` none of whose sites lies in the layer `1`,
`‖detActivityBg y Y‖ ≤ ½ N covBLog / (1 - z) · exp(-(λ / (2 d L)) dExt Y)` (the bound of
`norm_detActivityBg_le`). -/
theorem norm_detActivityBg_le_of_avoid (hN : L ^ m₀ ∣ N₁) (y : unitPts Gp)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1)
    (Y : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
      Set.univ))
    (hYav : ∀ x ∈ sitesOf Y, x ∉ Gp.layer 1) :
    ‖detActivityBg m₀ (compWeight L a₁) a₁ ν (rho4 d L N BG κ) D y Y‖ ≤
      (1 / 2 : ℝ) * N * covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ /
        (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ)) *
      Real.exp (-((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) /
        (2 * d * L)) * dExt Y) := by
  rw [← cutActivity_restrict_eq_of_avoid hN y hYav]
  have hΔ0 : (0 : ℝ) < ((detDeg d L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hbd0 := (rootTraceBg_cut_expansion hC hk hδc hcap hsm hmar hα
    (isUnitLatticeB_unit (G := Gp)).toIsUnitLattice {y} hD).2
  have hM0 : 0 ≤ (1 / 2 : ℝ) * N * covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ := by
    have := (norm_nonneg _).trans (hbd0 ∅)
    simpa using this
  have hbd : ∀ J : Finset (cubeIdx Gp),
      ‖mixDiff J (fun s => rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp)
        (unitP Gp) {y} D fun P => if 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1 then s P else 0)‖ ≤
        (1 / 2 : ℝ) * N * covBLog d L (compWeight L a₁ k) (a₁ / (L : ℝ) ^ 2) κ *
          (2 / Real.exp κ) ^ J.card := by
    intro J
    by_cases hJ : ∀ P ∈ J, 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1
    · rw [mixDiff_restrict_two_le _ hJ]
      have := hbd0 J
      simpa only [Finset.card_singleton, Nat.cast_one, mul_one] using this
    · push Not at hJ
      obtain ⟨p, hp, hp2⟩ := hJ
      rw [mixDiff_restrict_two_le_eq_zero _ hp (by omega), norm_zero]
      positivity
  have hsupp : ∀ J : Finset (cubeIdx Gp),
      mixDiff J (fun s => rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp)
        (unitP Gp) {y} D fun P => if 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1 then s P else 0) ≠
        0 → ∀ p ∈ J, ∃ q, RootChain Gp J y q ∧ p ∈ QsetP Gp q := by
    intro J hne
    obtain ⟨-, y', hy', hJ⟩ := restrict_cutSupport hC hk hδc hcap hsm hmar hα hD {y} J hne
    rw [Finset.mem_singleton] at hy'
    exact hy' ▸ hJ
  have hconnF : ∀ J : Finset (cubeIdx Gp),
      mixDiff J (fun s => rootTraceBg Gp (compWeight L a₁) a₁ ν (rho4 d L N BG κ) (unitQ Gp)
        (unitP Gp) {y} D fun P => if 2 ≤ (P : ℕ × CTorus d L N₁ m₁ (k + 1)).1 then s P else 0) ≠
        0 → ∀ q, ActIn Gp J q → ConnIn (hatI Gp q) := fun J hne _ hq =>
    connIn_hatI_of_actIn_of_two_le hC.Sp
      (restrict_cutSupport hC hk hδc hcap hsm hmar hα hD {y} J hne).1 hq
  have h := norm_cutActivity_le_of_conn (m₀ := m₀) hC.Sp hN hsupp hconnF (by positivity) hbd hz Y
  rw [log_cutRate hΔ0 κ] at h
  have e : -(κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L) =
      -((κ - Real.log 2 - 2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * d * L)) := by ring
  rw [e] at h
  exact h

end Det

end Balaban.Fluctuation
