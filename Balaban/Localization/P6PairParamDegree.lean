/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.P6PairChain
public import Balaban.Localization.P6FsharpRootedCount
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sharp rootedness of the reached patches of the P6 pair, and the sharp rooted sum

Finite geometry and combinatorics only.  This file improves the count of `P6PairChain.lean`
(`VMOD-39` §3, packages (2)-(4)).  Active-only coefficient support
(`OPEN-P6-ACTIVE-COMPOSITE-LOC`) and the choice of the uncut core `X₁`
(`OPEN-P6-X1-INSTANTIATION`) are open; this file only supplies the combinatorial count that a proved
support statement would feed.

## Where the three-edge paths came from

Let `u` (newer) and `v` (older) be two centres of a root chain joined by a `PairCentreLink`.  Each
centre is parameter-free or charged (`chain_dichotomy`).  The link says either

* (i) the footprints `𝒬(u)`, `𝒬(v)` share a marked patch `P₀`; or
* (ii) a footprint site `y` of `u` is equal or adjacent to a site `x` of the extended footprint of
  `v` (a footprint site of `v`, or a site of a marked patch of `𝒬(v)`).

In case (ii) the cover contains patches `Q_y ∋ y` (in `𝒬(u)`) and `Q_x ∋ x` (in `𝒬(v)`), and `Q_y`,
`Q_x` Moore-touch (or coincide).  A patch of `𝒬(z)` of an eligible centre `z` is either marked or
not a parameter cube, that is, contained in `X₁` (`unmarked_site_mem`).  So the exact case in which
a patch on the way is unmarked is `Q_y ∉ 𝒞` or `Q_x ∉ 𝒞`, and then the site `y` (resp. `x`) lies in
`X₁`.  The landed chain graph `chainPatchGraph` allowed these patches as intermediate vertices,
which gives paths of up to three edges `P -- Q_y -- Q_x -- P_v`.

## What is proved

If both `Q_y` and `Q_x` are marked, they are reached patches themselves, so the path
`P -- Q_y -- Q_x` (and then onward) is a path of the footprint graph `G♯ = paramGraph G` *inside the
set of reached patches*: every step is a single edge of `G♯`.  If one of them is unmarked, its
site lies in `X₁ ⊆ U` (the seed contains the uncut core), and the chain restarts at the seed: the
patch reached so far is in the sharp root set.  Hence:

* `jointParams_rooted_sharp`: every reached marked patch is joined, by a walk of `paramGraph G`
  inside the reached patches, to `pairRootSetSharp G U`, the closed `G♯`-neighbourhood of the
  cover patches that contain a site of the seed `U`.  No longer paths are needed.  The seed is
  assumed to lie in the domain of the cover (`hU`), so that every seed site is in a patch.
* `detDeg_eq`: `detDeg d L = 3 (L+4)^d + 9 (L+9)^d (8 L)^d` (`= 214 991 877` for `d = L = 3`).
* `card_pairRootSetSharp_le`: the root set has at most `(D + 1)` patches per patch meeting `U`.
* `sharp_rooted_sum_le`, `sharp_rooted_sum_le_exp`: `Σ t^|C| ≤ (1 / (1 - (D+1)² t))^{|S|}` over the
  sets rooted at the closed neighbourhoods of the patches `S` meeting the seed; the rate
  requirement is `κ₂ > 2 log (D + 1) ≈ 38.4` for `d = L = 3`.
* `p6_sharp_cells_sum_le`: for a seed that is the union of top cells of active cells `u ∈ A`,
  a sum rooted at the cells, with constant `p6SharpD = (D + 1) 3^d (L^{m₀})^d`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Finset

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}

section Degree

open Balaban.Fluctuation

/-- **The degree constant of the footprint graph, in closed form.** -/
theorem detDeg_eq (d L : ℕ) : detDeg d L = 3 * (L + 4) ^ d + 9 * (L + 9) ^ d * (8 * L) ^ d := by
  unfold detDeg N0
  ring

/-- `detDeg 3 3 = 214 991 877`. -/
theorem detDeg_three : detDeg 3 3 = 214991877 := by
  rw [detDeg_eq]
  norm_num

end Degree

section Sharp

open Balaban.Fluctuation Balaban.Polymer Classical

variable {k : ℕ} {ϱG : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱG}

variable (G) in
/-- The cover patches that contain a site of the seed `U`. -/
noncomputable def meetCubes (U : Set (CTorus d L N₁ m₁ (k + 1))) : Finset (cubeIdx G) :=
  Finset.univ.filter fun Q => ∃ y ∈ cubeP Q.1, y ∈ U

variable (G) in
/-- **The sharp root set**: the patches that are equal or adjacent in the footprint graph `G♯`
(Moore touching, or a common footprint) to a cover patch containing a site of the seed `U`. -/
noncomputable def pairRootSetSharp (U : Set (CTorus d L N₁ m₁ (k + 1))) : Set (cubeIdx G) :=
  ⋃ Q ∈ meetCubes G U, ((closedNbhd Q : Finset (cubeIdx G)) : Set (cubeIdx G))

theorem mem_meetCubes {U : Set (CTorus d L N₁ m₁ (k + 1))} {Q : cubeIdx G} :
    Q ∈ meetCubes G U ↔ ∃ y ∈ cubeP Q.1, y ∈ U := by
  simp [meetCubes]

theorem mem_closedNbhd {P Q : cubeIdx G} :
    P ∈ closedNbhd Q ↔ P = Q ∨ (paramGraph G).Adj P Q := by
  unfold closedNbhd
  rw [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
  exact or_congr_right (SimpleGraph.adj_comm _ _ _)

theorem mem_pairRootSetSharp {U : Set (CTorus d L N₁ m₁ (k + 1))} {P : cubeIdx G} :
    P ∈ pairRootSetSharp G U ↔
      ∃ Q : cubeIdx G, (∃ y ∈ cubeP Q.1, y ∈ U) ∧ (P = Q ∨ (paramGraph G).Adj P Q) := by
  unfold pairRootSetSharp
  simp only [Set.mem_iUnion, Finset.mem_coe, mem_meetCubes, mem_closedNbhd, exists_prop]

section Rooted

variable {Hb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {ν : ℝ} {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))}
  {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))} {U : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **An unmarked patch of an eligible centre lies in `X₁`.**  A patch of `𝒬(z)` of an eligible
centre `z` that is not marked is not a parameter cube, that is, it is contained in `X₁`. -/
theorem unmarked_site_mem {u : Bool × (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hu : PairAct (coverOf G) Hb Hm X₁ 𝒞 u) {Q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hQ : Q ∈ Qset G u.2) (hQ𝒞 : Q ∉ 𝒞) {y : CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ cubeP Q) :
    y ∈ X₁ := by
  by_contra hyX
  exact hQ𝒞 (hu.1.2 Q hQ (Finset.mem_filter.2
    ⟨Qset_subset_cubeIdx _ hQ, fun hsub => hyX (hsub hy)⟩))

/-- **Sharp rootedness.**  Under `X₁ ⊆ U` and `U ⊆ Ω₁`, every reached marked patch is joined, by a
walk of the footprint graph `G♯ = paramGraph G` (Moore touch or common footprint) inside the set of
reached patches, to the sharp root set of the seed. -/
theorem jointParams_rooted_sharp (hG : CubeAligned G m₁)
    (hΩb : ∀ x ∈ Hb.Ω 1, x ∈ G.Ω 1) (hΩm : ∀ x ∈ Hm.Ω 1, x ∈ G.Ω 1)
    (hfb : ∀ z ∈ cubeIdx G, ∀ t ∈ footprint Hb a ν z, t ∈ hatBox z)
    (hfm : ∀ z ∈ cubeIdx G, ∀ t ∈ footprint Hm a ν z, t ∈ hatBox z)
    (hX : ∀ x ∈ X₁, x ∈ U) (hU : ∀ s ∈ U, s ∈ G.Ω 1) :
    Rooted (paramGraph G) (pairRootSetSharp G U)
      ((jointParams (coverOf G) Hb Hm a ν X₁ 𝒞 U).subtype (fun P => P ∈ cubeIdx G)) := by
  set J := (jointParams (coverOf G) Hb Hm a ν X₁ 𝒞 U).subtype (fun P => P ∈ cubeIdx G) with hJ
  have memJ : ∀ {u : Bool × (ℕ × CTorus d L N₁ m₁ (k + 1))},
      PairRootChain (coverOf G) Hb Hm a ν X₁ 𝒞 U u → ∀ P : cubeIdx G, P.1 ∈ Qset G u.2 →
        P.1 ∈ 𝒞 → P ∈ J := fun hu P hP hP𝒞 =>
    Finset.mem_subtype.2 (mem_jointParams_of_chain hu hP hP𝒞)
  have walkJ : ∀ {P P' : cubeIdx G}, P ∈ J → P' ∈ J →
      (P = P' ∨ (paramGraph G).Adj P P') → WalkIn (paramGraph G) J P P' :=
    fun hP hP' h => walkIn_of_eq_or_adj hP hP' h
  have rootOf : ∀ (Q P : cubeIdx G), (∃ y ∈ cubeP Q.1, y ∈ U) →
      (P = Q ∨ (paramGraph G).Adj P Q) → P ∈ pairRootSetSharp G U :=
    fun Q P h1 h2 => mem_pairRootSetSharp.2 ⟨Q, h1, h2⟩
  have nearRoot : ∀ (Qy : cubeIdx G) (y s : CTorus d L N₁ m₁ (k + 1)), s ∈ U →
      (s = y ∨ Adj s y) → y ∈ cubeP Qy.1 → Qy ∈ pairRootSetSharp G U := by
    intro Qy y s hs hnear hyQ
    obtain ⟨Q, hQ, hsQ⟩ := exists_cube_of_mem_Omega hG (hU s hs)
    refine rootOf ⟨Q, hQ⟩ Qy ⟨s, hsQ, hs⟩ ?_
    exact pg_moore (P := Qy) (P' := ⟨Q, hQ⟩) hyQ hsQ
      (hnear.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm))
  have claim : ∀ u v, Relation.ReflTransGen (PairCentreLink (coverOf G) Hb Hm a ν X₁ 𝒞) u v →
      PairAnchor (coverOf G) Hb Hm a ν X₁ 𝒞 U v →
      ∀ P : cubeIdx G, P.1 ∈ Qset G u.2 → P.1 ∈ 𝒞 →
        ∃ w ∈ pairRootSetSharp G U, WalkIn (paramGraph G) J P w := by
    intro u v hr hv
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro P hP hP𝒞
      have hvc : PairRootChain (coverOf G) Hb Hm a ν X₁ 𝒞 U v := PairRootChain.of_anchor hv
      have hPJ := memJ hvc P hP hP𝒞
      obtain ⟨hact, s, hs, y, hy, hatt⟩ := hv
      obtain ⟨Qy, hyQ, hQyz⟩ := pFoot_cube hG hΩb hΩm hfb hfm hact.1.1 hy
      have e1 := pg_common (P := P) (P' := Qy) hact.1.1 hP hQyz
      by_cases hQy𝒞 : Qy.1 ∈ 𝒞
      · have hQyJ := memJ hvc Qy hQyz hQy𝒞
        exact ⟨Qy, nearRoot Qy y s hs (att_near hatt) hyQ, walkJ hPJ hQyJ e1⟩
      · have hyX := unmarked_site_mem hact hQyz hQy𝒞 hyQ
        exact ⟨P, rootOf Qy P ⟨y, hyQ, hX y hyX⟩ e1, WalkIn.refl hPJ⟩
    | @head u' w hstep hrest ih =>
      intro P hP hP𝒞
      obtain ⟨hu', hw, hcase⟩ := hstep
      have hwc : PairRootChain (coverOf G) Hb Hm a ν X₁ 𝒞 U w := ⟨v, hv, hrest⟩
      have huc : PairRootChain (coverOf G) Hb Hm a ν X₁ 𝒞 U u' := PairRootChain.head
        ⟨hu', hw, hcase⟩ hwc
      have hPJ := memJ huc P hP hP𝒞
      rcases hcase with ⟨x, hx, y, hy, hatt⟩ | ⟨P₀, hP₀𝒞, hP₀u, hP₀w⟩
      · obtain ⟨Qy, hyQ, hQyu⟩ := pFoot_cube hG hΩb hΩm hfb hfm hu'.1.1 hy
        have hnear := att_near hatt
        have hnear' : y = x ∨ Adj y x :=
          hnear.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
        have e1 := pg_common (P := P) (P' := Qy) hu'.1.1 hP hQyu
        by_cases hQy𝒞 : Qy.1 ∈ 𝒞
        · have hQyJ := memJ huc Qy hQyu hQy𝒞
          obtain ⟨r, hr, wk⟩ : ∃ r ∈ pairRootSetSharp G U, WalkIn (paramGraph G) J Qy r := by
            rcases hx with hx | ⟨P', hP'𝒞, hP'w, hxP'⟩
            · obtain ⟨Qx, hxQ, hQxw⟩ := pFoot_cube hG hΩb hΩm hfb hfm hw.1.1 hx
              by_cases hQx𝒞 : Qx.1 ∈ 𝒞
              · have hQxJ := memJ hwc Qx hQxw hQx𝒞
                obtain ⟨r, hr, wk⟩ := ih Qx hQxw hQx𝒞
                exact ⟨r, hr, (walkJ hQyJ hQxJ
                  (pg_moore (P := Qy) (P' := Qx) hyQ hxQ hnear')).trans wk⟩
              · have hxX := unmarked_site_mem hw hQxw hQx𝒞 hxQ
                exact ⟨Qy, nearRoot Qy y x (hX x hxX) hnear hyQ, WalkIn.refl hQyJ⟩
            · have hP'c : P' ∈ cubeIdx G := Qset_subset_cubeIdx _ hP'w
              obtain ⟨r, hr, wk⟩ := ih ⟨P', hP'c⟩ hP'w hP'𝒞
              have hP'J := memJ hwc ⟨P', hP'c⟩ hP'w hP'𝒞
              exact ⟨r, hr, (walkJ hQyJ hP'J
                (pg_moore (P := Qy) (P' := ⟨P', hP'c⟩) hyQ hxP' hnear')).trans wk⟩
          exact ⟨r, hr, (walkJ hPJ hQyJ e1).trans wk⟩
        · have hyX := unmarked_site_mem hu' hQyu hQy𝒞 hyQ
          exact ⟨P, rootOf Qy P ⟨y, hyQ, hX y hyX⟩ e1, WalkIn.refl hPJ⟩
      · have hP₀c : P₀ ∈ cubeIdx G := Qset_subset_cubeIdx _ hP₀w
        obtain ⟨r, hr, wk⟩ := ih ⟨P₀, hP₀c⟩ hP₀w hP₀𝒞
        have hP₀J := memJ hwc ⟨P₀, hP₀c⟩ hP₀w hP₀𝒞
        have e1 := pg_common (P := P) (P' := ⟨P₀, hP₀c⟩) hu'.1.1 hP hP₀u
        exact ⟨r, hr, (walkJ hPJ hP₀J e1).trans wk⟩
  intro P hP
  obtain ⟨hP𝒞, u, hu, hPu⟩ := jointParams_support hX (Finset.mem_subtype.1 hP)
  obtain ⟨v, hv, hr⟩ := hu
  exact claim u v hr hv P hPu hP𝒞

end Rooted

/-! ### The count -/

section Count

theorem card_closedNbhd_le' (hdeg : ∀ P : cubeIdx G, (paramGraph G).degree P ≤ detDeg d L)
    (Q : cubeIdx G) : (closedNbhd Q).card ≤ detDeg d L + 1 :=
  card_closedNbhd_le hdeg Q

/-- The sharp root set has at most `D + 1` patches per patch meeting the seed. -/
theorem card_pairRootSetSharp_le (hdeg : ∀ P : cubeIdx G, (paramGraph G).degree P ≤ detDeg d L)
    (U : Set (CTorus d L N₁ m₁ (k + 1))) :
    ∃ F : Finset (cubeIdx G), (F : Set (cubeIdx G)) = pairRootSetSharp G U ∧
      F.card ≤ (detDeg d L + 1) * (meetCubes G U).card := by
  refine ⟨(meetCubes G U).biUnion closedNbhd, ?_, ?_⟩
  · ext P; simp [pairRootSetSharp]
  · refine Finset.card_biUnion_le.trans ?_
    calc ∑ Q ∈ meetCubes G U, (closedNbhd Q).card
        ≤ ∑ _Q ∈ meetCubes G U, (detDeg d L + 1) :=
          Finset.sum_le_sum fun Q _ => card_closedNbhd_le hdeg Q
      _ = (detDeg d L + 1) * (meetCubes G U).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The sharp rooted sum.**  With `D = detDeg d L`, `z = (D+1)² t < 1`:
`Σ t^|C| ≤ (1/(1-z))^|S|` over the sets rooted at the closed neighbourhoods of the patches in `S`
(for the seed `U`, take `S = meetCubes G U`; the root set is then `pairRootSetSharp G U`). -/
theorem sharp_rooted_sum_le (hG : CubeAligned G m₁) (hSS : SupSep G m₁)
    (hd : (d : ℝ) ≤ ϱG * (L : ℝ) ^ 2) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L)
    (S : Finset (cubeIdx G)) {t : ℝ} (ht : 0 ≤ t)
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * t < 1) :
    ∑ C ∈ rootedSets (G := paramGraph G) (⋃ Q ∈ S, ((closedNbhd Q : Finset (cubeIdx G)) :
        Set (cubeIdx G))), t ^ C.card
      ≤ (1 / (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * t)) ^ S.card := by
  have hdeg := fun P => paramGraph_degree_le_sup (G := G) hG hSS hd hM hL P
  have key := sum_rooted_le (G := paramGraph G) (b := detDeg d L) (b_root := detDeg d L + 1)
    hdeg (fun Q : cubeIdx G => closedNbhd Q) (fun Q => card_closedNbhd_le hdeg Q) ht
    (by rwa [max_self]) S
  rwa [max_self] at key

/-- **The sharp rooted sum, exponential form.**  With `t = e^{-κ₂}`, `z = (D+1)² t < 1`,
`h = -log (1 - z)`: if `|S| ≤ c_A (1 + Δ)` the sum is at most `e^{h c_A} e^{h c_A Δ}`. -/
theorem sharp_rooted_sum_le_exp (hG : CubeAligned G m₁) (hSS : SupSep G m₁)
    (hd : (d : ℝ) ≤ ϱG * (L : ℝ) ^ 2) (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L)
    (S : Finset (cubeIdx G)) {κ₂ Δ c_A : ℝ}
    (hz : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) < 1)
    (hR : (S.card : ℝ) ≤ c_A * (1 + Δ)) :
    ∑ C ∈ rootedSets (G := paramGraph G) (⋃ Q ∈ S, ((closedNbhd Q : Finset (cubeIdx G)) :
        Set (cubeIdx G))), Real.exp (-κ₂ * C.card)
      ≤ Real.exp (-Real.log (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_A) *
        Real.exp (-Real.log (1 - ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_A * Δ) := by
  set z : ℝ := ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) with hzdef
  have hz0 : 0 ≤ z := by positivity
  have hpos : 0 < 1 - z := by linarith
  set h : ℝ := -Real.log (1 - z) with hh
  have hh0 : 0 ≤ h := by
    have : Real.log (1 - z) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  have hsum := sharp_rooted_sum_le hG hSS hd hM hL S (Real.exp_pos (-κ₂)).le hz
  have hterm : ∀ C : Finset (cubeIdx G), Real.exp (-κ₂ * C.card) = Real.exp (-κ₂) ^ C.card :=
    fun C => by rw [← Real.exp_nat_mul]; ring_nf
  simp only [hterm]
  refine hsum.trans ?_
  have : 1 / (1 - z) = Real.exp h := by
    rw [hh, Real.exp_neg, Real.exp_log hpos, one_div]
  rw [this, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith [mul_le_mul_of_nonneg_left hR hh0]

/-- **The reached patches form a set rooted at the sharp root set of the seed**, hence are one of
the sets counted by `sharp_rooted_sum_le` with `S = meetCubes G U`. -/
theorem jointParams_mem_rootedSets_sharp {Hb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ'}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {ν : ℝ}
    {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    {U : Set (CTorus d L N₁ m₁ (k + 1))} (hG : CubeAligned G m₁)
    (hΩb : ∀ x ∈ Hb.Ω 1, x ∈ G.Ω 1) (hΩm : ∀ x ∈ Hm.Ω 1, x ∈ G.Ω 1)
    (hfb : ∀ z ∈ cubeIdx G, ∀ t ∈ footprint Hb a ν z, t ∈ hatBox z)
    (hfm : ∀ z ∈ cubeIdx G, ∀ t ∈ footprint Hm a ν z, t ∈ hatBox z)
    (hX : ∀ x ∈ X₁, x ∈ U) (hU : ∀ s ∈ U, s ∈ G.Ω 1) :
    ((jointParams (coverOf G) Hb Hm a ν X₁ 𝒞 U).subtype (fun P => P ∈ cubeIdx G)) ∈
      rootedSets (G := paramGraph G)
        (⋃ Q ∈ meetCubes G U, ((closedNbhd Q : Finset (cubeIdx G)) : Set (cubeIdx G))) :=
  mem_rootedSets.2 (jointParams_rooted_sharp hG hΩb hΩm hfb hfm hX hU)

end Count

end Sharp

end Balaban.Localization.Dec2

/-! ### The P6 pair -/

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Localization.Dec2 Balaban.Polymer
  Balaban.Fluctuation

set_option linter.unusedSectionVars false

section P6

variable {d M1 c n1 L k n0 m₁ m₀ : ℕ} [NeZero L] [NeZero c] [NeZero M1] [NeZero n0] [NeZero n1]
  {Rprev Rk : ℝ} {Zp : Set (Torus d n1)} (st : RegionStep d L n0 n1 Rprev Rk)

/-- **Sharp rootedness for the P6 pair.**  For `C = coverOf F♯`, `H_b = H^∂`, `H_m = H^-`, a seed
`U ⊇ X₁` contained in the domain of `F♯`: every reached marked patch is joined, by a walk of the
footprint graph `G♯ = paramGraph F♯` inside the reached patches, to the sharp root set of the seed.
Counting only (`OPEN-P6-ACTIVE-COMPOSITE-LOC`, `OPEN-P6-X1-INSTANTIATION`). -/
theorem p6_jointParams_rooted_sharp (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1))
    (X₁ : Finset (Localization.CTorus d L (c * n1) m₁ (k + 1)))
    (𝒞 : Finset (ℕ × Localization.CTorus d L (c * n1) m₁ (k + 1)))
    (U : Set (Localization.CTorus d L (c * n1) m₁ (k + 1))) (hX : ∀ x ∈ X₁, x ∈ U)
    (hU : ∀ s ∈ U, s ∈ (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1).Ω 1) :
    Rooted (paramGraph (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
      (pairRootSetSharp (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1) U)
      ((jointParams (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
        (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ)
        (p6OldC (k := k) (n1 := n1) (c := c) hM1 ⌊Rprev⌋₊ st.Z) a ν X₁ 𝒞 U).subtype
        (fun P => P ∈ cubeIdx (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))) :=
  jointParams_rooted_sharp
    (GeneratingSet.castN_cubeAligned _ (p6_fsharp_cubeAligned hn hρ (by omega : 5 ≤ c) st.Z hM1 hm₁))
    (fun x hx => (GeneratingSet.castN_precedes _ (p6_boundary_embedded st hc hn hL hρ hZ)).mem_Ω1 hx)
    (fun x hx => (GeneratingSet.castN_precedes _
      (p6_old_precedes hn hρ (by omega : 5 ≤ c) st.Z)).mem_Ω1 hx)
    (footprint_hat_of_coverGeom (p6_coverGeom_boundary st hc hn hL hρ hZ hM1 hm₁ hM hd hL3 hν hνL
      ha hsep))
    (footprint_hat_of_coverGeom (p6_coverGeom_old hn hρ (by omega : 5 ≤ c) st.Z hM1 hm₁ hM hd hL3
      hν hνL ha hsep)) hX hU

open Classical in
/-- **Degree of the footprint graph `G♯` of `F♯`** (`d < 5 L³ M₁`): at most `detDeg d L`, and
`detDeg d L = 3 (L+4)^d + 9 (L+9)^d (8 L)^d` (`detDeg_eq`). -/
theorem p6_paramGraph_degree_le (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) (hd : d < 5 * L ^ 3 * M1)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L)
    (P : cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1)) :
    (paramGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1)).degree P ≤ detDeg d L :=
  paramGraph_degree_le_sup
    (GeneratingSet.castN_cubeAligned _ (p6_fsharp_cubeAligned hn hρ hc Z hM1 hm₁))
    (GeneratingSet.castN_supSep _ (p6_fsharp_supSep hn hρ hc Z hM1)) (p6_moore_premise hd) hM hL P

/-- The constant of the sharp rooted sum indexed by patches: `D + 1`, `D = detDeg d L`. -/
def p6SharpDPatch (d L : ℕ) : ℕ := detDeg d L + 1

/-- The constant of the sharp rooted sum indexed by active cells:
`max (D + 1) ((D + 1) 3^d (L^m₀)^d)`. -/
def p6SharpD (d L m₀ : ℕ) : ℕ :=
  max (detDeg d L + 1) ((detDeg d L + 1) * (3 ^ d * (L ^ m₀) ^ d))

open Classical in
/-- **The sharp rooted sum for `F♯`, indexed by patches** (exponential form): for a finite set `S`
of patches (take `S = meetCubes F♯ U` for the seed `U`), `z = (D+1)² e^{-κ₂} < 1`,
`h = -log (1 - z)`, `|S| ≤ c_A (1 + Δ)`:
`Σ_{C rooted at the closed neighbourhoods of S} e^{-κ₂ |C|} ≤ e^{h c_A} e^{h c_A Δ}`. -/
theorem p6_sharp_rooted_sum_le (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁) (hd : d < 5 * L ^ 3 * M1)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L)
    (S : Finset (cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1))) {κ₂ Δ c_A : ℝ}
    (hz : ((p6SharpDPatch d L : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂) < 1)
    (hR : (S.card : ℝ) ≤ c_A * (1 + Δ)) :
    ∑ C ∈ rootedSets (G := paramGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1))
        (⋃ Q ∈ S, ((closedNbhd Q : Finset _) : Set _)), Real.exp (-κ₂ * C.card)
      ≤ Real.exp (-Real.log (1 - ((p6SharpDPatch d L : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_A) *
        Real.exp (-Real.log (1 - ((p6SharpDPatch d L : ℕ) : ℝ) ^ 2 * Real.exp (-κ₂)) * c_A * Δ) :=
  sharp_rooted_sum_le_exp
    (GeneratingSet.castN_cubeAligned _ (p6_fsharp_cubeAligned hn hρ hc Z hM1 hm₁))
    (GeneratingSet.castN_supSep _ (p6_fsharp_supSep hn hρ hc Z hM1)) (p6_moore_premise hd) hM hL
    S hz hR

variable (m₀) in
/-- The sharp root family of the active cell `u`: the closed `G♯`-neighbourhoods of the patches of
`F♯` Moore-touching the top cell of `u`. -/
noncomputable def p6SharpRootNbhd (hn : n0 = L * n1) {ρ' : ℕ} (hρ : 3 * L ≤ ρ') (hc : 5 ≤ c)
    (Z : Set (Torus d n0)) (hM1 : M1 = L ^ m₁)
    (u : Localization.CTorus d L (c * n1) m₁ (k + 1)) :
    Finset (cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc Z hM1)) :=
  open Classical in
  (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc Z hM1 m₀ u).biUnion closedNbhd

open Classical in
/-- **Sharp rooted sum indexed by the active cells.**  For a finite set `A` of active top cells
(hypotheses of `p6_root_patch_count`) and `z = (p6SharpD d L m₀)² t < 1`:
`Σ_{C rooted at the sharp root families of A} t^|C| ≤ (1 / (1 - z))^|A|`. -/
theorem p6_sharp_cells_sum_le (hM1 : M1 = L ^ m₁) (hmc : L ^ m₀ ∣ c) (hn : n0 = L * n1)
    (hL : 0 < L) (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hc : 5 ≤ c) (hm₁ : 2 ≤ m₁) (hd : d < 5 * L ^ 3 * M1)
    (hM : 4 * L ^ 2 ≤ L ^ m₁)
    (A : Finset (Localization.CTorus d L (c * n1) m₁ (k + 1)))
    (hA : ∀ u ∈ A, LargeField.torusCast (by rw [p6_side hM1] : (c * n1) * L ^ m₁ * L ^ (k + 1) =
        M1 * (c * n1) * L ^ (k + 1)) u ∈ fineK1 M1 c n1 L k st.Omega)
    {t : ℝ} (ht : 0 ≤ t) (hz : ((p6SharpD d L m₀ : ℕ) : ℝ) ^ 2 * t < 1) :
    ∑ C ∈ rootedSets (G := paramGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1))
        (⋃ u ∈ A, ((p6SharpRootNbhd (k := k) m₀ hn hρ hc st.Z hM1 u : Finset _) : Set _)),
        t ^ C.card
      ≤ (1 / (1 - ((p6SharpD d L m₀ : ℕ) : ℝ) ^ 2 * t)) ^ A.card := by
  have hdeg := fun P => p6_paramGraph_degree_le (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 hm₁ hd hM
    hL P
  have hN : ∀ u : {u // u ∈ A},
      (p6SharpRootNbhd (k := k) m₀ hn hρ hc st.Z hM1 u.1).card ≤
        (detDeg d L + 1) * (3 ^ d * (L ^ m₀) ^ d) := by
    intro u
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ Q ∈ fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u.1,
          (closedNbhd Q).card
        ≤ ∑ _Q ∈ fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u.1, (detDeg d L + 1) :=
          Finset.sum_le_sum fun Q _ => card_closedNbhd_le hdeg Q
      _ = (fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ hc st.Z hM1 m₀ u.1).card *
            (detDeg d L + 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (3 ^ d * (L ^ m₀) ^ d) * (detDeg d L + 1) :=
          Nat.mul_le_mul_right _ (card_fsharpRootNbhd_le st hM1 hmc hn hL hρ hc u.1 (hA u.1 u.2))
      _ = (detDeg d L + 1) * (3 ^ d * (L ^ m₀) ^ d) := by ring
  have key := sum_rooted_le (G := paramGraph (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1))
    (b := detDeg d L) (b_root := (detDeg d L + 1) * (3 ^ d * (L ^ m₀) ^ d)) hdeg
    (fun u : {u // u ∈ A} => p6SharpRootNbhd (k := k) m₀ hn hρ hc st.Z hM1 u.1) hN ht hz A.attach
  have hU : ((⋃ i ∈ A.attach, ((p6SharpRootNbhd (k := k) m₀ hn hρ hc st.Z hM1 i.1 : Finset _) :
        Set _)) : Set (cubeIdx (p6FsharpC (k := k) (m₁ := m₁) hn hρ hc st.Z hM1)))
      = ⋃ u ∈ A, ((p6SharpRootNbhd (k := k) m₀ hn hρ hc st.Z hM1 u : Finset _) : Set _) := by
    ext x; simp
  rw [hU, Finset.card_attach] at key
  exact key

/-- **The reached patches form a set counted by `p6_sharp_cells_sum_le`.**  For the seed `U` the
union of the top cells of the active cells in `A`, with `X₁ ⊆ U ⊆ Ω₁`. -/
theorem p6_jointParams_mem_rootedSets_cells (hc : 14 ≤ c) (hn : n0 = L * n1) (hL : 2 ≤ L)
    (hρ : 3 * L ≤ ⌊Rprev⌋₊) (hZ : st.Omegaᶜ ⊆ Zp) (hM1 : M1 = L ^ m₁) (hm₁ : 2 ≤ m₁)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) {a : ℕ → ℝ} {ν : ℝ} (hd : 3 ≤ d) (hL3 : 3 ≤ L) (hν : 0 ≤ ν)
    (hνL : ν * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) (ha : IsAdmissibleWeights (k + 1) a)
    (hsep : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L M1 - 1))
    (X₁ : Finset (Localization.CTorus d L (c * n1) m₁ (k + 1)))
    (𝒞 : Finset (ℕ × Localization.CTorus d L (c * n1) m₁ (k + 1)))
    (A : Finset (Localization.CTorus d L (c * n1) m₁ (k + 1)))
    (hX : ∀ x ∈ X₁, ∃ u ∈ A, x ∈ topCell m₀ (k + 1, u))
    (hU : ∀ u ∈ A, ∀ s ∈ topCell m₀ (k + 1, u),
      s ∈ (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1).Ω 1) :
    ((jointParams (coverOf (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
        (p6BoundaryC (k := k) st hM1 hc hn hL hρ hZ)
        (p6OldC (k := k) (n1 := n1) (c := c) hM1 ⌊Rprev⌋₊ st.Z) a ν X₁ 𝒞
        (⋃ u ∈ A, topCell m₀ (k + 1, u))).subtype
        (fun P => P ∈ cubeIdx (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))) ∈
      rootedSets (G := paramGraph (p6FsharpC (k := k) hn hρ (by omega : 5 ≤ c) st.Z hM1))
        (⋃ u ∈ A, ((p6SharpRootNbhd (k := k) m₀ hn hρ (by omega : 5 ≤ c) st.Z hM1 u :
          Finset _) : Set _)) := by
  classical
  rw [mem_rootedSets]
  refine Rooted.mono ?_ (p6_jointParams_rooted_sharp st hc hn hL hρ hZ hM1 hm₁ hM hd hL3 hν hνL ha
    hsep X₁ 𝒞 (⋃ u ∈ A, topCell m₀ (k + 1, u))
    (fun x hx => by
      obtain ⟨u, hu, hxu⟩ := hX x hx
      exact Set.mem_iUnion₂.2 ⟨u, hu, hxu⟩)
    (fun s hs => by
      obtain ⟨u, hu, hsu⟩ := Set.mem_iUnion₂.1 hs
      exact hU u hu s hsu))
  intro P hP
  obtain ⟨Q, ⟨y, hyQ, hyU⟩, hPQ⟩ := mem_pairRootSetSharp.1 hP
  obtain ⟨u, hu, hyu⟩ := Set.mem_iUnion₂.1 hyU
  refine Set.mem_iUnion₂.2 ⟨u, hu, Finset.mem_coe.2 ?_⟩
  unfold p6SharpRootNbhd
  refine Finset.mem_biUnion.2 ⟨Q, ?_, mem_closedNbhd.2 hPQ⟩
  exact (mem_fsharpRootNbhd (k := k) (m₁ := m₁) hn hρ (by omega : 5 ≤ c) st.Z hM1 m₀ u).2
    ⟨y, hyu, y, mem_Pset_iff.2 hyQ, near_of_eq_or_adj (Or.inl rfl)⟩

end P6

end Balaban.LargeField
