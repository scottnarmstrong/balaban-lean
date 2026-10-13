/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.GeneralRenormInput
public import Balaban.Fluctuation.ClassOldTermInputE
public import Balaban.Fluctuation.ClassOldTermSiteSums
public import Balaban.Fluctuation.HatLabelsGeom
public import Balaban.Fluctuation.RootActiveSize
public import Balaban.Fluctuation.MarkFibreSitesOf
public import Balaban.Polymer.MarkedCubes
public import Balaban.SmallField.PsiGeomPath
public import Balaban.SmallField.Def6v2
public import Balaban.Fluctuation.GeneralEnergyMarksBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The inherited energy of a class member as a coefficient family over cube sets

A label `τ = (j, y, X)` of the old energy of a class (`mem_classLabels_E_iff`) has a polymer
`X ∈ 𝒟_j` with `j ≤ k`.  Here the labels are regrouped into the cube sets `T` of the level `k + 1`.

* `box_subset_box_cbase_of_dvd`: a box of side `L a` based at a point aligned to `a` lies in the
  box of side `L c` at the coarsened base, for `a ∣ c`;
* `exists_cubeSet_of_isPolyDom`: for a polymer `X ∈ 𝒟_j`, `j ≤ K`, there is a set `T` of cubes of the
  level `K` with `X ⊆ sitesOf T`, `sitesOf T ∈ 𝒟_K` and `d_Ω(T) ≤ d^cov_j(X)`: the lifted cubes are
  met by the connected structure of `X`, so the same structure measures the lift, at the smaller
  bond cost.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.SmallField Balaban.SmallField.Def6

section Geometry

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **A box lies in the box of the coarsened base.**  If `b` is aligned to `a`, `a ∣ c`, `0 < a`
and `0 < c`, then `box b (L a) ⊆ box (cbase c b) (L c)`. -/
theorem box_subset_box_cbase_of_dvd {n : ℕ} [NeZero n] {a c L : ℕ} (hc : 0 < c) (hac : a ∣ c)
    (hL : 1 ≤ L) {b : Torus d n} (hb : Aligned a b) :
    box b (L * a) ⊆ box (cbase c b) (L * c) := by
  rintro x ⟨w, hw, rfl⟩
  refine ⟨(fun μ => (b μ).val % c) + w, fun μ => ?_, ?_⟩
  · have h1 : (b μ).val % c < c := Nat.mod_lt _ hc
    have h2 : ((b μ).val % c) % a = 0 := by rw [Nat.mod_mod_of_dvd _ hac]; exact hb μ
    obtain ⟨s, hs⟩ := Nat.dvd_of_mod_eq_zero h2
    obtain ⟨r, hr⟩ := hac
    have hsr : s < r := by
      by_contra hcon
      replace hcon := not_lt.1 hcon
      have : a * r ≤ a * s := Nat.mul_le_mul_left a hcon
      omega
    have h3 : (b μ).val % c + a ≤ c := by
      have : a * (s + 1) ≤ a * r := Nat.mul_le_mul_left a hsr
      rw [mul_add] at this
      omega
    have h4 : a ≤ c := by omega
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have h5 : L' * a ≤ L' * c := Nat.mul_le_mul_left L' h4
    have h6 := hw μ
    simp only [Pi.add_apply]
    nlinarith
  · rw [cbase_eq_sub, natT_add]; abel

omit [NeZero N₁] in
/-- The bond weight decreases with the level. -/
theorem bondCost_scaleW_mono {j j' : ℕ} (hjj : j ≤ j')
    (E : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)) :
    bondCost (scaleW L m₀ m₁ j') E ≤ bondCost (scaleW L m₀ m₁ j) E := by
  refine Finset.sum_le_sum fun p _ => ?_
  unfold scaleW
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hL (by omega))

/-- **The cube set of a polymer.**  For a polymer `X ∈ 𝒟_j` with `j ≤ K` there is a set `T` of cubes
of the level `K` (all of `Ω = univ`) whose sites contain `X`, form a polymer `𝒟_K`, and have
`d_Ω(T) ≤ d^cov_j(X)`.  The cubes of `T` are the cubes of the level `K` containing the chosen cubes of
`X` (`box_subset_box_cbase_of_dvd`); the connected structure of `X` meets them all, and its bonds cost
less at the level `K`. -/
theorem exists_cubeSet_of_isPolyDom (hN : L ^ m₀ ∣ N₁) {j : ℕ} (hjK : j ≤ K) {X : Set (CTorus d L N₁ m₁ K)}
    (hX : IsPolyDom m₀ j X) :
    ∃ T : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ),
      X ⊆ sitesOf T ∧ IsPolyDom m₀ K (sitesOf T) ∧ dExt T ≤ treeLenCovOne m₀ j X := by
  classical
  obtain ⟨𝒦, W, E, hch, hconn, hWX, hmeet, hcost⟩ :=
    treeLenCovOne_attained m₀ j X (SmallField.exists_cover_struct hX)
  have hac : cellSide L m₀ m₁ j ∣ cellSide L m₀ m₁ K :=
    pow_dvd_pow L (by omega)
  have hc0 := cellSide_pos (L := L) m₀ m₁ K
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have lift : ∀ q ∈ 𝒦, box q (L * cellSide L m₀ m₁ j) ⊆
      box (cbase (cellSide L m₀ m₁ K) q) (L * cellSide L m₀ m₁ K) := fun q hq =>
    box_subset_box_cbase_of_dvd hc0 hac hL1 (hch.1 q hq).1
  set Y : Set (CTorus d L N₁ m₁ K) :=
    ⋃ q ∈ 𝒦, box (cbase (cellSide L m₀ m₁ K) q) (L * cellSide L m₀ m₁ K) with hYdef
  have hbox : ∀ q ∈ 𝒦, box (cbase (cellSide L m₀ m₁ K) q) (L * cellSide L m₀ m₁ K) ⊆ Y :=
    fun q hq => Set.subset_iUnion₂ (s := fun q (_ : q ∈ 𝒦) =>
      box (cbase (cellSide L m₀ m₁ K) q) (L * cellSide L m₀ m₁ K)) q hq
  have hXY : X ⊆ Y := by
    intro z hz
    obtain ⟨q, hq, hzq⟩ := hch.2 z hz
    exact hbox q hq (lift q hq hzq)
  have hY1 : IsPiPrimeUnion m₀ K Y := by
    intro z hz
    obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.1 hz
    exact ⟨cbase (cellSide L m₀ m₁ K) q, aligned_cbase q, hzq, hbox q hq⟩
  have hYconn : SiteConnected Y := by
    intro z hz z' hz'
    obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.1 hz
    obtain ⟨q', hq', hzq'⟩ := Set.mem_iUnion₂.1 hz'
    obtain ⟨w, hwW, hwq⟩ := hmeet q hq
    obtain ⟨w', hwW', hwq'⟩ := hmeet q' hq'
    have h1 := siteConnected_box_aux _ _ z hzq w (lift q hq hwq)
    have h2 := hX.2.2 w (hWX hwW) w' (hWX hwW')
    have h3 := siteConnected_box_aux _ _ w' (lift q' hq' hwq') z' hzq'
    have h1' : Relation.ReflTransGen (fun u v => u ∈ Y ∧ v ∈ Y ∧ Nbr u v) z w :=
      Relation.ReflTransGen.mono (fun u v h => ⟨hbox q hq h.1, hbox q hq h.2.1, h.2.2⟩) z w h1
    have h2' : Relation.ReflTransGen (fun u v => u ∈ Y ∧ v ∈ Y ∧ Nbr u v) w w' :=
      Relation.ReflTransGen.mono (fun u v h => ⟨hXY h.1, hXY h.2.1, h.2.2⟩) w w' h2
    have h3' : Relation.ReflTransGen (fun u v => u ∈ Y ∧ v ∈ Y ∧ Nbr u v) w' z' :=
      Relation.ReflTransGen.mono (fun u v h => ⟨hbox q' hq' h.1, hbox q' hq' h.2.1, h.2.2⟩) w' z' h3
    exact h1'.trans (h2'.trans h3')
  obtain ⟨z0, hz0⟩ := hX.1
  have hch' : ChosenOne m₀ K Y ((fun q => cbase (cellSide L m₀ m₁ K) q) '' 𝒦) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact ⟨aligned_cbase q, hbox q hq⟩
    · intro z hz
      obtain ⟨q, hq, hzq⟩ := Set.mem_iUnion₂.1 hz
      exact ⟨_, ⟨q, hq, rfl⟩, hzq⟩
  have hpoly : IsPolyDom m₀ K Y := ⟨⟨z0, hXY hz0⟩, ⟨_, hch'⟩, hYconn⟩
  have hΩ : IsPiUnion (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ :=
    fun z _ => ⟨cbase (cellSide L m₀ m₁ K) z, aligned_cbase z, mem_box_cbase hc0 z,
      Set.subset_univ _⟩
  have hsites : sitesOf (blocksOf m₀ K Set.univ Y) = Y := by
    rw [sitesOf_blocksOf hN le_rfl hΩ hY1]; simp
  refine ⟨blocksOf m₀ K Set.univ Y, by rw [hsites]; exact hXY, by rw [hsites]; exact hpoly, ?_⟩
  rw [dExt_eq_sizeJ_of_isPolyDom (by rw [hsites]; exact hpoly), hsites]
  unfold sizeJ
  rw [← hcost]
  refine (treeLenCovOne_le_of_chosen hch' hconn (hWX.trans hXY) ?_).trans
    (bondCost_scaleW_mono hjK E)
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨w, hwW, hwq⟩ := hmeet q hq
  exact ⟨w, hwW, lift q hq hwq⟩

end Geometry

section Family

open Balaban.Multiscale Balaban.Background Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **Fibre sums of label weights.**  Let `T` be a set of cubes of the level `k + 1`, `Tof` a map of
the labels to sets of cubes such that the root of every label of the fibre of `T` lies in `sitesOf T`,
and `wt` nonnegative weights whose sum over the labels rooted at each site is at most `ρ`.  Then the
weights of the fibre of `T` add up to at most `|T| a^d ρ`, `a` the side of a cube. -/
theorem fibre_weight_le {ι : Type*} [DecidableEq ι] {m₀ : ℕ}
    (𝒯 : Finset ι) (Tof : ι → Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ))
    (rE : ι → CTorus d L N₁ m₁ (k + 1)) (wt : ι → ℝ) (hwt : ∀ τ, 0 ≤ wt τ) {ρ : ℝ}
    (hρ : ∀ x, ∑ τ ∈ 𝒯.filter (fun τ => rE τ = x), wt τ ≤ ρ)
    (T : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ))
    (hroot : ∀ τ ∈ 𝒯, Tof τ = T → rE τ ∈ sitesOf T) :
    ∑ τ ∈ 𝒯.filter (fun τ => Tof τ = T), wt τ ≤
      T.card * ((cellSide L m₀ m₁ (k + 1) : ℝ) ^ d * ρ) := by
  classical
  set R : Finset (CTorus d L N₁ m₁ (k + 1)) := Finset.univ.filter (fun x => x ∈ sitesOf T) with hR
  have hcardR : (R.card : ℝ) ≤ T.card * (cellSide L m₀ m₁ (k + 1) : ℝ) ^ d := by
    have hsub : R ⊆ T.biUnion (fun b => Finset.univ.filter
        (fun y : CTorus d L N₁ m₁ (k + 1) => y ∈ box b.1 (cellSide L m₀ m₁ (k + 1)))) := by
      intro x hx
      have hx' : x ∈ sitesOf T := (Finset.mem_filter.1 hx).2
      obtain ⟨b, hb, hxb⟩ := mem_sitesOf.1 hx'
      exact Finset.mem_biUnion.2 ⟨b, hb, by simpa using hxb⟩
    have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have h2 : ∑ b ∈ T, (Finset.univ.filter
        (fun y : CTorus d L N₁ m₁ (k + 1) => y ∈ box b.1 (cellSide L m₀ m₁ (k + 1)))).card ≤
        ∑ _b ∈ T, cellSide L m₀ m₁ (k + 1) ^ d :=
      Finset.sum_le_sum fun b _ => Balaban.Localization.card_box_le _ _
    have h3 : R.card ≤ T.card * cellSide L m₀ m₁ (k + 1) ^ d := by
      refine h1.trans (h2.trans (le_of_eq ?_))
      rw [Finset.sum_const, smul_eq_mul]
    exact_mod_cast h3
  have hρ0 : 0 ≤ ρ := (Finset.sum_nonneg fun τ _ => hwt τ).trans (hρ 0)
  have hmain := sum_le_card_mul_of_fibre (𝒯.filter (fun τ => Tof τ = T)) rE R wt wt
    (fun τ _ => hwt τ) (fun τ _ => le_rfl)
    (fun τ hτ hnot => absurd (by
      have := hroot τ (Finset.mem_filter.1 hτ).1 (Finset.mem_filter.1 hτ).2
      simpa [hR] using this) hnot)
    (ρ := ρ) (fun x => le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun τ hτ => by
      simp only [Finset.mem_filter] at hτ ⊢
      exact ⟨hτ.1.1, hτ.2⟩) (fun τ _ _ => hwt τ)) (hρ x))
  calc _ ≤ R.card * ρ := hmain
    _ ≤ (T.card * (cellSide L m₀ m₁ (k + 1) : ℝ) ^ d) * ρ := mul_le_mul_of_nonneg_right hcardR hρ0
    _ = _ := by ring

variable (S : StepSetting d L N₁ m₁ k N ϱ)

open Classical in
/-- **The inherited energy of a class member as a coefficient family over cube sets.**  Let `𝒯E` be a
finite set of labels `τ = (j, y, X)` of the old energy of `C` (for instance the label set of
`mem_classLabels_E_iff`), with the label term `β⁻¹ ℰ^{(j)}(y, X; Ψ, h)` analytic and bounded by
`β⁻¹ E₀ exp(-(κ_dec - 1) d_j(X))` on the chart `Ξ^c(𝔹_j(X); a, ν, σ, ε)` (`hchart`), and let the
chart of the parameter space lie in it (`hV`).  Each label is assigned the cube set `Tof τ` of
`exists_cubeSet_of_isPolyDom`, and the family is
`c θ T = ∑_{τ : Tof τ = T} β⁻¹ ℰ^{(j)}(y, X; θ)`.  Then:

* the sites of `Tof τ` contain `X`, form a polymer of the level `k + 1`, and `d_Ω(Tof τ) ≤ d_j(X)`;
* `c · T` is analytic on `physV` (`han`);
* `c θ T` depends only on the restriction of `θ` to `sitesOf T` (`hloc`; the term clause `localE` is
  exact on `X`, so no background agreement is needed);
* `‖c θ T‖ ≤ B exp(-(κ - 1) d_Ω(T))` with `B = c₁ a^d ρE`, `a` the side of a cube of the level
  `k + 1` (`hbd`; the hypothesis `hρE` is the per-site summability of the label bounds with the rate
  `κ₁`, and `κ + κ₁ ≤ κ_dec - 1`);
* `c θ T ≠ 0` only for polymers `sitesOf T` (`hsupp`);
* the sum over `T` is the sum of the label terms. -/
theorem exists_oldEnergyCoeffFamily {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hN : L ^ C.m₀ ∣ N₁) (hm : P.m₀ = C.m₀)
    (hcl : SFTermClauses P Dom C.Tm) {β : ℝ} (hβ : 0 < β) {κdec : ℝ} (hκdec : κdec - 1 ≤ P.κ)
    (hE₀ : 0 ≤ P.E₀) (a : ℕ → ℝ) (ν σ ε : ℝ)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : ∀ τ ∈ 𝒯E, (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    (hchart : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (C.Tm.gs τ.1 τ.2.2) a ν τ.1 σ ε,
      Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2) r.1 r.2)
    {a₁ ν₁ eps : ℝ}
    (hV : ∀ τ ∈ 𝒯E, ∀ θ ∈ physV S a₁ ν₁ eps,
      (physIncl N S θ).1 ∈ XiCRaw (C.Tm.gs τ.1 τ.2.2) a ν τ.1 σ ε)
    {κ κ₁ : ℝ} (hκ : 0 ≤ κ) (hrate : κ + κ₁ ≤ κdec - 1) {ρE : ℝ}
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => τ.2.1 = x),
      β⁻¹ * P.E₀ * Real.exp (-κ₁ * treeLenCovOne C.m₀ τ.1 τ.2.2) ≤ ρE) :
    ∃ (Tof : ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1)) →
        Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) C.m₀ (k + 1) Set.univ))
      (c : physParam N S →
        Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) C.m₀ (k + 1) Set.univ) → ℂ),
      (∀ τ ∈ 𝒯E, τ.2.2 ⊆ sitesOf (Tof τ) ∧ IsPolyDom C.m₀ (k + 1) (sitesOf (Tof τ)) ∧
        dExt (Tof τ) ≤ treeLenCovOne C.m₀ τ.1 τ.2.2) ∧
      (∀ θ T, c θ T = ∑ τ ∈ 𝒯E.filter (fun τ => Tof τ = T),
        (β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2 (physIncl N S θ).1.1 (physIncl N S θ).1.2) ∧
      (∀ T, AnalyticOnNhd ℂ (fun θ => c θ T) (physV S a₁ ν₁ eps)) ∧
      (∀ T, ∀ θ ∈ physV S a₁ ν₁ eps, ∀ θ' ∈ physV S a₁ ν₁ eps,
        physRestrict (sitesOf T) (physIncl N S θ) = physRestrict (sitesOf T) (physIncl N S θ') →
          c θ T = c θ' T) ∧
      0 ≤ c1 d L * ((cellSide L C.m₀ m₁ (k + 1) : ℝ) ^ d * ρE) ∧
      (∀ θ ∈ physV S a₁ ν₁ eps, ∀ T, IsPolyDom C.m₀ (k + 1) (sitesOf T) →
        ‖c θ T‖ ≤ c1 d L * ((cellSide L C.m₀ m₁ (k + 1) : ℝ) ^ d * ρE) *
          Real.exp (-(κ - 1) * dExt T)) ∧
      (∀ θ ∈ physV S a₁ ν₁ eps, ∀ T, c θ T ≠ 0 → IsPolyDom C.m₀ (k + 1) (sitesOf T)) ∧
      (∀ θ, ∑ T, c θ T = ∑ τ ∈ 𝒯E,
        (β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2 (physIncl N S θ).1.1 (physIncl N S θ).1.2) := by
  have hAB := classOldEnergy_analytic_bound C hm hcl hβ hκdec hE₀ a ν σ ε 𝒯E h𝒯 hchart
  have hex : ∀ τ ∈ 𝒯E, ∃ T : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) C.m₀
      (k + 1) Set.univ), τ.2.2 ⊆ sitesOf T ∧ IsPolyDom C.m₀ (k + 1) (sitesOf T) ∧
      dExt T ≤ treeLenCovOne C.m₀ τ.1 τ.2.2 := fun τ hτ =>
    exists_cubeSet_of_isPolyDom hN (by have := (h𝒯 τ hτ).1.2; omega) (h𝒯 τ hτ).2.1
  choose! Tof hTof using hex
  have hroot : ∀ T, ∀ τ ∈ 𝒯E, Tof τ = T → τ.2.1 ∈ sitesOf T := fun T τ hτ hT =>
    hT ▸ (hTof τ hτ).1 (h𝒯 τ hτ).2.2
  have hρ0 : 0 ≤ ρE := (Finset.sum_nonneg fun τ _ => by positivity).trans (hρE 0)
  have hB : 0 ≤ c1 d L * ((cellSide L C.m₀ m₁ (k + 1) : ℝ) ^ d * ρE) := by
    have := one_le_c1 d L
    positivity
  refine ⟨Tof, fun θ T => ∑ τ ∈ 𝒯E.filter (fun τ => Tof τ = T),
    (β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2 (physIncl N S θ).1.1 (physIncl N S θ).1.2, hTof,
    fun _ _ => rfl, ?_, ?_, hB, ?_, ?_, ?_⟩
  · intro T
    refine Finset.analyticOnNhd_fun_sum _ fun τ hτ => ?_
    have hτ' := (Finset.mem_filter.1 hτ).1
    exact (hAB.1 τ hτ').comp (f := fun θ => (physIncl N S θ).1)
      (fun θ _ => ((ContinuousLinearMap.fst ℂ _ _).comp (physIncl N S)).analyticAt θ)
      (fun θ hθ => hV τ hτ' θ hθ)
  · intro T θ _ θ' _ hrest
    refine Finset.sum_congr rfl fun τ hτ => ?_
    obtain ⟨hτ', hT⟩ := Finset.mem_filter.1 hτ
    congr 1
    refine hcl.localE τ.1 τ.2.1 τ.2.2 _ _ _ _ fun x hx => ?_
    have := physRestrict_eq_apply hrest x (hT ▸ (hTof τ hτ').1 hx)
    exact ⟨this.1, this.2.1⟩
  · intro θ hθ T _
    have hfib : ∀ τ ∈ 𝒯E.filter (fun τ => Tof τ = T),
        ‖(β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2 (physIncl N S θ).1.1 (physIncl N S θ).1.2‖ ≤
          β⁻¹ * P.E₀ * Real.exp (-κ₁ * treeLenCovOne C.m₀ τ.1 τ.2.2) *
            Real.exp (-κ * dExt T) := by
      intro τ hτ
      obtain ⟨hτ', hT⟩ := Finset.mem_filter.1 hτ
      refine (hAB.2 τ hτ' _ (hV τ hτ' θ hθ)).trans ?_
      have hd := treeLenCovOne_nonneg (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
        C.m₀ τ.1 τ.2.2
      have hle : dExt T ≤ treeLenCovOne C.m₀ τ.1 τ.2.2 := hT ▸ (hTof τ hτ').2.2
      have hexp : Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2) ≤
          Real.exp (-κ₁ * treeLenCovOne C.m₀ τ.1 τ.2.2) * Real.exp (-κ * dExt T) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        nlinarith [mul_le_mul_of_nonneg_left hle hκ, mul_le_mul_of_nonneg_right hrate hd]
      calc β⁻¹ * P.E₀ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2) ≤
          β⁻¹ * P.E₀ * (Real.exp (-κ₁ * treeLenCovOne C.m₀ τ.1 τ.2.2) *
            Real.exp (-κ * dExt T)) := mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = β⁻¹ * P.E₀ * Real.exp (-κ₁ * treeLenCovOne C.m₀ τ.1 τ.2.2) *
            Real.exp (-κ * dExt T) := by ring
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hfib).trans ?_)
    rw [← Finset.sum_mul]
    have hw := fibre_weight_le 𝒯E Tof (fun τ => τ.2.1)
      (fun τ => β⁻¹ * P.E₀ * Real.exp (-κ₁ * treeLenCovOne C.m₀ τ.1 τ.2.2))
      (fun τ => by positivity) hρE T (hroot T)
    have hcard := card_le_dExt (m₀ := C.m₀) (j := k + 1) (Ω := Set.univ) hN le_rfl T
    have hu := dExt_nonneg T
    have h1 : (T.card : ℝ) ≤ c1 d L * Real.exp (dExt T) :=
      hcard.trans (mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (dExt T)])
        (by have := one_le_c1 d L; linarith))
    have hcs : 0 ≤ (cellSide L C.m₀ m₁ (k + 1) : ℝ) ^ d * ρE := by positivity
    calc _ ≤ ((T.card : ℝ) * ((cellSide L C.m₀ m₁ (k + 1) : ℝ) ^ d * ρE)) *
          Real.exp (-κ * dExt T) :=
          mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
      _ ≤ (c1 d L * Real.exp (dExt T) * ((cellSide L C.m₀ m₁ (k + 1) : ℝ) ^ d * ρE)) *
          Real.exp (-κ * dExt T) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hcs) (Real.exp_pos _).le
      _ = _ := by
          rw [show -(κ - 1) * dExt T = dExt T + -κ * dExt T by ring, Real.exp_add]; ring
  · intro θ _ T hT
    by_contra hne
    apply hT
    refine Finset.sum_eq_zero fun τ hτ => ?_
    obtain ⟨hτ', hTτ⟩ := Finset.mem_filter.1 hτ
    exact absurd (hTτ ▸ (hTof τ hτ').2.1) hne
  · intro θ
    exact Finset.sum_fiberwise_of_maps_to (g := Tof) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _) _

open Classical in
/-- **The per-site summability `hρE` of the old-energy labels, from the entropy bound.**  For
`κ₁ ≥ a_ent + 1` and `L ^ m₀ ∣ N₁` the sum over the labels rooted at a site of
`β⁻¹ E₀ exp(-κ₁ d_j(X))` is at most `k β⁻¹ E₀ K₀`. -/
theorem oldEnergy_siteSum_le {P : Consts} (C : StepClass d L N₁ m₁ k N ϱ) (hN : L ^ C.m₀ ∣ N₁)
    {β : ℝ} (hβ : 0 < β) (hE₀ : 0 ≤ P.E₀) {κ₁ : ℝ} (hκ₁ : aEnt d L + 1 ≤ κ₁)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : ∀ τ ∈ 𝒯E, (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    (x : CTorus d L N₁ m₁ (k + 1)) :
    ∑ τ ∈ 𝒯E.filter (fun τ => τ.2.1 = x),
      β⁻¹ * P.E₀ * Real.exp (-κ₁ * treeLenCovOne C.m₀ τ.1 τ.2.2) ≤
      (k : ℝ) * (β⁻¹ * P.E₀ * K0 d L κ₁) :=
  classE_siteSum_le_const hN hκ₁ (Nat.le_succ k) 𝒯E h𝒯 (fun _ => β⁻¹ * P.E₀)
    (by positivity) (fun _ _ => le_rfl) x

open Classical in
/-- **The inherited energy of a class member at the renormalized datum is a localized expansion.**
The family of `exists_oldEnergyCoeffFamily` evaluated at the renormalized datum
`((1 + ζ(ξ)) Ψ, h)` (the fixed source `g₀` plays no role in the label terms) is an expansion
`IsLocExp` on every cover `Ys'` containing the site sets of all cube sets, with the rate `κ - 1`
and the bound `c₁ a^d ρE`.  This is the hypothesis `hOE` of `renormExpInputOn_class_of_fields`
for the old-energy functions `fE z D ξ = ∑_τ β⁻¹ ℰ^{(j)}(y, X; datum)` of a set `𝒯E` of labels. -/
theorem exists_locExp_renTheta_oldEnergy {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hN : L ^ C.m₀ ∣ N₁) (hm : P.m₀ = C.m₀)
    (hcl : SFTermClauses P Dom C.Tm) {β : ℝ} (hβ : 0 < β) {κdec : ℝ} (hκdec : κdec - 1 ≤ P.κ)
    (hE₀ : 0 ≤ P.E₀) (a : ℕ → ℝ) (ν σ ε : ℝ)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : ∀ τ ∈ 𝒯E, (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    (hchart : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (C.Tm.gs τ.1 τ.2.2) a ν τ.1 σ ε,
      Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2) r.1 r.2)
    {a₁ ν₁ eps : ℝ}
    (hV : ∀ τ ∈ 𝒯E, ∀ θ ∈ physV S a₁ ν₁ eps,
      (physIncl N S θ).1 ∈ XiCRaw (C.Tm.gs τ.1 τ.2.2) a ν τ.1 σ ε)
    {κ κ₁ : ℝ} (hκ : 0 ≤ κ) (hrate : κ + κ₁ ≤ κdec - 1) {ρE : ℝ}
    (hρE : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ τ ∈ 𝒯E.filter (fun τ => τ.2.1 = x),
      β⁻¹ * P.E₀ * Real.exp (-κ₁ * treeLenCovOne C.m₀ τ.1 τ.2.2) ≤ ρE)
    (εren : ℝ) (Dom' : BgData S.G' N → Prop) {r : ℝ}
    (g₀ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (hg₀ : g₀ ∈ l1Ball d L N₁ m₁ (k + 1) N)
    (hchart' : ∀ D, Dom' D → ∀ ξ : Fin 3 → ℂ, ‖ξ‖ < r →
      XiCData S.G' (compWeight L a₁) ν₁ (k + 1) 1 eps (renThetaDatum S εren D ξ))
    (Pr : RawData d L (N₁ * L ^ m₁) (k + 1) N →L[ℂ] ↥(rawSub N S.G'))
    (hPr : ∀ p : ↥(rawSub N S.G'), Pr p = p)
    {Ys' : Finset (Finset (CTorus d L N₁ m₁ (k + 1)))}
    (hYs : (Finset.univ.image fun T : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
        C.m₀ (k + 1) Set.univ) =>
        (Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => x ∈ sitesOf T)) ⊆ Ys') :
    ∃ term, IsLocExp S.G' Dom' r Ys' (renDY S.G' C.m₀) (κ - 1)
      (c1 d L * ((cellSide L C.m₀ m₁ (k + 1) : ℝ) ^ d * ρE))
      (fun D ξ => ∑ τ ∈ 𝒯E, (β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2
        (rawOf (renThetaDatum S εren D ξ)).1 (rawOf (renThetaDatum S εren D ξ)).2) term := by
  obtain ⟨Tof, c, -, hc, han, hloc, hB, hbd, hsupp, hsum⟩ :=
    exists_oldEnergyCoeffFamily S C hN hm hcl hβ hκdec hE₀ a ν σ ε 𝒯E h𝒯 hchart hV hκ hrate hρE
  obtain ⟨term, h⟩ := exists_locExp_renTheta_of_coeffFamily S hN εren Dom' hB c han hloc hbd hsupp
    g₀ hg₀ hchart' Pr hPr hYs
  have hf : (fun (D : BgData S.G' N) (ξ : Fin 3 → ℂ) => ∑ τ ∈ 𝒯E, (β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2
        (rawOf (renThetaDatum S εren D ξ)).1 (rawOf (renThetaDatum S εren D ξ)).2) =
      fun D ξ => ∑ T : Finset (CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) C.m₀ (k + 1)
        Set.univ), c (⟨rawOf (renThetaDatum S εren D ξ), rawOf_mem_rawSub _⟩, g₀) T := by
    funext D ξ
    exact (hsum (⟨rawOf (renThetaDatum S εren D ξ), rawOf_mem_rawSub _⟩, g₀)).symm
  rw [hf]
  exact ⟨term, h⟩

open Classical in
/-- **The sum of the label terms of the whole label set is the old energy.**  For the label set of
`mem_classLabels_E_iff`, `∑_τ β⁻¹ ℰ^{(j)}(y, X; Ψ, h) = β⁻¹ ∑_{j=1}^k ℰ^{(j)}(Ψ, h)`; with
`exists_oldEnergyCoeffFamily` this gives `∑_T c θ T = β⁻¹ ∑_{j ≤ k} ℰ^{(j)}` at the datum of `θ`. -/
theorem sum_labels_eq_Edens (C : StepClass d L N₁ m₁ k N ϱ) (β : ℝ)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
    (Ψ h : Fld d L N₁ m₁ (k + 1) N) :
    ∑ τ ∈ 𝒯E, (β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2 Ψ h =
      (β : ℂ)⁻¹ * ∑ j ∈ Finset.Icc 1 k, Edens C.m₀ C.Tm j Ψ h := by
  subst h𝒯
  rw [← Finset.mul_sum]
  exact congrArg _ (sum_classLabels_E_eq_Edens C.m₀ C.Tm (fun _ => Ψ) (fun _ => h))

end Family

end Balaban.Fluctuation
