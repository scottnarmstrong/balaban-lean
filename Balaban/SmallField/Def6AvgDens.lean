/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgLimit
public import Balaban.SmallField.Def6AvgFamily

/-!
# Reynolds averaging: the thermodynamic limit of the density at a centre, and translation invariance
at constant data

* `polysAt_eq_image`, `Eloc_eq_finsum`: the density of a torus at a point is the sum over the shapes
  through the block of the point;
* `XiAll`, `tendsto_Eloc`: for data that pull back into the analyticity domains of every polymer of
  every torus, `ℰ_n(y; ψ, h) → ℰ_∞(y; ψ, h)` along the tori (CLASS-RULINGS Q-C (2), values);
* `xiAll_const`, `ElocInf_const_translate`: at constant data near `e_{i₀}` the infinite-volume density
  does not depend on the centre (H.3-E passed to the limit).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **The polymers of `𝒟_j` through a torus point are the lifts of the shapes through its block.** -/
theorem polysAt_eq_image {m₀ j : ℕ} (hjk : j ≤ k) (hN : L ^ m₀ ∣ N₁)
    (z : CTorus d L N₁ m₁ k) :
    polysAt m₀ j z = (fun X' => Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') ''
      {X' : Finset (Site d) | unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z ∈ X' ∧
        NonWind L N₁ m₁ k j X' ∧
        IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')} := by
  ext Y
  constructor
  · rintro ⟨hY, hz⟩
    set X' : Finset (Fin d → ℤ) := (Finset.univ.filter (fun y => y ∈ Y)).image
      (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j) with hX'
    have hmem : ∀ w, w ∈ X' ↔ ∃ y₀ ∈ Y, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y₀ = w := by
      intro w; simp [hX']
    have hYeq : Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' = Y := by
      ext w
      constructor
      · intro hw
        obtain ⟨y₀, hy₀, hyz⟩ := (hmem _).1 hw
        refine IsPolyDom.block_closed hjk hN hY hy₀ ?_
        funext μ
        have := congrFun hyz μ
        simp only [unlift] at this
        exact ZMod.valMinAbs_inj.1 (by exact_mod_cast this)
      · intro hw
        exact (hmem _).2 ⟨w, hw, rfl⟩
    refine ⟨X', ⟨?_, ?_, ?_⟩, hYeq⟩
    · exact (hmem _).2 ⟨z, hz, rfl⟩
    · intro w hw μ
      obtain ⟨y₀, -, rfl⟩ := (hmem _).1 hw
      have : NeZero (N₁ * L ^ m₁ * L ^ (k - j)) := ⟨by
        have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
      simp only [unlift]
      rw [ZMod.coe_valMinAbs]
    · rw [hYeq]; exact hY
  · rintro ⟨X', ⟨hz, -, hX⟩, rfl⟩
    exact ⟨hX, hz⟩

open Classical in
/-- **`Eloc` at a point as a sum over the shapes through its block.** -/
theorem Eloc_eq_finsum {m₀ j : ℕ} (hjk : j ≤ k) (hN : L ^ m₀ ∣ N₁) (Tm : Terms d L N₁ m₁ k N ϱ)
    (z : CTorus d L N₁ m₁ k) (ψ h : Fld d L N₁ m₁ k N) :
    Eloc m₀ Tm j z ψ h =
      ∑ᶠ X' ∈ {X' : Finset (Site d) | unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z ∈ X' ∧
        NonWind L N₁ m₁ k j X' ∧
        IsPolyDom (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')},
        Tm.E j z (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') ψ h := by
  unfold Eloc
  rw [polysAt_eq_image hjk hN z]
  rw [finsum_mem_image (g := fun X' => Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
    (f := fun Y => Tm.E j z Y ψ h)]
  intro A hA B hB h
  exact ypoly_injOn_nonWind hjk hA.2.1 hB.2.1 h

section V

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ} {ψ h : InfFld d N}

variable (P β ν a Tm j) in
/-- The data `(ψ, h)` of `ℤ^d` pull back into the analyticity domain of every polymer of `𝒟_j`
on every torus of the sequence. -/
def XiAll (ψ h : InfFld d N) : Prop :=
  ∀ n : ℕ, ∀ Y : Set (CTorus d L (torusSeq L P.m₀ n) m₁ k),
    IsPolyDom (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P.m₀ j Y →
      XiDom ((Tm (torusSeq L P.m₀ n)).gs j Y) (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j
        (P.eps d L j) (pullFld j ψ) (pullFld j h)

theorem XiAll.extAll (hD : XiAll P β ν a Tm j ψ h) {X' : Finset (Site d)} :
    ExtAll P β ν a Tm j X' ψ h := fun n hn =>
  ⟨pullFld j ψ, pullFld j h, fun _ _ => ⟨rfl, rfl⟩, hD n _ hn.2⟩

theorem eventually_unlift_blockPt (hjk : j ≤ k) (m₀ : ℕ) (y : Site d) :
    ∀ᶠ n in atTop, unlift (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) j
      (blockPt j y) = y := by
  filter_upwards [eventually_nonWind (L := L) (m₁ := m₁) (k := k) m₀ j ({y} : Finset (Site d))]
    with n hn
  have : blockPt (L := L) (N₁ := torusSeq L m₀ n) (m₁ := m₁) (k := k) j y = ibase j y := by
    funext μ; simp only [blockPt, ibase]; congr 1; ring
  rw [this]
  exact unlift_ibase hjk (hn y (Finset.mem_singleton_self y))

open Classical in
/-- **The thermodynamic limit of the density at a centre** (CLASS-RULINGS Q-C (2), values): for data
that pull back into the analyticity domains, `ℰ^{(j)}_n(y; ψ, h) → ℰ_∞^{(j)}(y; ψ, h)` along the
tori of the sequence. -/
theorem tendsto_Eloc (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P) (y : Site d)
    (hD : XiAll P β ν a Tm j ψ h) :
    Tendsto (fun n => Eloc P.m₀ (Tm (torusSeq L P.m₀ n)) j (blockPt j y) (pullFld j ψ) (pullFld j h))
      atTop (nhds (ElocInf P.m₀ Tm j y ψ h)) := by
  have hE0 := hF.admissible.E₀_nonneg
  have hlim := tendsto_shapeSum (m₀ := P.m₀) (j := j) (L := L) (m₁ := m₁) (k := k) hn.hjk
    (κ := P.κ) (by linarith [hn.hκ, aEnt_nonneg d L]) y
    (fun n X' => (Tm (torusSeq L P.m₀ n)).E j (blockPt j y) (Ypoly j X') (pullFld j ψ) (pullFld j h))
    (fun X' => ElocInfTerm P Tm j y ψ h X') hE0 ?_ ?_ ?_ ?_
  · rw [← ElocInf_eq_tsum] at hlim
    refine hlim.congr' ?_
    filter_upwards [eventually_unlift_blockPt (L := L) (m₁ := m₁) hn.hjk P.m₀ y] with n hn'
    rw [Eloc_eq_finsum hn.hjk (torusSeq_dvd P.m₀ n)]
    congr 1
    ext X'
    simp only [ShAt, mem_ofPred_eq, hn', GoodAt]
  · intro n X' hy hgood hsz
    have hX := infPoly_of_small hn.hjk hy hgood hsz
    unfold ElocInfTerm
    rw [ite_eq_left ⟨hX, hy⟩]
    exact (Einf_eq_torus hF.torusIndep hn.hj1 hn.hjk hy hX ψ h (torusSeq L P.m₀ n) hgood.1 hgood.2).symm
  · intro n X' hy hgood
    have hsf := hF.torus (torusSeq L P.m₀ n)
    exact hsf.boundE j hn.hj1 hn.hjk _ _ hgood.2 (blockPt_mem_Ypoly hn.hjk hgood.1 hy) _ _
      (hD n _ hgood.2)
  · intro X' hy hX
    unfold ElocInfTerm
    rw [ite_eq_left ⟨hX, hy⟩]
    exact Einf_norm_le_dom hF hn.hj1 hn.hjk hX hy hD.extAll
  · intro X' hX
    unfold ElocInfTerm
    rw [ite_eq_right (fun h' => hX ⟨h'.2, h'.1⟩)]

end V

section TI

variable {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ} {ρ : ℝ}

/-- **Constant data lie in the analyticity domain** (the generalization of `LiftCtx.xiDom_const` to
a constant `h = w`). -/
theorem LiftCtx.xiDom_constw {N₁ : ℕ} [NeZero N₁] {Tm : Terms d L N₁ m₁ k N ϱ}
    {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    {Ek : ℝ} (ctx : LiftCtx P β ν a Tm ρd Ek j ρ)
    (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (hΩ : ∀ i, j < i → G.Ω i = ∅) (i₀ : Fin N)
    (v w : Fin N → ℂ) (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ)
    (hw : ∀ i, nuIdeal L k (ν k) j * ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) :
    XiDom G (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j (P.eps d L j)
      (constFld v) (constFld w) := by
  obtain ⟨δ, hδ0, hδ1, hδ2, hδ3, hδ4⟩ := ctx.radius
  have hN : (0 : ℝ) ≤ N * rotB N := by unfold rotB; positivity
  have hρ0 := ctx.rho_pos
  refine xiDom_of_close ctx.bg hΩ ctx.jk i₀ hδ0 hδ1 hδ2 hρ0 (by nlinarith) hδ3
    (constFld v) w (fun x i => hv i) (fun _ _ _ => rfl) (fun i => ?_)
  have hm := bgMass_mul_le_nuIdeal (L := L) (k := k) (βk := β k) ctx.nu_pos.le ctx.jk
  exact (mul_le_mul_of_nonneg_right hm (norm_nonneg _)).trans (hw i)

variable (hF : IsSFFamily P β ν a Tm ρd Ek) (hn : MomNum d L N k j ϱ P)
include hF hn

/-- Constant data pull back into the analyticity domain of every polymer on every torus. -/
theorem xiAll_const (i₀ : Fin N) (v w : Fin N → ℂ)
    (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ liftRadius d L N P j)
    (hw : ∀ i, nuIdeal L k (ν k) j * ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤
      liftRadius d L N P j) :
    XiAll P β ν a Tm j (constInf v) (constInf w) := by
  intro n Y hY
  have ctx := hF.ctxSeq hn i₀ n
  exact ctx.xiDom_constw _ ((hF.torus (torusSeq L P.m₀ n)).gs_spec j hn.hj1 hn.hjk Y hY).2 i₀ v w hv hw

/-- **Translation invariance of the density at constant data** (CLASS-RULINGS Q-A, (H.3-E) passed
to the limit): for constant data near `e_{i₀}`, `ℰ_∞^{(j)}(y; v, w)` does not depend on the centre
`y ∈ ℤ^d`.  From the covariance `eucEloc` of the density of every torus under the translations
of the level-`j` lattice and the thermodynamic limit `tendsto_Eloc`. -/
theorem ElocInf_const_translate (i₀ : Fin N) (v w : Fin N → ℂ)
    (hv : ∀ i, ‖v i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ liftRadius d L N P j)
    (hw : ∀ i, nuIdeal L k (ν k) j * ‖w i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤
      liftRadius d L N P j) (y : Site d) :
    ElocInf P.m₀ Tm j y (constInf v) (constInf w) = ElocInf P.m₀ Tm j 0 (constInf v) (constInf w) := by
  have hD := xiAll_const hF hn i₀ v w hv hw
  have h1 := tendsto_Eloc hF hn y hD
  have h0 := tendsto_Eloc hF hn 0 hD
  refine tendsto_nhds_unique h1 (h0.congr fun n => ?_)
  have hjk := hn.hjk
  have ctx := hF.ctxSeq hn i₀ n
  have hsf := hF.torus (torusSeq L P.m₀ n)
  have hbp : blockPt (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j y = ibase j y := by
    funext μ; simp only [blockPt, ibase]; congr 1; ring
  have hal : Aligned (L ^ j) (blockPt (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j y) := by
    rw [hbp]; exact ibase_aligned hjk y
  have hr := mem_fullJSymGroup_addRight_neg (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k)
    (j := j) hal
  have hlev : ∀ i, j < i →
      (levelGS (d := d) (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (ϱ := ϱ) j hjk).Ω i = ∅ := by
    intro i hi
    simp [levelGS, not_le.2 hi]
  have X1 := ctx.xiDom_constw _ hlev i₀ v w hv hw
  have key := hsf.eucEloc j hn.hj1 hjk (blockPt j y) _ hr (constFld v) (constFld w) X1 X1
  have hry : (Equiv.addRight (-blockPt (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j y) :
      Equiv.Perm (CTorus d L (torusSeq L P.m₀ n) m₁ k)) (blockPt j y) = 0 := by
    simp
  rw [hry, blockBase_zero] at key
  have e0 : pullFld (d := d) (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (constInf v) =
      constFld v := rfl
  have e1 : pullFld (d := d) (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j (constInf w) =
      constFld w := rfl
  rw [e0, e1, blockPt_zero]
  exact key

end TI

end Balaban.SmallField.Def6
