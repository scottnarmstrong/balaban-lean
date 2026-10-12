/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgDens
public import Balaban.SmallField.Def6InfExpand

/-!
# Reynolds averaging: the second moment of a torus around an arbitrary centre

The centre-`y` versions of `LiftCtx.D2_Eloc_translate`, `LiftCtx.momentSum_eq` and
`LiftCtx.momentSum_shapes` (`Def6InfCov`, `Def6InfExpand`):

* `LiftCtx.D2_Eloc_translate'`: `∂_u ∂_v ℰ(y) = ∂_{u-y} ∂_{v-y} ℰ(0)` at the constant field;
* `LiftCtx.momentSum_eq_centre`: `momentSum = ∑_{u,v} ∂_u ∂_v ℰ(y) |u - v|²`;
* `LiftCtx.momentSum_shapes_centre`: `momentSum = ∑_{X' ∋ y} ∑_{x,x' ∈ X'} B_{X'}(x,x') |x - x'|²`
  with the tensor `B_{X'} = tensB` of the centre-`y` class term `EauxC`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

section Torus

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

/-- **Translation covariance of the second derivative of the density, general pair of
directions**: `∂_u ∂_v ℰ(y) = ∂_{u-y} ∂_{v-y} ℰ(0)` at the constant field. -/
theorem LiftCtx.D2_Eloc_translate' (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ i₁ : Fin N)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y) (x v : CTorus d L N₁ m₁ k) :
    D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀))
        (eFld d L N₁ m₁ k N i₀) (blockDir L j x i₁) (blockDir L j v i₁) =
      D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j 0 ψ (eFld d L N₁ m₁ k N i₀))
        (eFld d L N₁ m₁ k N i₀) (blockDir L j (x - y) i₁) (blockDir L j (v - y) i₁) := by
  have hjk := ctx.jk
  have hr := mem_fullJSymGroup_addRight_neg (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hy
  have hlev : ∀ i, j < i →
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk).Ω i = ∅ := by
    intro i hi
    simp [levelGS, not_le.2 hi]
  refine D2_congr_slice (ctx.analyticAt_Eloc i₀ y) (ctx.analyticAt_Eloc i₀ 0)
    (δ := ρ / 2) (by linarith [ctx.rho_pos]) fun s t hs ht => ?_
  have hst : ‖s‖ + ‖t‖ ≤ ρ := by linarith
  have X1 := ctx.xiDom_const (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk) hlev i₀
    (eFld d L N₁ m₁ k N i₀ + s • blockDir L j x i₁ + t • blockDir L j v i₁)
    (fun z i => (slice_dev x v i₁ i₀ s t z i).trans hst) (fun z z' h => slice_jBlock hjk x v i₁ i₀ s t h)
  have X2 := ctx.xiDom_const (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk) hlev i₀
    (eFld d L N₁ m₁ k N i₀ + s • blockDir L j (x - y) i₁ + t • blockDir L j (v - y) i₁)
    (fun z i => (slice_dev (x - y) (v - y) i₁ i₀ s t z i).trans hst)
    (fun z z' h => slice_jBlock hjk (x - y) (v - y) i₁ i₀ s t h)
  set r : Equiv.Perm (CTorus d L N₁ m₁ k) := Equiv.addRight (-y) with hrdef
  have e1 := actField_addRight_neg_blockDir (N := N) hjk hy x i₁
  have e2 := actField_addRight_neg_blockDir (N := N) hjk hy v i₁
  have hact : actField (N := N) r (eFld d L N₁ m₁ k N i₀ + s • blockDir L j x i₁ +
      t • blockDir L j v i₁) = eFld d L N₁ m₁ k N i₀ + s • blockDir L j (x - y) i₁ +
        t • blockDir L j (v - y) i₁ := by
    funext z i'
    have h1 := congrFun (congrFun e1 z) i'
    have h2 := congrFun (congrFun e2 z) i'
    simp only [actField, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eFld, constFld] at h1 h2 ⊢
    rw [h1, h2]
  have hc0 : actField (N := N) r (eFld d L N₁ m₁ k N i₀) = eFld d L N₁ m₁ k N i₀ := rfl
  have key := ctx.sf.eucEloc j ctx.j1 hjk y r hr
    (eFld d L N₁ m₁ k N i₀ + s • blockDir L j x i₁ + t • blockDir L j v i₁)
    (eFld d L N₁ m₁ k N i₀) X1 (by rw [hact, hc0]; exact X2)
  rw [hact, hc0] at key
  have hry : r y = 0 := by
    funext μ; simp [hrdef]
  rw [hry, blockBase_zero] at key
  exact key.symm

open Classical in
/-- **The second-moment sum of the torus in terms of the density at an aligned centre**
(CLASS-RULINGS Q-B (1)): `momentSum = ∑_{u,v} ∂_u∂_v ℰ(y) |u - v|²`. -/
theorem LiftCtx.momentSum_eq_centre (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ i₁ : Fin N)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y) :
    momentSum P.m₀ Tm j i₀ i₁ =
      ∑ u ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        ∑ v ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
          D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j y ψ (eFld d L N₁ m₁ k N i₀))
            (eFld d L N₁ m₁ k N i₀) (blockDir L j u i₁) (blockDir L j v i₁) *
            (liftSq L j (u - v) : ℂ) := by
  set Λ : Finset (CTorus d L N₁ m₁ k) :=
    (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)) with hΛ
  have hjk := ctx.jk
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k := by
    rw [side_eq hjk]; exact dvd_mul_right _ _
  have hmem : ∀ x, x ∈ Λ ↔ Aligned (L ^ j) x := by intro x; simp [hΛ]
  have hneg : ∀ x ∈ Λ, -x ∈ Λ := fun x hx => (hmem _).2 (aligned_neg hdvd ((hmem _).1 hx))
  have hsub : ∀ x z, x ∈ Λ → z ∈ Λ → x - z ∈ Λ := fun x z hx hz => (hmem _).2 (by
    rw [sub_eq_add_neg]
    exact aligned_add hdvd ((hmem _).1 hx) (aligned_neg hdvd ((hmem _).1 hz)))
  have hadd : ∀ x z, x ∈ Λ → z ∈ Λ → x + z ∈ Λ := fun x z hx hz => (hmem _).2
    (aligned_add hdvd ((hmem _).1 hx) ((hmem _).1 hz))
  have hyΛ : y ∈ Λ := (hmem _).2 hy
  rw [ctx.momentSum_eq i₀ i₁]
  simp only [ctx.D2_Eloc_translate' i₀ i₁ hy]
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => (p.1 + y, p.2 + y)) (fun p => (p.1 - y, p.2 - y)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product] at hp ⊢
    exact ⟨hadd _ _ hp.1 hyΛ, hadd _ _ hp.2 hyΛ⟩
  · intro p hp
    rw [Finset.mem_product] at hp ⊢
    exact ⟨hsub _ _ hp.1 hyΛ, hsub _ _ hp.2 hyΛ⟩
  · intro p hp
    ext <;> simp
  · intro p hp
    ext <;> simp
  · intro p hp
    simp

/-- The second derivative of the term `E j z₀ Y` at the constant field in two block directions. -/
noncomputable def HtermC (Tm : Terms d L N₁ m₁ k N ϱ) (j : ℕ) (i₀ i₁ : Fin N)
    (z₀ : CTorus d L N₁ m₁ k) (Y : Set (CTorus d L N₁ m₁ k)) (u v : CTorus d L N₁ m₁ k) : ℂ :=
  D2 (fun ψ : Fld d L N₁ m₁ k N => Tm.E j z₀ Y ψ (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
    (blockDir L j u i₁) (blockDir L j v i₁)

/-- **Locality**: the derivative in a block direction supported outside the polymer vanishes. -/
theorem LiftCtx.HtermC_zero_left (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ i₁ : Fin N)
    {z₀ : CTorus d L N₁ m₁ k} {Y : Set (CTorus d L N₁ m₁ k)} (hY : IsPolyDom P.m₀ j Y)
    (h0 : z₀ ∈ Y) {u : CTorus d L N₁ m₁ k} (hu : ∀ z ∈ Y, blockDir (N := N) L j u i₁ z = 0)
    (v : CTorus d L N₁ m₁ k) : HtermC Tm j i₀ i₁ z₀ Y u v = 0 := by
  have ha := ctx.analyticAt_E i₀ z₀ hY h0
  have := D2_congr_slice (f₁ := fun ψ : Fld d L N₁ m₁ k N => Tm.E j z₀ Y ψ (eFld d L N₁ m₁ k N i₀))
    (f₂ := fun ψ : Fld d L N₁ m₁ k N => Tm.E j z₀ Y ψ (eFld d L N₁ m₁ k N i₀)) ha ha
    (c₁ := eFld d L N₁ m₁ k N i₀) (c₂ := eFld d L N₁ m₁ k N i₀) (v₁ := blockDir L j u i₁)
    (w₁ := blockDir L j v i₁) (v₂ := 0) (w₂ := blockDir L j v i₁) (δ := 1) one_pos
    (fun s t _ _ => ctx.sf.localE j z₀ Y _ _ _ _ fun z hz => by
      refine ⟨?_, rfl⟩
      simp [Pi.add_apply, hu z hz])
  unfold HtermC
  rw [this, D2_zero_left]

theorem LiftCtx.HtermC_zero_right (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ i₁ : Fin N)
    {z₀ : CTorus d L N₁ m₁ k} {Y : Set (CTorus d L N₁ m₁ k)} (hY : IsPolyDom P.m₀ j Y)
    (h0 : z₀ ∈ Y) (u : CTorus d L N₁ m₁ k) {v : CTorus d L N₁ m₁ k}
    (hv : ∀ z ∈ Y, blockDir (N := N) L j v i₁ z = 0) : HtermC Tm j i₀ i₁ z₀ Y u v = 0 := by
  have ha := ctx.analyticAt_E i₀ z₀ hY h0
  have := D2_congr_slice (f₁ := fun ψ : Fld d L N₁ m₁ k N => Tm.E j z₀ Y ψ (eFld d L N₁ m₁ k N i₀))
    (f₂ := fun ψ : Fld d L N₁ m₁ k N => Tm.E j z₀ Y ψ (eFld d L N₁ m₁ k N i₀)) ha ha
    (c₁ := eFld d L N₁ m₁ k N i₀) (c₂ := eFld d L N₁ m₁ k N i₀) (v₁ := blockDir L j u i₁)
    (w₁ := blockDir L j v i₁) (v₂ := blockDir L j u i₁) (w₂ := 0) (δ := 1) one_pos
    (fun s t _ _ => ctx.sf.localE j z₀ Y _ _ _ _ fun z hz => by
      refine ⟨?_, rfl⟩
      simp [Pi.add_apply, hv z hz])
  unfold HtermC
  rw [this, D2_zero_right]

/-- **`HtermC` is the tensor `tensB` of the centre-`y` class term `EauxC`**. -/
theorem LiftCtx.HtermC_eq_tensB (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ i₁ : Fin N}
    {y : Site d} {X' : Finset (Site d)} (hnw : NonWind L N₁ m₁ k j X')
    (hpd : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) (hy : y ∈ X')
    {u v : CTorus d L N₁ m₁ k} (hu : Aligned (L ^ j) u) (hv : Aligned (L ^ j) v)
    (huX : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u ∈ X')
    (hvX : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v ∈ X') :
    HtermC Tm j i₀ i₁ (blockPt j y) (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v =
      tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
        (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X')
        ⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u, huX⟩
        ⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v, hvX⟩ := by
  have hjk := ctx.jk
  have hρ0 := ctx.rho_pos
  have h1 := ctx.analyticAt_E i₀ (blockPt j y) hpd (blockPt_mem_Ypoly hjk hnw hy)
  have h2 : AnalyticAt ℂ (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X')
      (refPt i₀ (nuIdeal L k (ν k) j) X') :=
    ctx.analyticAt_EauxC i₀ hpd y hnw hy (mem_ball_self hρ0)
  unfold HtermC tensB
  refine D2_congr_slice h1 h2 (δ := ρ / 2) (by linarith) fun s t hs ht => ?_
  set c : Cfg d N X' := refPt i₀ (nuIdeal L k (ν k) j) X' +
    s • (Pi.single (Sum.inl (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u, huX⟩, i₁)) 1 :
      Cfg d N X') +
    t • (Pi.single (Sum.inl (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v, hvX⟩, i₁)) 1 :
      Cfg d N X') with hc
  have hcu : ∀ (w : CTorus d L N₁ m₁ k) (z : CTorus d L N₁ m₁ k), Aligned (L ^ j) w →
      (cbase (L ^ j) z = w ↔ unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z =
        unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j w) := fun w z hw => by
    rw [cbase_eq_iff_jBlock hjk hw z, unlift_eq_iff]
  have hf : fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ X' c =
      eFld d L N₁ m₁ k N i₀ + s • blockDir L j u i₁ + t • blockDir L j v i₁ := by
    funext z i
    by_cases hz : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z ∈ X'
    · simp only [fieldOf, hz, dite_true, hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply, refPt_inl, blockDir, eFld, constFld, hcu u z hu, hcu v z hv,
        Sum.inl.injEq, Prod.mk.injEq, Subtype.mk.injEq]
    · have hu0 : blockDir (N := N) L j u i₁ z i = 0 := by
        simp only [blockDir, hcu u z hu]
        refine ite_eq_right_iff.2 fun h => absurd ?_ hz
        rw [h.1]; exact huX
      have hv0 : blockDir (N := N) L j v i₁ z i = 0 := by
        simp only [blockDir, hcu v z hv]
        refine ite_eq_right_iff.2 fun h => absurd ?_ hz
        rw [h.1]; exact hvX
      simp only [fieldOf, hz, dite_false, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eFld,
        constFld, hu0, hv0]
      ring
  have hνj : 0 < nuIdeal L k (ν k) j := by
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have := ctx.nu_pos
    unfold nuIdeal; positivity
  have hνc : ((nuIdeal L k (ν k) j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
  have hh : hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' c =
      eFld d L N₁ m₁ k N i₀ := by
    funext z i
    simp only [hOf, hc, Pi.add_apply, Pi.smul_apply, eFld, constFld]
    rw [refPt_inr]
    simp only [Pi.single_apply, smul_eq_mul]
    simp only [reduceCtorEq, ite_false, mul_zero, add_zero]
    field_simp
  show _ = Tm.E j (blockPt j y) (Ypoly j X') (fieldOf j i₀ X' c) (hOf (nuIdeal L k (ν k) j) X' c)
  rw [hf, hh]

omit [NeZero N₁] in
theorem shN_finite [NeZero N₁] (y : Site d) :
    {X' : Finset (Site d) | y ∈ X' ∧ NonWind L N₁ m₁ k j X'}.Finite := by
  classical
  set r : ℕ := (N₁ * L ^ m₁ * L ^ (k - j)) / 2 with hr
  set B : Finset (Site d) := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) r) with hB
  refine ((B.powerset : Set (Finset (Site d))).toFinite).subset ?_
  intro X' hX'
  obtain ⟨-, hnw⟩ := hX'
  show X' ∈ (B.powerset : Set (Finset (Site d)))
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
  intro z hz
  simp only [hB, Fintype.mem_piFinset, Finset.mem_Icc]
  intro μ
  have h1 := ZMod.natAbs_valMinAbs_le
    (((z μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k - j))))
  rw [hnw z hz μ] at h1
  have h2 : ((z μ).natAbs : ℤ) ≤ r := by exact_mod_cast h1
  constructor <;> omega

open Classical in
/-- **The second-moment sum of the torus as a sum over the shapes through a centre `y`**
(CLASS-RULINGS Q-B (1)): `momentSum = ∑_{X' ∋ y} ∑_{x, x' ∈ X'} B_{X'}(x, x') |x - x'|²` with the
tensor `B_{X'} = tensB` of the centre-`y` class term `EauxC`. -/
theorem LiftCtx.momentSum_shapes_centre (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hN : L ^ P.m₀ ∣ N₁)
    {i₀ i₁ : Fin N} (y : Site d)
    (hyu : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (blockPt j y) = y) :
    momentSum P.m₀ Tm j i₀ i₁ =
      ∑ᶠ X' ∈ {X' : Finset (Site d) | y ∈ X' ∧ NonWind L N₁ m₁ k j X' ∧
          IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')},
        ∑ z : ↥X', ∑ z' : ↥X', tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (EauxC Tm j i₀ (nuIdeal L k (ν k) j) y X') z z' *
          (liftSq L j (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z.1 -
            ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z'.1) : ℂ) := by
  have hjk := ctx.jk
  set Sset : Set (Finset (Site d)) := {X' : Finset (Site d) | y ∈ X' ∧ NonWind L N₁ m₁ k j X' ∧
          IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')} with hSset
  have hfin : Sset.Finite :=
    (shN_finite (L := L) (m₁ := m₁) (k := k) (j := j) (N₁ := N₁) y).subset fun X' hX' =>
      ⟨hX'.1, hX'.2.1⟩
  set Sh := hfin.toFinset with hSh
  have hmemSh : ∀ X', X' ∈ Sh ↔ (y ∈ X' ∧ NonWind L N₁ m₁ k j X' ∧
      IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) :=
    fun X' => Set.Finite.mem_toFinset _
  set Λ : Finset (CTorus d L N₁ m₁ k) :=
    (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)) with hΛ
  have hbp : blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y = ibase j y := by
    funext μ; simp only [blockPt, ibase]; congr 1; ring
  have hal : Aligned (L ^ j) (blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y) := by
    rw [hbp]; exact ibase_aligned hjk y
  rw [ctx.momentSum_eq_centre i₀ i₁ hal]
  have hG : ∀ u v : CTorus d L N₁ m₁ k,
      D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j (blockPt j y) ψ (eFld d L N₁ m₁ k N i₀))
        (eFld d L N₁ m₁ k N i₀) (blockDir L j u i₁) (blockDir L j v i₁) =
      ∑ X' ∈ Sh, HtermC Tm j i₀ i₁ (blockPt j y)
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v := by
    intro u v
    have h1 : (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j (blockPt j y) ψ (eFld d L N₁ m₁ k N i₀)) =
        fun ψ => ∑ X' ∈ Sh, Tm.E j (blockPt j y)
          (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') ψ (eFld d L N₁ m₁ k N i₀) := by
      funext ψ
      rw [Eloc_eq_finsum hjk hN Tm (blockPt j y) ψ _, hyu]
      exact finsum_mem_eq_finite_toFinset_sum _ hfin
    rw [h1, D2_sum Sh (fun X' hX' => ctx.analyticAt_E i₀ (blockPt j y) ((hmemSh X').1 hX').2.2
      (blockPt_mem_Ypoly hjk ((hmemSh X').1 hX').2.1 ((hmemSh X').1 hX').1))]
    rfl
  simp only [hG, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_comm), Finset.sum_comm]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_congr rfl fun X' hX' => ?_
  obtain ⟨hy, hnw, hpd⟩ := (hmemSh X').1 hX'
  have hY0 : blockPt (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y ∈
      Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' := blockPt_mem_Ypoly hjk hnw hy
  have hvan : ∀ u : CTorus d L N₁ m₁ k, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u ∉ X' →
      ∀ z ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X', blockDir (N := N) L j u i₁ z = 0 := by
    intro u hu z hz
    funext i
    simp only [blockDir]
    refine ite_eq_right_iff.2 fun h => absurd ?_ hu
    have h2 : jBlock d L (N₁ * L ^ m₁) k j z = jBlock d L (N₁ * L ^ m₁) k j u := by
      rw [← jBlock_cbase z, h.1]
    have h3 := unlift_eq_iff.2 h2
    rw [← h3]; exact hz
  have hL : ∀ u v : CTorus d L N₁ m₁ k,
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u ∉ X' →
      HtermC Tm j i₀ i₁ (blockPt j y) (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v = 0 :=
    fun u v hu => ctx.HtermC_zero_left i₀ i₁ hpd hY0 (hvan u hu) v
  have hR : ∀ u v : CTorus d L N₁ m₁ k,
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v ∉ X' →
      HtermC Tm j i₀ i₁ (blockPt j y) (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v = 0 :=
    fun u v hv => ctx.HtermC_zero_right i₀ i₁ hpd hY0 u (hvan v hv)
  set Λ' := Λ.filter (fun u => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u ∈ X') with hΛ'
  have e1 : ∀ u : CTorus d L N₁ m₁ k, ∑ v ∈ Λ, HtermC Tm j i₀ i₁ (blockPt j y)
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v * (liftSq L j (u - v) : ℂ) =
      ∑ v ∈ Λ', HtermC Tm j i₀ i₁ (blockPt j y)
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v * (liftSq L j (u - v) : ℂ) := by
    intro u
    symm
    refine Finset.sum_filter_of_ne fun v _ hne' => ?_
    by_contra hv
    exact hne' (by rw [hR u v hv, zero_mul])
  rw [Finset.sum_congr rfl (fun u _ => e1 u)]
  have e2 : ∑ u ∈ Λ, ∑ v ∈ Λ', HtermC Tm j i₀ i₁ (blockPt j y)
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v * (liftSq L j (u - v) : ℂ) =
      ∑ u ∈ Λ', ∑ v ∈ Λ', HtermC Tm j i₀ i₁ (blockPt j y)
        (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v * (liftSq L j (u - v) : ℂ) := by
    symm
    refine Finset.sum_filter_of_ne fun u _ hne' => ?_
    by_contra hu
    exact hne' (Finset.sum_eq_zero fun v _ => by rw [hL u v hu, zero_mul])
  rw [e2]
  rw [hΛ', sum_aligned_filter hjk hnw]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [sum_aligned_filter hjk hnw]
  refine Finset.sum_congr rfl fun z' _ => ?_
  have hzu : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
      (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z.1) = z.1 := unlift_ibase hjk (hnw z.1 z.2)
  have hzu' : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
      (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z'.1) = z'.1 := unlift_ibase hjk (hnw z'.1 z'.2)
  have := ctx.HtermC_eq_tensB (i₀ := i₀) (i₁ := i₁) hnw hpd hy (ibase_aligned hjk z.1) (ibase_aligned hjk z'.1)
    (by rw [hzu]; exact z.2) (by rw [hzu']; exact z'.2)
  have e3 : (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
      (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z.1), by rw [hzu]; exact z.2⟩ : ↥X') = z :=
    Subtype.ext hzu
  have e4 : (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
      (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z'.1), by rw [hzu']; exact z'.2⟩ : ↥X') = z' :=
    Subtype.ext hzu'
  rw [e3, e4] at this
  rw [this]

end Torus

end Balaban.SmallField.Def6
