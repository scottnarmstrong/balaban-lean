/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6InfPoly
public import Balaban.SmallField.Def6InfD2
public import Balaban.SmallField.Def6InfPaving
public import Balaban.SmallField.Def6BridgeInfSum
public import Balaban.SmallField.Def6InfCov
public import Balaban.SmallField.Def6InfShapes

/-!
# Def-6: the second-moment sum of a torus as a sum over the shapes

* `Hterm`: the second derivative of the torus term `E j 0 Y` at the constant field in two block
  directions; it vanishes if a direction is supported off the polymer (`Hterm_zero_left/right`) and
  equals the tensor `tensB` of the centred term `termL` of the lifted family
  (`LiftCtx.Hterm_eq_tensB`);
* `LiftCtx.momentSum_shapes`: `momentSum = ∑_{X'} ∑_{x,x' ∈ X'} B_{X'}(x,x') |x - x'|²`
  (the relative-pair form of CLASS-RULINGS Q-B equation (1), on one torus).
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter Metric Set

section Blk

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem jBlock_cbase {j : ℕ} (z : CTorus d L N₁ m₁ k) :
    jBlock d L (N₁ * L ^ m₁) k j (cbase (L ^ j) z) = jBlock d L (N₁ * L ^ m₁) k j z := by
  have : NeZero (N₁ * L ^ m₁ * L ^ (k - j)) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  have hp : 0 < L ^ j := pow_pos (NeZero.pos L) j
  funext μ
  simp only [jBlock, blockMap_apply, blockCoord]
  have hlt : L ^ j * ((z μ).val / L ^ j) < N₁ * L ^ m₁ * L ^ k := by
    have := Nat.div_mul_le_self (z μ).val (L ^ j)
    have h2 := ZMod.val_lt (z μ)
    rw [mul_comm]; omega
  have : ((cbase (L ^ j) z) μ).val = L ^ j * ((z μ).val / L ^ j) := by
    simp only [cbase]; exact ZMod.val_natCast_of_lt hlt
  rw [this, Nat.mul_div_cancel_left _ hp]

omit [NeZero L] in
omit [NeZero N₁] in
theorem unlift_eq_iff {j : ℕ} {z z' : CTorus d L N₁ m₁ k} :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z =
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z' ↔
      jBlock d L (N₁ * L ^ m₁) k j z = jBlock d L (N₁ * L ^ m₁) k j z' := by
  constructor
  · intro h
    funext μ
    have := congrFun h μ
    simp only [unlift] at this
    exact ZMod.valMinAbs_inj.1 this
  · intro h
    funext μ
    simp only [unlift, h]

theorem cbase_eq_iff_jBlock {j : ℕ} (hjk : j ≤ k) {u : CTorus d L N₁ m₁ k} (hu : Aligned (L ^ j) u)
    (z : CTorus d L N₁ m₁ k) :
    cbase (L ^ j) z = u ↔
      jBlock d L (N₁ * L ^ m₁) k j z = jBlock d L (N₁ * L ^ m₁) k j u := by
  have hp : 0 < L ^ j := pow_pos (NeZero.pos L) j
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k := by
    rw [side_eq hjk]; exact dvd_mul_right _ _
  have hcu : cbase (L ^ j) u = u := cbase_eq_of_mem_box hdvd hu (mem_box_self u hp)
  constructor
  · intro h
    rw [← jBlock_cbase z, h]
  · intro h
    rw [cbase_pow_eq_of_jBlock hjk h, hcu]

end Blk


section Terms

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {P : Consts} {β ν a : ℕ → ℝ}
  {Tm : Terms d L N₁ m₁ k N ϱ}
  {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {Ek : ℝ} {j : ℕ} {ρ : ℝ}

/-- The second derivative of the term `E j 0 Y` at the constant field in the block directions. -/
noncomputable def Hterm (Tm : Terms d L N₁ m₁ k N ϱ) (j : ℕ) (i₀ i₁ : Fin N)
    (Y : Set (CTorus d L N₁ m₁ k)) (u v : CTorus d L N₁ m₁ k) : ℂ :=
  D2 (fun ψ : Fld d L N₁ m₁ k N => Tm.E j 0 Y ψ (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
    (blockDir L j u i₁) (blockDir L j v i₁)

/-- **Locality**: the derivative in a block direction supported outside the polymer vanishes. -/
theorem LiftCtx.Hterm_zero_left (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ i₁ : Fin N)
    {Y : Set (CTorus d L N₁ m₁ k)} (hY : IsPolyDom P.m₀ j Y) (h0 : (0 : CTorus d L N₁ m₁ k) ∈ Y)
    {u : CTorus d L N₁ m₁ k} (hu : ∀ z ∈ Y, blockDir (N := N) L j u i₁ z = 0)
    (v : CTorus d L N₁ m₁ k) : Hterm Tm j i₀ i₁ Y u v = 0 := by
  have ha := ctx.analyticAt_E i₀ 0 hY h0
  have := D2_congr_slice (f₁ := fun ψ : Fld d L N₁ m₁ k N => Tm.E j 0 Y ψ (eFld d L N₁ m₁ k N i₀))
    (f₂ := fun ψ : Fld d L N₁ m₁ k N => Tm.E j 0 Y ψ (eFld d L N₁ m₁ k N i₀)) ha ha
    (c₁ := eFld d L N₁ m₁ k N i₀) (c₂ := eFld d L N₁ m₁ k N i₀) (v₁ := blockDir L j u i₁)
    (w₁ := blockDir L j v i₁) (v₂ := 0) (w₂ := blockDir L j v i₁) (δ := 1) one_pos
    (fun s t _ _ => ctx.sf.localE j 0 Y _ _ _ _ fun z hz => by
      refine ⟨?_, rfl⟩
      simp [Pi.add_apply, hu z hz])
  unfold Hterm
  rw [this, D2_zero_left]

theorem LiftCtx.Hterm_zero_right (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (i₀ i₁ : Fin N)
    {Y : Set (CTorus d L N₁ m₁ k)} (hY : IsPolyDom P.m₀ j Y) (h0 : (0 : CTorus d L N₁ m₁ k) ∈ Y)
    (u : CTorus d L N₁ m₁ k) {v : CTorus d L N₁ m₁ k}
    (hv : ∀ z ∈ Y, blockDir (N := N) L j v i₁ z = 0) : Hterm Tm j i₀ i₁ Y u v = 0 := by
  have ha := ctx.analyticAt_E i₀ 0 hY h0
  have := D2_congr_slice (f₁ := fun ψ : Fld d L N₁ m₁ k N => Tm.E j 0 Y ψ (eFld d L N₁ m₁ k N i₀))
    (f₂ := fun ψ : Fld d L N₁ m₁ k N => Tm.E j 0 Y ψ (eFld d L N₁ m₁ k N i₀)) ha ha
    (c₁ := eFld d L N₁ m₁ k N i₀) (c₂ := eFld d L N₁ m₁ k N i₀) (v₁ := blockDir L j u i₁)
    (w₁ := blockDir L j v i₁) (v₂ := blockDir L j u i₁) (w₂ := 0) (δ := 1) one_pos
    (fun s t _ _ => ctx.sf.localE j 0 Y _ _ _ _ fun z hz => by
      refine ⟨?_, rfl⟩
      simp [Pi.add_apply, hv z hz])
  unfold Hterm
  rw [this, D2_zero_right]


/-- **`Hterm` is the tensor `tensB` of the centred term `termL`** (CLASS-RULINGS Q-B (1), (5)):
for a shape `X'` of the lifted family and two blocks `u`, `v` of `X'`, the second derivative of
the torus term in the block directions is the tensor `B_{X'}(ũ, ṽ)` of the lifted family. -/
theorem LiftCtx.Hterm_eq_tensB (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) {i₀ i₁ : Fin N}
    (hne : i₁ ≠ i₀) {X' : Finset (Fin d → ℤ)}
    (hX : X' ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j)
    {u v : CTorus d L N₁ m₁ k} (hu : Aligned (L ^ j) u) (hv : Aligned (L ^ j) v)
    (huX : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u ∈ X')
    (hvX : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v ∈ X') :
    Hterm Tm j i₀ i₁ (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v =
      tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
        (termL Tm j i₀ (nuIdeal L k (ν k) j) ρ X')
        ⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u, huX⟩
        ⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v, hvX⟩ := by
  obtain ⟨h0, hnw, hpd⟩ := hX
  have hjk := ctx.jk
  have hρ0 := ctx.rho_pos
  have hνj : 0 < nuIdeal L k (ν k) j := by
    have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have := ctx.nu_pos
    unfold nuIdeal; positivity
  have hνc : ((nuIdeal L k (ν k) j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hνj.ne'
  have h1 := ctx.analyticAt_E i₀ 0 hpd (zero_mem_Ypoly h0)
  have h2 : AnalyticAt ℂ (termL Tm j i₀ (nuIdeal L k (ν k) j) ρ X')
      (refPt i₀ (nuIdeal L k (ν k) j) X') :=
    ctx.analytic hne hpd h0 _ (ball_subset_tube i₀ _ ρ X' (mem_ball_self hρ0))
  unfold Hterm tensB
  refine D2_congr_slice h1 h2 (δ := ρ / 2) (by linarith) fun s t hs ht => ?_
  set c : Cfg d N X' := refPt i₀ (nuIdeal L k (ν k) j) X' +
    s • (Pi.single (Sum.inl (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u, huX⟩, i₁)) 1 :
      Cfg d N X') +
    t • (Pi.single (Sum.inl (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v, hvX⟩, i₁)) 1 :
      Cfg d N X') with hc
  have hcb : c ∈ Metric.ball (refPt i₀ (nuIdeal L k (ν k) j) X') ρ := by
    rw [mem_ball, dist_eq_norm, hc, add_assoc, add_sub_cancel_left]
    refine lt_of_le_of_lt (norm_add_le _ _) ?_
    have e1 := norm_single_one_le (Sum.inl (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u, huX⟩,
      i₁) : Idx d N X')
    have e2 := norm_single_one_le (Sum.inl (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v, hvX⟩,
      i₁) : Idx d N X')
    rw [norm_smul, norm_smul]
    nlinarith [norm_nonneg s, norm_nonneg t]
  have hL := ctx.termL_of_ball hne hpd h0 hcb
  rw [hL]
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
  have hh : hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (nuIdeal L k (ν k) j) X' c =
      eFld d L N₁ m₁ k N i₀ := by
    funext z i
    simp only [hOf, hc, Pi.add_apply, Pi.smul_apply, eFld, constFld]
    rw [refPt_inr]
    simp only [Pi.single_apply, smul_eq_mul]
    simp only [reduceCtorEq, ite_false, mul_zero, add_zero]
    field_simp
  rw [hf, hh]


/-- The sites aligned to the grid of side `L^j` are the lifts `ibase` of centred block positions. -/
theorem ibase_aligned {j : ℕ} (hjk : j ≤ k) (z : Fin d → ℤ) :
    Aligned (L ^ j) (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z) := by
  have : NeZero (N₁ * L ^ m₁ * L ^ k) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k := by
    rw [side_eq hjk]; exact dvd_mul_right _ _
  intro μ
  exact (aligned_val_iff hdvd _).2 (dvd_mul_right _ _)

theorem ibase_unlift {j : ℕ} (hjk : j ≤ k) {u : CTorus d L N₁ m₁ k} (hu : Aligned (L ^ j) u) :
    ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
      (unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u) = u := by
  have : NeZero (N₁ * L ^ m₁ * L ^ k) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  have h := toTorus_fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hjk u
  funext μ
  have h1 := congrFun h μ
  simp only [toTorus] at h1
  have h2 : fineLift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u μ =
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u μ * ((L ^ j : ℕ) : ℤ) := by
    simp only [fineLift, hu μ, Nat.cast_zero, add_zero]
  rw [h2] at h1
  rw [← h1]
  simp only [ibase]
  congr 1
  ring


open Classical in
/-- Sums over the aligned sites whose block lies in `X'` are sums over `X'`. -/
theorem sum_aligned_filter {M : Type*} [AddCommMonoid M] {j : ℕ} (hjk : j ≤ k)
    {X' : Finset (Fin d → ℤ)} (hnw : NonWind L N₁ m₁ k j X') (F : CTorus d L N₁ m₁ k → M) :
    ∑ u ∈ ((Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j))).filter
        (fun u => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u ∈ X'), F u =
      ∑ z : ↥X', F (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z.1) := by
  refine Finset.sum_bij' (fun u hu => ⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u,
    (Finset.mem_filter.1 hu).2⟩) (fun z _ => ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z.1)
    ?_ ?_ ?_ ?_ ?_
  · intro u hu; exact Finset.mem_univ _
  · intro z _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨ibase_aligned hjk z.1, ?_⟩
    rw [unlift_ibase hjk (hnw z.1 z.2)]; exact z.2
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact ibase_unlift hjk hu.1
  · intro z _
    exact Subtype.ext (unlift_ibase hjk (hnw z.1 z.2))
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact congrArg F (ibase_unlift hjk hu.1).symm


open Classical in
/-- **The second-moment sum of the torus as a sum over the shapes** (CLASS-RULINGS Q-B (1)):
`momentSum = ∑_{X'} ∑_{x, x' ∈ X'} B_{X'}(x, x') |x - x'|²` with the tensor `B_{X'} = tensB` of the
lifted family `termL` and `|·|²` the (wrapped) squared norm of the torus. -/
theorem LiftCtx.momentSum_shapes (ctx : LiftCtx P β ν a Tm ρd Ek j ρ) (hN : L ^ P.m₀ ∣ N₁)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    momentSum P.m₀ Tm j i₀ i₁ =
      ∑ X' ∈ (liftPolys_finite (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j).toFinset,
        ∑ z : ↥X', ∑ z' : ↥X', tensB i₀ i₁ (nuIdeal L k (ν k) j) X'
          (termL Tm j i₀ (nuIdeal L k (ν k) j) ρ X') z z' *
          (liftSq L j (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z.1 -
            ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z'.1) : ℂ) := by
  have hjk := ctx.jk
  set Sh := (liftPolys_finite (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j).toFinset
    with hSh
  set Λ : Finset (CTorus d L N₁ m₁ k) :=
    (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)) with hΛ
  have hmemSh : ∀ X', X' ∈ Sh ↔ X' ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j :=
    fun X' => Set.Finite.mem_toFinset _
  rw [ctx.momentSum_eq i₀ i₁]
  have hG : ∀ u v : CTorus d L N₁ m₁ k,
      D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j 0 ψ (eFld d L N₁ m₁ k N i₀))
        (eFld d L N₁ m₁ k N i₀) (blockDir L j u i₁) (blockDir L j v i₁) =
      ∑ X' ∈ Sh, Hterm Tm j i₀ i₁ (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v := by
    intro u v
    have h1 : (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ Tm j 0 ψ (eFld d L N₁ m₁ k N i₀)) =
        fun ψ => ∑ X' ∈ Sh, Tm.E j 0 (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') ψ
          (eFld d L N₁ m₁ k N i₀) :=
      funext fun ψ => Eloc_zero_eq_sum hjk hN Tm ψ _
    rw [h1, D2_sum Sh (fun X' hX' => ctx.analyticAt_E i₀ 0 ((hmemSh X').1 hX').2.2
      (zero_mem_Ypoly ((hmemSh X').1 hX').1))]
    rfl
  simp only [hG, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl fun X' hX' => ?_
  have hX := (hmemSh X').1 hX'
  obtain ⟨h0, hnw, hpd⟩ := hX
  have hY0 : (0 : CTorus d L N₁ m₁ k) ∈ Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' :=
    zero_mem_Ypoly h0
  -- vanishing
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
      Hterm Tm j i₀ i₁ (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v = 0 :=
    fun u v hu => ctx.Hterm_zero_left i₀ i₁ hpd hY0 (hvan u hu) v
  have hR : ∀ u v : CTorus d L N₁ m₁ k,
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v ∉ X' →
      Hterm Tm j i₀ i₁ (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v = 0 :=
    fun u v hv => ctx.Hterm_zero_right i₀ i₁ hpd hY0 u (hvan v hv)
  set Λ' := Λ.filter (fun u => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j u ∈ X') with hΛ'
  have e1 : ∀ u : CTorus d L N₁ m₁ k, ∑ v ∈ Λ, Hterm Tm j i₀ i₁
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v * (liftSq L j (u - v) : ℂ) =
      ∑ v ∈ Λ', Hterm Tm j i₀ i₁ (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v *
        (liftSq L j (u - v) : ℂ) := by
    intro u
    symm
    refine Finset.sum_filter_of_ne fun v _ hne' => ?_
    by_contra hv
    exact hne' (by rw [hR u v hv, zero_mul])
  rw [Finset.sum_congr rfl (fun u _ => e1 u)]
  have e2 : ∑ u ∈ Λ, ∑ v ∈ Λ', Hterm Tm j i₀ i₁
      (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X') u v * (liftSq L j (u - v) : ℂ) =
      ∑ u ∈ Λ', ∑ v ∈ Λ', Hterm Tm j i₀ i₁
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
  have := ctx.Hterm_eq_tensB hne ⟨h0, hnw, hpd⟩ (ibase_aligned hjk z.1) (ibase_aligned hjk z'.1)
    (by rw [hzu]; exact z.2) (by rw [hzu']; exact z'.2)
  have e3 : (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
      (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z.1), by rw [hzu]; exact z.2⟩ : ↥X') = z :=
    Subtype.ext hzu
  have e4 : (⟨unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
      (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z'.1), by rw [hzu']; exact z'.2⟩ : ↥X') = z' :=
    Subtype.ext hzu'
  rw [e3, e4] at this
  rw [this]

end Terms

end Balaban.SmallField.Def6
