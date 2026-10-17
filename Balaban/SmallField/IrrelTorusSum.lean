/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorus
public import Balaban.SmallField.Def6v2Bridge
public import Balaban.SmallField.Def6InfCov
public import Balaban.SmallField.Def6InfExpand
public import Balaban.Fluctuation.HatLabelsGeom
public import Balaban.Fluctuation.ClassOldTermInputE

/-!
# The representation `ℰ^{(j)} = Σ_y Σ_{X ∋ y} ℰ^{(j)}_{irrel}(y, X)` on the torus (P1 (3.127))

P1 Proposition 3.10, (3.126)–(3.127), pp. 152–153, for the label functional `irrelTorus`:

* `isPolyDom_cubeAt`, `mem_cubeAt`: the cube `□(y)` (the `π'_j`-cube whose central `π_j`-cube is
  the cell of `y`) is a polymer of `𝒟_j` containing `y`;
* `finsum_irrelTorus_eq`: at each centre `y` the relevant local parts `T_{X'} + Φ_{y,X'}` filed at
  `□(y)` cancel those subtracted from the terms:
  `Σ_{X ∋ y} ℰ_{irrel}(y, X) = ℰ^{(j)}(y) - Σ_{X ∋ y} A_{y,X}`;
* `sum_Aterm_irrelTorus_eq_zero`: `Σ_{y ∈ Λ_j} Σ_{X ∋ y} A_{y,X} = 0` on the torus, from the
  covariance (H.3) of the density `ℰ^{(j)}(y)` under the translations of the level-`j` lattice
  (`eucEloc`): `v₁(x, y) = ∂_{ψ(x)} ℰ^{(j)}(y)(P₀)` depends on `x - y` only (P1 (3.112)–(3.113));
* `sum_irrelTorus_eq_Edens`: `Σ_{y ∈ Λ_j} Σ_{X ∋ y} ℰ_{irrel}(y, X; Ψ, h) = ℰ^{(j)}(Ψ, h)` for all
  fields `(Ψ, h)`, in particular at the composed fields of the step chart;
  `sum_irrelTorus_eq_Edens_xi`: the same on the main instance `xiFieldDom` of the class
  (`xiFieldDom_near_ref`); `IsSFFamily2.sum_irrelTorus_eq_Edens`: on every torus of a member of
  the class; `sum_classLabels_irrelTorus_eq_Edens`: the sum over the labels `𝒯E` of the step,
  `Σ_τ ℰ_{irrel}(τ) = Σ_{j=1}^k ℰ^{(j)}`.

The class hypotheses used: the term clauses `SFTermClauses` (`analyticE`, `localE`, `eucEloc`,
`gs_spec`), `L^{m₀} ∣ N₁`, `1 ≤ j ≤ k`, and that the domain of the level `j` contains the
block-constant fields near the reference field `e_{i₀}` with `h = e_{i₀}` (for `xiFieldDom`: the
background hypotheses `BgHyp` and the smallness `(2K₁+2) δ ≤ ε_j`, `δ ≤ min (c₀, c₁)`, as in
`xiDom_of_close`).  No renormalization condition, no `MomNum`, no `CRotE` and no membership of a
family `IsSFFamily2` is used: the identity is exact on every torus.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Filter Topology

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-! ### The cube `□(y)` -/

theorem aligned_cubeAt_base {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k)
    (y : CTorus d L N₁ m₁ k) :
    Aligned (cellSide L m₀ m₁ j)
      (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j :
        CTorus d L N₁ m₁ k) := by
  have hdvd := cellSide_dvd (K := k) (m₁ := m₁) (L := L) (N₁ := N₁) hN hjk
  rw [sub_eq_add_neg]
  refine aligned_add hdvd (aligned_cbase y) (aligned_neg hdvd ?_)
  intro μ
  simp only [natT, ZMod.val_natCast]
  rw [Nat.mod_mod_of_dvd _ hdvd]
  exact Nat.mul_mod_left _ _

theorem mem_cubeAt {m₀ j : ℕ} (y : CTorus d L N₁ m₁ k) :
    y ∈ box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
      (L * cellSide L m₀ m₁ j) := by
  have hcs : 0 < cellSide L m₀ m₁ j := cellSide_pos m₀ m₁ j
  refine ⟨fun μ => L / 2 * cellSide L m₀ m₁ j + (y μ).val % cellSide L m₀ m₁ j,
    fun μ => ?_, ?_⟩
  · have h1 : (y μ).val % cellSide L m₀ m₁ j < cellSide L m₀ m₁ j := Nat.mod_lt _ hcs
    have h2 : L / 2 + 1 ≤ L := by have := NeZero.pos L; omega
    calc L / 2 * cellSide L m₀ m₁ j + (y μ).val % cellSide L m₀ m₁ j
        < L / 2 * cellSide L m₀ m₁ j + cellSide L m₀ m₁ j := by omega
      _ = (L / 2 + 1) * cellSide L m₀ m₁ j := by ring
      _ ≤ L * cellSide L m₀ m₁ j := Nat.mul_le_mul_right _ h2
  · have e : (fun μ => L / 2 * cellSide L m₀ m₁ j + (y μ).val % cellSide L m₀ m₁ j) =
        (fun _ => L / 2 * cellSide L m₀ m₁ j) + fun μ => (y μ).val % cellSide L m₀ m₁ j := rfl
    rw [e, natT_add, cbase_eq_sub]
    abel

/-- **`□(y)` is a polymer of `𝒟_j`**: a single `π'_j`-cube. -/
theorem isPolyDom_cubeAt {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k) (y : CTorus d L N₁ m₁ k) :
    IsPolyDom m₀ j (box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
      (L * cellSide L m₀ m₁ j)) := by
  obtain ⟨hne, hpi, hcon⟩ := isDj_box (m₀ := m₀) (j := j) (aligned_cubeAt_base hN hjk y)
  refine ⟨hne, ⟨{b | Aligned (cellSide L m₀ m₁ j) b ∧ box b (L * cellSide L m₀ m₁ j) ⊆
    box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
      (L * cellSide L m₀ m₁ j)}, fun b hb => hb, fun z hz => ?_⟩, hcon⟩
  obtain ⟨b, h1, h2, h3⟩ := hpi z hz
  exact ⟨b, ⟨h1, h3⟩, h2⟩

/-! ### The cancellation of the filed local parts at each centre -/

open Classical in
/-- **At each centre the filed local parts cancel** (P1 (3.126)–(3.127)): with the cube `□(y)` a
polymer containing `y`, `Σ_{X ∋ y} ℰ_{irrel}(y, X) = ℰ^{(j)}(y) - Σ_{X ∋ y} A_{y,X}`. -/
theorem finsum_irrelTorus_eq {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hjk : j ≤ k)
    (Tm : Terms d L N₁ m₁ k N ϱ) (i₀ i₁ : Fin N) (y : CTorus d L N₁ m₁ k)
    (Ψ h : Fld d L N₁ m₁ k N) :
    ∑ᶠ X ∈ polysAt m₀ j y, irrelTorus m₀ Tm i₀ i₁ j y X Ψ h =
      Eloc m₀ Tm j y Ψ h - ∑ᶠ X ∈ polysAt m₀ j y, (1 / 2 : ℂ) *
        ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
          fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1)))
            (constFld (Pi.single i₀ 1)) (blockDir L j x i₀) *
            (dot (Ψ x) (Ψ x) - dot (Ψ y) (Ψ y)) := by
  obtain ⟨F, hF⟩ : ∃ F : Set (CTorus d L N₁ m₁ k) → ℂ, ∀ X, irrelTorus m₀ Tm i₀ i₁ j y X Ψ h =
      Tm.E j y X Ψ h - F X - (1 / 2 : ℂ) *
        ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
          fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1)))
            (constFld (Pi.single i₀ 1)) (blockDir L j x i₀) *
            (dot (Ψ x) (Ψ x) - dot (Ψ y) (Ψ y)) +
        if X = box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
            (L * cellSide L m₀ m₁ j) then ∑ᶠ Z ∈ polysAt m₀ j y, F Z else 0 :=
    ⟨_, fun X => rfl⟩
  have hfin := Set.toFinite (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j y)
  have hmem : box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
      (L * cellSide L m₀ m₁ j) ∈ hfin.toFinset :=
    hfin.mem_toFinset.2 ⟨isPolyDom_cubeAt hN hjk y, mem_cubeAt y⟩
  unfold Eloc
  simp only [hF]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp only [hmem, ↓reduceIte]
  ring

/-! ### `Σ_y Σ_X A_{y,X} = 0` on the torus -/

/-- The derivative along a line: `Df(c) v = d/dt f(c + t v)|_{t=0}`. -/
theorem fderiv_apply_eq_deriv_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {c : E} (hf : DifferentiableAt ℂ f c) (v : E) :
    fderiv ℂ f c v = deriv (fun t : ℂ => f (c + t • v)) 0 := by
  have hl : HasDerivAt (fun t : ℂ => c + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add c
  have hf' : HasFDerivAt f (fderiv ℂ f c) (c + (0 : ℂ) • v) := by
    simpa using hf.hasFDerivAt
  exact ((hf'.comp_hasDerivAt (0 : ℂ) hl).deriv).symm

/-- Two functions that agree along two lines near `t = 0` have equal derivatives in the directions
of the lines. -/
theorem fderiv_eq_of_eventually_line {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] {f : E → ℂ} {g : E' → ℂ} {c v : E} {c' w : E'}
    (hf : DifferentiableAt ℂ f c) (hg : DifferentiableAt ℂ g c')
    (hfg : ∀ᶠ t in 𝓝 (0 : ℂ), f (c + t • v) = g (c' + t • w)) :
    fderiv ℂ f c v = fderiv ℂ g c' w := by
  rw [fderiv_apply_eq_deriv_line hf, fderiv_apply_eq_deriv_line hg]
  exact Filter.EventuallyEq.deriv_eq hfg

open Classical in
/-- **`Σ_{y ∈ Λ_j} Σ_{X ∋ y} A_{y,X} = 0` on the torus** (P1 (3.109), third sum, and
(3.112)–(3.113)): the coefficient `Σ_{X ∋ y, x} a_X(x) = ∂_{ψ(x)} ℰ^{(j)}(y)(P₀)` of
`Ψ(x)·Ψ(x) - Ψ(y)·Ψ(y)` depends only on `x - y`, by the covariance (H.3) `eucEloc` of the density
under the translations of the level-`j` lattice, so its sums over `x` and over `y` agree.  The
hypothesis `hdom`: the domain of the level `j` (for every generating set of level `≤ j`) contains
the block-constant fields within `ρ` of `e_{i₀}`, with `h = e_{i₀}`. -/
theorem sum_Aterm_irrelTorus_eq_zero {P : Consts} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    {Tm : Terms d L N₁ m₁ k N ϱ} (hcl : SFTermClauses P Dom Tm) (hN : L ^ P.m₀ ∣ N₁) {j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (i₀ : Fin N)
    (hdom : ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ, (∀ i, j < i → G.Ω i = ∅) →
      ∀ Ψ : Fld d L N₁ m₁ k N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
      (∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x') →
      Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
    (Ψ : Fld d L N₁ m₁ k N) :
    ∑ y ∈ Finset.univ.filter (Aligned (L ^ j)), ∑ᶠ X ∈ polysAt P.m₀ j y, (1 / 2 : ℂ) *
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
        fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' (constFld (Pi.single i₀ 1)))
          (constFld (Pi.single i₀ 1)) (blockDir L j x i₀) *
          (dot (Ψ x) (Ψ x) - dot (Ψ y) (Ψ y)) = 0 := by
  obtain ⟨ρ, hρ, hD⟩ := hdom
  set e : Fld d L N₁ m₁ k N := constFld (Pi.single i₀ 1) with he
  set Λ : Finset (CTorus d L N₁ m₁ k) := Finset.univ.filter (Aligned (L ^ j)) with hΛ
  have hdvd : L ^ j ∣ N₁ * L ^ m₁ * L ^ k := by rw [side_eq hjk]; exact dvd_mul_right _ _
  -- the terms are analytic at the reference field
  have hAn : ∀ y X, IsPolyDom P.m₀ j X → y ∈ X →
      AnalyticAt ℂ (fun Ψ' : Fld d L N₁ m₁ k N => Tm.E j y X Ψ' e) e := by
    intro y X hX hy
    have hp0 : Dom.dom j (Tm.gs j X) e e :=
      hD (Tm.gs j X) (hcl.gs_spec j hj1 hjk X hX).2 e (fun x i => by simp [he, constFld, hρ.le])
        (fun _ _ _ => rfl)
    have h1 := hcl.analyticE j hj1 hjk y X hX hy (e, e) hp0
    exact AnalyticAt.comp (f := fun Ψ' : Fld d L N₁ m₁ k N => (Ψ', e)) h1
      (analyticAt_id.prod analyticAt_const)
  have hfinP : ∀ y, (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y).Finite :=
    fun y => Set.toFinite _
  have hEloc : ∀ y, (fun Ψ' => Eloc P.m₀ Tm j y Ψ' e) =
      fun Ψ' => ∑ X ∈ (hfinP y).toFinset, Tm.E j y X Ψ' e := by
    intro y; funext Ψ'; unfold Eloc; exact finsum_mem_eq_finite_toFinset_sum _ (hfinP y)
  have hAnL : ∀ y, AnalyticAt ℂ (fun Ψ' => Eloc P.m₀ Tm j y Ψ' e) e := by
    intro y; rw [hEloc y]
    exact Finset.analyticAt_fun_sum _ fun X hX =>
      hAn y X ((hfinP y).mem_toFinset.1 hX).1 ((hfinP y).mem_toFinset.1 hX).2
  -- a term has zero derivative in the direction of a block outside its polymer
  have hzero : ∀ y X, IsPolyDom P.m₀ j X → y ∈ X → ∀ x, x ∉ X →
      fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' e) e (blockDir L j x i₀) = 0 := by
    intro y X hX hy x hxX
    rw [fderiv_apply_eq_deriv_line (hAn y X hX hy).differentiableAt]
    have hc : (fun t : ℂ => Tm.E j y X (e + t • blockDir L j x i₀) e) =
        fun _ => Tm.E j y X e e := by
      funext t
      refine hcl.localE j y X _ _ _ _ fun z hz => ⟨?_, rfl⟩
      have hzx : ¬ cbase (L ^ j) z = x := by
        intro hzx
        apply hxX
        rw [← hzx]
        exact hX.block_closed hjk hN hz (jBlock_cbase z).symm
      have hb : blockDir (N := N) L j x i₀ z = 0 := by
        funext i'
        simp [blockDir, hzx]
      simp [hb]
    rw [hc, deriv_const]
  -- the coefficient of a centre is the derivative of the density
  have hcoef : ∀ y ∈ Λ, ∑ᶠ X ∈ polysAt P.m₀ j y, (1 / 2 : ℂ) *
      ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
        fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' e) e (blockDir L j x i₀) *
          (dot (Ψ x) (Ψ x) - dot (Ψ y) (Ψ y)) =
      (1 / 2 : ℂ) * ∑ x ∈ Λ, fderiv ℂ (fun Ψ' => Eloc P.m₀ Tm j y Ψ' e) e (blockDir L j x i₀) *
        (dot (Ψ x) (Ψ x) - dot (Ψ y) (Ψ y)) := by
    intro y _
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfinP y), ← Finset.mul_sum]
    congr 1
    have hsub : ∀ X ∈ (hfinP y).toFinset,
        ∑ x ∈ Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X),
          fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' e) e (blockDir L j x i₀) *
            (dot (Ψ x) (Ψ x) - dot (Ψ y) (Ψ y)) =
        ∑ x ∈ Λ, fderiv ℂ (fun Ψ' => Tm.E j y X Ψ' e) e (blockDir L j x i₀) *
            (dot (Ψ x) (Ψ x) - dot (Ψ y) (Ψ y)) := by
      intro X hX
      have hX' := (hfinP y).mem_toFinset.1 hX
      refine Finset.sum_subset (fun x hx => ?_) (fun x hx hxn => ?_)
      · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hx).2.1⟩
      · have hxX : x ∉ X := fun h => hxn (Finset.mem_filter.2
          ⟨Finset.mem_univ _, (Finset.mem_filter.1 hx).2, h⟩)
        rw [hzero y X hX'.1 hX'.2 x hxX, zero_mul]
    rw [Finset.sum_congr rfl hsub, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, hEloc y, fderiv_fun_sum fun X hX =>
      (hAn y X ((hfinP y).mem_toFinset.1 hX).1 ((hfinP y).mem_toFinset.1 hX).2).differentiableAt,
      _root_.sum_apply]
  -- translation covariance of the coefficient
  have hlev : ∀ i, j < i →
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk).Ω i = ∅ := by
    intro i hi
    simp [levelGS, not_le.2 hi]
  have hline : ∀ (t : ℂ), ‖t‖ ≤ ρ → ∀ x', Dom.dom j
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (ϱ := ϱ) j hjk)
      (e + t • blockDir L j x' i₀) e := by
    intro t ht x'
    refine hD _ hlev _ (fun z i => ?_) (fun z z' hzz => ?_)
    · have h1 := norm_blockDir_le (N := N) L j x' i₀ z i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, he, constFld, add_sub_cancel_left,
        norm_mul]
      nlinarith [norm_nonneg t, norm_nonneg (blockDir (N := N) L j x' i₀ z i)]
    · simp only [Pi.add_apply, Pi.smul_apply, he, constFld, blockDir_jBlock hjk x' i₀ hzz]
  have hT : ∀ y, Aligned (L ^ j) y → ∀ x,
      fderiv ℂ (fun Ψ' => Eloc P.m₀ Tm j y Ψ' e) e (blockDir L j x i₀) =
        fderiv ℂ (fun Ψ' => Eloc P.m₀ Tm j 0 Ψ' e) e (blockDir L j (x - y) i₀) := by
    intro y hy x
    refine fderiv_eq_of_eventually_line (hAnL y).differentiableAt (hAnL 0).differentiableAt ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) hρ] with t ht
    have ht' : ‖t‖ ≤ ρ := by simpa using ht
    have hr := mem_fullJSymGroup_addRight_neg (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hy
    have e1 := actField_addRight_neg_blockDir (N := N) hjk hy x i₀
    have hact : actField (Equiv.addRight (-y)) (e + t • blockDir L j x i₀) =
        e + t • blockDir L j (x - y) i₀ := by
      rw [← e1]; funext z; rfl
    have hacte : actField (N := N) (Equiv.addRight (-y)) e = e := rfl
    have key := hcl.eucEloc j hj1 hjk y _ hr (e + t • blockDir L j x i₀) e (hline t ht' x)
      (by rw [hact, hacte]; exact hline t ht' (x - y))
    rw [hact, hacte] at key
    have hry : blockBase L j ((Equiv.addRight (-y) : Equiv.Perm (CTorus d L N₁ m₁ k)) y) = 0 := by
      simp only [Equiv.coe_addRight, add_neg_cancel]
      exact blockBase_zero L j
    rw [hry] at key
    exact key.symm
  -- the sums over `x` and over `y` of the coefficient agree
  set c : ℂ := ∑ z ∈ Λ, fderiv ℂ (fun Ψ' => Eloc P.m₀ Tm j 0 Ψ' e) e (blockDir L j z i₀) with hc
  have hmemΛ : ∀ z, z ∈ Λ ↔ Aligned (L ^ j) z := fun z => by simp [hΛ]
  have hsumy : ∀ x ∈ Λ, ∑ y ∈ Λ, fderiv ℂ (fun Ψ' => Eloc P.m₀ Tm j 0 Ψ' e) e
      (blockDir L j (x - y) i₀) = c := by
    intro x hx
    rw [hc]
    refine Finset.sum_nbij' (fun y => x - y) (fun z => x - z) (fun y hy => ?_) (fun z hz => ?_)
      (fun y _ => by simp) (fun z _ => by simp) (fun y _ => rfl)
    · rw [hmemΛ] at hx hy ⊢
      rw [sub_eq_add_neg]; exact aligned_add hdvd hx (aligned_neg hdvd hy)
    · rw [hmemΛ] at hx hz ⊢
      rw [sub_eq_add_neg]; exact aligned_add hdvd hx (aligned_neg hdvd hz)
  have hsumx : ∀ y ∈ Λ, ∑ x ∈ Λ, fderiv ℂ (fun Ψ' => Eloc P.m₀ Tm j 0 Ψ' e) e
      (blockDir L j (x - y) i₀) = c := by
    intro y hy
    rw [hc]
    refine Finset.sum_nbij' (fun x => x - y) (fun z => z + y) (fun x hx => ?_) (fun z hz => ?_)
      (fun x _ => by simp) (fun z _ => by simp) (fun x _ => rfl)
    · rw [hmemΛ] at hx hy ⊢
      rw [sub_eq_add_neg]; exact aligned_add hdvd hx (aligned_neg hdvd hy)
    · rw [hmemΛ] at hy hz ⊢
      exact aligned_add hdvd hz hy
  rw [Finset.sum_congr rfl hcoef]
  have hstep : ∀ y ∈ Λ, (1 / 2 : ℂ) * ∑ x ∈ Λ,
      fderiv ℂ (fun Ψ' => Eloc P.m₀ Tm j y Ψ' e) e (blockDir L j x i₀) *
        (dot (Ψ x) (Ψ x) - dot (Ψ y) (Ψ y)) =
      (1 / 2 : ℂ) * (∑ x ∈ Λ, fderiv ℂ (fun Ψ' => Eloc P.m₀ Tm j 0 Ψ' e) e
          (blockDir L j (x - y) i₀) * dot (Ψ x) (Ψ x) - c * dot (Ψ y) (Ψ y)) := by
    intro y hy
    congr 1
    rw [← hsumx y hy, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hT y ((hmemΛ y).1 hy) x]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_comm]
  have h1 : ∑ x ∈ Λ, ∑ y ∈ Λ, fderiv ℂ (fun Ψ' => Eloc P.m₀ Tm j 0 Ψ' e) e
      (blockDir L j (x - y) i₀) * dot (Ψ x) (Ψ x) = ∑ x ∈ Λ, c * dot (Ψ x) (Ψ x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← Finset.sum_mul, hsumy x hx]
  rw [h1, sub_self, mul_zero]

/-! ### The representation (3.127) -/

open Classical in
/-- **P1 (3.127) on the torus**: for a class whose level-`j` domain contains the block-constant
fields near the reference field (`hdom`),
`Σ_{y ∈ Λ_j} Σ_{X ∈ 𝒟_j, X ∋ y} ℰ^{(j)}_{irrel}(y, X; Ψ, h) = ℰ^{(j)}(Ψ, h)` for **all** fields
`(Ψ, h)`, in particular at the composed fields of every datum of the step chart. -/
theorem sum_irrelTorus_eq_Edens {P : Consts} {Dom : FieldDom d L N₁ m₁ k N ϱ}
    {Tm : Terms d L N₁ m₁ k N ϱ} (hcl : SFTermClauses P Dom Tm) (hN : L ^ P.m₀ ∣ N₁) {j : ℕ}
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (i₀ i₁ : Fin N)
    (hdom : ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ, (∀ i, j < i → G.Ω i = ∅) →
      ∀ Ψ : Fld d L N₁ m₁ k N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
      (∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x') →
      Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
    (Ψ h : Fld d L N₁ m₁ k N) :
    ∑ y ∈ Finset.univ.filter (Aligned (L ^ j)), ∑ᶠ X ∈ polysAt P.m₀ j y,
      irrelTorus P.m₀ Tm i₀ i₁ j y X Ψ h = Edens P.m₀ Tm j Ψ h := by
  rw [Finset.sum_congr rfl fun y _ => finsum_irrelTorus_eq hN hjk Tm i₀ i₁ y Ψ h,
    Finset.sum_sub_distrib, sum_Aterm_irrelTorus_eq_zero hcl hN hj1 hjk i₀ hdom Ψ, sub_zero]
  rfl

/-- **The domain hypothesis on the main instance `xiFieldDom`**: under the background hypotheses
`BgHyp` at the mass `μ` and P1's smallness `ε_j ≤ (2 K₁ + 2) min (c₀, c₁)` (`xiDom_of_close`), the
domain `Ξ^c_j(𝔹; 1, ε_j)` of every generating set of level `≤ j` contains the block-constant fields
within `ρ = ε_j² / (2 N (2 K₁ + 2)²)` of `e_{i₀}`, with `h = e_{i₀}`. -/
theorem xiFieldDom_near_ref {a : ℕ → ℝ} {μ : ℝ} {ε : ℕ → ℝ} (hBg : BgHyp d L k ϱ a μ) {j : ℕ}
    (hjk : j ≤ k) (hε : 0 < ε j)
    (hsmall : ε j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N)) (i₀ : Fin N) :
    ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ, (∀ i, j < i → G.Ω i = ∅) →
      ∀ Ψ : Fld d L N₁ m₁ k N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
      (∀ x x', jBlock d L (N₁ * L ^ m₁) k j x = jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x') →
      (xiFieldDom (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N) (ϱ := ϱ) a μ ε).dom j G Ψ
        (constFld (Pi.single i₀ 1)) := by
  have hK : 0 < 2 * bgK1 d L N + 2 := by have := bgK1_pos d L N; linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos i₀
  set δ : ℝ := ε j / (2 * bgK1 d L N + 2) with hδ
  have hδ0 : 0 < δ := div_pos hε hK
  have hδm : δ ≤ min (bgC0 d L N) (bgC1 d L N) := by
    rw [hδ, div_le_iff₀ hK]; linarith
  refine ⟨δ ^ 2 / (2 * N), by positivity, fun G hΩ Ψ hΨ hΨb => ?_⟩
  exact xiDom_of_close hBg hΩ hjk i₀ hδ0 (hδm.trans (min_le_left _ _))
    (hδm.trans (min_le_right _ _)) (by positivity)
    (by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [sq_pos_of_pos hδ0])
    (by rw [hδ, mul_div_cancel₀ _ hK.ne']) Ψ (Pi.single i₀ 1) hΨ hΨb
    (fun i => by simp only [sub_self, norm_zero, mul_zero]; positivity)

open Classical in
/-- **P1 (3.127) on the main instance of the class**: for term clauses on `xiFieldDom a μ ε`, the
background hypotheses `BgHyp` at the mass `μ` and `0 < ε_j ≤ (2 K₁ + 2) min (c₀, c₁)`,
`Σ_{y ∈ Λ_j} Σ_{X ∋ y} ℰ^{(j)}_{irrel}(y, X; Ψ, h) = ℰ^{(j)}(Ψ, h)` for all fields `(Ψ, h)`. -/
theorem sum_irrelTorus_eq_Edens_xi {P : Consts} {a : ℕ → ℝ} {μ : ℝ} {ε : ℕ → ℝ}
    {Tm : Terms d L N₁ m₁ k N ϱ} (hcl : SFTermClauses P (xiFieldDom a μ ε) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hN : L ^ P.m₀ ∣ N₁) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hε : 0 < ε j) (hsmall : ε j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    (i₀ i₁ : Fin N) (Ψ h : Fld d L N₁ m₁ k N) :
    ∑ y ∈ Finset.univ.filter (Aligned (L ^ j)), ∑ᶠ X ∈ polysAt P.m₀ j y,
      irrelTorus P.m₀ Tm i₀ i₁ j y X Ψ h = Edens P.m₀ Tm j Ψ h :=
  sum_irrelTorus_eq_Edens hcl hN hj1 hjk i₀ i₁ (xiFieldDom_near_ref hBg hjk hε hsmall i₀) Ψ h

open Classical in
/-- **P1 (3.127) over the labels of the step** (the label set `𝒯E` of `sum_classLabels_E_eq_Edens`
and `classActivityFamily_sum_eq`: `(j, y, X)` with `1 ≤ j ≤ k`, `y` an `L^j`-aligned site of the
step torus, `X ∈ 𝒟_j`, `y ∈ X`): `Σ_τ ℰ^{(j)}_{irrel}(τ; ψ_j, h_j) = Σ_{j=1}^k ℰ^{(j)}(ψ_j, h_j)`
for all families of fields, e.g. the composed pairs `(ψ_k^{(j)}, h)` of a datum of the chart. -/
theorem sum_classLabels_irrelTorus_eq_Edens {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    {Tm : Terms d L N₁ m₁ (k + 1) N ϱ} (hcl : SFTermClauses P Dom Tm) (hN : L ^ P.m₀ ∣ N₁)
    (i₀ i₁ : Fin N)
    (hdom : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ,
      (∀ i, j < i → G.Ω i = ∅) →
      ∀ Ψ : Fld d L N₁ m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
      (∀ x x', jBlock d L (N₁ * L ^ m₁) (k + 1) j x = jBlock d L (N₁ * L ^ m₁) (k + 1) j x' →
        Ψ x = Ψ x') →
      Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
    (ψ h : ℕ → Fld d L N₁ m₁ (k + 1) N) :
    ∑ τ ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom P.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2),
      irrelTorus P.m₀ Tm i₀ i₁ τ.1 τ.2.1 τ.2.2 (ψ τ.1) (h τ.1) =
    ∑ j ∈ Finset.Icc 1 k, Edens P.m₀ Tm j (ψ j) (h j) := by
  rw [sum_classLabels_E_eq_Edens P.m₀
    ({ E := irrelTorus P.m₀ Tm i₀ i₁, M := Tm.M, gs := Tm.gs } : Terms d L N₁ m₁ (k + 1) N ϱ) ψ h]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.1 hj
  exact sum_irrelTorus_eq_Edens hcl hN hj1 (hjk.trans (Nat.le_succ k)) i₀ i₁
    (hdom j hj1 hjk) (ψ j) (h j)

open Classical in
/-- **P1 (3.127) for the members of the class** (P-6): for a member of `IsSFFamily2` on the main
field domain `completeXiDom` (complete backgrounds), on every torus `N₁` with `L^{m₀} ∣ N₁` and at
every level `1 ≤ j ≤ k` with P1's smallness `ε_j ≤ (2 K₁ + 2) min (c₀, c₁)`,
`Σ_{y ∈ Λ_j} Σ_{X ∋ y} ℰ^{(j)}_{irrel}(y, X; Ψ, h) = ℰ^{(j)}(Ψ, h)` for all fields.  Only the term
clauses of the torus and the background hypotheses (from `admissible`, `coeff`, `d, L ≥ 3`,
`ϱ ≥ R₀`) are used: not `MomNum`, not `CRotE`, not the renormalization conditions. -/
theorem IsSFFamily2.sum_irrelTorus_eq_Edens {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ}
    {Ek : ℕ → ℝ} {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
    {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
      (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek) (hd : 3 ≤ d) (hL : 3 ≤ L)
    (hϱ : bgR0 d L ≤ ϱ) (N₂ : ℕ) [NeZero N₂] (hN : L ^ P.m₀ ∣ N₂) {j : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    (i₀ i₁ : Fin N) (Ψ h : Fld d L N₂ m₁ k N) :
    ∑ y ∈ Finset.univ.filter (Aligned (L ^ j)), ∑ᶠ X ∈ polysAt P.m₀ j y,
      irrelTorus P.m₀ (Tm N₂) i₀ i₁ j y X Ψ h = Edens P.m₀ (Tm N₂) j Ψ h :=
  sum_irrelTorus_eq_Edens_xi (hF.torus N₂).terms
    (bgHyp_of_class2 hF.admissible hF.coeff hd hL hϱ) hN hj1 hjk
    (eps_pos hF.admissible.α₀_pos j) hsmall i₀ i₁ Ψ h

open Classical in
/-- **P1 (3.127) over the labels of a step, for its class** (`StepClass`; the labels `𝒯E` of
`classActivityFamily_sum_eq`): with `P.m₀ = C.m₀` and the term clauses of `C.Tm` on a field domain
containing the block-constant fields near the reference field at every level `1 ≤ j ≤ k`,
`Σ_{(j,y,X) ∈ 𝒯E} ℰ^{(j)}_{irrel}(y, X; ψ_j, h_j) = Σ_{j=1}^k ℰ^{(j)}(ψ_j, h_j)`. -/
theorem _root_.Balaban.Fluctuation.StepClass.sum_classLabels_irrelTorus_eq_Edens {P : Consts}
    {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ} (C : Balaban.Fluctuation.StepClass d L N₁ m₁ k N ϱ)
    (hm : P.m₀ = C.m₀) (hcl : SFTermClauses P Dom C.Tm) (hN : L ^ C.m₀ ∣ N₁) (i₀ i₁ : Fin N)
    (hdom : ∀ j, 1 ≤ j → j ≤ k → ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ,
      (∀ i, j < i → G.Ω i = ∅) →
      ∀ Ψ : Fld d L N₁ m₁ (k + 1) N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
      (∀ x x', jBlock d L (N₁ * L ^ m₁) (k + 1) j x = jBlock d L (N₁ * L ^ m₁) (k + 1) j x' →
        Ψ x = Ψ x') →
      Dom.dom j G Ψ (constFld (Pi.single i₀ 1)))
    (ψ h : ℕ → Fld d L N₁ m₁ (k + 1) N) :
    ∑ τ ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2),
      irrelTorus C.m₀ C.Tm i₀ i₁ τ.1 τ.2.1 τ.2.2 (ψ τ.1) (h τ.1) =
    ∑ j ∈ Finset.Icc 1 k, Edens C.m₀ C.Tm j (ψ j) (h j) := by
  rw [← hm]
  exact Balaban.SmallField.Def6v2.sum_classLabels_irrelTorus_eq_Edens hcl (by rw [hm]; exact hN) i₀
    i₁ hdom ψ h

end Balaban.SmallField.Def6v2
